import React, { Component } from 'react';
import ReactDOM from 'react-dom';
import classNames from 'classnames';
import 'primereact/resources/themes/nova-light/theme.css';
import 'primereact/resources/primereact.min.css';
import 'primeicons/primeicons.css';
import moment from 'moment';
import 'moment/min/locales';

function _extends() {
  _extends = Object.assign || function (target) {
    for (var i = 1; i < arguments.length; i++) {
      var source = arguments[i];

      for (var key in source) {
        if (Object.prototype.hasOwnProperty.call(source, key)) {
          target[key] = source[key];
        }
      }
    }

    return target;
  };

  return _extends.apply(this, arguments);
}

function _inheritsLoose(subClass, superClass) {
  subClass.prototype = Object.create(superClass.prototype);
  subClass.prototype.constructor = subClass;
  subClass.__proto__ = superClass;
}

function _assertThisInitialized(self) {
  if (self === void 0) {
    throw new ReferenceError("this hasn't been initialised - super() hasn't been called");
  }

  return self;
}

function _unsupportedIterableToArray(o, minLen) {
  if (!o) return;
  if (typeof o === "string") return _arrayLikeToArray(o, minLen);
  var n = Object.prototype.toString.call(o).slice(8, -1);
  if (n === "Object" && o.constructor) n = o.constructor.name;
  if (n === "Map" || n === "Set") return Array.from(o);
  if (n === "Arguments" || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(n)) return _arrayLikeToArray(o, minLen);
}

function _arrayLikeToArray(arr, len) {
  if (len == null || len > arr.length) len = arr.length;

  for (var i = 0, arr2 = new Array(len); i < len; i++) arr2[i] = arr[i];

  return arr2;
}

function _createForOfIteratorHelperLoose(o, allowArrayLike) {
  var it;

  if (typeof Symbol === "undefined" || o[Symbol.iterator] == null) {
    if (Array.isArray(o) || (it = _unsupportedIterableToArray(o)) || allowArrayLike && o && typeof o.length === "number") {
      if (it) o = it;
      var i = 0;
      return function () {
        if (i >= o.length) return {
          done: true
        };
        return {
          done: false,
          value: o[i++]
        };
      };
    }

    throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.");
  }

  it = o[Symbol.iterator]();
  return it.next.bind(it);
}

function createCommonjsModule(fn, module) {
	return module = { exports: {} }, fn(module, module.exports), module.exports;
}

/** @license React v16.13.1
 * react-is.production.min.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */
var b="function"===typeof Symbol&&Symbol.for,c=b?Symbol.for("react.element"):60103,d=b?Symbol.for("react.portal"):60106,e=b?Symbol.for("react.fragment"):60107,f=b?Symbol.for("react.strict_mode"):60108,g=b?Symbol.for("react.profiler"):60114,h=b?Symbol.for("react.provider"):60109,k=b?Symbol.for("react.context"):60110,l=b?Symbol.for("react.async_mode"):60111,m=b?Symbol.for("react.concurrent_mode"):60111,n=b?Symbol.for("react.forward_ref"):60112,p=b?Symbol.for("react.suspense"):60113,q=b?
Symbol.for("react.suspense_list"):60120,r=b?Symbol.for("react.memo"):60115,t=b?Symbol.for("react.lazy"):60116,v=b?Symbol.for("react.block"):60121,w=b?Symbol.for("react.fundamental"):60117,x=b?Symbol.for("react.responder"):60118,y=b?Symbol.for("react.scope"):60119;
function z(a){if("object"===typeof a&&null!==a){var u=a.$$typeof;switch(u){case c:switch(a=a.type,a){case l:case m:case e:case g:case f:case p:return a;default:switch(a=a&&a.$$typeof,a){case k:case n:case t:case r:case h:return a;default:return u}}case d:return u}}}function A(a){return z(a)===m}var AsyncMode=l;var ConcurrentMode=m;var ContextConsumer=k;var ContextProvider=h;var Element=c;var ForwardRef=n;var Fragment=e;var Lazy=t;var Memo=r;var Portal=d;
var Profiler=g;var StrictMode=f;var Suspense=p;var isAsyncMode=function(a){return A(a)||z(a)===l};var isConcurrentMode=A;var isContextConsumer=function(a){return z(a)===k};var isContextProvider=function(a){return z(a)===h};var isElement=function(a){return "object"===typeof a&&null!==a&&a.$$typeof===c};var isForwardRef=function(a){return z(a)===n};var isFragment=function(a){return z(a)===e};var isLazy=function(a){return z(a)===t};
var isMemo=function(a){return z(a)===r};var isPortal=function(a){return z(a)===d};var isProfiler=function(a){return z(a)===g};var isStrictMode=function(a){return z(a)===f};var isSuspense=function(a){return z(a)===p};
var isValidElementType=function(a){return "string"===typeof a||"function"===typeof a||a===e||a===m||a===g||a===f||a===p||a===q||"object"===typeof a&&null!==a&&(a.$$typeof===t||a.$$typeof===r||a.$$typeof===h||a.$$typeof===k||a.$$typeof===n||a.$$typeof===w||a.$$typeof===x||a.$$typeof===y||a.$$typeof===v)};var typeOf=z;

var reactIs_production_min = {
	AsyncMode: AsyncMode,
	ConcurrentMode: ConcurrentMode,
	ContextConsumer: ContextConsumer,
	ContextProvider: ContextProvider,
	Element: Element,
	ForwardRef: ForwardRef,
	Fragment: Fragment,
	Lazy: Lazy,
	Memo: Memo,
	Portal: Portal,
	Profiler: Profiler,
	StrictMode: StrictMode,
	Suspense: Suspense,
	isAsyncMode: isAsyncMode,
	isConcurrentMode: isConcurrentMode,
	isContextConsumer: isContextConsumer,
	isContextProvider: isContextProvider,
	isElement: isElement,
	isForwardRef: isForwardRef,
	isFragment: isFragment,
	isLazy: isLazy,
	isMemo: isMemo,
	isPortal: isPortal,
	isProfiler: isProfiler,
	isStrictMode: isStrictMode,
	isSuspense: isSuspense,
	isValidElementType: isValidElementType,
	typeOf: typeOf
};

var reactIs_development = createCommonjsModule(function (module, exports) {



if (process.env.NODE_ENV !== "production") {
  (function() {

// The Symbol used to tag the ReactElement-like types. If there is no native Symbol
// nor polyfill, then a plain number is used for performance.
var hasSymbol = typeof Symbol === 'function' && Symbol.for;
var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
// (unstable) APIs that have been removed. Can we remove the symbols?

var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;

function isValidElementType(type) {
  return typeof type === 'string' || typeof type === 'function' || // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
  type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
}

function typeOf(object) {
  if (typeof object === 'object' && object !== null) {
    var $$typeof = object.$$typeof;

    switch ($$typeof) {
      case REACT_ELEMENT_TYPE:
        var type = object.type;

        switch (type) {
          case REACT_ASYNC_MODE_TYPE:
          case REACT_CONCURRENT_MODE_TYPE:
          case REACT_FRAGMENT_TYPE:
          case REACT_PROFILER_TYPE:
          case REACT_STRICT_MODE_TYPE:
          case REACT_SUSPENSE_TYPE:
            return type;

          default:
            var $$typeofType = type && type.$$typeof;

            switch ($$typeofType) {
              case REACT_CONTEXT_TYPE:
              case REACT_FORWARD_REF_TYPE:
              case REACT_LAZY_TYPE:
              case REACT_MEMO_TYPE:
              case REACT_PROVIDER_TYPE:
                return $$typeofType;

              default:
                return $$typeof;
            }

        }

      case REACT_PORTAL_TYPE:
        return $$typeof;
    }
  }

  return undefined;
} // AsyncMode is deprecated along with isAsyncMode

var AsyncMode = REACT_ASYNC_MODE_TYPE;
var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
var ContextConsumer = REACT_CONTEXT_TYPE;
var ContextProvider = REACT_PROVIDER_TYPE;
var Element = REACT_ELEMENT_TYPE;
var ForwardRef = REACT_FORWARD_REF_TYPE;
var Fragment = REACT_FRAGMENT_TYPE;
var Lazy = REACT_LAZY_TYPE;
var Memo = REACT_MEMO_TYPE;
var Portal = REACT_PORTAL_TYPE;
var Profiler = REACT_PROFILER_TYPE;
var StrictMode = REACT_STRICT_MODE_TYPE;
var Suspense = REACT_SUSPENSE_TYPE;
var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

function isAsyncMode(object) {
  {
    if (!hasWarnedAboutDeprecatedIsAsyncMode) {
      hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

      console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
    }
  }

  return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
}
function isConcurrentMode(object) {
  return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
}
function isContextConsumer(object) {
  return typeOf(object) === REACT_CONTEXT_TYPE;
}
function isContextProvider(object) {
  return typeOf(object) === REACT_PROVIDER_TYPE;
}
function isElement(object) {
  return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
}
function isForwardRef(object) {
  return typeOf(object) === REACT_FORWARD_REF_TYPE;
}
function isFragment(object) {
  return typeOf(object) === REACT_FRAGMENT_TYPE;
}
function isLazy(object) {
  return typeOf(object) === REACT_LAZY_TYPE;
}
function isMemo(object) {
  return typeOf(object) === REACT_MEMO_TYPE;
}
function isPortal(object) {
  return typeOf(object) === REACT_PORTAL_TYPE;
}
function isProfiler(object) {
  return typeOf(object) === REACT_PROFILER_TYPE;
}
function isStrictMode(object) {
  return typeOf(object) === REACT_STRICT_MODE_TYPE;
}
function isSuspense(object) {
  return typeOf(object) === REACT_SUSPENSE_TYPE;
}

exports.AsyncMode = AsyncMode;
exports.ConcurrentMode = ConcurrentMode;
exports.ContextConsumer = ContextConsumer;
exports.ContextProvider = ContextProvider;
exports.Element = Element;
exports.ForwardRef = ForwardRef;
exports.Fragment = Fragment;
exports.Lazy = Lazy;
exports.Memo = Memo;
exports.Portal = Portal;
exports.Profiler = Profiler;
exports.StrictMode = StrictMode;
exports.Suspense = Suspense;
exports.isAsyncMode = isAsyncMode;
exports.isConcurrentMode = isConcurrentMode;
exports.isContextConsumer = isContextConsumer;
exports.isContextProvider = isContextProvider;
exports.isElement = isElement;
exports.isForwardRef = isForwardRef;
exports.isFragment = isFragment;
exports.isLazy = isLazy;
exports.isMemo = isMemo;
exports.isPortal = isPortal;
exports.isProfiler = isProfiler;
exports.isStrictMode = isStrictMode;
exports.isSuspense = isSuspense;
exports.isValidElementType = isValidElementType;
exports.typeOf = typeOf;
  })();
}
});

var reactIs = createCommonjsModule(function (module) {

if (process.env.NODE_ENV === 'production') {
  module.exports = reactIs_production_min;
} else {
  module.exports = reactIs_development;
}
});

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/
/* eslint-disable no-unused-vars */
var getOwnPropertySymbols = Object.getOwnPropertySymbols;
var hasOwnProperty = Object.prototype.hasOwnProperty;
var propIsEnumerable = Object.prototype.propertyIsEnumerable;

function toObject(val) {
	if (val === null || val === undefined) {
		throw new TypeError('Object.assign cannot be called with null or undefined');
	}

	return Object(val);
}

function shouldUseNative() {
	try {
		if (!Object.assign) {
			return false;
		}

		// Detect buggy property enumeration order in older V8 versions.

		// https://bugs.chromium.org/p/v8/issues/detail?id=4118
		var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
		test1[5] = 'de';
		if (Object.getOwnPropertyNames(test1)[0] === '5') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test2 = {};
		for (var i = 0; i < 10; i++) {
			test2['_' + String.fromCharCode(i)] = i;
		}
		var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
			return test2[n];
		});
		if (order2.join('') !== '0123456789') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test3 = {};
		'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
			test3[letter] = letter;
		});
		if (Object.keys(Object.assign({}, test3)).join('') !==
				'abcdefghijklmnopqrst') {
			return false;
		}

		return true;
	} catch (err) {
		// We don't expect any of the above to throw, but better to be safe.
		return false;
	}
}

var objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
	var from;
	var to = toObject(target);
	var symbols;

	for (var s = 1; s < arguments.length; s++) {
		from = Object(arguments[s]);

		for (var key in from) {
			if (hasOwnProperty.call(from, key)) {
				to[key] = from[key];
			}
		}

		if (getOwnPropertySymbols) {
			symbols = getOwnPropertySymbols(from);
			for (var i = 0; i < symbols.length; i++) {
				if (propIsEnumerable.call(from, symbols[i])) {
					to[symbols[i]] = from[symbols[i]];
				}
			}
		}
	}

	return to;
};

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

var ReactPropTypesSecret_1 = ReactPropTypesSecret;

var printWarning = function() {};

if (process.env.NODE_ENV !== 'production') {
  var ReactPropTypesSecret$1 = ReactPropTypesSecret_1;
  var loggedTypeFailures = {};
  var has = Function.call.bind(Object.prototype.hasOwnProperty);

  printWarning = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

/**
 * Assert that the values match with the type specs.
 * Error messages are memorized and will only be shown once.
 *
 * @param {object} typeSpecs Map of name to a ReactPropType
 * @param {object} values Runtime values that need to be type-checked
 * @param {string} location e.g. "prop", "context", "child context"
 * @param {string} componentName Name of the component for error messages.
 * @param {?Function} getStack Returns the component stack.
 * @private
 */
function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
  if (process.env.NODE_ENV !== 'production') {
    for (var typeSpecName in typeSpecs) {
      if (has(typeSpecs, typeSpecName)) {
        var error;
        // Prop type validation may throw. In case they do, we don't want to
        // fail the render phase where it didn't fail before. So we log it.
        // After these have been cleaned up, we'll let them throw.
        try {
          // This is intentionally an invariant that gets caught. It's the same
          // behavior as without this statement except with a better message.
          if (typeof typeSpecs[typeSpecName] !== 'function') {
            var err = Error(
              (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
              'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.'
            );
            err.name = 'Invariant Violation';
            throw err;
          }
          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret$1);
        } catch (ex) {
          error = ex;
        }
        if (error && !(error instanceof Error)) {
          printWarning(
            (componentName || 'React class') + ': type specification of ' +
            location + ' `' + typeSpecName + '` is invalid; the type checker ' +
            'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
            'You may have forgotten to pass an argument to the type checker ' +
            'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
            'shape all require an argument).'
          );
        }
        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
          // Only monitor this failure once because there tends to be a lot of the
          // same error.
          loggedTypeFailures[error.message] = true;

          var stack = getStack ? getStack() : '';

          printWarning(
            'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
          );
        }
      }
    }
  }
}

/**
 * Resets warning cache when testing.
 *
 * @private
 */
checkPropTypes.resetWarningCache = function() {
  if (process.env.NODE_ENV !== 'production') {
    loggedTypeFailures = {};
  }
};

var checkPropTypes_1 = checkPropTypes;

var has$1 = Function.call.bind(Object.prototype.hasOwnProperty);
var printWarning$1 = function() {};

if (process.env.NODE_ENV !== 'production') {
  printWarning$1 = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

function emptyFunctionThatReturnsNull() {
  return null;
}

var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
  /* global Symbol */
  var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
  var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

  /**
   * Returns the iterator method function contained on the iterable object.
   *
   * Be sure to invoke the function with the iterable as context:
   *
   *     var iteratorFn = getIteratorFn(myIterable);
   *     if (iteratorFn) {
   *       var iterator = iteratorFn.call(myIterable);
   *       ...
   *     }
   *
   * @param {?object} maybeIterable
   * @return {?function}
   */
  function getIteratorFn(maybeIterable) {
    var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
    if (typeof iteratorFn === 'function') {
      return iteratorFn;
    }
  }

  /**
   * Collection of methods that allow declaration and validation of props that are
   * supplied to React components. Example usage:
   *
   *   var Props = require('ReactPropTypes');
   *   var MyArticle = React.createClass({
   *     propTypes: {
   *       // An optional string prop named "description".
   *       description: Props.string,
   *
   *       // A required enum prop named "category".
   *       category: Props.oneOf(['News','Photos']).isRequired,
   *
   *       // A prop named "dialog" that requires an instance of Dialog.
   *       dialog: Props.instanceOf(Dialog).isRequired
   *     },
   *     render: function() { ... }
   *   });
   *
   * A more formal specification of how these methods are used:
   *
   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
   *   decl := ReactPropTypes.{type}(.isRequired)?
   *
   * Each and every declaration produces a function with the same signature. This
   * allows the creation of custom validation functions. For example:
   *
   *  var MyLink = React.createClass({
   *    propTypes: {
   *      // An optional string or URI prop named "href".
   *      href: function(props, propName, componentName) {
   *        var propValue = props[propName];
   *        if (propValue != null && typeof propValue !== 'string' &&
   *            !(propValue instanceof URI)) {
   *          return new Error(
   *            'Expected a string or an URI for ' + propName + ' in ' +
   *            componentName
   *          );
   *        }
   *      }
   *    },
   *    render: function() {...}
   *  });
   *
   * @internal
   */

  var ANONYMOUS = '<<anonymous>>';

  // Important!
  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
  var ReactPropTypes = {
    array: createPrimitiveTypeChecker('array'),
    bool: createPrimitiveTypeChecker('boolean'),
    func: createPrimitiveTypeChecker('function'),
    number: createPrimitiveTypeChecker('number'),
    object: createPrimitiveTypeChecker('object'),
    string: createPrimitiveTypeChecker('string'),
    symbol: createPrimitiveTypeChecker('symbol'),

    any: createAnyTypeChecker(),
    arrayOf: createArrayOfTypeChecker,
    element: createElementTypeChecker(),
    elementType: createElementTypeTypeChecker(),
    instanceOf: createInstanceTypeChecker,
    node: createNodeChecker(),
    objectOf: createObjectOfTypeChecker,
    oneOf: createEnumTypeChecker,
    oneOfType: createUnionTypeChecker,
    shape: createShapeTypeChecker,
    exact: createStrictShapeTypeChecker,
  };

  /**
   * inlined Object.is polyfill to avoid requiring consumers ship their own
   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
   */
  /*eslint-disable no-self-compare*/
  function is(x, y) {
    // SameValue algorithm
    if (x === y) {
      // Steps 1-5, 7-10
      // Steps 6.b-6.e: +0 != -0
      return x !== 0 || 1 / x === 1 / y;
    } else {
      // Step 6.a: NaN == NaN
      return x !== x && y !== y;
    }
  }
  /*eslint-enable no-self-compare*/

  /**
   * We use an Error-like object for backward compatibility as people may call
   * PropTypes directly and inspect their output. However, we don't use real
   * Errors anymore. We don't inspect their stack anyway, and creating them
   * is prohibitively expensive if they are created too often, such as what
   * happens in oneOfType() for any type before the one that matched.
   */
  function PropTypeError(message) {
    this.message = message;
    this.stack = '';
  }
  // Make `instanceof Error` still work for returned errors.
  PropTypeError.prototype = Error.prototype;

  function createChainableTypeChecker(validate) {
    if (process.env.NODE_ENV !== 'production') {
      var manualPropTypeCallCache = {};
      var manualPropTypeWarningCount = 0;
    }
    function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
      componentName = componentName || ANONYMOUS;
      propFullName = propFullName || propName;

      if (secret !== ReactPropTypesSecret_1) {
        if (throwOnDirectAccess) {
          // New behavior only for users of `prop-types` package
          var err = new Error(
            'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
            'Use `PropTypes.checkPropTypes()` to call them. ' +
            'Read more at http://fb.me/use-check-prop-types'
          );
          err.name = 'Invariant Violation';
          throw err;
        } else if (process.env.NODE_ENV !== 'production' && typeof console !== 'undefined') {
          // Old behavior for people using React.PropTypes
          var cacheKey = componentName + ':' + propName;
          if (
            !manualPropTypeCallCache[cacheKey] &&
            // Avoid spamming the console because they are often not actionable except for lib authors
            manualPropTypeWarningCount < 3
          ) {
            printWarning$1(
              'You are manually calling a React.PropTypes validation ' +
              'function for the `' + propFullName + '` prop on `' + componentName  + '`. This is deprecated ' +
              'and will throw in the standalone `prop-types` package. ' +
              'You may be seeing this warning due to a third-party PropTypes ' +
              'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
            );
            manualPropTypeCallCache[cacheKey] = true;
            manualPropTypeWarningCount++;
          }
        }
      }
      if (props[propName] == null) {
        if (isRequired) {
          if (props[propName] === null) {
            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
          }
          return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
        }
        return null;
      } else {
        return validate(props, propName, componentName, location, propFullName);
      }
    }

    var chainedCheckType = checkType.bind(null, false);
    chainedCheckType.isRequired = checkType.bind(null, true);

    return chainedCheckType;
  }

  function createPrimitiveTypeChecker(expectedType) {
    function validate(props, propName, componentName, location, propFullName, secret) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== expectedType) {
        // `propValue` being instance of, say, date/regexp, pass the 'object'
        // check, but we can offer a more precise error message here rather than
        // 'of type `object`'.
        var preciseType = getPreciseType(propValue);

        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createAnyTypeChecker() {
    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
  }

  function createArrayOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
      }
      var propValue = props[propName];
      if (!Array.isArray(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
      }
      for (var i = 0; i < propValue.length; i++) {
        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret_1);
        if (error instanceof Error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!isValidElement(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!reactIs.isValidElementType(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createInstanceTypeChecker(expectedClass) {
    function validate(props, propName, componentName, location, propFullName) {
      if (!(props[propName] instanceof expectedClass)) {
        var expectedClassName = expectedClass.name || ANONYMOUS;
        var actualClassName = getClassName(props[propName]);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createEnumTypeChecker(expectedValues) {
    if (!Array.isArray(expectedValues)) {
      if (process.env.NODE_ENV !== 'production') {
        if (arguments.length > 1) {
          printWarning$1(
            'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
            'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
          );
        } else {
          printWarning$1('Invalid argument supplied to oneOf, expected an array.');
        }
      }
      return emptyFunctionThatReturnsNull;
    }

    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      for (var i = 0; i < expectedValues.length; i++) {
        if (is(propValue, expectedValues[i])) {
          return null;
        }
      }

      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
        var type = getPreciseType(value);
        if (type === 'symbol') {
          return String(value);
        }
        return value;
      });
      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createObjectOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
      }
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
      }
      for (var key in propValue) {
        if (has$1(propValue, key)) {
          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
          if (error instanceof Error) {
            return error;
          }
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createUnionTypeChecker(arrayOfTypeCheckers) {
    if (!Array.isArray(arrayOfTypeCheckers)) {
      process.env.NODE_ENV !== 'production' ? printWarning$1('Invalid argument supplied to oneOfType, expected an instance of array.') : void 0;
      return emptyFunctionThatReturnsNull;
    }

    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
      var checker = arrayOfTypeCheckers[i];
      if (typeof checker !== 'function') {
        printWarning$1(
          'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
          'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
        );
        return emptyFunctionThatReturnsNull;
      }
    }

    function validate(props, propName, componentName, location, propFullName) {
      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
        var checker = arrayOfTypeCheckers[i];
        if (checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret_1) == null) {
          return null;
        }
      }

      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createNodeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      if (!isNode(props[propName])) {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      for (var key in shapeTypes) {
        var checker = shapeTypes[key];
        if (!checker) {
          continue;
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createStrictShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      // We need to check all keys in case some are required but missing from
      // props.
      var allKeys = objectAssign({}, props[propName], shapeTypes);
      for (var key in allKeys) {
        var checker = shapeTypes[key];
        if (!checker) {
          return new PropTypeError(
            'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
            '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
            '\nValid keys: ' +  JSON.stringify(Object.keys(shapeTypes), null, '  ')
          );
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }

    return createChainableTypeChecker(validate);
  }

  function isNode(propValue) {
    switch (typeof propValue) {
      case 'number':
      case 'string':
      case 'undefined':
        return true;
      case 'boolean':
        return !propValue;
      case 'object':
        if (Array.isArray(propValue)) {
          return propValue.every(isNode);
        }
        if (propValue === null || isValidElement(propValue)) {
          return true;
        }

        var iteratorFn = getIteratorFn(propValue);
        if (iteratorFn) {
          var iterator = iteratorFn.call(propValue);
          var step;
          if (iteratorFn !== propValue.entries) {
            while (!(step = iterator.next()).done) {
              if (!isNode(step.value)) {
                return false;
              }
            }
          } else {
            // Iterator will provide entry [k,v] tuples rather than values.
            while (!(step = iterator.next()).done) {
              var entry = step.value;
              if (entry) {
                if (!isNode(entry[1])) {
                  return false;
                }
              }
            }
          }
        } else {
          return false;
        }

        return true;
      default:
        return false;
    }
  }

  function isSymbol(propType, propValue) {
    // Native Symbol.
    if (propType === 'symbol') {
      return true;
    }

    // falsy value can't be a Symbol
    if (!propValue) {
      return false;
    }

    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
    if (propValue['@@toStringTag'] === 'Symbol') {
      return true;
    }

    // Fallback for non-spec compliant Symbols which are polyfilled.
    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
      return true;
    }

    return false;
  }

  // Equivalent of `typeof` but with special handling for array and regexp.
  function getPropType(propValue) {
    var propType = typeof propValue;
    if (Array.isArray(propValue)) {
      return 'array';
    }
    if (propValue instanceof RegExp) {
      // Old webkits (at least until Android 4.0) return 'function' rather than
      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
      // passes PropTypes.object.
      return 'object';
    }
    if (isSymbol(propType, propValue)) {
      return 'symbol';
    }
    return propType;
  }

  // This handles more types than `getPropType`. Only used for error messages.
  // See `createPrimitiveTypeChecker`.
  function getPreciseType(propValue) {
    if (typeof propValue === 'undefined' || propValue === null) {
      return '' + propValue;
    }
    var propType = getPropType(propValue);
    if (propType === 'object') {
      if (propValue instanceof Date) {
        return 'date';
      } else if (propValue instanceof RegExp) {
        return 'regexp';
      }
    }
    return propType;
  }

  // Returns a string that is postfixed to a warning about an invalid type.
  // For example, "undefined" or "of type array"
  function getPostfixForTypeWarning(value) {
    var type = getPreciseType(value);
    switch (type) {
      case 'array':
      case 'object':
        return 'an ' + type;
      case 'boolean':
      case 'date':
      case 'regexp':
        return 'a ' + type;
      default:
        return type;
    }
  }

  // Returns class name of the object, if any.
  function getClassName(propValue) {
    if (!propValue.constructor || !propValue.constructor.name) {
      return ANONYMOUS;
    }
    return propValue.constructor.name;
  }

  ReactPropTypes.checkPropTypes = checkPropTypes_1;
  ReactPropTypes.resetWarningCache = checkPropTypes_1.resetWarningCache;
  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

function emptyFunction() {}
function emptyFunctionWithReset() {}
emptyFunctionWithReset.resetWarningCache = emptyFunction;

var factoryWithThrowingShims = function() {
  function shim(props, propName, componentName, location, propFullName, secret) {
    if (secret === ReactPropTypesSecret_1) {
      // It is still safe when called from React.
      return;
    }
    var err = new Error(
      'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
      'Use PropTypes.checkPropTypes() to call them. ' +
      'Read more at http://fb.me/use-check-prop-types'
    );
    err.name = 'Invariant Violation';
    throw err;
  }  shim.isRequired = shim;
  function getShim() {
    return shim;
  }  // Important!
  // Keep this list in sync with production version in `./factoryWithTypeCheckers.js`.
  var ReactPropTypes = {
    array: shim,
    bool: shim,
    func: shim,
    number: shim,
    object: shim,
    string: shim,
    symbol: shim,

    any: shim,
    arrayOf: getShim,
    element: shim,
    elementType: shim,
    instanceOf: getShim,
    node: shim,
    objectOf: getShim,
    oneOf: getShim,
    oneOfType: getShim,
    shape: getShim,
    exact: getShim,

    checkPropTypes: emptyFunctionWithReset,
    resetWarningCache: emptyFunction
  };

  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

var propTypes = createCommonjsModule(function (module) {
/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

if (process.env.NODE_ENV !== 'production') {
  var ReactIs = reactIs;

  // By explicitly using `prop-types` you are opting into new development behavior.
  // http://fb.me/prop-types-in-prod
  var throwOnDirectAccess = true;
  module.exports = factoryWithTypeCheckers(ReactIs.isElement, throwOnDirectAccess);
} else {
  // By explicitly using `prop-types` you are opting into new production behavior.
  // http://fb.me/prop-types-in-prod
  module.exports = factoryWithThrowingShims();
}
});

var DomHandler = /*#__PURE__*/function () {
  function DomHandler() {}

  DomHandler.innerWidth = function innerWidth(el) {
    if (el) {
      var width = el.offsetWidth;
      var style = getComputedStyle(el);
      width += parseFloat(style.paddingLeft) + parseFloat(style.paddingRight);
      return width;
    }

    return 0;
  };

  DomHandler.width = function width(el) {
    if (el) {
      var width = el.offsetWidth;
      var style = getComputedStyle(el);
      width -= parseFloat(style.paddingLeft) + parseFloat(style.paddingRight);
      return width;
    }

    return 0;
  };

  DomHandler.getWindowScrollTop = function getWindowScrollTop() {
    var doc = document.documentElement;
    return (window.pageYOffset || doc.scrollTop) - (doc.clientTop || 0);
  };

  DomHandler.getWindowScrollLeft = function getWindowScrollLeft() {
    var doc = document.documentElement;
    return (window.pageXOffset || doc.scrollLeft) - (doc.clientLeft || 0);
  };

  DomHandler.getOuterWidth = function getOuterWidth(el, margin) {
    if (el) {
      var width = el.offsetWidth;

      if (margin) {
        var style = getComputedStyle(el);
        width += parseFloat(style.marginLeft) + parseFloat(style.marginRight);
      }

      return width;
    }

    return 0;
  };

  DomHandler.getOuterHeight = function getOuterHeight(el, margin) {
    if (el) {
      var height = el.offsetHeight;

      if (margin) {
        var style = getComputedStyle(el);
        height += parseFloat(style.marginTop) + parseFloat(style.marginBottom);
      }

      return height;
    }

    return 0;
  };

  DomHandler.getClientHeight = function getClientHeight(el, margin) {
    if (el) {
      var height = el.clientHeight;

      if (margin) {
        var style = getComputedStyle(el);
        height += parseFloat(style.marginTop) + parseFloat(style.marginBottom);
      }

      return height;
    }

    return 0;
  };

  DomHandler.getViewport = function getViewport() {
    var win = window,
        d = document,
        e = d.documentElement,
        g = d.getElementsByTagName('body')[0],
        w = win.innerWidth || e.clientWidth || g.clientWidth,
        h = win.innerHeight || e.clientHeight || g.clientHeight;
    return {
      width: w,
      height: h
    };
  };

  DomHandler.getOffset = function getOffset(el) {
    if (el) {
      var rect = el.getBoundingClientRect();
      return {
        top: rect.top + document.body.scrollTop,
        left: rect.left + document.body.scrollLeft
      };
    }

    return {
      top: 'auto',
      left: 'auto'
    };
  };

  DomHandler.generateZIndex = function generateZIndex() {
    this.zindex = this.zindex || 999;
    return ++this.zindex;
  };

  DomHandler.getCurrentZIndex = function getCurrentZIndex() {
    return this.zindex;
  };

  DomHandler.index = function index(element) {
    if (element) {
      var children = element.parentNode.childNodes;
      var num = 0;

      for (var i = 0; i < children.length; i++) {
        if (children[i] === element) return num;
        if (children[i].nodeType === 1) num++;
      }
    }

    return -1;
  };

  DomHandler.addMultipleClasses = function addMultipleClasses(element, className) {
    if (element) {
      if (element.classList) {
        var styles = className.split(' ');

        for (var i = 0; i < styles.length; i++) {
          element.classList.add(styles[i]);
        }
      } else {
        var _styles = className.split(' ');

        for (var _i = 0; _i < _styles.length; _i++) {
          element.className += ' ' + _styles[_i];
        }
      }
    }
  };

  DomHandler.addClass = function addClass(element, className) {
    if (element) {
      if (element.classList) element.classList.add(className);else element.className += ' ' + className;
    }
  };

  DomHandler.removeClass = function removeClass(element, className) {
    if (element) {
      if (element.classList) element.classList.remove(className);else element.className = element.className.replace(new RegExp('(^|\\b)' + className.split(' ').join('|') + '(\\b|$)', 'gi'), ' ');
    }
  };

  DomHandler.hasClass = function hasClass(element, className) {
    if (element) {
      if (element.classList) return element.classList.contains(className);else return new RegExp('(^| )' + className + '( |$)', 'gi').test(element.className);
    }
  };

  DomHandler.find = function find(element, selector) {
    return element ? Array.from(element.querySelectorAll(selector)) : [];
  };

  DomHandler.findSingle = function findSingle(element, selector) {
    if (element) {
      return element.querySelector(selector);
    }

    return null;
  };

  DomHandler.getHeight = function getHeight(el) {
    if (el) {
      var height = el.offsetHeight;
      var style = getComputedStyle(el);
      height -= parseFloat(style.paddingTop) + parseFloat(style.paddingBottom) + parseFloat(style.borderTopWidth) + parseFloat(style.borderBottomWidth);
      return height;
    }

    return 0;
  };

  DomHandler.getWidth = function getWidth(el) {
    if (el) {
      var width = el.offsetWidth;
      var style = getComputedStyle(el);
      width -= parseFloat(style.paddingLeft) + parseFloat(style.paddingRight) + parseFloat(style.borderLeftWidth) + parseFloat(style.borderRightWidth);
      return width;
    }

    return 0;
  };

  DomHandler.absolutePosition = function absolutePosition(element, target) {
    if (element) {
      var elementDimensions = element.offsetParent ? {
        width: element.offsetWidth,
        height: element.offsetHeight
      } : this.getHiddenElementDimensions(element);
      var elementOuterHeight = elementDimensions.height;
      var elementOuterWidth = elementDimensions.width;
      var targetOuterHeight = target.offsetHeight;
      var targetOuterWidth = target.offsetWidth;
      var targetOffset = target.getBoundingClientRect();
      var windowScrollTop = this.getWindowScrollTop();
      var windowScrollLeft = this.getWindowScrollLeft();
      var viewport = this.getViewport();
      var top, left;

      if (targetOffset.top + targetOuterHeight + elementOuterHeight > viewport.height) {
        top = targetOffset.top + windowScrollTop - elementOuterHeight;

        if (top < 0) {
          top = windowScrollTop;
        }
      } else {
        top = targetOuterHeight + targetOffset.top + windowScrollTop;
      }

      if (targetOffset.left + targetOuterWidth + elementOuterWidth > viewport.width) left = Math.max(0, targetOffset.left + windowScrollLeft + targetOuterWidth - elementOuterWidth);else left = targetOffset.left + windowScrollLeft;
      element.style.top = top + 'px';
      element.style.left = left + 'px';
    }
  };

  DomHandler.relativePosition = function relativePosition(element, target) {
    if (element) {
      var elementDimensions = element.offsetParent ? {
        width: element.offsetWidth,
        height: element.offsetHeight
      } : this.getHiddenElementDimensions(element);
      var targetHeight = target.offsetHeight;
      var targetOffset = target.getBoundingClientRect();
      var viewport = this.getViewport();
      var top, left;

      if (targetOffset.top + targetHeight + elementDimensions.height > viewport.height) {
        top = -1 * elementDimensions.height;

        if (targetOffset.top + top < 0) {
          top = -1 * targetOffset.top;
        }
      } else {
        top = targetHeight;
      }

      if (elementDimensions.width > viewport.width) {
        left = targetOffset.left * -1;
      } else if (targetOffset.left + elementDimensions.width > viewport.width) {
        left = (targetOffset.left + elementDimensions.width - viewport.width) * -1;
      } else {
        left = 0;
      }

      element.style.top = top + 'px';
      element.style.left = left + 'px';
    }
  };

  DomHandler.getHiddenElementOuterHeight = function getHiddenElementOuterHeight(element) {
    if (element) {
      element.style.visibility = 'hidden';
      element.style.display = 'block';
      var elementHeight = element.offsetHeight;
      element.style.display = 'none';
      element.style.visibility = 'visible';
      return elementHeight;
    }

    return 0;
  };

  DomHandler.getHiddenElementOuterWidth = function getHiddenElementOuterWidth(element) {
    if (element) {
      element.style.visibility = 'hidden';
      element.style.display = 'block';
      var elementWidth = element.offsetWidth;
      element.style.display = 'none';
      element.style.visibility = 'visible';
      return elementWidth;
    }

    return 0;
  };

  DomHandler.getHiddenElementDimensions = function getHiddenElementDimensions(element) {
    var dimensions = {};

    if (element) {
      element.style.visibility = 'hidden';
      element.style.display = 'block';
      dimensions.width = element.offsetWidth;
      dimensions.height = element.offsetHeight;
      element.style.display = 'none';
      element.style.visibility = 'visible';
    }

    return dimensions;
  };

  DomHandler.fadeIn = function fadeIn(element, duration) {
    if (element) {
      element.style.opacity = 0;
      var last = +new Date();
      var opacity = 0;

      var tick = function tick() {
        opacity = +element.style.opacity + (new Date().getTime() - last) / duration;
        element.style.opacity = opacity;
        last = +new Date();

        if (+opacity < 1) {
          window.requestAnimationFrame && requestAnimationFrame(tick) || setTimeout(tick, 16);
        }
      };

      tick();
    }
  };

  DomHandler.fadeOut = function fadeOut(element, ms) {
    if (element) {
      var opacity = 1,
          interval = 50,
          duration = ms,
          gap = interval / duration;
      var fading = setInterval(function () {
        opacity -= gap;

        if (opacity <= 0) {
          opacity = 0;
          clearInterval(fading);
        }

        element.style.opacity = opacity;
      }, interval);
    }
  };

  DomHandler.getUserAgent = function getUserAgent() {
    return navigator.userAgent;
  };

  DomHandler.isIOS = function isIOS() {
    return /iPad|iPhone|iPod/.test(navigator.userAgent) && !window['MSStream'];
  };

  DomHandler.isAndroid = function isAndroid() {
    return /(android)/i.test(navigator.userAgent);
  };

  DomHandler.appendChild = function appendChild(element, target) {
    if (this.isElement(target)) target.appendChild(element);else if (target.el && target.el.nativeElement) target.el.nativeElement.appendChild(element);else throw new Error('Cannot append ' + target + ' to ' + element);
  };

  DomHandler.scrollInView = function scrollInView(container, item) {
    var borderTopValue = getComputedStyle(container).getPropertyValue('borderTopWidth');
    var borderTop = borderTopValue ? parseFloat(borderTopValue) : 0;
    var paddingTopValue = getComputedStyle(container).getPropertyValue('paddingTop');
    var paddingTop = paddingTopValue ? parseFloat(paddingTopValue) : 0;
    var containerRect = container.getBoundingClientRect();
    var itemRect = item.getBoundingClientRect();
    var offset = itemRect.top + document.body.scrollTop - (containerRect.top + document.body.scrollTop) - borderTop - paddingTop;
    var scroll = container.scrollTop;
    var elementHeight = container.clientHeight;
    var itemHeight = this.getOuterHeight(item);

    if (offset < 0) {
      container.scrollTop = scroll + offset;
    } else if (offset + itemHeight > elementHeight) {
      container.scrollTop = scroll + offset - elementHeight + itemHeight;
    }
  };

  DomHandler.clearSelection = function clearSelection() {
    if (window.getSelection) {
      if (window.getSelection().empty) {
        window.getSelection().empty();
      } else if (window.getSelection().removeAllRanges && window.getSelection().rangeCount > 0 && window.getSelection().getRangeAt(0).getClientRects().length > 0) {
        window.getSelection().removeAllRanges();
      }
    } else if (document['selection'] && document['selection'].empty) {
      try {
        document['selection'].empty();
      } catch (error) {}
    }
  };

  DomHandler.calculateScrollbarWidth = function calculateScrollbarWidth(el) {
    if (el) {
      var style = getComputedStyle(el);
      return el.offsetWidth - el.clientWidth - parseFloat(style.borderLeftWidth) - parseFloat(style.borderRightWidth);
    } else {
      if (this.calculatedScrollbarWidth != null) return this.calculatedScrollbarWidth;
      var scrollDiv = document.createElement("div");
      scrollDiv.className = "p-scrollbar-measure";
      document.body.appendChild(scrollDiv);
      var scrollbarWidth = scrollDiv.offsetWidth - scrollDiv.clientWidth;
      document.body.removeChild(scrollDiv);
      this.calculatedScrollbarWidth = scrollbarWidth;
      return scrollbarWidth;
    }
  };

  DomHandler.getBrowser = function getBrowser() {
    if (!this.browser) {
      var matched = this.resolveUserAgent();
      this.browser = {};

      if (matched.browser) {
        this.browser[matched.browser] = true;
        this.browser['version'] = matched.version;
      }

      if (this.browser['chrome']) {
        this.browser['webkit'] = true;
      } else if (this.browser['webkit']) {
        this.browser['safari'] = true;
      }
    }

    return this.browser;
  };

  DomHandler.resolveUserAgent = function resolveUserAgent() {
    var ua = navigator.userAgent.toLowerCase();
    var match = /(chrome)[ ]([\w.]+)/.exec(ua) || /(webkit)[ ]([\w.]+)/.exec(ua) || /(opera)(?:.*version|)[ ]([\w.]+)/.exec(ua) || /(msie) ([\w.]+)/.exec(ua) || ua.indexOf("compatible") < 0 && /(mozilla)(?:.*? rv:([\w.]+)|)/.exec(ua) || [];
    return {
      browser: match[1] || "",
      version: match[2] || "0"
    };
  };

  DomHandler.isVisible = function isVisible(element) {
    return element && element.offsetParent != null;
  };

  DomHandler.getFocusableElements = function getFocusableElements(element) {
    var focusableElements = DomHandler.find(element, "button:not([tabindex = \"-1\"]):not([disabled]):not([style*=\"display:none\"]):not([hidden]), \n                [href][clientHeight][clientWidth]:not([tabindex = \"-1\"]):not([disabled]):not([style*=\"display:none\"]):not([hidden]), \n                input:not([tabindex = \"-1\"]):not([disabled]):not([style*=\"display:none\"]):not([hidden]), select:not([tabindex = \"-1\"]):not([disabled]):not([style*=\"display:none\"]):not([hidden]), \n                textarea:not([tabindex = \"-1\"]):not([disabled]):not([style*=\"display:none\"]):not([hidden]), [tabIndex]:not([tabIndex = \"-1\"]):not([disabled]):not([style*=\"display:none\"]):not([hidden]), \n                [contenteditable]:not([tabIndex = \"-1\"]):not([disabled]):not([style*=\"display:none\"]):not([hidden])");
    var visibleFocusableElements = [];

    for (var _iterator = _createForOfIteratorHelperLoose(focusableElements), _step; !(_step = _iterator()).done;) {
      var focusableElement = _step.value;
      if (getComputedStyle(focusableElement).display !== "none" && getComputedStyle(focusableElement).visibility !== "hidden") visibleFocusableElements.push(focusableElement);
    }

    return visibleFocusableElements;
  };

  return DomHandler;
}();

var KeyFilter = /*#__PURE__*/function () {
  function KeyFilter() {}

  KeyFilter.isNavKeyPress = function isNavKeyPress(e) {
    var k = e.keyCode;
    k = DomHandler.getBrowser().safari ? KeyFilter.SAFARI_KEYS[k] || k : k;
    return k >= 33 && k <= 40 || k === KeyFilter.KEYS.RETURN || k === KeyFilter.KEYS.TAB || k === KeyFilter.KEYS.ESC;
  };

  KeyFilter.isSpecialKey = function isSpecialKey(e) {
    var k = e.keyCode;
    return k === 9 || k === 13 || k === 27 || k === 16 || k === 17 || k >= 18 && k <= 20 || DomHandler.getBrowser().opera && !e.shiftKey && (k === 8 || k >= 33 && k <= 35 || k >= 36 && k <= 39 || k >= 44 && k <= 45);
  };

  KeyFilter.getKey = function getKey(e) {
    var k = e.keyCode || e.charCode;
    return DomHandler.getBrowser().safari ? KeyFilter.SAFARI_KEYS[k] || k : k;
  };

  KeyFilter.getCharCode = function getCharCode(e) {
    return e.charCode || e.keyCode || e.which;
  };

  KeyFilter.onKeyPress = function onKeyPress(e, keyfilter, validateOnly) {
    if (validateOnly) {
      return;
    }

    var regex = KeyFilter.DEFAULT_MASKS[keyfilter] ? KeyFilter.DEFAULT_MASKS[keyfilter] : keyfilter;
    var browser = DomHandler.getBrowser();

    if (e.ctrlKey || e.altKey) {
      return;
    }

    var k = this.getKey(e);

    if (browser.mozilla && (this.isNavKeyPress(e) || k === KeyFilter.KEYS.BACKSPACE || k === KeyFilter.KEYS.DELETE && e.charCode === 0)) {
      return;
    }

    var c = this.getCharCode(e);
    var cc = String.fromCharCode(c);

    if (browser.mozilla && (this.isSpecialKey(e) || !cc)) {
      return;
    }

    if (!regex.test(cc)) {
      e.preventDefault();
    }
  };

  KeyFilter.validate = function validate(e, keyfilter) {
    var value = e.target.value,
        validatePattern = true;

    if (value && !keyfilter.test(value)) {
      validatePattern = false;
    }

    return validatePattern;
  };

  return KeyFilter;
}();

KeyFilter.DEFAULT_MASKS = {
  pint: /[\d]/,
  "int": /[\d\-]/,
  pnum: /[\d\.]/,
  money: /[\d\.\s,]/,
  num: /[\d\-\.]/,
  hex: /[0-9a-f]/i,
  email: /[a-z0-9_\.\-@]/i,
  alpha: /[a-z_]/i,
  alphanum: /[a-z0-9_]/i
};
KeyFilter.KEYS = {
  TAB: 9,
  RETURN: 13,
  ESC: 27,
  BACKSPACE: 8,
  DELETE: 46
};
KeyFilter.SAFARI_KEYS = {
  63234: 37,
  63235: 39,
  63232: 38,
  63233: 40,
  63276: 33,
  63277: 34,
  63272: 46,
  63273: 36,
  63275: 35
};

var Tooltip = /*#__PURE__*/function () {
  function Tooltip(props) {
    this.target = props.target;
    this.targetContainer = props.targetContainer;
    this.content = props.content;
    this.options = props.options || {};
    this.options.event = this.options.event || 'hover';
    this.options.position = this.options.position || 'right';
    this.bindEvents();
  }

  var _proto = Tooltip.prototype;

  _proto.bindEvents = function bindEvents() {
    if (this.options.event === 'hover') {
      this.mouseEnterListener = this.onMouseEnter.bind(this);
      this.mouseLeaveListener = this.onMouseLeave.bind(this);
      this.clickListener = this.onClick.bind(this);
      this.target.addEventListener('mouseenter', this.mouseEnterListener);
      this.target.addEventListener('mouseleave', this.mouseLeaveListener);
      this.target.addEventListener('click', this.clickListener);
    } else if (this.options.event === 'focus') {
      this.focusListener = this.onFocus.bind(this);
      this.blurListener = this.onBlur.bind(this);
      this.target.addEventListener('focus', this.focusListener);
      this.target.addEventListener('blur', this.blurListener);
    }
  };

  _proto.unbindEvents = function unbindEvents() {
    if (this.options.event === 'hover') {
      this.target.removeEventListener('mouseenter', this.mouseEnterListener);
      this.target.removeEventListener('mouseleave', this.mouseLeaveListener);
      this.target.removeEventListener('click', this.clickListener);
    } else if (this.options.event === 'focus') {
      this.target.removeEventListener('focus', this.focusListener);
      this.target.removeEventListener('blur', this.blurListener);
    }

    this.unbindDocumentResizeListener();
  };

  _proto.onMouseEnter = function onMouseEnter() {
    if (!this.container && !this.showTimeout) {
      this.activate();
    }
  };

  _proto.onMouseLeave = function onMouseLeave() {
    this.deactivate();
  };

  _proto.onFocus = function onFocus() {
    this.activate();
  };

  _proto.onBlur = function onBlur() {
    this.deactivate();
  };

  _proto.onClick = function onClick() {
    this.deactivate();
  };

  _proto.activate = function activate() {
    var _this = this;

    this.clearHideTimeout();
    if (this.options.showDelay) this.showTimeout = setTimeout(function () {
      _this.show();
    }, this.options.showDelay);else this.show();
  };

  _proto.deactivate = function deactivate() {
    var _this2 = this;

    this.clearShowTimeout();
    if (this.options.hideDelay) this.hideTimeout = setTimeout(function () {
      _this2.hide();
    }, this.options.hideDelay);else this.hide();
  };

  _proto.clearShowTimeout = function clearShowTimeout() {
    if (this.showTimeout) {
      clearTimeout(this.showTimeout);
      this.showTimeout = null;
    }
  };

  _proto.clearHideTimeout = function clearHideTimeout() {
    if (this.hideTimeout) {
      clearTimeout(this.hideTimeout);
      this.hideTimeout = null;
    }
  };

  _proto.clearTimeouts = function clearTimeouts() {
    this.clearShowTimeout();
    this.clearHideTimeout();
  };

  _proto.updateContent = function updateContent(content) {
    this.content = content;
  };

  _proto.show = function show() {
    if (!this.content) {
      return;
    }

    this.create();
    this.align();
    DomHandler.fadeIn(this.container, 250);
    this.container.style.zIndex = ++DomHandler.zindex;
    this.bindDocumentResizeListener();
  };

  _proto.hide = function hide() {
    this.remove();
  };

  _proto.create = function create() {
    this.container = document.createElement('div');
    var tooltipArrow = document.createElement('div');
    tooltipArrow.className = 'p-tooltip-arrow';
    this.container.appendChild(tooltipArrow);
    this.tooltipText = document.createElement('div');
    this.tooltipText.className = 'p-tooltip-text';
    this.tooltipText.innerHTML = this.content;
    this.container.appendChild(this.tooltipText);
    document.body.appendChild(this.container);
    this.container.style.display = 'inline-block';
  };

  _proto.remove = function remove() {
    if (this.container && this.container.parentElement) {
      document.body.removeChild(this.container);
    }

    this.unbindDocumentResizeListener();
    this.clearTimeouts();
    this.container = null;
  };

  _proto.align = function align() {
    switch (this.options.position) {
      case 'top':
        this.alignTop();

        if (this.isOutOfBounds()) {
          this.alignBottom();
        }

        break;

      case 'bottom':
        this.alignBottom();

        if (this.isOutOfBounds()) {
          this.alignTop();
        }

        break;

      case 'left':
        this.alignLeft();

        if (this.isOutOfBounds()) {
          this.alignRight();

          if (this.isOutOfBounds()) {
            this.alignTop();

            if (this.isOutOfBounds()) {
              this.alignBottom();
            }
          }
        }

        break;

      case 'right':
        this.alignRight();

        if (this.isOutOfBounds()) {
          this.alignLeft();

          if (this.isOutOfBounds()) {
            this.alignTop();

            if (this.isOutOfBounds()) {
              this.alignBottom();
            }
          }
        }

        break;

      default:
        throw new Error('Invalid position:' + this.options.position);
    }
  };

  _proto.getHostOffset = function getHostOffset() {
    var target = this.targetContainer || this.target;
    var offset = target.getBoundingClientRect();
    var targetLeft = offset.left + DomHandler.getWindowScrollLeft();
    var targetTop = offset.top + DomHandler.getWindowScrollTop();
    return {
      left: targetLeft,
      top: targetTop
    };
  };

  _proto.alignRight = function alignRight() {
    this.preAlign('right');
    var target = this.targetContainer || this.target;
    var hostOffset = this.getHostOffset();
    var left = hostOffset.left + DomHandler.getOuterWidth(target);
    var top = hostOffset.top + (DomHandler.getOuterHeight(target) - DomHandler.getOuterHeight(this.container)) / 2;
    this.container.style.left = left + 'px';
    this.container.style.top = top + 'px';
  };

  _proto.alignLeft = function alignLeft() {
    this.preAlign('left');
    var target = this.targetContainer || this.target;
    var hostOffset = this.getHostOffset();
    var left = hostOffset.left - DomHandler.getOuterWidth(this.container);
    var top = hostOffset.top + (DomHandler.getOuterHeight(target) - DomHandler.getOuterHeight(this.container)) / 2;
    this.container.style.left = left + 'px';
    this.container.style.top = top + 'px';
  };

  _proto.alignTop = function alignTop() {
    this.preAlign('top');
    var target = this.targetContainer || this.target;
    var hostOffset = this.getHostOffset();
    var left = hostOffset.left + (DomHandler.getOuterWidth(target) - DomHandler.getOuterWidth(this.container)) / 2;
    var top = hostOffset.top - DomHandler.getOuterHeight(this.container);
    this.container.style.left = left + 'px';
    this.container.style.top = top + 'px';
  };

  _proto.alignBottom = function alignBottom() {
    this.preAlign('bottom');
    var target = this.targetContainer || this.target;
    var hostOffset = this.getHostOffset();
    var left = hostOffset.left + (DomHandler.getOuterWidth(target) - DomHandler.getOuterWidth(this.container)) / 2;
    var top = hostOffset.top + DomHandler.getOuterHeight(target);
    this.container.style.left = left + 'px';
    this.container.style.top = top + 'px';
  };

  _proto.preAlign = function preAlign(position) {
    this.container.style.left = -999 + 'px';
    this.container.style.top = -999 + 'px';
    var defaultClassName = 'p-tooltip p-component p-tooltip-' + position;
    this.container.className = this.options.className ? defaultClassName + ' ' + this.options.className : defaultClassName;
  };

  _proto.isOutOfBounds = function isOutOfBounds() {
    var offset = this.container.getBoundingClientRect();
    var targetTop = offset.top;
    var targetLeft = offset.left;
    var width = DomHandler.getOuterWidth(this.container);
    var height = DomHandler.getOuterHeight(this.container);
    var viewport = DomHandler.getViewport();
    return targetLeft + width > viewport.width || targetLeft < 0 || targetTop < 0 || targetTop + height > viewport.height;
  };

  _proto.bindDocumentResizeListener = function bindDocumentResizeListener() {
    this.resizeListener = this.onWindowResize.bind(this);
    window.addEventListener('resize', this.resizeListener);
  };

  _proto.unbindDocumentResizeListener = function unbindDocumentResizeListener() {
    if (this.resizeListener) {
      window.removeEventListener('resize', this.resizeListener);
      this.resizeListener = null;
    }
  };

  _proto.onWindowResize = function onWindowResize() {
    this.hide();
  };

  _proto.destroy = function destroy() {
    this.unbindEvents();
    this.remove();
    this.target = null;
    this.targetContainer = null;
  };

  return Tooltip;
}();

var ObjectUtils = /*#__PURE__*/function () {
  function ObjectUtils() {}

  ObjectUtils.equals = function equals(obj1, obj2, field) {
    if (field && obj1 && typeof obj1 === 'object' && obj2 && typeof obj2 === 'object') return this.resolveFieldData(obj1, field) === this.resolveFieldData(obj2, field);else return this.deepEquals(obj1, obj2);
  };

  ObjectUtils.deepEquals = function deepEquals(a, b) {
    if (a === b) return true;

    if (a && b && typeof a == 'object' && typeof b == 'object') {
      var arrA = Array.isArray(a),
          arrB = Array.isArray(b),
          i,
          length,
          key;

      if (arrA && arrB) {
        length = a.length;
        if (length !== b.length) return false;

        for (i = length; i-- !== 0;) {
          if (!this.deepEquals(a[i], b[i])) return false;
        }

        return true;
      }

      if (arrA !== arrB) return false;
      var dateA = a instanceof Date,
          dateB = b instanceof Date;
      if (dateA !== dateB) return false;
      if (dateA && dateB) return a.getTime() === b.getTime();
      var regexpA = a instanceof RegExp,
          regexpB = b instanceof RegExp;
      if (regexpA !== regexpB) return false;
      if (regexpA && regexpB) return a.toString() === b.toString();
      var keys = Object.keys(a);
      length = keys.length;
      if (length !== Object.keys(b).length) return false;

      for (i = length; i-- !== 0;) {
        if (!Object.prototype.hasOwnProperty.call(b, keys[i])) return false;
      }

      for (i = length; i-- !== 0;) {
        key = keys[i];
        if (!this.deepEquals(a[key], b[key])) return false;
      }

      return true;
    }

    return a !== a && b !== b;
  };

  ObjectUtils.resolveFieldData = function resolveFieldData(data, field) {
    if (data && field) {
      if (this.isFunction(field)) {
        return field(data);
      } else if (field.indexOf('.') === -1) {
        return data[field];
      } else {
        var fields = field.split('.');
        var value = data;

        for (var i = 0, len = fields.length; i < len; ++i) {
          if (value == null) {
            return null;
          }

          value = value[fields[i]];
        }

        return value;
      }
    } else {
      return null;
    }
  };

  ObjectUtils.isFunction = function isFunction(obj) {
    return !!(obj && obj.constructor && obj.call && obj.apply);
  };

  ObjectUtils.findDiffKeys = function findDiffKeys(obj1, obj2) {
    if (!obj1 || !obj2) {
      return {};
    }

    return Object.keys(obj1).filter(function (key) {
      return !obj2.hasOwnProperty(key);
    }).reduce(function (result, current) {
      result[current] = obj1[current];
      return result;
    }, {});
  };

  ObjectUtils.reorderArray = function reorderArray(value, from, to) {
    var target;

    if (value && from !== to) {
      if (to >= value.length) {
        target = to - value.length;

        while (target-- + 1) {
          value.push(undefined);
        }
      }

      value.splice(to, 0, value.splice(from, 1)[0]);
    }
  };

  ObjectUtils.findIndexInList = function findIndexInList(value, list) {
    var index = -1;

    if (list) {
      for (var i = 0; i < list.length; i++) {
        if (list[i] === value) {
          index = i;
          break;
        }
      }
    }

    return index;
  };

  ObjectUtils.getJSXElement = function getJSXElement(obj) {
    for (var _len = arguments.length, params = new Array(_len > 1 ? _len - 1 : 0), _key = 1; _key < _len; _key++) {
      params[_key - 1] = arguments[_key];
    }

    return this.isFunction(obj) ? obj.apply(void 0, params) : obj;
  };

  ObjectUtils.removeAccents = function removeAccents(str) {
    if (str && str.search(/[\xC0-\xFF]/g) > -1) {
      str = str.replace(/[\xC0-\xC5]/g, "A").replace(/[\xC6]/g, "AE").replace(/[\xC7]/g, "C").replace(/[\xC8-\xCB]/g, "E").replace(/[\xCC-\xCF]/g, "I").replace(/[\xD0]/g, "D").replace(/[\xD1]/g, "N").replace(/[\xD2-\xD6\xD8]/g, "O").replace(/[\xD9-\xDC]/g, "U").replace(/[\xDD]/g, "Y").replace(/[\xDE]/g, "P").replace(/[\xE0-\xE5]/g, "a").replace(/[\xE6]/g, "ae").replace(/[\xE7]/g, "c").replace(/[\xE8-\xEB]/g, "e").replace(/[\xEC-\xEF]/g, "i").replace(/[\xF1]/g, "n").replace(/[\xF2-\xF6\xF8]/g, "o").replace(/[\xF9-\xFC]/g, "u").replace(/[\xFE]/g, "p").replace(/[\xFD\xFF]/g, "y");
    }

    return str;
  };

  return ObjectUtils;
}();

var InputText = /*#__PURE__*/function (_Component) {
  _inheritsLoose(InputText, _Component);

  function InputText(props) {
    var _this;

    _this = _Component.call(this, props) || this;
    _this.onInput = _this.onInput.bind(_assertThisInitialized(_this));
    _this.onKeyPress = _this.onKeyPress.bind(_assertThisInitialized(_this));
    return _this;
  }

  var _proto = InputText.prototype;

  _proto.onKeyPress = function onKeyPress(event) {
    if (this.props.onKeyPress) {
      this.props.onKeyPress(event);
    }

    if (this.props.keyfilter) {
      KeyFilter.onKeyPress(event, this.props.keyfilter, this.props.validateOnly);
    }
  };

  _proto.onInput = function onInput(event) {
    var validatePattern = true;

    if (this.props.keyfilter && this.props.validateOnly) {
      validatePattern = KeyFilter.validate(event, this.props.keyfilter);
    }

    if (this.props.onInput) {
      this.props.onInput(event, validatePattern);
    }

    if (!this.props.onChange) {
      if (event.target.value.length > 0) DomHandler.addClass(event.target, 'p-filled');else DomHandler.removeClass(event.target, 'p-filled');
    }
  };

  _proto.componentDidMount = function componentDidMount() {
    if (this.props.tooltip) {
      this.renderTooltip();
    }
  };

  _proto.componentDidUpdate = function componentDidUpdate(prevProps) {
    if (prevProps.tooltip !== this.props.tooltip) {
      if (this.tooltip) this.tooltip.updateContent(this.props.tooltip);else this.renderTooltip();
    }
  };

  _proto.componentWillUnmount = function componentWillUnmount() {
    if (this.tooltip) {
      this.tooltip.destroy();
      this.tooltip = null;
    }
  };

  _proto.renderTooltip = function renderTooltip() {
    this.tooltip = new Tooltip({
      target: this.element,
      content: this.props.tooltip,
      options: this.props.tooltipOptions
    });
  };

  _proto.render = function render() {
    var _this2 = this;

    var className = classNames('p-inputtext p-component', this.props.className, {
      'p-disabled': this.props.disabled,
      'p-filled': this.props.value != null && this.props.value.toString().length > 0 || this.props.defaultValue != null && this.props.defaultValue.toString().length > 0
    });
    var inputProps = ObjectUtils.findDiffKeys(this.props, InputText.defaultProps);
    return /*#__PURE__*/React.createElement("input", _extends({
      ref: function ref(el) {
        return _this2.element = el;
      }
    }, inputProps, {
      className: className,
      onInput: this.onInput,
      onKeyPress: this.onKeyPress
    }));
  };

  return InputText;
}(Component);
InputText.defaultProps = {
  onInput: null,
  onKeyPress: null,
  keyfilter: null,
  validateOnly: false,
  tooltip: null,
  tooltipOptions: null
};
InputText.propTypes = {
  onInput: propTypes.func,
  onKeyPress: propTypes.func,
  keyfilter: propTypes.any,
  validateOnly: propTypes.bool,
  tooltip: propTypes.string,
  tooltipOptions: propTypes.object
};

var Button = /*#__PURE__*/function (_Component) {
  _inheritsLoose(Button, _Component);

  function Button() {
    return _Component.apply(this, arguments) || this;
  }

  var _proto = Button.prototype;

  _proto.componentDidMount = function componentDidMount() {
    if (this.props.tooltip) {
      this.renderTooltip();
    }
  };

  _proto.componentDidUpdate = function componentDidUpdate(prevProps) {
    if (prevProps.tooltip !== this.props.tooltip) {
      if (this.tooltip) this.tooltip.updateContent(this.props.tooltip);else this.renderTooltip();
    }
  };

  _proto.componentWillUnmount = function componentWillUnmount() {
    if (this.tooltip) {
      this.tooltip.destroy();
      this.tooltip = null;
    }
  };

  _proto.renderTooltip = function renderTooltip() {
    this.tooltip = new Tooltip({
      target: this.element,
      content: this.props.tooltip,
      options: this.props.tooltipOptions
    });
  };

  _proto.renderIcon = function renderIcon() {
    if (this.props.icon) {
      var className = classNames(this.props.icon, 'p-c', {
        'p-button-icon-left': this.props.iconPos !== 'right',
        'p-button-icon-right': this.props.iconPos === 'right'
      });
      return /*#__PURE__*/React.createElement("span", {
        className: className
      });
    } else {
      return null;
    }
  };

  _proto.renderLabel = function renderLabel() {
    var buttonLabel = this.props.label || 'p-btn';
    return /*#__PURE__*/React.createElement("span", {
      className: "p-button-text p-c"
    }, buttonLabel);
  };

  _proto.render = function render() {
    var _this = this;

    var className = classNames('p-button p-component', this.props.className, {
      'p-button-icon-only': this.props.icon && !this.props.label,
      'p-button-text-icon-left': this.props.icon && this.props.label && this.props.iconPos === 'left',
      'p-button-text-icon-right': this.props.icon && this.props.label && this.props.iconPos === 'right',
      'p-button-text-only': !this.props.icon && this.props.label,
      'p-disabled': this.props.disabled
    });
    var icon = this.renderIcon();
    var label = this.renderLabel();
    var buttonProps = ObjectUtils.findDiffKeys(this.props, Button.defaultProps);
    return /*#__PURE__*/React.createElement("button", _extends({
      ref: function ref(el) {
        return _this.element = el;
      }
    }, buttonProps, {
      className: className
    }), this.props.iconPos === 'left' && icon, label, this.props.iconPos === 'right' && icon, this.props.children);
  };

  return Button;
}(Component);
Button.defaultProps = {
  label: null,
  icon: null,
  iconPos: 'left',
  tooltip: null,
  tooltipOptions: null
};
Button.propTypes = {
  label: propTypes.string,
  icon: propTypes.string,
  iconPos: propTypes.string,
  tooltip: propTypes.string,
  tooltipOptions: propTypes.object
};

var CalendarPanel = /*#__PURE__*/function (_Component) {
  _inheritsLoose(CalendarPanel, _Component);

  function CalendarPanel() {
    return _Component.apply(this, arguments) || this;
  }

  var _proto = CalendarPanel.prototype;

  _proto.renderElement = function renderElement() {
    var _this = this;

    return /*#__PURE__*/React.createElement("div", {
      ref: function ref(el) {
        return _this.element = el;
      },
      className: this.props.className,
      style: this.props.style
    }, this.props.children);
  };

  _proto.render = function render() {
    var element = this.renderElement();
    if (this.props.appendTo) return ReactDOM.createPortal(element, this.props.appendTo);else return element;
  };

  return CalendarPanel;
}(Component);
CalendarPanel.defaultProps = {
  appendTo: null,
  style: null,
  className: null
};
CalendarPanel.propTypes = {
  appendTo: propTypes.object,
  style: propTypes.object,
  className: propTypes.string
};

var Calendar = /*#__PURE__*/function (_Component) {
  _inheritsLoose(Calendar, _Component);

  function Calendar(props) {
    var _this;

    _this = _Component.call(this, props) || this;
    _this.state = {
      localeData: {
        firstDayOfWeek: 0,
        dayNames: moment.weekdays(),
        dayNamesShort: moment.weekdaysShort(),
        dayNamesMin: moment.weekdaysMin(),
        monthNames: moment.months(),
        monthNamesShort: moment.monthsShort(),
        today: 'Today',
        clear: 'Clear',
        dateFormat: moment.localeData(_this.props.locale).longDateFormat('L'),
        weekHeader: 'Wk'
      }
    };

    if (!_this.props.onViewDateChange) {
      var propValue = _this.props.value;

      if (Array.isArray(propValue)) {
        propValue = propValue[0];
      }

      var viewDate = _this.props.viewDate && _this.isValidDate(_this.props.viewDate) ? _this.props.viewDate : propValue && _this.isValidDate(propValue) ? propValue : new Date();
      _this.state = {
        viewDate: viewDate
      };
    }

    _this.navigation = null;
    _this.onUserInput = _this.onUserInput.bind(_assertThisInitialized(_this));
    _this.onInputFocus = _this.onInputFocus.bind(_assertThisInitialized(_this));
    _this.onInputBlur = _this.onInputBlur.bind(_assertThisInitialized(_this));
    _this.onInputKeyDown = _this.onInputKeyDown.bind(_assertThisInitialized(_this));
    _this.onButtonClick = _this.onButtonClick.bind(_assertThisInitialized(_this));
    _this.onPrevButtonClick = _this.onPrevButtonClick.bind(_assertThisInitialized(_this));
    _this.onNextButtonClick = _this.onNextButtonClick.bind(_assertThisInitialized(_this));
    _this.onMonthDropdownChange = _this.onMonthDropdownChange.bind(_assertThisInitialized(_this));
    _this.onYearDropdownChange = _this.onYearDropdownChange.bind(_assertThisInitialized(_this));
    _this.onTodayButtonClick = _this.onTodayButtonClick.bind(_assertThisInitialized(_this));
    _this.onClearButtonClick = _this.onClearButtonClick.bind(_assertThisInitialized(_this));
    _this.incrementHour = _this.incrementHour.bind(_assertThisInitialized(_this));
    _this.decrementHour = _this.decrementHour.bind(_assertThisInitialized(_this));
    _this.incrementMinute = _this.incrementMinute.bind(_assertThisInitialized(_this));
    _this.decrementMinute = _this.decrementMinute.bind(_assertThisInitialized(_this));
    _this.incrementSecond = _this.incrementSecond.bind(_assertThisInitialized(_this));
    _this.decrementSecond = _this.decrementSecond.bind(_assertThisInitialized(_this));
    _this.toggleAmPm = _this.toggleAmPm.bind(_assertThisInitialized(_this));
    _this.onTimePickerElementMouseDown = _this.onTimePickerElementMouseDown.bind(_assertThisInitialized(_this));
    _this.onTimePickerElementMouseUp = _this.onTimePickerElementMouseUp.bind(_assertThisInitialized(_this));
    _this.onTimePickerElementMouseLeave = _this.onTimePickerElementMouseLeave.bind(_assertThisInitialized(_this));
    return _this;
  }

  var _proto = Calendar.prototype;

  _proto.componentWillMount = function componentWillMount() {
    moment().locale(this.props.locale);
    this.setState({
      localeData: {
        firstDayOfWeek: 0,
        dayNames: moment.weekdays(),
        dayNamesShort: moment.weekdaysShort(),
        dayNamesMin: moment.weekdaysMin(),
        monthNames: moment.months(),
        monthNamesShort: moment.monthsShort(),
        today: 'Today',
        clear: 'Clear',
        dateFormat: moment.localeData(this.props.locale).longDateFormat('L'),
        weekHeader: 'Wk'
      }
    }, function () {});
  };

  _proto.componentDidMount = function componentDidMount() {
    if (this.props.tooltip) {
      this.renderTooltip();
    }

    if (this.props.inline) {
      this.initFocusableCell();
    }

    if (this.props.value) {
      this.updateInputfield(this.props.value);
    }

    moment().locale(this.props.locale);
    this.setState({
      localeData: {
        firstDayOfWeek: 0,
        dayNames: moment.weekdays(),
        dayNamesShort: moment.weekdaysShort(),
        dayNamesMin: moment.weekdaysMin(),
        monthNames: moment.months(),
        monthNamesShort: moment.monthsShort(),
        today: 'Today',
        clear: 'Clear',
        dateFormat: moment.localeData(this.props.locale).longDateFormat('L'),
        weekHeader: 'Wk'
      }
    }, function () {});
  };

  _proto.componentDidUpdate = function componentDidUpdate(prevProps) {
    if (prevProps.tooltip !== this.props.tooltip) {
      if (this.tooltip) this.tooltip.updateContent(this.props.tooltip);else this.renderTooltip();
    }

    if (!this.props.onViewDateChange && !this.viewStateChanged) {
      var propValue = this.props.value;

      if (Array.isArray(propValue)) {
        propValue = propValue[0];
      }

      var prevPropValue = prevProps.value;

      if (Array.isArray(prevPropValue)) {
        prevPropValue = prevPropValue[0];
      }

      if (!prevPropValue && propValue || propValue && propValue instanceof Date && propValue.getTime() !== prevPropValue.getTime()) {
        var viewDate = this.props.viewDate && this.isValidDate(this.props.viewDate) ? this.props.viewDate : propValue && this.isValidDate(propValue) ? propValue : new Date();
      }
    }

    if (this.panel) {
      this.updateFocus();
    }

    if (prevProps.value !== this.props.value && (!this.viewStateChanged || !this.panel.offsetParent)) {
      this.updateInputfield(this.props.value);
    }
  };

  _proto.componentWillUnmount = function componentWillUnmount() {
    if (this.hideTimeout) {
      clearTimeout(this.hideTimeout);
    }

    if (this.mask) {
      this.disableModality();
      this.mask = null;
    }

    if (this.tooltip) {
      this.tooltip.destroy();
      this.tooltip = null;
    }

    this.unbindDocumentClickListener();
    this.unbindDocumentResizeListener();
  };

  _proto.renderTooltip = function renderTooltip() {
    this.tooltip = new Tooltip({
      target: this.inputElement,
      content: this.props.tooltip,
      options: this.props.tooltipOptions
    });
  };

  _proto.onInputFocus = function onInputFocus(event) {
    if (this.props.showOnFocus && !this.panel.offsetParent) {
      this.showOverlay();
    }

    if (this.props.onFocus) {
      this.props.onFocus(event);
    }

    DomHandler.addClass(this.container, 'p-inputwrapper-focus');
  };

  _proto.onInputBlur = function onInputBlur(event) {
    if (this.props.onBlur) {
      this.props.onBlur(event);
    }

    if (!this.props.keepInvalid) {
      this.updateInputfield(this.props.value);
    }

    DomHandler.removeClass(this.container, 'p-inputwrapper-focus');
  };

  _proto.onInputKeyDown = function onInputKeyDown(event) {
    this.isKeydown = true;

    switch (event.which) {
      case 27:
        {
          this.hideOverlay();
          break;
        }

      case 9:
        {
          if (this.props.touchUI) {
            this.disableModality();
          }

          if (event.shiftKey) {
            this.hideOverlay();
          }

          break;
        }
    }
  };

  _proto.onUserInput = function onUserInput(event) {
    if (!this.isKeydown) {
      return;
    }

    this.isKeydown = false;
    var rawValue = event.target.value;

    try {
      var value = this.parseValueFromString(rawValue);

      if (this.isValidSelection(value)) {
        this.updateModel(event, value);
        this.updateViewDate(event, value.length ? value[0] : value);
      }
    } catch (err) {
      var _value = this.props.keepInvalid ? rawValue : null;

      this.updateModel(event, _value);
    }

    if (this.props.onInput) {
      this.props.onInput(event);
    }
  };

  _proto.isValidSelection = function isValidSelection(value) {
    var _this2 = this;

    var isValid = true;

    if (this.isSingleSelection()) {
      if (!(this.isSelectable(value.getDate(), value.getMonth(), value.getFullYear(), false) && this.isSelectableTime(value))) {
        isValid = false;
      }
    } else if (value.every(function (v) {
      return _this2.isSelectable(v.getDate(), v.getMonth(), v.getFullYear(), false) && _this2.isSelectableTime(value);
    })) {
      if (this.isRangeSelection()) {
        isValid = value.length > 1 && value[1] > value[0] ? true : false;
      }
    }

    return isValid;
  };

  _proto.onButtonClick = function onButtonClick(event) {
    if (!this.panel.offsetParent) {
      this.showOverlay();
    } else {
      this.hideOverlay();
    }
  };

  _proto.onPrevButtonClick = function onPrevButtonClick(event) {
    this.navigation = {
      backward: true,
      button: true
    };
    this.navBackward(event);
  };

  _proto.onNextButtonClick = function onNextButtonClick(event) {
    this.navigation = {
      backward: false,
      button: true
    };
    this.navForward(event);
  };

  _proto.onContainerButtonKeydown = function onContainerButtonKeydown(event) {
    switch (event.which) {
      case 9:
        this.trapFocus(event);
        break;

      case 27:
        this.hideOverlay();
        event.preventDefault();
        break;
    }
  };

  _proto.trapFocus = function trapFocus(event) {
    event.preventDefault();
    var focusableElements = DomHandler.getFocusableElements(this.panel);

    if (focusableElements && focusableElements.length > 0) {
      if (!document.activeElement) {
        focusableElements[0].focus();
      } else {
        var focusedIndex = focusableElements.indexOf(document.activeElement);

        if (event.shiftKey) {
          if (focusedIndex === -1 || focusedIndex === 0) focusableElements[focusableElements.length - 1].focus();else focusableElements[focusedIndex - 1].focus();
        } else {
          if (focusedIndex === -1 || focusedIndex === focusableElements.length - 1) focusableElements[0].focus();else focusableElements[focusedIndex + 1].focus();
        }
      }
    }
  };

  _proto.updateFocus = function updateFocus() {
    var cell;

    if (this.navigation) {
      if (this.navigation.button) {
        this.initFocusableCell();
        if (this.navigation.backward) DomHandler.findSingle(this.panel, ".p-datepicker-prev").focus();else DomHandler.findSingle(this.panel, ".p-datepicker-next").focus();
      } else {
        if (this.navigation.backward) {
          var cells = DomHandler.find(this.panel, ".p-datepicker-calendar td span:not(.p-disabled)");
          cell = cells[cells.length - 1];
        } else {
          cell = DomHandler.findSingle(this.panel, ".p-datepicker-calendar td span:not(.p-disabled)");
        }

        if (cell) {
          cell.tabIndex = "0";
          cell.focus();
        }
      }

      this.navigation = null;
    } else {
      this.initFocusableCell();
    }
  };

  _proto.initFocusableCell = function initFocusableCell() {
    var cell;

    if (this.view === "month") {
      var cells = DomHandler.find(this.panel, ".p-monthpicker .p-monthpicker-month");
      var selectedCell = DomHandler.findSingle(this.panel, ".p-monthpicker .p-monthpicker-month.p-highlight");
      cells.forEach(function (cell) {
        return cell.tabIndex = -1;
      });
      cell = selectedCell || cells[0];
    } else {
      cell = DomHandler.findSingle(this.panel, "span.p-highlight");

      if (!cell) {
        var todayCell = DomHandler.findSingle(this.panel, "td.p-datepicker-today span:not(.p-disabled)");
        if (todayCell) cell = todayCell;else cell = DomHandler.findSingle(this.panel, ".p-datepicker-calendar td span:not(.p-disabled)");
      }
    }

    if (cell) {
      cell.tabIndex = "0";
    }
  };

  _proto.navBackward = function navBackward(event) {
    if (this.props.disabled) {
      event.preventDefault();
      return;
    }

    var newViewDate = new Date(this.getViewDate().getTime());
    newViewDate.setDate(1);

    if (this.props.view === "date") {
      if (newViewDate.getMonth() === 0) {
        newViewDate.setMonth(11);
        newViewDate.setFullYear(newViewDate.getFullYear() - 1);
      } else {
        newViewDate.setMonth(newViewDate.getMonth() - 1);
      }
    } else if (this.props.view === "month") {
      var currentYear = newViewDate.getFullYear();
      var newYear = currentYear - 1;

      if (this.props.yearNavigator) {
        var minYear = parseInt(this.props.yearRange.split(":")[0], 10);

        if (newYear < minYear) {
          newYear = minYear;
        }
      }

      newViewDate.setFullYear(newYear);
    }

    this.updateViewDate(event, newViewDate);
    event.preventDefault();
  };

  _proto.navForward = function navForward(event) {
    if (this.props.disabled) {
      event.preventDefault();
      return;
    }

    var newViewDate = new Date(this.getViewDate().getTime());
    newViewDate.setDate(1);

    if (this.props.view === "date") {
      if (newViewDate.getMonth() === 11) {
        newViewDate.setMonth(0);
        newViewDate.setFullYear(newViewDate.getFullYear() + 1);
      } else {
        newViewDate.setMonth(newViewDate.getMonth() + 1);
      }
    } else if (this.props.view === "month") {
      var currentYear = newViewDate.getFullYear();
      var newYear = currentYear + 1;

      if (this.props.yearNavigator) {
        var maxYear = parseInt(this.props.yearRange.split(":")[1], 10);

        if (newYear > maxYear) {
          newYear = maxYear;
        }
      }

      newViewDate.setFullYear(newYear);
    }

    this.updateViewDate(event, newViewDate);
    event.preventDefault();
  };

  _proto.onMonthDropdownChange = function onMonthDropdownChange(event) {
    var currentViewDate = this.getViewDate();
    var newViewDate = new Date(currentViewDate.getTime());
    newViewDate.setMonth(parseInt(event.target.value, 10));
    this.updateViewDate(event, newViewDate);
  };

  _proto.onYearDropdownChange = function onYearDropdownChange(event) {
    var currentViewDate = this.getViewDate();
    var newViewDate = new Date(currentViewDate.getTime());
    newViewDate.setFullYear(parseInt(event.target.value, 10));
    this.updateViewDate(event, newViewDate);
  };

  _proto.onTodayButtonClick = function onTodayButtonClick(event) {
    var today = new Date();
    var dateMeta = {
      day: today.getDate(),
      month: today.getMonth(),
      year: today.getFullYear(),
      today: true,
      selectable: true
    };
    var timeMeta = {
      hours: today.getHours(),
      minutes: today.getMinutes(),
      seconds: today.getSeconds(),
      milliseconds: today.getMilliseconds()
    };
    this.updateViewDate(event, today);
    this.onDateSelect(event, dateMeta, timeMeta);

    if (this.props.onTodayButtonClick) {
      this.props.onTodayButtonClick(event);
    }
  };

  _proto.onClearButtonClick = function onClearButtonClick(event) {
    this.updateModel(event, null);
    this.updateInputfield(null);
    this.hideOverlay();

    if (this.props.onClearButtonClick) {
      this.props.onClearButtonClick(event);
    }
  };

  _proto.onTimePickerElementMouseDown = function onTimePickerElementMouseDown(event, type, direction) {
    if (!this.props.disabled) {
      this.repeat(event, null, type, direction);
      event.preventDefault();
    }
  };

  _proto.onTimePickerElementMouseUp = function onTimePickerElementMouseUp() {
    if (!this.props.disabled) {
      this.clearTimePickerTimer();
    }
  };

  _proto.onTimePickerElementMouseLeave = function onTimePickerElementMouseLeave() {
    if (!this.props.disabled) {
      this.clearTimePickerTimer();
    }
  };

  _proto.repeat = function repeat(event, interval, type, direction) {
    var _this3 = this;

    event.persist();
    var i = interval || 500;
    this.clearTimePickerTimer();
    this.timePickerTimer = setTimeout(function () {
      _this3.repeat(event, 100, type, direction);
    }, i);

    switch (type) {
      case 0:
        if (direction === 1) this.incrementHour(event);else this.decrementHour(event);
        break;

      case 1:
        if (direction === 1) this.incrementMinute(event);else this.decrementMinute(event);
        break;

      case 2:
        if (direction === 1) this.incrementSecond(event);else this.decrementSecond(event);
        break;

      case 3:
        if (direction === 1) this.incrementMilliSecond(event);else this.decrementMilliSecond(event);
        break;
    }
  };

  _proto.clearTimePickerTimer = function clearTimePickerTimer() {
    if (this.timePickerTimer) {
      clearTimeout(this.timePickerTimer);
    }
  };

  _proto.incrementHour = function incrementHour(event) {
    var currentTime = this.props.value && this.props.value instanceof Date ? this.props.value : this.getViewDate();
    var currentHour = currentTime.getHours();
    var newHour = currentHour;
    newHour = newHour >= 24 ? newHour - 24 : newHour;

    if (this.validateHour(newHour, currentTime)) {
      if (this.props.maxDate && this.props.maxDate.toDateString() === currentTime.toDateString() && this.props.maxDate.getHours() === newHour) {
        if (this.props.maxDate.getMinutes() < currentTime.getMinutes()) {
          if (this.props.maxDate.getSeconds() < currentTime.getSeconds()) {
            if (this.props.maxDate.getMilliseconds() < currentTime.getMilliseconds()) {
              this.updateTime(event, newHour, this.props.maxDate.getMinutes(), this.props.maxDate.getSeconds(), this.props.maxDate.getMilliseconds());
            } else {
              this.updateTime(event, newHour, this.props.maxDate.getMinutes(), this.props.maxDate.getSeconds(), currentTime.getMilliseconds());
            }
          } else {
            this.updateTime(event, newHour, this.props.maxDate.getMinutes(), currentTime.getSeconds(), currentTime.getMilliseconds());
          }
        } else if (this.props.maxDate.getMinutes() === currentTime.getMinutes()) {
          if (this.props.maxDate.getSeconds() < currentTime.getSeconds()) {
            if (this.props.maxDate.getMilliseconds() < currentTime.getMilliseconds()) {
              this.updateTime(event, newHour, this.props.maxDate.getMinutes(), this.props.maxDate.getSeconds(), this.props.maxDate.getMilliseconds());
            } else {
              this.updateTime(event, newHour, this.props.maxDate.getMinutes(), this.props.maxDate.getSeconds(), currentTime.getMilliseconds());
            }
          } else {
            this.updateTime(event, newHour, this.props.maxDate.getMinutes(), currentTime.getSeconds(), currentTime.getMilliseconds());
          }
        } else {
          this.updateTime(event, newHour, currentTime.getMinutes(), currentTime.getSeconds(), currentTime.getMilliseconds());
        }
      } else {
        this.updateTime(event, newHour, currentTime.getMinutes(), currentTime.getSeconds(), currentTime.getMilliseconds());
      }
    }

    event.preventDefault();
  };

  _proto.decrementHour = function decrementHour(event) {
    var currentTime = this.props.value && this.props.value instanceof Date ? this.props.value : this.getViewDate();
    var currentHour = currentTime.getHours();
    var newHour = currentHour;
    newHour = newHour < 0 ? newHour + 24 : newHour;

    if (this.validateHour(newHour, currentTime)) {
      if (this.props.minDate && this.props.minDate.toDateString() === currentTime.toDateString() && this.props.minDate.getHours() === newHour) {
        if (this.props.minDate.getMinutes() > currentTime.getMinutes()) {
          if (this.props.minDate.getSeconds() > currentTime.getSeconds()) {
            if (this.props.minDate.getMilliseconds() > currentTime.getMilliseconds()) {
              this.updateTime(event, newHour, this.props.minDate.getMinutes(), this.props.minDate.getSeconds(), this.props.minDate.getMilliseconds());
            } else {
              this.updateTime(event, newHour, this.props.minDate.getMinutes(), this.props.minDate.getSeconds(), currentTime.getMilliseconds());
            }
          } else {
            this.updateTime(event, newHour, this.props.minDate.getMinutes(), currentTime.getSeconds(), currentTime.getMilliseconds());
          }
        } else if (this.props.minDate.getMinutes() === currentTime.getMinutes()) {
          if (this.props.minDate.getSeconds() > currentTime.getSeconds()) {
            if (this.props.minDate.getMilliseconds() > currentTime.getMilliseconds()) {
              this.updateTime(event, newHour, this.props.minDate.getMinutes(), this.props.minDate.getSeconds(), this.props.minDate.getMilliseconds());
            } else {
              this.updateTime(event, newHour, this.props.minDate.getMinutes(), this.props.minDate.getSeconds(), currentTime.getMilliseconds());
            }
          } else {
            this.updateTime(event, newHour, this.props.minDate.getMinutes(), currentTime.getSeconds(), currentTime.getMilliseconds());
          }
        } else {
          this.updateTime(event, newHour, currentTime.getMinutes(), currentTime.getSeconds(), currentTime.getMilliseconds());
        }
      } else {
        this.updateTime(event, newHour, currentTime.getMinutes(), currentTime.getSeconds(), currentTime.getMilliseconds());
      }
    }

    event.preventDefault();
  };

  _proto.incrementMinute = function incrementMinute(event) {
    var currentTime = this.props.value && this.props.value instanceof Date ? this.props.value : this.getViewDate();
    var currentMinute = currentTime.getMinutes();
    var newMinute = currentMinute;
    newMinute = newMinute > 59 ? newMinute - 60 : newMinute;

    if (this.validateMinute(newMinute, currentTime)) {
      if (this.props.maxDate && this.props.maxDate.toDateString() === currentTime.toDateString() && this.props.maxDate.getMinutes() === newMinute) {
        if (this.props.maxDate.getSeconds() < currentTime.getSeconds()) {
          if (this.props.maxDate.getMilliseconds() < currentTime.getMilliseconds()) {
            this.updateTime(event, currentTime.getHours(), newMinute, this.props.maxDate.getSeconds(), this.props.maxDate.getMilliseconds());
          } else {
            this.updateTime(event, currentTime.getHours(), newMinute, this.props.maxDate.getSeconds(), currentTime.getMilliseconds());
          }
        } else {
          this.updateTime(event, currentTime.getHours(), newMinute, currentTime.getSeconds(), currentTime.getMilliseconds());
        }
      } else {
        this.updateTime(event, currentTime.getHours(), newMinute, currentTime.getSeconds(), currentTime.getMilliseconds());
      }
    }

    event.preventDefault();
  };

  _proto.decrementMinute = function decrementMinute(event) {
    var currentTime = this.props.value && this.props.value instanceof Date ? this.props.value : this.getViewDate();
    var currentMinute = currentTime.getMinutes();
    var newMinute = currentMinute;
    newMinute = newMinute < 0 ? newMinute + 60 : newMinute;

    if (this.validateMinute(newMinute, currentTime)) {
      if (this.props.minDate && this.props.minDate.toDateString() === currentTime.toDateString() && this.props.minDate.getMinutes() === newMinute) {
        if (this.props.minDate.getSeconds() > currentTime.getSeconds()) {
          if (this.props.minDate.getMilliseconds() > currentTime.getMilliseconds()) {
            this.updateTime(event, currentTime.getHours(), newMinute, this.props.minDate.getSeconds(), this.props.minDate.getMilliseconds());
          } else {
            this.updateTime(event, currentTime.getHours(), newMinute, this.props.minDate.getSeconds(), currentTime.getMilliseconds());
          }
        } else {
          this.updateTime(event, currentTime.getHours(), newMinute, currentTime.getSeconds(), currentTime.getMilliseconds());
        }
      } else {
        this.updateTime(event, currentTime.getHours(), newMinute, currentTime.getSeconds(), currentTime.getMilliseconds());
      }
    }

    event.preventDefault();
  };

  _proto.incrementSecond = function incrementSecond(event) {
    var currentTime = this.props.value && this.props.value instanceof Date ? this.props.value : this.getViewDate();
    var currentSecond = currentTime.getSeconds();
    var newSecond = currentSecond;
    newSecond = newSecond > 59 ? newSecond - 60 : newSecond;

    if (this.validateSecond(newSecond, currentTime)) {
      if (this.props.maxDate && this.props.maxDate.toDateString() === currentTime.toDateString() && this.props.maxDate.getSeconds() === newSecond) {
        if (this.props.maxDate.getMilliseconds() < currentTime.getMilliseconds()) {
          this.updateTime(event, currentTime.getHours(), currentTime.getMinutes(), newSecond, this.props.maxDate.getMilliseconds());
        } else {
          this.updateTime(event, currentTime.getHours(), currentTime.getMinutes(), newSecond, currentTime.getMilliseconds());
        }
      } else {
        this.updateTime(event, currentTime.getHours(), currentTime.getMinutes(), newSecond, currentTime.getMilliseconds());
      }
    }

    event.preventDefault();
  };

  _proto.decrementSecond = function decrementSecond(event) {
    var currentTime = this.props.value && this.props.value instanceof Date ? this.props.value : this.getViewDate();
    var currentSecond = currentTime.getSeconds();
    var newSecond = currentSecond;
    newSecond = newSecond < 0 ? newSecond + 60 : newSecond;

    if (this.validateSecond(newSecond, currentTime)) {
      if (this.props.minDate && this.props.minDate.toDateString() === currentTime.toDateString() && this.props.minDate.getSeconds() === newSecond) {
        if (this.props.minDate.getMilliseconds() > currentTime.getMilliseconds()) {
          this.updateTime(event, currentTime.getHours(), currentTime.getMinutes(), newSecond, this.props.minDate.getMilliseconds());
        } else {
          this.updateTime(event, currentTime.getHours(), currentTime.getMinutes(), newSecond, currentTime.getMilliseconds());
        }
      } else {
        this.updateTime(event, currentTime.getHours(), currentTime.getMinutes(), newSecond, currentTime.getMilliseconds());
      }
    }

    event.preventDefault();
  };

  _proto.incrementMilliSecond = function incrementMilliSecond(event) {
    var currentTime = this.props.value && this.props.value instanceof Date ? this.props.value : this.getViewDate();
    var currentMillisecond = currentTime.getMilliseconds();
    var newMillisecond = currentMillisecond;
    newMillisecond = newMillisecond > 999 ? newMillisecond - 1000 : newMillisecond;

    if (this.validateMillisecond(newMillisecond, currentTime)) {
      this.updateTime(event, currentTime.getHours(), currentTime.getMinutes(), currentTime.getSeconds(), newMillisecond);
    }

    event.preventDefault();
  };

  _proto.decrementMilliSecond = function decrementMilliSecond(event) {
    var currentTime = this.props.value && this.props.value instanceof Date ? this.props.value : this.getViewDate();
    var currentMillisecond = currentTime.getMilliseconds();
    var newMillisecond = currentMillisecond;
    newMillisecond = newMillisecond < 0 ? newMillisecond + 200 : newMillisecond;

    if (this.validateMillisecond(newMillisecond, currentTime)) {
      this.updateTime(event, currentTime.getHours(), currentTime.getMinutes(), currentTime.getSeconds(), newMillisecond);
    }

    event.preventDefault();
  };

  _proto.toggleAmPm = function toggleAmPm(event) {
    var currentTime = this.props.value && this.props.value instanceof Date ? this.props.value : this.getViewDate();
    var currentHour = currentTime.getHours();
    var newHour = currentHour >= 12 ? currentHour - 12 : currentHour + 12;
    this.updateTime(event, newHour, currentTime.getMinutes(), currentTime.getSeconds(), currentTime.getMilliseconds());
    event.preventDefault();
  };

  _proto.getViewDate = function getViewDate() {
    return this.props.onViewDateChange ? this.props.viewDate : this.state.viewDate;
  };

  _proto.isValidDate = function isValidDate(date) {
    return date instanceof Date && !isNaN(date);
  };

  _proto.validateHour = function validateHour(hour, value) {
    var valid = true;
    var valueDateString = value ? value.toDateString() : null;

    if (this.props.minDate && valueDateString && this.props.minDate.toDateString() === valueDateString) {
      if (this.props.minDate.getHours() > hour) {
        valid = false;
      }
    }

    if (this.props.maxDate && valueDateString && this.props.maxDate.toDateString() === valueDateString) {
      if (this.props.maxDate.getHours() < hour) {
        valid = false;
      }
    }

    return valid;
  };

  _proto.validateMinute = function validateMinute(minute, value) {
    var valid = true;
    var valueDateString = value ? value.toDateString() : null;

    if (this.props.minDate && valueDateString && this.props.minDate.toDateString() === valueDateString) {
      if (value.getHours() === this.props.minDate.getHours()) {
        if (this.props.minDate.getMinutes() > minute) {
          valid = false;
        }
      }
    }

    if (this.props.maxDate && valueDateString && this.props.maxDate.toDateString() === valueDateString) {
      if (value.getHours() === this.props.maxDate.getHours()) {
        if (this.props.maxDate.getMinutes() < minute) {
          valid = false;
        }
      }
    }

    return valid;
  };

  _proto.validateSecond = function validateSecond(second, value) {
    var valid = true;
    var valueDateString = value ? value.toDateString() : null;

    if (this.props.minDate && valueDateString && this.props.minDate.toDateString() === valueDateString) {
      if (value.getHours() === this.props.minDate.getHours() && value.getMinutes() === this.props.minDate.getMinutes()) {
        if (this.props.minDate.getSeconds() > second) {
          valid = false;
        }
      }
    }

    if (this.props.maxDate && valueDateString && this.props.maxDate.toDateString() === valueDateString) {
      if (value.getHours() === this.props.maxDate.getHours() && value.getMinutes() === this.props.maxDate.getMinutes()) {
        if (this.props.maxDate.getSeconds() < second) {
          valid = false;
        }
      }
    }

    return valid;
  };

  _proto.validateMillisecond = function validateMillisecond(millisecond, value) {
    var valid = true;
    var valueDateString = value ? value.toDateString() : null;

    if (this.props.minDate && valueDateString && this.props.minDate.toDateString() === valueDateString) {
      if (value.getHours() === this.props.minDate.getHours() && value.getSeconds() === this.props.minDate.getSeconds() && value.getMinutes() === this.props.minDate.getMinutes()) {
        if (this.props.minDate.getMilliseconds() > millisecond) {
          valid = false;
        }
      }
    }

    if (this.props.maxDate && valueDateString && this.props.maxDate.toDateString() === valueDateString) {
      if (value.getHours() === this.props.maxDate.getHours() && value.getSeconds() === this.props.maxDate.getSeconds() && value.getMinutes() === this.props.maxDate.getMinutes()) {
        if (this.props.maxDate.getMilliseconds() < millisecond) {
          valid = false;
        }
      }
    }

    return valid;
  };

  _proto.updateTime = function updateTime(event, hour, minute, second, millisecond) {
    var newDateTime = this.props.value && this.props.value instanceof Date ? new Date(this.props.value) : new Date();
    newDateTime.setHours(hour);
    newDateTime.setMinutes(minute);
    newDateTime.setSeconds(second);
    newDateTime.setMilliseconds(millisecond);
    this.updateModel(event, newDateTime);

    if (this.props.onSelect) {
      this.props.onSelect({
        originalEvent: event,
        value: newDateTime
      });
    }

    this.updateInputfield(newDateTime);
  };

  _proto.updateViewDate = function updateViewDate(event, value) {
    if (this.props.yearNavigator) {
      var viewYear = value.getFullYear();

      if (this.props.minDate && this.props.minDate.getFullYear() > viewYear) {
        viewYear = this.props.minDate.getFullYear();
      }

      if (this.props.maxDate && this.props.maxDate.getFullYear() < viewYear) {
        viewYear = this.props.maxDate.getFullYear();
      }

      value.setFullYear(viewYear);
    }

    if (this.props.monthNavigator && this.props.view !== "month") {
      var viewMonth = value.getMonth();
      var viewMonthWithMinMax = parseInt(this.isInMinYear(value) && Math.max(this.props.minDate.getMonth(), viewMonth).toString() || this.isInMaxYear(value) && Math.min(this.props.maxDate.getMonth(), viewMonth).toString() || viewMonth);
      value.setMonth(viewMonthWithMinMax);
    }

    if (this.props.onViewDateChange) {
      this.props.onViewDateChange({
        originalEvent: event,
        value: value
      });
    } else {
      this.viewStateChanged = true;
      this.setState({
        viewDate: value
      });
    }
  };

  _proto.onDateCellKeydown = function onDateCellKeydown(event, date, groupIndex) {
    var cellContent = event.currentTarget;
    var cell = cellContent.parentElement;

    switch (event.which) {
      case 40:
        {
          cellContent.tabIndex = "-1";
          var cellIndex = DomHandler.index(cell);
          var nextRow = cell.parentElement.nextElementSibling;

          if (nextRow) {
            var focusCell = nextRow.children[cellIndex].children[0];

            if (DomHandler.hasClass(focusCell, "p-disabled")) {
              this.navigation = {
                backward: false
              };
              this.navForward(event);
            } else {
              nextRow.children[cellIndex].children[0].tabIndex = "0";
              nextRow.children[cellIndex].children[0].focus();
            }
          } else {
            this.navigation = {
              backward: false
            };
            this.navForward(event);
          }

          event.preventDefault();
          break;
        }

      case 38:
        {
          cellContent.tabIndex = "-1";

          var _cellIndex = DomHandler.index(cell);

          var prevRow = cell.parentElement.previousElementSibling;

          if (prevRow) {
            var _focusCell = prevRow.children[_cellIndex].children[0];

            if (DomHandler.hasClass(_focusCell, "p-disabled")) {
              this.navigation = {
                backward: true
              };
              this.navBackward(event);
            } else {
              _focusCell.tabIndex = "0";

              _focusCell.focus();
            }
          } else {
            this.navigation = {
              backward: true
            };
            this.navBackward(event);
          }

          event.preventDefault();
          break;
        }

      case 37:
        {
          cellContent.tabIndex = "-1";
          var prevCell = cell.previousElementSibling;

          if (prevCell) {
            var _focusCell2 = prevCell.children[0];

            if (DomHandler.hasClass(_focusCell2, "p-disabled")) {
              this.navigateToMonth(true, groupIndex, event);
            } else {
              _focusCell2.tabIndex = "0";

              _focusCell2.focus();
            }
          } else {
            this.navigateToMonth(true, groupIndex, event);
          }

          event.preventDefault();
          break;
        }

      case 39:
        {
          cellContent.tabIndex = "-1";
          var nextCell = cell.nextElementSibling;

          if (nextCell) {
            var _focusCell3 = nextCell.children[0];

            if (DomHandler.hasClass(_focusCell3, "p-disabled")) {
              this.navigateToMonth(false, groupIndex, event);
            } else {
              _focusCell3.tabIndex = "0";

              _focusCell3.focus();
            }
          } else {
            this.navigateToMonth(false, groupIndex, event);
          }

          event.preventDefault();
          break;
        }

      case 13:
        {
          this.onDateSelect(event, date);
          event.preventDefault();
          break;
        }

      case 27:
        {
          this.hideOverlay();
          event.preventDefault();
          break;
        }

      case 9:
        {
          this.trapFocus(event);
          break;
        }
    }
  };

  _proto.navigateToMonth = function navigateToMonth(prev, groupIndex, event) {
    if (prev) {
      if (this.props.numberOfMonths === 1 || groupIndex === 0) {
        this.navigation = {
          backward: true
        };
        this.navBackward(event);
      } else {
        var prevMonthContainer = this.panel.children[groupIndex - 1];
        var cells = DomHandler.find(prevMonthContainer, ".p-datepicker-calendar td span:not(.p-disabled)");
        var focusCell = cells[cells.length - 1];
        focusCell.tabIndex = "0";
        focusCell.focus();
      }
    } else {
      if (this.props.numberOfMonths === 1 || groupIndex === this.props.numberOfMonths - 1) {
        this.navigation = {
          backward: false
        };
        this.navForward(event);
      } else {
        var nextMonthContainer = this.panel.children[groupIndex + 1];

        var _focusCell4 = DomHandler.findSingle(nextMonthContainer, ".p-datepicker-calendar td span:not(.p-disabled)");

        _focusCell4.tabIndex = "0";

        _focusCell4.focus();
      }
    }
  };

  _proto.onMonthCellKeydown = function onMonthCellKeydown(event, index) {
    var cell = event.currentTarget;

    switch (event.which) {
      case 38:
      case 40:
        {
          cell.tabIndex = '-1';
          var cells = cell.parentElement.children;
          var cellIndex = DomHandler.index(cell);
          var nextCell = cells[event.which === 40 ? cellIndex + 3 : cellIndex - 3];

          if (nextCell) {
            nextCell.tabIndex = '0';
            nextCell.focus();
          }

          event.preventDefault();
          break;
        }

      case 37:
        {
          cell.tabIndex = "-1";
          var prevCell = cell.previousElementSibling;

          if (prevCell) {
            prevCell.tabIndex = "0";
            prevCell.focus();
          }

          event.preventDefault();
          break;
        }

      case 39:
        {
          cell.tabIndex = "-1";
          var _nextCell = cell.nextElementSibling;

          if (_nextCell) {
            _nextCell.tabIndex = "0";

            _nextCell.focus();
          }

          event.preventDefault();
          break;
        }

      case 13:
        {
          this.onMonthSelect(event, index);
          event.preventDefault();
          break;
        }

      case 27:
        {
          this.hideOverlay();
          event.preventDefault();
          break;
        }

      case 9:
        {
          this.trapFocus(event);
          break;
        }
    }
  };

  _proto.onDateSelect = function onDateSelect(event, dateMeta, timeMeta) {
    var _this4 = this;

    if (this.props.disabled || !dateMeta.selectable) {
      event.preventDefault();
      return;
    }

    DomHandler.find(this.panel, ".p-datepicker-calendar td span:not(.p-disabled)").forEach(function (cell) {
      return cell.tabIndex = -1;
    });
    event.currentTarget.focus();

    if (this.isMultipleSelection()) {
      if (this.isSelected(dateMeta)) {
        var value = this.props.value.filter(function (date, i) {
          return !_this4.isDateEquals(date, dateMeta);
        });
        this.updateModel(event, value);
      } else if (!this.props.maxDateCount || !this.props.value || this.props.maxDateCount > this.props.value.length) {
        this.selectDate(event, dateMeta, timeMeta);
      }
    } else {
      this.selectDate(event, dateMeta, timeMeta);
    }

    if (!this.props.inline && this.isSingleSelection() && this.props.hideOnDateTimeSelect) {
      setTimeout(function () {
        _this4.hideOverlay();
      }, 100);

      if (this.mask) {
        this.disableModality();
      }
    }

    event.preventDefault();
  };

  _proto.selectDate = function selectDate(event, dateMeta, timeMeta) {
    var date = new Date(dateMeta.year, dateMeta.month, dateMeta.day);

    if (this.props.minDate && this.props.minDate > date) {
      date = this.props.minDate;
    }

    if (this.props.maxDate && this.props.maxDate < date) {
      date = this.props.maxDate;
    }

    var selectedValues = date;

    if (this.isSingleSelection()) {
      this.updateModel(event, date);
    } else if (this.isMultipleSelection()) {
      selectedValues = this.props.value ? [].concat(this.props.value, [date]) : [date];
      this.updateModel(event, selectedValues);
    } else if (this.isRangeSelection()) {
      if (this.props.value && this.props.value.length) {
        var startDate = this.props.value[0];
        var endDate = this.props.value[1];

        if (!endDate && date.getTime() >= startDate.getTime()) {
          endDate = date;
        } else {
          startDate = date;
          endDate = null;
        }

        selectedValues = [startDate, endDate];
        this.updateModel(event, selectedValues);
      } else {
        selectedValues = [date, null];
        this.updateModel(event, selectedValues);
      }
    }

    if (this.props.onSelect) {
      this.props.onSelect({
        originalEvent: event,
        value: date
      });
    }

    this.updateInputfield(selectedValues);
  };

  _proto.onMonthSelect = function onMonthSelect(event, month) {
    this.onDateSelect(event, {
      year: this.getViewDate().getFullYear(),
      month: month,
      day: 1,
      selectable: true
    });
    event.preventDefault();
  };

  _proto.updateModel = function updateModel(event, value) {
    if (this.props.onChange) {
      this.props.onChange({
        originalEvent: event,
        value: value,
        stopPropagation: function stopPropagation() {},
        preventDefault: function preventDefault() {},
        target: {
          name: this.props.name,
          id: this.props.id,
          value: value
        }
      });
      this.viewStateChanged = true;
    }
  };

  _proto.showOverlay = function showOverlay() {
    var _this5 = this;

    if (this.props.autoZIndex) {
      this.panel.style.zIndex = String(this.props.baseZIndex + DomHandler.generateZIndex());
    }

    this.panel.style.display = "block";
    setTimeout(function () {
      DomHandler.addClass(_this5.panel, "p-input-overlay-visible");
      DomHandler.removeClass(_this5.panel, "p-input-overlay-hidden");
    }, 1);
    this.alignPanel();
    this.bindDocumentClickListener();
    this.bindDocumentResizeListener();
  };

  _proto.hideOverlay = function hideOverlay() {
    var _this6 = this;

    if (this.panel) {
      DomHandler.addClass(this.panel, "p-input-overlay-hidden");
      DomHandler.removeClass(this.panel, "p-input-overlay-visible");
      this.unbindDocumentClickListener();
      this.unbindDocumentResizeListener();
      this.hideTimeout = setTimeout(function () {
        _this6.panel.style.display = "none";
        DomHandler.removeClass(_this6.panel, "p-input-overlay-hidden");
      }, 150);
    }
  };

  _proto.bindDocumentClickListener = function bindDocumentClickListener() {
    var _this7 = this;

    if (!this.documentClickListener) {
      this.documentClickListener = function (event) {
        if (_this7.isOutsideClicked(event)) {
          _this7.hideOverlay();
        }
      };

      document.addEventListener("mousedown", this.documentClickListener);
    }
  };

  _proto.unbindDocumentClickListener = function unbindDocumentClickListener() {
    if (this.documentClickListener) {
      document.removeEventListener("mousedown", this.documentClickListener);
      this.documentClickListener = null;
    }
  };

  _proto.bindDocumentResizeListener = function bindDocumentResizeListener() {
    if (!this.documentResizeListener && !this.props.touchUI) {
      this.documentResizeListener = this.onWindowResize.bind(this);
      window.addEventListener("resize", this.documentResizeListener);
    }
  };

  _proto.unbindDocumentResizeListener = function unbindDocumentResizeListener() {
    if (this.documentResizeListener) {
      window.removeEventListener("resize", this.documentResizeListener);
      this.documentResizeListener = null;
    }
  };

  _proto.isOutsideClicked = function isOutsideClicked(event) {
    return this.container && !(this.container.isSameNode(event.target) || this.isNavIconClicked(event) || this.container.contains(event.target) || this.panel && this.panel.contains(event.target));
  };

  _proto.isNavIconClicked = function isNavIconClicked(event) {
    return DomHandler.hasClass(event.target, "p-datepicker-prev") || DomHandler.hasClass(event.target, "p-datepicker-prev-icon") || DomHandler.hasClass(event.target, "p-datepicker-next") || DomHandler.hasClass(event.target, "p-datepicker-next-icon");
  };

  _proto.onWindowResize = function onWindowResize() {
    if (this.panel.offsetParent && !DomHandler.isAndroid()) {
      this.hideOverlay();
    }
  };

  _proto.alignPanel = function alignPanel() {
    if (this.props.touchUI) {
      this.enableModality();
    } else {
      if (this.props.appendTo) {
        DomHandler.absolutePosition(this.panel, this.inputElement);
        this.panel.style.minWidth = DomHandler.getWidth(this.container) + "px";
      } else {
        DomHandler.relativePosition(this.panel, this.inputElement);
      }
    }
  };

  _proto.enableModality = function enableModality() {
    var _this8 = this;

    if (!this.mask) {
      this.mask = document.createElement("div");
      this.mask.style.zIndex = String(parseInt(this.panel.style.zIndex, 10) - 1);
      DomHandler.addMultipleClasses(this.mask, "p-component-overlay p-datepicker-mask p-datepicker-mask-scrollblocker");

      this.maskClickListener = function () {
        _this8.disableModality();
      };

      this.mask.addEventListener("click", this.maskClickListener);
      document.body.appendChild(this.mask);
      DomHandler.addClass(document.body, "p-overflow-hidden");
    }
  };

  _proto.disableModality = function disableModality() {
    if (this.mask) {
      this.mask.removeEventListener("click", this.maskClickListener);
      this.maskClickListener = null;
      document.body.removeChild(this.mask);
      this.mask = null;
      var bodyChildren = document.body.children;
      var hasBlockerMasks;

      for (var i = 0; i < bodyChildren.length; i++) {
        var bodyChild = bodyChildren[i];

        if (DomHandler.hasClass(bodyChild, "p-datepicker-mask-scrollblocker")) {
          hasBlockerMasks = true;
          break;
        }
      }

      if (!hasBlockerMasks) {
        DomHandler.removeClass(document.body, "p-overflow-hidden");
      }

      this.hideOverlay();
    }
  };

  _proto.getFirstDayOfMonthIndex = function getFirstDayOfMonthIndex(month, year) {
    var day = new Date();
    day.setDate(1);
    day.setMonth(month);
    day.setFullYear(year);
    var dayIndex = day.getDay() + this.getSundayIndex();
    return dayIndex >= 7 ? dayIndex - 7 : dayIndex;
  };

  _proto.getDaysCountInMonth = function getDaysCountInMonth(month, year) {
    return 32 - this.daylightSavingAdjust(new Date(year, month, 32)).getDate();
  };

  _proto.getDaysCountInPrevMonth = function getDaysCountInPrevMonth(month, year) {
    var prev = this.getPreviousMonthAndYear(month, year);
    return this.getDaysCountInMonth(prev.month, prev.year);
  };

  _proto.daylightSavingAdjust = function daylightSavingAdjust(date) {
    if (!date) {
      return null;
    }

    date.setHours(date.getHours() > 12 ? date.getHours() + 2 : 0);
    return date;
  };

  _proto.getPreviousMonthAndYear = function getPreviousMonthAndYear(month, year) {
    var m, y;

    if (month === 0) {
      m = 11;
      y = year - 1;
    } else {
      m = month - 1;
      y = year;
    }

    return {
      month: m,
      year: y
    };
  };

  _proto.getNextMonthAndYear = function getNextMonthAndYear(month, year) {
    var m, y;

    if (month === 11) {
      m = 0;
      y = year + 1;
    } else {
      m = month + 1;
      y = year;
    }

    return {
      month: m,
      year: y
    };
  };

  _proto.getSundayIndex = function getSundayIndex() {
    return this.state.localeData.firstDayOfWeek > 0 ? 7 - this.state.localeData.firstDayOfWeek : 0;
  };

  _proto.createWeekDays = function createWeekDays() {
    var weekDays = [];
    var dayIndex = this.state.localeData.firstDayOfWeek;

    for (var i = 0; i < 7; i++) {
      weekDays.push(this.state.localeData.dayNamesMin[dayIndex]);
      dayIndex = dayIndex === 6 ? 0 : ++dayIndex;
    }

    return weekDays;
  };

  _proto.createMonths = function createMonths(month, year) {
    var months = [];

    for (var i = 0; i < this.props.numberOfMonths; i++) {
      var m = month + i;
      var y = year;

      if (m > 11) {
        m = m % 11 - 1;
        y = year + 1;
      }

      months.push(this.createMonth(m, y));
    }

    return months;
  };

  _proto.createMonth = function createMonth(month, year) {
    var dates = [];
    var firstDay = this.getFirstDayOfMonthIndex(month, year);
    var daysLength = this.getDaysCountInMonth(month, year);
    var prevMonthDaysLength = this.getDaysCountInPrevMonth(month, year);
    var dayNo = 1;
    var today = new Date();
    var weekNumbers = [];
    var monthRows = Math.ceil((daysLength + firstDay) / 7);

    for (var i = 0; i < monthRows; i++) {
      var week = [];

      if (i === 0) {
        for (var j = prevMonthDaysLength - firstDay + 1; j <= prevMonthDaysLength; j++) {
          var prev = this.getPreviousMonthAndYear(month, year);
          week.push({
            day: j,
            month: prev.month,
            year: prev.year,
            otherMonth: true,
            today: this.isToday(today, j, prev.month, prev.year),
            selectable: this.isSelectable(j, prev.month, prev.year, true)
          });
        }

        var remainingDaysLength = 7 - week.length;

        for (var _j = 0; _j < remainingDaysLength; _j++) {
          week.push({
            day: dayNo,
            month: month,
            year: year,
            today: this.isToday(today, dayNo, month, year),
            selectable: this.isSelectable(dayNo, month, year, false)
          });
          dayNo++;
        }
      } else {
        for (var _j2 = 0; _j2 < 7; _j2++) {
          if (dayNo > daysLength) {
            var next = this.getNextMonthAndYear(month, year);
            week.push({
              day: dayNo - daysLength,
              month: next.month,
              year: next.year,
              otherMonth: true,
              today: this.isToday(today, dayNo - daysLength, next.month, next.year),
              selectable: this.isSelectable(dayNo - daysLength, next.month, next.year, true)
            });
          } else {
            week.push({
              day: dayNo,
              month: month,
              year: year,
              today: this.isToday(today, dayNo, month, year),
              selectable: this.isSelectable(dayNo, month, year, false)
            });
          }

          dayNo++;
        }
      }

      if (this.props.showWeek) {
        weekNumbers.push(this.getWeekNumber(new Date(week[0].year, week[0].month, week[0].day)));
      }

      dates.push(week);
    }

    return {
      month: month,
      year: year,
      dates: dates,
      weekNumbers: weekNumbers
    };
  };

  _proto.getWeekNumber = function getWeekNumber(date) {
    var checkDate = new Date(date.getTime());
    checkDate.setDate(checkDate.getDate() + 4 - (checkDate.getDay() || 7));
    var time = checkDate.getTime();
    checkDate.setMonth(0);
    checkDate.setDate(1);
    return Math.floor(Math.round((time - checkDate.getTime()) / 86400000) / 7) + 1;
  };

  _proto.isSelectable = function isSelectable(day, month, year, otherMonth) {
    var validMin = true;
    var validMax = true;
    var validDate = true;
    var validDay = true;
    var validMonth = true;

    if (this.props.minDate) {
      if (this.props.minDate.getFullYear() > year) {
        validMin = false;
      } else if (this.props.minDate.getFullYear() === year) {
        if (this.props.minDate.getMonth() > month) {
          validMin = false;
        } else if (this.props.minDate.getMonth() === month) {
          if (this.props.minDate.getDate() > day) {
            validMin = false;
          }
        }
      }
    }

    if (this.props.maxDate) {
      if (this.props.maxDate.getFullYear() < year) {
        validMax = false;
      } else if (this.props.maxDate.getFullYear() === year) {
        if (this.props.maxDate.getMonth() < month) {
          validMax = false;
        } else if (this.props.maxDate.getMonth() === month) {
          if (this.props.maxDate.getDate() < day) {
            validMax = false;
          }
        }
      }
    }

    if (this.props.disabledDates) {
      validDate = !this.isDateDisabled(day, month, year);
    }

    if (this.props.disabledDays) {
      validDay = !this.isDayDisabled(day, month, year);
    }

    if (this.props.selectOtherMonths === false && otherMonth) {
      validMonth = false;
    }

    return validMin && validMax && validDate && validDay && validMonth;
  };

  _proto.isSelectableTime = function isSelectableTime(value) {
    var validMin = true;
    var validMax = true;

    if (this.props.minDate && this.props.minDate.toDateString() === value.toDateString()) {
      if (this.props.minDate.getHours() > value.getHours()) {
        validMin = false;
      } else if (this.props.minDate.getHours() === value.getHours()) {
        if (this.props.minDate.getMinutes() > value.getMinutes()) {
          validMin = false;
        } else if (this.props.minDate.getMinutes() === value.getMinutes()) {
          if (this.props.minDate.getSeconds() > value.getSeconds()) {
            validMin = false;
          } else if (this.props.minDate.getSeconds() === value.getSeconds()) {
            if (this.props.minDate.getMilliseconds() > value.getMilliseconds()) {
              validMin = false;
            }
          }
        }
      }
    }

    if (this.props.maxDate && this.props.maxDate.toDateString() === value.toDateString()) {
      if (this.props.maxDate.getHours() < value.getHours()) {
        validMax = false;
      } else if (this.props.maxDate.getHours() === value.getHours()) {
        if (this.props.maxDate.getMinutes() < value.getMinutes()) {
          validMax = false;
        } else if (this.props.maxDate.getMinutes() === value.getMinutes()) {
          if (this.props.maxDate.getSeconds() < value.getSeconds()) {
            validMax = false;
          } else if (this.props.maxDate.getSeconds() === value.getSeconds()) {
            if (this.props.maxDate.getMilliseconds() < value.getMilliseconds()) {
              validMax = false;
            }
          }
        }
      }
    }

    return validMin && validMax;
  };

  _proto.isSelected = function isSelected(dateMeta) {
    if (this.props.value) {
      if (this.isSingleSelection()) {
        return this.isDateEquals(this.props.value, dateMeta);
      } else if (this.isMultipleSelection()) {
        var selected = false;

        for (var _iterator = _createForOfIteratorHelperLoose(this.props.value), _step; !(_step = _iterator()).done;) {
          var date = _step.value;
          selected = this.isDateEquals(date, dateMeta);

          if (selected) {
            break;
          }
        }

        return selected;
      } else if (this.isRangeSelection()) {
        if (this.props.value[1]) return this.isDateEquals(this.props.value[0], dateMeta) || this.isDateEquals(this.props.value[1], dateMeta) || this.isDateBetween(this.props.value[0], this.props.value[1], dateMeta);else {
          return this.isDateEquals(this.props.value[0], dateMeta);
        }
      }
    } else {
      return false;
    }
  };

  _proto.isMonthSelected = function isMonthSelected(month) {
    var viewDate = this.getViewDate();
    if (this.props.value && this.props.value instanceof Date) return this.props.value.getDate() === 1 && this.props.value.getMonth() === month && this.props.value.getFullYear() === viewDate.getFullYear();else return false;
  };

  _proto.isDateEquals = function isDateEquals(value, dateMeta) {
    if (value && value instanceof Date) return value.getDate() === dateMeta.day && value.getMonth() === dateMeta.month && value.getFullYear() === dateMeta.year;else return false;
  };

  _proto.isDateBetween = function isDateBetween(start, end, dateMeta) {
    var between = false;

    if (start && end) {
      var date = new Date(dateMeta.year, dateMeta.month, dateMeta.day);
      return start.getTime() <= date.getTime() && end.getTime() >= date.getTime();
    }

    return between;
  };

  _proto.isSingleSelection = function isSingleSelection() {
    return this.props.selectionMode === "single";
  };

  _proto.isRangeSelection = function isRangeSelection() {
    return this.props.selectionMode === "range";
  };

  _proto.isMultipleSelection = function isMultipleSelection() {
    return this.props.selectionMode === "multiple";
  };

  _proto.isToday = function isToday(today, day, month, year) {
    return today.getDate() === day && today.getMonth() === month && today.getFullYear() === year;
  };

  _proto.isDateDisabled = function isDateDisabled(day, month, year) {
    if (this.props.disabledDates) {
      for (var i = 0; i < this.props.disabledDates.length; i++) {
        var disabledDate = this.props.disabledDates[i];

        if (disabledDate.getFullYear() === year && disabledDate.getMonth() === month && disabledDate.getDate() === day) {
          return true;
        }
      }
    }

    return false;
  };

  _proto.isDayDisabled = function isDayDisabled(day, month, year) {
    if (this.props.disabledDays) {
      var weekday = new Date(year, month, day);
      var weekdayNumber = weekday.getDay();
      return this.props.disabledDays.indexOf(weekdayNumber) !== -1;
    }

    return false;
  };

  _proto.updateInputfield = function updateInputfield(value) {
    if (!this.inputElement) {
      return;
    }

    var formattedValue = "";

    if (value) {
      try {
        if (this.isSingleSelection()) {
          formattedValue = this.isValidDate(value) ? this.formatDateTime(value) : "";
        } else if (this.isMultipleSelection()) {
          for (var i = 0; i < value.length; i++) {
            var selectedValue = value[i];
            var dateAsString = this.isValidDate(selectedValue) ? this.formatDateTime(selectedValue) : "";
            formattedValue += dateAsString;

            if (i !== value.length - 1) {
              formattedValue += ", ";
            }
          }
        } else if (this.isRangeSelection()) {
          if (value && value.length) {
            var startDate = value[0];
            var endDate = value[1];
            formattedValue = this.isValidDate(startDate) ? this.formatDateTime(startDate) : "";

            if (endDate) {
              formattedValue += this.isValidDate(endDate) ? " - " + this.formatDateTime(endDate) : "";
            }
          }
        }
      } catch (err) {
        formattedValue = value;
      }
    }

    this.inputElement.value = formattedValue;
  };

  _proto.formatDateTime = function formatDateTime(date) {
    var formattedValue = null;

    if (date) {
      formattedValue = this.formatDate(date, this.props.dateFormat);
    }

    return formattedValue;
  };

  _proto.formatDate = function formatDate(date, format) {
    if (!date) {
      return "";
    }

    var iFormat;

    var lookAhead = function lookAhead(match) {
      var matches = iFormat + 1 < format.length && format.charAt(iFormat + 1) === match;

      if (matches) {
        iFormat++;
      }

      return matches;
    },
        formatNumber = function formatNumber(match, value, len) {
      var num = "" + value;

      if (lookAhead(match)) {
        while (num.length < len) {
          num = "0" + num;
        }
      }

      return num;
    },
        formatName = function formatName(match, value, shortNames, longNames) {
      return lookAhead(match) ? longNames[value] : shortNames[value];
    };

    var output = "";
    var literal = false;

    if (date) {
      for (iFormat = 0; iFormat < format.length; iFormat++) {
        if (literal) {
          if (format.charAt(iFormat) === "'" && !lookAhead("'")) {
            literal = false;
          } else {
            output += format.charAt(iFormat);
          }
        } else {
          switch (format.charAt(iFormat)) {
            case "d":
              output += formatNumber("d", date.getDate(), 2);
              break;

            case "D":
              output += formatName("D", date.getDay(), this.state.localeData.dayNamesShort, this.state.localeData.dayNames);
              break;

            case "o":
              output += formatNumber("o", Math.round((new Date(date.getFullYear(), date.getMonth(), date.getDate()).getTime() - new Date(date.getFullYear(), 0, 0).getTime()) / 86400000), 3);
              break;

            case "m":
              output += formatNumber("m", date.getMonth() + 1, 2);
              break;

            case "M":
              output += formatName("M", date.getMonth(), this.state.localeData.monthNamesShort, this.state.localeData.monthNames);
              break;

            case "y":
              output += lookAhead("y") ? date.getFullYear() : (date.getFullYear() % 100 < 10 ? "0" : "") + date.getFullYear() % 100;
              break;

            case "@":
              output += date.getTime();
              break;

            case "!":
              output += date.getTime() * 10000 + this.ticksTo1970;
              break;

            case "'":
              if (lookAhead("'")) {
                output += "'";
              } else {
                literal = true;
              }

              break;

            default:
              output += format.charAt(iFormat);
          }
        }
      }
    }

    return output;
  };

  _proto.formatTime = function formatTime(date) {
    if (!date) {
      return "";
    }

    var output = "";
    var hours = date.getHours();
    var minutes = date.getMinutes();
    output += hours < 10 ? "0" + hours : hours;
    output += ":";
    output += minutes < 10 ? "0" + minutes : minutes;
    return output;
  };

  _proto.parseValueFromString = function parseValueFromString(text) {
    if (!text || text.trim().length === 0) {
      return null;
    }

    var value;

    if (this.isSingleSelection()) {
      value = this.parseDateTime(text);
    } else if (this.isMultipleSelection()) {
      var tokens = text.split(",");
      value = [];

      for (var _iterator2 = _createForOfIteratorHelperLoose(tokens), _step2; !(_step2 = _iterator2()).done;) {
        var token = _step2.value;
        value.push(this.parseDateTime(token.trim()));
      }
    } else if (this.isRangeSelection()) {
      var _tokens = text.split(" - ");

      value = [];

      for (var i = 0; i < _tokens.length; i++) {
        value[i] = this.parseDateTime(_tokens[i].trim());
      }
    }

    return value;
  };

  _proto.parseDateTime = function parseDateTime(text) {
    var date;
    date = this.parseDate(text, this.props.dateFormat);
    return date;
  };

  _proto.populateTime = function populateTime(value, timeString, ampm) {
    var time = this.parseTime(timeString, ampm);
    value.setHours(time.hour);
    value.setMinutes(time.minute);
    value.setSeconds(time.second);
    value.setMilliseconds(time.millisecond);
  };

  _proto.parseTime = function parseTime(value, ampm) {
    var tokens = value.split(":");

    if (tokens[0].length !== 2 || tokens[1].length !== 2 || tokens[3].length !== 3) {
      throw new Error("Invalid time");
    }

    var h = parseInt(tokens[0], 10);
    var m = parseInt(tokens[1], 10);
    var s = null;
    var ms = null;

    if (isNaN(h) || isNaN(m) || h > 23 || m > 59) {
      return {
        hour: h,
        minute: m,
        second: s,
        millisecond: ms
      };
    }
  };

  _proto.parseDate = function parseDate(value, format) {
    if (format == null || value == null) {
      throw new Error("Invalid arguments");
    }

    value = typeof value === "object" ? value.toString() : value + "";

    if (value === "") {
      return null;
    }

    var iFormat,
        dim,
        extra,
        iValue = 0,
        shortYearCutoff = typeof this.props.shortYearCutoff !== "string" ? this.props.shortYearCutoff : new Date().getFullYear() % 100 + parseInt(this.props.shortYearCutoff, 10),
        year = -1,
        month = -1,
        day = -1,
        doy = -1,
        literal = false,
        date,
        lookAhead = function lookAhead(match) {
      var matches = iFormat + 1 < format.length && format.charAt(iFormat + 1) === match;

      if (matches) {
        iFormat++;
      }

      return matches;
    },
        getNumber = function getNumber(match) {
      var isDoubled = lookAhead(match),
          size = match === "@" ? 14 : match === "!" ? 20 : match === "y" && isDoubled ? 4 : match === "o" ? 3 : 2,
          minSize = match === "y" ? size : 1,
          digits = new RegExp("^\\d{" + minSize + "," + size + "}"),
          num = value.substring(iValue).match(digits);

      if (!num) {
        throw new Error("Missing number at position " + iValue);
      }

      iValue += num[0].length;
      return parseInt(num[0], 10);
    },
        getName = function getName(match, shortNames, longNames) {
      var index = -1;
      var arr = lookAhead(match) ? longNames : shortNames;
      var names = [];

      for (var i = 0; i < arr.length; i++) {
        names.push([i, arr[i]]);
      }

      names.sort(function (a, b) {
        return -(a[1].length - b[1].length);
      });

      for (var _i = 0; _i < names.length; _i++) {
        var name = names[_i][1];

        if (value.substr(iValue, name.length).toLowerCase() === name.toLowerCase()) {
          index = names[_i][0];
          iValue += name.length;
          break;
        }
      }

      if (index !== -1) {
        return index + 1;
      } else {
        throw new Error("Unknown name at position " + iValue);
      }
    },
        checkLiteral = function checkLiteral() {
      if (value.charAt(iValue) !== format.charAt(iFormat)) {
        throw new Error("Unexpected literal at position " + iValue);
      }

      iValue++;
    };

    if (this.props.view === "month") {
      day = 1;
    }

    for (iFormat = 0; iFormat < format.length; iFormat++) {
      if (literal) {
        if (format.charAt(iFormat) === "'" && !lookAhead("'")) {
          literal = false;
        } else {
          checkLiteral();
        }
      } else {
        switch (format.charAt(iFormat)) {
          case "d":
            day = getNumber("d");
            break;

          case "D":
            getName("D", this.state.localeData.dayNamesShort, this.state.localeData.dayNames);
            break;

          case "o":
            doy = getNumber("o");
            break;

          case "m":
            month = getNumber("m");
            break;

          case "M":
            month = getName("M", this.state.localeData.monthNamesShort, this.state.localeData.monthNames);
            break;

          case "y":
            year = getNumber("y");
            break;

          case "@":
            date = new Date(getNumber("@"));
            year = date.getFullYear();
            month = date.getMonth() + 1;
            day = date.getDate();
            break;

          case "!":
            date = new Date((getNumber("!") - this.ticksTo1970) / 10000);
            year = date.getFullYear();
            month = date.getMonth() + 1;
            day = date.getDate();
            break;

          case "'":
            if (lookAhead("'")) {
              checkLiteral();
            } else {
              literal = true;
            }

            break;

          default:
            checkLiteral();
        }
      }
    }

    if (iValue < value.length) {
      extra = value.substr(iValue);

      if (!/^\s+/.test(extra)) {
        throw new Error("Extra/unparsed characters found in date: " + extra);
      }
    }

    if (year === -1) {
      year = new Date().getFullYear();
    } else if (year < 100) {
      year += new Date().getFullYear() - new Date().getFullYear() % 100 + (year <= shortYearCutoff ? 0 : -100);
    }

    if (doy > -1) {
      month = 1;
      day = doy;

      do {
        dim = this.getDaysCountInMonth(year, month - 1);

        if (day <= dim) {
          break;
        }

        month++;
        day -= dim;
      } while (true);
    }

    date = this.daylightSavingAdjust(new Date(year, month - 1, day));

    if (date.getFullYear() !== year || date.getMonth() + 1 !== month || date.getDate() !== day) {
      throw new Error("Invalid date");
    }

    return date;
  };

  _proto.renderBackwardNavigator = function renderBackwardNavigator() {
    var _this9 = this;

    return /*#__PURE__*/React.createElement("button", {
      type: "button",
      className: "p-datepicker-prev p-link",
      onClick: this.onPrevButtonClick,
      onKeyDown: function onKeyDown(e) {
        return _this9.onContainerButtonKeydown(e);
      }
    }, /*#__PURE__*/React.createElement("span", {
      className: "p-datepicker-prev-icon pi pi-chevron-left"
    }));
  };

  _proto.renderForwardNavigator = function renderForwardNavigator() {
    var _this10 = this;

    return /*#__PURE__*/React.createElement("button", {
      type: "button",
      className: "p-datepicker-next p-link",
      onClick: this.onNextButtonClick,
      onKeyDown: function onKeyDown(e) {
        return _this10.onContainerButtonKeydown(e);
      }
    }, /*#__PURE__*/React.createElement("span", {
      className: "p-datepicker-next-icon pi pi-chevron-right"
    }));
  };

  _proto.isInMinYear = function isInMinYear(viewDate) {
    return this.props.minDate && this.props.minDate.getFullYear() === viewDate.getFullYear();
  };

  _proto.isInMaxYear = function isInMaxYear(viewDate) {
    return this.props.maxDate && this.props.maxDate.getFullYear() === viewDate.getFullYear();
  };

  _proto.renderTitleMonthElement = function renderTitleMonthElement(month) {
    var _this11 = this;

    if (this.props.monthNavigator && this.props.view !== "month") {
      var viewDate = this.getViewDate();
      var viewMonth = viewDate.getMonth();
      return /*#__PURE__*/React.createElement("select", {
        className: "p-datepicker-month",
        onChange: this.onMonthDropdownChange,
        value: viewMonth
      }, this.state.localeData.monthNames.map(function (month, index) {
        if ((!_this11.isInMinYear(viewDate) || index >= _this11.props.minDate.getMonth()) && (!_this11.isInMaxYear(viewDate) || index <= _this11.props.maxDate.getMonth())) {
          return /*#__PURE__*/React.createElement("option", {
            key: month,
            value: index
          }, month);
        }

        return null;
      }));
    } else {
      return /*#__PURE__*/React.createElement("span", {
        className: "p-datepicker-month"
      }, this.state.localeData.monthNames[month]);
    }
  };

  _proto.renderTitleYearElement = function renderTitleYearElement(year) {
    var _this12 = this;

    if (this.props.yearNavigator) {
      var yearOptions = [];
      var years = this.props.yearRange.split(":");
      var yearStart = parseInt(years[0], 10);
      var yearEnd = parseInt(years[1], 10);

      for (var i = yearStart; i <= yearEnd; i++) {
        yearOptions.push(i);
      }

      var viewDate = this.getViewDate();
      var viewYear = viewDate.getFullYear();
      return /*#__PURE__*/React.createElement("select", {
        className: "p-datepicker-year",
        onChange: this.onYearDropdownChange,
        value: viewYear
      }, yearOptions.map(function (year) {
        if (!(_this12.props.minDate && _this12.props.minDate.getFullYear() > year) && !(_this12.props.maxDate && _this12.props.maxDate.getFullYear() < year)) {
          return /*#__PURE__*/React.createElement("option", {
            key: year,
            value: year
          }, year);
        }

        return null;
      }));
    } else {
      return /*#__PURE__*/React.createElement("span", {
        className: "p-datepicker-year"
      }, year);
    }
  };

  _proto.renderTitle = function renderTitle(monthMetaData) {
    var month = this.renderTitleMonthElement(monthMetaData.month);
    var year = this.renderTitleYearElement(monthMetaData.year);
    return /*#__PURE__*/React.createElement("div", {
      className: "p-datepicker-title"
    }, month, year);
  };

  _proto.renderDayNames = function renderDayNames(weekDays) {
    var dayNames = weekDays.map(function (weekDay) {
      return /*#__PURE__*/React.createElement("th", {
        key: weekDay,
        scope: "col"
      }, /*#__PURE__*/React.createElement("span", null, weekDay));
    });

    if (this.props.showWeek) {
      var weekHeader = /*#__PURE__*/React.createElement("th", {
        scope: "col",
        key: "wn",
        className: "p-datepicker-weekheader p-disabled"
      }, /*#__PURE__*/React.createElement("span", null, this.state.localeData["weekHeader"]));
      return [weekHeader].concat(dayNames);
    } else {
      return dayNames;
    }
  };

  _proto.renderDateCellContent = function renderDateCellContent(date, className, groupIndex) {
    var _this13 = this;

    var content = this.props.dateTemplate ? this.props.dateTemplate(date) : date.day;
    return /*#__PURE__*/React.createElement("span", {
      className: className,
      onClick: function onClick(e) {
        return _this13.onDateSelect(e, date);
      },
      onKeyDown: function onKeyDown(e) {
        return _this13.onDateCellKeydown(e, date, groupIndex);
      }
    }, content);
  };

  _proto.renderWeek = function renderWeek(weekDates, weekNumber, groupIndex) {
    var _this14 = this;

    var week = weekDates.map(function (date) {
      var selected = _this14.isSelected(date);

      var cellClassName = classNames({
        "p-datepicker-other-month": date.otherMonth,
        "p-datepicker-today": date.today
      });
      var dateClassName = classNames({
        "p-highlight": selected,
        "p-disabled": !date.selectable
      });
      var content = date.otherMonth && !_this14.props.showOtherMonths ? null : _this14.renderDateCellContent(date, dateClassName, groupIndex);
      return /*#__PURE__*/React.createElement("td", {
        key: date.day,
        className: cellClassName
      }, content);
    });

    if (this.props.showWeek) {
      var weekNumberCell = /*#__PURE__*/React.createElement("td", {
        key: "wn" + weekNumber,
        className: "p-datepicker-weeknumber"
      }, /*#__PURE__*/React.createElement("span", {
        className: "p-disabled"
      }, weekNumber));
      return [weekNumberCell].concat(week);
    } else {
      return week;
    }
  };

  _proto.renderDates = function renderDates(monthMetaData, groupIndex) {
    var _this15 = this;

    return monthMetaData.dates.map(function (weekDates, index) {
      return /*#__PURE__*/React.createElement("tr", {
        key: index
      }, _this15.renderWeek(weekDates, monthMetaData.weekNumbers[index], groupIndex));
    });
  };

  _proto.renderDateViewGrid = function renderDateViewGrid(monthMetaData, weekDays, groupIndex) {
    var dayNames = this.renderDayNames(weekDays);
    var dates = this.renderDates(monthMetaData, groupIndex);
    return /*#__PURE__*/React.createElement("div", {
      className: "p-datepicker-calendar-container"
    }, /*#__PURE__*/React.createElement("table", {
      className: "p-datepicker-calendar"
    }, /*#__PURE__*/React.createElement("thead", null, /*#__PURE__*/React.createElement("tr", null, dayNames)), /*#__PURE__*/React.createElement("tbody", null, dates)));
  };

  _proto.renderMonth = function renderMonth(monthMetaData, index) {
    var weekDays = this.createWeekDays();
    var backwardNavigator = index === 0 ? this.renderBackwardNavigator() : null;
    var forwardNavigator = this.props.numberOfMonths === 1 || index === this.props.numberOfMonths - 1 ? this.renderForwardNavigator() : null;
    var title = this.renderTitle(monthMetaData);
    var dateViewGrid = this.renderDateViewGrid(monthMetaData, weekDays, index);
    var header = this.props.headerTemplate ? this.props.headerTemplate() : null;
    return /*#__PURE__*/React.createElement("div", {
      key: monthMetaData.month,
      className: "p-datepicker-group"
    }, /*#__PURE__*/React.createElement("div", {
      className: "p-datepicker-header"
    }, header, backwardNavigator, forwardNavigator, title), dateViewGrid);
  };

  _proto.renderMonths = function renderMonths(monthsMetaData) {
    var _this16 = this;

    return monthsMetaData.map(function (monthMetaData, index) {
      return _this16.renderMonth(monthMetaData, index);
    });
  };

  _proto.renderDateView = function renderDateView() {
    var viewDate = this.getViewDate();
    var monthsMetaData = this.createMonths(viewDate.getMonth(), viewDate.getFullYear());
    var months = this.renderMonths(monthsMetaData);
    return /*#__PURE__*/React.createElement(React.Fragment, null, months);
  };

  _proto.renderMonthViewMonth = function renderMonthViewMonth(index) {
    var _this17 = this;

    var className = classNames("p-monthpicker-month", {
      "p-highlight": this.isMonthSelected(index)
    });
    var monthName = this.state.localeData.monthNamesShort[index];
    return /*#__PURE__*/React.createElement("span", {
      key: monthName,
      className: className,
      onClick: function onClick(event) {
        return _this17.onMonthSelect(event, index);
      },
      onKeyDown: function onKeyDown(event) {
        return _this17.onMonthCellKeydown(event, index);
      }
    }, monthName);
  };

  _proto.renderMonthViewMonths = function renderMonthViewMonths() {
    var months = [];

    for (var i = 0; i <= 11; i++) {
      months.push(this.renderMonthViewMonth(i));
    }

    return months;
  };

  _proto.renderMonthView = function renderMonthView() {
    var backwardNavigator = this.renderBackwardNavigator();
    var forwardNavigator = this.renderForwardNavigator();
    var yearElement = this.renderTitleYearElement(this.getViewDate().getFullYear());
    var months = this.renderMonthViewMonths();
    return /*#__PURE__*/React.createElement(React.Fragment, null, /*#__PURE__*/React.createElement("div", {
      className: "p-datepicker-header"
    }, backwardNavigator, forwardNavigator, /*#__PURE__*/React.createElement("div", {
      className: "p-datepicker-title"
    }, yearElement)), /*#__PURE__*/React.createElement("div", {
      className: "p-monthpicker"
    }, months));
  };

  _proto.renderDatePicker = function renderDatePicker() {
    if (this.props.view === "date") {
      return this.renderDateView();
    } else if (this.props.view === "month") {
      return this.renderMonthView();
    } else {
      return null;
    }
  };

  _proto.renderInputElement = function renderInputElement() {
    var _this18 = this;

    if (!this.props.inline) {
      var className = classNames("p-inputtext p-component", this.props.inputClassName);
      return /*#__PURE__*/React.createElement(InputText, {
        ref: function ref(el) {
          return _this18.inputElement = ReactDOM.findDOMNode(el);
        },
        id: this.props.inputId,
        name: this.props.name,
        type: "text",
        className: className,
        style: this.props.inputStyle,
        readOnly: this.props.readOnlyInput,
        disabled: this.props.disabled,
        required: this.props.required,
        autoComplete: "off",
        placeholder: this.props.placeholder,
        onInput: this.onUserInput,
        onFocus: this.onInputFocus,
        onBlur: this.onInputBlur,
        onKeyDown: this.onInputKeyDown,
        "aria-labelledby": this.props.ariaLabelledBy
      });
    } else {
      return null;
    }
  };

  _proto.renderButton = function renderButton() {
    if (this.props.showIcon) {
      return /*#__PURE__*/React.createElement(Button, {
        type: "button",
        icon: this.props.icon,
        onClick: this.onButtonClick,
        tabIndex: "-1",
        disabled: this.props.disabled,
        className: "p-datepicker-trigger p-calendar-button"
      });
    } else {
      return null;
    }
  };

  _proto.renderButtonBar = function renderButtonBar() {
    var _this19 = this;

    if (this.props.showButtonBar) {
      return /*#__PURE__*/React.createElement("div", {
        className: "p-datepicker-buttonbar"
      }, /*#__PURE__*/React.createElement(Button, {
        type: "button",
        label: this.state.localeData.today,
        onClick: this.onTodayButtonClick,
        onKeyDown: function onKeyDown(e) {
          return _this19.onContainerButtonKeydown(e);
        },
        className: this.props.todayButtonClassName
      }), /*#__PURE__*/React.createElement(Button, {
        type: "button",
        label: this.state.localeData.clear,
        onClick: this.onClearButtonClick,
        onKeyDown: function onKeyDown(e) {
          return _this19.onContainerButtonKeydown(e);
        },
        className: this.props.clearButtonClassName
      }));
    } else {
      return null;
    }
  };

  _proto.renderFooter = function renderFooter() {
    if (this.props.footerTemplate) {
      var content = this.props.footerTemplate();
      return /*#__PURE__*/React.createElement("div", {
        className: "p-datepicker-footer"
      }, content);
    } else {
      return null;
    }
  };

  _proto.render = function render() {
    var _this20 = this;

    var className = classNames("p-calendar", this.props.className, {
      "p-calendar-w-btn": this.props.showIcon,
      "p-inputwrapper-filled": this.props.value || DomHandler.hasClass(this.inputElement, "p-filled") && this.inputElement.value !== ""
    });
    var panelClassName = classNames("p-datepicker p-component", this.props.panelClassName, {
      "p-datepicker-inline": this.props.inline,
      "p-input-overlay": !this.props.inline,
      "p-shadow": !this.props.inline,
      "p-disabled": this.props.disabled,
      "p-datepicker-multiple-month": this.props.numberOfMonths > 1,
      "p-datepicker-monthpicker": this.props.view === "month",
      "p-datepicker-touch-ui": this.props.touchUI
    });
    var input = this.renderInputElement();
    var button = this.renderButton();
    var datePicker = this.renderDatePicker();
    var buttonBar = this.renderButtonBar();
    var footer = this.renderFooter();
    return /*#__PURE__*/React.createElement("span", {
      ref: function ref(el) {
        return _this20.container = el;
      },
      id: this.props.id,
      className: className,
      style: this.props.style
    }, input, button, /*#__PURE__*/React.createElement(CalendarPanel, {
      ref: function ref(el) {
        return _this20.panel = ReactDOM.findDOMNode(el);
      },
      className: panelClassName,
      style: this.props.panelStyle,
      appendTo: this.props.appendTo
    }, datePicker, buttonBar, footer));
  };

  return Calendar;
}(Component);

Calendar.defaultProps = {
  id: null,
  name: null,
  value: null,
  viewDate: null,
  style: null,
  className: null,
  inline: false,
  selectionMode: "single",
  inputId: null,
  inputStyle: null,
  inputClassName: null,
  required: false,
  readOnlyInput: false,
  keepInvalid: false,
  disabled: false,
  tabIndex: null,
  placeholder: null,
  showIcon: false,
  icon: "pi pi-calendar",
  showOnFocus: true,
  numberOfMonths: 1,
  view: "date",
  touchUI: false,
  shortYearCutoff: "+10",
  hideOnDateTimeSelect: false,
  showWeek: false,
  locale: "en",
  dateFormat: "mm/dd/yy",
  panelStyle: null,
  panelClassName: null,
  monthNavigator: false,
  yearNavigator: false,
  disabledDates: null,
  disabledDays: null,
  minDate: null,
  maxDate: null,
  maxDateCount: null,
  showOtherMonths: true,
  selectOtherMonths: false,
  showButtonBar: false,
  todayButtonClassName: "p-button-secondary",
  clearButtonClassName: "p-button-secondary",
  autoZIndex: true,
  baseZIndex: 0,
  appendTo: null,
  tooltip: null,
  tooltipOptions: null,
  ariaLabelledBy: null,
  dateTemplate: null,
  headerTemplate: null,
  footerTemplate: null,
  onFocus: null,
  onBlur: null,
  onInput: null,
  onSelect: null,
  onChange: null,
  onViewDateChange: null,
  onTodayButtonClick: null,
  onClearButtonClick: null
};
Calendar.propTypes = {
  id: propTypes.string,
  name: propTypes.string,
  value: propTypes.any,
  viewDate: propTypes.any,
  style: propTypes.object,
  className: propTypes.string,
  inline: propTypes.bool,
  selectionMode: propTypes.string,
  inputId: propTypes.string,
  inputStyle: propTypes.object,
  inputClassName: propTypes.string,
  required: propTypes.bool,
  readOnlyInput: propTypes.bool,
  keepInvalid: propTypes.bool,
  disabled: propTypes.bool,
  tabIndex: propTypes.string,
  placeholder: propTypes.string,
  showIcon: propTypes.bool,
  icon: propTypes.string,
  showOnFocus: propTypes.bool,
  numberOfMonths: propTypes.number,
  view: propTypes.string,
  touchUI: propTypes.bool,
  shortYearCutoff: propTypes.string,
  hideOnDateTimeSelect: propTypes.bool,
  showWeek: propTypes.bool,
  locale: propTypes.string,
  dateFormat: propTypes.string,
  panelStyle: propTypes.object,
  panelClassName: propTypes.string,
  monthNavigator: propTypes.bool,
  yearNavigator: propTypes.bool,
  disabledDates: propTypes.array,
  disabledDays: propTypes.array,
  minDate: propTypes.any,
  maxDate: propTypes.any,
  maxDateCount: propTypes.number,
  showOtherMonths: propTypes.bool,
  selectOtherMonths: propTypes.bool,
  showButtonBar: propTypes.bool,
  todayButtonClassName: propTypes.string,
  clearButtonClassName: propTypes.string,
  autoZIndex: propTypes.bool,
  baseZIndex: propTypes.number,
  appendTo: propTypes.any,
  tooltip: propTypes.string,
  tooltipOptions: propTypes.object,
  ariaLabelledBy: propTypes.string,
  dateTemplate: propTypes.func,
  headerTemplate: propTypes.func,
  footerTemplate: propTypes.func,
  onFocus: propTypes.func,
  onBlur: propTypes.func,
  onInput: propTypes.func,
  onSelect: propTypes.func,
  onChange: propTypes.func,
  onViewDateChange: propTypes.func,
  onTodayButtonClick: propTypes.func,
  onClearButtonClick: propTypes.func
};

export default Calendar;
//# sourceMappingURL=index.modern.js.map
