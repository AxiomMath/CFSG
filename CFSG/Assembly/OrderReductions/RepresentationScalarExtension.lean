module

public import CFSG.Assembly.OrderReductions.QuadraticSolvableOdd

public section

namespace CFSG.OrderReductions.RepresentationScalarExtension

open scoped TensorProduct

theorem tensor_one_injective {field extension vector : Type*} [Field field] [Field extension]
    [Algebra field extension] [AddCommGroup vector] [Module field vector] :
    Function.Injective (fun element : vector => (1 : extension) ⊗ₜ[field] element) := by
  classical
  obtain ⟨functional, functional_one⟩ := Module.Projective.exists_dual_eq_one field
    (show (1 : extension) ≠ 0 from one_ne_zero)
  intro first second equal
  have mapped := congrArg (fun tensor : TensorProduct field extension vector =>
    TensorProduct.lid field vector (TensorProduct.map functional (LinearMap.id : vector →ₗ[field] vector) tensor)) equal
  simpa only [TensorProduct.map_tmul, functional_one, LinearMap.id_apply, TensorProduct.lid_tmul,
    one_smul] using mapped

@[expose] def scalarExtension {field vector actors : Type*} [Field field] [AddCommGroup vector]
    [Module field vector] [Group actors] (extension : Type*) [Field extension]
    [Algebra field extension] (representation : Representation field actors vector) :
    Representation extension actors (TensorProduct field extension vector) where
  toFun actor := (representation actor).baseChange extension
  map_one' := by rw [map_one, LinearMap.baseChange_one]
  map_mul' first second := by rw [map_mul, LinearMap.baseChange_mul]

theorem scalarExtension_apply {field extension vector actors : Type*} [Field field] [Field extension]
    [Algebra field extension] [AddCommGroup vector] [Module field vector] [Group actors]
    (representation : Representation field actors vector) (actor : actors) :
    scalarExtension extension representation actor = (representation actor).baseChange extension := rfl

theorem scalarExtension_quadratic {field extension vector actors : Type*} [Field field] [Field extension]
    [Algebra field extension] [AddCommGroup vector] [Module field vector] [Group actors]
    (representation : Representation field actors vector) (actor : actors)
    (square_zero : (representation actor - 1) * (representation actor - 1) = 0) :
    (scalarExtension extension representation actor - 1) *
      (scalarExtension extension representation actor - 1) = 0 := by
  have mapped := congrArg (LinearMap.baseChange extension) square_zero
  rw [LinearMap.baseChange_mul, LinearMap.baseChange_sub, LinearMap.baseChange_one] at mapped
  rw [scalarExtension_apply]
  refine mapped.trans ?_
  apply TensorProduct.AlgebraTensorModule.ext
  intro scalar element
  simp only [LinearMap.baseChange_tmul, LinearMap.zero_apply, TensorProduct.tmul_zero]

theorem identity_of_scalarExtension_identity {field extension vector actors : Type*} [Field field]
    [Field extension] [Algebra field extension] [AddCommGroup vector] [Module field vector] [Group actors]
    (representation : Representation field actors vector) (actor : actors)
    (identity : scalarExtension extension representation actor = 1) : representation actor = 1 := by
  apply LinearMap.ext
  intro element
  apply tensor_one_injective (field := field) (extension := extension)
  have fixed := congrArg (fun operator : Module.End extension (TensorProduct field extension vector) =>
    operator ((1 : extension) ⊗ₜ[field] element)) identity
  simpa only [scalarExtension_apply, LinearMap.baseChange_tmul, Module.End.one_apply] using fixed

theorem exists_prime_power_identity {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] [Finite actors] [Group.IsSolvable actors]
    (prime : ℕ) [Fact (Nat.Prime prime)] [CharP field prime]
    (representation : Representation field actors vector) (odd_order : Odd (Nat.card actors))
    (first second : actors) (generates : Subgroup.closure ({first, second} : Set actors) = ⊤)
    (first_square : (representation first - 1) * (representation first - 1) = 0)
    (second_square : (representation second - 1) * (representation second - 1) = 0) :
    ∀ actor : actors, ∃ exponent : ℕ, representation actor ^ (prime ^ exponent) = 1 := by
  have result := CFSG.OrderReductions.QuadraticSolvableOdd.exists_prime_power_identity prime
    (scalarExtension (AlgebraicClosure field) representation) odd_order first second generates
    (scalarExtension_quadratic representation first first_square)
    (scalarExtension_quadratic representation second second_square)
  intro actor
  obtain ⟨exponent, powered_identity⟩ := result actor
  refine ⟨exponent, ?_⟩
  rw [← map_pow] at powered_identity
  rw [← map_pow]
  exact identity_of_scalarExtension_identity representation _ powered_identity

end CFSG.OrderReductions.RepresentationScalarExtension
