module

public import CFSG.FeitThompson.Representations.CentralElementsSeparatedIrreducibles
import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module ComplexConjugate

noncomputable section

variable {G : Type*} [Group G]

instance finite_coe_irrChar [Finite G] : Finite (irrChar ℂ G) := finite_irrChar.to_subtype

theorem mem_classFun_of_mem_irrChar {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G) : χ ∈ classFun G :=
  Irr_subset_classFun (by rwa [Irr_eq_irrChar])

theorem mem_center_of_coeff_eq_of_isConj {k : Type*} [CommSemiring k] {x : MonoidAlgebra k G}
    (h : ∀ g g' : G, IsConj g g' → x.coeff g = x.coeff g') :
    x ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  rw [Subalgebra.mem_center_iff]
  intro y
  induction y using MonoidAlgebra.induction_on with
  | of g =>
      refine MonoidAlgebra.coeff_inj.1 ?_
      ext a
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply,
        MonoidAlgebra.coeff_mul_single_apply]
      simp only [one_mul, mul_one]
      exact h _ _ (isConj_iff.2 ⟨g, by group⟩)
  | add u v hu hv => rw [add_mul, mul_add, hu, hv]
  | smul r u hu => rw [smul_mul_assoc, mul_smul_comm, hu]

theorem eq_of_centralScalar_eq [Finite G] {z w : Subalgebra.center ℂ (MonoidAlgebra ℂ G)}
    (h : ∀ ψ : G → ℂ, ∀ hψ : ψ ∈ irrChar ℂ G, centralScalar hψ z = centralScalar hψ w) : z = w :=
  injective_centralScalarPi (funext fun χ => by
    rw [centralScalarPi_apply, centralScalarPi_apply]; exact h χ χ.2)

def centralIdempotent [Fintype G] (χ : G → ℂ) : MonoidAlgebra ℂ G :=
  ∑ g : G, MonoidAlgebra.single g (χ 1 / (Nat.card G : ℂ) * conj (χ g))

theorem coeff_centralIdempotent [Fintype G] (χ : G → ℂ) (g : G) :
    (centralIdempotent χ).coeff g = χ 1 / (Nat.card G : ℂ) * conj (χ g) := by
  classical
  rw [centralIdempotent, MonoidAlgebra.coeff_sum]
  simp only [Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_ite_eq' Finset.univ g fun c => χ 1 / (Nat.card G : ℂ) * conj (χ c)]
  simp

theorem coeff_centralIdempotent_eq_of_mem_irrChar [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ irrChar ℂ G) (g : G) :
    (centralIdempotent χ).coeff g = χ 1 / (Nat.card G : ℂ) * χ g⁻¹ := by
  rw [coeff_centralIdempotent]
  congr 1
  rw [← character_irrRep hχ,
    ← Representation.character_inv (irrRep hχ).ρ (isOfFinOrder_of_finite g)]

theorem centralIdempotent_mem_center [Fintype G] {χ : G → ℂ} (hχ : χ ∈ classFun G) :
    centralIdempotent χ ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
  refine mem_center_of_coeff_eq_of_isConj fun g g' hgg' => ?_
  rw [coeff_centralIdempotent, coeff_centralIdempotent, classFun.apply_eq_of_isConj hχ hgg']

def centralIdempotentCenter [Fintype G] {χ : G → ℂ} (hχ : χ ∈ classFun G) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) :=
  ⟨centralIdempotent χ, centralIdempotent_mem_center hχ⟩

@[simp]
theorem coe_centralIdempotentCenter [Fintype G] {χ : G → ℂ} (hχ : χ ∈ classFun G) :
    (centralIdempotentCenter hχ : MonoidAlgebra ℂ G) = centralIdempotent χ := (rfl)

theorem trace_asAlgebraHom_centralIdempotent [Fintype G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (χ : G → ℂ) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom (centralIdempotent χ)) =
      χ 1 * cfInner ρ.character χ := by
  simp only [centralIdempotent, map_sum, Representation.asAlgebraHom_single, map_smul,
    smul_eq_mul, cfInner_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  change χ 1 / (Nat.card G : ℂ) * conj (χ g) * ρ.character g = _
  rw [div_eq_mul_inv]
  ring

open scoped Classical in
theorem centralScalar_centralIdempotentCenter [Fintype G] {χ ψ : G → ℂ}
    (hχ : χ ∈ irrChar ℂ G) (hψ : ψ ∈ irrChar ℂ G) :
    centralScalar hψ (centralIdempotentCenter (mem_classFun_of_mem_irrChar hχ)) =
      if ψ = χ then 1 else 0 := by
  classical
  have hirr : Representation.IsIrreducible (irrRep hψ).ρ := irrRep_isIrreducible hψ
  have hchar : Representation.character (irrRep hψ).ρ = ψ := character_irrRep hψ
  set c := centralScalar hψ (centralIdempotentCenter (mem_classFun_of_mem_irrChar hχ)) with hc
  have hmap : Representation.asAlgebraHom (irrRep hψ).ρ (centralIdempotent χ) =
      c • LinearMap.id := by
    ext v
    have := asAlgebraHom_center_apply_eq_centralScalar_smul (irrRep hψ).ρ hψ hchar
      (centralIdempotentCenter (mem_classFun_of_mem_irrChar hχ)) v
    simpa [hc] using this
  have htr1 : LinearMap.trace ℂ (irrRep hψ).V
      (Representation.asAlgebraHom (irrRep hψ).ρ (centralIdempotent χ)) = c * ψ 1 := by
    rw [hmap, map_smul, LinearMap.trace_id, smul_eq_mul, ← Representation.char_one (irrRep hψ).ρ,
      hchar]
  have htr2 := trace_asAlgebraHom_centralIdempotent (irrRep hψ).ρ χ
  rw [hchar] at htr2
  have hin : cfInner ψ χ = if ψ = χ then 1 else 0 :=
    cfInner_eq_ite_of_mem_Irr (by rwa [Irr_eq_irrChar]) (by rwa [Irr_eq_irrChar])
  rw [htr1, hin] at htr2
  have hψ1 : ψ 1 ≠ 0 := by rw [← hchar]; exact character_one_ne_zero (irrRep hψ).ρ
  by_cases h : ψ = χ
  · rw [if_pos h]
    subst h
    rw [if_pos rfl, mul_one] at htr2
    exact mul_right_cancel₀ hψ1 (by rw [htr2, one_mul])
  · rw [if_neg h]
    rw [if_neg h, mul_zero] at htr2
    exact (mul_eq_zero.1 htr2).resolve_right hψ1

open scoped Classical in
theorem asAlgebraHom_centralIdempotent_apply [Fintype G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G) (v : V) :
    ρ.asAlgebraHom (centralIdempotent χ) v = if ρ.character = χ then v else 0 := by
  classical
  have hψ := character_mem_irrChar_of_isIrreducible ρ inferInstance
  have h := asAlgebraHom_center_apply_eq_centralScalar_smul ρ hψ rfl
    (centralIdempotentCenter (mem_classFun_of_mem_irrChar hχ)) v
  rw [coe_centralIdempotentCenter, centralScalar_centralIdempotentCenter hχ hψ] at h
  rw [h]
  split <;> simp

open scoped Classical in
theorem centralIdempotentCenter_mul_centralIdempotentCenter [Fintype G] {χ ψ : G → ℂ}
    (hχ : χ ∈ irrChar ℂ G) (hψ : ψ ∈ irrChar ℂ G) :
    centralIdempotentCenter (mem_classFun_of_mem_irrChar hχ) *
        centralIdempotentCenter (mem_classFun_of_mem_irrChar hψ) =
      if χ = ψ then centralIdempotentCenter (mem_classFun_of_mem_irrChar hχ) else 0 := by
  classical
  refine eq_of_centralScalar_eq fun φ hφ => ?_
  rw [map_mul, centralScalar_centralIdempotentCenter hχ hφ,
    centralScalar_centralIdempotentCenter hψ hφ, apply_ite (centralScalar hφ), map_zero,
    centralScalar_centralIdempotentCenter hχ hφ]
  by_cases hcs : χ = ψ
  · subst hcs; simp
  · rw [if_neg hcs]
    by_cases h1 : φ = χ
    · rw [if_pos h1, if_neg (fun h => hcs (h1 ▸ h)), mul_zero]
    · rw [if_neg h1, zero_mul]

open scoped Classical in
theorem centralIdempotent_mul_centralIdempotent [Fintype G] {χ ψ : G → ℂ}
    (hχ : χ ∈ irrChar ℂ G) (hψ : ψ ∈ irrChar ℂ G) :
    centralIdempotent χ * centralIdempotent ψ = if χ = ψ then centralIdempotent χ else 0 := by
  classical
  have h := congrArg (fun z : Subalgebra.center ℂ (MonoidAlgebra ℂ G) => (z : MonoidAlgebra ℂ G))
    (centralIdempotentCenter_mul_centralIdempotentCenter hχ hψ)
  simpa [apply_ite (fun z : Subalgebra.center ℂ (MonoidAlgebra ℂ G) =>
    (z : MonoidAlgebra ℂ G))] using h

theorem isIdempotentElem_centralIdempotent [Fintype G] {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G) :
    IsIdempotentElem (centralIdempotent χ) := by
  classical
  have h := centralIdempotent_mul_centralIdempotent hχ hχ
  rwa [if_pos rfl] at h

theorem sum_centralIdempotentCenter [Fintype G] [Fintype (irrChar ℂ G)] :
    ∑ χ : irrChar ℂ G, centralIdempotentCenter (mem_classFun_of_mem_irrChar χ.2) = 1 := by
  classical
  refine eq_of_centralScalar_eq fun ψ hψ => ?_
  rw [map_sum, map_one]
  have key : ∀ χ : irrChar ℂ G,
      centralScalar hψ (centralIdempotentCenter (mem_classFun_of_mem_irrChar χ.2)) =
        if (⟨ψ, hψ⟩ : irrChar ℂ G) = χ then 1 else 0 := by
    intro χ
    rw [centralScalar_centralIdempotentCenter χ.2 hψ]
    congr 1
    exact propext ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [Finset.sum_congr rfl fun χ _ => key χ,
    Finset.sum_ite_eq Finset.univ (⟨ψ, hψ⟩ : irrChar ℂ G) fun _ => (1 : ℂ)]
  simp

theorem sum_centralIdempotent [Fintype G] [Fintype (irrChar ℂ G)] :
    ∑ χ : irrChar ℂ G, centralIdempotent (χ : G → ℂ) = 1 := by
  have h := congrArg (fun z : Subalgebra.center ℂ (MonoidAlgebra ℂ G) => (z : MonoidAlgebra ℂ G))
    (sum_centralIdempotentCenter (G := G))
  simpa using h

theorem eq_sum_centralScalar_smul_centralIdempotentCenter [Fintype G] [Fintype (irrChar ℂ G)]
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) :
    z = ∑ χ : irrChar ℂ G,
      centralScalar χ.2 z • centralIdempotentCenter (mem_classFun_of_mem_irrChar χ.2) := by
  classical
  refine eq_of_centralScalar_eq fun ψ hψ => ?_
  rw [map_sum]
  have key : ∀ χ : irrChar ℂ G,
      centralScalar hψ (centralScalar χ.2 z •
          centralIdempotentCenter (mem_classFun_of_mem_irrChar χ.2)) =
        if (⟨ψ, hψ⟩ : irrChar ℂ G) = χ then centralScalar hψ z else 0 := by
    intro χ
    rw [map_smul, smul_eq_mul, centralScalar_centralIdempotentCenter χ.2 hψ]
    by_cases h : (⟨ψ, hψ⟩ : irrChar ℂ G) = χ
    · subst h; simp
    · rw [if_neg h, if_neg (fun he : ψ = (χ : G → ℂ) => h (Subtype.ext he)), mul_zero]
  rw [Finset.sum_congr rfl fun χ _ => key χ,
    Finset.sum_ite_eq Finset.univ (⟨ψ, hψ⟩ : irrChar ℂ G) fun _ => centralScalar hψ z]
  simp

theorem coe_eq_sum_centralScalar_smul_centralIdempotent [Fintype G] [Fintype (irrChar ℂ G)]
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) :
    (z : MonoidAlgebra ℂ G) =
      ∑ χ : irrChar ℂ G, centralScalar χ.2 z • centralIdempotent (χ : G → ℂ) := by
  have h := congrArg (fun w : Subalgebra.center ℂ (MonoidAlgebra ℂ G) => (w : MonoidAlgebra ℂ G))
    (eq_sum_centralScalar_smul_centralIdempotentCenter z)
  simpa using h

end

end CFSG.FeitThompson
