module

public import CFSG.FeitThompson.Representations.InductionCoprimePowerCommutes
public import CFSG.FeitThompson.Representations.CoprimePowerPermutesIrreducibles
public import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
import CFSG.FeitThompson.Representations.LinearIrreduciblesKillDerived
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.PowerOperationsPreserveVirtualChars

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalLinearInduced

open scoped ComplexConjugate

section Aux

variable {K : Type*} [Group K]

def nonprincipalLinearIrr (K : Type*) [Group K] : Set (K → ℂ) :=
  {θ ∈ Irr K | θ 1 = 1 ∧ θ ≠ 1}

theorem mem_nonprincipalLinearIrr {θ : K → ℂ} :
    θ ∈ nonprincipalLinearIrr K ↔ θ ∈ Irr K ∧ θ 1 = 1 ∧ θ ≠ 1 := Iff.rfl

theorem nonprincipalLinearIrr_subset_Irr : nonprincipalLinearIrr K ⊆ Irr K := fun _ h => h.1

theorem finite_nonprincipalLinearIrr [Finite K] : (nonprincipalLinearIrr K).Finite :=
  finite_Irr.subset nonprincipalLinearIrr_subset_Irr

theorem powOp_mem_nonprincipalLinearIrr [Finite K] {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k.Coprime (Nat.card K)) {θ : K → ℂ} (hθ : θ ∈ nonprincipalLinearIrr K) :
    powOp k θ ∈ nonprincipalLinearIrr K := by
  refine ⟨powOp_mem_Irr hk1 hk hθ.1, by rw [powOp_apply_one]; exact hθ.2.1, fun h => ?_⟩
  refine hθ.2.2 (powOp_injective (M := ℂ)
    (Nat.Coprime.pow_left_bijective hk.symm).surjective ?_)
  rw [h, powOp_one_fun]

theorem conj_mem_nonprincipalLinearIrr [Finite K] {θ : K → ℂ}
    (hθ : θ ∈ nonprincipalLinearIrr K) : (fun x => conj (θ x)) ∈ nonprincipalLinearIrr K := by
  refine ⟨conj_mem_Irr hθ.1, by simpa using congrArg conj hθ.2.1, fun h => hθ.2.2 ?_⟩
  funext x
  simpa using congrArg conj (congrFun h x)

theorem eq_one_of_mem_commutator {θ : K → ℂ} (hθ : θ ∈ nonprincipalLinearIrr K) {x : K}
    (hx : x ∈ commutator K) : θ x = 1 := by
  rw [mem_charValueKernel.1 (Irr.commutator_subset_charValueKernel hθ.1 hθ.2.1 hx), hθ.2.1]

end Aux

variable {L : Type*} [Group L] (K : Subgroup L)

theorem coe_mem_commutator_iff {x : K} :
    (x : L) ∈ (⁅K, K⁆ : Subgroup L) ↔ x ∈ commutator (K : Type _) := by
  rw [← Subgroup.map_subtype_commutator K]
  refine ⟨fun h => ?_, fun h => ⟨x, h, rfl⟩⟩
  obtain ⟨y, hy, hyx⟩ := h
  exact Subtype.ext hyx ▸ hy

private theorem natCard_div_natCard_eq_index [Finite L] :
    (Nat.card L : ℂ) / (Nat.card (K : Type _) : ℂ) = (K.index : ℂ) := by
  have hK : (Nat.card (K : Type _) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [div_eq_iff hK, ← Nat.cast_mul]
  exact_mod_cast (Subgroup.index_mul_card K).symm

variable [Fintype L]

noncomputable def indFamLinear : Set (L → ℂ) := indFam K (nonprincipalLinearIrr K)

theorem indFamLinear_eq_indFam : indFamLinear K = indFam K (nonprincipalLinearIrr K) := (rfl)

theorem mem_indFamLinear {f : L → ℂ} :
    f ∈ indFamLinear K ↔ ∃ θ ∈ nonprincipalLinearIrr (K : Type _), indClassFun K θ = f := by
  rw [indFamLinear_eq_indFam, mem_indFam]

theorem indClassFun_mem_indFamLinear {θ : K → ℂ} (hθ : θ ∈ nonprincipalLinearIrr (K : Type _)) :
    indClassFun K θ ∈ indFamLinear K := (mem_indFamLinear K).2 ⟨θ, hθ, rfl⟩

theorem finite_indFamLinear : (indFamLinear K).Finite :=
  indFam_finite K finite_nonprincipalLinearIrr

theorem indFamLinear_subset_indFam_Irr : indFamLinear K ⊆ indFam K (Irr (K : Type _)) :=
  indFam_mono K nonprincipalLinearIrr_subset_Irr

theorem conj_eq_of_mem_indFamLinear {η : L → ℂ} (hη : η ∈ indFamLinear K) (x y : L) :
    η (x * y * x⁻¹) = η y :=
  conj_eq_of_mem_indFam K hη x y

theorem powOp_mem_indFamLinear {k : ℕ} (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card L))
    {η : L → ℂ} (hη : η ∈ indFamLinear K) : powOp k η ∈ indFamLinear K := by
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFamLinear K).1 hη
  rw [powOp_indClassFun K hk.symm]
  exact indClassFun_mem_indFamLinear K (powOp_mem_nonprincipalLinearIrr hk1
    (hk.coprime_dvd_right (Subgroup.card_subgroup_dvd_card K)) hθ)

theorem powOp_bijOn_indFamLinear {k : ℕ} (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card L)) :
    Set.BijOn (powOp k) (indFamLinear K) (indFamLinear K) := by
  obtain ⟨b, hb1, hb⟩ := exists_one_le_mul_modEq_one (G := L) hk1 hk
  exact ⟨fun _ hη => powOp_mem_indFamLinear K hk1 hk hη,
    fun _ _ _ _ h => powOp_injective (Nat.Coprime.pow_left_bijective hk.symm).surjective h,
    fun η hη => ⟨powOp b η, powOp_mem_indFamLinear K hb1
      (coprime_right_of_mul_modEq_one hb) hη, powOp_powOp_eq_self' hb η⟩⟩

theorem powOp_bijOn_indFamLinear_of_dvd {n k : ℕ} (hn : Nat.card L ∣ n) (hk1 : 1 ≤ k)
    (hk : k.Coprime n) : Set.BijOn (powOp k) (indFamLinear K) (indFamLinear K) :=
  powOp_bijOn_indFamLinear K hk1 (hk.coprime_dvd_right hn)

noncomputable def indFamLinearPowPerm {k : ℕ} (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card L)) :
    Equiv.Perm (indFamLinear K) :=
  (powOp_bijOn_indFamLinear K hk1 hk).equiv _

@[simp] theorem coe_indFamLinearPowPerm_apply {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k.Coprime (Nat.card L)) (η : indFamLinear K) :
    ((indFamLinearPowPerm K hk1 hk η : indFamLinear K) : L → ℂ) = powOp k (η : L → ℂ) := (rfl)

theorem apply_one_of_mem_indFamLinear {η : L → ℂ} (hη : η ∈ indFamLinear K) :
    η 1 = (K.index : ℂ) := by
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFamLinear K).1 hη
  rw [indClassFun_one, hθ.2.1, mul_one, natCard_div_natCard_eq_index]

theorem eq_zero_of_mem_indFamLinear_of_notMem [K.Normal] {η : L → ℂ} (hη : η ∈ indFamLinear K)
    {y : L} (hy : y ∉ K) : η y = 0 :=
  eq_zero_of_mem_indFam_of_notMem K hη hy

theorem ne_one_of_mem_indFamLinear {η : L → ℂ} (hη : η ∈ indFamLinear K) : η ≠ 1 := by
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFamLinear K).1 hη
  have : Fintype (K : Type _) := Fintype.ofFinite _
  have hres : resClassFun K (1 : L → ℂ) = 1 := by funext x; simp
  have h0 : cfInner (indClassFun K θ) (1 : L → ℂ) = 0 := by
    rw [cfInner_indClassFun K θ (Irr_subset_classFun one_mem_Irr), hres,
      cfInner_eq_ite_of_mem_Irr hθ.1 one_mem_Irr, if_neg hθ.2.2]
  intro h
  rw [h, cfInner_def] at h0
  simp [Nat.card_eq_fintype_card, Fintype.card_ne_zero] at h0

theorem apply_eq_apply_one_of_mem_commutator [K.Normal] {η : L → ℂ} (hη : η ∈ indFamLinear K)
    {z : L} (hz : z ∈ (⁅K, K⁆ : Subgroup L)) : η z = η 1 := by
  classical
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFamLinear K).1 hη
  rw [indClassFun_apply, apply_one_of_mem_indFamLinear K (indClassFun_mem_indFamLinear K hθ)]
  have hall : ∀ t : L, (if h : t⁻¹ * z * t ∈ K then θ ⟨t⁻¹ * z * t, h⟩ else 0) = 1 := by
    intro t
    have hc : t⁻¹ * z * t ∈ (⁅K, K⁆ : Subgroup L) := by
      have := (Subgroup.commutator_normal K K).conj_mem _ hz t⁻¹
      simpa [mul_assoc] using this
    rw [dif_pos (Subgroup.commutator_le_self K hc)]
    exact eq_one_of_mem_commutator hθ ((coe_mem_commutator_iff K).1 hc)
  rw [Finset.sum_congr rfl fun t _ => hall t]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Nat.card_eq_fintype_card]
  rw [← natCard_div_natCard_eq_index K]
  field_simp

theorem apply_eq_index_of_mem_commutator [K.Normal] {η : L → ℂ} (hη : η ∈ indFamLinear K)
    {z : L} (hz : z ∈ (⁅K, K⁆ : Subgroup L)) : η z = (K.index : ℂ) := by
  rw [apply_eq_apply_one_of_mem_commutator K hη hz, apply_one_of_mem_indFamLinear K hη]

theorem indClassFun_conj_fun (θ : K → ℂ) :
    indClassFun K (fun x => conj (θ x)) = fun y => conj (indClassFun K θ y) := by
  classical
  funext y
  rw [indClassFun_apply, indClassFun_apply, map_mul, map_sum]
  simp only [map_inv₀, Complex.conj_natCast]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  split <;> simp

theorem conj_mem_indFamLinear {η : L → ℂ} (hη : η ∈ indFamLinear K) :
    (fun y => conj (η y)) ∈ indFamLinear K := by
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFamLinear K).1 hη
  rw [← indClassFun_conj_fun K θ]
  exact indClassFun_mem_indFamLinear K (conj_mem_nonprincipalLinearIrr hθ)

theorem two_le_ncard_indFamLinear (hodd : Odd (Nat.card L)) (hne : (indFamLinear K).Nonempty)
    (hsub : indFamLinear K ⊆ Irr L) : 2 ≤ (indFamLinear K).ncard := by
  obtain ⟨η, hη⟩ := hne
  have hpair : ({η, fun y => conj (η y)} : Set (L → ℂ)) ⊆ indFamLinear K := by
    rintro f (rfl | rfl)
    · exact hη
    · exact conj_mem_indFamLinear K hη
  have hne2 : η ≠ fun y => conj (η y) :=
    ne_conj_of_mem_Irr_of_ne_one_of_odd hodd (hsub hη) (ne_one_of_mem_indFamLinear K hη)
  calc 2 = ({η, fun y => conj (η y)} : Set (L → ℂ)).ncard := (Set.ncard_pair hne2).symm
    _ ≤ (indFamLinear K).ncard := Set.ncard_le_ncard hpair (finite_indFamLinear K)

end NormalLinearInduced

end CFSG.FeitThompson
