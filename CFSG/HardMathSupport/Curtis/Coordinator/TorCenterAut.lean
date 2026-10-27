module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ComponentClassification

variable {K : Type} [Field K]

theorem linearAutGroup_eq_range : linearAutGroup 3 K = (conjAut 3 K).range :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup_eq_range

theorem mem_linearAutGroup_of_three_pow {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card K = 2 ^ f)
    (h3 : ¬ 3 ∣ f) {α : MulAut (projectiveSL 3 K)} {k : ℕ} (hα : α ^ 3 ^ k = 1) :
    α ∈ linearAutGroup 3 K := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos (by norm_num) f).ne')
  have hR := (automorphism_generation (K := K) (n := 3) le_rfl).1
  obtain ⟨hID, -, hDnorm, -, -, -, -, hRE, -, -⟩ := standard_outer_quotients (n := 3) (K := K)
  rw [hR] at hDnorm hRE
  have hDE : linearAutGroup 3 K ≤ semilinearAutGroup 3 K := linearAutGroup_le_semilinearAutGroup
  have hDn : (linearAutGroup 3 K).Normal := ⟨fun d hd g =>
    hDnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨g, Subgroup.mem_top g⟩⟩
  have hE : semilinearAutGroup 3 K = linearAutGroup 3 K ⊔ (fieldAut 3 K).range := by
    rw [semilinearAutGroup, Subgroup.closure_union, Subgroup.closure_eq, ← MonoidHom.coe_range,
      Subgroup.closure_eq]
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hk
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have h2 : (linearAutGroup 3 K).relIndex (semilinearAutGroup 3 K) ∣ f := by
    rw [hE, Subgroup.relIndex_sup_left, ← hcard]
    refine (Subgroup.index_dvd_card _).trans ?_
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_card _
  have h3' : (semilinearAutGroup 3 K).index ∣ 2 := by
    have hle : (semilinearAutGroup 3 K).index ≤ 2 := by
      rwa [← Subgroup.relIndex_top_right]
    have : Finite (MulAut (projectiveSL 3 K)) :=
      Finite.of_injective (fun e : MulAut (projectiveSL 3 K) => (e : projectiveSL 3 K →
        projectiveSL 3 K)) fun a b hab => MulEquiv.ext (congrFun hab)
    have h0 : (semilinearAutGroup 3 K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (by omega : (semilinearAutGroup 3 K).index = 1 ∨
        (semilinearAutGroup 3 K).index = 2) with h | h <;> rw [h]
    · exact one_dvd 2
  have hidx : (linearAutGroup 3 K).index ∣ f * 2 := by
    rw [← Subgroup.relIndex_mul_index hDE]
    exact Nat.mul_dvd_mul h2 h3'
  have hcop : Nat.Coprime (3 ^ k) (linearAutGroup 3 K).index := by
    refine Nat.Coprime.pow_left _ ?_
    refine Nat.Coprime.coprime_dvd_right hidx ?_
    refine Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3) ?_
    norm_num
  have hq : (QuotientGroup.mk α : MulAut (projectiveSL 3 K) ⧸ linearAutGroup 3 K) = 1 := by
    have h1 : orderOf (QuotientGroup.mk α : MulAut (projectiveSL 3 K) ⧸ linearAutGroup 3 K) ∣
        3 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hα]; rfl)
    have h2 : orderOf (QuotientGroup.mk α : MulAut (projectiveSL 3 K) ⧸ linearAutGroup 3 K) ∣
        (linearAutGroup 3 K).index := orderOf_dvd_natCard _
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  exact (QuotientGroup.eq_one_iff α).mp hq

theorem exists_slConjugation_of_three_pow {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card K = 2 ^ f)
    (h3 : ¬ 3 ∣ f) {β : MulAut (SpecialLinearGroup (Fin 3) K)} {k : ℕ} (hβ : β ^ 3 ^ k = 1) :
    ∃ A : GL (Fin 3) K, β = CatalogueBHigherLinearAction.slConjugation 3 K A := by
  have hα : descendAut 3 K β ^ 3 ^ k = 1 := by rw [← map_pow, hβ, map_one]
  have hD := mem_linearAutGroup_of_three_pow hf hk h3 hα
  rw [linearAutGroup_eq_range] at hD
  obtain ⟨A, hA⟩ := hD
  exact ⟨A, RankThree.PartOne.AUTSL.descendAut_injective (by norm_num) hA.symm⟩

end CFSG.HardMathSupport.Curtis.Coordinator
