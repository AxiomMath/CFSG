module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Gen

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup

variable {K : Type} [Group K]

section Sylow

variable [Finite K]

theorem elemFactsIn_sylow (hP : P12Facts) (hK : SolomonA12HypK K) (S : Sylow 2 K) :
    ElemFactsIn (S : Subgroup K) := by
  obtain ⟨S₀, S', ⟨e⟩⟩ := hK.sylowType
  have hS₀ : ElemFactsIn (S₀ : Subgroup K) := ElemFactsIn.of_mulEquiv e (hP.sylow S')
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S₀ S
  refine ElemFactsIn.of_mulEquiv ?_ hS₀
  rw [← hg]
  exact (Sylow.equivSMul S₀ g).symm

theorem two_part_card (hP : P12Facts) (hK : SolomonA12HypK K) :
    (Nat.card K).factorization 2 = 9 := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 K))
  have hS : Nat.card S = 2 ^ 9 := (elemFactsIn_sylow hP hK S).1
  have hmult : Nat.card S = 2 ^ (Nat.card K).factorization 2 := Sylow.card_eq_multiplicity S
  rw [hS] at hmult
  exact (Nat.pow_right_injective (le_refl 2) hmult).symm

theorem ElemFactsIn.le_of_elem {Q E A : Subgroup K} (hQ : ElemFactsIn Q) (hEQ : E ≤ Q)
    (hEsq : ∀ x ∈ E, x * x = 1) (hEcard : Nat.card E = 2 ^ 6) (hAQ : A ≤ Q)
    (hAsq : ∀ x ∈ A, x * x = 1) (hA : 2 ^ 6 ≤ Nat.card A) : A ≤ E := by
  obtain ⟨-, -, E₀, hE₀Q, hE₀sq, hE₀card, hmax⟩ := hQ
  have hE_le : E ≤ E₀ := hmax E hEQ hEsq (by simp [hEcard])
  have hcard : Nat.card E₀ ≤ Nat.card E := by simp [hE₀card, hEcard]
  have hEq : E = E₀ := Subgroup.eq_of_le_of_card_ge hE_le hcard
  rw [hEq]
  exact hmax A hAQ hAsq hA

theorem GoodE.conj_eq_of_le (hP : P12Facts) (hK : SolomonA12HypK K) {E : Subgroup K}
    (hE : GoodE E) {S : Sylow 2 K} (hES : E ≤ S) {g : K}
    (hg : E.map (MulAut.conj g).toMonoidHom ≤ S) : E.map (MulAut.conj g).toMonoidHom = E := by
  let E' : Subgroup K := E.map (MulAut.conj g).toMonoidHom
  have hE'sq : ∀ x ∈ E', x * x = 1 := by
    rintro x ⟨y, hy, rfl⟩
    rw [← map_mul, hE.sq y hy, map_one]
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hE'le : E' ≤ E :=
    ElemFactsIn.le_of_elem (elemFactsIn_sylow hP hK S) hES hE.sq hE.card hg hE'sq
      (by simp [hE'card, hE.card])
  change E' = E
  exact Subgroup.eq_of_le_of_card_ge hE'le (by simp [hE'card])

theorem GoodE.normalizer_sylow_le (hP : P12Facts) (hK : SolomonA12HypK K) {E : Subgroup K}
    (hE : GoodE E) {S : Sylow 2 K} (hES : E ≤ S) :
    normalizer (S : Set K) ≤ normalizer (E : Set K) := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff] at hg ⊢
  have hmap_le : E.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro x ⟨y, hy, rfl⟩
    show g * y * g⁻¹ ∈ (S : Subgroup K)
    exact (hg y).mp (show y ∈ (S : Set K) from hES hy)
  have hconj : E.map (MulAut.conj g).toMonoidHom = E :=
    GoodE.conj_eq_of_le hP hK hE hES hmap_le
  intro h
  constructor
  · intro hh
    have hmem : g * h * g⁻¹ ∈ E.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (show h ∈ E from hh)
    rwa [hconj] at hmem
  · intro hh
    have hhmap : g * h * g⁻¹ ∈ E.map (MulAut.conj g).toMonoidHom := by
      rw [hconj]
      exact hh
    obtain ⟨y, hy, hyh⟩ := hhmap
    have hyh' : y = h := by
      have hyh'' : g * y * g⁻¹ = g * h * g⁻¹ := hyh
      exact mul_left_cancel (mul_right_cancel hyh'')
    rwa [← hyh']

end Sylow

end CFSG.EvenSporadicStandard.M12Std.SolomonK
