module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableSp4
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowO

public section

namespace CFSG.GH74.Generic.BProg.B2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace PuL4GraphUniSplit

theorem central_quotient_sl2 {F : Type} [Field F] {Y X : Type} [Group Y] [Group X]
    (eY : Y ≃* Matrix.SpecialLinearGroup (Fin 2) F) (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∨
      Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  by_cases hker : σ.ker = ⊥
  · left
    exact ⟨(MulEquiv.ofBijective σ ⟨(MonoidHom.ker_eq_bot_iff σ).mp hker, hσs⟩).symm.trans eY⟩
  · right
    have hc : ∀ z ∈ center Y, eY z = 1 ∨ eY z = -1 := by
      intro z hz
      apply (CFSG.ComponentClassification.OddSelector.mem_center_sl_two_iff _).mp
      rw [mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := eY.surjective g
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz y]
    obtain ⟨k, hkK, hk1⟩ : ∃ k ∈ σ.ker, k ≠ 1 := by
      by_contra! hno
      exact hker ((Subgroup.eq_bot_iff_forall _).mpr hno)
    have hkneg : eY k = -1 := by
      rcases hc k (hσk hkK) with h1 | h1
      · exact absurd (eY.injective (h1.trans (map_one eY).symm)) hk1
      · exact h1
    have hle : center Y ≤ σ.ker := by
      intro z hz
      rcases hc z hz with h1 | h1
      · have : z = 1 := eY.injective (h1.trans (map_one eY).symm)
        rw [this]
        exact one_mem _
      · have : z = k := eY.injective (h1.trans hkneg.symm)
        rw [this]
        exact hkK
    have hkerc : σ.ker = center Y := le_antisymm hσk hle
    exact ⟨(QuotientGroup.quotientKerEquivOfSurjective σ hσs).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerc).trans
        (QuotientGroup.congr _ _ eY (Subgroup.map_center_eq eY)))⟩

section Certified


theorem false_of_uni_split {N : Type} [Group N] [Finite N] {H L : Subgroup N} {t : N}
    (hs : ShapeInCent H t L) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) (h4 : 4 ≤ p ^ f) {Y X : Type}
    [Group Y] [Group X] (eY : Y ≃* Matrix.SpecialLinearGroup (Fin 2) F) (σ : Y →* X)
    (hσs : Function.Surjective σ) (hσk : σ.ker ≤ center Y) (eLX : ↥L ≃* X) : False := by
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have hk : ringChar F ≠ 2 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd
  rcases central_quotient_sl2 eY σ hσs hσk with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact PumpupTableSp4.false_of_sl2_component hs hk (eLX.trans e)
  · exact PumpupTableOmega3.false_of_psl2_component hs hp hp2
      (PumpupTableOmega3.lieModel_psl2_of_equiv hp hf h4 hF (eLX.trans e))

end Certified

end PuL4GraphUniSplit

end CFSG.GH74.Generic.BProg.B2
