module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGPin
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial

theorem SG.spModel_of_innLabel {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) {lab : GLALabel} (hlab : InnLabelOf B S lab)
    (ht : lab.tag = .B ∨ lab.tag = .C) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ lab.n ∧
      IsSimpleGroup (StatedProj (StatedSp lab.rank F)) ∧
      (∃ a b : StatedProj (StatedSp lab.rank F), a * b ≠ b * a) ∧
      ∃ Φ : PSimple 3 S ≃* StatedProj (StatedSp lab.rank F),
        ∀ (b : Ω) (hbN : b ∈ Subgroup.normalizer (S : Set Ω)), b ∈ B →
          ∃ g : StatedSp lab.rank F,
            MulAut.congr Φ (chevAut 3 S ⟨b, hbN⟩) =
              MulAut.conj (SymplecticFlag.proj lab.rank F g) := by
  have hraw := SG.exists_rawDatum_chevAut h hlab
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht ⊢
  replace hraw : CFSG.Assembly.LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I _ =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ ∃ Φ : PSimple 3 S ≃* R,
        ∀ (b : Ω) (hbN : b ∈ Subgroup.normalizer (S : Set Ω)), b ∈ B →
          MulAut.congr Φ (chevAut 3 S ⟨b, hbN⟩) ∈ I := by
    rcases ht with rfl | rfl <;> exact hraw
  obtain ⟨F, _, _, hF, hs, hnc, Φ, hΦ⟩ := hraw
  have hc2 : CharP F 2 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
  refine ⟨F, inferInstance, inferInstance, hc2, hF, hs, hnc, Φ, fun b hbN hb => ?_⟩
  obtain ⟨A, hA⟩ := Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage (hΦ b hbN hb)
  obtain ⟨s, hsA⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
  exact ⟨s, hA.symm.trans (hsA.trans (SymplecticHigher.conjAut_statedSp s))⟩

end CFSG.LocalAnalysis.GLTheoremA.S265

end
