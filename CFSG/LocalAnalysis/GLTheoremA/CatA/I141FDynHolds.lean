module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynOrders
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.I141F.Ord

@[expose] def CompTypeLie2 : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (labL : GLALabel) (β : MulAut S) (p : ℕ), p.Prime → p ≠ 2 →
    Subgroup.center S = ⊥ → CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β →
    β ^ p = 1 → β ≠ 1 → labL.tag ≠ .G2 → labL.tag ≠ .B2der → labL.tag ≠ .G2der →
    labL.tag ≠ .twF4der → labL.tag ≠ .twB2 →
    ∀ J : Subgroup S, CFSG.Open.IsComponentOf J (fixSubgroup β) →
      (∃ (t : StatedLieTag) (r e : ℕ),
          CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t r 2 e) ∨
        Nat.card (↥J ⧸ Subgroup.center ↥J) = 360

section Small


theorem tag_eq_G2_of_compTypeLie2 (hC : CompTypeLie2) {S : Type} [Group S] [Finite S]
    {labL : GLALabel} {β : MulAut S} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β)
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β))
    (hJc : Nat.card (↥J ⧸ Subgroup.center ↥J) = 6048) : labL.tag = .G2 := by
  by_contra hG2
  have hB2 : labL.tag ≠ .B2der := fun h =>
    false_of_small hcen hin hβ1 (Or.inl h) hJ hJc
  have hG2d : labL.tag ≠ .G2der := fun h =>
    false_of_small hcen hin hβ1 (Or.inr (Or.inl h)) hJ hJc
  have htwF4 : labL.tag ≠ .twF4der := fun h =>
    false_of_small hcen hin hβ1 (Or.inr (Or.inr (Or.inl h))) hJ hJc
  have htwB2 : labL.tag ≠ .twB2 := fun h =>
    false_of_small hcen hin hβ1 (Or.inr (Or.inr (Or.inr h))) hJ hJc
  rcases hC S labL β p hp hp2 hcen hin hβp hβ1 hG2 hB2 hG2d htwF4 htwB2 J hJ with
    ⟨t, r, e, hM⟩ | h360
  · exact card_ne_6048_of_compType (Or.inl ⟨t, r, e, hM⟩) hJc
  · exact card_ne_6048_of_compType (Or.inr h360) hJc

end Small

section Head


theorem i141DynkinLie_of_compTypeLie2 (hC : CompTypeLie2) : I141DynkinLie := by
  intro p hp hp2 Γ _ _ L K A y hlie hAel hAN hInn hyA hyC hK hG2
  obtain ⟨labL, β, J, hlab, hcen, hin, hβp, hβ1, hJ, hKiso⟩ :=
    exists_sLevel_of_i141 hp hp2 hlie hAel hInn hyA hyC hK
  have hJc : Nat.card (↥J ⧸ Subgroup.center ↥J) = 6048 := by
    rw [← Nat.card_congr hKiso.some.toEquiv]
    exact card_eq_6048_of_isG2der hG2
  have htag : labL.tag = .G2 :=
    tag_eq_G2_of_compTypeLie2 hC hp hp2 hcen hin hβp hβ1 hJ hJc
  exact catalogIs_isG2Quot_of_hasLabel_G2 hlab htag

end Head

end CFSG.LocalAnalysis.GLTheoremA.I141F
