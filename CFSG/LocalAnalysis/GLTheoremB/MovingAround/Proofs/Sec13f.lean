module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13a

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut IsLocallyBalanced IsWeaklyLocallyBalanced)
open scoped MatrixGroups

namespace Sec13f

section Helpers

variable {G : Type} [Group G] [Finite G]

abbrev PiSummand (p : ℕ) (H : Subgroup G) : Type :=
  {L : Subgroup G // GLAPComponent p H L ∧ IsPiGroup p (↥L ⧸ GLAPPrimeCore p ↥L)}

theorem piLayer_eq_iSup_subtype (p : ℕ) (H : Subgroup G) :
    piLayer p H = ⨆ i : PiSummand p H, i.1 := by
  unfold piLayer
  exact le_antisymm (iSup₂_le fun L h => le_iSup_of_le ⟨L, h⟩ le_rfl)
    (iSup_le fun i => le_iSup₂_of_le i.1 i.2 le_rfl)

theorem piLayer_le (p : ℕ) (H : Subgroup G) : piLayer p H ≤ H := by
  unfold piLayer
  exact iSup₂_le fun L h => h.1.1

theorem le_piLayer {p : ℕ} {H L : Subgroup G} (hL : GLAPComponent p H L)
    (hP : IsPiGroup p (↥L ⧸ GLAPPrimeCore p ↥L)) : L ≤ piLayer p H :=
  le_iSup₂_of_le (f := fun L (_ : GLAPComponent p H L ∧ IsPiGroup p (↥L ⧸ GLAPPrimeCore p ↥L)) => L)
    L ⟨hL, hP⟩ le_rfl

theorem barX_piLayer_le_of_forall {p : ℕ} {M H : Subgroup G} (hHM : H ≤ M)
    {X : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)}
    (hcon : ∀ L0 : Subgroup G, GLAPComponent p H L0 → IsPiGroup p (↥L0 ⧸ GLAPPrimeCore p ↥L0) →
      barX p M L0 ≤ X) :
    barX p M (piLayer p H) ≤ X := by
  rw [piLayer_eq_iSup_subtype]
  have hsub : ∀ i : PiSummand p H, i.1 ≤ M := fun i => le_trans i.2.1.1 hHM
  have key : barX p M (⨆ i : PiSummand p H, i.1) ≤ ⨆ i : PiSummand p H, barX p M i.1 :=
    barX_iSup_le_iSup (p := p) (C := M) (ι := PiSummand p H) (fun i => i.1) hsub
  exact le_trans key (iSup_le fun i => hcon i.1 i.2.1 i.2.2)

theorem exists_piComp_not_le {p : ℕ} (hp : p.Prime) {M H : Subgroup G} (hHM : H ≤ M)
    {X : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)} (hnot : ¬ barX p M (piLayer p H) ≤ X) :
    ∃ L0 : Subgroup G, GLAPComponent p (piLayer p H) L0 ∧ ¬ barX p M L0 ≤ X := by
  have hfam : ∃ L0 : Subgroup G, GLAPComponent p H L0 ∧
      IsPiGroup p (↥L0 ⧸ GLAPPrimeCore p ↥L0) ∧ ¬ barX p M L0 ≤ X := by
    by_contra hcon
    push Not at hcon
    exact hnot (barX_piLayer_le_of_forall hHM hcon)
  obtain ⟨L0, hL0, hPi, hnotL0⟩ := hfam
  have hLP : L0 ≤ piLayer p H := le_piLayer hL0 hPi
  have hPH : piLayer p H ≤ H := piLayer_le p H
  have hL0P : GLAPComponent p (piLayer p H) L0 := glaPComponent_of_le hp hL0 hLP hPH
  exact ⟨L0, hL0P, hnotL0⟩

theorem sylowIn_above {p : ℕ} {M P : Subgroup G} (hPM : P ≤ M) (hP : IsPGroup p ↥P) :
    ∃ R : Subgroup G, IsSylowIn p M R ∧ P ≤ R := by
  obtain ⟨R, hPR, hRmax⟩ :=
    (Set.toFinite {R : Subgroup G | R ≤ M ∧ IsPGroup p ↥R}).exists_le_maximal ⟨hPM, hP⟩
  exact ⟨R, ⟨hRmax.1.1, hRmax.1.2, fun R' hR'M hR'p hRR' =>
    le_antisymm (hRmax.2 ⟨hR'M, hR'p⟩ hRR') hRR'⟩, hPR⟩

end Helpers

end Sec13f

open Sec13f

theorem prop1310_of_inputs (h139 : Prop139Statement) (h1311 : Lemma1311Statement)
    (h1316 : Lemma1316Statement) (ha5 : Prop1310_a5Statement) : Prop1310Statement := by
  intro G _ _ m p B M E A D T hs
  have hp : p.Prime := hs.standing.prime
  have hdisj : Prop139a p M D ∨ Prop139b p M D := h139 hs
  have hcov := (h1311 hs hdisj).1
  by_contra hnot
  rw [hcov] at hnot
  obtain ⟨d, hdD, hd1, hdnot⟩ : ∃ d : G, d ∈ D ∧ d ≠ 1 ∧
      ¬ barX p M (piLayer p (Istar p M D ⊓ Cg d)) ≤ barX p M (piStar p D) := by
    by_contra hcon
    push Not at hcon
    exact hnot (iSup_le fun d => iSup_le fun hdD => iSup_le fun hd1 => hcon d hdD hd1)
  have hHM : Istar p M D ⊓ Cg d ≤ M := inf_le_left.trans (istar_le_M p M D)
  obtain ⟨L0, hL0, hL0not⟩ := exists_piComp_not_le hp hHM hdnot
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hs.standing hs.bOne hs.pre
  have hAM : A ≤ M := hs.pair.1.2.1.1.1.1
  obtain ⟨R, hR, hABR⟩ := sylowIn_above (sup_le hAM hBM) hs.hAB
  have cex : Cex1310 G m p B M E A D T R L0 d :=
    ⟨hs, hdisj, ⟨hdD, hd1⟩, hL0, hL0not, ⟨hR, hABR⟩,
      fun L hL => (h1311 hs hdisj).2 d hdD hd1 L0 hL0 L hL⟩
  rcases hdisj with ha | hb
  · exact h1316 cex ha
  · exact ha5 cex hb

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
