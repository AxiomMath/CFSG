module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.I71RedComp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.I71RedTransfer
public import CFSG.LocalAnalysis.GLTheoremA.CatC.I71RedD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs61
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.Helpers (quasisimple_central_quotient_nonabelian)

private theorem i71_D4_of_isD4 (d : TauCeti.LieTypeIndex) (hd : d.Valid) (h : isD4ThreePowThree d) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid),
      d = TauCeti.LieTypeIndex.D 4 q ∧ q.p = 3 ∧ 3 ∣ q.exponent := by
  cases d with
  | D n q =>
    by_cases hn : n = 4
    · subst hn
      exact ⟨q, hd, rfl, h.1, h.2⟩
    · exfalso
      unfold isD4ThreePowThree at h
      split at h <;> simp_all
  | _ => exact (show False from h).elim

private theorem isPOmegaEightPlusChar_of_catalog {S : Type} [Group S]
    (h : catalogIs S (onLie isD4ThreePowThree)) : IsPOmegaEightPlusChar 3 S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact (show False from hi).elim
  | alternating _ _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim
  | lie j =>
    obtain ⟨q, hv, hdq, hq3, -⟩ := i71_D4_of_isD4 j.1 j.2 hi
    have hj : j = ⟨.D 4 q, hv⟩ := Subtype.ext hdq
    subst hj
    exact ⟨q, hv, hq3, ⟨e⟩⟩

section Main

set_option linter.unusedSectionVars false


theorem i71i117At_of_charThree (G : Type) [Group G] [Finite G] (h33 : NoTrialityCharThreeAt G)
    (p : ℕ) : I71I117At G p := by
  intro hp hp2 B x L hK hB hx hL hBL hch
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hL
  have hS : IsSimpleGroup (PSimple p L) := hq.2
  have hnab : ∃ a b : PSimple p L, a * b ≠ b * a :=
    quasisimple_central_quotient_nonabelian _ hq
  have hno : ∀ D : Subgroup (MulAut (PSimple p L)), D ≤ actImage p L B → IsElemAbelian p D →
      Nat.card D = p ^ 2 → D ⊓ inner (PSimple p L) = ⊥ → False := by
    intro D hDP hD hcard hDI
    obtain ⟨h3, hcat⟩ := kd76c_holds hp hp2 (kd76cLieP_holds p hp hp2) (PSimple p L) hS hnab hch
      D hD hcard hDI
    subst h3
    exact no_E9_of_noTrialityAt (h33 B x L hB hx hL hBL (isPOmegaEightPlusChar_of_catalog hcat))
      hDP hD hcard hDI
  have hP : Nat.card ↥(actImage p L B) ≤ p * Nat.card ↥(actImage p L B ⊓ inner (PSimple p L)) :=
    le_mul_card_of_no_sq hp (isElemAbelian_actImage_gen hB.1 hBL) hno
  exact card_le_of_actImage hp hL hBL hP

end Main

end CFSG.LocalAnalysis.GLTheoremA
