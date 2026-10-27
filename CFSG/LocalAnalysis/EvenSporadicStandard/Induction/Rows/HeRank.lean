module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SOInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RankE8
public import CFSG.Sporadic.Recognition.HeMultiplierCert
public import Certificates.Certificate27143

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Sporadic.He CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.He.Native (VOrbit genTables)

section Tables

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)] [FaithfulSMul G (Fin n)]

theorem eq_of_eqTab {T T' : Table} {g h : G} (hg : Rep n T g) (hh : Rep n T' h)
    (hT : eqTab n T T' = true) : g = h := by
  refine FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := Fin n) fun i => ?_
  apply Fin.ext
  have h1 := hg i.val i.isLt
  have h2 := hh i.val i.isLt
  have h3 := allIn_eq_true.1 hT i.val (Nat.zero_le _) i.isLt
  rw [beq_iff_eq] at h3
  rw [idx_of_lt g i.isLt] at h1
  rw [idx_of_lt h i.isLt] at h2
  exact h1.symm.trans (h3.trans h2)

theorem ne_of_eqTab_false {T T' : Table} {g h : G} (hg : Rep n T g) (hh : Rep n T' h)
    (hT : eqTab n T T' = false) : g ≠ h := by
  rintro rfl
  have : eqTab n T T' = true := by
    unfold eqTab
    rw [allIn_eq_true]
    intro i _ hi
    rw [hg i hi, hh i hi]
    exact beq_self_eq_true _
  rw [hT] at this
  exact Bool.false_ne_true this

end Tables


theorem three_le_pRank_J_of_check (O : VOrbit) (hO : ∀ z, Rep 8330 (genTables O z) (genG z))
    (h : heE8Check O = true) : 3 ≤ CFSG.pRank 2 CFSG.Sporadic.He.J := by
  have : Finite CFSG.Sporadic.He.J := Finite.of_equiv _ heEquivJ.toEquiv
  simp only [heE8Check, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, n1⟩, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩, n7⟩ := h
  have hw : ∀ w : List Int, Rep 8330 (wordT 8330 (genTables O) w) (wordG genG w) := fun w =>
    Rep.wordT (by norm_num) w (fun l _ => hO l)
  have hx := hw heWordE1
  have hy := hw heWordE2
  have hz := hw heWordE3
  have h1 : Rep 8330 (idT 8330) (1 : CFSG.Sporadic.He.J) := Rep.idT (by norm_num)
  exact three_le_pRank_of_three_involutions
    (eq_of_eqTab (Rep.compT hx hx) h1 e1) (eq_of_eqTab (Rep.compT hy hy) h1 e2)
    (eq_of_eqTab (Rep.compT hz hz) h1 e3)
    (eq_of_eqTab (Rep.compT hx hy) (Rep.compT hy hx) e4)
    (eq_of_eqTab (Rep.compT hx hz) (Rep.compT hz hx) e5)
    (eq_of_eqTab (Rep.compT hy hz) (Rep.compT hz hy) e6)
    (ne_of_eqTab_false hx h1 n1) (ne_of_eqTab_false hy h1 n2) (ne_of_eqTab_false hy hx n3)
    (ne_of_eqTab_false hz h1 n4) (ne_of_eqTab_false hz hx n5) (ne_of_eqTab_false hz hy n6)
    (ne_of_eqTab_false hz (Rep.compT hx hy) n7)


theorem heCoverRank_of_certificate : HeCoverRank := by
  intro X _ _ hq hX
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate X hq hX
  obtain ⟨e⟩ := hX
  have eJ : X ≃* CFSG.Sporadic.He.J := (((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).symm.trans e).trans heEquivJ
  have hp : CFSG.pRank 2 X = CFSG.pRank 2 CFSG.Sporadic.He.J := pRank_two_eq_of_mulEquiv' eJ
  rw [hp]
  have hO : ∀ z, Rep 8330 (genTables orb z) (genG z) := rep_gen
  have hc : heE8Check orb = true := Certificates.certificate27143
  exact three_le_pRank_J_of_check orb hO hc

end CFSG.EvenSporadicStandard.Induction
