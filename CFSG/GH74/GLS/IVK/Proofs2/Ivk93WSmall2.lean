module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WLeaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95XSolv
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Bender
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Ord
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L34
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WTransport
public import CFSG.GH74.GLS.LU.Local.A3Reduce2
public import CFSG.GH74.GLS.Stage1.Main.Bridge
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.GLS.Stage2.Local.P34Stmt
public import CFSG.GH74.Generic.BarSubnormal
public import CFSG.GH74.Generic.S1.DecompCore
public import CFSG.GH74.Generic.S1.KL3Red
public import CFSG.GH74.Generic.S1.TFrame
public import CFSG.GH74.Generic.S1.TLeafA
public import CFSG.GH74.Generic.S1.TLeafBar
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.GH74.Uniqueness.Bender
open scoped MatrixGroups
open CFSG.ComponentClassification.PSL3Four (S_le_R nonempty_equiv_of_stated)
local notation "S42" => CFSG.ComponentClassification.PSL3Four.S
local notation "R42" => CFSG.ComponentClassification.PSL3Four.R

theorem ivk93w_l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93WEmpty (fun X _ => LieModel X .PSL 2 p f) := by
  intro p f hp hp2 hf J _ _ hJ x q B h _
  obtain ⟨k, _, _, hkcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hJ
  have hπ := ivk95x_isCentralQuot_of_equiv e
  obtain ⟨g, hg, hgc, -⟩ := hπ.lift_involution h.ord
  rw [← hg] at h
  exact h.false_of_solvable (hπ.solvable_centralizer (ivk95x_sl2_centralizer_solvable hgc))

theorem ivk93w_l28 :
    Ivk93WEmpty (fun X _ => LieModel X .PSL 2 2 3) := by
  intro J _ _ hJ x q B h _
  obtain ⟨e⟩ := KGroups.equiv_psl2_of_lieModel_even (S := J) (f := 3) (by norm_num) hJ
  have hB : BenderType J 3 1 1 := .linear 3 (by norm_num) e
  have hcard := bender_card_centralizer_involution hB h.mul_self_eq_one h.ne_one
  exact h.false_of_card_cent_dvd (N := 8) (by rw [hcard]; norm_num)
    (not_sl2_dvd_of_lt (by norm_num) (by norm_num))

theorem ivk93w_l216 :
    Ivk93WEmpty (fun X _ => LieModel X .PSL 2 2 4) := by
  intro J _ _ hJ x q B h _
  obtain ⟨e⟩ := KGroups.equiv_psl2_of_lieModel_even (S := J) (f := 4) (by norm_num) hJ
  have hB : BenderType J 4 1 1 := .linear 4 (by norm_num) e
  have hcard := bender_card_centralizer_involution hB h.mul_self_eq_one h.ne_one
  exact h.false_of_card_cent_dvd (N := 16) (by rw [hcard]; norm_num)
    (not_sl2_dvd_of_lt (by norm_num) (by norm_num))

theorem ivk93w_u34 :
    Ivk93WEmpty (fun X _ => LieModel X .PSU 3 2 2) := by
  intro J _ _ hJ x q B h _
  have hS := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  obtain ⟨e⟩ := (RankTwoShapes.statedClassicalModel_PSU_three_two_iff J 2 le_rfl).1 hS
  have hB : BenderType J 2 3 _ := .unitary 2 le_rfl e
  have hcard := bender_card_centralizer_involution hB h.mul_self_eq_one h.ne_one
  have h320 : Nat.card ↥(centralizer ({x} : Set J)) = 320 := by
    rw [hcard]
    norm_num
  exact h.false_of_card_cent_dvd (N := 320) (by rw [h320])
    (fun q _ => not_sl2_dvd_of_not_three (by norm_num) q)

theorem ivk93w_sz8 :
    Ivk93WEmpty (fun X _ => LieModel X .twistedB2 0 2 3) := by
  intro J _ _ hJ x q B h _
  obtain ⟨e⟩ := KGroups.Sz8.equiv_of_lieModel hJ
  have hcard : Nat.card J = 29120 := by
    rw [Nat.card_congr e.toEquiv, KGroups.card_group KGroups.Sz8.QP KGroups.Sz8.QP_ok,
      KGroups.Sz8.QP_valid.2]
  exact h.false_of_card_group (N := 29120) (by rw [hcard])
    (fun q _ => not_sl2_dvd_of_not_three (by norm_num) q)

theorem ivk93w_l34 :
    Ivk93WEmpty (fun X _ => LieModel X .PSL 3 2 2) := by
  intro J _ _ hJ x q B h _
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  obtain ⟨θ⟩ := nonempty_equiv_of_stated J hst
  have hcard := GHInv.card_centralizer_eq_centralizerIn S42 θ x
  have hx2 : orderOf ((θ x : ↥S42) : Equiv.Perm (Fin 42)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact h.ord
  have hxR : ((θ x : ↥S42) : Equiv.Perm (Fin 42)) ∈ R42 := S_le_R (θ x).2
  rcases l34_inv_cases hxR hx2 with ⟨c, hc', hce, h64⟩ | ⟨c, hc', hce, h168⟩ | ⟨c, hc', hce, h60⟩ |
    ⟨c, hc', hce, h72⟩
  · exact h.false_of_card_cent_dvd (N := 64) (by rw [hcard]; exact dvd_of_eq h64)
      (not_sl2_dvd_of_lt (by norm_num) (by norm_num))
  · exact h.false_of_card_cent_dvd (N := 168) (by rw [hcard]; exact dvd_of_eq h168)
      (fun q hq => not_sl2_dvd_168 q hq)
  · exact h.false_of_card_cent_dvd (N := 60) (by rw [hcard]; exact dvd_of_eq h60)
      (not_sl2_dvd_of_lt (by norm_num) (by norm_num))
  · exact h.false_of_card_cent_dvd (N := 72) (by rw [hcard]; exact dvd_of_eq h72)
      (not_sl2_dvd_of_lt (by norm_num) (by norm_num))

end CFSG.GH74.GLS.IVK.Proofs2
