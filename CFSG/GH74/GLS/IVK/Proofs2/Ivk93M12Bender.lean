module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Crit
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Bender
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.GH74.GLS.LU.Local.A3Reduce2
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.GH74.Uniqueness.Bender.SuzukiOdd
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSemidihedralKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.Walter.J1

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open CFSG.GH74.Uniqueness.Bender

theorem ivk93m12_no_cent_shape {c : ℕ} (hc : c = 16 ∨ c = 64 ∨ c = 320) :
    ∀ n m : ℕ, (n = 8 ∨ n = 32 ∨ n = 96 ∨ n = 192) → Odd m → n * m ≠ c := by
  intro n m hn hm
  obtain ⟨k, rfl⟩ := hm
  rcases hn with rfl | rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl <;> omega

theorem ivk93m12_l216 :
    Ivk93M12Empty (fun X _ => LieModel X .PSL 2 2 4) := by
  intro J _ _ hJ y D
  obtain ⟨e⟩ := KGroups.equiv_psl2_of_lieModel_even (S := J) (f := 4) (by norm_num) hJ
  have hB : BenderType J 4 1 1 := .linear 4 (by norm_num) e
  have hcard := bender_card_centralizer_involution hB D.mul_self_eq_one D.ne_one
  exact D.false_of_cent_card_eq (c := 16) (by rw [hcard]; norm_num)
    (ivk93m12_no_cent_shape (Or.inl rfl))

theorem ivk93m12_u34 :
    Ivk93M12Empty (fun X _ => LieModel X .PSU 3 2 2) := by
  intro J _ _ hJ y D
  have hS := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  obtain ⟨e⟩ := (RankTwoShapes.statedClassicalModel_PSU_three_two_iff J 2 le_rfl).1 hS
  have hB : BenderType J 2 3 _ := .unitary 2 le_rfl e
  have hcard := bender_card_centralizer_involution hB D.mul_self_eq_one D.ne_one
  exact D.false_of_cent_card_eq (c := 320) (by rw [hcard]; norm_num)
    (ivk93m12_no_cent_shape (Or.inr (Or.inr rfl)))

theorem ivk93m12_szModel_equiv {J : Type} [Group J] (h : SuzukiModel J 2 3) :
    Nonempty (J ≃* CFSG.Theory.Comparator.SzModel 1) := by
  obtain ⟨-, a, ha, K, _, _, hf, hcard, ⟨e⟩⟩ := h
  have ha1 : a = 1 := by omega
  subst ha1
  exact ⟨(e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup 1 K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative 1 ha hcard))).trans
    (MulEquiv.subgroupCongr (szModel_eq_open_sz 1).symm)⟩

theorem ivk93m12_sz8 :
    Ivk93M12Empty (fun X _ => LieModel X .twistedB2 0 2 3) := by
  intro J _ _ hJ y D
  have hS : SuzukiModel J 2 3 := by
    rcases hJ with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hS
  obtain ⟨e⟩ := ivk93m12_szModel_equiv hS
  have hB : BenderType J (2 * 1 + 1) 2 1 := .suzuki 1 le_rfl e
  have hcard := bender_card_centralizer_involution hB D.mul_self_eq_one D.ne_one
  exact D.false_of_cent_card_eq (c := 64) (by rw [hcard]; norm_num)
    (ivk93m12_no_cent_shape (Or.inr (Or.inl rfl)))

end CFSG.GH74.GLS.IVK.Proofs2
