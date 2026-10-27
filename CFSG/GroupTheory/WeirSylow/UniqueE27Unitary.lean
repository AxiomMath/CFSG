module

public import CFSG.GroupTheory.UniqueElemSylow
public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Background.A3Structure316
import CFSG.GroupTheory.UniqueElemSylowProj
import CFSG.GroupTheory.WeirSylow.SigmaThree
import CFSG.GroupTheory.WeirSylow.UniqueE27Symplectic
import CFSG.GroupTheory.WeirSylow.Unitary
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.GroupTheory.WeirSylow

open CFSG.Open
open CFSG.Quasithin (StatedGU)

theorem uniqueElemSylow_statedGU_of_div_eq_three (L : Type) [Field L] [Finite L] {q : ℕ}
    (hL : Nat.card L = q ^ 2) (hq : ¬ 3 ∣ q) {n : ℕ}
    (hn : n / orderOf (-(q : ZMod 3)) = 3) : UniqueElemSylow 3 3 (StatedGU n q L) := by
  letI := Fintype.ofFinite L
  have hL' : Fintype.card L = q ^ 2 := by rwa [← Nat.card_eq_fintype_card]
  have hq2 : 2 ≤ q := by
    have h1 : 1 < Fintype.card L := Fintype.one_lt_card
    rw [hL'] at h1
    by_contra h
    interval_cases q <;> simp at h1
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hn
    · exact h
  have ha := one_le_padicValInt_three_pow_orderOf_sub_one (c := -(q : ℤ))
    (by rw [dvd_neg]; exact_mod_cast hq) (by rw [abs_neg, Nat.abs_cast]; exact_mod_cast hq2)
  have hcast : ((-(q : ℤ) : ℤ) : ZMod 3) = -(q : ZMod 3) := by push_cast; rfl
  rw [hcast] at ha
  exact uniqueElemSylow_of_sigmaModel ha hn fun P => sylow_GU (by decide) L hL' hq hn1 P

theorem uniqueElemSylow_statedSU_of_mod_three_eq_one (L : Type) [Field L] [Finite L] {q : ℕ}
    (hL : Nat.card L = q ^ 2) (hq : q % 3 = 1) {n : ℕ} (hn : n = 6 ∨ n = 7) :
    UniqueElemSylow 3 3 (StatedSU n q L) := by
  open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure in
  letI := Fintype.ofFinite L
  obtain ⟨f, hqf, hdata⟩ := exists_unitaryFieldData L (q := q) (by rwa [← Nat.card_eq_fintype_card])
  have hGU := uniqueElemSylow_statedGU_of_div_eq_three L hL (by omega) (n := n)
    (by rw [orderOf_neg_natCast_zmod_three_of_mod_eq_one hq]; omega)
  refine (UniqueElemSylow.subgroup_of_pow_mem
    ((StatedSU n q L).subgroupOf (StatedGU n q L)) (m := q + 1) (by omega) (fun g => ?_)
    hGU).of_mulEquiv (Subgroup.subgroupOfEquivOfLe statedSU_le_statedGU)
  rw [Subgroup.mem_subgroupOf]
  refine mem_statedSU_of_mem_statedGU hdata hqf (pow_mem g.2 _) ?_
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Matrix.det_pow]
  exact det_pow_card_add_one_of_mem_statedGU hdata hqf g.2

theorem uniqueElemSylow_statedProj_statedSU_of_mod_three_eq_one (L : Type) [Field L] [Finite L]
    {q : ℕ} (hL : Nat.card L = q ^ 2) (hq : q % 3 = 1) {n : ℕ} (hn : n = 6 ∨ n = 7) :
    UniqueElemSylow 3 3 (StatedProj (StatedSU n q L)) := by
  letI := Fintype.ofFinite L
  obtain ⟨f, hqf, hdata⟩ := exists_unitaryFieldData L (q := q) (by rwa [← Nat.card_eq_fintype_card])
  refine UniqueElemSylow.statedProj (d := q + 1) (by omega) (fun c hc => ?_)
    (uniqueElemSylow_statedSU_of_mod_three_eq_one L hL hq hn)
  subst hqf
  exact ((CFSG.LinearGroups.scalar_mem_statedSU_iff hdata.prime hL (by omega) c).1 hc).2

end CFSG.GroupTheory.WeirSylow
