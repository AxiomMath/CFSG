module

public import CFSG.LargeExtraspecial.S14C13Cent
public import CFSG.LargeExtraspecial.S14C13Simple
public import CFSG.LargeExtraspecial.S14C10Schur
public import CFSG.LargeExtraspecial.S8FusA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Rbar_le_Ct (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} : Rbar S g t ≤ Ct S t := fun _ hr =>
  Subgroup.mem_inf.mpr ⟨Rbar_le_Mbar hr, Rbar_le_centralizer haQ hr⟩

theorem eq_one_or_eq_of_centralizes_Nbar {t : S.O} (hSt : Stage S g t)
    (hext : IsExtraspecialPGroup 2 (Nbar S g t)) {y : S.O} (hy : y ∈ Nbar S g t)
    (hyc : ∀ n ∈ Nbar S g t, y * n = n * y) : y = 1 ∨ y = t := by
  have haQ := hSt.hyp4.conj_mem
  have htN := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have hc : (⟨y, hy⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (hyc v v.2).symm
  exact S8.eq_one_or_eq_of_mem_zpowers (mul_self_of_mem_Lbar S haQ hSt.mem)
    (mem_zpowers_of_mem_center_Nbar hext htN hSt.ne_one
      (fun n hn => (commute_of_mem_Rbar haQ (Nbar_le_Rbar hn)).symm) hc)

theorem partA_simple (hCE : CentralExtInput.{0}) [IsSimpleGroup G] {t : S.O} {c : Config}
    (hSt : Stage S g t) (hocc : c.Occurs S g t) (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (hc : c = .sp6 ∨ c = .omegaPlus8a ∨ c = .omegaPlus12) (h6 : IsSimpleGroup (Mbar0 S))
    (h7 : Concl14_7 S g t) (h8 : Rbar S g t ≤ (Mbar0 S).map S.Mbar.subtype)
    (hF : FCt S t = Nbar S g t) :
    Ct S t = Rbar S g t ∧ IsSimpleGroup S.Mbar := by
  have haQ := hSt.hyp4.conj_mem
  have hCt := le_antisymm (Ct_le_Rbar hCE hSt hocc hext hc h7) (Rbar_le_Ct haQ)
  refine ⟨hCt, ?_⟩
  have htN := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have : (Mbar0 S).Normal := timmesfeldFStar_normal S.Mbar
  have htop : Mbar0 S = ⊤ := eq_top_of_centralizer_le (Rbar_le_Mbar (Nbar_le_Rbar htN)) hF
    hext.1 htN hSt.ne_one (fun y hy hyc => eq_one_or_eq_of_centralizes_Nbar hSt hext hy hyc)
    (by rw [show (S.Mbar ⊓ centralizer ({t} : Set S.O)) = Ct S t from rfl, hCt]; exact h8)
  exact (MulEquiv.isSimpleGroup_congr ((MulEquiv.subgroupCongr htop).trans
    Subgroup.topEquiv)).mp h6

end CFSG.LargeExtraspecial.S14
