module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3T326L
public import CFSG.Quasithin.Vol2.Ch3T326N
public import CFSG.Quasithin.Vol2.Ch3T326PN
public import CFSG.Quasithin.Vol2.Ch3T326G
public import CFSG.Quasithin.Vol2.Ch3T326PM

public section
namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative
open T325 (V_le_VM)

namespace Ctx

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem case_d321_F4 (h316 : Theorem316Statement) (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) (hG : T326ActsGlued_F4) (hD321 : D321Spelled)
    (hO2 : D321O2) [IsMulCommutative ↥(conjClosure V₀ T)]
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hlt : conjClosure V₀ T ≠
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :
    Concl326C3 T L V₀ := by
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVM
  obtain ⟨s, hs, hsn⟩ := c.exists_t
  have htS : conjAct VM ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩ ∈ autOn T VM :=
    Setup.mem_autOn_iff.2 ⟨⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩, T.inv_mem hs, rfl⟩
  have htn := c.not_mem_normalizer hA37 hs hsn
  have hMp := c.autOn_L₀_eq hA37 hA38 hs hsn
  obtain ⟨_, hq⟩ := qhat_VM h316 c
  have hq' : qhatOf (autOn (Subgroup.normalizer (conjClosure L T : Set G)) VM) ≤
      ((2 : ℚ) : WithTop ℚ) := by exact_mod_cast hq
  have htop : orbSup (autOn T VM) (V₀.subgroupOf VM) ≠ ⊤ := by
    rw [c.orbSup_eq]
    intro h
    exact hlt (le_antisymm (V_le_VM T (conjClosure L T) V₀) (Subgroup.subgroupOf_eq_top.mp h))
  have hD := c.d3Std h316
  rcases hD321 ↥VM _ _ _ _ _ hD _ htS htn hMp hq' with hVT | ⟨-, hfix, h23⟩
  · exact (htop hVT).elim
  have ha := c.concl_a hA37 hA38 hs hsn (c.le_centralizer_of_fixV hs hfix)
  obtain ⟨h1, h2, h3⟩ := ha s hs hsn
  obtain ⟨hc, hrk⟩ : Concl326Cc T L V₀ ∧ 2 < rk ↥((⁅VM, L⁆).subgroupOf VM) := by
    rcases h23 with h2' | h3'
    · obtain ⟨hiii, hrk⟩ := c.case_iii_of_d321Two h2' (hO2 ↥VM _ _ _ _ _ hD _ htS htn hMp hq' htop)
      exact ⟨Or.inr (Or.inr (Or.inl hiii)), hrk⟩
    · obtain ⟨hiv, hrk⟩ := c.case_iv_of_d321Three h3'
      exact ⟨Or.inr (Or.inr (Or.inr hiv)), hrk⟩
  have hacts := c.qhatStar_acts_F4 hA37 hA38 hG hs hsn h1 h2 h3 hrk
  exact ⟨⟨ha, hacts, c.qhat_U h316 hA37 hA38 hacts⟩, hc⟩

end Ctx

end CFSG.Quasithin.H13.T326
