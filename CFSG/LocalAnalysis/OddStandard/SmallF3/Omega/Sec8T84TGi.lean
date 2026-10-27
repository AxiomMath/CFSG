module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TGiInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TGiCov
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TI4mCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84FactGamInner_holds : Sec8T84FactGamInner := by
  intro G _ _ L hL s hss hind l hl hcomm
  obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx2, hx⟩ := hind
  obtain ⟨ρc, hρc, hρφ⟩ := ff6m_exists_centCover hQ (by omega) e (ff6m_odd_center hL) hs hss
  obtain ⟨E, hEn, hLie, hP⟩ := ff6m_K4_layerModel hQ hdim hsgn hx2 hx
  obtain ⟨ρ, rfl, hρ, hρρ⟩ := ff6m_K4_split hQ hdim hsgn hx2 hx
  haveI : E.Normal := hEn
  obtain ⟨hEs, hEnc⟩ := ff_simple_of_lieModel_psl2 hLie
  have hcent : ∀ c, (∀ e ∈ E, c * e = e * c) → c = 1 := fun c hc =>
    sec8t84t_centB_eq_one hQ hdim hsgn E hEs hEnc hP hc
  have hinv : ∀ b, b * b = 1 → b ∈ E := fun b hb =>
    sec8t84t_gi_involution_mem hQ hdim hsgn hρ hρρ E hP hb
  let l' : ↥(L ⊓ centralizer ({s} : Set G)) := ⟨l, hl⟩
  have hlcomm : ∀ y ∈ CFSG.layer ↥(L ⊓ centralizer ({s} : Set G)),
      l' * l' * y = y * (l' * l') := by
    intro y hy
    have hyK : ((y : ↥(L ⊓ centralizer ({s} : Set G))) : G) ∈ layerCent L s :=
      Subgroup.mem_map_of_mem (L ⊓ centralizer ({s} : Set G)).subtype hy
    exact Subtype.ext (hcomm _ hyK)
  obtain ⟨y, hy, hk⟩ := sec8t84t_gi_of_cover hρc E hEs hEnc hcent hinv hlcomm
  have hyK : ((y : ↥(L ⊓ centralizer ({s} : Set G))) : G) ∈ layerCent L s :=
    Subgroup.mem_map_of_mem (L ⊓ centralizer ({s} : Set G)).subtype hy
  have hkodd : ((l' * y⁻¹ : ↥(L ⊓ centralizer ({s} : Set G))) : G) ∈ oddCoreIn L := by
    have hkL : ((l' * y⁻¹ : ↥(L ⊓ centralizer ({s} : Set G))) : G) ∈ L :=
      (Subgroup.mem_inf.mp (l' * y⁻¹).2).1
    let kL : ↥L := ⟨((l' * y⁻¹ : ↥(L ⊓ centralizer ({s} : Set G))) : G), hkL⟩
    have hkφ : ff6mPhi e kL = 1 := by
      have h := hρφ (l' * y⁻¹)
      rw [MonoidHom.mem_ker.mp hk] at h
      exact h.symm.trans rfl
    have hkZ : kL ∈ Subgroup.center ↥L := by
      rw [← ff6mPhi_ker e]
      exact hkφ
    have hkO : kL ∈ CFSG.oddCore ↥L := by
      rw [← ff_center_eq_oddCore_six_minus hL]
      exact hkZ
    exact ⟨kL, hkO, rfl⟩
  have hl_eq : l = ((l' * y⁻¹ : ↥(L ⊓ centralizer ({s} : Set G))) : G) *
      ((y : ↥(L ⊓ centralizer ({s} : Set G))) : G) := by
    simp [l']
  rw [hl_eq]
  exact mul_mem (Subgroup.mem_sup_right hkodd) (Subgroup.mem_sup_left hyK)

end CFSG.OddStandard.SmallF3.Omega
