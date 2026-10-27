module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGPocketCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MField2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkOmega
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem fg_pocket_M : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ z : G, z ∈ L → (IsI4PlusIn L z ↔ orderOf z = 2 ∧ InducesTypeSome L z 6 (-1) 4 1) := by
  intro G _ _ L hL z hz
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hs⟩ := ff6m_exists_model hL
  have hcov := ff6m_phi_cover e (ff6m_odd_center hL)
  have hN : z ∈ normalizer (L : Set G) := Subgroup.le_normalizer hz
  constructor
  · intro hI
    have hz2 := hI.1
    refine ⟨hz2, ?_⟩
    have hnc : z ∉ centralizer (L : Set G) := by
      intro hzc
      have hker : (⟨z, hz⟩ : ↥L) ∈ (ff6mPhi e).ker := by
        rw [ff6mPhi_ker]
        exact Subgroup.mem_center_iff.mpr fun g =>
          Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc g g.2)
      have hzz : z * z = 1 := by
        rw [← pow_two]
        exact hz2 ▸ pow_orderOf_eq_one z
      have h1 := hcov.eq_one_of_mul_self_eq_one hker (Subtype.ext hzz)
      rw [Subtype.ext_iff] at h1
      exact absurd (hz2 ▸ (congrArg orderOf h1).trans orderOf_one) (by decide)
    exact (ff6m_inner_iff G L hL z hz2 hN).mp ⟨Subgroup.mem_sup_left hz, hnc⟩
  · rintro ⟨hz2, -⟩
    obtain ⟨q, hq⟩ := exists_isI4PlusIn_omegaProj hQ (by omega : 5 ≤ Module.finrank (ZMod 3) V)
    have hqq : q * q = 1 := by
      rw [← pow_two]
      exact hq.1 ▸ pow_orderOf_eq_one q
    obtain ⟨a, haa, haq⟩ := hcov.exists_mul_self_eq_one_lift hqq
    have ha1 : (a : G) ≠ 1 := by
      intro h
      have : a = 1 := Subtype.ext h
      rw [this, map_one] at haq
      have := hq.1
      rw [← haq, orderOf_one] at this
      omega
    have ha2 : orderOf (a : G) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact congrArg Subtype.val haa) ha1
    have hpa : IsI4PlusIn L (a : G) :=
      (fg_isI4PlusIn_iff_of_cover hcov a.2 ha2).mpr (by rw [haq]; exact hq)
    obtain ⟨l, hl, hzl⟩ := ff6m_inv_one_class G L hL (a : G) z a.2 hz ha2 hz2
    rw [hzl]
    exact IsI4PlusIn.conj_of_mem hpa hl

end CFSG.OddStandard.SmallF3.Omega
