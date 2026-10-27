module

public import CFSG.GH74.GLS.IVK.Lifted.CentSylow
public import CFSG.GH74.GLS.IVK.Lifted.Out
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Closed

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem ivk_1_4j_lifted_of_II4 (h44 : II4_44) :
    CFSG.GH74.GLS.Stage1.Thm3.Sec7.IVK_1_4j_lifted := by
  intro G _ _ z S K₁ K₂ h K hK hSL s hsS hsN hcomm
  have hKc : K = K₁ ∨ K = K₂ := by simpa using hK
  have hOK := std4_hatOK h44 h hK
  rcases sl_or_a7 hOK.sl2 with ⟨F, _, _, hodd, h3, ⟨e⟩⟩ | h7
  · have hno := noCommInv_of_pRank hOK.rank
    obtain ⟨Pbar, hPbar⟩ := exists_sylow_hatImg (std4_exists_sylow_P h hKc)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 h.sylow.isPGroup) ⟨s, hsS⟩
    have hsm : orderOf s = 2 ^ m := by rw [← Subgroup.orderOf_mk s hsS]; exact hm
    have hφ : orderOf (phi K s hsN) ∣ 2 ^ m := by
      have h1 : orderOf (phiHom K ⟨s, hsN⟩) ∣ orderOf (⟨s, hsN⟩ : ↥(normalizer (K : Set G))) :=
        orderOf_map_dvd (phiHom K) _
      rw [Subgroup.orderOf_mk s hsN, hsm] at h1
      exact h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hφ
    have hfix : ∀ p ∈ (Pbar : Subgroup (Hat K)), phi K s hsN p = p := by
      intro p hp
      rw [hPbar] at hp
      exact phi_fixes_hatImg hsN hcomm hp
    have h1 := sl2_no_central_sylow hodd h3 e hOK.quasi hno (phi K s hsN) hk Pbar hfix
    exact (phi_eq_one_iff K hsN).1 h1
  · exfalso
    obtain ⟨F, _, _, -, ⟨e0⟩⟩ := hSL
    exact not_sl2_of_double_cover_alt7 h7 e0

end CFSG.GH74.GLS.IVK.Lifted
