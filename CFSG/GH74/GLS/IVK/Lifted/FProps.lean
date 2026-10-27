module

public import CFSG.GH74.GLS.IVK.Lifted.Dict
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage1.Thm2.Recip (II4_44 II4_Aut IsSL2Or2A7 innOf)

section Std4Glue

open CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem phi_one_aux (K : Subgroup G) (hh : (1 : G) ∈ normalizer (K : Set G)) : phi K (1 : G) hh = 1 := by
  have h1K : hatMk K (⟨1, one_mem K⟩ : ↥K) = 1 := by
    have : (⟨1, one_mem K⟩ : ↥K) = 1 := rfl
    rw [this, map_one]
  rw [show phi K (1 : G) hh = phi K (1 : G) (le_normalizer (one_mem K)) from rfl,
    phi_of_mem K (one_mem K), h1K, map_one]

omit [Finite G] in
theorem phi_inv_aux (K : Subgroup G) {t : G} (ht : t ∈ normalizer (K : Set G))
    (hti : t⁻¹ ∈ normalizer (K : Set G)) : phi K t⁻¹ hti = (phi K t ht)⁻¹ := by
  have h3 : phi K t ht * phi K t⁻¹ hti = 1 := by
    rw [← phi_mul K ht hti]
    have : phi K (t * t⁻¹) (mul_mem ht hti) = phi K 1 (one_mem _) := phi_congr K (by group) _ _
    rw [this]
    exact phi_one_aux K _
  exact eq_inv_of_mul_eq_one_right h3

theorem std4_comp_rigid {z : G} {S K₁ K₂ : Subgroup G} (h : Std4 G z S K₁ K₂) {K : Subgroup G}
    (hK : K ∈ ({K₁, K₂} : Set (Subgroup G))) : IsRigidRankOneComp z K := by
  have : K ∈ {K' | IsRigidRankOneComp z K'} := by rw [h.comps]; exact hK
  exact this

theorem std4_hatOK (h44 : II4_44) {z : G} {S K₁ K₂ : Subgroup G} (h : Std4 G z S K₁ K₂)
    {K : Subgroup G} (hK : K ∈ ({K₁, K₂} : Set (Subgroup G))) : HatOK (Hat K) := by
  have hr := std4_comp_rigid h hK
  have hz : orderOf z = 2 := h.classical.1
  have hKc : IsPCompIn 2 (centralizer ({z} : Set G)) K := hr.1.1.2.2
  exact ⟨TwoThin.isQuasisimple_hat hKc, isKGroupNative_hat h.simple hz hKc.1,
    (pRank_hat K).trans hr.2, h44 G h.simple z hz K hKc hr.2⟩

theorem ivk_f_inner_of_II4 (h44 : II4_44) (h2A7 : II4_2A7) : IVK_f_inner := by
  intro G _ _ z S K₁ K₂ h K hK b hb hbin
  obtain ⟨hbN, hF⟩ := hb
  have hOK := std4_hatOK h44 h hK
  have hinn : phi K b hbN ∈ innOf (Hat K) := (phi_mem_inn_iff K hbN).2 (mem_innSub_iff.1 hbin)
  obtain ⟨c, hc⟩ := hinn
  have hcz : c ∈ Subgroup.center (Hat K) := dict_inner h2A7 hOK.sl2 c (by rw [hc]; exact hF)
  have h1 : phi K b hbN = 1 := by rw [← hc]; exact conj_eq_one_of_mem_center hcz
  exact (phi_eq_one_iff K hbN).1 h1

theorem ivk_f_sq_of_II4 (h44 : II4_44) (h2A7 : II4_2A7) : IVK_f_sq := by
  intro G _ _ z S K₁ K₂ h K hK b hb hbb
  obtain ⟨hbN, hF⟩ := hb
  have hOK := std4_hatOK h44 h hK
  have hbbN : b * b ∈ normalizer (K : Set G) := mul_mem hbN hbN
  have hphi : phi K (b * b) hbbN = phi K b hbN * phi K b hbN := phi_mul K hbN hbN
  have hin : phi K b hbN * phi K b hbN ∈ innOf (Hat K) := by
    rw [← hphi]
    exact (phi_mem_inn_iff K hbbN).2 (mem_innSub_iff.1 hbb)
  have h1 := dict_sq h2A7 hOK.sl2 _ hF hin
  rw [← hphi] at h1
  exact (phi_eq_one_iff K hbbN).1 h1

theorem ivk_f_coset_of_II4 (h44 : II4_44) (h2A7 : II4_2A7) : IVK_f_coset := by
  intro G _ _ z S K₁ K₂ h K hK s t hsN htN hss htt htcs hst hft
  obtain ⟨htN', hF⟩ := hft
  have hOK := std4_hatOK h44 h hK
  have hφ1 : phi K t htN ≠ 1 := fun h1 => htcs ((phi_eq_one_iff K htN).1 h1)
  have hφ2 : phi K t htN * phi K t htN = 1 := by
    rw [← phi_mul K htN htN]
    exact (phi_eq_one_iff K (mul_mem htN htN)).2 htt
  have hψ2 : phi K s hsN * phi K s hsN = 1 := by
    rw [← phi_mul K hsN hsN]
    exact (phi_eq_one_iff K (mul_mem hsN hsN)).2 hss
  have htiN : t⁻¹ ∈ normalizer (K : Set G) := inv_mem htN
  have hstN : s * t⁻¹ ∈ normalizer (K : Set G) := mul_mem hsN htiN
  have hin : phi K s hsN * (phi K t htN)⁻¹ ∈ innOf (Hat K) := by
    have := (phi_mem_inn_iff K hstN).2 (mem_innSub_iff.1 hst)
    rwa [phi_mul K hsN htiN, phi_inv_aux K htN htiN] at this
  exact ⟨hsN, dict_coset h2A7 hOK _ _ hF hφ1 hφ2 hψ2 hin⟩

end Std4Glue

end CFSG.GH74.GLS.IVK.Lifted
