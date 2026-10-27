module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DCoord
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaBridgeC2
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSettingC
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaFactsProof
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DAsm
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DCard
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DHyp3

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaD CFSG.Blueprint
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}

theorem hypC_sec3DData : HypC (sec3DData e t) where
  A₁_sq := d_A₁_sq
  hom_wedge_A₁ := d_hom_wedge_A₁

theorem hypB_sec3DData (hA : HypAut (sec3DData e t)) : HypB (sec3DData e t) where
  K₂_le_L := toG_le_L _
  K₂_le_normalizer := d_K₂_le_normalizer
  Λ_le_K₂ := d_Λ_le_K₂
  A₂_irred := d_A₂_irred
  K₂_trans := d_K₂_trans
  A₁_irred := d_A₁_irred
  CH_A₁_mod := hA.CH_A₁_mod
  w₂_mem_K₁ := d_w₂_mem_K₁
  w₂_mem_K₂ := d_w₂_mem_K₂
  A₁_inf_A₄ := d_A₁_inf_A₄
  A₁_inf_A₂ := d_A₁_inf_A₂
  Z₂S_inf := d_Z₂S_inf

theorem t_not_mem_of_center {t : G} (hZ : center L = ⊥) (htL : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) : t ∉ L := by
  intro htL'
  have hz : (⟨t, htL'⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (mem_centralizer_iff.1 htL l l.2)
  rw [hZ, mem_bot] at hz
  have h1 : t = 1 := congrArg Subtype.val hz
  rw [h1, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem hyp_sec3DData [Finite G] (hset : StandardSetting G L) (hZ : center L = ⊥)
    (hQ : LieModel (L ⧸ center L) .PSU 6 2 1) (htL : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hC₂ : HypC₂ (sec3DData e t)) (hA : HypAut (sec3DData e t)) :
    Hyp (sec3DData e t) where
  t_sq := by
    show t * t = 1
    rw [← pow_two, ← ht, pow_orderOf_eq_one]
  t_ne_one := by
    show t ≠ 1
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  L_le_H := fun l hl => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL l hl)
  H_le_normalizer_L := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standard htL ht
  t_not_mem_L := t_not_mem_of_center hZ htL ht
  card_le := by
    obtain ⟨D, hD⟩ := Yamada.exists_setting hset hZ hQ htL ht
    exact card_le_of_setting hD (by rw [Nat.card_congr e.toEquiv, card_T46])
  C₂_pGroup := hC₂.C₂_pGroup
  C₂_le := hC₂.C₂_le
  C₂_normal := hC₂.C₂_normal
  C₂_le_cent := hC₂.C₂_le_cent
  C₂_inf_H := hC₂.C₂_inf_H
  C₂_conj := hC₂.C₂_conj
  C₂_max := hC₂.C₂_max
  A₂_le_L := toG_le_L _
  A₃_le_L := toG_le_L _
  A₄_le_A₂ := d_A₄_le_A₂
  A₄_le_A₃ := d_A₄_le_A₃
  A₂_comm := d_A₂_comm
  A₂_sq := d_A₂_sq
  card_A₂ := d_card_A₂
  A₃_le_cent_A₄ := d_A₃_le_cent_A₄
  card_A₃ := d_card_A₃
  center_A₃ := d_center_A₃
  card_A₄ := d_card_A₄
  NHA₄_le := hA.NHA₄_le
  oTwo_NA₄ := hA.oTwo_NA₄
  oTwo_CA₄ := hA.oTwo_CA₄
  Λ_comm_CA₄ := hA.Λ_comm_CA₄
  center_CA₄ := hA.center_CA₄
  Λ_le_L := toG_le_L _
  Λ_le_normalizer := d_Λ_le_normalizer
  A₄_le_comm := d_A₄_le_comm
  e_mem_L := gw_mem_L _
  e_pow := d_e_pow
  e_cent_A₄ := d_e_cent_A₄
  e_norm_A₃ := d_e_norm_A₃
  A₃_cent_e := d_A₃_cent_e
  A₃_le_comm_e := d_A₃_le_comm_e
  A₃_irred := d_A₃_irred
  NLA₃_le := d_NLA₃_le
  NLA₃_le_gen := d_NLA₃_le_gen
  Λ_le_NA₃ := d_Λ_le_NA₃
  Sig_le_L := toG_le_L _
  Sig_le_NA₃ := d_Sig_le_NA₃
  Sig_le_cent_A₄ := d_Sig_le_cent_A₄
  Λ_comm_Sig := d_Λ_comm_Sig
  X₁_le_Λ := d_X₁_le_Λ
  card_X₁ := card_sX₁
  odd_index_X₁ := d_odd_index_X₁
  u₁_mem := d_u₁_mem
  u₂_mem := d_u₂_mem
  X₁_le_closure := d_X₁_le_closure
  u₁_sq := d_u₁_sq
  u₂_sq := d_u₂_sq
  u₁_comm_u₂ := d_u₁_comm_u₂
  a₀_mem := d_a₀_mem
  A₄_le_closure := d_A₄_le_closure
  norm_a₀ := d_norm_a₀
  A₄_cent_X₁ := d_A₄_cent_X₁
  hom_wedge_A₄ := d_hom_wedge_A₄
  z_mem_A₄ := d_z_mem_A₄
  z_ne_one := d_z_ne_one
  z_cent_X₁ := d_z_cent_X₁
  A₁_le_L := toG_le_L _
  A₁_le := d_A₁_le
  z_mem_A₁ := d_z_mem_A₁
  card_A₁ := d_card_A₁
  center_A₁ := d_center_A₁
  CHz_le := hA.CHz_le
  CH_A₁ := hA.CH_A₁
  oTwo_CHz := hA.oTwo_CHz
  K₁_le_L := toG_le_L _
  K₁_cent_z := d_K₁_cent_z
  K₁_perfect := d_K₁_perfect
  j₀_mem_L := phiG_mem _
  J_eq := rfl
  j₀_pow := d_j₀_pow
  j₀_u₁ := d_j₀_u₁
  j₀_u₂ := d_j₀_u₂
  j₀_norm_A₃ := d_j₀_norm_A₃
  j₀_comm_z := d_j₀_comm_z
  comm_A₄_J := d_comm_A₄_J
  A₄_le_cent_J_sup := d_A₄_le_cent_J_sup
  card_X₈ := d_card_X₈
  X₈_inf_z := d_X₈_inf_z
  X₈_le_A₁ := d_X₈_le_A₁
  comm_X₁_Z₂ := d_comm_X₁_Z₂
  A₄_comm_X₁ := d_A₄_comm_X₁
  x₃_mem_K₁ := d_x₃_mem_K₁
  x₃_mem_Sig := d_x₃_mem_Sig
  A₂_le_x₃ := d_A₂_le_x₃
  A₄_le_orbit_z := d_A₄_le_orbit_z
  A₁_comm := d_A₁_comm
  card_sing := d_card_sing
  K₁_trans := d_K₁_trans
  card_CHz := hA.card_CHz

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
