module

public import CFSG.GF2Type.Aschbacher1976Full.WidthCore
public import CFSG.GF2Type.Aschbacher1976Full.WidthCbit

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.Embed

open CFSG
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {z : G} {Z A : Subgroup G}

theorem cdata_Fz {w : ℕ} (hD : Width.Z4Data z w Z A) (hz : orderOf z = 2) :
    Width.CData z (Fz z) where
  zF := hD.sup_eq ▸ Subgroup.mem_sup_left hD.mem_z
  zc := fun f hf => Width.Z_comm_F hD hD.mem_z hf
  z2 := Width.z_sq hz
  z1 := fun h => by simp [h] at hz
  comm := fun f hf g hg => Width.comm_F hD hz hf hg
  sq := fun f hf => Width.sq_F hD hz hf

theorem map_center_Fz {w : ℕ} (hD : Width.Z4Data z w Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 ↥(Fz z)) : (Subgroup.center ↥(Fz z)).map (Fz z).subtype = Z := by
  have key : ∀ S : Subgroup G, S = Fz z → (Subgroup.center ↥S).map S.subtype =
      (Subgroup.center ↥(Fz z)).map (Fz z).subtype := fun S h => by subst h; rfl
  rw [← key _ (Width.coreAt_eq_Fz hF2)]
  exact Subgroup.ext fun x => Width.mem_centerAt_iff hD hz hF2

theorem isCyclic_center_Fz {w : ℕ} (hD : Width.Z4Data z w Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 ↥(Fz z)) : IsCyclic ↥(Subgroup.center ↥(Fz z)) := by
  have hcyc : IsCyclic ↥((Subgroup.center ↥(Fz z)).map (Fz z).subtype) := by
    rw [map_center_Fz hD hz hF2]
    exact hD.cyc
  exact isCyclic_of_injective
    (Subgroup.equivMapOfInjective _ (Fz z).subtype (Fz z).subtype_injective).toMonoidHom
    (Subgroup.equivMapOfInjective _ (Fz z).subtype (Fz z).subtype_injective).injective

theorem card_center_Fz {w : ℕ} (hD : Width.Z4Data z w Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 ↥(Fz z)) : Nat.card ↥(Subgroup.center ↥(Fz z)) = 4 := by
  rw [← Subgroup.card_map_of_injective (Fz z).subtype_injective, map_center_Fz hD hz hF2,
    hD.card_Z]

theorem z_mem_map_center_Fz {w : ℕ} (hD : Width.Z4Data z w Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 ↥(Fz z)) : z ∈ (Subgroup.center ↥(Fz z)).map (Fz z).subtype := by
  rw [map_center_Fz hD hz hF2]
  exact hD.mem_z

theorem exists_noncomm_of_extraspecial {B : Subgroup G} (hB : IsExtraspecialPGroup 2 B)
    (h : 2 < Nat.card B) : ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have htop : Subgroup.center ↥B = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro g
    rw [Subgroup.mem_center_iff]
    intro h'
    apply Subtype.ext
    exact (hcon g.1 g.2 h'.1 h'.2).symm
  have h2 := hB.2.2.2
  rw [htop, Subgroup.card_top] at h2
  omega

theorem commutator_Fz (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) :
    ⁅Fz z, Fz z⁆ = Subgroup.zpowers z := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rcases Width.comm_F hD hz hx hy with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers z
  · have hzmem : z ∈ ⁅Fz z, Fz z⁆ := by
      obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_extraspecial hD.ext_A
        (by rw [hD.card_A]; norm_num)
      have h1 : ⁅a, b⁆ ∈ Subgroup.zpowers z := Width.comm_mem_zpowers_A hD hz ha hb
      have h2 : ⁅a, b⁆ ≠ 1 := fun h => hab (commutatorElement_eq_one_iff_mul_comm.mp h)
      have h3 : ⁅a, b⁆ = z := (Width.mem_zpowers_involution hz h1).resolve_left h2
      have haF : a ∈ Fz z := by rw [← hD.sup_eq]; exact Subgroup.mem_sup_right ha
      have hbF : b ∈ Fz z := by rw [← hD.sup_eq]; exact Subgroup.mem_sup_right hb
      have hmem := Subgroup.commutator_mem_commutator haF hbF
      rw [h3] at hmem
      exact hmem
    exact Subgroup.zpowers_le.mpr hzmem

theorem card_Fz (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) :
    Nat.card ↥(Fz z) = 64 :=
  (Width.card_Fz hD hz).trans (by norm_num)

theorem Fz_eq_inSubgroup_pCore (hF2 : IsPGroup 2 ↥(Fz z)) :
    Fz z = inSubgroup (pCore 2) (Hz z) :=
  (Width.coreAt_eq_Fz hF2).symm

theorem isCharacteristicP_Hz (hF2 : IsPGroup 2 ↥(Fz z)) : IsCharacteristicP 2 ↥(Hz z) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mpr (Width.pCore_eq_gf hF2).symm

noncomputable def pCoreEquiv (hF2 : IsPGroup 2 ↥(Fz z)) :
    ↥(pCore 2 ↥(Hz z)) ≃* ↥(Fz z) :=
  (Subgroup.equivMapOfInjective (pCore 2 ↥(Hz z)) (Hz z).subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (Fz_eq_inSubgroup_pCore hF2).symm)

theorem card_pCore_Hz (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 ↥(Fz z)) : Nat.card ↥(pCore 2 ↥(Hz z)) = 64 := by
  rw [Nat.card_congr (pCoreEquiv hF2).toEquiv]
  exact card_Fz hD hz

theorem card_center_pCore (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 ↥(Fz z)) : Nat.card ↥(Subgroup.center ↥(pCore 2 ↥(Hz z))) = 4 := by
  have h1 : Subgroup.map (pCoreEquiv hF2) (Subgroup.center ↥(pCore 2 ↥(Hz z))) =
      Subgroup.center ↥(Fz z) := Subgroup.map_center_eq (pCoreEquiv hF2)
  rw [← card_center_Fz hD hz hF2, ← h1]
  exact (Subgroup.card_map_of_injective (f := (pCoreEquiv hF2).toMonoidHom)
    (pCoreEquiv hF2).injective).symm

theorem card_quot_pCore (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 ↥(Fz z)) :
    Nat.card (↥(pCore 2 ↥(Hz z)) ⧸ Subgroup.center ↥(pCore 2 ↥(Hz z))) = 16 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center ↥(pCore 2 ↥(Hz z)))
  rw [card_center_pCore hD hz hF2, card_pCore_Hz hD hz hF2] at h
  omega

theorem finrank_quot_pCore
    [IsElementaryAbelian 2 (↥(pCore 2 ↥(Hz z)) ⧸ Subgroup.center ↥(pCore 2 ↥(Hz z)))]
    (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 ↥(Fz z)) :
    Module.finrank (ZMod 2)
      (Additive (↥(pCore 2 ↥(Hz z)) ⧸ Subgroup.center ↥(pCore 2 ↥(Hz z)))) = 4 := by
  have hcard : Nat.card
      (Additive (↥(pCore 2 ↥(Hz z)) ⧸ Subgroup.center ↥(pCore 2 ↥(Hz z)))) = 16 :=
    (Nat.card_congr Additive.ofMul).symm.trans (card_quot_pCore hD hz hF2)
  haveI : Fintype (Additive (↥(pCore 2 ↥(Hz z)) ⧸ Subgroup.center ↥(pCore 2 ↥(Hz z)))) :=
    Fintype.ofFinite _
  have h := Module.card_eq_pow_finrank (K := ZMod 2)
    (V := Additive (↥(pCore 2 ↥(Hz z)) ⧸ Subgroup.center ↥(pCore 2 ↥(Hz z))))
  rw [← Nat.card_eq_fintype_card, hcard, ZMod.card] at h
  exact Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num))

end CFSG.GF2Type.Aschbacher1976Full.HS.Embed
