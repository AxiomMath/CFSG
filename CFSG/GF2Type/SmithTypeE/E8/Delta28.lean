module

public import CFSG.LargeExtraspecial.S14SMKDelta32

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S14.SMK (card_L0_ge z_not_mem_Qa card_clSub_Dl
  finrank_clSub_Dl_le_one sq_eq_one_of_mem_L0 isElementaryAbelian_Lbar_of_sq
  isElementaryAbelian_Lbar_of_Dl_eq_bot isConj_of_mem_Dl_of_le card_centralizer_eq
  finrank_fixQt_le mem_centralizer_of_mem_Qa)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem QG_inf_Qa_ne_bot
    (hrank : ∀ E : Subgroup S.O, E ≤ S.Mbar → CFSG.IsElementaryAbelian 2 E → Nat.card E ≤ 2 ^ 27)
    (hw : S.width = 28) {g : G}
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hno : ¬ ∃ y ∈ S.QG, y * (g * S.z * g⁻¹) * y⁻¹ = g * S.z * g⁻¹ * S.z) :
    S.QG ⊓ S.Qa g ≠ ⊥ := by
  intro hbot
  have hfix : S.fixQt (g * S.z * g⁻¹) =
      S.clSub (S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G)) := by
    by_contra h
    exact hno (S.lemma_3_2_1 hxM h)
  have := isElementaryAbelian_Lbar_of_Dl_eq_bot S hxM hbot hfix
  have h1 := hrank (S.Lbar g) (S.Lbar_le_Mbar g) this
  have h2 := S.card_Lbar_mul g
  rw [hbot, card_bot, mul_one] at h2
  have h3 := card_L0_ge S hxM hxQ
  rw [hw, ← h2] at h3
  have : (2 : ℕ) ^ 28 ≤ 2 ^ 27 := h3.trans h1
  norm_num at this

theorem exists_isConj_mem_Dl
    (hrank : ∀ E : Subgroup S.O, E ≤ S.Mbar → CFSG.IsElementaryAbelian 2 E → Nat.card E ≤ 2 ^ 27)
    (hw : S.width = 28) {g : G}
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hl5 : 5 ≤ finrank (ZMod 2) (S.commQt (g * S.z * g⁻¹)))
    (hxz : IsConj S.z (g * S.z * g⁻¹ * S.z)) :
    ∃ v, IsConj S.z v ∧ v ∈ S.QG ⊓ S.Qa g := by
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hxc : IsConj S.z (g * S.z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have hzx : S.z * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * S.z := (S.z_comm hxM).symm
  by_cases hJ : ∃ y ∈ S.QG ⊓ S.Qa g, y ∈ S.clPre (S.commQt (g * S.z * g⁻¹)) ∧ y ≠ 1
  · obtain ⟨y, hyD, hyJ, hy1⟩ := hJ
    have hyJ' : y ∈ (⁅zpowers (g * S.z * g⁻¹), S.QG⁆ : Subgroup G) := by
      rw [S.commutator_zpowers_eq_clPre hxM hxQ hx2]
      exact hyJ
    have hyx : Commute (g * S.z * g⁻¹) y :=
      (mem_centralizer_singleton_iff.mp (mem_centralizer_of_mem_Qa S hyD.2)).symm
    rcases SMF.isConj_of_mem_J S hxM hxQ hy1 hyJ' hyx hyD.2 with h | h
    · exact ⟨y, h, hyD⟩
    · exact ⟨y, hxz.trans h, hyD⟩
  · have hJ' : ∀ d ∈ S.QG ⊓ S.Qa g, d ∈ S.clPre (S.commQt (g * S.z * g⁻¹)) → d = 1 := by
      intro d hd hdJ
      by_contra h
      exact hJ ⟨d, hd, hdJ, h⟩
    have hD1 := finrank_clSub_Dl_le_one S hxM hxQ hJ'
    have hsq : ∀ k ∈ S.L0 g, k ^ 2 = 1 := fun k hk => sq_eq_one_of_mem_L0 S hxM hxQ hl5 hD1 hk
    have := isElementaryAbelian_Lbar_of_sq S hsq
    have h1 := hrank (S.Lbar g) (S.Lbar_le_Mbar g) this
    have h2 := S.card_Lbar_mul g
    have h3 := card_L0_ge S hxM hxQ
    rw [hw] at h3
    have h4 : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤ 2 := by
      rw [← card_clSub_Dl S hxQ, S.card_submodule]
      calc 2 ^ finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) ≤ 2 ^ 1 :=
            Nat.pow_le_pow_right (by norm_num) hD1
        _ = 2 := by norm_num
    have h5 : Nat.card (S.L0 g) = 2 ^ 28 := by
      have h6 : Nat.card (S.Lbar g) * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤ 2 ^ 27 * 2 :=
        Nat.mul_le_mul h1 h4
      have : (2 : ℕ) ^ 27 * 2 = 2 ^ 28 := by norm_num
      omega
    have hDne : 1 < Nat.card (S.QG ⊓ S.Qa g : Subgroup G) := by
      have h7 : Nat.card (S.Lbar g) * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤
          2 ^ 27 * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) := Nat.mul_le_mul_right _ h1
      have h6 : 2 ^ 28 ≤ 2 ^ 27 * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) := by
        rw [← h5, ← h2]
        exact h7
      by_contra h
      push Not at h
      have : 2 ^ 27 * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤ 2 ^ 27 * 1 :=
        Nat.mul_le_mul_left _ h
      omega
    have := Finite.one_lt_card_iff_nontrivial.mp hDne
    obtain ⟨⟨d, hd⟩, hd1⟩ := exists_ne (1 : (S.QG ⊓ S.Qa g : Subgroup G))
    have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
    set T := S.conjBy g with hT
    have hzM : S.z ∈ T.M := mem_centralizer_singleton_iff.mpr (S.z_comm hxM).symm
    have hzQ : S.z ∉ T.QG := z_not_mem_Qa S hxQ
    have hTw : T.width = 28 := by rw [S.width_conjBy g, hw]
    have hC : Nat.card (T.QG ⊓ centralizer ({S.z} : Set G) : Subgroup G) = 2 ^ 28 := h5
    have hc9 : finrank (ZMod 2) (T.clSub (T.QG ⊓ centralizer ({S.z} : Set G))) = 27 := by
      have := card_centralizer_eq T S.z hzM
      rw [hC] at this
      have e2 : (2 : ℕ) ^ 28 = 2 * 2 ^ 27 := by norm_num
      rw [e2] at this
      exact Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left (by norm_num) this).symm
    have hf := finrank_fixQt_le T hzM hzQ S.z_sq
    have hd5 := finrank_commSpace_add_finrank_fixSpace (T.ρ ⟨S.z, hzM⟩ : T.Qt ≃ₗ[ZMod 2] T.Qt)
    rw [← T.fixQt_of_mem hzM, ← T.commQt_of_mem hzM, T.finrank_Qt_eq_two_mul_width, hTw] at hd5
    have hcf := Submodule.finrank_mono (T.commQt_le_fixQt hzM S.z_sq)
    have heq : T.commQt S.z = T.fixQt S.z :=
      Submodule.eq_of_le_of_finrank_eq (T.commQt_le_fixQt hzM S.z_sq) (by omega)
    have hle : S.L0 g ≤ ⁅zpowers S.z, T.QG⁆ := by
      rw [T.commutator_zpowers_eq_clPre hzM hzQ S.z_sq, heq]
      calc S.L0 g = T.QG ⊓ centralizer ({S.z} : Set G) := rfl
        _ ≤ T.clPre (T.clSub (T.QG ⊓ centralizer ({S.z} : Set G))) := T.le_clPre_clSub inf_le_left
        _ ≤ T.clPre (T.fixQt S.z) := T.clPre_mono (T.clSub_centralizer_le_fixQt hzM)
    refine ⟨d, ?_, hd⟩
    rcases isConj_of_mem_Dl_of_le hxM hxQ hle hd hd1' with h | h
    · exact hxc.trans h
    · rw [hzx] at h
      exact hxz.trans h

end CFSG.GF2Type.SmithTypeE.E8
