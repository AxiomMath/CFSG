module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIISl2
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC4

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

section Twin

variable {G : Type} [Group G] {F : Type*} [Field F] [Finite F] (hodd : Odd (Nat.card F))
include hodd

theorem equiv_sl2_apply_eq_neg_one {K : Subgroup G} {z : G} (e : K ≃* SL(2, F))
    (hz : IsUniqueInvolution K z) : e ⟨z, hz.mem⟩ = -1 := by
  have h2 : orderOf (⟨z, hz.mem⟩ : K) = 2 := by
    have : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
    rw [Subgroup.orderOf_mk]
    exact this
  have := (orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp h2
  rw [this]
  simp

variable {K K' : Subgroup G} {z : G}

theorem eq_one_or_eq_of_central (e : K ≃* SL(2, F)) (hz : IsUniqueInvolution K z) {c : G}
    (hc : c ∈ K) (hcc : ∀ y ∈ K, c * y = y * c) : c = 1 ∨ c = z := by
  have hcen : (⟨c, hc⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcc y y.2).symm
  have h1 := (mem_center_iff_of_equiv_sl2 e _).mp hcen
  rcases (mem_center_sl2_iff _).mp h1 with h | h
  · left
    have : (⟨c, hc⟩ : K) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  · right
    have h2 : e ⟨c, hc⟩ = e ⟨z, hz.mem⟩ := by rw [h, equiv_sl2_apply_eq_neg_one hodd e hz]
    exact congrArg Subtype.val (e.injective h2)

theorem exists_sq_eq_z_of_involution (e : K ≃* SL(2, F)) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hcomm : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k) {s : G}
    (hs : s ∈ K ⊔ K') (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsz : s ≠ z) :
    ∃ k ∈ K, ∃ k' ∈ K', s = k * k' ∧ k * k = z ∧ k' * k' = z := by
  have hN : K' ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_commutes fun x hx y hy => (hcomm y hy x hx).symm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K K' hN] at hs
  obtain ⟨k, hk, k', hk', hsk⟩ := hs
  have hsk' : s = k * k' := hsk.symm
  subst hsk'
  have hkk' : k * k' = k' * k := hcomm k hk k' hk'
  have hsq : (k * k) * (k' * k') = 1 := by
    calc (k * k) * (k' * k') = k * (k * k') * k' := by group
      _ = k * (k' * k) * k' := by rw [hkk']
      _ = (k * k') * (k * k') := by group
      _ = 1 := hs2
  have hc : k * k = (k' * k')⁻¹ := eq_inv_of_mul_eq_one_left hsq
  have hcK : k * k ∈ K := K.mul_mem hk hk
  have hcK' : k * k ∈ K' := by rw [hc]; exact K'.inv_mem (K'.mul_mem hk' hk')
  have hcen : ∀ y ∈ K, (k * k) * y = y * (k * k) := fun y hy => hcomm y hy _ hcK' |>.symm
  rcases eq_one_or_eq_of_central hodd e hz hcK hcen with h | h
  · exfalso
    have hk1 : k * k = 1 := h
    have hk'1 : k' * k' = 1 := by
      rw [hk1, one_mul] at hsq
      exact hsq
    have hkz := hz.unique k hk hk1
    have hk'z := hz'.unique k' hk' hk'1
    have hzz : z * z = 1 := hz.sq
    rcases hkz with h1 | h1 <;> rcases hk'z with h2 | h2
    · exact hs1 (by rw [h1, h2, one_mul])
    · exact hsz (by rw [h1, h2, one_mul])
    · exact hsz (by rw [h1, h2, mul_one])
    · exact hs1 (by rw [h1, h2, hzz])
  · refine ⟨k, hk, k', hk', rfl, h, ?_⟩
    have : k' * k' = (k * k)⁻¹ := eq_inv_of_mul_eq_one_right hsq
    rw [this, h]
    exact inv_eq_of_mul_eq_one_right hz.sq

theorem exists_conj_of_involutions_sup (e : K ≃* SL(2, F)) (e' : K' ≃* SL(2, F))
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (hcomm : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k) {s s' : G} (hs : s ∈ K ⊔ K')
    (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsz : s ≠ z) (hs' : s' ∈ K ⊔ K') (hs'2 : s' * s' = 1)
    (hs'1 : s' ≠ 1) (hs'z : s' ≠ z) : ∃ m ∈ K ⊔ K', m * s * m⁻¹ = s' := by
  obtain ⟨k, hk, k', hk', rfl, hkz, hk'z⟩ := exists_sq_eq_z_of_involution hodd e hz hz' hcomm hs hs2
    hs1 hsz
  obtain ⟨h, hh, h', hh', rfl, hhz, hh'z⟩ :=
    exists_sq_eq_z_of_involution hodd e hz hz' hcomm hs' hs'2 hs'1 hs'z
  have hzK := equiv_sl2_apply_eq_neg_one hodd e hz
  have hzK' := equiv_sl2_apply_eq_neg_one hodd e' hz'
  obtain ⟨x, hx⟩ := exists_conj_of_sq_eq_of_equiv_sl2 hodd e hzK
    (k := ⟨k, hk⟩) (h := ⟨h, hh⟩) (Subtype.ext hkz) (Subtype.ext hhz)
  obtain ⟨x', hx'⟩ := exists_conj_of_sq_eq_of_equiv_sl2 hodd e' hzK'
    (k := ⟨k', hk'⟩) (h := ⟨h', hh'⟩) (Subtype.ext hk'z) (Subtype.ext hh'z)
  obtain ⟨g, hgK, hg⟩ : ∃ g ∈ K, g * k * g⁻¹ = h := ⟨x, x.2, congrArg Subtype.val hx⟩
  obtain ⟨g', hgK', hg'⟩ : ∃ g' ∈ K', g' * k' * g'⁻¹ = h' := ⟨x', x'.2, congrArg Subtype.val hx'⟩
  refine ⟨g * g', Subgroup.mul_mem _ (Subgroup.mem_sup_left hgK) (Subgroup.mem_sup_right hgK'), ?_⟩
  have c1 : g' * k = k * g' := (hcomm k hk g' hgK').symm
  have c2 : g * (g' * k' * g'⁻¹) = (g' * k' * g'⁻¹) * g := by
    rw [hg']
    exact hcomm g hgK h' hh'
  calc g * g' * (k * k') * (g * g')⁻¹
      = (g * k * g⁻¹) * (g * (g' * k' * g'⁻¹) * g⁻¹) := by
        have : g * g' * (k * k') * (g * g')⁻¹ = g * (g' * k) * k' * g'⁻¹ * g⁻¹ := by group
        rw [this, c1]
        group
    _ = h * h' := by
        rw [c2, hg, hg']
        group

end Twin

end CFSG.ClassicalInvolution.Asc77.T3CII
