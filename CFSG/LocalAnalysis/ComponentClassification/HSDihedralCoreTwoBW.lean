module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoBE

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HSFLit (ElemAbelianTwo mem_or_mul_mem_of_mem_sup_zpowers)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

namespace LocalDatum

variable {Δ : LocalDatum X A}

namespace TwoBSplit

variable {φ : Δ.Fusion} (B : TwoBSplit φ)

abbrev b₁ : X := B.e * Δ.db * B.e⁻¹

abbrev db' : X := B.d₀⁻¹ * Δ.db * B.d₀

omit [Finite X] in
theorem db'_mem : B.db' ∈ Δ.D := by
  simpa [db'] using Δ.conj_mem_D _ (inv_mem B.d₀S) _ Δ.db_mem

omit [Finite X] in
theorem b₁_eq : B.b₁ = φ.x * B.db' * φ.x⁻¹ := B.conj_e_D _

include B in
omit [Finite X] in
theorem uniq {a a' b b' : X} (ha : a ∈ Δ.D) (ha' : a' ∈ Δ.D) (hb : b ∈ Δ.D) (hb' : b' ∈ Δ.D)
    (h : a * (φ.x * b * φ.x⁻¹) = a' * (φ.x * b' * φ.x⁻¹)) : a = a' ∧ b = b' :=
  TwoB_unique φ B.hD1 ha ha' hb hb' h

include B in
omit [Finite X] in
theorem tz_eq : Δ.t * Δ.dz = Δ.dz * (φ.x * Δ.dz * φ.x⁻¹) := by
  rw [B.conj_dz, (Δ.commute_t (Δ.D_le Δ.dz_mem))]

include B in
theorem tz_comm {s : X} (hs : s ∈ Δ.S) : Δ.t * Δ.dz * s = s * (Δ.t * Δ.dz) := by
  rw [mul_assoc, ← Δ.dz_comm_S B.h8 hs, ← mul_assoc, ← Δ.commute_t hs, mul_assoc]

omit B in
theorem tz_sq : (Δ.t * Δ.dz) ^ 2 = 1 := by
  rw [(show Commute Δ.t Δ.dz from (Δ.commute_t (Δ.D_le Δ.dz_mem)).symm).mul_pow, Δ.t_sq, Δ.dz_sq, one_mul]

theorem bb_sq : (Δ.db * B.b₁) ^ 2 = 1 := by
  have hc : Commute Δ.db B.b₁ := by
    change Δ.db * B.b₁ = B.b₁ * Δ.db
    rw [B.b₁_eq]
    exact B.comm₁ Δ.db_mem B.db'_mem
  rw [hc.mul_pow, Δ.db_sq, one_mul]
  show (B.e * Δ.db * B.e⁻¹) ^ 2 = 1
  rw [conj_pow, Δ.db_sq]
  group

omit [Finite X] in
theorem bb_S : Δ.db * B.b₁ ∈ Δ.S := mul_mem (Δ.D_le Δ.db_mem) (B.conj_e_S (Δ.D_le Δ.db_mem))

theorem tz_e : Δ.t * Δ.dz * B.e = B.e * (Δ.t * Δ.dz) := by
  have h : B.e * (Δ.t * Δ.dz) * B.e⁻¹ = Δ.t * Δ.dz := by
    calc B.e * (Δ.t * Δ.dz) * B.e⁻¹ = (B.e * Δ.t * B.e⁻¹) * (B.e * Δ.dz * B.e⁻¹) := by group
      _ = Δ.t * Δ.dz := by rw [B.conj_e_t, B.conj_e_dz, Δ.commute_t (Δ.D_le Δ.dz_mem)]
  calc Δ.t * Δ.dz * B.e = B.e * (Δ.t * Δ.dz) * B.e⁻¹ * B.e := by rw [h]
    _ = B.e * (Δ.t * Δ.dz) := by group

theorem bb_e : Δ.db * B.b₁ * B.e = B.e * (Δ.db * B.b₁) := by
  have hc : Δ.db * B.b₁ = B.b₁ * Δ.db := by rw [B.b₁_eq]; exact B.comm₁ Δ.db_mem B.db'_mem
  have h1 : B.e * B.b₁ * B.e⁻¹ = Δ.db := by
    show B.e * (B.e * Δ.db * B.e⁻¹) * B.e⁻¹ = Δ.db
    have : B.e * (B.e * Δ.db * B.e⁻¹) * B.e⁻¹ = B.e ^ 2 * Δ.db * (B.e ^ 2)⁻¹ := by
      rw [pow_two]; group
    rw [this, B.e_sq]; group
  have h : B.e * (Δ.db * B.b₁) * B.e⁻¹ = Δ.db * B.b₁ := by
    calc B.e * (Δ.db * B.b₁) * B.e⁻¹ = (B.e * Δ.db * B.e⁻¹) * (B.e * B.b₁ * B.e⁻¹) := by group
      _ = B.b₁ * Δ.db := by rw [h1]
      _ = Δ.db * B.b₁ := hc.symm
  calc Δ.db * B.b₁ * B.e = B.e * (Δ.db * B.b₁) * B.e⁻¹ * B.e := by rw [h]
    _ = B.e * (Δ.db * B.b₁) := by group

abbrev E : Subgroup X := zpowers (Δ.t * Δ.dz) ⊔ zpowers (Δ.db * B.b₁) ⊔ zpowers B.e

theorem elem_E : ElemAbelianTwo B.E :=
  elem_E8 (tz_sq (Δ := Δ)) B.bb_sq B.e_sq (B.tz_comm B.bb_S) B.tz_e B.bb_e

theorem card_E : Nat.card B.E = 8 := by
  have htz1 : Δ.t * Δ.dz ≠ 1 := fun h => Δ.t_not_mem_D (by
    rw [show Δ.t = Δ.dz⁻¹ by rw [← mul_eq_one_iff_eq_inv.mp h]]
    exact inv_mem Δ.dz_mem)
  have hbb1 : Δ.db * B.b₁ ≠ 1 := fun h => Δ.db_ne_one (by
    have := B.uniq Δ.db_mem (one_mem _) B.db'_mem (one_mem _)
      (by rw [← B.b₁_eq, h]; group)
    exact this.1)
  have hbbtz : Δ.db * B.b₁ ≠ Δ.t * Δ.dz := fun h => Δ.db_ne_dz (by
    have := B.uniq Δ.db_mem Δ.dz_mem B.db'_mem Δ.dz_mem (by rw [← B.b₁_eq, h, B.tz_eq])
    exact this.1)
  have heS := B.e_not_mem
  refine card_E8 (tz_sq (Δ := Δ)) B.bb_sq B.e_sq (B.tz_comm B.bb_S) B.tz_e B.bb_e htz1 hbb1 hbbtz
    ⟨fun h => heS (h ▸ one_mem _), fun h => heS (h ▸ mul_mem Δ.t_mem (Δ.D_le Δ.dz_mem)),
      fun h => heS (h ▸ B.bb_S), fun h => heS (h ▸ mul_mem (mul_mem Δ.t_mem (Δ.D_le Δ.dz_mem)) B.bb_S)⟩

end TwoBSplit

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
