module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoBW

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HSFLit (ElemAbelianTwo mem_or_mul_mem_of_mem_sup_zpowers)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

namespace LocalDatum

variable {Δ : LocalDatum X A}

namespace TwoBSplit

variable {φ : Δ.Fusion} (B : TwoBSplit φ)

abbrev T₁ : Subgroup X := Δ.S ⊔ zpowers B.e

theorem e_norm : B.e ∈ normalizer (Δ.S : Set X) := by
  rw [mem_normalizer_iff]
  intro s
  refine ⟨B.conj_e_S, fun h => ?_⟩
  have h' := B.conj_e_S h
  have : B.e * (B.e * s * B.e⁻¹) * B.e⁻¹ = B.e ^ 2 * s * (B.e ^ 2)⁻¹ := by rw [pow_two]; group
  rw [this, B.e_sq] at h'
  simpa using h'

theorem mem_T₁ {g : X} (hg : g ∈ B.T₁) : g ∈ Δ.S ∨ g * B.e ∈ Δ.S :=
  mem_or_mul_mem_of_mem_sup_zpowers B.e_sq B.e_norm hg

omit [Finite X] in
theorem e_T₁ : B.e ∈ B.T₁ := mem_sup_right (mem_zpowers _)

omit [Finite X] in
theorem S_T₁ {s : X} (hs : s ∈ Δ.S) : s ∈ B.T₁ := mem_sup_left hs

omit [Finite X] in
theorem T₁_le : B.T₁ ≤ φ.T := sup_le φ.le (zpowers_le.mpr B.e_mem)

theorem eq_mul_e {g : X} : g = g * B.e * B.e := by
  rw [mul_assoc, ← pow_two, B.e_sq, mul_one]

theorem tz_central {g : X} (hg : g ∈ B.T₁) : Δ.t * Δ.dz * g = g * (Δ.t * Δ.dz) := by
  rcases B.mem_T₁ hg with h | h
  · exact B.tz_comm h
  · calc Δ.t * Δ.dz * g = Δ.t * Δ.dz * (g * B.e * B.e) := by rw [← B.eq_mul_e]
      _ = (Δ.t * Δ.dz * (g * B.e)) * B.e := by group
      _ = (g * B.e) * (Δ.t * Δ.dz) * B.e := by rw [B.tz_comm h]
      _ = (g * B.e) * (B.e * (Δ.t * Δ.dz)) := by rw [mul_assoc, B.tz_e]
      _ = g * (Δ.t * Δ.dz) := by rw [← mul_assoc, ← B.eq_mul_e]

theorem conj_t_T₁ {g : X} (hg : g ∈ B.T₁) : g * Δ.t * g⁻¹ = Δ.t ∨ g * Δ.t * g⁻¹ = Δ.dz := by
  rcases B.mem_T₁ hg with h | h
  · left
    rw [Δ.commute_t h, mul_inv_cancel_right]
  · right
    have h1 : (g * B.e) * Δ.dz * (g * B.e)⁻¹ = Δ.dz := by
      rw [Δ.dz_comm_S B.h8 h, mul_inv_cancel_right]
    calc g * Δ.t * g⁻¹ = (g * B.e) * (B.e * Δ.t * B.e⁻¹) * (g * B.e)⁻¹ := by
          rw [B.e_inv]; nth_rw 1 [B.eq_mul_e (g := g)]; group
      _ = Δ.dz := by rw [B.conj_e_t, h1]

include B in
theorem central_left {a b : X} (ha : a ∈ Δ.D) (hb : b ∈ Δ.D)
    (hc : ∀ g ∈ Δ.D, g * (a * (φ.x * b * φ.x⁻¹)) * g⁻¹ = a * (φ.x * b * φ.x⁻¹) ∨
      g * (a * (φ.x * b * φ.x⁻¹)) * g⁻¹ = a * (φ.x * b * φ.x⁻¹) * (Δ.t * Δ.dz)) :
    a = 1 ∨ a = Δ.dz := by
  refine Δ.eq_dz_of_central B.h8 ha fun g hg => ?_
  have hgb := B.comm₁ hg hb
  have he : g * (a * (φ.x * b * φ.x⁻¹)) * g⁻¹ = (g * a * g⁻¹) * (φ.x * b * φ.x⁻¹) := by
    have hy : g * (φ.x * b * φ.x⁻¹) * g⁻¹ = φ.x * b * φ.x⁻¹ := by rw [hgb]; group
    calc g * (a * (φ.x * b * φ.x⁻¹)) * g⁻¹ =
        (g * a * g⁻¹) * (g * (φ.x * b * φ.x⁻¹) * g⁻¹) := by group
      _ = (g * a * g⁻¹) * (φ.x * b * φ.x⁻¹) := by rw [hy]
  have hgaD : g * a * g⁻¹ ∈ Δ.D := Δ.conj_mem_D g (Δ.D_le hg) a ha
  rcases hc g hg with h | h
  · rw [he] at h
    have := (B.uniq hgaD ha hb hb h).1
    calc a * g = g * a * g⁻¹ * g := by rw [this]
      _ = g * a := by group
  · exfalso
    rw [he] at h
    have h' : (g * a * g⁻¹) * (φ.x * b * φ.x⁻¹) =
        (a * Δ.dz) * (φ.x * (b * Δ.dz) * φ.x⁻¹) := by
      rw [h]
      calc a * (φ.x * b * φ.x⁻¹) * (Δ.t * Δ.dz) =
          a * (φ.x * b * φ.x⁻¹) * (Δ.dz * (φ.x * Δ.dz * φ.x⁻¹)) := by rw [B.tz_eq]
        _ = a * (Δ.dz * (φ.x * b * φ.x⁻¹)) * (φ.x * Δ.dz * φ.x⁻¹) := by
            rw [B.comm₁ Δ.dz_mem hb]; group
        _ = (a * Δ.dz) * (φ.x * (b * Δ.dz) * φ.x⁻¹) := by group
    have := (B.uniq hgaD (mul_mem ha Δ.dz_mem) hb (mul_mem hb Δ.dz_mem) h').2
    apply Δ.dz_ne_one
    calc Δ.dz = b⁻¹ * (b * Δ.dz) := by group
      _ = 1 := by rw [← this, inv_mul_cancel]

include B in
theorem mul_tz {a b : X} (hb : b ∈ Δ.D) :
    a * (φ.x * b * φ.x⁻¹) * (Δ.t * Δ.dz) = (a * Δ.dz) * (φ.x * (b * Δ.dz) * φ.x⁻¹) := by
  calc a * (φ.x * b * φ.x⁻¹) * (Δ.t * Δ.dz) =
      a * (φ.x * b * φ.x⁻¹) * (Δ.dz * (φ.x * Δ.dz * φ.x⁻¹)) := by rw [B.tz_eq]
    _ = a * (Δ.dz * (φ.x * b * φ.x⁻¹)) * (φ.x * Δ.dz * φ.x⁻¹) := by
        rw [B.comm₁ Δ.dz_mem hb]; group
    _ = (a * Δ.dz) * (φ.x * (b * Δ.dz) * φ.x⁻¹) := by group

include B in
theorem central_right {a b : X} (ha : a ∈ Δ.D) (hb : b ∈ Δ.D)
    (hc : ∀ g ∈ Δ.D, (φ.x * g * φ.x⁻¹) * (a * (φ.x * b * φ.x⁻¹)) * (φ.x * g * φ.x⁻¹)⁻¹ =
        a * (φ.x * b * φ.x⁻¹) ∨
      (φ.x * g * φ.x⁻¹) * (a * (φ.x * b * φ.x⁻¹)) * (φ.x * g * φ.x⁻¹)⁻¹ =
        a * (φ.x * b * φ.x⁻¹) * (Δ.t * Δ.dz)) :
    b = 1 ∨ b = Δ.dz := by
  refine Δ.eq_dz_of_central B.h8 hb fun g hg => ?_
  have hag := B.comm₁ ha hg
  have he : (φ.x * g * φ.x⁻¹) * (a * (φ.x * b * φ.x⁻¹)) * (φ.x * g * φ.x⁻¹)⁻¹ =
      a * (φ.x * (g * b * g⁻¹) * φ.x⁻¹) := by
    calc (φ.x * g * φ.x⁻¹) * (a * (φ.x * b * φ.x⁻¹)) * (φ.x * g * φ.x⁻¹)⁻¹ =
        ((φ.x * g * φ.x⁻¹) * a) * (φ.x * b * φ.x⁻¹) * (φ.x * g * φ.x⁻¹)⁻¹ := by group
      _ = a * (φ.x * (g * b * g⁻¹) * φ.x⁻¹) := by rw [← hag]; group
  have hgbD : g * b * g⁻¹ ∈ Δ.D := Δ.conj_mem_D g (Δ.D_le hg) b hb
  rcases hc g hg with h | h
  · rw [he] at h
    have := (B.uniq ha ha hgbD hb h).2
    calc b * g = g * b * g⁻¹ * g := by rw [this]
      _ = g * b := by group
  · exfalso
    rw [he, B.mul_tz hb] at h
    have := (B.uniq ha (mul_mem ha Δ.dz_mem) hgbD (mul_mem hb Δ.dz_mem) h).1
    apply Δ.dz_ne_one
    calc Δ.dz = a⁻¹ * (a * Δ.dz) := by group
      _ = 1 := by rw [← this, inv_mul_cancel]

include B in
omit [Finite X] in
theorem eq_of_central_parts {a b : X} (ha : a = 1 ∨ a = Δ.dz) (hb : b = 1 ∨ b = Δ.dz) :
    a * (φ.x * b * φ.x⁻¹) = 1 ∨ a * (φ.x * b * φ.x⁻¹) = Δ.t ∨
      a * (φ.x * b * φ.x⁻¹) = Δ.dz ∨ a * (φ.x * b * φ.x⁻¹) = Δ.t * Δ.dz := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · left; group
  · right; left; rw [one_mul, B.conj_dz]
  · right; right; left; group
  · right; right; right; rw [B.conj_dz, Δ.commute_t (Δ.D_le Δ.dz_mem)]

end TwoBSplit

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
