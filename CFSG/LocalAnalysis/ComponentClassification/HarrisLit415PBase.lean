module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma415Inputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X]

structure Data415B (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X)
    (V : Subgroup X) (i j : ℕ) (z₁ τ α : X) (K₂ W 𝒱 : Subgroup X) : Prop where
  hs : Setting46e t L p f S w z V i j
  h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)
  h47 : ∀ i' j' : ℕ, IsLemma47 p (w ^ (orderOf w / 2) * t ^ i' * z ^ j')
  hnq : ¬ IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
  fd : Harris415FData t L S (w ^ (orderOf w / 2)) z (w ^ (orderOf w / 2) * t ^ i * z ^ j)
    z₁ τ α K₂ W 𝒱

variable {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem t_mul_t : t * t = 1 := by
  rw [← sq, ← hD.hs.standing.config.orderOf_eq, pow_orderOf_eq_one]

theorem beta_mul_beta :
    (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) = 1 := by
  rw [← sq]
  exact hD.hs.setup.sq_eq_one_of_mem_X hD.hs.beta.mem_X

theorem z₁_mul_z₁ : z₁ * z₁ = 1 := by
  rw [← sq]
  exact hD.fd.sq_z₁

theorem t_comm_beta :
    t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) = (w ^ (orderOf w / 2) * t ^ i * z ^ j) * t :=
  mem_centralizer_singleton_iff.mp (hD.hs.setup.t_mem_centralizer_beta i j)

theorem K₂_le : K₂ ≤ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} :=
  hD.fd.isTwoComponentIn_K₂.1

theorem z₂_comm_beta : t * z₁ * t⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
    (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (t * z₁ * t⁻¹) :=
  mem_centralizer_singleton_iff.mp (mem_inf.mp (hD.K₂_le hD.fd.z₂_mem)).2

theorem beta_comm_z₁ :
    (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z₁ = z₁ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have ht := hD.t_comm_beta
  have hti : t⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      (w ^ (orderOf w / 2) * t ^ i * z ^ j) * t⁻¹ := by
    calc t⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
        t⁻¹ * ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * t⁻¹ := by rw [ht]
      _ = (w ^ (orderOf w / 2) * t ^ i * z ^ j) * t⁻¹ := by group
  have h2 := hD.z₂_comm_beta
  calc (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z₁ =
      t⁻¹ * ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * (t * z₁ * t⁻¹)) * t := by
        rw [← mul_assoc t⁻¹, hti]
        group
    _ = t⁻¹ * (t * z₁ * t⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * t := by rw [h2]
    _ = z₁ * (t⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * t) := by group
    _ = z₁ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
      rw [hti, mul_assoc, inv_mul_cancel, mul_one]

theorem z_ne_one : z ≠ 1 := hD.hs.setup.z_ne_one

theorem z₁_ne_one : z₁ ≠ 1 := fun h1 => hD.fd.z₁_ne (by rw [h1]; group)

theorem z₂_ne_one : t * z₁ * t⁻¹ ≠ 1 := fun h1 => hD.z₁_ne_one (by
  calc z₁ = t⁻¹ * (t * z₁ * t⁻¹) * t := by group
    _ = 1 := by rw [h1]; group)

theorem mem_center_of_mem {y : X} (hy : y ∈ closure ({z₁, t * z₁ * t⁻¹} : Set X)) :
    y ∈ 𝒱 ⊓ centralizer {z₁} ∧ ∀ v ∈ 𝒱 ⊓ centralizer {z₁}, v * y = y * v := by
  rw [← hD.fd.center_𝒱₀] at hy
  obtain ⟨c, hc, rfl⟩ := hy
  refine ⟨c.2, fun v hv => ?_⟩
  have h1 := Subgroup.mem_center_iff.mp hc ⟨v, hv⟩
  exact congrArg Subtype.val h1

theorem z₁_mem_V₀ : z₁ ∈ 𝒱 ⊓ centralizer {z₁} :=
  (hD.mem_center_of_mem (subset_closure (by simp))).1

theorem z₂_mem_V₀ : t * z₁ * t⁻¹ ∈ 𝒱 ⊓ centralizer {z₁} :=
  (hD.mem_center_of_mem (subset_closure (by simp))).1

theorem comm_z₂ {v : X} (hv : v ∈ 𝒱 ⊓ centralizer {z₁}) :
    v * (t * z₁ * t⁻¹) = (t * z₁ * t⁻¹) * v :=
  (hD.mem_center_of_mem (subset_closure (by simp))).2 v hv

theorem z_mem_center : z ∈ 𝒱 ⊓ centralizer {z₁} ∧
    ∀ v ∈ 𝒱 ⊓ centralizer {z₁}, v * z = z * v := by
  have hz : z ∈ closure ({z₁, t * z₁ * t⁻¹} : Set X) := by
    rw [hD.fd.z_eq]
    exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  exact hD.mem_center_of_mem hz

theorem beta_mem_W : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβ2 : IsPGroup 2 (zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime ?_ ?_
    · rw [sq]
      exact hD.beta_mul_beta
    · exact hD.hs.beta.ne_one
  have hN : W ≤ normalizer ((zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) : Subgroup X) :
      Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [centralizer_zpowers_eq]
    exact hD.fd.isSylowOf_W.le
  have hp := hD.fd.isSylowOf_W.isPGroup.to_sup_of_normal_right' hβ2 hN
  have heq := hD.fd.isSylowOf_W.eq_of_le le_sup_left
    (sup_le hD.fd.isSylowOf_W.le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))) hp
  rw [← heq]
  exact mem_sup_right (mem_zpowers _)

theorem beta_mem_V₀ : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ 𝒱 ⊓ centralizer {z₁} :=
  mem_inf.mpr ⟨hD.fd.W_le hD.beta_mem_W, mem_centralizer_singleton_iff.mpr hD.beta_comm_z₁⟩

end Data415B

end CFSG.ComponentClassification.HarrisLit
