module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Beta
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415E8c

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem card_le_twoPart_of_comm {G : Type} [Group G] [Finite G] {P : Subgroup G} {z : G}
    (hP : IsPGroup 2 P) (hzP : ∀ v ∈ P, z * v = v * z) :
    Nat.card P ≤ twoPart (centralizer ({z} : Set G)) :=
  card_le_twoPart hP fun v hv => mem_centralizer_singleton_iff.mpr (hzP v hv).symm

end L415

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem comm_of_mem_beta_z {x y : X}
    (hx : x ∈ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z) (hy : y ∈ W) :
    x * y = y * x := by
  have hσ := hs.setup
  have hz2 : z * z = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X (subset_closure (by simp))
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  obtain ⟨a, ha, b, hb, rfl⟩ := L415.mem_sup_of_commute hc.comm_beta_z hx
  have hay : a * y = y * a := by
    rcases L415.mem_zpowers_two hβ2 ha with rfl | rfl
    · simp
    · exact (hc.comm_beta hy).symm
  have hby : b * y = y * b := by
    rcases L415.mem_zpowers_two hz2 hb with rfl | rfl
    · simp
    · exact (hc.comm_z hy).symm
  calc a * b * y = a * (y * b) := by rw [mul_assoc, hby]
    _ = (a * y) * b := by group
    _ = y * a * b := by rw [hay]
    _ = y * (a * b) := by group

theorem mem_beta_z_cases {c : X}
    (hcm : c ∈ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z) :
    c = 1 ∨ c = w ^ (orderOf w / 2) * t ^ i * z ^ j ∨ c = z ∨
      c = w ^ (orderOf w / 2) * t ^ i * z ^ j * z := by
  have hσ := hs.setup
  have hz2 : z * z = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X (subset_closure (by simp))
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  obtain ⟨a, ha, b, hb, rfl⟩ := L415.mem_sup_of_commute hc.comm_beta_z hcm
  rcases L415.mem_zpowers_two hβ2 ha with rfl | rfl <;>
    rcases L415.mem_zpowers_two hz2 hb with rfl | rfl <;> simp

theorem conj_t_ne_mem_beta_z (g : X) :
    g * t * g⁻¹ ∉ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z := by
  intro h1
  apply hc.not_le_centralizer_conj g
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (hc.comm_of_mem_beta_z h1 (mem_inf.mp hx).1).symm

theorem conj_t_ne_z₁ (g : X) : g * t * g⁻¹ ≠ z₁ := by
  intro h1
  apply hc.not_le_centralizer_conj g
  rw [h1]
  exact inf_le_right

theorem conj_t_X_cases {g : X} (hg : g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z}) :
    g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∨
      g * t * g⁻¹ = t * z ∨ g * t * g⁻¹ = t * (w ^ (orderOf w / 2) * t ^ i * z ^ j * z) := by
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  rcases hc.mem_X_cases hg with h1 | h1
  · exact absurd h1 (hc.conj_t_ne_mem_beta_z g)
  · have h2 : g * t * g⁻¹ = t * (t * (g * t * g⁻¹)) := by rw [← mul_assoc t t, ht2, one_mul]
    rcases hc.mem_beta_z_cases h1 with h3 | h3 | h3 | h3
    · left
      rw [h2, h3, mul_one]
    · right; left
      rw [h2, h3]
    · right; right; left
      rw [h2, h3]
    · right; right; right
      rw [h2, h3]

theorem z₁_conj_t : z₁ * t * z₁⁻¹ = t * z := by
  have hz₁2 : z₁ * z₁ = 1 := by rw [← sq]; exact hc.sq_z₁
  have hz₁i : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁2
  rw [hc.comm_z hc.t_mem_W, hc.z_eq, hz₁i]
  group

theorem z₁_conj_t_mul :
    z₁ * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * z₁⁻¹ =
      t * (w ^ (orderOf w / 2) * t ^ i * z ^ j * z) := by
  have hσ := hs.setup
  have hβz : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z =
      z * (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
    hσ.X_comm hs.beta.mem_X (subset_closure (by simp))
  have hz₁β := hc.comm_beta hc.z₁_mem
  calc z₁ * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * z₁⁻¹ =
      (z₁ * t * z₁⁻¹) * (z₁ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z₁⁻¹) := by group
    _ = (t * z) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
      rw [hc.z₁_conj_t, hz₁β, mul_inv_cancel_right]
    _ = t * (w ^ (orderOf w / 2) * t ^ i * z ^ j * z) := by rw [mul_assoc, ← hβz]

theorem card_W_lt_V {𝒱 : Subgroup X} (hW𝒱 : W ≤ 𝒱)
    (hcen : ∀ c ∈ 𝒱, (∀ v ∈ 𝒱, c * v = v * c) → c = 1 ∨ c = z) :
    Nat.card W < Nat.card 𝒱 := by
  have hσ := hs.setup
  have hWV : W ≠ 𝒱 := by
    intro h1
    have hβW : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ W := hc.T_le_W (hσ.X_le_T hs.beta.mem_X)
    rcases hcen _ (hW𝒱 hβW) (fun v hv => (hc.comm_beta (by rw [h1]; exact hv)).symm) with
      h2 | h2
    · exact hs.beta.ne_one h2
    · exact hσ.beta_ne_z hs.beta h2
  exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hW𝒱 hWV)

theorem conj_z_ne_beta {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤) (hW𝒱 : W ≤ 𝒱)
    (hcen : ∀ c ∈ 𝒱, (∀ v ∈ 𝒱, c * v = v * c) → c = 1 ∨ c = z)
    (hz𝒱 : ∀ v ∈ 𝒱, z * v = v * z) (g : X) :
    g * z * g⁻¹ ≠ w ^ (orderOf w / 2) * t ^ i * z ^ j := by
  intro h1
  have h2 := L415.twoPart_centralizer_conj z g
  rw [h1] at h2
  have h3 := L415.card_le_twoPart_of_comm h𝒱.isPGroup hz𝒱
  have h4 := hc.card_W_lt_V hW𝒱 hcen
  have h5 : twoPart (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) =
      Nat.card W := hc.isSylowOf_W.card_eq.symm
  omega

end Config415

end CFSG.ComponentClassification.HarrisLit
