module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Ctx

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_four {U : Subgroup G} {z u g : G} (hz : z ∈ U) (hu : u ∈ U)
    (hcases : ∀ v ∈ U, v = 1 ∨ v = z ∨ v = u ∨ v = z * u) (hgz : g * z * g⁻¹ ∈ U)
    (hgu : g * u * g⁻¹ ∈ U) : g ∈ normalizer (U : Set G) := by
  have hfwd : ∀ v ∈ U, g * v * g⁻¹ ∈ U := by
    intro v hv
    rcases hcases v hv with rfl | rfl | rfl | rfl
    · simp
    · exact hgz
    · exact hgu
    · have : g * (z * u) * g⁻¹ = (g * z * g⁻¹) * (g * u * g⁻¹) := by group
      rw [this]; exact mul_mem hgz hgu
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hfwd h, fun hh => ?_⟩
  let φ : ↥U → ↥U := fun v => ⟨g * v * g⁻¹, hfwd v v.2⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    apply Subtype.ext
    have h2 : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := this
    simpa using h2
  have hsurj := Finite.injective_iff_surjective.1 hinj
  obtain ⟨v, hv⟩ := hsurj ⟨g * h * g⁻¹, hh⟩
  have h2 : g * (v : G) * g⁻¹ = g * h * g⁻¹ := congrArg Subtype.val hv
  have h3 : (v : G) = h := by simpa using h2
  rw [← h3]; exact v.2

theorem exists_three_elt {N : Subgroup G} {g z u : G} (hg : g ∈ N) (hzu : z * u = u * z)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z) (hgz : g * z * g⁻¹ = u)
    (hgu : g * u * g⁻¹ = z * u) :
    ∃ x ∈ N, IsPGroup 3 ↥(zpowers x) ∧ x * z * x⁻¹ ≠ z := by
  have hgzu : g * (z * u) * g⁻¹ = z := by
    calc g * (z * u) * g⁻¹ = (g * z * g⁻¹) * (g * u * g⁻¹) := by group
      _ = u * (z * u) := by rw [hgz, hgu]
      _ = z * (u * u) := by rw [← mul_assoc, ← hzu, mul_assoc]
      _ = z := by rw [hu2, mul_one]
  have hf : ∀ k : ℕ, (g ^ k * z * (g ^ k)⁻¹ = z ∧ k % 3 = 0) ∨
      (g ^ k * z * (g ^ k)⁻¹ = u ∧ k % 3 = 1) ∨ (g ^ k * z * (g ^ k)⁻¹ = z * u ∧ k % 3 = 2) := by
    intro k
    induction k with
    | zero => left; simp
    | succ k ih =>
      have e : g ^ (k + 1) * z * (g ^ (k + 1))⁻¹ = g * (g ^ k * z * (g ^ k)⁻¹) * g⁻¹ := by
        rw [pow_succ']; group
      rw [e]
      rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; left; exact ⟨by rw [h1, hgz], by omega⟩
      · right; right; exact ⟨by rw [h1, hgu], by omega⟩
      · left; exact ⟨by rw [h1, hgzu], by omega⟩
  obtain ⟨e, m, hm3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  refine ⟨g ^ m, N.pow_mem hg m, ?_, ?_⟩
  · have hpos : m ≠ 0 := by
      rintro rfl
      exact hm3 (dvd_zero 3)
    have hdvd : m ∣ orderOf g := ⟨3 ^ e, by rw [hn]; ring⟩
    have hord : orderOf (g ^ m) = 3 ^ e := by
      rw [orderOf_pow_of_dvd hpos hdvd]
      conv_lhs => rw [hn]
      rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hpos)]
    exact IsPGroup.of_card (n := e) (by rw [Nat.card_zpowers, hord])
  · have hm' : m % 3 ≠ 0 := fun h => hm3 (Nat.dvd_of_mod_eq_zero h)
    rcases hf m with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h2 hm'
    · rw [h1]; exact huz
    · rw [h1]
      intro hh
      apply hu1
      calc u = z⁻¹ * (z * u) := by group
        _ = z⁻¹ * z := by rw [hh]
        _ = 1 := by group

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
