module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

variable {Y : Type} [Group Y]

theorem map_mem_normalizer_of_fix {U : Subgroup Y} (c : MulAut Y) (hc : ∀ u ∈ U, c u = u)
    (hc' : ∀ u ∈ U, c⁻¹ u = u) {x : Y} (hx : x ∈ normalizer (U : Set Y)) :
    c x ∈ normalizer (U : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  have key : c x * h * (c x)⁻¹ = c (x * c⁻¹ h * x⁻¹) := by simp [map_mul]
  rw [key]
  constructor
  · intro hh
    have h1 : x * c⁻¹ h * x⁻¹ ∈ U := (hx (c⁻¹ h)).1 (by rw [hc' h hh]; exact hh)
    rw [hc _ h1]
    exact h1
  · intro hh
    have h1 : x * c⁻¹ h * x⁻¹ ∈ U := by
      have h2 : c⁻¹ (c (x * c⁻¹ h * x⁻¹)) = x * c⁻¹ h * x⁻¹ := c.symm_apply_apply _
      rw [hc' _ hh] at h2
      rw [← h2]
      exact hh
    have h3 : c⁻¹ h ∈ U := (hx (c⁻¹ h)).2 h1
    have h4 : c (c⁻¹ h) = h := c.apply_symm_apply h
    rw [hc _ h3] at h4
    rw [← h4]
    exact h3

theorem aut_eq_one_of_bruhat {r : ℕ} [Fact r.Prime] (b : MulAut Y) (hb : ¬ r ∣ orderOf b)
    {U M : Subgroup Y} (hM : normalizer (U : Set Y) = M) (hUp : IsPGroup r ↥U)
    (hUfix : ∀ u ∈ U, b u = u) {w : Y} (hw : w ∉ M)
    (hbr : ∀ g : Y, g ∉ M → ∃ u ∈ U, ∃ m ∈ M, g = u * w * m)
    (hcore : ∀ c : Y, (∀ x : Y, x⁻¹ * c * x ∈ M) → c = 1) : b = 1 := by
  have hUfix' : ∀ u ∈ U, b⁻¹ u = u := by
    intro u hu
    have h : b⁻¹ (b u) = u := b.symm_apply_apply u
    rwa [hUfix u hu] at h
  have hbM : ∀ x ∈ M, b x ∈ M := fun x hx => by
    rw [← hM] at hx ⊢
    exact map_mem_normalizer_of_fix b hUfix hUfix' hx
  have hbM' : ∀ x ∈ M, b⁻¹ x ∈ M := fun x hx => by
    rw [← hM] at hx ⊢
    exact map_mem_normalizer_of_fix b⁻¹ hUfix' (by simpa using hUfix) hx
  have hbw : b w ∉ M := fun h => hw (by
    have h1 := hbM' _ h
    have h2 : b⁻¹ (b w) = w := b.symm_apply_apply w
    rwa [h2] at h1)
  obtain ⟨u₀, hu₀, m₀, hm₀, hbw'⟩ := hbr _ hbw
  have hpow : ∀ k : ℕ, ∃ μ ∈ M, (b ^ k) w = u₀ ^ k * w * μ := by
    intro k
    induction k with
    | zero => exact ⟨1, M.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨μ, hμ, hk⟩ := ih
      refine ⟨m₀ * b μ, M.mul_mem hm₀ (hbM μ hμ), ?_⟩
      rw [pow_succ', MulAut.mul_apply, hk, map_mul, map_mul, map_pow, hUfix u₀ hu₀, hbw']
      simp only [pow_succ, mul_assoc]
  obtain ⟨μ, hμ, hbm⟩ := hpow (orderOf b)
  rw [pow_orderOf_eq_one, MulAut.one_apply] at hbm
  have hQ : w⁻¹ * u₀ ^ orderOf b * w ∈ M := by
    have h1 : w⁻¹ * u₀ ^ orderOf b * w = μ⁻¹ := by
      calc w⁻¹ * u₀ ^ orderOf b * w = w⁻¹ * (u₀ ^ orderOf b * w * μ) * μ⁻¹ := by group
        _ = w⁻¹ * w * μ⁻¹ := by rw [← hbm]
        _ = μ⁻¹ := by group
    rw [h1]
    exact M.inv_mem hμ
  obtain ⟨j, hj⟩ := hUp ⟨u₀, hu₀⟩
  have hj' : u₀ ^ r ^ j = 1 := congrArg Subtype.val hj
  have hcop : Nat.Coprime (orderOf b) (r ^ j) :=
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hb).symm.pow_right j
  have hcop' : Nat.Coprime (orderOf b) (orderOf u₀) :=
    hcop.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hj')
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop'
  have hu₀M : w⁻¹ * u₀ * w ∈ M := by
    have h1 : w⁻¹ * (u₀ ^ orderOf b) ^ n * w = (w⁻¹ * u₀ ^ orderOf b * w) ^ n := by
      have := conj_pow (a := w⁻¹) (b := u₀ ^ orderOf b) (i := n)
      simpa only [inv_inv] using this.symm
    rw [hn] at h1
    rw [h1]
    exact M.pow_mem hQ n
  have hbw'' : w⁻¹ * b w ∈ M := by
    rw [hbw']
    have : w⁻¹ * (u₀ * w * m₀) = (w⁻¹ * u₀ * w) * m₀ := by group
    rw [this]
    exact M.mul_mem hu₀M hm₀
  have hg : ∀ g : Y, g⁻¹ * b g ∈ M := by
    intro g
    by_cases hgM : g ∈ M
    · exact M.mul_mem (M.inv_mem hgM) (hbM g hgM)
    · obtain ⟨u, hu, m, hm, rfl⟩ := hbr g hgM
      rw [map_mul, map_mul, hUfix u hu]
      have : (u * w * m)⁻¹ * (u * b w * b m) = m⁻¹ * (w⁻¹ * b w) * b m := by group
      rw [this]
      exact M.mul_mem (M.mul_mem (M.inv_mem hm) hbw'') (hbM m hm)
  ext z
  rw [MulAut.one_apply]
  have hc : z⁻¹ * b z = 1 := hcore _ fun x => by
    have h1 := hg (z * x)
    have h2 := hg x
    have : x⁻¹ * (z⁻¹ * b z) * x = ((z * x)⁻¹ * b (z * x)) * (x⁻¹ * b x)⁻¹ := by
      rw [map_mul]
      group
    rw [this]
    exact M.mul_mem h1 (M.inv_mem h2)
  exact (inv_mul_eq_one.1 hc).symm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
