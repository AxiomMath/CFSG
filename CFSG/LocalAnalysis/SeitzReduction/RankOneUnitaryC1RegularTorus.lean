module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Regular

theorem exists_centralizing_of_regular {G : Type*} [Group G] {Y A₁ : Subgroup G} [Finite A₁]
    {Ω : Type*} [Finite Ω] {f : ℕ} (hf : 1 ≤ f) (hΩ : Nat.card Ω = 2 ^ f)
    (hA₁ : Nat.card A₁ = 2 ^ f) (φ : Y →* Equiv.Perm Ω) {N : Subgroup (Equiv.Perm Ω)}
    (hN : N ≤ φ.range) (hNn : (N.subgroupOf φ.range).Normal)
    (hNreg : ∀ a b : Ω, ∃! x : N, (x : Equiv.Perm Ω) a = b)
    (hYA : Y ≤ normalizer (A₁ : Set G))
    (hker : ∀ y : Y, φ y = 1 → ∀ c ∈ A₁, (y : G) * c * (y : G)⁻¹ = c)
    {d : G} (hdY : d ∈ Y)
    (hdtr : ∀ b ∈ A₁, ∀ b' ∈ A₁, b ≠ 1 → b' ≠ 1 → ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b')
    (a b : Ω) : ∃ y : Y, φ y a = b ∧ ∀ c ∈ A₁, (y : G) * c * (y : G)⁻¹ = c := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNcard : Nat.card N = 2 ^ f := by
    rw [← hΩ]
    refine Nat.card_eq_of_bijective (fun x : N => (x : Equiv.Perm Ω) a) ⟨fun x x' hxx => ?_,
      fun c => ?_⟩
    · obtain ⟨z, -, hz⟩ := hNreg a ((x : Equiv.Perm Ω) a)
      exact (hz x rfl).trans (hz x' hxx.symm).symm
    · obtain ⟨z, hz, -⟩ := hNreg a c
      exact ⟨z, hz⟩
  have hpow : ∀ y : Y, φ y ∈ N → φ (y ^ 2 ^ f) = 1 := by
    intro y hy
    have h1 : (⟨φ y, hy⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
    rw [hNcard] at h1
    rw [map_pow]
    exact congrArg Subtype.val h1
  let χ : Y →* MulAut A₁ := (A₁.normalizerMonoidHom).comp (inclusion hYA)
  have hχ : ∀ (y : Y) (c : A₁), ((χ y c : A₁) : G) = (y : G) * c * (y : G)⁻¹ :=
    fun _ _ => rfl
  set P : Subgroup (MulAut A₁) := (N.comap φ).map χ with hPdef
  have hP : IsPGroup 2 P := by
    rintro ⟨g, y, hy, rfl⟩
    refine ⟨f, Subtype.ext ?_⟩
    change (χ y) ^ 2 ^ f = 1
    rw [← map_pow]
    refine MulEquiv.ext fun c => Subtype.ext ?_
    rw [hχ, MulAut.one_apply]
    exact hker _ (hpow y hy) c c.2
  have h1 : (1 : A₁) ∈ MulAction.fixedPoints P A₁ := fun g => by
    change (g : MulAut A₁) 1 = 1
    exact map_one _
  obtain ⟨b₀, hb₀, hb₀1⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point A₁
    (by rw [hA₁]; exact dvd_pow_self 2 (by omega)) h1
  have hfix : ∀ y : Y, φ y ∈ N → (y : G) * b₀ * (y : G)⁻¹ = b₀ := by
    intro y hy
    have h2 := hb₀ ⟨χ y, y, hy, rfl⟩
    change χ y b₀ = b₀ at h2
    rw [← hχ, h2]
  set δ : Y := ⟨d, hdY⟩ with hδ
  have hconj : ∀ y : Y, φ y ∈ N → ∀ n : ℕ, φ (δ ^ n * y * (δ ^ n)⁻¹) ∈ N := by
    intro y hy n
    have h2 := hNn.conj_mem ⟨φ y, hN hy⟩ (mem_subgroupOf.mpr hy) ⟨φ (δ ^ n), δ ^ n, rfl⟩
    rw [mem_subgroupOf] at h2
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h2
  have hcent : ∀ y : Y, φ y ∈ N → ∀ c ∈ A₁, (y : G) * c * (y : G)⁻¹ = c := by
    intro y hy c hc
    by_cases hc1 : c = 1
    · rw [hc1, mul_one, mul_inv_cancel]
    have hb₀1' : (b₀ : G) ≠ 1 := fun h0 => hb₀1 (Subtype.ext h0.symm)
    obtain ⟨n, hn⟩ := hdtr _ b₀.2 _ hc hb₀1' hc1
    have h2 := hfix _ (hconj y hy n)
    have hcoe : ((δ ^ n * y * (δ ^ n)⁻¹ : Y) : G) = d ^ n * y * (d ^ n)⁻¹ := by
      simp [hδ]
    rw [hcoe] at h2
    have e : (y : G) * c * (y : G)⁻¹ =
        (d ^ n)⁻¹ * ((d ^ n * y * (d ^ n)⁻¹) * b₀ * (d ^ n * y * (d ^ n)⁻¹)⁻¹) * d ^ n := by
      rw [← hn]; group
    rw [e, h2, hn]
  obtain ⟨⟨x, hxN⟩, hx, -⟩ := hNreg a b
  obtain ⟨y, hy⟩ := hN hxN
  refine ⟨y, by rw [hy]; exact hx, hcent y (by rw [hy]; exact hxN)⟩

theorem two_transitive_of_stabilizer {Ω : Type*} {X : Subgroup (Equiv.Perm Ω)} (ω₀ : Ω)
    (htr : ∀ a : Ω, ∃ g ∈ X, g ω₀ = a)
    (hstab : ∀ a b : Ω, a ≠ ω₀ → b ≠ ω₀ → ∃ g ∈ X, g ω₀ = ω₀ ∧ g a = b) :
    ∀ a b c e : Ω, a ≠ b → c ≠ e → ∃ x ∈ X, x a = c ∧ x b = e := by
  intro a b c e hab hce
  obtain ⟨g₁, hg₁, hg₁a⟩ := htr a
  obtain ⟨g₂, hg₂, hg₂c⟩ := htr c
  have hb' : g₁⁻¹ b ≠ ω₀ := fun h1 => hab (by rw [← hg₁a, ← h1]; simp)
  have he' : g₂⁻¹ e ≠ ω₀ := fun h1 => hce (by rw [← hg₂c, ← h1]; simp)
  obtain ⟨k, hk, hk₀, hkb⟩ := hstab _ _ hb' he'
  refine ⟨g₂ * k * g₁⁻¹, mul_mem (mul_mem hg₂ hk) (inv_mem hg₁), ?_, ?_⟩
  · rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, Function.comp_apply,
      ← hg₁a]
    simp [hk₀, hg₂c]
  · rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, Function.comp_apply, hkb]
    simp

end U3C1Regular

end CFSG.SeitzReduction.RankOne
