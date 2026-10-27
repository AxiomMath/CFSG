module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharOutTower

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open scoped commutatorElement

@[expose] def OutTwoTowerAt (K : Type*) [Group K] (p : ℕ) : Prop :=
  ∃ D : Subgroup (MulAut K),
    (∀ γ α : MulAut K, (∃ k : ℕ, α ^ (p ^ k) = 1) → γ * α * γ⁻¹ * α⁻¹ ∈ D) ∧
    ∀ α : MulAut K, (∃ k : ℕ, α ^ (p ^ k) = 1) → ∀ δ ∈ D, (∃ k : ℕ, δ ^ (2 ^ k) ∈ inner K) →
      α * δ * α⁻¹ * δ⁻¹ ∈ inner K

theorem outTwoTowerAt_of_outTowerAt {K : Type*} [Group K] {p : ℕ} (h : OutTowerAt K p) :
    OutTwoTowerAt K p := by
  obtain ⟨D, hD, hcent⟩ := h
  exact ⟨D, hD, fun α hα δ hδ _ => hcent α hα δ hδ⟩

theorem OutTwoTowerAt.of_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L) {p : ℕ}
    (h : OutTwoTowerAt L p) : OutTwoTowerAt K p := by
  obtain ⟨D, hab, hcent⟩ := h
  have hinner : ∀ x : MulAut K, MulAut.congr e x ∈ inner L ↔ x ∈ inner K := by
    intro x
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e]
    constructor
    · rintro hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := (MulAut.congr e).injective hyx
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨D.comap (MulAut.congr e).toMonoidHom, fun γ α ⟨k, hk⟩ => ?_,
    fun α ⟨k, hk⟩ δ hδ ⟨m, hm⟩ => ?_⟩
  · have hk' : (MulAut.congr e α) ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
    change MulAut.congr e (γ * α * γ⁻¹ * α⁻¹) ∈ D
    simpa only [map_mul, map_inv] using hab (MulAut.congr e γ) (MulAut.congr e α) ⟨k, hk'⟩
  · have hk' : (MulAut.congr e α) ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
    have hm' : (MulAut.congr e δ) ^ (2 ^ m) ∈ inner L := by
      rw [← map_pow]
      exact (hinner _).2 hm
    have := hcent (MulAut.congr e α) ⟨k, hk'⟩ (MulAut.congr e δ) hδ ⟨m, hm'⟩
    rw [← hinner]
    simpa only [map_mul, map_inv] using this

theorem eq_one_of_commutator_comm {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {t a d : G} {k m : ℕ} (hd : d = t * a * t⁻¹ * a⁻¹) (hk : a ^ (p ^ k) = 1)
    (hcomm : a * d * a⁻¹ = d) (hm : d ^ (2 ^ m) = 1) : d = 1 := by
  have hdc : Commute a d := mul_inv_eq_iff_eq_mul.1 hcomm
  have key : ∀ j : ℕ, a ^ j * t⁻¹ * (a ^ j)⁻¹ = t⁻¹ * d ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : a * t⁻¹ * a⁻¹ = t⁻¹ * d := by rw [hd]; group
      have h2 : a * d ^ j * a⁻¹ = d ^ j := by
        have := (hdc.pow_right j).eq
        rw [this]; group
      calc a ^ (j + 1) * t⁻¹ * (a ^ (j + 1))⁻¹
          = a * (a ^ j * t⁻¹ * (a ^ j)⁻¹) * a⁻¹ := by rw [pow_succ']; group
        _ = a * (t⁻¹ * d ^ j) * a⁻¹ := by rw [ih]
        _ = (a * t⁻¹ * a⁻¹) * (a * d ^ j * a⁻¹) := by group
        _ = t⁻¹ * d ^ (j + 1) := by rw [h1, h2, pow_succ]; group
  have h3 := key (p ^ k)
  rw [hk] at h3
  simp only [pow_zero, one_mul, inv_one, mul_one] at h3
  have h4 : d ^ (p ^ k) = 1 := by
    have : t⁻¹ * d ^ (p ^ k) = t⁻¹ * 1 := by rw [mul_one]; exact h3.symm
    exact mul_left_cancel this
  have hcop : Nat.Coprime (p ^ k) (2 ^ m) :=
    Nat.Coprime.pow k m ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have h5 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h4)
    (orderOf_dvd_of_pow_eq_one hm)
  exact orderOf_eq_one_iff.1 h5

theorem commutator_le_inner_of_outTwoTower {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : OutTwoTowerAt K p) {P T : Subgroup (MulAut K)} (hP : IsPGroup p P)
    (hT : IsPGroup 2 T) (hPT : P ≤ Subgroup.normalizer (T : Set (MulAut K))) :
    ⁅T, P⁆ ≤ inner K := by
  obtain ⟨D, hD, hcent⟩ := h
  rw [Subgroup.commutator_le]
  intro t ht a ha
  obtain ⟨k, hk⟩ := hP ⟨a, ha⟩
  have hk' : a ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  set δ : MulAut K := t * a * t⁻¹ * a⁻¹ with hδ
  have hδD : δ ∈ D := hD t a ⟨k, hk'⟩
  have hδT : δ ∈ T := by
    have h1 : a * t⁻¹ * a⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hPT ha) t⁻¹).1 (T.inv_mem ht)
    have : δ = t * (a * t⁻¹ * a⁻¹) := by rw [hδ]; group
    rw [this]
    exact T.mul_mem ht h1
  obtain ⟨m, hm⟩ := hT ⟨δ, hδT⟩
  have hm' : δ ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have hcomm := hcent a ⟨k, hk'⟩ δ hδD ⟨m, by rw [hm']; exact (inner K).one_mem⟩
  haveI : (inner K).Normal := inner_normal K
  let π : MulAut K →* MulAut K ⧸ inner K := QuotientGroup.mk' (inner K)
  have h1 : π (a * δ * a⁻¹ * δ⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hcomm
  have hcomm' : π a * π δ * (π a)⁻¹ = π δ := by
    simp only [map_mul, map_inv] at h1
    exact mul_inv_eq_one.1 (by simpa [mul_assoc] using h1)
  have hd' : π δ = π t * π a * (π t)⁻¹ * (π a)⁻¹ := by
    rw [hδ]; simp only [map_mul, map_inv]
  have hk'' : (π a) ^ (p ^ k) = 1 := by rw [← map_pow, hk', map_one]
  have hm'' : (π δ) ^ (2 ^ m) = 1 := by rw [← map_pow, hm', map_one]
  have := eq_one_of_commutator_comm hp hp2 hd' hk'' hcomm' hm''
  exact (QuotientGroup.eq_one_iff _).1 this

end CFSG.LocalAnalysis.GLTheoremA
