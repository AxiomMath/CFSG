module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def ParabCore (X : Type*) [Group X] (q : ℕ) : Prop :=
  ∀ (T : Sylow 2 X) (J : Subgroup X), Subgroup.normalizer (T : Set X) ≤ J →
    J ≠ Subgroup.normalizer (T : Set X) → ∀ p : ℕ, p.Prime → 5 ≤ p →
      (p ∣ q ^ 2 - 1 → ∃ V : Subgroup X, V ≤ J ∧ ⁅V, V⁆ = V ∧ p ∣ Nat.card V) ∧
        (p ∣ Nat.card J → J = ⊤ ∨ ∃ V : Subgroup X, V ≤ J ∧ ⁅V, V⁆ = V ∧ p ∣ Nat.card V)

variable {Y X : Type*} [Group Y] [Group X]

theorem mem_sylow_of_central [Finite Y] (S : Sylow 2 Y) {z : Y} (hz : z ∈ Subgroup.center Y)
    (h2 : ∃ k : ℕ, z ^ 2 ^ k = 1) : z ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2
  have hP : IsPGroup 2 (Subgroup.zpowers z) := by
    rintro ⟨g, m, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    simp only [OneMemClass.coe_one, Subgroup.coe_pow]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq Y S Q
  have hzQ : z ∈ ((h • S : Sylow 2 Y) : Subgroup Y) := hQ (Subgroup.mem_zpowers z)
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hzQ
  obtain ⟨s, hs, hsz⟩ : z ∈ Subgroup.map (MulAut.conj h).toMonoidHom (S : Subgroup Y) := hzQ
  have : s = z := by
    have hc := Subgroup.mem_center_iff.1 hz h
    replace hsz : h * s * h⁻¹ = z := hsz
    calc s = h⁻¹ * (h * s * h⁻¹) * h := by group
      _ = h⁻¹ * z * h := by rw [hsz]
      _ = z := by rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  exact this ▸ hs

theorem inv_mul_pow_eq_one {a b : Y} (hab : Commute a b) {r s : ℕ} (ha : a ^ 2 ^ r = 1)
    (hb : b ^ 2 ^ s = 1) : (a⁻¹ * b) ^ 2 ^ max r s = 1 := by
  rw [hab.inv_left.mul_pow, inv_pow]
  have h1 : a ^ 2 ^ max r s = 1 := by
    obtain ⟨k, hk⟩ : 2 ^ r ∣ 2 ^ max r s := pow_dvd_pow 2 (le_max_left r s)
    rw [hk, pow_mul, ha, one_pow]
  have h2 : b ^ 2 ^ max r s = 1 := by
    obtain ⟨k, hk⟩ : 2 ^ s ∣ 2 ^ max r s := pow_dvd_pow 2 (le_max_right r s)
    rw [hk, pow_mul, hb, one_pow]
  rw [h1, h2, inv_one, one_mul]

theorem conj_mem_of_normalizer_map [Finite Y] (S : Sylow 2 Y) {ρ : Y →* X}
    (hker : ρ.ker ≤ Subgroup.center Y) {g : Y}
    (hg : ρ g ∈ Subgroup.normalizer (((S : Subgroup Y).map ρ : Subgroup X) : Set X)) {x : Y}
    (hx : x ∈ S) : g * x * g⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ρ (g * x * g⁻¹) ∈ (S : Subgroup Y).map ρ := by
    have h1 := (Subgroup.mem_set_normalizer_iff.1 hg (ρ x)).1 (Subgroup.mem_map_of_mem ρ hx)
    have h2 : ρ (g * x * g⁻¹) = ρ g * ρ x * (ρ g)⁻¹ := by simp
    rw [h2]
    exact h1
  obtain ⟨s, hs, hse⟩ := hmem
  have hz : s⁻¹ * (g * x * g⁻¹) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hse, inv_mul_cancel]
  have hzc := hker hz
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
  obtain ⟨r, hr⟩ := S.isPGroup' ⟨s, hs⟩
  have hy2 : (g * x * g⁻¹) ^ 2 ^ k = 1 := by
    rw [conj_pow, show x ^ 2 ^ k = 1 from congrArg Subtype.val hk, mul_one, mul_inv_cancel]
  have hs2 : s ^ 2 ^ r = 1 := congrArg Subtype.val hr
  have hcomm : Commute s (g * x * g⁻¹) := by
    rw [show g * x * g⁻¹ = s * (s⁻¹ * (g * x * g⁻¹)) by group]
    exact (Commute.refl s).mul_right (Subgroup.mem_center_iff.1 hzc s)
  have hzS := mem_sylow_of_central S hzc ⟨_, inv_mul_pow_eq_one hcomm hs2 hy2⟩
  have := S.mul_mem hs hzS
  rwa [mul_inv_cancel_left] at this

theorem normalizer_map_le [Finite Y] (S : Sylow 2 Y) {ρ : Y →* X} (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center Y) :
    Subgroup.normalizer (((S : Subgroup Y).map ρ : Subgroup X) : Set X) ≤
      (Subgroup.normalizer ((S : Subgroup Y) : Set Y)).map ρ := by
  intro gb hgb
  obtain ⟨g, rfl⟩ := hρ gb
  refine ⟨g, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_set_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_of_normalizer_map S hker hgb hx, fun hx => ?_⟩
  have hgb' : ρ g⁻¹ ∈ Subgroup.normalizer (((S : Subgroup Y).map ρ : Subgroup X) : Set X) := by
    rw [map_inv]
    exact inv_mem hgb
  have := conj_mem_of_normalizer_map S hker hgb' hx
  simpa [mul_assoc] using this

theorem card_eq_card_center_mul [Finite Y] {ρ : Y →* X} (hker : ρ.ker = Subgroup.center Y)
    {J : Subgroup Y} (hZJ : Subgroup.center Y ≤ J) :
    Nat.card J = Nat.card (Subgroup.center Y) * Nat.card (J.map ρ) := by
  have h := Subgroup.card_ker_mul_card_range (ρ.comp J.subtype)
  have hr : (ρ.comp J.subtype).range = J.map ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : Nat.card (ρ.comp J.subtype).ker = Nat.card (Subgroup.center Y) := by
    have : (ρ.comp J.subtype).ker = (Subgroup.center Y).subgroupOf J := by
      rw [← MonoidHom.comap_ker, hker]
      rfl
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZJ).toEquiv
  rw [hr, hk] at h
  exact h.symm

theorem parabPrime_of_parabCore [Finite Y] {ρ : Y →* X} (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.center Y) (hperfY : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤) {q : ℕ}
    (hcore : ParabCore X q)
    (hZ : ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card (Subgroup.center Y) → p ∣ q ^ 2 - 1)
    {T J : Subgroup Y} (hT : IsSylowTwoOf T ⊤)
    (hNJ : Subgroup.normalizer (T : Set Y) ≤ J) (hJ : J ≠ Subgroup.normalizer (T : Set Y))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → p.Coprime (Nat.card U)) :
    p.Coprime (Nat.card J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
  let S : Sylow 2 Y := hT.2.1.toSylow hidx
  have hSe : (S : Subgroup Y) = T := rfl
  have hZN : Subgroup.center Y ≤ Subgroup.normalizer (T : Set Y) :=
    Subgroup.center_le_normalizer _
  have hZJ : Subgroup.center Y ≤ J := hZN.trans hNJ
  have hkerc : ρ.ker ≤ Subgroup.center Y := hker.le
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hpJ
  have hlift : (∃ V : Subgroup X, V ≤ J.map ρ ∧ ⁅V, V⁆ = V ∧ p ∣ Nat.card V) → False := by
    rintro ⟨V, hVJ, hV, hpV⟩
    obtain ⟨W, hW, hWV, hWm⟩ := exists_perfect_map_eq ρ hkerc hV
      (by rw [MonoidHom.range_eq_top_of_surjective ρ hρ]; exact le_top)
    have hWJ : W ≤ J := by
      intro w hw
      have := Subgroup.mem_comap.1 (hWV hw)
      have h2 : ρ w ∈ J.map ρ := hVJ this
      obtain ⟨j, hj, hjw⟩ := h2
      have : j⁻¹ * w ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hjw, inv_mul_cancel]
      have h3 : w = j * (j⁻¹ * w) := by group
      rw [h3]
      exact J.mul_mem hj (hZJ (hker ▸ this))
    have hpW : p ∣ Nat.card W := by
      refine hpV.trans ?_
      rw [← hWm]
      exact Subgroup.card_map_dvd _ _
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (hperf W hWJ hW) hpW
  have hρS : (S.mapSurjective hρ : Subgroup X) = (T.map ρ) := by
    rw [Sylow.coe_mapSurjective]
    rfl
  have hN1 : Subgroup.normalizer ((S.mapSurjective hρ : Subgroup X) : Set X) ≤ J.map ρ := by
    rw [hρS]
    exact (normalizer_map_le S hρ hkerc).trans (Subgroup.map_mono hNJ)
  have hN2 : J.map ρ ≠ Subgroup.normalizer ((S.mapSurjective hρ : Subgroup X) : Set X) := by
    intro h
    apply hJ
    refine le_antisymm ?_ hNJ
    have h1 : J.map ρ ≤ (Subgroup.normalizer (T : Set Y)).map ρ := by
      rw [h, hρS]
      exact normalizer_map_le S hρ hkerc
    have h2 := Subgroup.comap_mono (f := ρ) h1
    rwa [Subgroup.comap_map_eq_self (hkerc.trans hZN), Subgroup.comap_map_eq_self
      (hkerc.trans hZJ)] at h2
  obtain ⟨hcore1, hcore2⟩ := hcore (S.mapSurjective hρ) (J.map ρ) hN1 hN2 p hp hp5
  rw [card_eq_card_center_mul hker hZJ] at hpJ
  rcases hp.dvd_mul.1 hpJ with h | h
  · exact hlift (hcore1 (hZ p hp hp5 h))
  · rcases hcore2 h with h' | h'
    · have : J = ⊤ := by
        have h2 := congrArg (Subgroup.comap ρ) h'
        rwa [Subgroup.comap_map_eq_self (hkerc.trans hZJ), Subgroup.comap_top] at h2
      subst this
      have := (Nat.Prime.coprime_iff_not_dvd hp).1 (hperf ⊤ le_rfl hperfY)
      exact this (by rwa [card_eq_card_center_mul hker hZJ])
    · exact hlift h'

end CFSG.AGLEmbedding.ParabPrime
