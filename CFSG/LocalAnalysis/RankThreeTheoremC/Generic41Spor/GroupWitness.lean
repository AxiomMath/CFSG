module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

@[expose] def TwoWitness {K : Type} [Group K] (u : K) : Prop :=
  ∃ V : Subgroup K, IsPGroup 2 V ∧ u ∈ normalizer (V : Set K) ∧ ∃ v ∈ V, u * v ≠ v * u

theorem TwoWitness.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') {u : K}
    (h : TwoWitness u) : TwoWitness (e u) := by
  obtain ⟨V, hV2, hN, v, hv, hne⟩ := h
  refine ⟨V.map e.toMonoidHom, hV2.map e.toMonoidHom, ?_, e v, ⟨v, hv, rfl⟩, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨u, hN, rfl⟩
  · intro h
    apply hne
    apply e.injective
    simpa using h

theorem TwoWitness.conj {K : Type} [Group K] {u : K} (h : TwoWitness u) (g : K) :
    TwoWitness (g * u * g⁻¹) := by
  have := h.of_mulEquiv (MulAut.conj g)
  simpa using this

theorem exists_conj_mem_sylow_of_isPGroup {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {x : G} (hx : IsPGroup p (Subgroup.zpowers x)) :
    ∃ g : G, g * x * g⁻¹ ∈ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  have hmem : x ∈ ((g • P : Sylow p G) : Subgroup G) := hQ (Subgroup.mem_zpowers x)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨y, hy, hyx⟩ := hmem
  refine ⟨g⁻¹, ?_⟩
  have : g⁻¹ * x * g⁻¹⁻¹ = y := by
    rw [← hyx]
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact hy

theorem isPGroup_zpowers_of_orderOf {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {x : G}
    (hx : orderOf x = p) : IsPGroup p (Subgroup.zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])

theorem TwoWitness.of_orbit {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (htrans : NormalizerTransitive p K) {u₀ u : K} (hu₀ : orderOf u₀ = p) (hu : orderOf u = p)
    (h₀ : TwoWitness u₀) : TwoWitness u := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := (isPGroup_zpowers_of_orderOf hu).exists_le_sylow
  have huS : u ∈ (S : Subgroup K) := hS (Subgroup.mem_zpowers u)
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_of_isPGroup S (isPGroup_zpowers_of_orderOf hu₀)
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    exact hp.one_lt.ne hu
  have hg1 : g * u₀ * g⁻¹ ≠ 1 := by
    intro h
    have : u₀ = 1 := by
      have h' : g * u₀ * g⁻¹ * g = g := by rw [h]; simp
      simpa using h'
    rw [this, orderOf_one] at hu₀
    exact hp.one_lt.ne hu₀
  obtain ⟨n, -, hn⟩ := htrans S (g * u₀ * g⁻¹) hg hg1 u huS hu1
  have : u = (n * g) * u₀ * (n * g)⁻¹ := by
    rw [← hn]
    group
  rw [this]
  exact h₀.conj (n * g)

theorem eq_zpowers_of_card_prime {X : Type} [Group X] {p : ℕ} (hp : p.Prime) {U : Subgroup X}
    (hU : Nat.card U = p) {u : X} (hu : u ∈ U) (hu1 : u ≠ 1) : U = Subgroup.zpowers u := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : Subgroup.zpowers u ≤ U := (Subgroup.zpowers_le).2 hu
  have hdvd : orderOf u ∣ p := by
    rw [← hU, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  have hord : orderOf u = p := by
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h
  haveI : Finite U := Nat.finite_of_card_ne_zero (by rw [hU]; exact hp.ne_zero)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, hU])).symm

theorem kwitness_to_x {X : Type} [Group X] (K : Subgroup X) {u : X} (hu : u ∈ K)
    (h : TwoWitness (⟨u, hu⟩ : K)) {U₀ : Subgroup X} (hU₀ : U₀ = Subgroup.zpowers u) :
    ∃ V : Subgroup X, V ≤ K ∧ IsPGroup 2 V ∧ U₀ ≤ normalizer (V : Set X) ∧
      ∃ v ∈ V, ∃ w ∈ U₀, w * v ≠ v * w := by
  obtain ⟨V, hV2, hN, v, hv, hne⟩ := h
  refine ⟨V.map K.subtype, ?_, hV2.map K.subtype, ?_, (v : X), ⟨v, hv, rfl⟩, u, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rw [hU₀, Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro y
    have hN' := Subgroup.mem_normalizer_iff.mp hN
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨u, hu⟩ * k * ⟨u, hu⟩⁻¹, (hN' k).mp hk, rfl⟩
    · rintro ⟨k', hk', hk'y⟩
      have hk'y' : (k' : X) = u * y * u⁻¹ := hk'y
      have hyK : y ∈ K := by
        have : y = u⁻¹ * (k' : X) * u := by rw [hk'y']; group
        rw [this]
        exact mul_mem (mul_mem (inv_mem hu) k'.2) hu
      refine ⟨⟨y, hyK⟩, (hN' ⟨y, hyK⟩).mpr ?_, rfl⟩
      have : (⟨u, hu⟩ * ⟨y, hyK⟩ * ⟨u, hu⟩⁻¹ : K) = k' := Subtype.ext (by simpa using hk'y'.symm)
      rw [this]
      exact hk'
  · rw [hU₀]
    exact Subgroup.mem_zpowers u
  · intro h
    apply hne
    apply Subtype.ext
    exact h

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
