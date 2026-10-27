module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

section Criterion

theorem card_le_card_zpowers_of_isPGroup_two_le_sup {G : Type*} [Group G] [Finite G]
    {E B : Subgroup G} {u : G} (hEodd : Odd (Nat.card E)) (hEu : ∀ e ∈ E, u * e * u⁻¹ ∈ E)
    (hB : IsPGroup 2 B) (hBle : B ≤ E ⊔ zpowers u) : Nat.card B ≤ Nat.card (zpowers u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : zpowers u ≤ normalizer (E : Set G) := by
    refine zpowers_le.2 (mem_normalizer_iff.2 fun h => ⟨hEu h, fun hh => ?_⟩)
    let φ : E → E := fun e => ⟨u * e * u⁻¹, hEu e e.2⟩
    have hφ : Function.Injective φ := fun e₁ e₂ h12 => by
      apply Subtype.ext
      have h' := congrArg Subtype.val h12
      simpa [φ] using h'
    obtain ⟨e, he⟩ := (Finite.injective_iff_surjective.1 hφ) ⟨u * h * u⁻¹, hh⟩
    have heh : (e : G) = h := by
      have h' := congrArg Subtype.val he
      simpa [φ] using h'
    exact heh ▸ e.2
  have key : ∀ b : B, ∃ z : zpowers u, (b : G) * (z : G)⁻¹ ∈ E := by
    intro b
    have hb : (b : G) ∈ ((E ⊔ zpowers u : Subgroup G) : Set G) := hBle b.2
    rw [coe_mul_of_right_le_normalizer_left E (zpowers u) hN] at hb
    obtain ⟨e, he, z, hz, hez⟩ := hb
    exact ⟨⟨z, hz⟩, by rw [← hez, mul_inv_cancel_right]; exact he⟩
  choose f hf using key
  have hdisj : Disjoint B E := by
    obtain ⟨n, hn⟩ := hB.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hEodd)
  refine Nat.card_le_card_of_injective f fun b b' hbb' => ?_
  have h1 : (b : G) * (b' : G)⁻¹ ∈ E := by
    have h' := E.mul_mem (hf b) (E.inv_mem (hf b'))
    rw [hbb'] at h'
    simpa [mul_assoc] using h'
  have h2 : (b : G) * (b' : G)⁻¹ ∈ B := B.mul_mem b.2 (B.inv_mem b'.2)
  exact Subtype.ext (mul_inv_eq_one.1 (disjoint_def.1 hdisj h2 h1))

theorem exists_conj_not_mem_zpowers_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    {p : X}
    (h : ∃ c : Y, c * φ p ^ 2 = φ p ^ 2 * c ∧ (∃ Q : Subgroup Y, IsPGroup 2 Q ∧ φ p ∈ Q ∧ c ∈ Q) ∧
      c * φ p * c⁻¹ ∉ zpowers (φ p)) :
    ∃ c : X, c * p ^ 2 = p ^ 2 * c ∧ (∃ Q : Subgroup X, IsPGroup 2 Q ∧ p ∈ Q ∧ c ∈ Q) ∧
      c * p * c⁻¹ ∉ zpowers p := by
  obtain ⟨c, hc, ⟨Q, hQ, hpQ, hcQ⟩, hnot⟩ := h
  refine ⟨φ.symm c, φ.injective ?_, ⟨Q.map φ.symm.toMonoidHom, hQ.map _, ⟨φ p, hpQ, by simp⟩,
    ⟨c, hcQ, rfl⟩⟩, fun hmem => hnot ?_⟩
  · simpa using hc
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    have h' := congrArg φ hk
    simpa using h'

theorem hypothesisOneStar_of_odd_card_outer {Y : Type*} [Group Y] [Finite Y]
    (hZ : center Y = ⊥) (hOut : Odd (Nat.card (Outer Y)))
    (hY : ∀ p : Y, orderOf p = 4 → ∃ c : Y, c * p ^ 2 = p ^ 2 * c ∧
      (∃ Q : Subgroup Y, IsPGroup 2 Q ∧ p ∈ Q ∧ c ∈ Q) ∧ c * p * c⁻¹ ∉ zpowers p) :
    HypothesisOneStar Y := by
  intro x u hx hux E _ hEodd hEu _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ center Y := mem_center_iff.2 fun y => by
      have h' := congrArg (fun α : MulAut Y => α y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h'
      calc y * g = g * y * g⁻¹ * g := by rw [h']
        _ = g * y := by group
    rwa [hZ, mem_bot] at hgZ
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hu4 : orderOf u = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := u) (by rwa [pow_one, hux])
      (by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hux, hx2])
    simpa using h
  have huinner : u ∈ inner Y :=
    CFSG.ProperTwoGeneratedCore.HighRankPair.le_inner_of_isPGroup_two hOut (zpowers u)
      (IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu4]; norm_num)) (mem_zpowers u)
  obtain ⟨p, rfl⟩ := huinner
  have hp4 : orderOf p = 4 := by rw [← orderOf_injective _ hinj p]; exact hu4
  obtain ⟨c, hcp, ⟨Q, hQ, hpQ, hcQ⟩, hnot⟩ := hY p hp4
  refine ⟨c, ?_, fun hmem => hnot ?_⟩
  · rw [← hux, ← map_pow, ← map_mul, ← map_mul, hcp]
  · set H := E ⊔ zpowers (MulAut.conj p)
    set B := Q.map (MulAut.conj : Y →* MulAut Y) ⊓ H
    have hBle : B ≤ H := inf_le_right
    have hcard : Nat.card B ≤ Nat.card (zpowers (MulAut.conj p)) :=
      card_le_card_zpowers_of_isPGroup_two_le_sup hEodd hEu (hQ.map _).to_inf_left hBle
    have hle : zpowers (MulAut.conj p) ≤ B :=
      zpowers_le.2 ⟨mem_map_of_mem _ hpQ, le_sup_right (a := E) (mem_zpowers _)⟩
    have hBeq : zpowers (MulAut.conj p) = B := eq_of_le_of_card_ge hle hcard
    have hw : MulAut.conj (c * p * c⁻¹) ∈ B := by
      refine ⟨mem_map_of_mem _ (Q.mul_mem (Q.mul_mem hcQ hpQ) (Q.inv_mem hcQ)), ?_⟩
      rwa [map_mul, map_mul, map_inv]
    rw [← hBeq] at hw
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hw
    rw [← map_zpow] at hk
    exact mem_zpowers_iff.2 ⟨k, hinj hk⟩

end Criterion

section Suzuki

variable {a : ℕ} {K : Type} [Field K]

theorem exists_pow_two_pow_add_self_ne [Finite K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ s : K, s ^ 2 ^ (a + 1) + s ≠ 0 ∧ s ^ 2 ^ (a + 1) + s ≠ 1 := by
  obtain ⟨-, hadd, hθθ⟩ := suzuki_frob_data a hK
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  by_contra h
  have h01 : ∀ s : K, s = 0 ∨ s = 1 := fun s => by
    have hfix : (s ^ 2 ^ (a + 1) + s) ^ 2 ^ (a + 1) = s ^ 2 ^ (a + 1) + s := by
      by_cases h0 : s ^ 2 ^ (a + 1) + s = 0
      · rw [h0, zero_pow hθ0]
      · have h1 : s ^ 2 ^ (a + 1) + s = 1 := by
          by_contra h1
          exact h ⟨s, h0, h1⟩
        rw [h1, one_pow]
    rw [hadd, hθθ] at hfix
    have hss : s * (s - 1) = 0 := by linear_combination hfix
    rcases mul_eq_zero.1 hss with h' | h'
    · exact Or.inl h'
    · exact Or.inr (sub_eq_zero.1 h')
  have hsurj : Function.Surjective (![0, 1] : Fin 2 → K) := fun s => by
    rcases h01 s with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  have h2 := Nat.card_le_card_of_surjective _ hsurj
  rw [hK, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
  have h8 : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem exists_conj_not_mem_zpowers_of_mem_suzukiU (ha : 1 ≤ a)
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : suzukiGroup a K} (hpU : p ∈ suzukiU a K)
    (hp : orderOf p = 4) :
    ∃ c ∈ suzukiU a K, c * p ^ 2 = p ^ 2 * c ∧ c * p * c⁻¹ ∉ zpowers p := by
  classical
  have := finite_suzukiGroup hK
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hpU
  obtain ⟨h2, -, -⟩ := suzuki_frob_data a hK
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hsq : suzukiSElt a K u v ^ 2 = suzukiSElt a K 0 (u ^ (2 ^ (a + 1) + 1)) := by
    rw [sq, suzukiSElt_mul hK, suzukiSElt_inj]
    constructor
    · linear_combination u * h2
    · rw [pow_succ]
      linear_combination v * h2
  have hu : u ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero _), suzukiSElt_zero_zero hK] at hsq
    have h4 := orderOf_dvd_of_pow_eq_one hsq
    rw [hp] at h4
    norm_num at h4
  obtain ⟨s, hs0, hs1⟩ := exists_pow_two_pow_add_self_ne ha hK
  obtain ⟨δ, hδ⟩ : ∃ δ : K, δ = (u * s) ^ 2 ^ (a + 1) * u + u ^ 2 ^ (a + 1) * (u * s) := ⟨_, rfl⟩
  have hδ' : δ = u ^ (2 ^ (a + 1) + 1) * (s ^ 2 ^ (a + 1) + s) := by
    rw [hδ, mul_pow, pow_succ]
    ring
  refine ⟨suzukiSElt a K (u * s) 0, suzukiSElt_mem_suzukiU a K _ 0, ?_, ?_⟩
  · rw [hsq]
    exact (suzukiSElt_zero_commute hK _ _ 0).symm
  have hconj : suzukiSElt a K (u * s) 0 * suzukiSElt a K u v * (suzukiSElt a K (u * s) 0)⁻¹ =
      suzukiSElt a K u (v + δ) := by
    rw [mul_inv_eq_iff_eq_mul, suzukiSElt_mul hK, suzukiSElt_mul hK, suzukiSElt_inj]
    constructor
    · ring
    · linear_combination (-(u ^ 2 ^ (a + 1) * (u * s))) * h2 - hδ
  rw [hconj]
  intro hmem
  rw [mem_zpowers_iff_mem_range_orderOf, hp, Finset.mem_image] at hmem
  obtain ⟨k, hk, hkeq⟩ := hmem
  have hu1 : u ^ (2 ^ (a + 1) + 1) ≠ 0 := pow_ne_zero _ hu
  have hδ01 : δ = 0 ∨ δ = u ^ (2 ^ (a + 1) + 1) := by
    rw [Finset.mem_range] at hk
    interval_cases k
    · rw [pow_zero, ← suzukiSElt_zero_zero hK, suzukiSElt_inj] at hkeq
      exact absurd hkeq.1.symm hu
    · rw [pow_one, suzukiSElt_inj] at hkeq
      left
      linear_combination -hkeq.2
    · rw [hsq, suzukiSElt_inj] at hkeq
      exact absurd hkeq.1.symm hu
    · rw [pow_succ, hsq, suzukiSElt_mul hK, suzukiSElt_inj] at hkeq
      right
      rw [zero_pow hθ0, zero_mul, add_zero] at hkeq
      linear_combination -hkeq.2
  rcases hδ01 with h | h
  · rw [hδ'] at h
    exact hs0 ((mul_eq_zero.1 h).resolve_left hu1)
  · rw [hδ'] at h
    exact hs1 ((mul_eq_left₀ hu1).1 h)

theorem exists_conj_not_mem_zpowers_suzukiGroup (ha : 1 ≤ a)
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : suzukiGroup a K} (hp : orderOf p = 4) :
    ∃ c : suzukiGroup a K, c * p ^ 2 = p ^ 2 * c ∧
      (∃ Q : Subgroup (suzukiGroup a K), IsPGroup 2 Q ∧ p ∈ Q ∧ c ∈ Q) ∧
      c * p * c⁻¹ ∉ zpowers p := by
  have := finite_suzukiGroup hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P₀ := Sylow.ofCard (suzukiU a K) (CFSG.RankThree.card_suzukiU_eq hK)
  obtain ⟨P, hP⟩ := (IsPGroup.of_card (p := 2) (n := 2) (G := zpowers p)
    (by rw [Nat.card_zpowers, hp]; norm_num)).exists_le_sylow
  have hpP : p ∈ P := hP (mem_zpowers p)
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (suzukiGroup a K) P₀ P
  have hp₀U : g⁻¹ * p * g ∈ suzukiU a K := (CFSG.RankThree.mem_smul_sylow_iff P₀ g p).1 hpP
  have hφp : MulAut.conj g⁻¹ p = g⁻¹ * p * g := by rw [MulAut.conj_apply, inv_inv]
  have hp₀ : orderOf (g⁻¹ * p * g) = 4 := by
    rw [← hφp, MulEquiv.orderOf_eq, hp]
  obtain ⟨c₀, hc₀U, hc₀, hnot⟩ := exists_conj_not_mem_zpowers_of_mem_suzukiU ha hK hp₀U hp₀
  refine exists_conj_not_mem_zpowers_of_mulEquiv (MulAut.conj g⁻¹) ?_
  rw [hφp]
  exact ⟨c₀, hc₀, ⟨suzukiU a K, P₀.isPGroup', hp₀U, hc₀U⟩, hnot⟩

theorem hypothesisOneStar_of_mulEquiv_suzukiGroup {Y : Type*}
    [Group Y] (ha : 1 ≤ a) [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : Y ≃* suzukiGroup a K) : HypothesisOneStar Y := by
  have := finite_suzukiGroup hK
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hZ : center (suzukiGroup a K) = ⊥ := by
    obtain ⟨-, -, hsimple⟩ := suzuki_simple ha hK
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (suzukiGroup a K)) with h | h
    · exact h
    · have h1 := (suzuki_perfect ha hK).1
      rw [(commutator_eq_bot_iff_center_eq_top _).2 h] at h1
      exact absurd h1 bot_ne_top
  refine hypothesisOneStar_of_odd_card_outer ?_ ?_ fun p hp => ?_
  · rw [eq_bot_iff]
    intro z hz
    have hez : e z ∈ center (suzukiGroup a K) := by
      rw [mem_center_iff] at hz ⊢
      intro y
      have h' := congrArg e (hz (e.symm y))
      simpa using h'
    rw [hZ, mem_bot] at hez
    rw [mem_bot]
    exact e.map_eq_one_iff.1 hez
  · rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.ProperTwoGeneratedCore.HighRankPair.odd_card_outer_suzukiGroup ha hK
  · exact exists_conj_not_mem_zpowers_of_mulEquiv e
      (exists_conj_not_mem_zpowers_suzukiGroup ha hK (by rw [MulEquiv.orderOf_eq]; exact hp))

end Suzuki

theorem hypothesisOneStar_of_suzukiModel {Y : Type} [Group Y]
    {p f : ℕ} (h : SuzukiModel Y p f) : HypothesisOneStar Y := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  exact hypothesisOneStar_of_mulEquiv_suzukiGroup ha hK e

theorem hypothesisOneStar_of_lieModel_twistedB2 {Y : Type}
    [Group Y] {p f : ℕ} (h : LieModel Y .twistedB2 0 p f) : HypothesisOneStar Y := by
  rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact hypothesisOneStar_of_suzukiModel h

end CFSG.SeitzReduction.RankOne
