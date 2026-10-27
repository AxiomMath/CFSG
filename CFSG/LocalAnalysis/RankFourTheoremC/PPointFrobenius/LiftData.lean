module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.HypDefs
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

private theorem ld_inj {J P : Type*} [Group J] [Group P] {p : ℕ} [hp : Fact p.Prime]
    (π : J →* P) (hpk : ¬ p ∣ Nat.card π.ker) (U : Subgroup J) (hU : IsPGroup p U) :
    ∀ u ∈ U, π u = 1 → u = 1 := by
  intro u hu h1
  have hk : u ∈ π.ker := h1
  obtain ⟨n, hn⟩ := hU ⟨u, hu⟩
  have hn' : u ^ (p ^ n) = 1 := congrArg Subtype.val hn
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one hn')
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simpa using hi
  · exact absurd ((hi ▸ dvd_pow_self p hi0.ne').trans (Subgroup.orderOf_dvd_natCard _ hk)) hpk

private theorem ld_card_comap {J P : Type*} [Group J] [Finite J] [Group P]
    (π : J →* P) (hπ : Function.Surjective π) (U₀ : Subgroup P) :
    Nat.card (U₀.comap π) = Nat.card π.ker * Nat.card U₀ := by
  have : Finite P := Finite.of_surjective π hπ
  have h1 := Subgroup.card_mul_index (U₀.comap π)
  have h2 := Subgroup.card_mul_index U₀
  have h3 := Subgroup.card_ker_mul_card_of_surjective hπ
  have h4 := Subgroup.index_comap_of_surjective (H := U₀) hπ
  rw [h4] at h1
  have hpos : 0 < U₀.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, ← h3, ← h2]
  ring

private theorem ld_fact {J P : Type*} [Group J] [Finite J] [Group P] {p : ℕ} [hp : Fact p.Prime]
    (π : J →* P) (hπ : Function.Surjective π) (hpk : ¬ p ∣ Nat.card π.ker)
    (U₀ : Subgroup P) {n : ℕ} (hcard : Nat.card U₀ = p ^ n) :
    (Nat.card (U₀.comap π)).factorization p = n := by
  rw [ld_card_comap π hπ U₀, hcard]
  have hK : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
  rw [Nat.factorization_mul hK (pow_ne_zero n hp.out.ne_zero), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hpk, hp.out.factorization_pow]
  simp

private theorem ld_exists_sylow {J P : Type*} [Group J] [Finite J] [Group P] {p : ℕ}
    [Fact p.Prime] (π : J →* P) (hπ : Function.Surjective π) (hpk : ¬ p ∣ Nat.card π.ker)
    (U₀ : Subgroup P) {n : ℕ} (hcard : Nat.card U₀ = p ^ n) :
    ∃ U : Subgroup J, U ≤ U₀.comap π ∧ Nat.card U = p ^ n := by
  obtain ⟨S⟩ : Nonempty (Sylow p (U₀.comap π)) := inferInstance
  refine ⟨(S : Subgroup (U₀.comap π)).map (U₀.comap π).subtype, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective (U₀.comap π).subtype_injective, S.card_eq_multiplicity,
      ld_fact π hπ hpk U₀ hcard]

open scoped Pointwise in
private theorem ld_sylow_conj {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (A B : Subgroup G) (hA : Nat.card A = p ^ (Nat.card G).factorization p)
    (hB : Nat.card B = p ^ (Nat.card G).factorization p) :
    ∃ w : G, ∀ x : G, x ∈ A ↔ w * x * w⁻¹ ∈ B := by
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq G (Sylow.ofCard A hA) (Sylow.ofCard B hB)
  refine ⟨w, fun x => ?_⟩
  have h2 : MulAut.conj w • A = B := congrArg (fun S : Sylow p G => (S : Subgroup G)) hw
  rw [← h2]
  have := (Subgroup.smul_mem_pointwise_smul_iff (a := MulAut.conj w) (S := A) (x := x)).symm
  simpa [MulAut.smul_def, MulAut.conj_apply] using this

private theorem ld_sylow_conj' {J : Type*} [Group J] [Finite J] {p : ℕ} [Fact p.Prime]
    (W A B : Subgroup J) (hAW : A ≤ W) (hBW : B ≤ W)
    (hA : Nat.card A = p ^ (Nat.card W).factorization p)
    (hB : Nat.card B = p ^ (Nat.card W).factorization p) :
    ∃ w ∈ W, ∀ x : J, x ∈ A ↔ w * x * w⁻¹ ∈ B := by
  have hA' : Nat.card (A.subgroupOf W) = p ^ (Nat.card W).factorization p := by
    rw [← hA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv
  have hB' : Nat.card (B.subgroupOf W) = p ^ (Nat.card W).factorization p := by
    rw [← hB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBW).toEquiv
  obtain ⟨w, hw⟩ := ld_sylow_conj (A.subgroupOf W) (B.subgroupOf W) hA' hB'
  refine ⟨w, w.2, fun x => ?_⟩
  by_cases hx : x ∈ W
  · have := hw ⟨x, hx⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · refine ⟨fun h => absurd (hAW h) hx, fun h => absurd ?_ hx⟩
    have h' := hBW h
    have := W.mul_mem (W.mul_mem (W.inv_mem w.2) h') w.2
    simpa [mul_assoc] using this

private theorem ld_lift {J P : Type*} [Group J] [Finite J] [Group P] {p : ℕ} [Fact p.Prime]
    (π : J →* P) (hπ : Function.Surjective π) (U₀ : Subgroup P)
    (hcomm : ∀ u ∈ U₀, ∀ v ∈ U₀, u * v = v * u)
    (U : Subgroup J) (hUW : U ≤ U₀.comap π)
    (hUcard : Nat.card U = p ^ (Nat.card (U₀.comap π)).factorization p)
    (g₀ : P) (hg₀ : g₀ ∈ Subgroup.normalizer (U₀ : Set P)) :
    ∃ g : J, g ∈ Subgroup.normalizer (U : Set J) ∧
      ∀ u ∈ U, π (g * u * g⁻¹) = g₀ * π u * g₀⁻¹ := by
  obtain ⟨t, ht⟩ := hπ g₀
  let V : Subgroup J := U.map (MulAut.conj t).toMonoidHom
  have hV : ∀ y, y ∈ V ↔ t⁻¹ * y * t ∈ U := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hx
    · intro hy
      exact ⟨t⁻¹ * y * t, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hVcard : Nat.card V = Nat.card U :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hVW : V ≤ U₀.comap π := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : π x ∈ U₀ := hUW hx
    have h2 := (Subgroup.mem_set_normalizer_iff.1 hg₀ (π x)).1 h1
    rw [Subgroup.mem_comap]
    simpa [MulAut.conj_apply, ht] using h2
  obtain ⟨w, hwW, hw⟩ := ld_sylow_conj' (U₀.comap π) V U hVW hUW (hVcard.trans hUcard) hUcard
  refine ⟨w * t, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    have e1 := hw (t * h * t⁻¹)
    have e2 := hV (t * h * t⁻¹)
    have e3 : t⁻¹ * (t * h * t⁻¹) * t = h := by group
    rw [e3] at e2
    have e4 : w * t * h * (w * t)⁻¹ = w * (t * h * t⁻¹) * w⁻¹ := by group
    rw [e4, ← e1, e2]
  · intro u hu
    have hπu : π u ∈ U₀ := hUW hu
    have hw' : π w ∈ U₀ := hwW
    have hc : g₀ * π u * g₀⁻¹ ∈ U₀ := (Subgroup.mem_set_normalizer_iff.1 hg₀ (π u)).1 hπu
    have hcw := hcomm _ hw' _ hc
    calc π (w * t * u * (w * t)⁻¹) = π w * (g₀ * π u * g₀⁻¹) * (π w)⁻¹ := by
          simp [mul_assoc, ht]
      _ = g₀ * π u * g₀⁻¹ := by rw [hcw]; group

theorem exists_hyperplane_data {J P : Type} [Group J] [Finite J] [Group P] {p : ℕ} [Fact p.Prime]
    {n : ℕ} (π : J →* P) (hπ : Function.Surjective π) (hpk : ¬ p ∣ Nat.card π.ker)
    (U₀ : Subgroup P) (σ₀ : P) (hcard : Nat.card U₀ = p ^ n) (hexp : ∀ u ∈ U₀, u ^ p = 1)
    (hcomm : ∀ u ∈ U₀, ∀ v ∈ U₀, u * v = v * u) (hσ : MovesHyperplanes p U₀ σ₀) :
    ∃ (U : Subgroup J) (σ : J), Nat.card U = p ^ n ∧ (∀ u ∈ U, u ^ p = 1) ∧
      (∀ u ∈ U, ∀ v ∈ U, u * v = v * u) ∧ (∀ u ∈ U, π u = 1 → u = 1) ∧
      MovesHyperplanes p U σ := by
  obtain ⟨U, hUW, hUcard⟩ := ld_exists_sylow π hπ hpk U₀ hcard
  have hker : ∀ u ∈ U, π u = 1 → u = 1 := ld_inj π hpk U (IsPGroup.of_card hUcard)
  have hinj : ∀ a ∈ U, ∀ b ∈ U, π a = π b → a = b := by
    intro a ha b hb hab
    exact mul_inv_eq_one.1 (hker _ (U.mul_mem ha (U.inv_mem hb)) (by simp [hab]))
  have hUcard' : Nat.card U = p ^ (Nat.card (U₀.comap π)).factorization p := by
    rw [hUcard, ld_fact π hπ hpk U₀ hcard]
  obtain ⟨σ, hσN, hσπ⟩ := ld_lift π hπ U₀ hcomm U hUW hUcard' σ₀ hσ.1
  have hpow : ∀ k : ℕ, ∀ u ∈ U, σ ^ k * u * (σ ^ k)⁻¹ ∈ U ∧
      π (σ ^ k * u * (σ ^ k)⁻¹) = σ₀ ^ k * π u * (σ₀ ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u hu; simp [hu]
    | succ k ih =>
      intro u hu
      obtain ⟨hv, hπv⟩ := ih u hu
      have hsucc : σ ^ (k + 1) * u * (σ ^ (k + 1))⁻¹ = σ * (σ ^ k * u * (σ ^ k)⁻¹) * σ⁻¹ := by
        simp only [pow_succ', mul_inv_rev, mul_assoc]
      rw [hsucc]
      refine ⟨(Subgroup.mem_normalizer_iff.1 hσN _).1 hv, ?_⟩
      rw [hσπ _ hv, hπv, pow_succ' σ₀ k]
      simp only [mul_inv_rev, mul_assoc]
  have hmapcard : ∀ H : Subgroup J, H ≤ U → Nat.card (H.map π) = Nat.card H := by
    intro H hHU
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun h : H => (⟨π h, Subgroup.mem_map_of_mem π h.2⟩ : H.map π)) ⟨?_, ?_⟩)
    · intro a b hab
      exact Subtype.ext (hinj a (hHU a.2) b (hHU b.2) (congrArg Subtype.val hab))
    · rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨U, σ, hUcard, ?_, ?_, hker, ⟨hσN, ?_⟩⟩
  · intro u hu
    refine hinj _ (U.pow_mem hu p) _ U.one_mem ?_
    rw [map_pow, map_one]
    exact hexp _ (hUW hu)
  · intro u hu v hv
    refine hinj _ (U.mul_mem hu hv) _ (U.mul_mem hv hu) ?_
    rw [map_mul, map_mul]
    exact hcomm _ (hUW hu) _ (hUW hv)
  · intro j hj1 hj3 H hHU hHcard
    have hHle : H.map π ≤ U₀ := Subgroup.map_le_iff_le_comap.2 (hHU.trans hUW)
    have hH' : Nat.card U₀ = p * Nat.card (H.map π) := by
      rw [hmapcard H hHU, ← hHcard, hcard, hUcard]
    obtain ⟨_, ⟨h, hh, rfl⟩, hh'⟩ := hσ.2 j hj1 hj3 (H.map π) hHle hH'
    refine ⟨h, hh, fun hmem => hh' ?_⟩
    have := Subgroup.mem_map_of_mem π hmem
    rwa [(hpow j h (hHU hh)).2] at this

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
