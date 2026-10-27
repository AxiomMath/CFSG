module

public import CFSG.ClassicalInvolution.Q3.TL3T24

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

variable {G : Type} [Group G]

section Count

variable [Finite G]

theorem card_le_two_mul_of_mem_or {K C : Subgroup G} {k₀ : G}
    (h : ∀ k ∈ K, k ∈ C ∨ k₀⁻¹ * k ∈ C) : Nat.card K ≤ 2 * Nat.card C := by
  classical
  let f : ↥K → Bool × ↥C := fun k =>
    if hk : (k : G) ∈ C then (false, ⟨k, hk⟩) else (true, ⟨k₀⁻¹ * k, (h k k.2).resolve_left hk⟩)
  have hf : Function.Injective f := by
    intro a b hab
    by_cases ha : (a : G) ∈ C <;> by_cases hb : (b : G) ∈ C <;>
      simp only [f, ha, hb, dite_true, dite_false, Prod.mk.injEq, Subtype.mk.injEq,
        Bool.false_eq_true, Bool.true_eq_false, false_and, true_and] at hab
    · exact Subtype.ext hab
    · exact Subtype.ext (mul_left_cancel hab)
  calc Nat.card K ≤ Nat.card (Bool × ↥C) := Nat.card_le_card_of_injective f hf
    _ = 2 * Nat.card C := by rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
        Fintype.card_bool]

theorem card_le_two_mul_centralizer {K : Subgroup G} {y z : G} (hz : ∀ k ∈ K, k * z = z * k)
    (hzz : z * z = 1) (h : ∀ k ∈ K, k * y * k⁻¹ = y ∨ k * y * k⁻¹ = z * y) :
    Nat.card K ≤ 2 * Nat.card ↥(K ⊓ Subgroup.centralizer {y}) := by
  have hmem : ∀ k ∈ K, k * y * k⁻¹ = y → k ∈ K ⊓ Subgroup.centralizer {y} := by
    intro k hk hky
    refine ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc k * y = k * y * k⁻¹ * k := by group
      _ = y * k := by rw [hky]
  by_cases hall : ∀ k ∈ K, k * y * k⁻¹ = y
  · exact card_le_two_mul_of_mem_or (k₀ := 1) fun k hk => Or.inl (hmem k hk (hall k hk))
  push Not at hall
  obtain ⟨k₀, hk₀, hk₀y⟩ := hall
  have hk₀' : k₀ * y * k₀⁻¹ = z * y := (h k₀ hk₀).resolve_left hk₀y
  refine card_le_two_mul_of_mem_or (k₀ := k₀) fun k hk => ?_
  rcases h k hk with hky | hky
  · exact Or.inl (hmem k hk hky)
  · right
    refine hmem _ (K.mul_mem (K.inv_mem hk₀) hk) ?_
    have h1 : k₀⁻¹ * z = z * k₀⁻¹ := by
      have := hz k₀ hk₀
      calc k₀⁻¹ * z = k₀⁻¹ * (z * k₀) * k₀⁻¹ := by group
        _ = k₀⁻¹ * (k₀ * z) * k₀⁻¹ := by rw [this]
        _ = z * k₀⁻¹ := by group
    have h2 : k₀⁻¹ * y * k₀ = z * y := by
      have e : y = k₀⁻¹ * (z * y) * k₀ := by rw [← hk₀']; group
      calc k₀⁻¹ * y * k₀ = z * z * (k₀⁻¹ * y * k₀) := by rw [hzz, one_mul]
        _ = z * (k₀⁻¹ * z * (y * k₀)) := by rw [h1]; group
        _ = z * (k₀⁻¹ * (z * y) * k₀) := by group
        _ = z * y := by rw [← e]
    calc k₀⁻¹ * k * y * (k₀⁻¹ * k)⁻¹ = k₀⁻¹ * (k * y * k⁻¹) * k₀ := by group
      _ = k₀⁻¹ * z * (y * k₀) := by rw [hky]; group
      _ = z * (k₀⁻¹ * y * k₀) := by rw [h1]; group
      _ = y := by rw [h2, ← mul_assoc, hzz, one_mul]

end Count

section Q8

variable [Finite G]

theorem mem_or_of_card_eq_two_mul {K C : Subgroup G} (hCK : C ≤ K)
    (hcard : Nat.card K = 2 * Nat.card C) {x₀ x : G} (hx₀ : x₀ ∈ K) (hx₀C : x₀ ∉ C) (hx : x ∈ K) :
    x ∈ C ∨ x₀⁻¹ * x ∈ C := by
  have hidx : (C.subgroupOf K).index = 2 := by
    have h1 := Subgroup.card_mul_index (C.subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv, hcard] at h1
    have hC0 : 0 < Nat.card C := Nat.card_pos
    nlinarith
  by_cases hxC : x ∈ C
  · exact Or.inl hxC
  right
  have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨x₀, hx₀⟩ : ↥K)⁻¹)
    (b := (⟨x, hx⟩ : ↥K))).mpr
  have h' : (⟨x₀, hx₀⟩ : ↥K)⁻¹ * ⟨x, hx⟩ ∈ C.subgroupOf K := by
    apply h
    constructor
    · intro h0
      exact absurd (by simpa [Subgroup.mem_subgroupOf] using h0) hx₀C
    · intro h0
      exact absurd (by simpa [Subgroup.mem_subgroupOf] using h0) hxC
  simpa [Subgroup.mem_subgroupOf] using h'

omit [Finite G] in
theorem sq_eq_of_quat8 {K : Subgroup G} (hq : IsQuatSub K) (h8 : Nat.card K = 8) {z : G}
    (hz : IsUniqueInvolution K z) {k : G} (hk : k ∈ K) (hk1 : k ≠ 1) (hkz : k ≠ z) :
    k * k = z := by
  have h4 : k ^ 4 = 1 := by
    have := Sec6Gen.IsQuatSub.pow_half_eq_one hq hk
    rwa [h8] at this
  have hkk : (k * k) * (k * k) = 1 := by
    rw [← h4, pow_succ, pow_succ, pow_succ, pow_one]
    simp only [mul_assoc]
  rcases hz.unique _ (K.mul_mem hk hk) hkk with h | h
  · exfalso
    rcases hz.unique k hk h with h' | h'
    · exact hk1 h'
    · exact hkz h'
  · exact h

omit [Finite G] in
theorem orderOf_eq_four_of_sq {k z : G} (hkk : k * k = z) (hz1 : z ≠ 1) (hzz : z * z = 1) :
    orderOf k = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (x := k) (p := 2) (n := 1) ?_ ?_
  · simpa using h
  · rw [pow_one, pow_two, hkk]
    exact hz1
  · have h2 : k ^ 2 = z := by rw [pow_two, hkk]
    rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 from rfl, pow_mul, h2, pow_two, hzz]

theorem le_ker_of_three {A : Type*} [CommGroup A] (ψ : G →* A) {K : Subgroup G}
    (hq : IsQuatSub K) (h8 : Nat.card K = 8) {z : G} (hz : IsUniqueInvolution K z)
    {y : G} (hyK : y ∈ Subgroup.normalizer (K : Set G))
    (hy3 : ∀ k ∈ K, y ^ 3 * k = k * y ^ 3) (hyc : ¬ ∀ k ∈ K, y * k = k * y) :
    K ≤ ψ.ker := by
  classical
  have hα : ∀ k ∈ K, y * k * y⁻¹ ∈ K := fun k hk => (Subgroup.mem_normalizer_iff.mp hyK k).mp hk
  have hα3 : ∀ k ∈ K, y * (y * (y * k * y⁻¹) * y⁻¹) * y⁻¹ = k := by
    intro k hk
    have e3 : y ^ 3 = y * y * y := by rw [pow_three, mul_assoc]
    calc y * (y * (y * k * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * k * (y * y * y)⁻¹ := by group
      _ = k := by rw [← e3, hy3 k hk, mul_inv_cancel_right]
  have hψα : ∀ k, ψ (y * k * y⁻¹) = ψ k := by
    intro k
    rw [map_mul, map_mul, map_inv, mul_comm (ψ y), mul_assoc, mul_inv_cancel, mul_one]
  have hyz : y * z * y⁻¹ = z := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hyK)
  have hzp : ∀ k : G, k * k = z → ∀ m ∈ Subgroup.zpowers k, m = 1 ∨ m = k ∨ m = z ∨ m = k⁻¹ := by
    intro k hkk m hm
    have ho := orderOf_eq_four_of_sq hkk hz.ne_one hz.sq
    rw [mem_zpowers_iff_mem_range_orderOf, ho] at hm
    simp only [Finset.mem_image, Finset.mem_range] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    interval_cases i
    · left; simp
    · right; left; simp
    · right; right; left; rw [pow_two, hkk]
    · right; right; right
      have h4 : k ^ 4 = 1 := by rw [← ho, pow_orderOf_eq_one]
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, h4]
  have hcard4 : ∀ k : G, k * k = z → Nat.card (Subgroup.zpowers k) = 4 := fun k hkk => by
    rw [Nat.card_zpowers, orderOf_eq_four_of_sq hkk hz.ne_one hz.sq]
  have step1 : ∀ k ∈ K, k * k = z → y * k * y⁻¹ ∉ Subgroup.zpowers k := by
    intro k hk hkk hmem
    have hαk2 : (y * k * y⁻¹) * (y * k * y⁻¹) = z := by
      calc (y * k * y⁻¹) * (y * k * y⁻¹) = y * (k * k) * y⁻¹ := by group
        _ = z := by rw [hkk, hyz]
    rcases hzp k hkk _ hmem with h | h | h | h
    · rw [h, one_mul] at hαk2
      exact hz.ne_one hαk2.symm
    ·
      apply hyc
      have hfix : ∀ m ∈ Subgroup.zpowers k, y * m * y⁻¹ = m := by
        intro m hm
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
        rw [← conj_zpow, h]
      have hKC : Nat.card K = 2 * Nat.card (Subgroup.zpowers k) := by rw [h8, hcard4 k hkk]
      have hCK : Subgroup.zpowers k ≤ K := Subgroup.zpowers_le.mpr hk
      intro x hx
      by_cases hxC : x ∈ Subgroup.zpowers k
      · have := hfix x hxC
        calc y * x = y * x * y⁻¹ * y := by group
          _ = x * y := by rw [this]
      · have hαx : y * x * y⁻¹ ∈ K := hα x hx
        have hαxC : y * x * y⁻¹ ∉ Subgroup.zpowers k := by
          intro hc
          apply hxC
          have h1 := hfix _ hc
          have : x = y⁻¹ * (y * x * y⁻¹) * y := by group
          rw [this]
          have h2 : y⁻¹ * (y * x * y⁻¹) * y = y * x * y⁻¹ := by
            calc y⁻¹ * (y * x * y⁻¹) * y = y⁻¹ * (y * (y * x * y⁻¹) * y⁻¹) * y := by rw [h1]
              _ = y * x * y⁻¹ := by group
          rw [h2]
          exact hc
        obtain hu | hu := mem_or_of_card_eq_two_mul hCK hKC hx hxC hαx
        · exact absurd hu hαxC
        generalize hu_def : x⁻¹ * (y * x * y⁻¹) = u at hu
        have hux : y * x * y⁻¹ = x * u := by rw [← hu_def]; group
        have hfu := hfix u hu
        have h2 : y * (y * x * y⁻¹) * y⁻¹ = x * u * u := by
          rw [hux]
          calc y * (x * u) * y⁻¹ = (y * x * y⁻¹) * (y * u * y⁻¹) := by group
            _ = x * u * u := by rw [hux, hfu]
        have h3 : y * (y * (y * x * y⁻¹) * y⁻¹) * y⁻¹ = x * u * u * u := by
          rw [h2]
          calc y * (x * u * u) * y⁻¹ = (y * x * y⁻¹) * (y * u * y⁻¹) * (y * u * y⁻¹) := by group
            _ = x * u * u * u := by rw [hux, hfu]
        rw [hα3 x hx] at h3
        have hu3 : u * u * u = 1 := by
          have : x * (u * u * u) = x * 1 := by
            rw [mul_one]
            simp only [← mul_assoc]
            exact h3.symm
          exact mul_left_cancel this
        have hu4 : u * u * u * u = 1 := by
          rcases hzp k hkk u hu with h0 | h0 | h0 | h0
          · rw [h0]; group
          · rw [h0, mul_assoc (k * k), hkk, hz.sq]
          · rw [h0, hz.sq, one_mul, hz.sq]
          · rw [h0, show k⁻¹ * k⁻¹ * k⁻¹ * k⁻¹ = (k * k * (k * k))⁻¹ by group, hkk, hz.sq,
              inv_one]
        have hu1 : u = 1 := by
          calc u = u * u * u * u * (u * u * u)⁻¹ := by group
            _ = 1 := by rw [hu4, hu3]; group
        calc y * x = y * x * y⁻¹ * y := by group
          _ = x * u * y := by rw [hux]
          _ = x * y := by rw [hu1, mul_one]
    · rw [h, hz.sq] at hαk2
      exact hz.ne_one hαk2.symm
    ·
      have h2 : y * (y * k * y⁻¹) * y⁻¹ = k := by
        rw [h]
        calc y * k⁻¹ * y⁻¹ = (y * k * y⁻¹)⁻¹ := by group
          _ = k := by rw [h, inv_inv]
      have h3 := hα3 k hk
      rw [h2, h] at h3
      apply hz.ne_one
      calc z = k * k := hkk.symm
        _ = k * k⁻¹ := by rw [h3]
        _ = 1 := mul_inv_cancel k
  obtain ⟨k, hk, hk4⟩ := hq.exists_orderOf_four
  have hk1 : k ≠ 1 := by
    intro h; rw [h, orderOf_one] at hk4; norm_num at hk4
  have hkz : k ≠ z := by
    intro h
    have : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
    rw [← h, hk4] at this
    norm_num at this
  have hkk := sq_eq_of_quat8 hq h8 hz hk hk1 hkz
  set j := y * k * y⁻¹ * k⁻¹ with hj_def
  have hjK : j ∈ K := K.mul_mem (hα k hk) (K.inv_mem hk)
  have hψj : ψ j = 1 := by rw [hj_def, map_mul, hψα, map_inv, mul_inv_cancel]
  have hjC : j ∉ Subgroup.zpowers k := by
    intro hc
    apply step1 k hk hkk
    have : y * k * y⁻¹ = j * k := by rw [hj_def]; group
    rw [this]
    exact Subgroup.mul_mem _ hc (Subgroup.mem_zpowers k)
  have hj1 : j ≠ 1 := fun h => hjC (h ▸ Subgroup.one_mem _)
  have hjz : j ≠ z := by
    intro h
    apply hjC
    rw [h, ← hkk]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers k) (Subgroup.mem_zpowers k)
  have hjj := sq_eq_of_quat8 hq h8 hz hjK hj1 hjz
  have hαj := step1 j hjK hjj
  set M := ψ.ker ⊓ K with hM
  have hjM : Subgroup.zpowers j ≤ M := by
    rw [Subgroup.zpowers_le]
    exact ⟨hψj, hjK⟩
  have hαjM : y * j * y⁻¹ ∈ M :=
    Subgroup.mem_inf.mpr ⟨MonoidHom.mem_ker.mpr (by rw [hψα, hψj]), hα j hjK⟩
  have hMK : M ≤ K := inf_le_right
  have hne : Subgroup.zpowers j ≠ M := fun h => hαj (h ▸ hαjM)
  have hdvd : Nat.card M ∣ 8 := h8 ▸ Subgroup.card_dvd_of_le hMK
  have hdvd4 : 4 ∣ Nat.card M := hcard4 j hjj ▸ Subgroup.card_dvd_of_le hjM
  have hM4 : Nat.card M ≠ 4 := by
    intro h4
    exact hne (Subgroup.eq_of_le_of_card_ge hjM (by rw [h4, hcard4 j hjj]))
  have hM8 : Nat.card M = 8 := by
    obtain ⟨a, ha⟩ := hdvd4
    have hpos : 0 < Nat.card M := Nat.card_pos
    have hle : Nat.card M ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    rcases (show a = 1 ∨ a = 2 by omega) with h | h
    · exact absurd (by rw [ha, h]) hM4
    · rw [ha, h]
  have hMeq : M = K := Subgroup.eq_of_le_of_card_ge hMK (by rw [hM8, h8])
  rw [← hMeq]
  exact inf_le_left

end Q8

theorem le_normalizer_of_comm {A B : Subgroup G} (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [h a ha b hb, mul_inv_cancel_right]
    exact hb
  · intro hb
    have hc := h a ha _ hb
    have e : a⁻¹ * (a * b * a⁻¹) * a = a * b * a⁻¹ := by
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [show b = a⁻¹ * (a * b * a⁻¹) * a by group, e]
    exact hb

section E8Fam

variable [Finite G] {r : ℕ} {Ω : Set (Subgroup G)} {E : Subgroup G}

omit [Finite G] in
theorem normal_of_e8 (hE : E8Struct ⊤ E) : E.Normal :=
  ⟨fun n hn g => hE.normal g (Subgroup.mem_top g) n hn⟩

omit [Finite G] in
theorem card_e8 (hE : E8Struct ⊤ E) : Nat.card G = 1344 := by
  have h1 := Subgroup.card_mul_index E
  rw [hE.card, ← Subgroup.relIndex_top_right, hE.index] at h1
  omega

omit [Finite G] in
theorem inv_mem_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) : z ∈ E := by
  obtain ⟨Q, hQn, hQ2, hzQ⟩ := hD.inO2 K hK z hz
  exact hE.core Q le_top (fun x _ q hq => hQn.conj_mem q hq x) hQ2 hzQ

omit [Finite G] in
theorem card_inf_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) : Nat.card ↥(K ⊓ E) = 2 := by
  have hzE := inv_mem_e8 hD hE hK hz
  have hset : ((K ⊓ E : Subgroup G) : Set G) = {1, z} := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_inf, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hxK, hxE⟩
      exact hz.unique x hxK (hE.sq x hxE)
    · rintro (rfl | rfl)
      · exact ⟨K.one_mem, E.one_mem⟩
      · exact ⟨hz.mem, hzE⟩
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_pair hz.ne_one.symm]

omit [Finite G] in
theorem card_sup_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) : Nat.card ↥(K ⊔ E) * 2 = Nat.card K * 8 := by
  have := normal_of_e8 hE
  have h := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer (A := K) (B := E)
    Subgroup.le_normalizer_of_normal
  rw [card_inf_e8 hD hE hK hz, hE.card] at h
  exact h

theorem le_normalizer_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K : Subgroup G} (hK : K ∈ Ω) :
    E ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := normal_of_e8 hE
  obtain ⟨⟨z, hz⟩, -⟩ := hD.hyp.omega1 K hK
  have hzE := inv_mem_e8 hD hE hK hz
  intro e he
  by_contra hne
  have hJK : conjSub e K ≠ K := fun h => hne (mem_normalizer_iff_conjSub_eq.mpr h)
  have hJ : conjSub e K ∈ Ω := hD.hyp.conjInvariant e K hK
  have hE2 : IsPGroup 2 ↥E := IsPGroup.of_card (n := 3) (by rw [hE.card]; norm_num)
  have hKE2 : IsPGroup 2 ↥(K ⊔ E) :=
    (hD.two K hK).to_sup_of_normal_right' hE2 Subgroup.le_normalizer_of_normal
  have hJKE : conjSub e K ≤ K ⊔ E := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have : x = e * (e⁻¹ * x * e) * e⁻¹ := by group
    rw [this]
    exact (K ⊔ E).mul_mem ((K ⊔ E).mul_mem (Subgroup.mem_sup_right he)
      (Subgroup.mem_sup_left hx)) ((K ⊔ E).inv_mem (Subgroup.mem_sup_right he))
  obtain ⟨S, hS⟩ := hKE2.exists_le_sylow
  have hcomm : ∀ x ∈ K, ∀ y ∈ conjSub e K, x * y = y * x :=
    Q3CP.l67Gen G Ω hD.hyp S K (TC.mem_RSet_of_isPGroup hK (hD.two K hK)) (conjSub e K)
      (TC.mem_RSet_of_isPGroup hJ (hD.two _ hJ)) (le_sup_left.trans hS) (hJKE.trans hS) hJK.symm
  have hq : IsQuatSub K := Sec6Gen.isQuatSub_of_mem_RSet hD.hyp
    (TC.mem_RSet_of_isPGroup hK (hD.two K hK))
  have hinf : Nat.card ↥(K ⊓ conjSub e K) ≤ 2 := by
    refine natCard_subgroup_le_two_of_subset (a := 1) (b := z) fun x hx => ?_
    refine hz.unique x hx.1 (hq.sq_eq_one_of_central hx.1 fun w hw => ?_)
    exact (hcomm w hw x hx.2).symm
  have hprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer (A := K) (B := conjSub e K)
    (le_normalizer_of_comm hcomm)
  have hcardJ : Nat.card ↥(conjSub e K) = Nat.card K := by rw [hD.card _ hJ, hD.card K hK]
  have hle : Nat.card ↥(K ⊔ conjSub e K) ≤ Nat.card ↥(K ⊔ E) :=
    Subgroup.card_le_of_le (sup_le le_sup_left hJKE)
  have hKE := card_sup_e8 hD hE hK hz
  have h8 := hq.eight_le
  have hinf1 : 1 ≤ Nat.card ↥(K ⊓ conjSub e K) := Nat.card_pos
  rw [hcardJ] at hprod
  have hK8 : Nat.card K = 8 := by nlinarith
  have hge : Nat.card ↥(K ⊔ E) ≤ Nat.card ↥(K ⊔ conjSub e K) := by nlinarith
  have heq : K ⊔ conjSub e K = K ⊔ E :=
    Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hJKE) hge
  have heN : e ∈ K ⊔ conjSub e K := heq ▸ Subgroup.mem_sup_right he
  exact hne ((sup_le (Subgroup.le_normalizer) (le_normalizer_of_comm fun x hx y hy =>
    (hcomm y hy x hx).symm)) heN)

theorem conj_mem_or_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {k : G} (hk : k ∈ K) {e : G} (he : e ∈ E) :
    k * e * k⁻¹ = e ∨ k * e * k⁻¹ = z * e := by
  have hc : k * e * k⁻¹ * e⁻¹ ∈ K := by
    have h1 : e * k⁻¹ * e⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_e8 hD hE hK he) _).mp (K.inv_mem hk)
    have : k * e * k⁻¹ * e⁻¹ = k * (e * k⁻¹ * e⁻¹) := by group
    rw [this]
    exact K.mul_mem hk h1
  have hcE : k * e * k⁻¹ * e⁻¹ ∈ E :=
    E.mul_mem (hE.normal k (Subgroup.mem_top k) e he) (E.inv_mem he)
  rcases hz.unique _ hc (hE.sq _ hcE) with h | h
  · left
    calc k * e * k⁻¹ = k * e * k⁻¹ * e⁻¹ * e := by group
      _ = e := by rw [h, one_mul]
  · right
    calc k * e * k⁻¹ = k * e * k⁻¹ * e⁻¹ * e := by group
      _ = z * e := by rw [h]

omit [Finite G] in
theorem exists_ne_e8 (hE : E8Struct ⊤ E) (z : G) : ∃ j ∈ E, j ≠ 1 ∧ j ≠ z := by
  by_contra hcon
  push Not at hcon
  have h := natCard_subgroup_le_two_of_subset (A := E) (a := 1) (b := z) fun x hx => by
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (hcon x hx h1)
  rw [hE.card] at h
  omega

omit [Finite G] in
theorem exists_frame_e8 (hE : E8Struct ⊤ E) [DecidableEq G] {z j : G} (hzE : z ∈ E) (hz1 : z ≠ 1)
    (hjE : j ∈ E) (hj1 : j ≠ 1) (hzj : z ≠ j) : ∃ e₀, E8Frame E z j e₀ := by
  obtain ⟨e, heE, heV⟩ : ∃ e ∈ E, e ∉ kleinSet z j := by
    by_contra hcon
    push Not at hcon
    have hsub : (E : Set G) ⊆ ((kleinSet z j : Finset G) : Set G) := fun x hx => hcon x hx
    have h1 : Nat.card E ≤ (kleinSet z j).card := by
      rw [← Nat.card_eq_finsetCard, ← SetLike.coe_sort_coe]
      exact Nat.card_mono (Finset.finite_toSet _) hsub
    have h2 : (kleinSet z j).card ≤ 4 := Finset.card_le_four
    rw [hE.card] at h1
    omega
  exact ⟨e, hE.card, hE.sq, hzE, hjE, hz1, hj1, hzj, heE, heV⟩

theorem card_inf_centralizer_le_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) [DecidableEq G] {j e₀ : G}
    (F : E8Frame E z j e₀) : Nat.card ↥(K ⊓ Subgroup.centralizer {j}) ≤ 4 := by
  have hzc : ∀ k ∈ K ⊓ Subgroup.centralizer {j}, k * z = z * k :=
    fun k hk => isUniqueInvolution_comm hz hk.1
  have h1 := card_le_two_mul_centralizer hzc hz.sq
    (fun k hk => conj_mem_or_e8 hD hE hK hz hk.1 F.eE)
  have h2 : Nat.card ↥((K ⊓ Subgroup.centralizer {j}) ⊓ Subgroup.centralizer {e₀}) ≤ 2 := by
    refine natCard_subgroup_le_two_of_subset (a := 1) (b := z) fun x hx => ?_
    have hxK : x ∈ K := hx.1.1
    have hxj : x * j = j * x := Subgroup.mem_centralizer_singleton_iff.mp hx.1.2
    have hxe : x * e₀ = e₀ * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hxz : x * z = z * x := isUniqueInvolution_comm hz hxK
    have hxE : x ∈ E := hE.cent x (Subgroup.mem_top x) (F.comm_of_comm hxz hxj hxe)
    exact hz.unique x hxK (hE.sq x hxE)
  omega

theorem card_eq_eight_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K : Subgroup G} (hK : K ∈ Ω) :
    Nat.card K = 8 := by
  classical
  obtain ⟨⟨z, hz⟩, -⟩ := hD.hyp.omega1 K hK
  have hzE := inv_mem_e8 hD hE hK hz
  obtain ⟨j, hjE, hj1, hjz⟩ := exists_ne_e8 hE z
  obtain ⟨e₀, F⟩ := exists_frame_e8 hE hzE hz.ne_one hjE hj1 (Ne.symm hjz)
  have h1 := card_le_two_mul_centralizer (K := K) (y := j)
    (fun k hk => isUniqueInvolution_comm hz hk) hz.sq
    (fun k hk => conj_mem_or_e8 hD hE hK hz hk hjE)
  have h2 := card_inf_centralizer_le_e8 hD hE hK hz F
  have h8 := (Sec6Gen.isQuatSub_of_mem_RSet hD.hyp
    (TC.mem_RSet_of_isPGroup hK (hD.two K hK))).eight_le
  omega

theorem eq_of_comm_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {e : G} (he : e ∈ E) (hc : ∀ k ∈ K, k * e = e * k) :
    e = 1 ∨ e = z := by
  classical
  by_contra hne
  push Not at hne
  have hzE := inv_mem_e8 hD hE hK hz
  obtain ⟨e₀, F⟩ := exists_frame_e8 hE hzE hz.ne_one he hne.1 (Ne.symm hne.2)
  have h2 := card_inf_centralizer_le_e8 hD hE hK hz F
  have hKe : K ⊓ Subgroup.centralizer {e} = K :=
    inf_eq_left.mpr fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hc k hk)
  rw [hKe] at h2
  have h8 := (Sec6Gen.isQuatSub_of_mem_RSet hD.hyp
    (TC.mem_RSet_of_isPGroup hK (hD.two K hK))).eight_le
  omega

omit [Finite G] in
theorem comm_of_pow_comm {y x : G} (hy : orderOf y = 7) {d : ℕ} (hd0 : 0 < d) (hd7 : d < 7)
    (h : y ^ d * x = x * y ^ d) : y * x = x * y := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := y) (n := d)
    (by rw [hy]; exact (Nat.coprime_of_lt_prime hd0.ne' hd7 (by norm_num)).symm)
  have h2 : (y ^ d) ^ m * x = x * (y ^ d) ^ m := Commute.pow_left h m
  rwa [hm] at h2

omit [Finite G] in
theorem conj_pow_injective {y x : G} (hy : orderOf y = 7) (hx : ¬ y * x = x * y) :
    Function.Injective (fun i : Fin 7 => y ^ (i : ℕ) * x * (y ^ (i : ℕ))⁻¹) := by
  have key : ∀ a b : ℕ, a < b → b < 7 →
      y ^ a * x * (y ^ a)⁻¹ = y ^ b * x * (y ^ b)⁻¹ → False := by
    intro a b hab hb h
    apply hx
    apply comm_of_pow_comm hy (d := b - a) (by omega) (by omega)
    have e : y ^ b = y ^ a * y ^ (b - a) := by rw [← pow_add]; congr 1; omega
    rw [e] at h
    have h2 : x = y ^ (b - a) * x * (y ^ (b - a))⁻¹ := by
      have := congrArg (fun t => (y ^ a)⁻¹ * t * y ^ a) h
      calc x = (y ^ a)⁻¹ * (y ^ a * x * (y ^ a)⁻¹) * y ^ a := by group
        _ = (y ^ a)⁻¹ * (y ^ a * y ^ (b - a) * x * (y ^ a * y ^ (b - a))⁻¹) * y ^ a := this
        _ = y ^ (b - a) * x * (y ^ (b - a))⁻¹ := by group
    calc y ^ (b - a) * x = y ^ (b - a) * x * (y ^ (b - a))⁻¹ * y ^ (b - a) := by group
      _ = x * y ^ (b - a) := by rw [← h2]
  intro i j hij
  simp only at hij
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · exact (key _ _ h j.2 hij).elim
  · exact Fin.ext h
  · exact (key _ _ h i.2 hij.symm).elim

theorem exists_conj_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    ∃ g : G, g * z * g⁻¹ = e := by
  classical
  have hzE := inv_mem_e8 hD hE hK hz
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := G) 7 (by rw [card_e8 hE]; norm_num)
  have hyE : ¬ ∀ x ∈ E, y * x = x * y := by
    intro h
    have hy2 : y * y = 1 := hE.sq y (hE.cent y (Subgroup.mem_top y) h)
    have := orderOf_dvd_of_pow_eq_one (show y ^ 2 = 1 by rw [pow_two]; exact hy2)
    rw [hy] at this
    norm_num at this
  have hEcard : (E : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hE.card]
  have hconjE : ∀ (i : ℕ) (x : G), x ∈ E → y ^ i * x * (y ^ i)⁻¹ ∈ E :=
    fun i x hx => hE.normal _ (Subgroup.mem_top _) x hx
  have hne1 : ∀ (i : ℕ) (x : G), y ^ i * x * (y ^ i)⁻¹ = 1 → x = 1 := by
    intro i x h
    calc x = (y ^ i)⁻¹ * (y ^ i * x * (y ^ i)⁻¹) * y ^ i := by group
      _ = 1 := by rw [h]; group
  have hyz : ¬ y * z = z * y := by
    intro hyz
    apply hyE
    intro x hx
    by_contra hxy
    have hinj := conj_pow_injective hy hxy
    have hsub : Set.range (fun i : Fin 7 => y ^ (i : ℕ) * x * (y ^ (i : ℕ))⁻¹) ⊆
        (E : Set G) \ {1, z} := by
      rintro _ ⟨i, rfl⟩
      refine ⟨hconjE i x hx, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro h1
        apply hxy
        rw [hne1 _ _ h1, one_mul, mul_one]
      · intro h1
        apply hxy
        have hyiz : y ^ (i : ℕ) * z = z * y ^ (i : ℕ) := Commute.pow_left hyz _
        have hxz : x = z := by
          calc x = (y ^ (i : ℕ))⁻¹ * (y ^ (i : ℕ) * x * (y ^ (i : ℕ))⁻¹) * y ^ (i : ℕ) := by
                group
            _ = (y ^ (i : ℕ))⁻¹ * (z * y ^ (i : ℕ)) := by rw [h1, mul_assoc]
            _ = z := by rw [← hyiz]; group
        rw [hxz]
        exact hyz
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hsub2 : ({1, z} : Set G) ⊆ E := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact E.one_mem
      · exact hzE
    rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin,
      Set.ncard_sdiff hsub2, hEcard, Set.ncard_pair hz.ne_one.symm] at h1
    omega
  have hinj := conj_pow_injective hy hyz
  have hsub : Set.range (fun i : Fin 7 => y ^ (i : ℕ) * z * (y ^ (i : ℕ))⁻¹) ⊆
      (E : Set G) \ {1} := by
    rintro _ ⟨i, rfl⟩
    exact ⟨hconjE i z hzE, fun h1 => hz.ne_one (hne1 _ _ h1)⟩
  have hsub1 : ({1} : Set G) ⊆ E := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact E.one_mem
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin,
      Set.ncard_sdiff hsub1, hEcard, Set.ncard_singleton]) (Set.toFinite _)
  have he' : e ∈ (E : Set G) \ {1} := ⟨he, he1⟩
  rw [← heq] at he'
  obtain ⟨i, hi⟩ := he'
  exact ⟨y ^ (i : ℕ), hi⟩

theorem card_centralizer_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G)) = 192 := by
  classical
  have hzE := inv_mem_e8 hD hE hK hz
  have hcls : (ConjClasses.mk z).carrier = (E : Set G) \ {1} := by
    ext x
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    constructor
    · rintro ⟨c, hc⟩
      have hx : x = c⁻¹ * z * c := by rw [← hc]; group
      refine ⟨?_, fun h1 => hz.ne_one ?_⟩
      · rw [hx]
        simpa using hE.normal c⁻¹ (Subgroup.mem_top _) z hzE
      · rw [← hc, show x = 1 from h1]
        group
    · rintro ⟨hxE, hx1⟩
      obtain ⟨g, hg⟩ := exists_conj_e8 hD hE hK hz hxE hx1
      exact ⟨g⁻¹, by rw [← hg]; group⟩
  have h1 := CFSG.GorensteinWalter.card_conjClass_eq_centralizer_index_local z
  have hsub1 : ({1} : Set G) ⊆ E := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact E.one_mem
  have hEcard : (E : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hE.card]
  have h7 : Nat.card ↑((E : Set G) \ {1}) = 7 := by
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff hsub1, hEcard, Set.ncard_singleton]
  rw [hcls, h7] at h1
  have h2 := Subgroup.card_mul_index (Subgroup.centralizer ({z} : Set G))
  rw [← h1, card_e8 hE] at h2
  omega

theorem exists_v_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {L : Subgroup G} (hL : L ∈ Ω) {t : G}
    (ht : IsUniqueInvolution L t) (htz : t ≠ z) :
    ∃ v ∈ L, v * z = z * v ∧ v * v = t ∧ v ∈ Subgroup.normalizer (K : Set G) ∧ v ∉ K ⊔ E := by
  have hzE := inv_mem_e8 hD hE hK hz
  have hL8 := card_eq_eight_e8 hD hE hL
  have hqL : IsQuatSub L :=
    Sec6Gen.isQuatSub_of_mem_RSet hD.hyp (TC.mem_RSet_of_isPGroup hL (hD.two L hL))
  have h1 := card_le_two_mul_centralizer (K := L) (y := z)
    (fun l hl => isUniqueInvolution_comm ht hl) ht.sq
    (fun l hl => conj_mem_or_e8 hD hE hL ht hl hzE)
  obtain ⟨v, hv, hv1, hvt⟩ : ∃ v ∈ L ⊓ Subgroup.centralizer {z}, v ≠ 1 ∧ v ≠ t := by
    by_contra hcon
    push Not at hcon
    have := natCard_subgroup_le_two_of_subset (A := L ⊓ Subgroup.centralizer {z}) (a := 1)
      (b := t) fun x hx => by
        by_cases h1 : x = 1
        · exact Or.inl h1
        · exact Or.inr (hcon x hx h1)
    omega
  have hvL : v ∈ L := hv.1
  have hvz : v * z = z * v := Subgroup.mem_centralizer_singleton_iff.mp hv.2
  have hvv : v * v = t := sq_eq_of_quat8 hqL hL8 ht hvL hv1 hvt
  have hKL : K ≠ L := by
    rintro rfl
    exact htz (hz.eq ht).symm
  have hvnc : ¬ ∀ w ∈ L, v * w = w * v := fun hc => by
    rcases ht.unique v hvL (hqL.sq_eq_one_of_central hvL hc) with h | h
    · exact hv1 h
    · exact hvt h
  have hvN : v ∈ Subgroup.normalizer (K : Set G) :=
    hD.hyp.omega5 K hK L hL hKL z hz v hvL hvnc
      ((hD.two L hL).to_le (Subgroup.zpowers_le.mpr hvL)) hvz
  obtain ⟨x, hxE, hvx⟩ : ∃ x ∈ E, v * x * v⁻¹ = t * x := by
    by_contra hcon
    push Not at hcon
    have hvE : v ∈ E := hE.cent v (Subgroup.mem_top v) fun x hx => by
      have := (conj_mem_or_e8 hD hE hL ht hvL hx).resolve_right (hcon x hx)
      calc v * x = v * x * v⁻¹ * v := by group
        _ = x * v := by rw [this]
    rcases ht.unique v hvL (hE.sq v hvE) with h | h
    · exact hv1 h
    · exact hvt h
  refine ⟨v, hvL, hvz, hvv, hvN, fun hvKE => ?_⟩
  have := normal_of_e8 hE
  obtain ⟨k, hk, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hvKE
  have hex : e * x * e⁻¹ = x := by rw [comm_of_sq hE.sq he hxE, mul_inv_cancel_right]
  have h2 : k * e * x * (k * e)⁻¹ = k * x * k⁻¹ := by
    calc k * e * x * (k * e)⁻¹ = k * (e * x * e⁻¹) * k⁻¹ := by group
      _ = k * x * k⁻¹ := by rw [hex]
  rw [h2] at hvx
  rcases conj_mem_or_e8 hD hE hK hz hk hxE with h | h
  · rw [h] at hvx
    apply ht.ne_one
    calc t = t * x * x⁻¹ := by group
      _ = 1 := by rw [← hvx, mul_inv_cancel]
  · rw [h] at hvx
    exact htz (mul_right_cancel hvx).symm

omit [Finite G] in
theorem mem_normalizer_sup_normal {K E : Subgroup G} [E.Normal] {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) : n ∈ Subgroup.normalizer ((K ⊔ E : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨k, hk, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    have : n * (k * e) * n⁻¹ = (n * k * n⁻¹) * (n * e * n⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hn k).mp hk))
      (Subgroup.mem_sup_right (‹E.Normal›.conj_mem e he n))
  · intro hx
    obtain ⟨k, hk, e, he, he'⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    have hn' := (Subgroup.normalizer (K : Set G)).inv_mem hn
    have : x = (n⁻¹ * k * n⁻¹⁻¹) * (n⁻¹ * e * n⁻¹⁻¹) := by
      rw [inv_inv, show n⁻¹ * k * n * (n⁻¹ * e * n) = n⁻¹ * (k * e) * n by group, he']
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hn' k).mp hk))
      (Subgroup.mem_sup_right (‹E.Normal›.conj_mem e he n⁻¹))

theorem card_S_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {v t : G} (hvN : v ∈ Subgroup.normalizer (K : Set G))
    (hvv : v * v = t) (htE : t ∈ E) (ht1 : t ≠ 1) (hvKE : v ∉ K ⊔ E) :
    Nat.card ↥(Subgroup.zpowers v ⊔ (K ⊔ E)) = 64 := by
  have := normal_of_e8 hE
  have hvNKE : Subgroup.zpowers v ≤ Subgroup.normalizer ((K ⊔ E : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_sup_normal hvN)
  have hprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hvNKE
  have hv4 : Nat.card (Subgroup.zpowers v) = 4 := by
    rw [Nat.card_zpowers, orderOf_eq_four_of_sq hvv ht1 (hE.sq t htE)]
  have hKE := card_sup_e8 hD hE hK hz
  rw [card_eq_eight_e8 hD hE hK] at hKE
  have htD : t ∈ Subgroup.zpowers v ⊓ (K ⊔ E) :=
    ⟨hvv ▸ Subgroup.mul_mem _ (Subgroup.mem_zpowers v) (Subgroup.mem_zpowers v),
      Subgroup.mem_sup_right htE⟩
  have hD1 : 1 < Nat.card ↥(Subgroup.zpowers v ⊓ (K ⊔ E)) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro h
    rw [h, Subgroup.mem_bot] at htD
    exact ht1 htD
  have hDdvd : Nat.card ↥(Subgroup.zpowers v ⊓ (K ⊔ E)) ∣ 4 :=
    hv4 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hD4 : Nat.card ↥(Subgroup.zpowers v ⊓ (K ⊔ E)) ≠ 4 := by
    intro h4
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : Subgroup.zpowers v ⊓ (K ⊔ E) ≤ _)
      (by rw [h4, hv4])
    have hvD : v ∈ Subgroup.zpowers v ⊓ (K ⊔ E) := by rw [heq]; exact Subgroup.mem_zpowers v
    exact hvKE hvD.2
  have hD2 : Nat.card ↥(Subgroup.zpowers v ⊓ (K ⊔ E)) = 2 := by
    have hle := Nat.le_of_dvd (by norm_num) hDdvd
    interval_cases h : Nat.card ↥(Subgroup.zpowers v ⊓ (K ⊔ E)) <;> omega
  rw [hD2, hv4] at hprod
  omega

omit [Finite G] in
theorem twin_comm [Finite G] (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hz : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : ∀ x ∈ K, ∀ y ∈ J, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : IsQuatSub K := Sec6Gen.isQuatSub_of_mem_RSet hΩ (TC.mem_RSet_of_isPGroup hK (h2 K hK))
  have hKN : K ≤ Subgroup.normalizer (J : Set G) := by
    intro k hk
    by_cases hc : ∀ w ∈ K, k * w = w * k
    · rcases hz.unique k hk (hq.sq_eq_one_of_central hk hc) with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.le_normalizer hzJ.mem
    · exact hΩ.omega5 J hJ K hK (Ne.symm hKJ) z hzJ k hk hc
        ((h2 K hK).to_le (Subgroup.zpowers_le.mpr hk)) (isUniqueInvolution_comm hz hk)
  have hP2 : IsPGroup 2 ↥(K ⊔ J) := (h2 K hK).to_sup_of_normal_right' (h2 J hJ) hKN
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  exact Q3CP.l67Gen G Ω hΩ S K (TC.mem_RSet_of_isPGroup hK (h2 K hK)) J
    (TC.mem_RSet_of_isPGroup hJ (h2 J hJ)) (le_sup_left.trans hPS) (le_sup_right.trans hPS) hKJ

theorem eq_of_inv_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) : K = J := by
  by_contra hKJ
  have hzE := inv_mem_e8 hD hE hK hz
  have hG := card_e8 hE
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => card_eq_eight_e8 hD hE hL
  have hqf : ∀ L ∈ Ω, IsQuatSub L := fun L hL =>
    Sec6Gen.isQuatSub_of_mem_RSet hD.hyp (TC.mem_RSet_of_isPGroup hL (hD.two L hL))
  have hcen : ∀ L ∈ Ω, IsUniqueInvolution L z → ∀ (M : Subgroup G),
      (∀ x ∈ M, ∀ y ∈ L, x * y = y * x) → Nat.card ↥(M ⊓ L) ≤ 2 := by
    intro L hL hzL M hML
    refine natCard_subgroup_le_two_of_subset (a := 1) (b := z) fun x hx => ?_
    exact hzL.unique x hx.2 ((hqf L hL).sq_eq_one_of_central hx.2 fun w hw => hML x hx.1 w hw)
  have hthird : ∀ L ∈ Ω, IsUniqueInvolution L z → L = K ∨ L = J := by
    intro L hL hzL
    by_contra hcon
    push Not at hcon
    have hKJc := twin_comm hD.hyp hD.two hK hJ hKJ hz hzJ
    have hKLc := twin_comm hD.hyp hD.two hK hL (Ne.symm hcon.1) hz hzL
    have hJLc := twin_comm hD.hyp hD.two hJ hL (Ne.symm hcon.2) hzJ hzL
    have h1 := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer (A := K) (B := J)
      (le_normalizer_of_comm hKJc)
    have hKJJ : ∀ x ∈ K ⊔ J, ∀ y ∈ L, x * y = y * x := by
      have hle : K ⊔ J ≤ Subgroup.centralizer (L : Set G) := by
        refine sup_le (fun x hx => ?_) (fun x hx => ?_) <;>
          rw [Subgroup.mem_centralizer_iff] <;> intro y hy
        · exact (hKLc x hx y hy).symm
        · exact (hJLc x hx y hy).symm
      intro x hx y hy
      exact ((Subgroup.mem_centralizer_iff.mp (hle hx)) y hy).symm
    have h2 := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer (A := K ⊔ J) (B := L)
      (le_normalizer_of_comm hKJJ)
    have hi1 : Nat.card ↥(K ⊓ J) ≤ 2 := hcen J hJ hzJ K hKJc
    have hi2 : Nat.card ↥((K ⊔ J) ⊓ L) ≤ 2 := hcen L hL hzL _ hKJJ
    have hi1' : 1 < Nat.card ↥(K ⊓ J) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro h
      have : z ∈ K ⊓ J := ⟨hz.mem, hzJ.mem⟩
      rw [h, Subgroup.mem_bot] at this
      exact hz.ne_one this
    have hi2' : 1 < Nat.card ↥((K ⊔ J) ⊓ L) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro h
      have : z ∈ (K ⊔ J) ⊓ L := ⟨Subgroup.mem_sup_left hz.mem, hzL.mem⟩
      rw [h, Subgroup.mem_bot] at this
      exact hz.ne_one this
    rw [h8 K hK, h8 J hJ] at h1
    rw [h8 L hL] at h2
    have hc1 : Nat.card ↥(K ⊔ J) = 32 := by
      have : Nat.card ↥(K ⊓ J) = 2 := by omega
      rw [this] at h1
      omega
    have hc2 : Nat.card ↥((K ⊔ J) ⊔ L) = 128 := by
      have : Nat.card ↥((K ⊔ J) ⊓ L) = 2 := by omega
      rw [this, hc1] at h2
      omega
    have hdvd := Subgroup.card_subgroup_dvd_card ((K ⊔ J) ⊔ L)
    rw [hc2, hG] at hdvd
    norm_num at hdvd
  obtain ⟨g, hg⟩ := hD.trans K hK J hJ
  have hgz : g * z = z * g := by
    have h1 := hz.conj g
    rw [hg] at h1
    have h2 := hzJ.eq h1
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [← h2]
  set N := Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer ({z} : Set G) with hN
  obtain ⟨t, htE, ht1, htz⟩ := exists_ne_e8 hE z
  obtain ⟨h, hh⟩ := exists_conj_e8 hD hE hK hz htE ht1
  have hL : conjSub h K ∈ Ω := hD.hyp.conjInvariant h K hK
  have ht : IsUniqueInvolution (conjSub h K) t := hh ▸ hz.conj h
  obtain ⟨v, -, hvz, hvv, hvN, hvKE⟩ := exists_v_e8 hD hE hK hz hL ht htz
  have hS := card_S_e8 hD hE hK hz hvN hvv htE ht1 hvKE
  have hSN : Subgroup.zpowers v ⊔ (K ⊔ E) ≤ N := by
    refine le_inf (sup_le (Subgroup.zpowers_le.mpr hvN)
      (sup_le Subgroup.le_normalizer (le_normalizer_e8 hD hE hK))) (sup_le ?_ (sup_le ?_ ?_))
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hvz)
    · exact fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (isUniqueInvolution_comm hz hk)
    · exact fun e he => Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_sq hE.sq he hzE)
  have h64 : 64 ∣ Nat.card N := hS ▸ Subgroup.card_dvd_of_le hSN
  have hcover : ∀ c ∈ Subgroup.centralizer ({z} : Set G), c ∈ N ∨ g⁻¹ * c ∈ N := by
    intro c hc
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hzc : IsUniqueInvolution (conjSub c K) z := by
      have h1 := hz.conj c
      rwa [show c * z * c⁻¹ = z by rw [hcz]; group] at h1
    rcases hthird _ (hD.hyp.conjInvariant c K hK) hzc with h1 | h1
    · exact Or.inl ⟨mem_normalizer_iff_conjSub_eq.mpr h1, hc⟩
    · right
      refine ⟨mem_normalizer_iff_conjSub_eq.mpr ?_, ?_⟩
      · rw [conjSub_mul, h1, ← hg, conjSub_inv_conjSub]
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _
          (Subgroup.mem_centralizer_singleton_iff.mpr hgz)) hc
  have h1 := card_le_two_mul_of_mem_or hcover
  rw [card_centralizer_e8 hD hE hK hz] at h1
  have hgN : g ∉ N := fun hgN => hKJ (by rw [← hg]; exact
    (mem_normalizer_iff_conjSub_eq.mp hgN.1).symm)
  have hNC : N ≤ Subgroup.centralizer ({z} : Set G) := inf_le_right
  have hNdvd : Nat.card N ∣ 192 := card_centralizer_e8 hD hE hK hz ▸ Subgroup.card_dvd_of_le hNC
  have hN192 : Nat.card N ≠ 192 := by
    intro h192
    have := Subgroup.eq_of_le_of_card_ge hNC (by rw [h192, card_centralizer_e8 hD hE hK hz])
    exact hgN (this ▸ Subgroup.mem_centralizer_singleton_iff.mpr hgz)
  obtain ⟨b, hb⟩ := hNdvd
  obtain ⟨a, ha⟩ := h64
  have hb1 : b ≤ 2 := by nlinarith
  interval_cases b <;> omega

theorem exists_three_e8 (hD : ThmDHyp r Ω) (hE : E8Struct ⊤ E) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) :
    ∃ x : G, x * z = z * x ∧ orderOf x = 3 ∧ x ∈ Subgroup.normalizer (K : Set G) ∧
      ¬ ∀ k ∈ K, x * k = k * x := by
  have hzE := inv_mem_e8 hD hE hK hz
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer ({z} : Set G))) 3
    (by rw [card_centralizer_e8 hD hE hK hz]; norm_num)
  set x : G := (x' : G) with hx_def
  have hx3 : orderOf x = 3 := by rw [hx_def, Subgroup.orderOf_coe, hx']
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp x'.2
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := by
    have hzc : IsUniqueInvolution (conjSub x K) z := by
      have h1 := hz.conj x
      rwa [show x * z * x⁻¹ = z by rw [hxz]; group] at h1
    exact mem_normalizer_iff_conjSub_eq.mpr
      (eq_of_inv_e8 hD hE (hD.hyp.conjInvariant x K hK) hK hzc hz)
  refine ⟨x, hxz, hx3, hxN, fun hc => ?_⟩
  have hxzi : x * z * x⁻¹ = z := by rw [hxz]; group
  have hmod : ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ = 1 ∨ x * e * x⁻¹ * e⁻¹ = z := by
    intro e he
    have hxe : x * e * x⁻¹ ∈ E := hE.normal x (Subgroup.mem_top x) e he
    have hfE : x * e * x⁻¹ * e⁻¹ ∈ E := E.mul_mem hxe (E.inv_mem he)
    refine eq_of_comm_e8 hD hE hK hz hfE fun k hk => ?_
    have hck : k * (x * e * x⁻¹) * k⁻¹ = x * (k * e * k⁻¹) * x⁻¹ := by
      have hkx : k * x = x * k := (hc k hk).symm
      have hkx' : x⁻¹ * k⁻¹ = k⁻¹ * x⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hkx]
      calc k * (x * e * x⁻¹) * k⁻¹ = (k * x) * e * (x⁻¹ * k⁻¹) := by group
        _ = (x * k) * e * (k⁻¹ * x⁻¹) := by rw [hkx, hkx']
        _ = x * (k * e * k⁻¹) * x⁻¹ := by group
    rcases conj_mem_or_e8 hD hE hK hz hk he with h | h
    · rw [h] at hck
      calc k * (x * e * x⁻¹ * e⁻¹) = k * (x * e * x⁻¹) * k⁻¹ * (k * e⁻¹ * k⁻¹) * k := by group
        _ = x * e * x⁻¹ * (k * e * k⁻¹)⁻¹ * k := by rw [hck]; group
        _ = x * e * x⁻¹ * e⁻¹ * k := by rw [h]
    · rw [h] at hck
      have hzf : z * (x * e * x⁻¹) = (x * e * x⁻¹) * z := comm_of_sq hE.sq hzE hxe
      have hze : z * e⁻¹ = e⁻¹ * z := comm_of_sq hE.sq hzE (E.inv_mem he)
      calc k * (x * e * x⁻¹ * e⁻¹) = k * (x * e * x⁻¹) * k⁻¹ * (k * e * k⁻¹)⁻¹ * k := by group
        _ = x * (z * e) * x⁻¹ * (z * e)⁻¹ * k := by rw [hck, h]
        _ = (x * z * x⁻¹) * (x * e * x⁻¹) * e⁻¹ * z⁻¹ * k := by group
        _ = z * (x * e * x⁻¹) * e⁻¹ * z⁻¹ * k := by rw [hxzi]
        _ = (x * e * x⁻¹) * z * e⁻¹ * z⁻¹ * k := by rw [hzf]
        _ = (x * e * x⁻¹) * e⁻¹ * (z * z⁻¹) * k := by rw [mul_assoc (x * e * x⁻¹) z, hze]; group
        _ = x * e * x⁻¹ * e⁻¹ * k := by rw [mul_inv_cancel, mul_one]
  have hx2E : x * x ∈ E := by
    refine hE.cent _ (Subgroup.mem_top _) fun e he => ?_
    have hfix : x * (x * e * x⁻¹) * x⁻¹ = e := by
      rcases hmod e he with h | h
      · have h' : x * e * x⁻¹ = e := by
          calc x * e * x⁻¹ = x * e * x⁻¹ * e⁻¹ * e := by group
            _ = e := by rw [h, one_mul]
        rw [h', h']
      · have h' : x * e * x⁻¹ = z * e := by
          calc x * e * x⁻¹ = x * e * x⁻¹ * e⁻¹ * e := by group
            _ = z * e := by rw [h]
        rw [h']
        calc x * (z * e) * x⁻¹ = (x * z * x⁻¹) * (x * e * x⁻¹) := by group
          _ = z * (z * e) := by rw [hxzi, h']
          _ = e := by rw [← mul_assoc, hz.sq, one_mul]
    calc x * x * e = x * (x * e * x⁻¹) * x⁻¹ * (x * x) := by group
      _ = e * (x * x) := by rw [hfix]
  have hx4 : x ^ 4 = 1 := by
    have := hE.sq _ hx2E
    have e4 : x ^ 4 = x * x * (x * x) := by
      rw [pow_succ, pow_succ, pow_succ, pow_one]
      simp only [mul_assoc]
    rw [e4]
    exact this
  have := orderOf_dvd_of_pow_eq_one hx4
  rw [hx3] at this
  norm_num at this

end E8Fam

theorem commutatorElement_mul_central {a b c d : G} (hc : c ∈ Subgroup.center G)
    (hd : d ∈ Subgroup.center G) : ⁅a * c, b * d⁆ = ⁅a, b⁆ :=
  CFSG.ClassicalInvolution.Asc77.AscE186.commutator_mul_central hc hd

section Lift

variable [Finite G] {r : ℕ} {Ω : Set (Subgroup G)}

local notation "πc" => QuotientGroup.mk' (Subgroup.center G)

theorem isUniqueInvolution_quot (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    IsUniqueInvolution (K.map πc) (πc z) :=
  isUniqueInvolution_map_mk_of_odd (by rw [hZK K hK, Subgroup.card_bot]; exact odd_one) hz

theorem mem_normalizer_of_quot (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    {K : Subgroup G} (hK : K ∈ Ω) {g : G}
    (hg : πc g ∈ Subgroup.normalizer ((K.map πc : Subgroup (G ⧸ Subgroup.center G)) :
      Set (G ⧸ Subgroup.center G))) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  apply eq_of_map_eq hD.hyp hD.two le_rfl hZK (hD.hyp.conjInvariant g K hK) hK
  rw [TwistQ.conjSub_map]
  exact mem_normalizer_iff_conjSub_eq.mp hg

variable {Ē : Subgroup (G ⧸ Subgroup.center G)}

theorem mem_normalizer_of_mem_e8 (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    (hE : E8Struct ⊤ Ē) {K : Subgroup G} (hK : K ∈ Ω) {g : G} (hg : πc g ∈ Ē) :
    g ∈ Subgroup.normalizer (K : Set G) :=
  mem_normalizer_of_quot hD hZK hK
    (le_normalizer_e8 (thmDHyp_quot hD hZK) hE ⟨K, hK, rfl⟩ hg)

theorem mk_inv_mem_e8 (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    (hE : E8Struct ⊤ Ē) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (g : G) : πc (g * z * g⁻¹) ∈ Ē := by
  have hzE := inv_mem_e8 (thmDHyp_quot hD hZK) hE ⟨K, hK, rfl⟩ (isUniqueInvolution_quot hZK hK hz)
  rw [map_mul, map_mul, map_inv]
  exact hE.normal _ (Subgroup.mem_top _) _ hzE

theorem conj_comm_e8 (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    (hE : E8Struct ⊤ Ē) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (g : G) : (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := by
  have hN := mem_normalizer_of_mem_e8 hD hZK hE hK (mk_inv_mem_e8 hD hZK hE hK hz g)
  have h := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hN)
  calc (g * z * g⁻¹) * z = (g * z * g⁻¹) * z * (g * z * g⁻¹)⁻¹ * (g * z * g⁻¹) := by group
    _ = z * (g * z * g⁻¹) := by rw [h]

theorem exists_conj_mul_e8 (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    (hE : E8Struct ⊤ Ē) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {g : G} (hgz : g * z * g⁻¹ ≠ z) : ∃ h : G, h * z * h⁻¹ = z * (g * z * g⁻¹) := by
  have hD' := thmDHyp_quot hD hZK
  set t := g * z * g⁻¹ with ht_def
  have hL : conjSub g K ∈ Ω := hD.hyp.conjInvariant g K hK
  have ht : IsUniqueInvolution (conjSub g K) t := hz.conj g
  have hz' := isUniqueInvolution_quot hZK hK hz
  have ht' := isUniqueInvolution_quot hZK hL ht
  have hzE := inv_mem_e8 hD' hE ⟨K, hK, rfl⟩ hz'
  have htz : πc t ≠ πc z := by
    intro h
    rw [h] at ht'
    have := eq_of_inv_e8 hD' hE ⟨_, hL, rfl⟩ ⟨K, hK, rfl⟩ ht' hz'
    have hLK := eq_of_map_eq hD.hyp hD.two le_rfl hZK hL hK this
    rw [hLK] at ht
    exact hgz (hz.eq ht).symm
  obtain ⟨w, hwL, hwz⟩ : ∃ w ∈ conjSub g K, ¬ w * z = z * w := by
    by_contra hcon
    push Not at hcon
    rcases eq_of_comm_e8 hD' hE ⟨_, hL, rfl⟩ ht' hzE (by
      rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul, ← map_mul, hcon w hw]) with h | h
    · exact hz'.ne_one h
    · exact htz h.symm
  have hzN := mem_normalizer_of_mem_e8 hD hZK hE hL (g := z) hzE
  have hc : w * z * w⁻¹ * z⁻¹ ∈ conjSub g K := by
    have h1 : z * w⁻¹ * z⁻¹ ∈ conjSub g K :=
      (Subgroup.mem_normalizer_iff.mp hzN _).mp (Subgroup.inv_mem _ hwL)
    have : w * z * w⁻¹ * z⁻¹ = w * (z * w⁻¹ * z⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hwL h1
  have hcc : (w * z * w⁻¹ * z⁻¹) * (w * z * w⁻¹ * z⁻¹) = 1 := by
    have hcomm := conj_comm_e8 hD hZK hE hK hz w
    have hzz := hz.sq
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    rw [hzi]
    calc (w * z * w⁻¹ * z) * (w * z * w⁻¹ * z) = (w * z * w⁻¹) * (z * (w * z * w⁻¹)) * z := by
          group
      _ = (w * z * w⁻¹) * ((w * z * w⁻¹) * z) * z := by rw [hcomm]
      _ = w * (z * z) * w⁻¹ * (z * z) := by group
      _ = 1 := by rw [hzz]; group
  have hc1 : w * z * w⁻¹ * z⁻¹ ≠ 1 := by
    intro h
    apply hwz
    calc w * z = w * z * w⁻¹ * z⁻¹ * z * w := by group
      _ = z * w := by rw [h, one_mul]
  have hct := (ht.unique _ hc hcc).resolve_left hc1
  refine ⟨w, ?_⟩
  have h1 : w * z * w⁻¹ = t * z := by
    calc w * z * w⁻¹ = w * z * w⁻¹ * z⁻¹ * z := by group
      _ = t * z := by rw [hct]
  rw [h1]
  have := conj_comm_e8 hD hZK hE hK hz g
  rw [← ht_def] at this
  exact this

theorem mem_normalClosure_e8 (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    (hE : E8Struct ⊤ Ē) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {e : G} (he : e ∈ Subgroup.normalClosure ({z} : Set G)) :
    e = 1 ∨ ∃ g : G, g * z * g⁻¹ = e := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz.sq
  induction he using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨c, hc⟩ := isConj_iff.mp hax
    exact Or.inr ⟨c, hc⟩
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | ⟨a, rfl⟩
    · rw [one_mul]; exact hy
    rcases hy with rfl | ⟨b, rfl⟩
    · rw [mul_one]; exact Or.inr ⟨a, rfl⟩
    by_cases hab : a * z * a⁻¹ = b * z * b⁻¹
    · left
      rw [← hab]
      calc a * z * a⁻¹ * (a * z * a⁻¹) = a * (z * z) * a⁻¹ := by group
        _ = 1 := by rw [hz.sq]; group
    · right
      have hne : (a⁻¹ * b) * z * (a⁻¹ * b)⁻¹ ≠ z := by
        intro h
        apply hab
        calc a * z * a⁻¹ = a * ((a⁻¹ * b) * z * (a⁻¹ * b)⁻¹) * a⁻¹ := by rw [h]
          _ = b * z * b⁻¹ := by group
      obtain ⟨h, hh⟩ := exists_conj_mul_e8 hD hZK hE hK hz hne
      refine ⟨a * h, ?_⟩
      calc a * h * z * (a * h)⁻¹ = a * (h * z * h⁻¹) * a⁻¹ := by group
        _ = a * (z * ((a⁻¹ * b) * z * (a⁻¹ * b)⁻¹)) * a⁻¹ := by rw [hh]
        _ = a * z * a⁻¹ * (b * z * b⁻¹) := by group
  | inv x _ hx =>
    rcases hx with rfl | ⟨a, rfl⟩
    · left; rw [inv_one]
    · right
      exact ⟨a, by rw [mul_inv_rev, mul_inv_rev, inv_inv, hzi, mul_assoc]⟩

theorem normalClosure_inf_center_e8 (hD : ThmDHyp r Ω)
    (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥) (hE : E8Struct ⊤ Ē) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) :
    Subgroup.center G ⊓ Subgroup.normalClosure ({z} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro e ⟨hec, he⟩
  rw [Subgroup.mem_bot]
  rcases mem_normalClosure_e8 hD hZK hE hK hz he with h | ⟨g, rfl⟩
  · exact h
  · exfalso
    have hc := Subgroup.mem_center_iff.mp hec
    have hzc : z ∈ Subgroup.center G := by
      have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [this, mul_assoc, ← hc g, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hec
    have : z ∈ Subgroup.center G ⊓ K := ⟨hzc, hz.mem⟩
    rw [hZK K hK, Subgroup.mem_bot] at this
    exact hz.ne_one this

theorem map_normalClosure_e8 (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    (hE : E8Struct ⊤ Ē) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    (Subgroup.normalClosure ({z} : Set G)).map πc = Ē := by
  have hD' := thmDHyp_quot hD hZK
  have hz' := isUniqueInvolution_quot hZK hK hz
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    have : (Ē.comap πc).Normal := (normal_of_e8 hE).comap πc
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact inv_mem_e8 hD' hE ⟨K, hK, rfl⟩ hz'
  · intro eb heb
    by_cases h1 : eb = 1
    · rw [h1]
      exact Subgroup.one_mem _
    obtain ⟨gb, hgb⟩ := exists_conj_e8 hD' hE ⟨K, hK, rfl⟩ hz' heb h1
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) gb
    refine ⟨g * z * g⁻¹, Subgroup.normalClosure_normal.conj_mem z
      (Subgroup.subset_normalClosure (Set.mem_singleton z)) g, ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact hgb

theorem center_eq_bot_of_e8 (hD : ThmDHyp r Ω) (hZK : ∀ K ∈ Ω, Subgroup.center G ⊓ K = ⊥)
    (hE : E8Struct ⊤ Ē) : Subgroup.center G = ⊥ := by
  have hD' := thmDHyp_quot hD hZK
  rcases Ω.eq_empty_or_nonempty with hΩ | ⟨K, hK⟩
  · have htop : (⊤ : Subgroup G) ≤ ⊥ := by
      rw [← hD.gen]
      exact pSpan_le fun L hL => absurd (hΩ ▸ hL) (Set.notMem_empty L)
    exact eq_bot_iff.mpr (le_top.trans htop)
  obtain ⟨⟨z, hz⟩, -⟩ := hD.hyp.omega1 K hK
  have hK' : K.map πc ∈ quotFam Ω := ⟨K, hK, rfl⟩
  have hz' := isUniqueInvolution_quot hZK hK hz
  have hK8 : Nat.card K = 8 := by
    rw [← card_map_mk_eq (hZK K hK)]
    exact card_eq_eight_e8 hD' hE hK'
  have hq : IsQuatSub K :=
    Sec6Gen.isQuatSub_of_mem_RSet hD.hyp (TC.mem_RSet_of_isPGroup hK (hD.two K hK))
  set EG := Subgroup.normalClosure ({z} : Set G) with hEG_def
  have hEGZ := normalClosure_inf_center_e8 hD hZK hE hK hz
  have hEGmap := map_normalClosure_e8 hD hZK hE hK hz
  have hEG8 : Nat.card EG = 8 := by
    rw [← card_map_mk_eq hEGZ, hEGmap, hE.card]
  have hzEG : z ∈ EG := Subgroup.subset_normalClosure (Set.mem_singleton z)
  obtain ⟨eb, hebE, heb1, hebz⟩ := exists_ne_e8 hE (πc z)
  obtain ⟨gb, hgb⟩ := exists_conj_e8 hD' hE hK' hz' hebE heb1
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) gb
  set t := g * z * g⁻¹ with ht_def
  have hL : conjSub g K ∈ Ω := hD.hyp.conjInvariant g K hK
  have ht : IsUniqueInvolution (conjSub g K) t := hz.conj g
  have ht' := isUniqueInvolution_quot hZK hL ht
  have hπt : πc t = eb := by
    rw [ht_def, map_mul, map_mul, map_inv]
    exact hgb
  have htz' : πc t ≠ πc z := hπt ▸ hebz
  obtain ⟨v', hv'L, hv'z, hv'v, hv'N, hv'KE⟩ :=
    exists_v_e8 hD' hE hK' hz' ⟨_, hL, rfl⟩ ht' htz'
  obtain ⟨v, hvL, rfl⟩ := hv'L
  have hvN : v ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_quot hD hZK hK hv'N
  have hvv : v * v = t := by
    have h1 : πc (v * v * t⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hv'v, mul_inv_cancel]
    have hmem : v * v * t⁻¹ ∈ Subgroup.center G ⊓ conjSub g K :=
      ⟨(QuotientGroup.eq_one_iff _).mp h1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hvL hvL) (Subgroup.inv_mem _ ht.mem)⟩
    rw [hZK _ hL, Subgroup.mem_bot] at hmem
    calc v * v = v * v * t⁻¹ * t := by group
      _ = t := by rw [hmem, one_mul]
  have htEG : t ∈ EG := Subgroup.normalClosure_normal.conj_mem z hzEG g
  have ht1 : t ≠ 1 := ht.ne_one
  set B := Subgroup.zpowers v ⊔ (K ⊔ EG) with hB_def
  have hBmap : B.map πc = Subgroup.zpowers (πc v) ⊔ (K.map πc ⊔ Ē) := by
    rw [hB_def, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, hEGmap]
  have htE' : πc t ∈ Ē := mk_inv_mem_e8 hD hZK hE hK hz g
  have hS' := card_S_e8 hD' hE hK' hz' hv'N hv'v htE' ht'.ne_one hv'KE
  have hKEG := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer (A := K) (B := EG)
    Subgroup.le_normalizer_of_normal
  have hKEG2 : 1 < Nat.card ↥(K ⊓ EG) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro h
    have : z ∈ K ⊓ EG := ⟨hz.mem, hzEG⟩
    rw [h, Subgroup.mem_bot] at this
    exact hz.ne_one this
  rw [hK8, hEG8] at hKEG
  have hvNKEG : Subgroup.zpowers v ≤ Subgroup.normalizer ((K ⊔ EG : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_sup_normal hvN)
  have hBprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hvNKEG
  have hv4 : Nat.card (Subgroup.zpowers v) = 4 := by
    rw [Nat.card_zpowers, orderOf_eq_four_of_sq hvv ht1 ht.sq]
  have hD2 : 1 < Nat.card ↥(Subgroup.zpowers v ⊓ (K ⊔ EG)) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro h
    have : t ∈ Subgroup.zpowers v ⊓ (K ⊔ EG) :=
      ⟨hvv ▸ Subgroup.mul_mem _ (Subgroup.mem_zpowers v) (Subgroup.mem_zpowers v),
        Subgroup.mem_sup_right htEG⟩
    rw [h, Subgroup.mem_bot] at this
    exact ht1 this
  rw [hv4] at hBprod
  have hBle : Nat.card B ≤ 64 := by nlinarith
  have hBge : Nat.card ↥(B.map πc) ≤ Nat.card B :=
    Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective πc B)
  rw [hBmap, hS'] at hBge
  have hbij := (MonoidHom.subgroupMap_surjective πc B).bijective_of_nat_card_le
    (by rw [hBmap, hS']; omega)
  have hBZ : B ⊓ Subgroup.center G = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcB, hcZ⟩
    rw [Subgroup.mem_bot]
    have h1 : MonoidHom.subgroupMap πc B ⟨c, hcB⟩ = MonoidHom.subgroupMap πc B 1 := by
      apply Subtype.ext
      simp only [MonoidHom.subgroupMap_apply_coe, map_one, OneMemClass.coe_one]
      exact (QuotientGroup.eq_one_iff c).mpr hcZ
    exact congrArg Subtype.val (hbij.1 h1)
  set H := B ⊔ Subgroup.center G with hH_def
  have hHidx : H.index = 21 := by
    have hHc : H = (B.map πc).comap πc := by rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [hHc, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have h1 := Subgroup.card_mul_index (B.map πc)
    rw [hBmap, hS', card_e8 hE] at h1
    rw [hBmap]
    omega
  set T : G →* Abelianization ↥H := (Abelianization.of : ↥H →* Abelianization ↥H).transfer
    with hT_def
  have hcommB : commutator ↥H ≤ B.subgroupOf H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro h₁ _ h₂ _
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨b₁, hb₁, c₁, hc₁, he₁⟩ := Subgroup.mem_sup_of_normal_right.mp h₁.2
    obtain ⟨b₂, hb₂, c₂, hc₂, he₂⟩ := Subgroup.mem_sup_of_normal_right.mp h₂.2
    have : ((⁅h₁, h₂⁆ : ↥H) : G) = ⁅(h₁ : G), (h₂ : G)⁆ := by
      simp [commutatorElement_def]
    rw [this, ← he₁, ← he₂, commutatorElement_mul_central hc₁ hc₂, commutatorElement_def]
    exact B.mul_mem (B.mul_mem (B.mul_mem hb₁ hb₂) (B.inv_mem hb₁)) (B.inv_mem hb₂)
  have hZ2 := isPGroup_center_of_oddCore hD.odd
  have hTZ : ∀ c ∈ Subgroup.center G, T c = 1 → c = 1 := by
    intro c hc hTc
    have hkey : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * c ^ k * g₀ ∈ H → g₀⁻¹ * c ^ k * g₀ = c ^ k := by
      intro k g₀ _
      have := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hc k) g₀
      rw [mul_assoc, ← this, ← mul_assoc, inv_mul_cancel, one_mul]
    have h1 := MonoidHom.transfer_eq_pow (Abelianization.of : ↥H →* Abelianization ↥H) c hkey
    rw [← hT_def, hTc] at h1
    have hmem : c ^ H.index ∈ H := MonoidHom.transfer_eq_pow_aux c hkey
    have h2 : (⟨c ^ H.index, hmem⟩ : ↥H) ∈ commutator ↥H := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      exact h1.symm
    have h3 : c ^ 21 ∈ B := by
      have h' : c ^ H.index ∈ B := Subgroup.mem_subgroupOf.mp (hcommB h2)
      rwa [hHidx] at h'
    have h4 : c ^ 21 ∈ B ⊓ Subgroup.center G := ⟨h3, Subgroup.pow_mem _ hc 21⟩
    rw [hBZ, Subgroup.mem_bot] at h4
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hZ2 ⟨c, hc⟩
    rw [Subgroup.orderOf_mk] at hk
    have h5 : orderOf c ∣ 21 := orderOf_dvd_of_pow_eq_one h4
    rw [hk] at h5
    have h6 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 21)) h5
    rw [h6] at hk
    exact orderOf_eq_one_iff.mp hk
  obtain ⟨xb, -, hx3, hxN, hxc⟩ := exists_three_e8 hD' hE hK' hz'
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) xb
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_quot hD hZK hK hxN
  have hy3 : ∀ k ∈ K, y ^ 3 * k = k * y ^ 3 := by
    intro k _
    have h1 : πc (y ^ 3) = 1 := by rw [map_pow, ← hx3, pow_orderOf_eq_one]
    exact (Subgroup.mem_center_iff.mp ((QuotientGroup.eq_one_iff _).mp h1) k).symm
  have hyc : ¬ ∀ k ∈ K, y * k = k * y := by
    intro h
    apply hxc
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul, h k hk]
  have hKT : K ≤ T.ker := le_ker_of_three T hq hK8 hz hyN hy3 hyc
  have hGT : (⊤ : Subgroup G) ≤ T.ker := by
    rw [← hD.gen]
    refine pSpan_le fun L hL => ?_
    obtain ⟨a, rfl⟩ := hD.trans K hK L hL
    intro x hx
    rw [mem_conjSub_iff] at hx
    have : x = a * (a⁻¹ * x * a) * a⁻¹ := by group
    rw [this]
    exact (MonoidHom.normal_ker T).conj_mem _ (hKT hx) a
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  exact hTZ c hc (hGT (Subgroup.mem_top c))

end Lift

theorem dLeafZ8_holds (r : ℕ) (IH : ℕ → Prop) : DLeafZ8 r IH :=
  fun _ _ _ _ hc hZK _ hE => center_eq_bot_of_e8 hc.toThmDHyp hZK hE

theorem thmDAbs_of_leaves₃ {r : ℕ} {IH : ℕ → Prop} (hC : DLeafC r IH) (hE4 : DLeafE4 r IH)
    (hstar : DLeafStar r IH) (hend : DLeafEnd r IH) (hih : ∀ n, IH n) : ThmDAbs r :=
  thmDAbs_of_leaves₂ (dLeafZ8_holds r IH) hC hE4 hstar hend hih

section Cit3

theorem thmD2Step_of_leaves₂ {r : ℕ} (hC : DLeafC r (PackIH r)) (hE4 : DLeafE4 r (PackIH r))
    (hstar : DLeafStar r (PackIH r)) (hend : DLeafEnd r (PackIH r)) (n : ℕ) :
    CIT3Below n → TL4.TightBelowRPlus r n → ThmDAbsBelow r (n + 1) :=
  thmD2Step_of_leaves (dLeafZ8_holds r _) hC hE4 hstar hend n

end Cit3

end CFSG.ClassicalInvolution.Q3.TC.Thin
