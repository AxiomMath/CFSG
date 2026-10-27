module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Aut
public import CFSG.CharacterTheory.Burnside
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup
open scoped commutatorElement

theorem eq_one_of_mem_zpowers_of_isPGroup_two {G : Type*} [Group G] {M : Subgroup G}
    (hM : IsPGroup 2 M) {x : G} (hx5 : x ^ 5 = 1) {y : G} (hyM : y ∈ M)
    (hyx : y ∈ Subgroup.zpowers x) : y = 1 := by
  obtain ⟨k, hk⟩ := hM ⟨y, hyM⟩
  have hk' : y ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf y ∣ 5 :=
    (orderOf_dvd_of_mem_zpowers hyx).trans (orderOf_dvd_of_pow_eq_one hx5)
  have hcop : Nat.Coprime (2 ^ k) 5 := Nat.Coprime.pow_left k (by norm_num)
  have h3 : orderOf y ∣ Nat.gcd (2 ^ k) 5 := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one hcop] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem normal_eq_bot_of_fixes {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] [FaithfulSMul G Ω]
    [MulAction.IsPretransitive G Ω] {K : Subgroup G} [K.Normal] (α : Ω) (hα : ∀ k ∈ K, k • α = α) :
    K = ⊥ := by
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  apply eq_of_smul_eq_smul (α := Ω)
  intro β
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G α β
  have hconj : g⁻¹ * k * g ∈ K := by
    have := Subgroup.Normal.conj_mem inferInstance k hk g⁻¹
    simpa using this
  have e : g * (g⁻¹ * k * g) = k * g := by group
  calc k • g • α = (k * g) • α := (mul_smul k g α).symm
    _ = (g * (g⁻¹ * k * g)) • α := by rw [e]
    _ = g • ((g⁻¹ * k * g) • α) := mul_smul _ _ _
    _ = g • α := by rw [hα _ hconj]
    _ = (1 : G) • g • α := (one_smul G _).symm

theorem normal_five_eq_bot {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] [Finite Ω]
    [FaithfulSMul G Ω] [MulAction.IsPretransitive G Ω] (hΩ : Nat.card Ω = 16)
    {K : Subgroup G} [K.Normal] (hK : IsPGroup 5 K) : K = ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmod := hK.card_modEq_card_fixedPoints Ω
  rw [hΩ] at hmod
  have hne : Nat.card (MulAction.fixedPoints K Ω) ≠ 0 := by
    intro h
    rw [h] at hmod
    exact absurd hmod (by decide)
  obtain ⟨α, hα⟩ := (Nat.card_ne_zero.1 hne).1
  exact normal_eq_bot_of_fixes (α : Ω) fun k hk => MulAction.mem_fixedPoints.1 hα ⟨k, hk⟩

@[expose] def twoTorsionSub {G : Type*} [Group G] (A : Subgroup G)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Subgroup G where
  carrier := {a | a ∈ A ∧ a * a = 1}
  one_mem' := ⟨A.one_mem, mul_one 1⟩
  mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hA b hb.1 a ha.1]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha.2, hb.2, mul_one]⟩
  inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by
    calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
      _ = 1 := by rw [ha.2, inv_one]⟩

theorem twoTorsionSub_normal {G : Type*} [Group G] {A : Subgroup G} [A.Normal]
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : (twoTorsionSub A hA).Normal :=
  ⟨fun n hn g => ⟨Subgroup.Normal.conj_mem inferInstance n hn.1 g, by
    calc g * n * g⁻¹ * (g * n * g⁻¹) = g * (n * n) * g⁻¹ := by group
      _ = 1 := by rw [hn.2]; group⟩⟩

theorem exists_abelian_normal_of_isSolvable {G : Type*} [Group G] [Group.IsSolvable G] [Nontrivial G] :
    ∃ A : Subgroup G, A.Normal ∧ A ≠ ⊥ ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  classical
  have hex : ∃ n, derivedSeries G n = ⊥ := Group.IsSolvable.solvable
  have hm : derivedSeries G (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, derivedSeries_zero] at hm
    exact top_ne_bot hm
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨derivedSeries G k, derivedSeries_normal G k, ?_, ?_⟩
  · exact Nat.find_min hex (by omega : k < Nat.find hex)
  · intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ ⁅derivedSeries G k, derivedSeries G k⁆ := commutator_mem_commutator ha hb
    rw [← derivedSeries_succ, ← hk, hm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem card_eq_two_pow_mul_five {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]
    [MulAction.IsPretransitive G Ω] (hΩ : Nat.card Ω = 16) (ω : Ω)
    (hS : Nat.card (MulAction.stabilizer G ω) = 20) : Nat.card G = 2 ^ 6 * 5 ^ 1 := by
  have h := (MulAction.stabilizer G ω).card_mul_index
  rw [MulAction.index_stabilizer_of_transitive, hΩ, hS] at h
  rw [← h]
  norm_num

theorem isSolvable_of_stabilizer_card {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]
    [MulAction.IsPretransitive G Ω] (hΩ : Nat.card Ω = 16) (ω : Ω)
    (hS : Nat.card (MulAction.stabilizer G ω) = 20) : Group.IsSolvable G := by
  haveI := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_five (by norm_num)
    (by rw [← Nat.card_eq_fintype_card]; exact card_eq_two_pow_mul_five hΩ ω hS)

theorem exists_normal_elementary_two {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]
    [Finite Ω] [FaithfulSMul G Ω] [MulAction.IsPretransitive G Ω] (hΩ : Nat.card Ω = 16) (ω : Ω)
    (hS : Nat.card (MulAction.stabilizer G ω) = 20) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧
      ∀ a ∈ N, a * a = 1 := by
  haveI := isSolvable_of_stabilizer_card hΩ ω hS
  have hG : Nat.card G = 2 ^ 6 * 5 ^ 1 := card_eq_two_pow_mul_five hΩ ω hS
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 (by rw [hG]; norm_num)
  obtain ⟨A, hAn, hAne, hAab⟩ := exists_abelian_normal_of_isSolvable (G := G)
  refine ⟨twoTorsionSub A hAab, twoTorsionSub_normal hAab, ?_,
    fun a ha b hb => hAab a ha.1 b hb.1, fun a ha => ha.2⟩
  intro hbot
  have h2 : ¬ 2 ∣ Nat.card A := by
    intro hdvd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have ha2 : a ^ 2 = 1 := by
      have := pow_orderOf_eq_one a
      rwa [ha] at this
    have haA : (a : G) ∈ twoTorsionSub A hAab := by
      refine ⟨a.2, ?_⟩
      have := congrArg Subtype.val ha2
      simpa [pow_two] using this
    rw [hbot, Subgroup.mem_bot] at haA
    have : a = 1 := Subtype.ext haA
    rw [this, orderOf_one] at ha
    omega
  have hdvd : Nat.card A ∣ 2 ^ 6 * 5 ^ 1 := hG ▸ Subgroup.card_subgroup_dvd_card A
  have hcop : Nat.Coprime (Nat.card A) (2 ^ 6) :=
    Nat.Coprime.pow_right 6 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2).symm
  have h5 : Nat.card A ∣ 5 := by simpa using hcop.dvd_of_dvd_mul_left hdvd
  rcases (Nat.dvd_prime Nat.prime_five).1 h5 with h1 | h5'
  · exact hAne (Subgroup.eq_bot_of_card_eq A h1)
  · have hP : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by rw [h5']; norm_num)
    exact hAne (normal_five_eq_bot hΩ hP)

theorem normal_two_regular {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] (ω : Ω) {x : G}
    (hx5 : x ^ 5 = 1) (hnorm : ∀ g ∈ MulAction.stabilizer G ω, g * x * g⁻¹ ∈ Subgroup.zpowers x)
    (hcent : ∀ g ∈ MulAction.stabilizer G ω, g * x = x * g → g ∈ Subgroup.zpowers x)
    {M : Subgroup G} [M.Normal] (hM : IsPGroup 2 M) : ∀ m ∈ M, m • ω = ω → m = 1 := by
  intro n hnM hnω
  have hnS : n ∈ MulAction.stabilizer G ω := MulAction.mem_stabilizer_iff.2 hnω
  have h1 : n * x * n⁻¹ * x⁻¹ ∈ Subgroup.zpowers x :=
    Subgroup.mul_mem _ (hnorm n hnS) (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have h2 : n * x * n⁻¹ * x⁻¹ ∈ M := by
    have : n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) := by group
    rw [this]
    exact M.mul_mem hnM (Subgroup.Normal.conj_mem inferInstance n⁻¹ (M.inv_mem hnM) x)
  have h3 : n * x * n⁻¹ * x⁻¹ = 1 := eq_one_of_mem_zpowers_of_isPGroup_two hM hx5 h2 h1
  have h4 : n * x = x * n :=
    calc n * x = (n * x * n⁻¹ * x⁻¹) * x * n := by group
      _ = x * n := by rw [h3]; group
  exact eq_one_of_mem_zpowers_of_isPGroup_two hM hx5 hnM (hcent n hnS h4)

theorem normal_two_transitive {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] [Finite Ω]
    [FaithfulSMul G Ω] [MulAction.IsPretransitive G Ω] (hΩ : Nat.card Ω = 16) (ω : Ω) {x : G}
    (hx5 : x ^ 5 = 1) (hxω : x • ω = ω) (hfix : ∀ α : Ω, x • α = α → α = ω)
    {M : Subgroup G} [M.Normal] (hM : IsPGroup 2 M) (hne : M ≠ ⊥) :
    ∀ α : Ω, ∃ m ∈ M, m • ω = α := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxB : ∀ α ∈ MulAction.orbit M ω, x • α ∈ MulAction.orbit M ω := by
    intro α hα
    obtain ⟨m, rfl⟩ := MulAction.mem_orbit_iff.1 hα
    refine MulAction.mem_orbit_iff.2
      ⟨⟨x * (m : G) * x⁻¹, Subgroup.Normal.conj_mem inferInstance (m : G) m.2 x⟩, ?_⟩
    show (x * (m : G) * x⁻¹) • ω = x • ((m : G) • ω)
    rw [mul_smul, mul_smul, inv_smul_eq_iff.2 hxω.symm]
  let f : MulAction.orbit M ω → MulAction.orbit M ω := fun b => ⟨x • (b : Ω), hxB _ b.2⟩
  have hf : ∀ n : ℕ, ∀ b, ((f^[n] b : MulAction.orbit M ω) : Ω) = (x ^ n) • (b : Ω) := by
    intro n
    induction n with
    | zero => intro b; simp
    | succ n ih =>
      intro b
      rw [Function.iterate_succ_apply', pow_succ']
      change x • ((f^[n] b : MulAction.orbit M ω) : Ω) = (x * x ^ n) • (b : Ω)
      rw [ih, mul_smul]
  have hf5 : ∀ b, f^[5] b = b := by
    intro b
    apply Subtype.ext
    rw [hf, hx5, one_smul]
  have hmod := card_modEq_five_fixed f hf5
  have hfixf : Function.fixedPoints f = {⟨ω, MulAction.mem_orbit_self ω⟩} := by
    ext b
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, Set.mem_singleton_iff]
    constructor
    · intro h
      exact Subtype.ext (hfix b (congrArg Subtype.val h))
    · intro h
      rw [h]
      exact Subtype.ext hxω
  rw [hfixf, Set.ncard_singleton] at hmod
  obtain ⟨n, hn⟩ := hM.card_orbit ω
  have hle : Nat.card (MulAction.orbit M ω) ≤ 16 := by
    rw [← hΩ]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  rw [hn] at hmod hle
  have hn4 : n ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn' : n = 0 ∨ n = 4 := by
    interval_cases n <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hmod; decide)
  rcases hn' with rfl | rfl
  · exfalso
    apply hne
    have hsub : Subsingleton (MulAction.orbit M ω) :=
      (Nat.card_eq_one_iff_unique.1 (by rw [hn]; rfl)).1
    refine normal_eq_bot_of_fixes ω fun m hm => ?_
    have := hsub.elim ⟨m • ω, MulAction.mem_orbit_iff.2 ⟨⟨m, hm⟩, rfl⟩⟩
      ⟨ω, MulAction.mem_orbit_self ω⟩
    exact congrArg Subtype.val this
  · intro α
    have hbij : Function.Bijective (Subtype.val : MulAction.orbit M ω → Ω) :=
      Subtype.val_injective.bijective_of_nat_card_le (by simp [hn, hΩ])
    obtain ⟨b, hb⟩ := hbij.2 α
    obtain ⟨m, hm⟩ := MulAction.mem_orbit_iff.1 b.2
    exact ⟨m, m.2, hm.trans hb⟩

theorem card_normal_two {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] [Finite Ω]
    [FaithfulSMul G Ω] [MulAction.IsPretransitive G Ω] (hΩ : Nat.card Ω = 16) (ω : Ω) {x : G}
    (hx5 : x ^ 5 = 1) (hxω : x • ω = ω) (hfix : ∀ α : Ω, x • α = α → α = ω)
    (hnorm : ∀ g ∈ MulAction.stabilizer G ω, g * x * g⁻¹ ∈ Subgroup.zpowers x)
    (hcent : ∀ g ∈ MulAction.stabilizer G ω, g * x = x * g → g ∈ Subgroup.zpowers x)
    {M : Subgroup G} [M.Normal] (hM : IsPGroup 2 M) (hne : M ≠ ⊥) : Nat.card M = 16 := by
  have htr := normal_two_transitive hΩ ω hx5 hxω hfix hM hne
  have hreg := normal_two_regular ω hx5 hnorm hcent hM
  let f : M → Ω := fun m => (m : G) • ω
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : (b : G)⁻¹ * a = 1 := by
      refine hreg _ (M.mul_mem (M.inv_mem b.2) a.2) ?_
      rw [mul_smul]
      change (b : G)⁻¹ • ((a : G) • ω) = ω
      rw [show (a : G) • ω = (b : G) • ω from hab, inv_smul_smul]
    exact Subtype.ext (inv_mul_eq_one.1 h1).symm
  have hsurj : Function.Surjective f := fun α => by
    obtain ⟨m, hm, rfl⟩ := htr α
    exact ⟨⟨m, hm⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), hΩ]

theorem exists_regular_normal_two {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] [Finite Ω]
    [FaithfulSMul G Ω] [MulAction.IsPretransitive G Ω] (hΩ : Nat.card Ω = 16) (ω : Ω)
    (hS : Nat.card (MulAction.stabilizer G ω) = 20) {x : G} (hx5 : x ^ 5 = 1) (hxω : x • ω = ω)
    (hfix : ∀ α : Ω, x • α = α → α = ω)
    (hnorm : ∀ g ∈ MulAction.stabilizer G ω, g * x * g⁻¹ ∈ Subgroup.zpowers x)
    (hcent : ∀ g ∈ MulAction.stabilizer G ω, g * x = x * g → g ∈ Subgroup.zpowers x) :
    ∃ R : Subgroup G, R.Normal ∧ IsPGroup 2 R ∧ Nat.card R = 16 ∧
      (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧ (∀ a ∈ R, a * a = 1) ∧
      (∀ α β : Ω, ∃ r ∈ R, r • α = β) ∧ (∀ r ∈ R, r • ω = ω → r = 1) ∧
      (∀ M : Subgroup G, M.Normal → IsPGroup 2 M → M ≤ R) := by
  obtain ⟨N, hNn, hNne, hNab, hN2⟩ := exists_normal_elementary_two hΩ ω hS
  haveI := hNn
  have hNP : IsPGroup 2 N := fun g => ⟨1, Subtype.ext (by simpa [pow_two] using hN2 g g.2)⟩
  have htr := normal_two_transitive hΩ ω hx5 hxω hfix hNP hNne
  refine ⟨N, hNn, hNP, card_normal_two hΩ ω hx5 hxω hfix hnorm hcent hNP hNne, hNab, hN2, ?_,
    normal_two_regular ω hx5 hnorm hcent hNP, ?_⟩
  · intro α β
    obtain ⟨s, hs, rfl⟩ := htr α
    obtain ⟨t, ht, rfl⟩ := htr β
    exact ⟨t * s⁻¹, N.mul_mem ht (N.inv_mem hs), by rw [mul_smul, inv_smul_smul]⟩
  · intro M hMn hM2
    haveI := hMn
    haveI : (M ⊔ N).Normal := inferInstance
    have hK2 : IsPGroup 2 (M ⊔ N : Subgroup G) := hM2.to_sup_of_normal_right hNP
    have hKne : (M ⊔ N : Subgroup G) ≠ ⊥ := fun h => hNne (le_bot_iff.1 (h ▸ le_sup_right))
    have hKcard := card_normal_two hΩ ω hx5 hxω hfix hnorm hcent hK2 hKne
    have hNcard := card_normal_two hΩ ω hx5 hxω hfix hnorm hcent hNP hNne
    have hNK : N = M ⊔ N :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hKcard, hNcard])
    exact hNK ▸ le_sup_left

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
