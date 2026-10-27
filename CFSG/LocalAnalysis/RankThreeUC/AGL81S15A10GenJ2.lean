module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace A10GenJ2

open Equiv Equiv.Perm

theorem card_modEq_five {Y : Type*} [Group Y] (K : Subgroup Y) [Finite K] (x : Y) (hx : x ^ 5 = 1)
    (hK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) :
    Nat.card K ≡ Nat.card ↥((Subgroup.centralizer {x}).subgroupOf K) [MOD 5] := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let f : Function.End K := fun k => ⟨x * k * x⁻¹, hK k k.2⟩
  have hfn : ∀ n : ℕ, ∀ k : K, ((f ^ n) k : Y) = x ^ n * k * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro k; simp; rfl
    | succ n ih =>
      intro k
      rw [pow_succ]
      show (((f ^ n) (f k) : K) : Y) = _
      rw [ih]
      simp [f, pow_succ, mul_assoc]
  have hf : f ^ 5 ^ 1 = 1 := by
    funext k
    apply Subtype.ext
    rw [pow_one, hfn, hx]
    simp
    rfl
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  have hcard : Nat.card ↥(Function.fixedPoints f) =
      Nat.card ↥((Subgroup.centralizer {x}).subgroupOf K) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun k => ?_)
    simp [f, Function.mem_fixedPoints, Function.IsFixedPt, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff, Subtype.ext_iff]
    exact mul_inv_eq_iff_eq_mul
  rw [hcard] at h
  exact h

theorem not_sixteen_dvd_card_centralizer (σ : Perm (Fin 10)) (h5 : σ ^ 5 = 1) (h1 : σ ≠ 1) :
    ¬ 16 ∣ Nat.card (Subgroup.centralizer {σ}) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf σ = 5 := orderOf_eq_prime h5 h1
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_five)
  rw [hord] at hm
  have hsum : σ.cycleType.sum = (m + 1) * 5 := by
    rw [hm, Multiset.sum_replicate, smul_eq_mul]
  have hle : σ.cycleType.sum ≤ 10 := by
    rw [Equiv.Perm.sum_cycleType]
    simpa using Finset.card_le_univ σ.support
  have hm01 : m = 0 ∨ m = 1 := by omega
  rw [Equiv.Perm.nat_card_centralizer]
  rcases hm01 with rfl | rfl
  · rw [hm]
    decide
  · rw [hm]
    decide

theorem free_of_perm {G : Type*} [Group G] [Finite G] (ρ : G →* Perm (Fin 10))
    (hρ : Function.Injective ρ) (E : Subgroup G) (hE16 : Nat.card E = 16) (x : G)
    (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) (hxE : ∀ e ∈ E, x * e * x⁻¹ ∈ E) :
    ∀ e ∈ E, x * e * x⁻¹ = e → e = 1 := by
  have hmod := card_modEq_five E x hx5 hxE
  rw [hE16] at hmod
  have hdvd : Nat.card ↥((Subgroup.centralizer {x}).subgroupOf E) ∣ 16 :=
    hE16 ▸ Subgroup.card_subgroup_dvd_card _
  have hc : Nat.card ↥((Subgroup.centralizer {x}).subgroupOf E) = 1 ∨
      Nat.card ↥((Subgroup.centralizer {x}).subgroupOf E) = 16 := by
    generalize Nat.card ↥((Subgroup.centralizer {x}).subgroupOf E) = c at hmod hdvd
    have hle : c ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases c <;>
      first | omega | (exfalso; revert hdvd; decide) | (exfalso; revert hmod; decide)
  rcases hc with h1 | h16
  · intro e he hcomm
    have hmem : (⟨e, he⟩ : E) ∈ (Subgroup.centralizer {x}).subgroupOf E := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.1 hcomm).symm
    rw [Subgroup.eq_bot_of_card_eq _ h1, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    have htop : (Subgroup.centralizer {x}).subgroupOf E = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [h16, hE16])
    have hcen : E.map ρ ≤ Subgroup.centralizer {ρ x} := by
      rintro _ ⟨e, he, rfl⟩
      have : (⟨e, he⟩ : E) ∈ (Subgroup.centralizer {x}).subgroupOf E := by rw [htop]; trivial
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at this
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg ρ this
    have h16' : 16 ∣ Nat.card (Subgroup.centralizer {ρ x}) := by
      have := Subgroup.card_dvd_of_le hcen
      rwa [Subgroup.card_map_of_injective hρ, hE16] at this
    refine not_sixteen_dvd_card_centralizer (ρ x) (by rw [← map_pow, hx5, map_one]) ?_ h16'
    intro h
    exact hx1 (hρ (by rw [h, map_one]))

theorem not_smul_mem_orbit {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] [Fintype Ω]
    (hΩ : Fintype.card Ω < 16) (E : Subgroup G) (hE16 : Nat.card E = 16)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (y : G) (hy5 : y ^ 5 = 1)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) (hyE' : ∀ e ∈ E, y⁻¹ * e * y ∈ E)
    (hfree : ∀ e ∈ E, y * e * y⁻¹ = e → e = 1) (ω : Ω) (hω : ∃ e ∈ E, e • ω ≠ ω)
    (e₀ : G) (he₀ : e₀ ∈ E) (h : y • ω = e₀ • ω) : False := by
  set K : Subgroup G := E ⊓ MulAction.stabilizer G ω with hKdef
  have hKE : K ≤ E := inf_le_left
  have hmemK : ∀ k, k ∈ K ↔ k ∈ E ∧ k • ω = ω := fun k => by
    simp [hKdef, MulAction.mem_stabilizer_iff]
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : G, e₁ = y⁻¹ * e₀⁻¹ * y := ⟨_, rfl⟩
  have he₁E : e₁ ∈ E := he₁ ▸ hyE' _ (E.inv_mem he₀)
  have hfixω : (e₀⁻¹ * y) • ω = ω := by
    rw [mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
  have hinv : y⁻¹ • ω = e₁ • ω := by
    conv_lhs => rw [← hfixω]
    rw [← mul_smul, he₁, mul_assoc]
  have hK : ∀ k ∈ K, y * k * y⁻¹ ∈ K := by
    intro k hk
    obtain ⟨hkE, hkω⟩ := (hmemK k).1 hk
    refine (hmemK _).2 ⟨hyE k hkE, ?_⟩
    calc (y * k * y⁻¹) • ω = y • (k • (y⁻¹ • ω)) := by simp [mul_smul]
      _ = y • (k • (e₁ • ω)) := by rw [hinv]
      _ = y • ((k * e₁) • ω) := by rw [mul_smul]
      _ = y • ((e₁ * k) • ω) := by rw [hEc k hkE e₁ he₁E]
      _ = y • (e₁ • (k • ω)) := by rw [mul_smul]
      _ = y • (e₁ • ω) := by rw [hkω]
      _ = y • (y⁻¹ • ω) := by rw [hinv]
      _ = ω := smul_inv_smul y ω
  have hmod := card_modEq_five K y hy5 hK
  have hbot : (Subgroup.centralizer {y}).subgroupOf K = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hk
    rw [Subgroup.mem_bot]
    refine Subtype.ext (hfree _ (hKE k.2) ?_)
    exact mul_inv_eq_iff_eq_mul.2 hk.symm
  rw [hbot, Subgroup.card_bot] at hmod
  have hdvdK : Nat.card K ∣ 16 := hE16 ▸ Subgroup.card_dvd_of_le hKE
  have hc : Nat.card K = 1 ∨ Nat.card K = 16 := by
    generalize Nat.card K = c at hmod hdvdK
    have hle : c ≤ 16 := Nat.le_of_dvd (by norm_num) hdvdK
    interval_cases c <;>
      first | omega | (exfalso; revert hdvdK; decide) | (exfalso; revert hmod; decide)
  rcases hc with h1 | h16
  · have hKbot : K = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hinj : Function.Injective (fun e : E => (e : G) • ω) := by
      intro a b hab
      have hab' : (a : G) • ω = (b : G) • ω := hab
      have : ((a : G)⁻¹ * b) ∈ K := by
        refine (hmemK _).2 ⟨E.mul_mem (E.inv_mem a.2) b.2, ?_⟩
        rw [mul_smul, ← hab', inv_smul_smul]
      rw [hKbot, Subgroup.mem_bot] at this
      exact Subtype.ext (inv_mul_eq_one.1 this)
    have := Nat.card_le_card_of_injective _ hinj
    rw [hE16, Nat.card_eq_fintype_card] at this
    omega
  · have hKeq : K = E := Subgroup.eq_of_le_of_card_ge hKE (by rw [h16, hE16])
    obtain ⟨e, he, hne⟩ := hω
    have : e ∈ K := hKeq ▸ he
    exact hne ((hmemK e).1 this).2

theorem not_pow_smul_mem_orbit {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]
    [Fintype Ω] (hΩ : Fintype.card Ω < 16) (E : Subgroup G) (hE16 : Nat.card E = 16)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (x : G) (hx5 : x ^ 5 = 1)
    (hxE : ∀ n : ℕ, ∀ e ∈ E, x ^ n * e * (x ^ n)⁻¹ ∈ E)
    (hfree : ∀ e ∈ E, x * e * x⁻¹ = e → e = 1) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (ω : Ω) (hω : ∃ e ∈ E, e • ω ≠ ω) (e₀ : G) (he₀ : e₀ ∈ E) : x ^ m • ω ≠ e₀ • ω := by
  intro h
  obtain ⟨t, ht⟩ : ∃ t : ℕ, m * t % 5 = 1 := by
    interval_cases m
    · exact ⟨1, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨4, by norm_num⟩
  have hxt : (x ^ m) ^ t = x := by
    rw [← pow_mul]
    have : m * t = 5 * (m * t / 5) + 1 := by omega
    rw [this, pow_add, pow_mul, hx5, one_pow, one_mul, pow_one]
  have hyz : x ^ m * x ^ (4 * m) = 1 := by
    rw [← pow_add, show m + 4 * m = 5 * m by ring, pow_mul, hx5, one_pow]
  refine not_smul_mem_orbit hΩ E hE16 hEc (x ^ m) ?_ (hxE m) ?_ ?_ ω hω e₀ he₀ h
  · rw [← pow_mul, mul_comm, pow_mul, hx5, one_pow]
  · intro e he
    have := hxE (4 * m) e he
    rwa [eq_inv_of_mul_eq_one_right hyz, inv_inv] at this
  · intro e he hcomm
    have hc : Commute (x ^ m) e := (mul_inv_eq_iff_eq_mul.1 hcomm)
    have hc' : Commute ((x ^ m) ^ t) e := hc.pow_left t
    rw [hxt] at hc'
    exact hfree e he (mul_inv_eq_iff_eq_mul.2 hc')

theorem exists_cover {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] [Fintype Ω]
    (hΩ : Fintype.card Ω = 10) (E : Subgroup G) (hE16 : Nat.card E = 16)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (x : G) (hx5 : x ^ 5 = 1)
    (hxE : ∀ n : ℕ, ∀ e ∈ E, x ^ n * e * (x ^ n)⁻¹ ∈ E)
    (hfree : ∀ e ∈ E, x * e * x⁻¹ = e → e = 1) (ω₀ : Ω) (hω₀ : ∃ e ∈ E, e • ω₀ ≠ ω₀) :
    ∀ ω : Ω, ∃ k : ℕ, ∃ e ∈ E, ω = (e * x ^ k) • ω₀ := by
  classical
  have hmoved : ∀ k : ℕ, ∃ e ∈ E, e • (x ^ k • ω₀) ≠ x ^ k • ω₀ := by
    intro k
    obtain ⟨e, he, hne⟩ := hω₀
    refine ⟨x ^ k * e * (x ^ k)⁻¹, hxE k e he, fun h => hne ?_⟩
    have h' : (x ^ k * e * (x ^ k)⁻¹) • (x ^ k • ω₀) = x ^ k • (e • ω₀) := by
      simp [mul_smul]
    rw [h'] at h
    exact (MulAction.injective (x ^ k)) h
  have hnot : ∀ j k : ℕ, j < k → k < 5 → ∀ e ∈ E, e • (x ^ j • ω₀) ≠ x ^ k • ω₀ := by
    intro j k hjk hk5 e he h
    have hm := not_pow_smul_mem_orbit (by omega) E hE16 hEc x hx5 hxE hfree (m := k - j)
      (by omega) (by omega) (x ^ j • ω₀) (hmoved j) e he
    apply hm
    rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hjk.le]
    exact h.symm
  let O : ℕ → Finset Ω := fun k => Finset.univ.filter (fun ω => ∃ e ∈ E, e • (x ^ k • ω₀) = ω)
  have hO2 : ∀ k, 2 ≤ (O k).card := by
    intro k
    obtain ⟨e, he, hne⟩ := hmoved k
    have : 1 < (O k).card := by
      rw [Finset.one_lt_card]
      refine ⟨x ^ k • ω₀, ?_, e • (x ^ k • ω₀), ?_, fun h => hne h.symm⟩
      · simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨1, E.one_mem, one_smul _ _⟩
      · simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, he, rfl⟩
    omega
  have hsymm : ∀ j k : ℕ, j < k → k < 5 → ∀ ω, ω ∈ O j → ω ∈ O k → False := by
    intro j k hjk hk5 ω hj hk
    simp only [O, Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
    obtain ⟨e, he, rfl⟩ := hj
    obtain ⟨e', he', hee'⟩ := hk
    refine hnot j k hjk hk5 (e'⁻¹ * e) (E.mul_mem (E.inv_mem he') he) ?_
    rw [mul_smul, ← hee', inv_smul_smul]
  have hdisj : (↑(Finset.range 5) : Set ℕ).PairwiseDisjoint O := by
    intro j hj k hk hjk
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    rw [Function.onFun, Finset.disjoint_left]
    rcases Nat.lt_or_gt_of_ne hjk with h | h
    · exact fun ω hωj hωk => hsymm j k h hk ω hωj hωk
    · exact fun ω hωj hωk => hsymm k j h hj ω hωk hωj
  have hcard : ((Finset.range 5).biUnion O).card = Fintype.card Ω := by
    refine le_antisymm (by simpa using Finset.card_le_univ _) ?_
    rw [Finset.card_biUnion hdisj, hΩ]
    calc 10 = ∑ _k ∈ Finset.range 5, 2 := by simp
      _ ≤ ∑ k ∈ Finset.range 5, (O k).card := Finset.sum_le_sum fun k _ => hO2 k
  intro ω
  have hω : ω ∈ (Finset.range 5).biUnion O := by
    rw [Finset.eq_univ_of_card _ hcard]; exact Finset.mem_univ _
  rw [Finset.mem_biUnion] at hω
  obtain ⟨k, -, hk⟩ := hω
  simp only [O, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  obtain ⟨e, he, rfl⟩ := hk
  exact ⟨k, e, he, by rw [mul_smul]⟩

theorem E_le_oddHull {G : Type} [Group G] [Finite G] (P E : Subgroup G) (hEP : E ≤ P)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (x : G) (hxP : x ∈ P) (hxodd : Odd (orderOf x))
    (hxE : ∀ e ∈ E, x * e * x⁻¹ ∈ E) (hfree : ∀ e ∈ E, x * e * x⁻¹ = e → e = 1) :
    E ≤ oddHull P := by
  let φ : E → E := fun e => ⟨e * (x * e * x⁻¹)⁻¹, E.mul_mem e.2 (E.inv_mem (hxE e e.2))⟩
  have hinj : Function.Injective φ := by
    rintro ⟨a, haE⟩ ⟨b, hbE⟩ hab
    have hab' : a * (x * a * x⁻¹)⁻¹ = b * (x * b * x⁻¹)⁻¹ := congrArg Subtype.val hab
    have huE : x * a * x⁻¹ ∈ E := hxE a haE
    have hvE : x * b * x⁻¹ ∈ E := hxE b hbE
    have ha : a = b * (x * b * x⁻¹)⁻¹ * (x * a * x⁻¹) := mul_inv_eq_iff_eq_mul.1 hab'
    have hcb : b * ((x * b * x⁻¹)⁻¹ * (x * a * x⁻¹)) = ((x * b * x⁻¹)⁻¹ * (x * a * x⁻¹)) * b :=
      hEc _ hbE _ (E.mul_mem (E.inv_mem hvE) huE)
    have h2 : a * b⁻¹ = (x * b * x⁻¹)⁻¹ * (x * a * x⁻¹) := by
      calc a * b⁻¹ = b * ((x * b * x⁻¹)⁻¹ * (x * a * x⁻¹)) * b⁻¹ := by
            rw [← mul_assoc, ← ha]
        _ = (x * b * x⁻¹)⁻¹ * (x * a * x⁻¹) := by rw [hcb, mul_inv_cancel_right]
    have h3 : x * (a * b⁻¹) * x⁻¹ = a * b⁻¹ := by
      calc x * (a * b⁻¹) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹)⁻¹ := by group
        _ = (x * b * x⁻¹)⁻¹ * (x * a * x⁻¹) := hEc _ huE _ (E.inv_mem hvE)
        _ = a * b⁻¹ := h2.symm
    exact Subtype.ext (mul_inv_eq_one.1 (hfree _ (E.mul_mem haE (E.inv_mem hbE)) h3))
  have hsurj : Function.Surjective φ := Finite.injective_iff_surjective.1 hinj
  intro e he
  obtain ⟨⟨a, haE⟩, ha⟩ := hsurj ⟨e, he⟩
  have hval : a * (x * a * x⁻¹)⁻¹ = e := congrArg Subtype.val ha
  have hmem : a * x * a⁻¹ ∈ { z : G | z ∈ P ∧ Odd (orderOf z) } := by
    refine ⟨P.mul_mem (P.mul_mem (hEP haE) hxP) (P.inv_mem (hEP haE)), ?_⟩
    have := orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective x
    simpa using this.symm ▸ hxodd
  have hmem' : x⁻¹ ∈ { z : G | z ∈ P ∧ Odd (orderOf z) } :=
    ⟨P.inv_mem hxP, by rwa [orderOf_inv]⟩
  rw [← hval, show a * (x * a * x⁻¹)⁻¹ = (a * x * a⁻¹) * x⁻¹ by group]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure hmem) (Subgroup.subset_closure hmem')

@[expose] def HasShape (P : Type) [Group P] : Prop :=
  ∃ E : Subgroup P, E.Normal ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ Nat.card E = 16 ∧
    5 ∣ Nat.card P

theorem HasShape.of_mulEquiv {P Q : Type} [Group P] [Group Q] (e : P ≃* Q) (h : HasShape P) :
    HasShape Q := by
  obtain ⟨E, hn, hc, h16, h5⟩ := h
  refine ⟨E.map e.toMonoidHom, hn.map e.toMonoidHom e.surjective, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  · rw [Subgroup.card_map_of_injective e.injective, h16]
  · rw [← Nat.card_congr e.toEquiv]; exact h5

theorem hasShape_of_isTwoFourSFive {Y : Type} [Group Y] (P : Subgroup Y)
    (hP : KFactsPair.IsTwoFourSFive P) : HasShape ↥P := by
  obtain ⟨⟨hcomm, -⟩, h16, ⟨e⟩⟩ := hP
  refine ⟨CFSG.pCore 2 ↥P, inferInstance, ?_, ?_, ?_⟩
  · intro a ha b hb
    have := hcomm.is_comm.comm ⟨(a : Y), ⟨a, ha, rfl⟩⟩ ⟨(b : Y), ⟨b, hb, rfl⟩⟩
    have h2 : (a : Y) * (b : Y) = (b : Y) * (a : Y) := congrArg Subtype.val this
    exact Subtype.ext h2
  · have h := h16
    unfold CFSG.Open.pCoreOf at h
    rwa [Subgroup.card_map_of_injective Subtype.val_injective] at h
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥P),
      Nat.card_congr e.toEquiv]
    refine Dvd.dvd.mul_right ?_ _
    simp [Nat.card_perm]
    decide

theorem core {G : Type} [Group G] [Finite G] (ρ : G →* Perm (Fin 10)) (hρ : Function.Injective ρ)
    (P : Subgroup G) (hP : HasShape ↥P) : ∀ i j : Fin 10, ∃ σ ∈ oddHull P, ρ σ i = j := by
  classical
  obtain ⟨E₀, hnorm, hcomm₀, h16₀, h5⟩ := hP
  set E : Subgroup G := E₀.map P.subtype with hEdef
  have hEP : E ≤ P := Subgroup.map_subtype_le E₀
  have hE16 : Nat.card E = 16 := by
    rw [hEdef, Subgroup.card_map_of_injective Subtype.val_injective, h16₀]
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h2 := hcomm₀ a ha b hb
    exact congrArg Subtype.val h2
  have hEnorm : ∀ g ∈ P, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    rintro g hg _ ⟨a, ha, rfl⟩
    exact ⟨⟨g, hg⟩ * a * ⟨g, hg⟩⁻¹, hnorm.conj_mem a ha ⟨g, hg⟩, by simp⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 5 h5
  obtain ⟨x, hxdef⟩ : ∃ x : G, x = (x₀ : G) := ⟨_, rfl⟩
  have hxP : x ∈ P := hxdef ▸ x₀.2
  have hxord : orderOf x = 5 := by rw [hxdef, Subgroup.orderOf_coe]; exact hx₀
  have hx5 : x ^ 5 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxord
    omega
  have hxE : ∀ e ∈ E, x * e * x⁻¹ ∈ E := fun e he => hEnorm x hxP e he
  have hxEn : ∀ n : ℕ, ∀ e ∈ E, x ^ n * e * (x ^ n)⁻¹ ∈ E :=
    fun n e he => hEnorm (x ^ n) (P.pow_mem hxP n) e he
  have hfree := free_of_perm ρ hρ E hE16 x hx5 hx1 hxE
  have hxodd : Odd (orderOf x) := by rw [hxord]; exact ⟨2, by norm_num⟩
  have hEle : E ≤ oddHull P := E_le_oddHull P E hEP hEc x hxP hxodd hxE hfree
  have hxO : x ∈ oddHull P := Subgroup.subset_closure ⟨hxP, hxodd⟩
  letI : MulAction G (Fin 10) := MulAction.compHom (Fin 10) ρ
  obtain ⟨e, he, hne⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra h
    push Not at h
    rw [(Subgroup.eq_bot_iff_forall E).2 h, Subgroup.card_bot] at hE16
    omega
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : Fin 10, ρ e ω₀ ≠ ω₀ := by
    by_contra h
    push Not at h
    exact hne (hρ (by rw [map_one]; exact Equiv.ext h))
  have hcover := exists_cover (Fintype.card_fin 10) E hE16 hEc x hx5 hxEn hfree ω₀
    ⟨e, he, hω₀⟩
  intro i j
  obtain ⟨k, e₁, he₁, hi⟩ := hcover i
  obtain ⟨l, e₂, he₂, hj⟩ := hcover j
  refine ⟨(e₂ * x ^ l) * (e₁ * x ^ k)⁻¹, Subgroup.mul_mem _
    (Subgroup.mul_mem _ (hEle he₂) (Subgroup.pow_mem _ hxO l))
    (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hEle he₁) (Subgroup.pow_mem _ hxO k))), ?_⟩
  show ((e₂ * x ^ l) * (e₁ * x ^ k)⁻¹) • i = j
  calc ((e₂ * x ^ l) * (e₁ * x ^ k)⁻¹) • i = (e₂ * x ^ l) • ((e₁ * x ^ k)⁻¹ • i) :=
        mul_smul _ _ _
    _ = (e₂ * x ^ l) • ω₀ := by rw [hi, inv_smul_smul]
    _ = j := hj.symm

end A10GenJ2

end CFSG.LocalAnalysis.RankThreeUC.S15
