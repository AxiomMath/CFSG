module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.GroupTheory.TransferOrderFour

open MulAction Subgroup

section Counting

variable {G Y : Type*} [Group G]

theorem exists_out_eq_mul {T : Subgroup G} (y : G) :
    ∃ t ∈ T, (QuotientGroup.mk y : G ⧸ T).out = y * t :=
  ⟨y⁻¹ * (QuotientGroup.mk y : G ⧸ T).out, QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm,
    by simp⟩

theorem card_preimage_eq_mul (H : Subgroup G) (f : G → Y) (hf : ∀ x y, f x = f y ↔ x * y⁻¹ ∈ H)
    (S : Set Y) (hS : S ⊆ Set.range f) : Nat.card (f ⁻¹' S) = Nat.card S * Nat.card H := by
  choose r hr using fun s : S => hS s.2
  have key : ∀ (h : H) (s : S), f (h * r s) = s := fun h s => by
    rw [(hf _ _).2 (by simpa using h.2 : (h : G) * r s * (r s)⁻¹ ∈ H)]
    exact hr s
  rw [← Nat.card_prod]
  refine (Nat.card_eq_of_bijective
    (fun p : S × H => (⟨p.2 * r p.1, by simp [key]⟩ : f ⁻¹' S)) ⟨?_, ?_⟩).symm
  · rintro ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ h
    have hs : s₁ = s₂ := Subtype.ext (by
      have := congrArg (fun x : f ⁻¹' S => f x) h
      simpa [key] using this)
    subst hs
    ext
    · rfl
    · simpa using congrArg Subtype.val h
  · rintro ⟨x, hx⟩
    refine ⟨(⟨f x, hx⟩, ⟨x * (r ⟨f x, hx⟩)⁻¹, (hf _ _).1 (hr ⟨f x, hx⟩).symm⟩), ?_⟩
    ext
    simp

theorem card_subtype_eq_mul_card_quotient (T : Subgroup G) (P : G → Prop)
    (hP : ∀ x, ∀ t ∈ T, P x → P (x * t)) :
    Nat.card {x : G // P x} = Nat.card T * Nat.card {c : G ⧸ T // P c.out} := by
  have hmk : ∀ x : G, P (QuotientGroup.mk x : G ⧸ T).out ↔ P x := fun x => by
    obtain ⟨t, ht, e⟩ := exists_out_eq_mul (T := T) x
    rw [e]
    exact ⟨fun h => by simpa using hP _ _ (T.inv_mem ht) h, hP x t ht⟩
  rw [← Nat.card_prod]
  exact Nat.card_congr ((Equiv.subtypeEquivRight fun x => (hmk x).symm).trans
    (QuotientGroup.preimageMkEquivSubgroupProdSet T {c : G ⧸ T | P c.out}))

theorem card_cosets [Finite G] (H T : Subgroup G) (hTH : T ≤ H) (f : G → Y)
    (hf : ∀ x y, f x = f y ↔ x * y⁻¹ ∈ H) (S : Set Y) (hS : S ⊆ Set.range f)
    (hT : ∀ x, ∀ t ∈ T, f x ∈ S → f (x * t) ∈ S) :
    Nat.card {c : G ⧸ T // f c.out ∈ S} = Nat.card S * T.relIndex H := by
  have h1 : Nat.card {x : G // f x ∈ S} = Nat.card S * Nat.card H :=
    card_preimage_eq_mul H f hf S hS
  have h2 := card_subtype_eq_mul_card_quotient T (fun x => f x ∈ S) hT
  have h3 : T.relIndex H * Nat.card T = Nat.card H := by
    simpa [inf_of_le_left hTH] using T.relIndex_mul_card (K := H)
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := T)) ?_
  calc Nat.card T * Nat.card {c : G ⧸ T // f c.out ∈ S} = Nat.card {x : G // f x ∈ S} := h2.symm
    _ = Nat.card S * Nat.card H := h1
    _ = Nat.card S * (T.relIndex H * Nat.card T) := by rw [h3]
    _ = Nat.card T * (Nat.card S * T.relIndex H) := by rw [← mul_assoc, mul_comm]

theorem card_filter_eq_nat_card {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = Nat.card {a // p a} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Counting

section Orbits

variable {K X : Type*} [Group K] [MulAction K X]

open scoped Classical in
theorem sum_eq_sum_orbits [Fintype X] (F : X → ℕ) (hF : ∀ (g : K) (x : X), F (g • x) = F x) :
    ∑ x, F x = ∑ q : orbitRel.Quotient K X, Nat.card (orbit K q.out) * F q.out := by
  calc ∑ x, F x
      = ∑ s : (ω : orbitRel.Quotient K X) × ↥(orbit K ω.out), F s.2.1 := by
        rw [← Equiv.sum_comp (selfEquivSigmaOrbits K X) (fun s => F s.2.1)]
        rfl
    _ = ∑ ω : orbitRel.Quotient K X, ∑ y : ↥(orbit K ω.out), F y.1 := Fintype.sum_sigma _
    _ = _ := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        have hconst : ∀ y : ↥(orbit K ω.out), F y.1 = F ω.out := by
          rintro ⟨y, g, rfl⟩
          exact hF g _
        rw [Finset.sum_congr rfl (fun y _ => hconst y), Finset.sum_const, Finset.card_univ,
          Fintype.card_eq_nat_card, smul_eq_mul]

theorem dvd_card_of_forall_orbit [Finite X] (S : Set X) (hS : ∀ (g : K) (x : X), x ∈ S → g • x ∈ S)
    (m : ℕ) (hm : ∀ x ∈ S, m ∣ Nat.card (orbit K x)) : m ∣ Nat.card S := by
  classical
  have := Fintype.ofFinite X
  have h := sum_eq_sum_orbits (K := K) (fun x : X => if x ∈ S then (1 : ℕ) else 0) (by
    intro g x
    have : x ∈ S ↔ g • x ∈ S := ⟨hS g x, fun h => by simpa using hS g⁻¹ _ h⟩
    simp only [this])
  have hcard : ∑ x : X, (if x ∈ S then (1 : ℕ) else 0) = Nat.card S := by
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    simp
  rw [← hcard, h]
  refine Finset.dvd_sum fun q _ => ?_
  by_cases hq : q.out ∈ S
  · simpa [hq] using hm _ hq
  · simp [hq]

theorem dvd_card_of_conj_stable {G : Type*} [Group G] [Finite G] (T : Subgroup G) (S : Set G)
    (hST : S ⊆ T) (hS : ∀ s ∈ T, ∀ u ∈ S, s * u * s⁻¹ ∈ S) (m : ℕ)
    (hm : ∀ (u : G) (hu : u ∈ T), u ∈ S →
      m ∣ Nat.card (orbit (ConjAct T) (⟨u, hu⟩ : T))) : m ∣ Nat.card S := by
  let S' : Set T := {t | (t : G) ∈ S}
  have h1 : Nat.card S = Nat.card S' :=
    Nat.card_congr (⟨fun u => ⟨⟨u, hST u.2⟩, u.2⟩, fun t => ⟨t, t.2⟩, fun _ => rfl, fun _ => rfl⟩ :
      S ≃ S')
  rw [h1]
  refine dvd_card_of_forall_orbit (K := ConjAct T) S' ?_ m ?_
  · intro g x hx
    have := hS (↑(ConjAct.ofConjAct g)) (ConjAct.ofConjAct g).2 x hx
    show ((g • x : T) : G) ∈ S
    rw [ConjAct.smul_def]
    simpa using this
  · intro x hx
    exact hm x x.2 hx

end Orbits

section Cosets

variable {G : Type*} [Group G] {T : Subgroup G}

theorem smul_mk_eq_iff (g x : G) :
    g • (QuotientGroup.mk x : G ⧸ T) = QuotientGroup.mk x ↔ x⁻¹ * g * x ∈ T := by
  have : g • (QuotientGroup.mk x : G ⧸ T) = QuotientGroup.mk (g * x) := rfl
  rw [this, QuotientGroup.eq]
  constructor
  · intro h
    simpa [mul_assoc] using T.inv_mem h
  · intro h
    simpa [mul_assoc] using T.inv_mem h

theorem smul_eq_iff_out (g : G) (c : G ⧸ T) : g • c = c ↔ c.out⁻¹ * g * c.out ∈ T := by
  conv_lhs => rw [← QuotientGroup.out_eq' c]
  exact smul_mk_eq_iff g c.out

theorem minimalPeriod_dvd_iff {X : Type*} [MulAction G X] (g : G) (c : X) (m : ℕ) :
    Function.minimalPeriod (g • ·) c ∣ m ↔ g ^ m • c = c := by
  constructor
  · intro hd
    have := (Function.isPeriodicPt_minimalPeriod (g • ·) c).trans_dvd hd
    simpa [Function.IsPeriodicPt, Function.IsFixedPt, smul_iterate_apply] using this
  · intro hc
    exact Function.IsPeriodicPt.minimalPeriod_dvd
      (by simpa [Function.IsPeriodicPt, Function.IsFixedPt, smul_iterate_apply] using hc)

theorem nat_eq_four_of_dvd {n : ℕ} (h4 : n ∣ 4) (h2 : ¬ n ∣ 2) : n = 4 := by
  have hle := Nat.le_of_dvd (by norm_num) h4
  have hpos := Nat.pos_of_dvd_of_pos h4 (by norm_num)
  interval_cases n <;> simp_all (config := {decide := true})

theorem out_mk_of_smul_eq {k : G} {c : G ⧸ T} (hc : k • c = c) :
    (Quotient.mk (orbitRel (zpowers k) (G ⧸ T)) c).out = c := by
  obtain ⟨g, hg⟩ := orbitRel_apply.mp (Quotient.mk_out (s := orbitRel (zpowers k) (G ⧸ T)) c)
  have hle : zpowers k ≤ stabilizer G c := Subgroup.zpowers_le.mpr hc
  rw [← hg]
  exact hle g.2

theorem card_orbit_eq_two [Finite G] {k : G} {c : G ⧸ T} (h1 : ¬ k • c = c)
    (h2 : k ^ 2 • c = c) : Nat.card (orbit (zpowers k) c) = 2 := by
  have hn : Function.minimalPeriod (k • ·) c = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp ((minimalPeriod_dvd_iff k c 2).mpr h2) with hd | hd
    · exact absurd (by simpa using (minimalPeriod_dvd_iff k c 1).mp (by rw [hd])) h1
    · exact hd
  haveI := Fintype.ofFinite (orbit (zpowers k) c)
  rw [← hn, MulAction.minimalPeriod_eq_card, Fintype.card_eq_nat_card]

end Cosets

section Powers

variable {A : Type*} [CommGroup A]

theorem pow_of_odd_of_sq {a : A} (ha : a ^ 2 = 1) {n : ℕ} (hn : Odd n) : a ^ n = a := by
  obtain ⟨m, rfl⟩ := hn
  rw [pow_succ, pow_mul, ha, one_pow, one_mul]

theorem pow_of_even_of_sq {a : A} (ha : a ^ 2 = 1) {n : ℕ} (hn : Even n) : a ^ n = 1 := by
  obtain ⟨m, rfl⟩ := hn
  rw [← two_mul, pow_mul, ha, one_pow]

end Powers

section Order4

variable {G : Type*} [Group G] {k : G}

theorem pow_four_eq_one (hk : orderOf k = 4) : k ^ 4 = 1 := hk ▸ pow_orderOf_eq_one k

theorem sq_ne_one (hk : orderOf k = 4) : k ^ 2 ≠ 1 :=
  pow_ne_one_of_lt_orderOf (by norm_num) (by omega)

theorem sq_inv_eq (hk : orderOf k = 4) : k⁻¹ ^ 2 = k ^ 2 := by
  rw [inv_pow]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact pow_four_eq_one hk)

theorem inv_mul_mul_pow (x y : G) (n : ℕ) : (x⁻¹ * y * x) ^ n = x⁻¹ * y ^ n * x := by
  simpa using conj_pow (a := x⁻¹) (b := y) (i := n)

theorem mem_zpowers_cases (hk : orderOf k = 4) {y : G} (hy : y ∈ zpowers k) :
    y = 1 ∨ y = k ∨ y = k ^ 2 ∨ y = k⁻¹ := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hk]
  have h0 : 0 ≤ j % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h1 : j % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
  generalize j % ((4 : ℕ) : ℤ) = r at h0 h1 ⊢
  interval_cases r
  · simp
  · simp
  · simp
  · right; right; right
    exact eq_inv_of_mul_eq_one_left (by rw [zpow_ofNat, ← pow_succ]; exact pow_four_eq_one hk)

theorem conj_eq_or (hk : orderOf k = 4) {x : G} (hx : x⁻¹ * k * x ∈ zpowers k) :
    x⁻¹ * k * x = k ∨ x⁻¹ * k * x = k⁻¹ := by
  have hsq : (x⁻¹ * k * x) ^ 2 = x⁻¹ * k ^ 2 * x := inv_mul_mul_pow x k 2
  rcases mem_zpowers_cases hk hx with h | h | h | h
  · exfalso
    have : k = 1 := by simpa [mul_assoc] using congrArg (fun y => x * y * x⁻¹) h
    simp [this] at hk
  · exact Or.inl h
  · exfalso
    rw [h, ← pow_mul, show 2 * 2 = 4 from rfl, pow_four_eq_one hk] at hsq
    have : k ^ 2 = 1 := by simpa [mul_assoc] using congrArg (fun y => x * y * x⁻¹) hsq.symm
    exact sq_ne_one hk this
  · exact Or.inr h

theorem conj_mem_iff_of_mem {t : G} {T : Subgroup G} (ht : t ∈ T) (y : G) :
    t⁻¹ * y * t ∈ T ↔ y ∈ T :=
  ⟨fun hy => by simpa [mul_assoc] using T.mul_mem (T.mul_mem ht hy) (T.inv_mem ht),
    fun hy => T.mul_mem (T.mul_mem (T.inv_mem ht) hy) ht⟩

end Order4

section Setting

variable {G : Type*} [Group G] {k : G} {T : Subgroup G}

abbrev Cz (k : G) : Subgroup G := Subgroup.centralizer {k ^ 2}

theorem mem_Cz {x : G} : x ∈ Cz k ↔ x * k ^ 2 = k ^ 2 * x :=
  Subgroup.mem_centralizer_singleton_iff

structure Core (k : G) (T : Subgroup G) : Prop where
  order : orderOf k = 4
  normalizes : Cz k ≤ Subgroup.normalizer (Subgroup.zpowers k : Set G)
  le : T ≤ Cz k
  mem : k ∈ T

namespace Core

variable (h : Core k T)
include h

theorem sq_mem : k ^ 2 ∈ T := T.pow_mem h.mem 2

theorem mem_Cz_iff {x : G} : x ∈ Cz k ↔ x⁻¹ * k * x ∈ zpowers k := by
  constructor
  · intro hx
    exact (Subgroup.mem_normalizer_iff''.mp (h.normalizes hx) k).mp (mem_zpowers k)
  · intro hx
    rw [mem_Cz]
    have hsq : x⁻¹ * k ^ 2 * x = k ^ 2 := by
      rw [← inv_mul_mul_pow]
      rcases conj_eq_or h.order hx with h1 | h1
      · rw [h1]
      · rw [h1, sq_inv_eq h.order]
    calc x * k ^ 2 = x * (x⁻¹ * k ^ 2 * x) := by rw [hsq]
      _ = k ^ 2 * x := by group

theorem conj_eq_or_of_mem_Cz {x : G} (hx : x ∈ Cz k) : x⁻¹ * k * x = k ∨ x⁻¹ * k * x = k⁻¹ :=
  conj_eq_or h.order (h.mem_Cz_iff.mp hx)

theorem zpowers_conj_eq {x : G} (hx : x ∈ Cz k) : zpowers (x⁻¹ * k * x) = zpowers k := by
  rcases h.conj_eq_or_of_mem_Cz hx with h1 | h1 <;> simp [h1]

theorem conj_mem_iff_mul {c : G} (hc : c ∈ Cz k) (x : G) :
    (c * x)⁻¹ * k * (c * x) ∈ T ↔ x⁻¹ * k * x ∈ T := by
  have e : (c * x)⁻¹ * k * (c * x) = x⁻¹ * (c⁻¹ * k * c) * x := by group
  rw [e]
  rcases h.conj_eq_or_of_mem_Cz hc with h1 | h1
  · rw [h1]
  · rw [h1, show x⁻¹ * k⁻¹ * x = (x⁻¹ * k * x)⁻¹ by group, T.inv_mem_iff]

theorem smul_eq_of_mem_Cz {c : G ⧸ T} (hc : c.out ∈ Cz k) : k • c = c := by
  rw [smul_eq_iff_out]
  rcases h.conj_eq_or_of_mem_Cz hc with h1 | h1
  · rw [h1]; exact h.mem
  · rw [h1]; exact T.inv_mem h.mem

end Core

@[expose] def fz (k x : G) : G := x⁻¹ * k ^ 2 * x

@[expose] def fk (k x : G) : Subgroup G := zpowers (x⁻¹ * k * x)

theorem fz_eq_iff (x y : G) : fz k x = fz k y ↔ x * y⁻¹ ∈ Cz k := by
  rw [mem_Cz, fz, fz]
  constructor
  · intro h
    calc x * y⁻¹ * k ^ 2 = x * (y⁻¹ * k ^ 2 * y) * y⁻¹ := by group
      _ = x * (x⁻¹ * k ^ 2 * x) * y⁻¹ := by rw [h]
      _ = k ^ 2 * (x * y⁻¹) := by group
  · intro h
    calc x⁻¹ * k ^ 2 * x = x⁻¹ * (k ^ 2 * (x * y⁻¹)) * y := by group
      _ = x⁻¹ * (x * y⁻¹ * k ^ 2) * y := by rw [h]
      _ = y⁻¹ * k ^ 2 * y := by group

theorem fz_mul_right (x t : G) : fz k (x * t) = t⁻¹ * fz k x * t := by
  simp only [fz]; group

theorem fz_mul_left {c : G} (hc : c ∈ Cz k) (x : G) : fz k (c * x) = fz k x := by
  rw [fz_eq_iff]
  simpa using inv_mem hc

theorem Core.fk_eq_iff (h : Core k T) (x y : G) : fk k x = fk k y ↔ x * y⁻¹ ∈ Cz k := by
  constructor
  · intro hxy
    have hx : x⁻¹ * k * x ∈ zpowers (y⁻¹ * k * y) := by
      rw [← fk, ← hxy]; exact mem_zpowers _
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hconj : (y⁻¹ * k * y) ^ j = y⁻¹ * k ^ j * y := by
      simpa using conj_zpow (a := y⁻¹) (b := k) (i := j)
    have e : (x * y⁻¹)⁻¹ * k * (x * y⁻¹) = k ^ j :=
      calc (x * y⁻¹)⁻¹ * k * (x * y⁻¹) = y * (x⁻¹ * k * x) * y⁻¹ := by group
        _ = y * (y⁻¹ * k ^ j * y) * y⁻¹ := by rw [← hj, hconj]
        _ = k ^ j := by group
    exact h.mem_Cz_iff.mpr (by rw [e]; exact Subgroup.zpow_mem _ (mem_zpowers k) j)
  · intro hg
    have e : x⁻¹ * k * x = y⁻¹ * ((x * y⁻¹)⁻¹ * k * (x * y⁻¹)) * y := by group
    unfold fk
    rw [e]
    rcases h.conj_eq_or_of_mem_Cz hg with h1 | h1
    · rw [h1]
    · rw [h1, show y⁻¹ * k⁻¹ * y = (y⁻¹ * k * y)⁻¹ by group, Subgroup.zpowers_inv]

end Setting

end CFSG.GroupTheory.TransferOrderFour
