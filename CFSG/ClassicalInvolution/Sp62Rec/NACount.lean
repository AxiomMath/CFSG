module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

variable {G : Type*} [Group G] [Finite G]

@[expose] def orbIn (X : Subgroup G) (a : G) : Set G := {b | ∃ x ∈ X, x * a * x⁻¹ = b}

private theorem mem_orbIn {X : Subgroup G} {a b : G} :
    b ∈ orbIn X a ↔ ∃ x ∈ X, x * a * x⁻¹ = b :=
  Iff.rfl

private theorem card_range_eq_index' {H X : Type*} [Group H] (f : H → X) (K : Subgroup H)
    (hK : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ K) : Nat.card (Set.range f) = K.index := by
  rw [Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective (fun q : H ⧸ K => (⟨Quotient.liftOn' q f
    (fun a b hab => (hK a b).mpr (QuotientGroup.leftRel_apply.mp hab)), by
      induction q using QuotientGroup.induction_on with | H a => exact ⟨a, rfl⟩⟩ :
      Set.range f)) ⟨fun q q' hqq => ?_, fun y => ?_⟩).symm
  · induction q using QuotientGroup.induction_on with | H a => ?_
    induction q' using QuotientGroup.induction_on with | H b => ?_
    have e : f a = f b := congrArg Subtype.val hqq
    exact QuotientGroup.eq.mpr ((hK a b).mp e)
  · obtain ⟨_, a, rfl⟩ := y
    exact ⟨QuotientGroup.mk a, rfl⟩

private theorem conj_pair_iff (n c a : G) :
    n * a * n⁻¹ = n * c * a * (n * c)⁻¹ ↔ c * a = a * c := by
  have e1 : n * c * a * (n * c)⁻¹ = n * (c * a * c⁻¹) * n⁻¹ := by group
  rw [e1]
  constructor
  · intro h
    have h3 : n * (a * n⁻¹) = n * ((c * a * c⁻¹) * n⁻¹) := by
      simpa only [mul_assoc] using h
    have h2 : a = c * a * c⁻¹ := mul_right_cancel (mul_left_cancel h3)
    calc c * a = (c * a * c⁻¹) * c := by group
      _ = a * c := by rw [← h2]
  · intro h
    have h2 : c * a * c⁻¹ = a := by
      rw [mul_inv_eq_iff_eq_mul]
      exact h
    rw [h2]

private theorem conj_of_eq {a a' u v b : G} (hu : u * a * u⁻¹ = b) (hv : v * a' * v⁻¹ = b) :
    (v⁻¹ * u) * a * (v⁻¹ * u)⁻¹ = a' := by
  calc (v⁻¹ * u) * a * (v⁻¹ * u)⁻¹ = v⁻¹ * (u * a * u⁻¹) * v := by group
    _ = v⁻¹ * b * v := by rw [hu]
    _ = a' := by rw [← hv]; group

theorem card_eq_ncard_orbIn_mul (N : Subgroup G) (a : G) :
    Nat.card N = (orbIn N a).ncard * Nat.card ↥(N ⊓ Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup ↥N,
      K = (N ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf N := ⟨_, rfl⟩
  have hrange : orbIn N a = Set.range (fun n : ↥N => (n : G) * a * (n : G)⁻¹) := by
    ext b
    constructor
    · intro hb
      obtain ⟨x, hx, rfl⟩ := mem_orbIn.mp hb
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨n, rfl⟩
      exact mem_orbIn.mpr ⟨n, n.2, rfl⟩
  have hK : ∀ n n' : ↥N, (n : G) * a * (n : G)⁻¹ = (n' : G) * a * (n' : G)⁻¹ ↔
      n⁻¹ * n' ∈ K := by
    intro n n'
    have key := conj_pair_iff (n : G) ((n : G)⁻¹ * (n' : G)) a
    simp only [mul_inv_cancel_left] at key
    rw [key, hKdef, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨N.mul_mem (N.inv_mem n.2) n'.2, h⟩, fun h => h.2⟩
  have hidx := card_range_eq_index' (fun n : ↥N => (n : G) * a * (n : G)⁻¹) K hK
  have hKcard : Nat.card ↥K = Nat.card ↥(N ⊓ Subgroup.centralizer ({a} : Set G)) := by
    rw [hKdef]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      N ⊓ Subgroup.centralizer ({a} : Set G) ≤ N)).toEquiv
  have hmul : Nat.card ↥K * K.index = Nat.card ↥N := Subgroup.card_mul_index K
  have hcount : (orbIn N a).ncard = K.index := by
    rw [← hidx, hrange, Nat.card_coe_set_eq]
  rw [← hmul, hKcard, hcount, mul_comm]

private theorem orbIn_eq_orbIn_of_mem {X : Subgroup G} {a b : G} (hb : b ∈ orbIn X a) :
    orbIn X a = orbIn X b := by
  obtain ⟨x, hx, rfl⟩ := mem_orbIn.mp hb
  ext c
  constructor
  · intro hc
    obtain ⟨x', hx', rfl⟩ := mem_orbIn.mp hc
    exact mem_orbIn.mpr ⟨x' * x⁻¹, X.mul_mem hx' (X.inv_mem hx), by group⟩
  · intro hc
    obtain ⟨x', hx', rfl⟩ := mem_orbIn.mp hc
    exact mem_orbIn.mpr ⟨x' * x, X.mul_mem hx' hx, by group⟩

private theorem orbIn_mono {X Y : Subgroup G} (hXY : X ≤ Y) (a : G) :
    orbIn X a ⊆ orbIn Y a := by
  intro b hb
  obtain ⟨x, hx, rfl⟩ := mem_orbIn.mp hb
  exact mem_orbIn.mpr ⟨x, hXY hx, rfl⟩

private theorem orbIn_subset_of_mem {X Y : Subgroup G} (hXY : X ≤ Y) {a b : G}
    (hb : b ∈ orbIn Y a) : orbIn X b ⊆ orbIn Y a := by
  obtain ⟨n, hn, rfl⟩ := mem_orbIn.mp hb
  intro c hc
  obtain ⟨x, hx, rfl⟩ := mem_orbIn.mp hc
  exact mem_orbIn.mpr ⟨x * n, Y.mul_mem (hXY hx) hn, by group⟩

private theorem ne_one_of_mem_orbIn {X : Subgroup G} {a b : G} (ha : a ≠ 1)
    (hb : b ∈ orbIn X a) : b ≠ 1 := by
  rintro rfl
  obtain ⟨x, _, hx⟩ := mem_orbIn.mp hb
  apply ha
  calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
    _ = x⁻¹ * 1 * x := by rw [hx]
    _ = 1 := by group

theorem normalizer_eq_of_orbits {A X : Subgroup G} {e y r : G}
    (hA : ∀ a ∈ A, a * a = 1) (hcardA : Nat.card A = 64)
    (hCA : ∀ g : G, (∀ a ∈ A, g * a = a * g) → g ∈ A)
    (hXN : X ≤ Subgroup.normalizer (A : Set G))
    (he : e ∈ A) (hy : y ∈ A) (hr : r ∈ A)
    (hcover : ∀ a ∈ A, a ≠ 1 →
      a ∈ orbIn X e ∨ a ∈ orbIn X y ∨ a ∈ orbIn X (e * y) ∨ a ∈ orbIn X r)
    (horbe : (orbIn X e).ncard = 7) (horbr : (orbIn X r).ncard = 28)
    (hD : Nat.card (Subgroup.closure (orbIn X y)) = 8)
    (hrig : ∀ g : G, g * e * g⁻¹ ≠ y ∧ g * e * g⁻¹ ≠ e * y ∧ g * y * g⁻¹ ≠ e * y)
    (hcard : Nat.card X =
      7 * Nat.card ↥(Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({e} : Set G)))
    (hfive : ∀ (D : Subgroup G) (g : G), D ≤ A → Nat.card D = 8 → (∀ a ∈ A, g * a * g⁻¹ ∈ A) →
      (∀ d ∈ D, g * d * g⁻¹ ∈ D) → g ^ 5 = 1 → ∀ a ∈ A, g * a = a * g) :
    Subgroup.normalizer (A : Set G) = X := by
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup G, N = Subgroup.normalizer (A : Set G) := ⟨_, rfl⟩
  rw [← hNdef] at hXN hcard ⊢
  have hNA : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A := by
    intro n hn a ha
    rw [hNdef, Subgroup.mem_set_normalizer_iff] at hn
    exact (hn a).mp ha
  have he1 : e ≠ 1 := by
    rintro rfl
    have h1 : orbIn X (1 : G) = {1} := by
      ext b
      constructor
      · intro hb
        obtain ⟨x, _, hx⟩ := mem_orbIn.mp hb
        rw [Set.mem_singleton_iff, ← hx]
        group
      · intro hb
        rw [Set.mem_singleton_iff] at hb
        exact mem_orbIn.mpr ⟨1, X.one_mem, by simp [hb]⟩
    rw [h1, Set.ncard_singleton] at horbe
    norm_num at horbe
  have hy1 : y ≠ 1 := by
    rintro rfl
    have hbot : Subgroup.closure (orbIn X (1 : G)) = ⊥ := by
      apply le_bot_iff.mp
      apply (Subgroup.closure_le _).mpr
      intro b hb
      obtain ⟨x, _, hx⟩ := mem_orbIn.mp hb
      rw [SetLike.mem_coe, Subgroup.mem_bot, ← hx]
      group
    rw [hbot, Subgroup.card_bot] at hD
    norm_num at hD
  have hdisjA : ∀ b : G, b ∈ orbIn N e → b ∈ orbIn X y → False := by
    intro b hb1 hb2
    obtain ⟨m, _, hm⟩ := mem_orbIn.mp hb1
    obtain ⟨x, _, hx⟩ := mem_orbIn.mp hb2
    exact (hrig (x⁻¹ * m)).1 (conj_of_eq hm hx)
  have hdisjB : ∀ b : G, b ∈ orbIn N e → b ∈ orbIn X (e * y) → False := by
    intro b hb1 hb2
    obtain ⟨m, _, hm⟩ := mem_orbIn.mp hb1
    obtain ⟨x, _, hx⟩ := mem_orbIn.mp hb2
    exact (hrig (x⁻¹ * m)).2.1 (conj_of_eq hm hx)
  have hdisjC : ∀ b : G, b ∈ orbIn N e → b ∈ orbIn N y → False := by
    intro b hb1 hb2
    obtain ⟨m, _, hm⟩ := mem_orbIn.mp hb1
    obtain ⟨n, _, hn⟩ := mem_orbIn.mp hb2
    exact (hrig (n⁻¹ * m)).1 (conj_of_eq hm hn)
  have hdisjE : ∀ b : G, b ∈ orbIn X (e * y) → b ∈ orbIn N y → False := by
    intro b hb1 hb2
    obtain ⟨x, _, hx⟩ := mem_orbIn.mp hb1
    obtain ⟨n, _, hn⟩ := mem_orbIn.mp hb2
    exact (hrig (x⁻¹ * n)).2.2 (conj_of_eq hn hx)
  have hsubE : orbIn N e ⊆ orbIn X e ∪ orbIn X r := by
    intro b hb
    obtain ⟨m, hm, hmb⟩ := mem_orbIn.mp hb
    have hbA : b ∈ A := by
      rw [← hmb]
      exact hNA m hm e he
    have hb1 : b ≠ 1 := ne_one_of_mem_orbIn he1 hb
    rcases hcover b hbA hb1 with h | h | h | h
    · exact Or.inl h
    · exact (hdisjA b hb h).elim
    · exact (hdisjB b hb h).elim
    · exact Or.inr h
  have hdisjEr : Disjoint (orbIn X e) (orbIn X r) := by
    rw [Set.disjoint_left]
    intro c hce hcr
    have hEq : orbIn X e = orbIn X r :=
      (orbIn_eq_orbIn_of_mem hce).trans (orbIn_eq_orbIn_of_mem hcr).symm
    have h28 := horbe
    rw [hEq, horbr] at h28
    omega
  by_cases hcase : ∃ b : G, b ∈ orbIn N e ∧ b ∈ orbIn X r
  ·
    exfalso
    obtain ⟨b0, hb0N, hb0X⟩ := hcase
    have hrN : orbIn X r ⊆ orbIn N e := by
      rw [orbIn_eq_orbIn_of_mem hb0X]
      exact orbIn_subset_of_mem hXN hb0N
    have hEN : orbIn N e = orbIn X e ∪ orbIn X r :=
      Set.Subset.antisymm hsubE (Set.union_subset (orbIn_mono hXN e) hrN)
    have hNcard35 : (orbIn N e).ncard = 35 := by
      rw [hEN, Set.ncard_union_eq hdisjEr]
      omega
    have hNeq : Nat.card N = 5 * Nat.card X := by
      rw [card_eq_ncard_orbIn_mul N e, hNcard35, hcard]
      ring
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨g, hgo⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 5 ⟨Nat.card X, hNeq⟩
    have hgo' : orderOf (g : G) = 5 := (Subgroup.orderOf_coe g).trans hgo
    have hg5 : (g : G) ^ 5 = 1 := by
      have h := pow_orderOf_eq_one (g : G)
      rwa [hgo'] at h
    have hNY : orbIn N y ⊆ orbIn X y := by
      intro b hb
      obtain ⟨n, hn, hnb⟩ := mem_orbIn.mp hb
      have hbA : b ∈ A := by
        rw [← hnb]
        exact hNA n hn y hy
      have hb1 : b ≠ 1 := ne_one_of_mem_orbIn hy1 hb
      rcases hcover b hbA hb1 with h | h | h | h
      · exact (hdisjC b (orbIn_mono hXN e h) hb).elim
      · exact h
      · exact (hdisjE b h hb).elim
      · exact (hdisjC b (hrN h) hb).elim
    have hDA : Subgroup.closure (orbIn X y) ≤ A := by
      apply (Subgroup.closure_le _).mpr
      intro b hb
      obtain ⟨x, hx, hxb⟩ := mem_orbIn.mp hb
      rw [SetLike.mem_coe, ← hxb]
      exact hNA x (hXN hx) y hy
    have hgA : ∀ a ∈ A, (g : G) * a * (g : G)⁻¹ ∈ A := fun a ha => hNA _ g.2 a ha
    have hgorb : ∀ b ∈ orbIn X y, (g : G) * b * (g : G)⁻¹ ∈ orbIn X y := by
      intro b hb
      obtain ⟨n, hn, hnb⟩ := mem_orbIn.mp (orbIn_mono hXN y hb)
      have hmem : (g : G) * b * (g : G)⁻¹ ∈ orbIn N y :=
        mem_orbIn.mpr ⟨(g : G) * n, N.mul_mem g.2 hn, by rw [← hnb]; group⟩
      exact hNY hmem
    have hgD : ∀ d ∈ Subgroup.closure (orbIn X y),
        (g : G) * d * (g : G)⁻¹ ∈ Subgroup.closure (orbIn X y) := by
      intro d hd
      induction hd using Subgroup.closure_induction with
      | mem x hx => exact Subgroup.subset_closure (hgorb x hx)
      | one => simp
      | mul x x' _ _ hx hx' =>
        have e' : (g : G) * (x * x') * (g : G)⁻¹ =
            ((g : G) * x * (g : G)⁻¹) * ((g : G) * x' * (g : G)⁻¹) := by group
        rw [e']
        exact mul_mem hx hx'
      | inv x _ hx =>
        have e' : (g : G) * x⁻¹ * (g : G)⁻¹ = ((g : G) * x * (g : G)⁻¹)⁻¹ := by group
        rw [e']
        exact inv_mem hx
    have hgA' : (g : G) ∈ A :=
      hCA (g : G) (hfive (Subgroup.closure (orbIn X y)) (g : G) hDA hD hgA hgD hg5)
    have hg2 : (g : G) ^ 2 = 1 := by
      rw [pow_two]
      exact hA _ hgA'
    have hdvd : orderOf (g : G) ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
    rw [hgo'] at hdvd
    omega
  ·
    have hEq : orbIn N e = orbIn X e := by
      apply Set.Subset.antisymm
      · intro b hb
        rcases hsubE hb with h | h
        · exact h
        · exact (hcase ⟨b, hb, h⟩).elim
      · exact orbIn_mono hXN e
    have hNcard : Nat.card N = Nat.card X := by
      rw [card_eq_ncard_orbIn_mul N e, hEq, horbe, hcard]
    exact (Subgroup.eq_of_le_of_card_ge hXN hNcard.le).symm
