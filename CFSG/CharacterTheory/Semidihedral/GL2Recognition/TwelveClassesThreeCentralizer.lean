module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.Order5616Simplicity
public import CFSG.CharacterTheory.Semidihedral.Principal.OrderTwentySevenNineCycles

public section

open scoped Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.GL2ThreeCharacters
open CFSG.TwoRankLowerBound.Helpers (orderOf_eq_of_isConj)

section Classes

variable {G : Type*} [Group G]

theorem card_eq_card_conjClass (P : G → Prop) (hP : ∀ g h : G, IsConj g h → P g → P h)
    {x : G} (hx : P x) (h : ∀ g, P g → IsConj x g) :
    Nat.card {g : G // P g} = Nat.card (ConjClasses.mk x).carrier :=
  Nat.card_congr (Equiv.subtypeEquivRight fun g => by
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    exact ⟨fun hg => (h g hg).symm, fun hg => hP x g hg.symm hx⟩)

theorem card_eq_add_card_conjClass [Finite G] (P : G → Prop)
    (hP : ∀ g h : G, IsConj g h → P g → P h) {x y : G} (hx : P x) (hy : P y)
    (hxy : ¬ IsConj x y) (h : ∀ g, P g → IsConj x g ∨ IsConj y g) :
    Nat.card {g : G // P g} =
      Nat.card (ConjClasses.mk x).carrier + Nat.card (ConjClasses.mk y).carrier := by
  have hdisj : Disjoint (fun g => g ∈ (ConjClasses.mk x).carrier)
      (fun g => g ∈ (ConjClasses.mk y).carrier) := by
    intro r hrx hry g hg
    have h1 := ConjClasses.mem_carrier_iff_mk_eq.mp (hrx g hg)
    have h2 := ConjClasses.mem_carrier_iff_mk_eq.mp (hry g hg)
    exact hxy (ConjClasses.mk_eq_mk_iff_isConj.mp (h1.symm.trans h2))
  rw [← Nat.card_sum, ← Nat.card_congr (subtypeOrEquiv _ _ hdisj)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj, ConjClasses.mk_eq_mk_iff_isConj]
  constructor
  · intro hg
    rcases h g hg with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'.symm
  · rintro (h' | h')
    · exact hP x g h'.symm hx
    · exact hP y g h'.symm hy

theorem exists_of_card_classes_eq_two (P : G → Prop)
    (h2 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g} = 2) {x : G}
    (hx : P x) : ∃ y, P y ∧ ¬ IsConj x y ∧ ∀ g, P g → IsConj x g ∨ IsConj y g := by
  obtain ⟨⟨c, y, rfl, hy⟩, hne, huniq⟩ := (Nat.card_eq_two_iff'
    (⟨ConjClasses.mk x, x, rfl, hx⟩ :
      {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g})).mp h2
  refine ⟨y, hy, fun hxy => hne (Subtype.ext (ConjClasses.mk_eq_mk_iff_isConj.mpr hxy).symm),
    fun g hg => ?_⟩
  by_cases hgx : IsConj x g
  · exact Or.inl hgx
  right
  have h := huniq ⟨ConjClasses.mk g, g, rfl, hg⟩ fun h =>
    hgx (ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val h).symm)
  exact (ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val h)).symm

end Classes

section Twelve

variable {G : Type*} [Group G] {t : G}

theorem factorization_5616_three : Nat.factorization 5616 3 = 3 := by
  have h : (5616 : ℕ) = 3 ^ 3 * 208 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem card_sylow_three_of_card_eq_5616 [Finite G] (hG : Nat.card G = 5616) (P : Sylow 3 G) :
    Nat.card P = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [P.card_eq_multiplicity, hG, factorization_5616_three]
  norm_num

theorem factorization_54_three : Nat.factorization 54 3 = 3 := by
  have h : (54 : ℕ) = 3 ^ 3 * 2 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem pow_three_eq_one_of_dvd_27 (hno : ∀ g : G, orderOf g ≠ 9 ∧ orderOf g ≠ 27) {x : G}
    (hx : orderOf x ∣ 27) : x ^ 3 = 1 := by
  have hmem : orderOf x ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hx, by norm_num⟩
  have key : ∀ m ∈ Nat.divisors 27, m ≠ 9 → m ≠ 27 → m ∣ 3 := by decide
  exact orderOf_dvd_iff_pow_eq_one.mp (key _ hmem (hno x).1 (hno x).2)

theorem exists_ne_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩

theorem twelve_classes_produce_exponent_three_centralizer_data [Finite G]
    (hG : Nat.card G = 5616) (hperf : commutator G = ⊤) (h12 : Nat.card (ConjClasses G) = 12)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer {t} ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) :
    (∀ g : G, orderOf g ≠ 9 ∧ orderOf g ≠ 27) ∧
    (∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 6, 8, 13} : Finset ℕ)) ∧
    Nat.card {g : G // orderOf g = 3} = 728 ∧
    (∀ P : Sylow 3 G, Nat.card P = 27 ∧
      (∃ a ∈ (P : Subgroup G), ∃ b ∈ (P : Subgroup G), a * b ≠ b * a) ∧
      ∀ x ∈ (P : Subgroup G), x ^ 3 = 1) ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 3} = 2 ∧
    (∃ x y : G, orderOf x = 3 ∧ orderOf y = 3 ∧
      Nat.card (ConjClasses.mk x).carrier = 104 ∧ Nat.card (ConjClasses.mk y).carrier = 624 ∧
      Nat.card (Subgroup.centralizer ({x} : Set G)) = 54 ∧
      Nat.card (Subgroup.centralizer ({y} : Set G)) = 9 ∧
      ∀ z : G, orderOf z = 3 → IsConj z x ∨ IsConj z y) ∧
    ∀ a ∈ Subgroup.centralizer ({t} : Set G), orderOf a = 3 →
      Nat.card (Subgroup.centralizer ({a} : Set G)) = 54 ∧
      ∃ P : Subgroup G, P ≤ Subgroup.centralizer ({a} : Set G) ∧ Nat.card P = 27 ∧
        (∀ x ∈ P, x ^ 3 = 1) ∧
        ∀ Q : Subgroup G, Q ≤ Subgroup.centralizer ({a} : Set G) → Nat.card Q = 27 → Q = P := by
  obtain ⟨φ⟩ := hC
  have := Fintype.ofFinite G
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h13, -, -, -, -, -, -, -, -, -, -, -, -, hS, h728⟩ :=
    order5616_classes hG hperf hinv ht φ
  have hcent : ∀ A : Subgroup G, Nat.card A = 13 → Subgroup.centralizer (A : Set G) = A :=
    fun A hA => (h13 A hA).1
  have h2cl := (perfect_order5616_GL2_centralizer_conjugacy_profile hG hperf hinv ht
    ⟨φ⟩).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h12
  have hinvar : ∀ (Q : ℕ → Prop) (g h : G), IsConj g h → Q (orderOf g) → Q (orderOf h) :=
    fun Q g h hgh hg => orderOf_pred_of_isConj Q hgh hg
  have h3pow := card_orderOf_mem_eq_sum (G := G) ({3, 9, 27} : Finset ℕ)
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h3pow
  have h728' : Nat.card {g : G // orderOf g ∈ ({3, 9, 27} : Finset ℕ)} = 728 := by
    rw [← h728]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp)
  rw [h728'] at h3pow
  have hcl : ∀ g : G, Nat.card (ConjClasses.mk g).carrier *
      Nat.card (Subgroup.centralizer ({g} : Set G)) = 5616 := fun g => by
    rw [← hG]
    exact CFSG.LyonsUnitaryFour.card_conjClass_mul_card_centralizer g
  have hno27 : ∀ g : G, orderOf g ≠ 27 := by
    intro g hg
    have hg3 : orderOf (g ^ 3) = 9 := by rw [orderOf_pow' g (by norm_num), hg]; norm_num
    have hg9 : orderOf (g ^ 9) = 3 := by rw [orderOf_pow' g (by norm_num), hg]; norm_num
    obtain ⟨y, -, hgy, hall⟩ := exists_of_card_classes_eq_two _ h2cl (x := g)
      (Or.inr (Or.inr hg))
    have h1 : IsConj y (g ^ 3) := by
      rcases hall (g ^ 3) (Or.inr (Or.inl hg3)) with h | h
      · exact absurd (orderOf_eq_of_isConj h) (by rw [hg, hg3]; norm_num)
      · exact h
    have h2 : IsConj y (g ^ 9) := by
      rcases hall (g ^ 9) (Or.inl hg9) with h | h
      · exact absurd (orderOf_eq_of_isConj h) (by rw [hg, hg9]; norm_num)
      · exact h
    have := orderOf_eq_of_isConj (h1.symm.trans h2)
    rw [hg3, hg9] at this
    norm_num at this
  have hno9 : ∀ g : G, orderOf g ≠ 9 := by
    intro x hx
    have hx3 : orderOf (x ^ 3) = 3 := by rw [orderOf_pow' x (by norm_num), hx]; norm_num
    obtain ⟨y, -, hxy, hall⟩ := exists_of_card_classes_eq_two _ h2cl (x := x)
      (Or.inr (Or.inl hx))
    have hall3 : ∀ g : G, orderOf g = 3 → IsConj (x ^ 3) g := by
      have hy3 : IsConj y (x ^ 3) := by
        rcases hall (x ^ 3) (Or.inl hx3) with h | h
        · exact absurd (orderOf_eq_of_isConj h) (by rw [hx, hx3]; norm_num)
        · exact h
      intro g hg
      rcases hall g (Or.inl hg) with h | h
      · exact absurd (orderOf_eq_of_isConj h) (by rw [hx, hg]; norm_num)
      · exact hy3.symm.trans h
    have hall9 : ∀ g : G, orderOf g = 9 → IsConj x g := by
      intro g hg
      rcases hall g (Or.inr (Or.inl hg)) with h | h
      · exact h
      · exfalso
        have hy3 : IsConj y (x ^ 3) := by
          rcases hall (x ^ 3) (Or.inl hx3) with h' | h'
          · exact absurd (orderOf_eq_of_isConj h') (by rw [hx, hx3]; norm_num)
          · exact h'
        have := orderOf_eq_of_isConj (hy3.symm.trans h)
        rw [hx3, hg] at this
        norm_num at this
    have hN3 := card_eq_card_conjClass (fun g : G => orderOf g = 3) (hinvar (· = 3)) hx3 hall3
    have hN9 := card_eq_card_conjClass (fun g : G => orderOf g = 9) (hinvar (· = 9)) hx hall9
    have hN27 : Nat.card {g : G // orderOf g = 27} = 0 := by
      rw [Nat.card_eq_zero]
      exact Or.inl ⟨fun g => hno27 g.1 g.2⟩
    have hodd : ¬ 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
      intro h2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card'
        (G := Subgroup.centralizer ({x} : Set G)) 2 h2
      have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe, hu]
      obtain ⟨ψ⟩ := nonempty_centralizer_involution_mulEquiv hinv ht φ hu'
      have hxu : x ∈ Subgroup.centralizer ({(u : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp u.2).symm
      have hord := GL2ThreeStructure.order_exhaustive (ψ ⟨x, hxu⟩)
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx] at hord
      simp at hord
    have h13x : ¬ 13 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
      intro h13'
      have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
        (G := Subgroup.centralizer ({x} : Set G)) 13 h13'
      have hw' : orderOf (w : G) = 13 := by rw [Subgroup.orderOf_coe, hw]
      have hxw : x ∈ Subgroup.centralizer ({(w : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp w.2).symm
      rw [centralizer_eq_zpowers_of_orderOf_eq_thirteen hcent hw'] at hxw
      have h := Subgroup.orderOf_dvd_natCard _ hxw
      rw [hx, Nat.card_zpowers, hw'] at h
      norm_num at h
    have h9x : 9 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
      have hle : Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      have h := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hx] at h
    have hdvd : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 16 * (13 * 27) := by
      have h := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer ({x} : Set G))
      rw [hG] at h
      exact h
    have hcop2 : Nat.Coprime (Nat.card (Subgroup.centralizer ({x} : Set G))) 16 := by
      have hodd' : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))) :=
        Nat.odd_iff.mpr (by omega)
      have h := Nat.Coprime.pow_right 4 (Nat.coprime_two_right.mpr hodd')
      rwa [show (2 : ℕ) ^ 4 = 16 by norm_num] at h
    have hcop13 : Nat.Coprime (Nat.card (Subgroup.centralizer ({x} : Set G))) 13 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h13x).symm
    have h27 := Nat.Coprime.dvd_of_dvd_mul_left hcop13
      (Nat.Coprime.dvd_of_dvd_mul_left hcop2 hdvd)
    have hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = 9 ∨
        Nat.card (Subgroup.centralizer ({x} : Set G)) = 27 := by
      have hmem : Nat.card (Subgroup.centralizer ({x} : Set G)) ∈ Nat.divisors 27 :=
        Nat.mem_divisors.mpr ⟨h27, by norm_num⟩
      have key : ∀ m ∈ Nat.divisors 27, 9 ∣ m → m = 9 ∨ m = 27 := by decide
      exact key _ hmem h9x
    have hcx := hcl x
    have hcx3 := hcl (x ^ 3)
    have hc9 : Nat.card (Subgroup.centralizer ({x} : Set G)) = 9 := by
      rcases hc with h | h
      · exact h
      · exfalso
        rw [h] at hcx
        have h208 : Nat.card (ConjClasses.mk x).carrier = 208 := by omega
        have h520 : Nat.card (ConjClasses.mk (x ^ 3)).carrier = 520 := by omega
        rw [h520] at hcx3
        omega
    rw [hc9] at hcx
    have h624 : Nat.card (ConjClasses.mk x).carrier = 624 := by omega
    have h104 : Nat.card (ConjClasses.mk (x ^ 3)).carrier = 104 := by omega
    obtain ⟨P, hP⟩ := (IsPGroup.of_card (p := 3) (n := 2)
      (by rw [Nat.card_zpowers, hx]; norm_num) : IsPGroup 3 (Subgroup.zpowers x)).exists_le_sylow
    have hxP : x ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers x)
    have hP27 := card_sylow_three_of_card_eq_5616 hG P
    have hPna : ¬ IsMulCommutative (P : Subgroup G) := by
      intro hcomm
      have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := fun p hp =>
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (hcomm.is_comm.comm (⟨p, hp⟩ : (P : Subgroup G)) ⟨x, hxP⟩))
      have h := Subgroup.card_dvd_of_le hle
      rw [hc9] at h
      have h27 : Nat.card (P : Subgroup G) = 27 := hP27
      rw [h27] at h
      norm_num at h
    have hfus := (order_twenty_seven_nine_cycle_fusion_inequality P hP27 hPna ⟨x, hxP, hx⟩
      fun a b ha hb => (hall3 a ha).symm.trans (hall3 b hb)).1
    rw [hN3, hN9, h624, h104] at hfus
    norm_num at hfus
  have hno : ∀ g : G, orderOf g ≠ 9 ∧ orderOf g ≠ 27 := fun g => ⟨hno9 g, hno27 g⟩
  have hS' : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 6, 8, 13} : Finset ℕ) := by
    intro g
    have h := hS g
    have h9 := hno9 g
    have h27 := hno27 g
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    omega
  have hN9 : Nat.card {g : G // orderOf g = 9} = 0 := by
    rw [Nat.card_eq_zero]
    exact Or.inl ⟨fun g => hno9 g.1 g.2⟩
  have hN27 : Nat.card {g : G // orderOf g = 27} = 0 := by
    rw [Nat.card_eq_zero]
    exact Or.inl ⟨fun g => hno27 g.1 g.2⟩
  have hN3 : Nat.card {g : G // orderOf g = 3} = 728 := by omega
  have h2cl3 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 3} = 2 := by
    rw [← h2cl]
    exact card_classes_congr fun g => by
      constructor
      · intro h
        exact Or.inl h
      · rintro (h | h | h)
        · exact h
        · exact absurd h (hno9 g)
        · exact absurd h (hno27 g)
  have hexp : ∀ P : Sylow 3 G, ∀ x ∈ (P : Subgroup G), x ^ 3 = 1 := by
    intro P x hx
    apply pow_three_eq_one_of_dvd_27 hno
    have h := Subgroup.orderOf_dvd_natCard (P : Subgroup G) hx
    have h27 : Nat.card (P : Subgroup G) = 27 := card_sylow_three_of_card_eq_5616 hG P
    rwa [h27] at h
  obtain ⟨P₀⟩ : Nonempty (Sylow 3 G) := Sylow.nonempty
  have hP₀27 : Nat.card (P₀ : Subgroup G) = 27 := card_sylow_three_of_card_eq_5616 hG P₀
  have : Nontrivial (P₀ : Subgroup G) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hP₀27]; norm_num)
  have hcen := IsPGroup.center_nontrivial P₀.isPGroup'
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center (P₀ : Subgroup G))
  set z₀ : G := ((z : (P₀ : Subgroup G)) : G) with hz₀
  have hz₀1 : z₀ ≠ 1 := fun h => hz (Subtype.ext (Subtype.ext h))
  have hz₀3 : orderOf z₀ = 3 := by
    have hpow : z₀ ^ 3 = 1 := hexp P₀ z₀ (z : (P₀ : Subgroup G)).2
    have h := orderOf_dvd_of_pow_eq_one hpow
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hz₀1
    · exact h1
  have hPz : (P₀ : Subgroup G) ≤ Subgroup.centralizer ({z₀} : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff, hz₀]
    have h := (Subgroup.mem_center_iff.mp z.2) ⟨p, hp⟩
    have h2 := congrArg (fun w : (P₀ : Subgroup G) => (w : G)) h
    simp only [Subgroup.coe_mul] at h2
    exact h2
  have hz27 : 27 ∣ Nat.card (Subgroup.centralizer ({z₀} : Set G)) :=
    hP₀27 ▸ Subgroup.card_dvd_of_le hPz
  have hz54 := card_centralizer_dvd_54_of_orderOf_eq_three hG hcent hinv ht φ hz₀3
  obtain ⟨y, hy3, hzy, hall⟩ := exists_of_card_classes_eq_two _ h2cl3 hz₀3
  have hsum := card_eq_add_card_conjClass (fun g : G => orderOf g = 3) (hinvar (· = 3)) hz₀3 hy3
    hzy hall
  rw [hN3] at hsum
  have hcz := hcl z₀
  have hcy := hcl y
  have hcz54 : Nat.card (Subgroup.centralizer ({z₀} : Set G)) = 54 := by
    obtain ⟨k, hk⟩ := hz27
    have hle := Nat.le_of_dvd (by norm_num) hz54
    have hpos : 0 < Nat.card (Subgroup.centralizer ({z₀} : Set G)) := Nat.card_pos
    rw [hk] at hle hpos hcz
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl
    · exfalso
      have h208 : Nat.card (ConjClasses.mk z₀).carrier = 208 := by omega
      rw [h208] at hsum
      have h520 : Nat.card (ConjClasses.mk y).carrier = 520 := by omega
      rw [h520] at hcy
      omega
    · rw [hk]
  rw [hcz54] at hcz
  have h104 : Nat.card (ConjClasses.mk z₀).carrier = 104 := by omega
  have h624 : Nat.card (ConjClasses.mk y).carrier = 624 := by omega
  have hcy9 : Nat.card (Subgroup.centralizer ({y} : Set G)) = 9 := by
    rw [h624] at hcy
    omega
  have hclasses : ∀ g : G, orderOf g = 3 → IsConj g z₀ ∨ IsConj g y := fun g hg =>
    (hall g hg).imp IsConj.symm IsConj.symm
  have hnonab : ∀ P : Sylow 3 G,
      ∃ a ∈ (P : Subgroup G), ∃ b ∈ (P : Subgroup G), a * b ≠ b * a := by
    obtain ⟨Q, hQ⟩ := (IsPGroup.of_card (p := 3) (n := 1)
      (by rw [Nat.card_zpowers, hy3, pow_one]) : IsPGroup 3 (Subgroup.zpowers y)).exists_le_sylow
    have hyQ : y ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers y)
    have hQna : ∃ a b : (Q : Subgroup G), a * b ≠ b * a := by
      by_contra hcon
      have hall' : ∀ a b : (Q : Subgroup G), a * b = b * a := fun a b => by
        by_contra h
        exact hcon ⟨a, b, h⟩
      have hle : (Q : Subgroup G) ≤ Subgroup.centralizer ({y} : Set G) := fun q hq =>
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (hall' ⟨q, hq⟩ ⟨y, hyQ⟩))
      have h := Subgroup.card_dvd_of_le hle
      have hQ27 : Nat.card (Q : Subgroup G) = 27 := card_sylow_three_of_card_eq_5616 hG Q
      rw [hQ27, hcy9] at h
      norm_num at h
    intro P
    obtain ⟨a, b, hab⟩ := exists_ne_of_mulEquiv (Sylow.equiv Q P) hQna
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  refine ⟨hno, hS', hN3, fun P => ⟨card_sylow_three_of_card_eq_5616 hG P, hnonab P, hexp P⟩,
    h2cl3, ⟨z₀, y, hz₀3, hy3, h104, h624, hcz54, hcy9, hclasses⟩, ?_⟩
  intro a ha ha3
  have hta : t ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp ha).symm
  have h2a : 2 ∣ Nat.card (Subgroup.centralizer ({a} : Set G)) := by
    have h := Subgroup.orderOf_dvd_natCard _ hta
    rwa [ht] at h
  have ha54 : Nat.card (Subgroup.centralizer ({a} : Set G)) = 54 := by
    rcases hclasses a ha3 with h | h
    · obtain ⟨c, rfl⟩ := isConj_iff.mp h.symm
      rw [card_centralizer_conj, hcz54]
    · exfalso
      obtain ⟨c, rfl⟩ := isConj_iff.mp h.symm
      rw [card_centralizer_conj, hcy9] at h2a
      norm_num at h2a
  refine ⟨ha54, ?_⟩
  set H := Subgroup.centralizer ({a} : Set G) with hH
  obtain ⟨S⟩ : Nonempty (Sylow 3 H) := Sylow.nonempty
  have hS27 : Nat.card (S : Subgroup H) = 27 := by
    rw [S.card_eq_multiplicity, ha54, factorization_54_three]
    norm_num
  have hSidx : (S : Subgroup H).index = 2 := by
    have h := (S : Subgroup H).card_mul_index
    rw [hS27, ha54] at h
    omega
  have hn1 : Nat.card (Sylow 3 H) = 1 := by
    have hdvd := Sylow.card_dvd_index S
    rw [hSidx] at hdvd
    have hmod : Nat.card (Sylow 3 H) % 3 = 1 := card_sylow_modEq_one 3 H
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 3 H) := Nat.card_pos
    interval_cases h : Nat.card (Sylow 3 H)
    · rfl
    · omega
  have hsub : Subsingleton (Sylow 3 H) := (Nat.card_eq_one_iff_unique.mp hn1).1
  refine ⟨(S : Subgroup H).map H.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hS27]
  · rintro _ ⟨s, hs, rfl⟩
    apply pow_three_eq_one_of_dvd_27 hno
    have h' : orderOf s ∣ 27 := by
      have := Subgroup.orderOf_dvd_natCard (S : Subgroup H) hs
      rwa [hS27] at this
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
    exact h'
  · intro Q hQH hQ27
    have hQ' : Nat.card (Q.subgroupOf H) = 27 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv, hQ27]
    let SQ : Sylow 3 H := Sylow.ofCard (Q.subgroupOf H)
      (by rw [hQ', ha54, factorization_54_three]; norm_num)
    have hSQ : SQ = S := Subsingleton.elim _ _
    have hQS : Q.subgroupOf H = (S : Subgroup H) := congrArg Sylow.toSubgroup hSQ
    rw [← hQS, Subgroup.map_subgroupOf_eq_of_le hQH]

end Twelve

end CFSG.Semidihedral.GL2Recognition
