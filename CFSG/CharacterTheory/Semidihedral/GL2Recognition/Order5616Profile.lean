module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.Order5616ProfileSupport
public import CFSG.GroupTheory.BurnsideNormalComplement

public section

open scoped Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.GL2ThreeCharacters
open CFSG.TwoRankLowerBound.Helpers (orderOf_eq_of_isConj)

section Thirteen

variable {G : Type*} [Group G]

theorem factorization_5616_thirteen : Nat.factorization 5616 13 = 1 := by
  have h : (5616 : ℕ) = 13 ^ 1 * 432 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem eq_top_of_quotient_comm (hperf : commutator G = ⊤) (K : Subgroup G) [K.Normal]
    (hK : ∀ a b : G ⧸ K, a * b = b * a) : K = ⊤ := by
  have hcomm : IsMulCommutative (G ⧸ K) := ⟨⟨hK⟩⟩
  have h := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  rw [hperf] at h
  exact top_le_iff.mp h

theorem eq_of_dvd_432_of_mod_thirteen {n : ℕ} (hdvd : n ∣ 432) (hmod : n % 13 = 1) :
    n = 1 ∨ n = 27 ∨ n = 144 := by
  have hmem : n ∈ Nat.divisors 432 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have key : ∀ m ∈ Nat.divisors 432, m % 13 = 1 → m = 1 ∨ m = 27 ∨ m = 144 := by decide
  exact key n hmem hmod

theorem centralizer_eq_zpowers_of_orderOf_eq_thirteen
    (hcent : ∀ A : Subgroup G, Nat.card A = 13 → Subgroup.centralizer (A : Set G) = A)
    {g : G} (hg : orderOf g = 13) :
    Subgroup.centralizer ({g} : Set G) = Subgroup.zpowers g := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact hcent _ (by rw [Nat.card_zpowers, hg])

variable [Finite G]

theorem thirteen_subgroup_facts (hG : Nat.card G = 5616) (hperf : commutator G = ⊤)
    (h48 : ∀ u : G, orderOf u = 2 → Nat.card (Subgroup.centralizer ({u} : Set G)) = 48)
    (A : Subgroup G) (hA : Nat.card A = 13) :
    Subgroup.centralizer (A : Set G) = A ∧ Nat.card (Subgroup.normalizer (A : Set G)) = 39 ∧
      Nat.card (Sylow 13 G) = 144 := by
  have hp : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hCodd : ¬ 2 ∣ Nat.card (Subgroup.centralizer (A : Set G)) := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer (A : Set G)) 2 h2
    have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe, hu]
    have hle : A ≤ Subgroup.centralizer ({(u : G)} : Set G) := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp u.2 a ha)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hA, h48 _ hu'] at hdvd
    norm_num at hdvd
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA
  have hAC : A ≤ Subgroup.centralizer (A : Set G) := Subgroup.le_centralizer A
  have hCN := Subgroup.centralizer_le_normalizer (A : Set G)
  have h13 : 13 ∣ Nat.card (Subgroup.centralizer (A : Set G)) := hA ▸ Subgroup.card_dvd_of_le hAC
  let P : Sylow 13 G := Sylow.ofCard A (by rw [hA, hG, factorization_5616_thirteen, pow_one])
  have hPA : (P : Subgroup G) = A := rfl
  have hidx : (P : Subgroup G).index = 432 := by
    have h := A.card_mul_index
    rw [hA, hG] at h
    change A.index = 432
    omega
  have hn : Nat.card (Sylow 13 G) % 13 = 1 := card_sylow_modEq_one 13 G
  have hdvd := Sylow.card_dvd_index P
  rw [hidx] at hdvd
  have hN : Nat.card (Subgroup.normalizer (A : Set G)) * Nat.card (Sylow 13 G) = 5616 := by
    have h := Sylow.card_eq_index_normalizer P
    change Nat.card (Sylow 13 G) = (Subgroup.normalizer (A : Set G)).index at h
    rw [h, Subgroup.card_mul_index, hG]
  have hrel : (Subgroup.centralizer (A : Set G)).relIndex (Subgroup.normalizer (A : Set G)) ∣
      12 := by
    have key := Subgroup.card_dvd_of_injective _
      (QuotientGroup.kerLift_injective A.normalizerMonoidHom)
    rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex,
      IsCyclic.card_mulAut, hA, Nat.totient_prime hp.out] at key
    exact key
  have hCN' : (Subgroup.centralizer (A : Set G)).relIndex (Subgroup.normalizer (A : Set G)) *
      Nat.card (Subgroup.centralizer (A : Set G)) =
        Nat.card (Subgroup.normalizer (A : Set G)) := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (A : Set G))
      (K := Subgroup.normalizer (A : Set G))
    rwa [inf_of_le_left hCN] at h
  set r := (Subgroup.centralizer (A : Set G)).relIndex (Subgroup.normalizer (A : Set G))
    with hr
  set c := Nat.card (Subgroup.centralizer (A : Set G)) with hc
  have hr12 : r ≤ 12 := Nat.le_of_dvd (by norm_num) hrel
  rcases eq_of_dvd_432_of_mod_thirteen hdvd hn with h1 | h27 | h144
  · exfalso
    rw [h1] at hN
    interval_cases r <;> omega
  · exfalso
    rw [h27] at hN
    interval_cases r <;> omega
  · rw [h144] at hN
    have hN39 : Nat.card (Subgroup.normalizer (A : Set G)) = 39 := by omega
    have hc13 : c = 13 := by
      have hc39 : c = 13 ∨ c = 39 := by interval_cases r <;> omega
      rcases hc39 with h | h
      · exact h
      · exfalso
        have hNC : Subgroup.normalizer (A : Set G) = Subgroup.centralizer (A : Set G) :=
          (Subgroup.eq_of_le_of_card_ge hCN (by omega)).symm
        have hP : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) :=
          le_of_eq hNC
        obtain ⟨K, hKn, -, hKidx, -, -, -, -, -, -, hKcomm⟩ :=
          CFSG.GroupTheory.burnside_normal_complement P hP
        have hKtop := eq_top_of_quotient_comm hperf K hKcomm
        rw [hKtop, Subgroup.index_top] at hKidx
        have hP13 : Nat.card P = 13 := hA
        omega
    refine ⟨(Subgroup.eq_of_le_of_card_ge hAC (by omega)).symm, hN39, h144⟩

theorem card_subgroups_thirteen (hG : Nat.card G = 5616) :
    Nat.card {A : Subgroup G // Nat.card A = 13} = Nat.card (Sylow 13 G) := by
  have hp : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine Nat.card_congr
    { toFun := fun A => Sylow.ofCard A.1 (by rw [A.2, hG, factorization_5616_thirteen, pow_one])
      invFun := fun P => ⟨P, (Sylow.card_eq_multiplicity P).trans
        (by rw [hG, factorization_5616_thirteen, pow_one])⟩
      left_inv := fun A => rfl
      right_inv := fun P => Sylow.ext rfl }

theorem card_orderOf_eq_thirteen (hcount : Nat.card {A : Subgroup G // Nat.card A = 13} = 144) :
    Nat.card {g : G // orderOf g = 13} = 1728 := by
  have hp : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let F : {g : G // orderOf g = 13} → {A : Subgroup G // Nat.card A = 13} :=
    fun g => ⟨Subgroup.zpowers g.1, by rw [Nat.card_zpowers, g.2]⟩
  have h := card_eq_mul_of_card_fiber F 12 ?_
  · rw [h, hcount]
  rintro ⟨A, hA⟩
  have hord : ∀ a : A, a ≠ 1 → orderOf (a : G) = 13 := by
    intro a ha
    have hdvd : orderOf (a : G) ∣ 13 := hA ▸ Subgroup.orderOf_dvd_natCard A a.2
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out _ hdvd) with h1 | h1
    · exfalso
      exact ha (Subtype.ext (orderOf_eq_one_iff.mp h1))
    · exact h1
  have hfib : {x : {g : G // orderOf g = 13} // F x = ⟨A, hA⟩} ≃ {a : A // a ≠ 1} :=
    { toFun := fun x => ⟨⟨x.1.1, by
          have h := congrArg Subtype.val x.2
          change Subgroup.zpowers x.1.1 = A at h
          have hmem : x.1.1 ∈ Subgroup.zpowers x.1.1 := Subgroup.mem_zpowers _
          rw [h] at hmem
          exact hmem⟩, fun h1 => by
          have h := congrArg Subtype.val h1
          change x.1.1 = 1 at h
          have := x.1.2
          rw [h, orderOf_one] at this
          norm_num at this⟩
      invFun := fun a => ⟨⟨a.1, hord a.1 a.2⟩, Subtype.ext (Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr a.1.2) (by rw [hA, Nat.card_zpowers, hord a.1 a.2]))⟩
      left_inv := fun x => rfl
      right_inv := fun a => rfl }
  rw [Nat.card_congr hfib]
  have : Fintype A := Fintype.ofFinite A
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    ← Nat.card_eq_fintype_card, hA]

end Thirteen


section Profile

variable {G : Type*} [Group G] [Finite G] {t : G}

theorem card_conjClass_of_even_orderOf (hG : Nat.card G = 5616)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) {g : G} (hg : Even (orderOf g)) :
    (orderOf g = 2 → Nat.card (ConjClasses.mk g).carrier = 117) ∧
    (orderOf g = 4 → Nat.card (ConjClasses.mk g).carrier = 702) ∧
    (orderOf g = 6 → Nat.card (ConjClasses.mk g).carrier = 936) ∧
    (orderOf g = 8 → Nat.card (ConjClasses.mk g).carrier = 702) := by
  have := Fintype.ofFinite G
  obtain ⟨-, h2, h4, h6, h8⟩ := card_centralizer_of_even_orderOf hinv ht φ hg
  have h := CFSG.LyonsUnitaryFour.card_conjClass_mul_card_centralizer g
  rw [hG] at h
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_⟩
  · rw [h2 hk] at h
    omega
  · rw [h4 hk] at h
    omega
  · rw [h6 hk] at h
    omega
  · rw [h8 hk] at h
    omega

theorem card_conjClass_of_orderOf_eq_thirteen (hG : Nat.card G = 5616)
    (hcent : ∀ A : Subgroup G, Nat.card A = 13 → Subgroup.centralizer (A : Set G) = A)
    {g : G} (hg : orderOf g = 13) : Nat.card (ConjClasses.mk g).carrier = 432 := by
  have := Fintype.ofFinite G
  have h := CFSG.LyonsUnitaryFour.card_conjClass_mul_card_centralizer g
  rw [centralizer_eq_zpowers_of_orderOf_eq_thirteen hcent hg, Nat.card_zpowers, hg, hG] at h
  omega

theorem orderOf_eq_three_pow_of_odd (hG : Nat.card G = 5616)
    (hcent : ∀ A : Subgroup G, Nat.card A = 13 → Subgroup.centralizer (A : Set G) = A)
    {g : G} (hg1 : g ≠ 1) (hodd : ¬ Even (orderOf g)) (h13 : orderOf g ≠ 13) :
    orderOf g = 3 ∨ orderOf g = 9 ∨ orderOf g = 27 := by
  have hdvd : orderOf g ∣ 16 * 351 := by
    have h := orderOf_dvd_natCard g
    rw [hG] at h
    exact h
  have hcop : Nat.Coprime (orderOf g) 16 := by
    have h2 : Nat.Coprime (orderOf g) 2 :=
      Nat.coprime_two_right.mpr (Nat.not_even_iff_odd.mp hodd)
    have h := Nat.Coprime.pow_right 4 h2
    norm_num at h
    exact h
  have h351 : orderOf g ∣ 351 := Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
  have hne1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  have hno : ¬ (3 ∣ orderOf g ∧ 13 ∣ orderOf g) := by
    rintro ⟨h3, h13'⟩
    have hy : orderOf (g ^ (orderOf g / 13)) = 13 :=
      orderOf_pow_orderOf_div (orderOf_pos g).ne' h13'
    have hx : orderOf (g ^ (orderOf g / 3)) = 3 := orderOf_pow_orderOf_div (orderOf_pos g).ne' h3
    have hmem : g ^ (orderOf g / 3) ∈ Subgroup.centralizer ({g ^ (orderOf g / 13)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Commute.refl g).pow_pow _ _).eq
    rw [centralizer_eq_zpowers_of_orderOf_eq_thirteen hcent hy] at hmem
    have h := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hx, Nat.card_zpowers, hy] at h
    norm_num at h
  have hmem : orderOf g ∈ Nat.divisors 351 := Nat.mem_divisors.mpr ⟨h351, by norm_num⟩
  have key : ∀ m ∈ Nat.divisors 351, m ≠ 1 → m ≠ 13 → ¬ (3 ∣ m ∧ 13 ∣ m) →
      m = 3 ∨ m = 9 ∨ m = 27 := by decide
  exact key _ hmem hne1 h13 hno

theorem orderOf_a0_sq : orderOf (a0 ^ 2) = 4 := by
  rw [orderOf_pow' a0 two_ne_zero, orderOf_a0]
  norm_num

theorem order5616_classes (hG : Nat.card G = 5616) (hperf : commutator G = ⊤)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) :
    (∀ A : Subgroup G, Nat.card A = 13 →
      Subgroup.centralizer (A : Set G) = A ∧ Nat.card (Subgroup.normalizer (A : Set G)) = 39) ∧
    Nat.card {A : Subgroup G // Nat.card A = 13} = 144 ∧
    Nat.card {g : G // orderOf g = 13} = 1728 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 13} = 4 ∧
    (∀ g : G, orderOf g = 13 → Nat.card (ConjClasses.mk g).carrier = 432) ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 2} = 1 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 4} = 1 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 6} = 1 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 8} = 2 ∧
    Nat.card {g : G // orderOf g = 2} = 117 ∧ Nat.card {g : G // orderOf g = 4} = 702 ∧
    Nat.card {g : G // orderOf g = 6} = 936 ∧ Nat.card {g : G // orderOf g = 8} = 1404 ∧
    (∀ g : G, orderOf g ∈ ({1, 2, 4, 6, 8, 13, 3, 9, 27} : Finset ℕ)) ∧
    Nat.card {g : G // orderOf g = 3 ∨ orderOf g = 9 ∨ orderOf g = 27} = 728 := by
  have h48 : ∀ u : G, orderOf u = 2 → Nat.card (Subgroup.centralizer ({u} : Set G)) = 48 :=
    fun u hu => card_centralizer_involution hinv ht φ hu
  have h13 := thirteen_subgroup_facts hG hperf h48
  have hcent : ∀ A : Subgroup G, Nat.card A = 13 → Subgroup.centralizer (A : Set G) = A :=
    fun A hA => (h13 A hA).1
  have hnsub : Nat.card {A : Subgroup G // Nat.card A = 13} = 144 := by
    rw [card_subgroups_thirteen hG]
    have hp : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    obtain ⟨P⟩ : Nonempty (Sylow 13 G) := Sylow.nonempty
    exact (h13 (P : Subgroup G) ((Sylow.card_eq_multiplicity P).trans
      (by rw [hG, factorization_5616_thirteen, pow_one]))).2.2
  have hN13 := card_orderOf_eq_thirteen hnsub
  have hsize13 : ∀ g : G, orderOf g = 13 → Nat.card (ConjClasses.mk g).carrier = 432 :=
    fun g hg => card_conjClass_of_orderOf_eq_thirteen hG hcent hg
  have hinvar : ∀ (Q : ℕ → Prop) (g h : G), IsConj g h → Q (orderOf g) → Q (orderOf h) :=
    fun Q g h hgh hg => (orderOf_eq_of_isConj hgh) ▸ hg
  have hcl13 := card_eq_mul_card_classes (fun g : G => orderOf g = 13)
    (hinvar (· = 13)) 432 hsize13
  rw [hN13] at hcl13
  have hev : ∀ k : ℕ, k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 8 → Even k := by
    rintro k (rfl | rfl | rfl | rfl) <;> decide
  have hsize : ∀ g : G, Even (orderOf g) → _ := fun g hg =>
    card_conjClass_of_even_orderOf hG hinv ht φ hg
  have hord : ∀ y : G23, orderOf ((φ.symm y : Subgroup.centralizer ({t} : Set G)) : G) =
      orderOf y := fun y => by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have hcl2 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 2} = 1 :=
    card_classes_eq_one (fun g : G => orderOf g = 2) ht fun g hg => hinv t g ht hg
  have hcl4 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 4} = 1 :=
    card_classes_eq_one (fun g : G => orderOf g = 4) (x := ((φ.symm (a0 ^ 2) :
      Subgroup.centralizer ({t} : Set G)) : G)) (by rw [hord, orderOf_a0_sq])
      fun g hg => isConj_of_orderOf_eq_four_or_six hinv ht φ (by rw [hord, orderOf_a0_sq, hg])
        (Or.inl (by rw [hord, orderOf_a0_sq]))
  have hcl6 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 6} = 1 :=
    card_classes_eq_one (fun g : G => orderOf g = 6) (x := ((φ.symm c0 :
      Subgroup.centralizer ({t} : Set G)) : G)) (by rw [hord, orderOf_c0])
      fun g hg => isConj_of_orderOf_eq_four_or_six hinv ht φ (by rw [hord, orderOf_c0, hg])
        (Or.inr (by rw [hord, orderOf_c0]))
  obtain ⟨h8a, h8b, h8n, h8c⟩ := order_eight_classes hinv ht φ
  have hcl8 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 8} = 2 :=
    card_classes_eq_two (fun g : G => orderOf g = 8) h8a h8b h8n h8c
  have hN2 := card_eq_mul_card_classes (fun g : G => orderOf g = 2) (hinvar (· = 2)) 117
    fun g hg => (hsize g (hev _ (Or.inl hg))).1 hg
  have hN4 := card_eq_mul_card_classes (fun g : G => orderOf g = 4) (hinvar (· = 4)) 702
    fun g hg => (hsize g (hev _ (Or.inr (Or.inl hg)))).2.1 hg
  have hN6 := card_eq_mul_card_classes (fun g : G => orderOf g = 6) (hinvar (· = 6)) 936
    fun g hg => (hsize g (hev _ (Or.inr (Or.inr (Or.inl hg))))).2.2.1 hg
  have hN8 := card_eq_mul_card_classes (fun g : G => orderOf g = 8) (hinvar (· = 8)) 702
    fun g hg => (hsize g (hev _ (Or.inr (Or.inr (Or.inr hg))))).2.2.2 hg
  rw [hcl2] at hN2
  rw [hcl4] at hN4
  rw [hcl6] at hN6
  rw [hcl8] at hN8
  have hS : ∀ g : G, orderOf g ∈ ({1, 2, 4, 6, 8, 13, 3, 9, 27} : Finset ℕ) := by
    intro g
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hg1 : g = 1
    · left
      rw [hg1, orderOf_one]
    by_cases he : Even (orderOf g)
    · rcases (card_centralizer_of_even_orderOf hinv ht φ he).1 with h | h | h | h <;> simp [h]
    by_cases h13' : orderOf g = 13
    · simp [h13']
    rcases orderOf_eq_three_pow_of_odd hG hcent hg1 he h13' with h | h | h <;> simp [h]
  have hsum := card_eq_sum_card_orderOf _ hS
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at hsum
  have hN1 : Nat.card {g : G // orderOf g = 1} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, orderOf_one⟩, fun g => Subtype.ext (orderOf_eq_one_iff.mp g.2)⟩
  have h3pow : Nat.card {g : G // orderOf g = 3 ∨ orderOf g = 9 ∨ orderOf g = 27} =
      Nat.card {g : G // orderOf g = 3} + Nat.card {g : G // orderOf g = 9} +
        Nat.card {g : G // orderOf g = 27} := by
    have h := card_orderOf_mem_eq_sum (G := G) ({3, 9, 27} : Finset ℕ)
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h
    rw [← add_assoc] at h
    rw [← h]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp)
  refine ⟨fun A hA => ⟨(h13 A hA).1, (h13 A hA).2.1⟩, hnsub, hN13, by omega, hsize13, hcl2, hcl4,
    hcl6, hcl8, by omega, by omega, by omega, by omega, hS, by omega⟩

end Profile


section Main

variable {G : Type*} [Group G] [Finite G]

theorem perfect_order5616_GL2_centralizer_conjugacy_profile (hG : Nat.card G = 5616)
    (hperf : commutator G = ⊤)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) {t : G} (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer {t} ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) :
    (∀ A : Subgroup G, Nat.card A = 13 →
      Subgroup.centralizer (A : Set G) = A ∧ Nat.card (Subgroup.normalizer (A : Set G)) = 39) ∧
    Nat.card {A : Subgroup G // Nat.card A = 13} = 144 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 13} = 4 ∧
    (∀ g : G, orderOf g = 13 → Nat.card (ConjClasses.mk g).carrier = 432) ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ Even (orderOf g)} = 5 ∧
    (∀ g : G, Even (orderOf g) →
      orderOf g = 2 ∨ orderOf g = 4 ∨ orderOf g = 6 ∨ orderOf g = 8) ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 2} = 1 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 4} = 1 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 6} = 1 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 8} = 2 ∧
    (∀ g : G, orderOf g = 2 → Nat.card (ConjClasses.mk g).carrier = 117) ∧
    (∀ g : G, orderOf g = 4 → Nat.card (ConjClasses.mk g).carrier = 702) ∧
    (∀ g : G, orderOf g = 6 → Nat.card (ConjClasses.mk g).carrier = 936) ∧
    (∀ g : G, orderOf g = 8 → Nat.card (ConjClasses.mk g).carrier = 702) ∧
    (∀ g : G, g ≠ 1 → ¬ Even (orderOf g) → orderOf g ≠ 13 →
      orderOf g = 3 ∨ orderOf g = 9 ∨ orderOf g = 27) ∧
    Nat.card {g : G // orderOf g = 3 ∨ orderOf g = 9 ∨ orderOf g = 27} = 728 ∧
    (Nat.card (ConjClasses G) = 12 →
      Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧
        (orderOf g = 3 ∨ orderOf g = 9 ∨ orderOf g = 27)} = 2) := by
  obtain ⟨φ⟩ := hC
  obtain ⟨h13, hnsub, -, hcl13, hsize13, hcl2, hcl4, hcl6, hcl8, -, -, -, -, -, h728⟩ :=
    order5616_classes hG hperf hinv ht φ
  have hcent : ∀ A : Subgroup G, Nat.card A = 13 → Subgroup.centralizer (A : Set G) = A :=
    fun A hA => (h13 A hA).1
  have hevord : ∀ g : G, Even (orderOf g) →
      orderOf g = 2 ∨ orderOf g = 4 ∨ orderOf g = 6 ∨ orderOf g = 8 :=
    fun g hg => (card_centralizer_of_even_orderOf hinv ht φ hg).1
  have hsize := fun (g : G) (hg : Even (orderOf g)) =>
    card_conjClass_of_even_orderOf hG hinv ht φ hg
  have hevcl : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ Even (orderOf g)} =
      5 := by
    rw [card_classes_congr (P := fun g : G => Even (orderOf g))
      (Q := fun g : G => (orderOf g = 2 ∨ orderOf g = 4) ∨ (orderOf g = 6 ∨ orderOf g = 8))
      fun g => ⟨fun h => by rcases hevord g h with h' | h' | h' | h' <;> simp [h'],
        fun h => by rcases h with (h' | h') | (h' | h') <;> rw [h'] <;> decide⟩]
    rw [card_classes_or (fun g : G => orderOf g = 2 ∨ orderOf g = 4)
        (fun g : G => orderOf g = 6 ∨ orderOf g = 8)
        (fun _ _ hgh hg => orderOf_pred_of_isConj (fun n => n = 2 ∨ n = 4) hgh hg)
        (fun g h h' => by omega),
      card_classes_or (fun g : G => orderOf g = 2) (fun g : G => orderOf g = 4)
        (fun _ _ hgh hg => orderOf_pred_of_isConj (· = 2) hgh hg) (fun g h h' => by omega),
      card_classes_or (fun g : G => orderOf g = 6) (fun g : G => orderOf g = 8)
        (fun _ _ hgh hg => orderOf_pred_of_isConj (· = 6) hgh hg) (fun g h h' => by omega),
      hcl2, hcl4, hcl6, hcl8]
  refine ⟨h13, hnsub, hcl13, hsize13, hevcl, hevord, hcl2, hcl4, hcl6, hcl8,
    fun g hg => (hsize g (by rw [hg]; decide)).1 hg,
    fun g hg => (hsize g (by rw [hg]; decide)).2.1 hg,
    fun g hg => (hsize g (by rw [hg]; decide)).2.2.1 hg,
    fun g hg => (hsize g (by rw [hg]; decide)).2.2.2 hg,
    fun g hg1 hodd h13' => orderOf_eq_three_pow_of_odd hG hcent hg1 hodd h13', h728, ?_⟩
  intro h12
  have hall : ∀ g : G, (orderOf g = 1 ∨ Even (orderOf g)) ∨
      (orderOf g = 13 ∨ (orderOf g = 3 ∨ orderOf g = 9 ∨ orderOf g = 27)) := by
    intro g
    by_cases hg1 : g = 1
    · exact Or.inl (Or.inl (by rw [hg1, orderOf_one]))
    by_cases he : Even (orderOf g)
    · exact Or.inl (Or.inr he)
    by_cases h13' : orderOf g = 13
    · exact Or.inr (Or.inl h13')
    exact Or.inr (Or.inr (orderOf_eq_three_pow_of_odd hG hcent hg1 he h13'))
  have htot := card_classes_of_forall _ hall
  rw [card_classes_or (fun g : G => orderOf g = 1 ∨ Even (orderOf g))
      (fun g : G => orderOf g = 13 ∨ (orderOf g = 3 ∨ orderOf g = 9 ∨ orderOf g = 27))
      (fun _ _ hgh hg => orderOf_pred_of_isConj (fun n => n = 1 ∨ Even n) hgh hg)
      (fun g h h' => by rw [Nat.even_iff] at h; omega),
    card_classes_or (fun g : G => orderOf g = 1) (fun g : G => Even (orderOf g))
      (fun _ _ hgh hg => orderOf_pred_of_isConj (· = 1) hgh hg)
      (fun g h h' => by rw [Nat.even_iff] at h'; omega),
    card_classes_or (fun g : G => orderOf g = 13)
      (fun g : G => orderOf g = 3 ∨ orderOf g = 9 ∨ orderOf g = 27)
      (fun _ _ hgh hg => orderOf_pred_of_isConj (· = 13) hgh hg) (fun g h h' => by omega),
    card_classes_orderOf_eq_one, hevcl, hcl13, h12] at htot
  omega

theorem perfect_order5616_GL2_centralizer_element_profile (hG : Nat.card G = 5616)
    (hperf : commutator G = ⊤)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) {t : G} (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer {t} ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) :
    Nat.card {g : G // orderOf g = 2} = 117 ∧
    (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) ∧
    (∀ g : G, orderOf g = 2 → Nat.card (ConjClasses.mk g).carrier = 117) ∧
    Nat.card {g : G // orderOf g = 4} = 702 ∧
    (∀ u v : G, orderOf u = 4 → orderOf v = 4 → IsConj u v) ∧
    (∀ g : G, orderOf g = 4 → Nat.card (ConjClasses.mk g).carrier = 702) ∧
    Nat.card {g : G // orderOf g = 6} = 936 ∧
    (∀ u v : G, orderOf u = 6 → orderOf v = 6 → IsConj u v) ∧
    (∀ g : G, orderOf g = 6 → Nat.card (ConjClasses.mk g).carrier = 936) ∧
    Nat.card {g : G // orderOf g = 8} = 1404 ∧
    (∃ x y : G, orderOf x = 8 ∧ orderOf y = 8 ∧ ¬ IsConj x y ∧
      ∀ z : G, orderOf z = 8 → IsConj z x ∨ IsConj z y) ∧
    (∀ g : G, orderOf g = 8 → Nat.card (ConjClasses.mk g).carrier = 702) ∧
    Nat.card {g : G // orderOf g = 13} = 1728 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 13} = 4 ∧
    (∀ g : G, orderOf g = 13 → Nat.card (ConjClasses.mk g).carrier = 432) ∧
    (∀ A : Subgroup G, Nat.card A = 13 →
      Subgroup.centralizer (A : Set G) = A ∧ Nat.card (Subgroup.normalizer (A : Set G)) = 39) ∧
    (∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 6, 8, 9, 13, 27} : Finset ℕ)) ∧
    Nat.card {g : G // orderOf g = 3 ∨ orderOf g = 9 ∨ orderOf g = 27} = 728 := by
  obtain ⟨φ⟩ := hC
  obtain ⟨h13, -, hN13, hcl13, hsize13, -, -, -, -, hN2, hN4, hN6, hN8, hS, h728⟩ :=
    order5616_classes hG hperf hinv ht φ
  have hsize := fun (g : G) (hg : Even (orderOf g)) =>
    card_conjClass_of_even_orderOf hG hinv ht φ hg
  have hconj : ∀ k : ℕ, k = 4 ∨ k = 6 → ∀ u v : G, orderOf u = k → orderOf v = k → IsConj u v := by
    rintro k hk u v hu hv
    exact isConj_of_orderOf_eq_four_or_six hinv ht φ (hu.trans hv.symm) (hu ▸ hk)
  obtain ⟨h8a, h8b, h8n, h8c⟩ := order_eight_classes hinv ht φ
  refine ⟨hN2, hinv, fun g hg => (hsize g (by rw [hg]; decide)).1 hg, hN4, hconj 4 (Or.inl rfl),
    fun g hg => (hsize g (by rw [hg]; decide)).2.1 hg, hN6, hconj 6 (Or.inr rfl),
    fun g hg => (hsize g (by rw [hg]; decide)).2.2.1 hg, hN8,
    ⟨_, _, h8a, h8b, h8n, fun z hz => (h8c z hz).imp IsConj.symm IsConj.symm⟩,
    fun g hg => (hsize g (by rw [hg]; decide)).2.2.2 hg, hN13, hcl13, hsize13, h13,
    fun g => ?_, h728⟩
  have h := hS g
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  omega

end Main

end CFSG.Semidihedral.GL2Recognition
