module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.Order5616Profile
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.DegreeTwelveSupport
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.ConjugateRepresentation
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.TraceValues
public import CFSG.LocalAnalysis.LyonsUnitaryFour.RationalBound.TraceGap

public section

open scoped Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.GL2ThreeCharacters
open CFSG.TwoRankLowerBound.Helpers (orderOf_eq_of_isConj)

namespace Order7920

section Eleven

variable {G : Type*} [Group G]

theorem factorization_7920_eleven : Nat.factorization 7920 11 = 1 := by
  have h : (7920 : ℕ) = 11 ^ 1 * 720 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem eq_of_dvd_720_of_mod_eleven {n : ℕ} (hdvd : n ∣ 720) (hmod : n % 11 = 1) :
    n = 1 ∨ n = 12 ∨ n = 45 ∨ n = 144 := by
  have hmem : n ∈ Nat.divisors 720 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have key : ∀ m ∈ Nat.divisors 720, m % 11 = 1 → m = 1 ∨ m = 12 ∨ m = 45 ∨ m = 144 := by
    decide +kernel
  exact key n hmem hmod

theorem centralizer_eq_zpowers_of_orderOf_eq_eleven
    (hcent : ∀ A : Subgroup G, Nat.card A = 11 → Subgroup.centralizer (A : Set G) = A)
    {g : G} (hg : orderOf g = 11) :
    Subgroup.centralizer ({g} : Set G) = Subgroup.zpowers g := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact hcent _ (by rw [Nat.card_zpowers, hg])

variable [Finite G]

theorem eleven_subgroup_facts (hG : Nat.card G = 7920) (hperf : commutator G = ⊤)
    (h48 : ∀ u : G, orderOf u = 2 → Nat.card (Subgroup.centralizer ({u} : Set G)) = 48)
    (A : Subgroup G) (hA : Nat.card A = 11) :
    Subgroup.centralizer (A : Set G) = A ∧ Nat.card (Subgroup.normalizer (A : Set G)) = 55 ∧
      Nat.card (Sylow 11 G) = 144 := by
  have hp : Fact (Nat.Prime 11) := ⟨by norm_num⟩
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
  have h11 : 11 ∣ Nat.card (Subgroup.centralizer (A : Set G)) :=
    hA ▸ Subgroup.card_dvd_of_le hAC
  let P : Sylow 11 G := Sylow.ofCard A (by rw [hA, hG, factorization_7920_eleven, pow_one])
  have hidx : (P : Subgroup G).index = 720 := by
    have h := A.card_mul_index
    rw [hA, hG] at h
    change A.index = 720
    omega
  have hn : Nat.card (Sylow 11 G) % 11 = 1 := card_sylow_modEq_one 11 G
  have hdvd := Sylow.card_dvd_index P
  rw [hidx] at hdvd
  have hN : Nat.card (Subgroup.normalizer (A : Set G)) * Nat.card (Sylow 11 G) = 7920 := by
    have h := Sylow.card_eq_index_normalizer P
    change Nat.card (Sylow 11 G) = (Subgroup.normalizer (A : Set G)).index at h
    rw [h, Subgroup.card_mul_index, hG]
  have hrel : (Subgroup.centralizer (A : Set G)).relIndex (Subgroup.normalizer (A : Set G)) ∣
      10 := by
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
  have hr10 : r ≤ 10 := Nat.le_of_dvd (by norm_num) hrel
  rcases eq_of_dvd_720_of_mod_eleven hdvd hn with h1 | h12 | h45 | h144
  · exfalso
    rw [h1] at hN
    interval_cases r <;> omega
  · exfalso
    rw [h12] at hN
    interval_cases r <;> omega
  · exfalso
    rw [h45] at hN
    interval_cases r <;> omega
  · rw [h144] at hN
    have hN55 : Nat.card (Subgroup.normalizer (A : Set G)) = 55 := by omega
    have hc11 : c = 11 := by
      have hc55 : c = 11 ∨ c = 55 := by interval_cases r <;> omega
      rcases hc55 with h | h
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
        have hP11 : Nat.card P = 11 := hA
        omega
    refine ⟨(Subgroup.eq_of_le_of_card_ge hAC (by omega)).symm, hN55, h144⟩

theorem card_subgroups_eleven (hG : Nat.card G = 7920) :
    Nat.card {A : Subgroup G // Nat.card A = 11} = Nat.card (Sylow 11 G) := by
  have hp : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine Nat.card_congr
    { toFun := fun A => Sylow.ofCard A.1 (by rw [A.2, hG, factorization_7920_eleven, pow_one])
      invFun := fun P => ⟨P, (Sylow.card_eq_multiplicity P).trans
        (by rw [hG, factorization_7920_eleven, pow_one])⟩
      left_inv := fun A => rfl
      right_inv := fun P => Sylow.ext rfl }

theorem card_orderOf_eq_eleven (hcount : Nat.card {A : Subgroup G // Nat.card A = 11} = 144) :
    Nat.card {g : G // orderOf g = 11} = 1440 := by
  have hp : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let F : {g : G // orderOf g = 11} → {A : Subgroup G // Nat.card A = 11} :=
    fun g => ⟨Subgroup.zpowers g.1, by rw [Nat.card_zpowers, g.2]⟩
  have h := card_eq_mul_of_card_fiber F 10 ?_
  · rw [h, hcount]
  rintro ⟨A, hA⟩
  have hord : ∀ a : A, a ≠ 1 → orderOf (a : G) = 11 := by
    intro a ha
    have hdvd : orderOf (a : G) ∣ 11 := hA ▸ Subgroup.orderOf_dvd_natCard A a.2
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out _ hdvd) with h1 | h1
    · exfalso
      exact ha (Subtype.ext (orderOf_eq_one_iff.mp h1))
    · exact h1
  have hfib : {x : {g : G // orderOf g = 11} // F x = ⟨A, hA⟩} ≃ {a : A // a ≠ 1} :=
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

end Eleven

section Profile

variable {G : Type*} [Group G] [Finite G] {t : G}

theorem card_conjClass_of_even_orderOf (hG : Nat.card G = 7920)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) {g : G} (hg : Even (orderOf g)) :
    (orderOf g = 2 → Nat.card (ConjClasses.mk g).carrier = 165) ∧
    (orderOf g = 4 → Nat.card (ConjClasses.mk g).carrier = 990) ∧
    (orderOf g = 6 → Nat.card (ConjClasses.mk g).carrier = 1320) ∧
    (orderOf g = 8 → Nat.card (ConjClasses.mk g).carrier = 990) := by
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

theorem card_conjClass_of_orderOf_eq_eleven (hG : Nat.card G = 7920)
    (hcent : ∀ A : Subgroup G, Nat.card A = 11 → Subgroup.centralizer (A : Set G) = A)
    {g : G} (hg : orderOf g = 11) : Nat.card (ConjClasses.mk g).carrier = 720 := by
  have := Fintype.ofFinite G
  have h := CFSG.LyonsUnitaryFour.card_conjClass_mul_card_centralizer g
  rw [centralizer_eq_zpowers_of_orderOf_eq_eleven hcent hg, Nat.card_zpowers, hg, hG] at h
  omega

theorem orderOf_of_odd (hG : Nat.card G = 7920)
    (hcent : ∀ A : Subgroup G, Nat.card A = 11 → Subgroup.centralizer (A : Set G) = A)
    {g : G} (hg1 : g ≠ 1) (hodd : ¬ Even (orderOf g)) (h11 : orderOf g ≠ 11) :
    orderOf g = 3 ∨ orderOf g = 5 ∨ orderOf g = 9 ∨ orderOf g = 15 ∨ orderOf g = 45 := by
  have hdvd : orderOf g ∣ 16 * 495 := by
    have h := orderOf_dvd_natCard g
    rw [hG] at h
    exact h
  have hcop : Nat.Coprime (orderOf g) 16 := by
    have h2 : Nat.Coprime (orderOf g) 2 :=
      Nat.coprime_two_right.mpr (Nat.not_even_iff_odd.mp hodd)
    have h := Nat.Coprime.pow_right 4 h2
    norm_num at h
    exact h
  have h495 : orderOf g ∣ 495 := Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
  have hne1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  have hno : ∀ p : ℕ, p = 3 ∨ p = 5 → ¬ (p ∣ orderOf g ∧ 11 ∣ orderOf g) := by
    rintro p hp ⟨hpd, h11'⟩
    have hy : orderOf (g ^ (orderOf g / 11)) = 11 :=
      orderOf_pow_orderOf_div (orderOf_pos g).ne' h11'
    have hx : orderOf (g ^ (orderOf g / p)) = p := orderOf_pow_orderOf_div (orderOf_pos g).ne' hpd
    have hmem : g ^ (orderOf g / p) ∈ Subgroup.centralizer ({g ^ (orderOf g / 11)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Commute.refl g).pow_pow _ _).eq
    rw [centralizer_eq_zpowers_of_orderOf_eq_eleven hcent hy] at hmem
    have h := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hx, Nat.card_zpowers, hy] at h
    rcases hp with rfl | rfl <;> norm_num at h
  have hmem : orderOf g ∈ Nat.divisors 495 := Nat.mem_divisors.mpr ⟨h495, by norm_num⟩
  have key : ∀ m ∈ Nat.divisors 495, m ≠ 1 → m ≠ 11 → ¬ (3 ∣ m ∧ 11 ∣ m) →
      ¬ (5 ∣ m ∧ 11 ∣ m) → m = 3 ∨ m = 5 ∨ m = 9 ∨ m = 15 ∨ m = 45 := by decide +kernel
  exact key _ hmem hne1 h11 (hno 3 (Or.inl rfl)) (hno 5 (Or.inr rfl))

theorem order7920_classes (hG : Nat.card G = 7920) (hperf : commutator G = ⊤)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) :
    (∀ A : Subgroup G, Nat.card A = 11 →
      Subgroup.centralizer (A : Set G) = A ∧ Nat.card (Subgroup.normalizer (A : Set G)) = 55) ∧
    Nat.card {A : Subgroup G // Nat.card A = 11} = 144 ∧
    Nat.card {g : G // orderOf g = 11} = 1440 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 11} = 2 ∧
    (∀ g : G, orderOf g = 11 → Nat.card (ConjClasses.mk g).carrier = 720) ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 2} = 1 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 4} = 1 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 6} = 1 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 8} = 2 ∧
    Nat.card {g : G // orderOf g = 2} = 165 ∧ Nat.card {g : G // orderOf g = 4} = 990 ∧
    Nat.card {g : G // orderOf g = 6} = 1320 ∧ Nat.card {g : G // orderOf g = 8} = 1980 ∧
    (∀ g : G, orderOf g ∈ ({1, 2, 4, 6, 8, 11, 3, 5, 9, 15, 45} : Finset ℕ)) ∧
    Nat.card {g : G // orderOf g = 3 ∨ orderOf g = 5 ∨ orderOf g = 9 ∨ orderOf g = 15 ∨
      orderOf g = 45} = 2024 := by
  have h48 : ∀ u : G, orderOf u = 2 → Nat.card (Subgroup.centralizer ({u} : Set G)) = 48 :=
    fun u hu => card_centralizer_involution hinv ht φ hu
  have h11 := eleven_subgroup_facts hG hperf h48
  have hcent : ∀ A : Subgroup G, Nat.card A = 11 → Subgroup.centralizer (A : Set G) = A :=
    fun A hA => (h11 A hA).1
  have hnsub : Nat.card {A : Subgroup G // Nat.card A = 11} = 144 := by
    rw [card_subgroups_eleven hG]
    have hp : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    obtain ⟨P⟩ : Nonempty (Sylow 11 G) := Sylow.nonempty
    exact (h11 (P : Subgroup G) ((Sylow.card_eq_multiplicity P).trans
      (by rw [hG, factorization_7920_eleven, pow_one]))).2.2
  have hN11 := card_orderOf_eq_eleven hnsub
  have hsize11 : ∀ g : G, orderOf g = 11 → Nat.card (ConjClasses.mk g).carrier = 720 :=
    fun g hg => card_conjClass_of_orderOf_eq_eleven hG hcent hg
  have hinvar : ∀ (Q : ℕ → Prop) (g h : G), IsConj g h → Q (orderOf g) → Q (orderOf h) :=
    fun Q g h hgh hg => (orderOf_eq_of_isConj hgh) ▸ hg
  have hcl11 := card_eq_mul_card_classes (fun g : G => orderOf g = 11)
    (hinvar (· = 11)) 720 hsize11
  rw [hN11] at hcl11
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
  have hN2 := card_eq_mul_card_classes (fun g : G => orderOf g = 2) (hinvar (· = 2)) 165
    fun g hg => (hsize g (hev _ (Or.inl hg))).1 hg
  have hN4 := card_eq_mul_card_classes (fun g : G => orderOf g = 4) (hinvar (· = 4)) 990
    fun g hg => (hsize g (hev _ (Or.inr (Or.inl hg)))).2.1 hg
  have hN6 := card_eq_mul_card_classes (fun g : G => orderOf g = 6) (hinvar (· = 6)) 1320
    fun g hg => (hsize g (hev _ (Or.inr (Or.inr (Or.inl hg))))).2.2.1 hg
  have hN8 := card_eq_mul_card_classes (fun g : G => orderOf g = 8) (hinvar (· = 8)) 990
    fun g hg => (hsize g (hev _ (Or.inr (Or.inr (Or.inr hg))))).2.2.2 hg
  rw [hcl2] at hN2
  rw [hcl4] at hN4
  rw [hcl6] at hN6
  rw [hcl8] at hN8
  have hS : ∀ g : G, orderOf g ∈ ({1, 2, 4, 6, 8, 11, 3, 5, 9, 15, 45} : Finset ℕ) := by
    intro g
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hg1 : g = 1
    · left
      rw [hg1, orderOf_one]
    by_cases he : Even (orderOf g)
    · rcases (card_centralizer_of_even_orderOf hinv ht φ he).1 with h | h | h | h <;> simp [h]
    by_cases h11' : orderOf g = 11
    · simp [h11']
    rcases orderOf_of_odd hG hcent hg1 he h11' with h | h | h | h | h <;> simp [h]
  have hsum := card_eq_sum_card_orderOf _ hS
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hsum
  have hN1 : Nat.card {g : G // orderOf g = 1} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, orderOf_one⟩, fun g => Subtype.ext (orderOf_eq_one_iff.mp g.2)⟩
  have hrest : Nat.card {g : G // orderOf g = 3 ∨ orderOf g = 5 ∨ orderOf g = 9 ∨
      orderOf g = 15 ∨ orderOf g = 45} =
      Nat.card {g : G // orderOf g = 3} + Nat.card {g : G // orderOf g = 5} +
        Nat.card {g : G // orderOf g = 9} + Nat.card {g : G // orderOf g = 15} +
          Nat.card {g : G // orderOf g = 45} := by
    have h := card_orderOf_mem_eq_sum (G := G) ({3, 5, 9, 15, 45} : Finset ℕ)
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton] at h
    rw [← add_assoc, ← add_assoc, ← add_assoc] at h
    rw [← h]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp)
  refine ⟨fun A hA => ⟨(h11 A hA).1, (h11 A hA).2.1⟩, hnsub, hN11, by omega, hsize11, hcl2,
    hcl4, hcl6, hcl8, by omega, by omega, by omega, by omega, hS, by omega⟩

theorem isConj_or_of_card_classes_eq_two (P : G → Prop)
    (h2 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g} = 2)
    {x y : G} (hx : P x) (hy : P y) (hxy : ¬ IsConj x y) :
    ∀ g, P g → IsConj x g ∨ IsConj y g := by
  intro g hg
  by_contra hcon
  push Not at hcon
  have := Fintype.ofFinite G
  let cx : {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g} :=
    ⟨ConjClasses.mk x, x, rfl, hx⟩
  let cy : {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g} :=
    ⟨ConjClasses.mk y, y, rfl, hy⟩
  let cg : {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g} :=
    ⟨ConjClasses.mk g, g, rfl, hg⟩
  have hxy' : cx ≠ cy := fun h =>
    hxy (ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val h))
  have hxg : cx ≠ cg := fun h =>
    hcon.1 (ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val h))
  have hyg : cy ≠ cg := fun h =>
    hcon.2 (ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val h))
  have h3 : 3 ≤ Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g} := by
    rw [Nat.card_eq_fintype_card]
    have hcard : ({cx, cy, cg} : Finset _).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hyg]
      simp [hxy', hxg]
    exact hcard ▸ Finset.card_le_univ _
  omega

omit [Finite G] in
theorem exists_reps_of_card_classes_eq_two (P : G → Prop)
    (h2 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g} = 2) :
    ∃ x y : G, P x ∧ P y ∧ ¬ IsConj x y ∧ ∀ g, P g → IsConj x g ∨ IsConj y g := by
  obtain ⟨⟨c₁, x, hx, hPx⟩, ⟨c₂, y, hy, hPy⟩, hne, huniv⟩ := Nat.card_eq_two_iff.mp h2
  refine ⟨x, y, hPx, hPy, fun hxy => hne (Subtype.ext ?_), fun g hg => ?_⟩
  · change c₁ = c₂
    exact hx.symm.trans ((ConjClasses.mk_eq_mk_iff_isConj.mpr hxy).trans hy)
  · have hmem : (⟨ConjClasses.mk g, g, rfl, hg⟩ :
        {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g}) ∈
        ({⟨c₁, x, hx, hPx⟩, ⟨c₂, y, hy, hPy⟩} : Set _) := by
      rw [huniv]
      exact Set.mem_univ _
    rcases hmem with h | h
    · left
      have h' := congrArg Subtype.val h
      change ConjClasses.mk g = c₁ at h'
      rw [← hx] at h'
      exact (ConjClasses.mk_eq_mk_iff_isConj.mp h').symm
    · right
      have h' := congrArg Subtype.val h
      change ConjClasses.mk g = c₂ at h'
      rw [← hy] at h'
      exact (ConjClasses.mk_eq_mk_iff_isConj.mp h').symm

theorem card_classes_even (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (ht : orderOf t = 2) (φ : Subgroup.centralizer ({t} : Set G) ≃* G23)
    (hcl2 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 2} = 1)
    (hcl4 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 4} = 1)
    (hcl6 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 6} = 1)
    (hcl8 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 8} = 2) :
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ Even (orderOf g)} = 5 := by
  have hevord : ∀ g : G, Even (orderOf g) →
      orderOf g = 2 ∨ orderOf g = 4 ∨ orderOf g = 6 ∨ orderOf g = 8 :=
    fun g hg => (card_centralizer_of_even_orderOf hinv ht φ hg).1
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

theorem eq_five_of_dvd_7920 {m : ℕ} (hm : m ∣ 7920) (h2 : ¬ 2 ∣ m) (h3 : ¬ 3 ∣ m)
    (h11 : ¬ 11 ∣ m) (h5 : 5 ∣ m) : m = 5 := by
  have hmem : m ∈ Nat.divisors 7920 := Nat.mem_divisors.mpr ⟨hm, by norm_num⟩
  have key : ∀ m ∈ Nat.divisors 7920, ¬ 2 ∣ m → ¬ 3 ∣ m → ¬ 11 ∣ m → 5 ∣ m → m = 5 := by
    decide +kernel
  exact key m hmem h2 h3 h11 h5

theorem order7920_odd_classes (hG : Nat.card G = 7920) (hperf : commutator G = ⊤)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) (h10 : Nat.card (ConjClasses G) = 10) :
    (∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 8, 11} : Finset ℕ)) ∧
    (∀ u v : G, orderOf u = 3 → orderOf v = 3 → IsConj u v) ∧
    (∀ u v : G, orderOf u = 5 → orderOf v = 5 → IsConj u v) ∧
    (∀ x : G, orderOf x = 5 → Nat.card (Subgroup.centralizer ({x} : Set G)) = 5) ∧
    (∀ x : G, orderOf x = 3 → Nat.card (ConjClasses.mk x).carrier = 440) ∧
    (∀ x : G, orderOf x = 5 → Nat.card (ConjClasses.mk x).carrier = 1584) ∧
    Nat.card {g : G // orderOf g = 3} = 440 ∧ Nat.card {g : G // orderOf g = 5} = 1584 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 3} = 1 ∧
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 5} = 1 := by
  have := Fintype.ofFinite G
  obtain ⟨-, -, -, hcl11, -, hcl2, hcl4, hcl6, hcl8, -, -, -, -, hS, h2024⟩ :=
    order7920_classes hG hperf hinv ht φ
  have hevcl := card_classes_even hinv ht φ hcl2 hcl4 hcl6 hcl8
  let R : G → Prop := fun g => orderOf g = 3 ∨ orderOf g = 5 ∨ orderOf g = 9 ∨
    orderOf g = 15 ∨ orderOf g = 45
  have hall : ∀ g : G, (orderOf g = 1 ∨ Even (orderOf g)) ∨ (orderOf g = 11 ∨ R g) := by
    intro g
    have h := hS g
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl (Or.inl h)
    all_goals first
      | exact Or.inl (Or.inr (by rw [h]; decide))
      | exact Or.inr (Or.inl h)
      | exact Or.inr (Or.inr (by simp [R, h]))
  have htot := card_classes_of_forall _ hall
  rw [card_classes_or (fun g : G => orderOf g = 1 ∨ Even (orderOf g))
      (fun g : G => orderOf g = 11 ∨ R g)
      (fun _ _ hgh hg => orderOf_pred_of_isConj (fun n => n = 1 ∨ Even n) hgh hg)
      (fun g h h' => by simp only [R] at h'; rw [Nat.even_iff] at h; omega),
    card_classes_or (fun g : G => orderOf g = 1) (fun g : G => Even (orderOf g))
      (fun _ _ hgh hg => orderOf_pred_of_isConj (· = 1) hgh hg)
      (fun g h h' => by rw [Nat.even_iff] at h'; omega),
    card_classes_or (fun g : G => orderOf g = 11) R
      (fun _ _ hgh hg => orderOf_pred_of_isConj (· = 11) hgh hg)
      (fun g h h' => by simp only [R] at h'; omega),
    card_classes_orderOf_eq_one, hevcl, hcl11, h10] at htot
  have hRcl : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ R g} = 2 := by omega
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x₃, hx₃⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hG]; norm_num)
  obtain ⟨x₅, hx₅⟩ := exists_prime_orderOf_dvd_card' (G := G) 5 (by rw [hG]; norm_num)
  have hx35 : ¬ IsConj x₃ x₅ := fun h => by
    have := orderOf_eq_of_isConj h
    omega
  have hR := isConj_or_of_card_classes_eq_two R hRcl (Or.inl hx₃) (Or.inr (Or.inl hx₅)) hx35
  have hRord : ∀ g, R g → orderOf g = 3 ∨ orderOf g = 5 := by
    intro g hg
    rcases hR g hg with h | h
    · exact Or.inl ((orderOf_eq_of_isConj h).symm.trans hx₃)
    · exact Or.inr ((orderOf_eq_of_isConj h).symm.trans hx₅)
  have horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 8, 11} : Finset ℕ) := by
    intro g
    have h := hS g
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    all_goals first
      | omega
      | (rcases hRord g (by simp [R, h]) with h' | h' <;> omega)
  have hconj3 : ∀ u v : G, orderOf u = 3 → orderOf v = 3 → IsConj u v := by
    intro u v hu hv
    have hu' : IsConj x₃ u := (hR u (Or.inl hu)).resolve_right fun h => by
      have := orderOf_eq_of_isConj h
      omega
    have hv' : IsConj x₃ v := (hR v (Or.inl hv)).resolve_right fun h => by
      have := orderOf_eq_of_isConj h
      omega
    exact hu'.symm.trans hv'
  have hconj5 : ∀ u v : G, orderOf u = 5 → orderOf v = 5 → IsConj u v := by
    intro u v hu hv
    have hu' : IsConj x₅ u := (hR u (Or.inr (Or.inl hu))).resolve_left fun h => by
      have := orderOf_eq_of_isConj h
      omega
    have hv' : IsConj x₅ v := (hR v (Or.inr (Or.inl hv))).resolve_left fun h => by
      have := orderOf_eq_of_isConj h
      omega
    exact hu'.symm.trans hv'
  have hcent5 : ∀ x : G, orderOf x = 5 → Nat.card (Subgroup.centralizer ({x} : Set G)) = 5 := by
    intro x hx
    have hno : ∀ p : ℕ, p.Prime → p ≠ 5 → p ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) →
        5 * p ∈ ({1, 2, 3, 4, 5, 6, 8, 11} : Finset ℕ) := by
      intro p hp hp5 hpd
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({x} : Set G))
        p hpd
      have hy' : orderOf (y : G) = p := by rw [Subgroup.orderOf_coe, hy]
      have hcomm : Commute x (y : G) :=
        (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
      have hcop : (orderOf x).Coprime (orderOf (y : G)) := by
        rw [hx, hy']
        exact (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hp5)
      have h := horders (x * y)
      rwa [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hx, hy'] at h
    have h2 : ¬ 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := fun h => by
      have := hno 2 Nat.prime_two (by norm_num) h
      simp at this
    have h3 : ¬ 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := fun h => by
      have := hno 3 Nat.prime_three (by norm_num) h
      simp at this
    have h11 : ¬ 11 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := fun h => by
      have := hno 11 (by norm_num) (by norm_num) h
      simp at this
    have h5 : 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
      have hmem : x ∈ Subgroup.centralizer ({x} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have h := Subgroup.orderOf_dvd_natCard _ hmem
      rwa [hx] at h
    have hdvd : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 7920 :=
      hG ▸ Subgroup.card_subgroup_dvd_card _
    exact eq_five_of_dvd_7920 hdvd h2 h3 h11 h5
  have hsize5 : ∀ x : G, orderOf x = 5 → Nat.card (ConjClasses.mk x).carrier = 1584 := by
    intro x hx
    have h := CFSG.LyonsUnitaryFour.card_conjClass_mul_card_centralizer x
    rw [hcent5 x hx, hG] at h
    omega
  have hcl5 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 5} = 1 :=
    card_classes_eq_one (fun g : G => orderOf g = 5) hx₅ fun g hg => hconj5 x₅ g hx₅ hg
  have hcl3 : Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 3} = 1 :=
    card_classes_eq_one (fun g : G => orderOf g = 3) hx₃ fun g hg => hconj3 x₃ g hx₃ hg
  have hinvar : ∀ (Q : ℕ → Prop) (g h : G), IsConj g h → Q (orderOf g) → Q (orderOf h) :=
    fun Q g h hgh hg => (orderOf_eq_of_isConj hgh) ▸ hg
  have hN5 := card_eq_mul_card_classes (fun g : G => orderOf g = 5) (hinvar (· = 5)) 1584 hsize5
  rw [hcl5] at hN5
  have hnone : ∀ k : ℕ, k = 9 ∨ k = 15 ∨ k = 45 → Nat.card {g : G // orderOf g = k} = 0 := by
    intro k hk
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun g => ?_⟩
    have h := horders g.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    have := g.2
    omega
  have hsplit : Nat.card {g : G // orderOf g = 3 ∨ orderOf g = 5 ∨ orderOf g = 9 ∨
      orderOf g = 15 ∨ orderOf g = 45} =
      Nat.card {g : G // orderOf g = 3} + Nat.card {g : G // orderOf g = 5} +
        Nat.card {g : G // orderOf g = 9} + Nat.card {g : G // orderOf g = 15} +
          Nat.card {g : G // orderOf g = 45} := by
    have h := card_orderOf_mem_eq_sum (G := G) ({3, 5, 9, 15, 45} : Finset ℕ)
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton] at h
    rw [← add_assoc, ← add_assoc, ← add_assoc] at h
    rw [← h]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp)
  rw [hnone 9 (Or.inl rfl), hnone 15 (Or.inr (Or.inl rfl)), hnone 45 (Or.inr (Or.inr rfl))]
    at hsplit
  have hN3 : Nat.card {g : G // orderOf g = 3} = 440 := by omega
  have hsize3 : ∀ x : G, orderOf x = 3 → Nat.card (ConjClasses.mk x).carrier = 440 := by
    intro x hx
    rw [← hN3]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    exact ⟨fun h => (orderOf_eq_of_isConj h).trans hx, fun h => (hconj3 x g hx h).symm⟩
  exact ⟨horders, hconj3, hconj5, hcent5, hsize3, hsize5, hN3, by omega, hcl3, hcl5⟩

end Profile

section Five

variable {G : Type*} [Group G] [Finite G]

theorem four_dvd_of_two_pow_mod_five {m : ℕ} (hm : m ∣ 7920) (h : 2 ^ m % 5 = 1) : 4 ∣ m := by
  have hmem : m ∈ Nat.divisors 7920 := Nat.mem_divisors.mpr ⟨hm, by norm_num⟩
  have key : ∀ m ∈ Nat.divisors 7920, 2 ^ m % 5 = 1 → 4 ∣ m := by decide +kernel
  exact key m hmem h

omit [Finite G] in
theorem conj_pow_eq_pow_two_pow {g x : G} (hg : g * x * g⁻¹ = x ^ 2) (j : ℕ) :
    g ^ j * x * (g ^ j)⁻¹ = x ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc g ^ (j + 1) * x * (g ^ (j + 1))⁻¹ = g * (g ^ j * x * (g ^ j)⁻¹) * g⁻¹ := by group
      _ = (g * x * g⁻¹) ^ (2 ^ j) := by rw [ih, conj_pow]
      _ = x ^ (2 ^ (j + 1)) := by rw [hg, ← pow_mul, pow_succ, mul_comm]

theorem five_subgroup_facts (hG : Nat.card G = 7920)
    (hcent5 : ∀ x : G, orderOf x = 5 → Nat.card (Subgroup.centralizer ({x} : Set G)) = 5)
    (hconj5 : ∀ u v : G, orderOf u = 5 → orderOf v = 5 → IsConj u v)
    (P : Subgroup G) (hP : Nat.card P = 5) :
    Subgroup.centralizer (P : Set G) = P ∧ Nat.card (Subgroup.normalizer (P : Set G)) = 20 ∧
    ∃ F : Subgroup G, IsCyclic F ∧ Nat.card F = 4 ∧ F ≤ Subgroup.normalizer (P : Set G) ∧
      P ⊓ F = ⊥ ∧ Subgroup.normalizer (P : Set G) = P ⊔ F ∧
      F ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [hP])
  set x : G := (x' : G) with hxdef
  have hx : orderOf x = 5 := by rw [hxdef, Subgroup.orderOf_coe, hx']
  have hPx : P = Subgroup.zpowers x := (Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr x'.2) (by rw [hP, Nat.card_zpowers, hx])).symm
  have hcyc : IsCyclic P := isCyclic_of_prime_card hP
  have hCP : Subgroup.centralizer (P : Set G) = Subgroup.centralizer ({x} : Set G) := by
    rw [hPx, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hPC : P ≤ Subgroup.centralizer (P : Set G) := Subgroup.le_centralizer P
  have hCeq : Subgroup.centralizer (P : Set G) = P :=
    (Subgroup.eq_of_le_of_card_ge hPC (by rw [hP, hCP, hcent5 x hx])).symm
  have hCN := Subgroup.centralizer_le_normalizer (P : Set G)
  have hrel : (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) ∣
      4 := by
    have key := Subgroup.card_dvd_of_injective _
      (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
    rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex,
      IsCyclic.card_mulAut, hP, Nat.totient_prime hp5.out] at key
    exact key
  have hCN' : (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) *
      Nat.card (Subgroup.centralizer (P : Set G)) =
        Nat.card (Subgroup.normalizer (P : Set G)) := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (P : Set G))
      (K := Subgroup.normalizer (P : Set G))
    rwa [inf_of_le_left hCN] at h
  have hNle : Nat.card (Subgroup.normalizer (P : Set G)) ≤ 20 := by
    have hc5 : Nat.card (Subgroup.centralizer (P : Set G)) = 5 := by rw [hCeq, hP]
    rw [hc5] at hCN'
    have := Nat.le_of_dvd (by norm_num) hrel
    omega
  have hx2 : orderOf (x ^ 2) = 5 := by
    rw [Nat.Coprime.orderOf_pow (by rw [hx]; norm_num), hx]
  obtain ⟨g, hg⟩ := isConj_iff.mp (hconj5 x (x ^ 2) hx hx2)
  have hx3 : g * x ^ 3 * g⁻¹ = x := by
    rw [← conj_pow, hg, ← pow_mul]
    exact (pow_eq_pow_mod 6 (pow_orderOf_eq_one x)).trans (by rw [hx]; simp)
  have hgN : g ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hPx, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨2 * k, ?_⟩
      rw [← conj_zpow, hg, ← zpow_natCast, ← zpow_mul]
      norm_num
    · rintro ⟨k, hk⟩
      refine ⟨3 * k, ?_⟩
      have hx3' : g⁻¹ * x * g = x ^ 3 := by
        calc g⁻¹ * x * g = g⁻¹ * (g * x ^ 3 * g⁻¹) * g := by rw [hx3]
          _ = x ^ 3 := by group
      have hconj : (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := by
        rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by rw [inv_inv], conj_zpow, inv_inv]
      have hh : h = (g⁻¹ * x * g) ^ k := by
        rw [hconj, hk]
        group
      rw [hh, hx3', ← zpow_natCast, ← zpow_mul]
      norm_num
  have hm : 4 ∣ orderOf g := by
    have hpow := conj_pow_eq_pow_two_pow hg (orderOf g)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hpow
    have hpow' : x ^ (2 ^ orderOf g) = x ^ 1 := by rw [pow_one]; exact hpow.symm
    have hmod := (pow_eq_pow_iff_modEq).mp hpow'
    rw [hx] at hmod
    have h2 : 2 ^ orderOf g % 5 = 1 := hmod
    exact four_dvd_of_two_pow_mod_five (hG ▸ orderOf_dvd_natCard g) h2
  set y := g ^ (orderOf g / 4) with hydef
  have hy : orderOf y = 4 := orderOf_pow_orderOf_div (orderOf_pos g).ne' hm
  have hyN : y ∈ Subgroup.normalizer (P : Set G) := Subgroup.pow_mem _ hgN _
  let F := Subgroup.zpowers y
  have hF4 : Nat.card F = 4 := by rw [Nat.card_zpowers, hy]
  have hFN : F ≤ Subgroup.normalizer (P : Set G) := Subgroup.zpowers_le.mpr hyN
  have hPF : P ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h5 : orderOf z ∣ 5 := hP ▸ Subgroup.orderOf_dvd_natCard P hz.1
    have h4 : orderOf z ∣ 4 := hF4 ▸ Subgroup.orderOf_dvd_natCard F hz.2
    have h1 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h5 h4
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  have hPN : P ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer
  have hsup : P ⊔ F ≤ Subgroup.normalizer (P : Set G) := sup_le hPN hFN
  have h20 : 20 ∣ Nat.card (P ⊔ F : Subgroup G) := by
    have h5 := Subgroup.card_dvd_of_le (le_sup_left : P ≤ P ⊔ F)
    have h4 := Subgroup.card_dvd_of_le (le_sup_right : F ≤ P ⊔ F)
    rw [hP] at h5
    rw [hF4] at h4
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h5
  have hNsup := Subgroup.card_le_of_le hsup
  have hsup20 : 20 ≤ Nat.card (P ⊔ F : Subgroup G) := Nat.le_of_dvd Nat.card_pos h20
  have hN20 : Nat.card (Subgroup.normalizer (P : Set G)) = 20 := by omega
  refine ⟨hCeq, hN20, F, inferInstance, hF4, hFN, hPF,
    (Subgroup.eq_of_le_of_card_ge hsup (by omega)).symm, by rw [hCeq, inf_comm, hPF]⟩

end Five

section OddNormal

variable {G : Type*} [Group G] [Finite G]

theorem card_conjClass_le_of_mem_normal {R : Subgroup G} (hR : R.Normal) {x : G} (hx : x ∈ R) :
    Nat.card (ConjClasses.mk x).carrier ≤ Nat.card R := by
  refine Nat.card_le_card_of_injective (fun y => (⟨y.1, ?_⟩ : R)) fun a b h => by
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa using this
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp
    (ConjClasses.mem_carrier_iff_mk_eq.mp y.2).symm)
  rw [← hc]
  exact hR.conj_mem x hx c

theorem eq_one_of_dvd_495 {m : ℕ} (hm : m ∣ 495) (h3 : ¬ 3 ∣ m) (h5 : ¬ 5 ∣ m)
    (h11 : ¬ 11 ∣ m) : m = 1 := by
  have hmem : m ∈ Nat.divisors 495 := Nat.mem_divisors.mpr ⟨hm, by norm_num⟩
  have key : ∀ m ∈ Nat.divisors 495, ¬ 3 ∣ m → ¬ 5 ∣ m → ¬ 11 ∣ m → m = 1 := by decide +kernel
  exact key m hmem h3 h5 h11

theorem odd_normal_eq_bot (hG : Nat.card G = 7920)
    (hsize3 : ∀ x : G, orderOf x = 3 → Nat.card (ConjClasses.mk x).carrier = 440)
    (hsize5 : ∀ x : G, orderOf x = 5 → Nat.card (ConjClasses.mk x).carrier = 1584)
    (hsize11 : ∀ x : G, orderOf x = 11 → Nat.card (ConjClasses.mk x).carrier = 720)
    (R : Subgroup G) (hR : R.Normal) (hodd : Odd (Nat.card R)) : R = ⊥ := by
  have hdvd : Nat.card R ∣ 16 * 495 := by
    have h := Subgroup.card_subgroup_dvd_card R
    rw [hG] at h
    exact h
  have hcop : Nat.Coprime (Nat.card R) 16 := by
    have h2 : Nat.Coprime (Nat.card R) 2 := Nat.coprime_two_right.mpr hodd
    have h := Nat.Coprime.pow_right 4 h2
    norm_num at h
    exact h
  have h495 : Nat.card R ∣ 495 := Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
  have hle : Nat.card R ≤ 495 := Nat.le_of_dvd (by norm_num) h495
  have hno : ∀ p : ℕ, p.Prime → p ∣ Nat.card R →
      ∃ x : G, x ∈ R ∧ orderOf x = p := by
    intro p hp hpd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) p hpd
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩
  have h5 : ¬ 5 ∣ Nat.card R := fun h => by
    obtain ⟨x, hxR, hx⟩ := hno 5 (by norm_num) h
    have := card_conjClass_le_of_mem_normal hR hxR
    rw [hsize5 x hx] at this
    omega
  have h11 : ¬ 11 ∣ Nat.card R := fun h => by
    obtain ⟨x, hxR, hx⟩ := hno 11 (by norm_num) h
    have := card_conjClass_le_of_mem_normal hR hxR
    rw [hsize11 x hx] at this
    omega
  have h3 : ¬ 3 ∣ Nat.card R := fun h => by
    obtain ⟨x, hxR, hx⟩ := hno 3 Nat.prime_three h
    have := card_conjClass_le_of_mem_normal hR hxR
    rw [hsize3 x hx] at this
    have h9 : Nat.card R ∣ 9 := by
      have hmem : Nat.card R ∈ Nat.divisors 495 := Nat.mem_divisors.mpr ⟨h495, by norm_num⟩
      have key : ∀ m ∈ Nat.divisors 495, ¬ 5 ∣ m → ¬ 11 ∣ m → m ∣ 9 := by decide +kernel
      exact key _ hmem h5 h11
    have := Nat.le_of_dvd (by norm_num) h9
    omega
  exact Subgroup.eq_bot_of_card_eq R (eq_one_of_dvd_495 h495 h3 h5 h11)

end OddNormal

section Rational

open IntermediateField

theorem character_rat_of_forall_pow_eq {G : Type*} [Group G] [Finite G] {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (h : ∀ k : ℕ, k.Coprime (Nat.card G) → ∀ g : G, ρ.character (g ^ k) = ρ.character g)
    (g : G) : ∃ q : ℚ, ρ.character g = q := by
  set n := Nat.card G with hndef
  have hn0 : 0 < n := Nat.card_pos
  have : NeZero n := ⟨hn0.ne'⟩
  set η : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hη : IsPrimitiveRoot η n := Complex.isPrimitiveRoot_exp n hn0.ne'
  have : IsCyclotomicExtension {n} ℚ ℚ⟮η⟯ :=
    CFSG.LyonsUnitaryFour.isCyclotomicExtension_adjoin_primitiveRoot hη
  have : NumberField ℚ⟮η⟯ := IsCyclotomicExtension.numberField {n} ℚ ℚ⟮η⟯
  have : IsGalois ℚ ℚ⟮η⟯ := IsCyclotomicExtension.isGalois {n} ℚ ℚ⟮η⟯
  have hg : g ^ n = 1 := pow_card_eq_one'
  set c : ℚ⟮η⟯ := ⟨ρ.character g, CFSG.LyonsUnitaryFour.character_mem_adjoin hη ρ hg⟩ with hcdef
  have hfix : ∀ τ : ℚ⟮η⟯ ≃ₐ[ℚ] ℚ⟮η⟯, τ c = c := by
    intro τ
    set u := ((IsCyclotomicExtension.Rat.galEquivZMod n ℚ⟮η⟯ τ : (ZMod n)ˣ) : ZMod n).val
      with hudef
    have hτ : (τ (AdjoinSimple.gen ℚ η) : ℂ) = η ^ u := by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n ℚ⟮η⟯ τ
        (CFSG.LyonsUnitaryFour.isPrimitiveRoot_adjoinSimple_gen hη).pow_eq_one]
      simp [u]
    have hu : u.Coprime n := ZMod.val_coe_unit_coprime _
    apply Subtype.ext
    rw [CFSG.LyonsUnitaryFour.galois_character_eq hη hτ ρ hg, h u hu g]
  have hbot : c ∈ (⊥ : IntermediateField ℚ ℚ⟮η⟯) := (IsGalois.mem_bot_iff_fixed c).mpr hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
  refine ⟨q, ?_⟩
  have := congrArg (fun y : ℚ⟮η⟯ => (y : ℂ)) hq
  simpa [hcdef] using this.symm

end Rational

section Characters

open CFSG.Semidihedral.Principal.GL2Columns (exists_label_of_mem_blocksIrr label_mem_blocksIrr)
open CFSG.TwoRankLowerBound.Helpers (finiteIrreducibleCharacterBasis_exists)
open CFSG.BlockSectionOrthogonality.Helpers (irreducibles_finite)

variable {G : Type} [Group G]

theorem character_trace_gap {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {p : ℕ} (hp : p.Prime) {a : ℕ} {g : G} (hg : g ^ (p ^ a) = 1)
    {q : ℚ} (hq : ρ.character g = q) :
    (∃ z : ℤ, (z : ℚ) = q) ∧ (∃ k : ℕ, (Module.finrank ℂ V : ℚ) - q = p * k) ∧
      -((Module.finrank ℂ V : ℚ) / (p - 1)) ≤ q ∧ q ≤ Module.finrank ℂ V ∧
      (ρ g ≠ 1 → q < Module.finrank ℂ V) :=
  CFSG.LyonsUnitaryFour.trace_gap_of_pow_prime_pow_eq_one hp (f := ρ g)
    (by rw [← map_pow, hg, map_one]) hq

theorem character_rat_of_unique [Fintype G] (heven : 2 ∣ Nat.card G) {t : G}
    (ht : orderOf t = 2) {χ : G → ℂ} (hχ : χ ∈ CFSG.BlocksIrr G)
    (huniq : ∀ ψ ∈ CFSG.BlocksIrr G, ψ 1 = χ 1 → ψ t = χ t → ψ = χ) (g : G) :
    ∃ q : ℚ, χ g = q := by
  have hχ' := hχ
  obtain ⟨V, _, _, _, ρ, -, hρχ⟩ := hχ'
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨a, ha⟩ := exists_label_of_mem_blocksIrr basis hχ
  rw [← hρχ]
  refine character_rat_of_forall_pow_eq ρ (fun k hk x => ?_) g
  rw [hρχ]
  obtain ⟨b, hb⟩ := CFSG.LyonsUnitaryFour.exists_label_character_pow basis hk.symm a
  have hodd : ¬ 2 ∣ k := fun h2 => by
    have h := Nat.Coprime.coprime_dvd_left h2 hk
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at h
    exact h heven
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have htk : t ^ k = t := by
    obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
    rw [hm, pow_succ, pow_mul, ht2, one_pow, one_mul]
  have hψ : (basis.representation b).character = χ := by
    refine huniq _ (label_mem_blocksIrr basis b) ?_ ?_
    · rw [hb, one_pow, ha]
    · rw [hb, htk, ha]
  calc χ (x ^ k) = (basis.representation a).character (x ^ k) := by rw [ha]
    _ = (basis.representation b).character x := (hb x).symm
    _ = χ x := by rw [hψ]

theorem ker_eq_bot_of_involution [Finite G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hodd : ∀ R : Subgroup G, R.Normal → Odd (Nat.card R) → R = ⊥)
    (h2 : ∀ u : G, orderOf u = 2 → ρ.character u ≠ ρ.character 1) : MonoidHom.ker ρ = ⊥ := by
  refine hodd _ inferInstance ?_
  rw [Nat.odd_iff]
  by_contra hev
  have h2d : 2 ∣ Nat.card (MonoidHom.ker ρ) := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := MonoidHom.ker ρ) 2 h2d
  have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe, hu]
  apply h2 _ hu'
  have h1 : ρ (u : G) = 1 := u.2
  show LinearMap.trace ℂ V (ρ (u : G)) = LinearMap.trace ℂ V (ρ 1)
  rw [h1, map_one ρ]

theorem degree_ten_integer_solution (A S W U : ℤ)
    (hnorm : 440 * A ^ 2 + 990 * S ^ 2 + 1584 * W ^ 2 + 1980 * U ^ 2 = 4400)
    (horth : 440 * A + 990 * S + 1584 * W + 1980 * U = 2420)
    (hA : ∃ k : ℕ, 10 - A = 3 * k) (hS : ∃ k : ℕ, 10 - S = 2 * k)
    (hW : ∃ k : ℕ, 10 - W = 5 * k) (hU : ∃ k : ℕ, 10 - U = 2 * k) :
    A = 1 ∧ S = 2 ∧ W = 0 ∧ U = 0 := by
  have hA2 : A ^ 2 ≤ 10 := by nlinarith [sq_nonneg S, sq_nonneg W, sq_nonneg U]
  have hS2 : S ^ 2 ≤ 4 := by nlinarith [sq_nonneg A, sq_nonneg W, sq_nonneg U]
  have hW2 : W ^ 2 ≤ 2 := by nlinarith [sq_nonneg A, sq_nonneg S, sq_nonneg U]
  have hU2 : U ^ 2 ≤ 2 := by nlinarith [sq_nonneg A, sq_nonneg S, sq_nonneg W]
  have hA3 : -3 ≤ A ∧ A ≤ 3 := ⟨by nlinarith, by nlinarith⟩
  have hS3 : -2 ≤ S ∧ S ≤ 2 := ⟨by nlinarith, by nlinarith⟩
  have hW3 : -1 ≤ W ∧ W ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have hU3 : -1 ≤ U ∧ U ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  obtain ⟨kA, hkA⟩ := hA
  obtain ⟨kS, hkS⟩ := hS
  obtain ⟨kW, hkW⟩ := hW
  obtain ⟨kU, hkU⟩ := hU
  obtain ⟨hA3, hA3'⟩ := hA3
  obtain ⟨hS3, hS3'⟩ := hS3
  obtain ⟨hW3, hW3'⟩ := hW3
  obtain ⟨hU3, hU3'⟩ := hU3
  clear hA2 hS2 hW2 hU2
  interval_cases A <;> interval_cases S <;> interval_cases W <;> interval_cases U <;> omega

theorem degree_ten_character_values [Fintype G] (hG : Nat.card G = 7920)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 8, 11} : Finset ℕ))
    (hN2 : Nat.card {g : G // orderOf g = 2} = 165)
    (hN3 : Nat.card {g : G // orderOf g = 3} = 440)
    (hN4 : Nat.card {g : G // orderOf g = 4} = 990)
    (hN5 : Nat.card {g : G // orderOf g = 5} = 1584)
    (hN6 : Nat.card {g : G // orderOf g = 6} = 1320)
    (hN8 : Nat.card {g : G // orderOf g = 8} = 1980)
    (hN11 : Nat.card {g : G // orderOf g = 11} = 1440)
    (hconj3 : ∀ u v : G, orderOf u = 3 → orderOf v = 3 → IsConj u v)
    (hconj4 : ∀ u v : G, orderOf u = 4 → orderOf v = 4 → IsConj u v)
    (hconj5 : ∀ u v : G, orderOf u = 5 → orderOf v = 5 → IsConj u v)
    {x₈ : G} (hx₈ : orderOf x₈ = 8) (h8 : ∀ g : G, orderOf g = 8 → IsConj x₈ g ∨ IsConj x₈⁻¹ g)
    {χ : G → ℂ} (hχ : χ ∈ CFSG.BlocksIrr G) (hχ1 : χ 1 = 10) (hne : χ ≠ 1)
    (hrat : ∀ g, ∃ q : ℚ, χ g = q) (hker : ∀ g, χ g = 10 → g = 1)
    (h2 : ∀ g, orderOf g = 2 → χ g = 2) (h6 : ∀ g, orderOf g = 6 → χ g = -1) :
    (∀ g, orderOf g = 3 → χ g = 1) ∧ (∀ g, orderOf g = 4 → χ g = 2) ∧
      (∀ g, orderOf g = 5 → χ g = 0) ∧ (∀ g, orderOf g = 8 → χ g = 0) ∧
      (∀ g, orderOf g = 11 → χ g = -1) := by
  have hχ' := hχ
  obtain ⟨V, _, _, _, ρ, -, hρχ⟩ := hχ'
  have hdim : (Module.finrank ℂ V : ℚ) = 10 := by
    have h := Representation.char_one ρ
    rw [hρχ, hχ1] at h
    exact_mod_cast h.symm
  have hρ1 : ∀ g : G, g ≠ 1 → ρ g ≠ 1 := fun g hg h1 => hg (hker g (by
    rw [← hχ1, ← hρχ]
    show LinearMap.trace ℂ V (ρ g) = LinearMap.trace ℂ V (ρ 1)
    rw [h1, map_one ρ]))
  have hgap : ∀ (p a : ℕ) (g : G), p.Prime → g ^ (p ^ a) = 1 → g ≠ 1 →
      ∃ z : ℤ, χ g = z ∧ ∃ k : ℕ, 1 ≤ k ∧ (10 : ℤ) - z = p * k ∧
        -((10 : ℚ) / ((p : ℚ) - 1)) ≤ z := by
    intro p a g hp hg hg1
    obtain ⟨q, hq⟩ := hrat g
    have hq' : ρ.character g = q := by rw [hρχ]; exact hq
    obtain ⟨⟨z, hz⟩, ⟨k, hk⟩, hlow, -, hlt⟩ := character_trace_gap ρ hp hg hq'
    rw [hdim] at hk hlow hlt
    have hlt' := hlt (hρ1 g hg1)
    rw [← hz] at hk hlow hlt'
    refine ⟨z, by rw [hq, ← hz]; norm_cast, k, ?_, by exact_mod_cast hk, hlow⟩
    by_contra hk0
    have hk0' : k = 0 := by omega
    rw [hk0'] at hk
    push_cast at hk
    linarith
  have hpow : ∀ (g : G) (p a : ℕ), orderOf g = p ^ a → g ^ (p ^ a) = 1 := fun g p a h => by
    rw [← h, pow_orderOf_eq_one]
  have hne1 : ∀ (g : G) (d : ℕ), orderOf g = d → d ≠ 1 → g ≠ 1 := fun g d hd hd1 h => by
    rw [h, orderOf_one] at hd
    exact hd1 hd.symm
  have hcls : ∀ g h : G, IsConj g h → χ g = χ h := fun g h hgh => by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hgh
    rw [← hρχ, Representation.char_conj]
  have hrep : ∀ d : ℕ, Nat.card {g : G // orderOf g = d} ≠ 0 → ∃ g : G, orderOf g = d :=
    fun d hd => by
      obtain ⟨⟨g, hg⟩⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hd)).1
      exact ⟨g, hg⟩
  obtain ⟨x₃, hx₃⟩ := hrep 3 (by rw [hN3]; norm_num)
  obtain ⟨x₄, hx₄⟩ := hrep 4 (by rw [hN4]; norm_num)
  obtain ⟨x₅, hx₅⟩ := hrep 5 (by rw [hN5]; norm_num)
  obtain ⟨A, hA, kA, -, hkA, -⟩ := hgap 3 1 x₃ Nat.prime_three (hpow x₃ 3 1 (by simp [hx₃]))
    (hne1 x₃ 3 hx₃ (by norm_num))
  obtain ⟨S, hS, kS, -, hkS, -⟩ := hgap 2 2 x₄ Nat.prime_two (hpow x₄ 2 2 (by simp [hx₄]))
    (hne1 x₄ 4 hx₄ (by norm_num))
  obtain ⟨W, hW, kW, -, hkW, -⟩ := hgap 5 1 x₅ (by norm_num)
    (hpow x₅ 5 1 (by simp [hx₅])) (hne1 x₅ 5 hx₅ (by norm_num))
  obtain ⟨U, hU, kU, -, hkU, -⟩ := hgap 2 3 x₈ Nat.prime_two (hpow x₈ 2 3 (by simp [hx₈]))
    (hne1 x₈ 8 hx₈ (by norm_num))
  have h11 : ∀ g : G, orderOf g = 11 → χ g = -1 := by
    intro g hg
    obtain ⟨z, hz, k, hk1, hk, hlow⟩ := hgap 11 1 g (by norm_num) (hpow g 11 1 (by simp [hg]))
      (hne1 g 11 hg (by norm_num))
    have hlow' : (-1 : ℚ) ≤ z := by
      norm_num at hlow
      exact hlow
    have hlowz : -1 ≤ z := by exact_mod_cast hlow'
    have hz1 : z = -1 := by omega
    rw [hz, hz1]
    norm_num
  have hx₈inv : χ x₈⁻¹ = χ x₈ := by
    have hv := CFSG.blocksVChar_conjugate_inverse (AddSubgroup.subset_closure hχ) x₈
    rw [← hv, hU]
    simp
  let cz : ℕ → ℤ := fun d => if d = 1 then 10 else if d = 2 then 2 else if d = 3 then A else
    if d = 4 then S else if d = 5 then W else if d = 6 then -1 else if d = 8 then U else -1
  have hc : ∀ g : G, χ g = (cz (orderOf g) : ℂ) := by
    intro g
    have h := horders g
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h | h | h <;> simp only [cz, h] <;> norm_num
    · rw [orderOf_eq_one_iff.mp h, hχ1]
    · rw [h2 g h]
    · rw [hcls g x₃ (hconj3 g x₃ h hx₃), hA]
    · rw [hcls g x₄ (hconj4 g x₄ h hx₄), hS]
    · rw [hcls g x₅ (hconj5 g x₅ h hx₅), hW]
    · rw [h6 g h]
    · rcases h8 g h with h' | h'
      · rw [← hcls x₈ g h', hU]
      · rw [← hcls _ g h', hx₈inv, hU]
    · rw [h11 g h]
  have hD : ∀ x : G, orderOf x ∈ ({1, 2, 3, 4, 5, 6, 8, 11} : Finset ℕ) := horders
  have hN1 : Nat.card {g : G // orderOf g = 1} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨⟨1, orderOf_one⟩, fun g => Subtype.ext (orderOf_eq_one_iff.mp g.2)⟩
  have hirr := (CFSG.irreducible_character_basis G).1
  have hnorm : ∑ x : G, χ x * starRingEnd ℂ (χ x) = 7920 := by
    have h := hirr χ hχ χ hχ
    rw [ite_eq_left rfl, CFSG.BlocksInnerProduct, hG] at h
    field_simp at h
    linear_combination h
  have horth : ∑ x : G, χ x = 0 := by
    have h := hirr χ hχ 1 (principal_mem_blocksIrr G)
    rw [ite_eq_right hne, CFSG.BlocksInnerProduct, hG] at h
    simp only [Pi.one_apply, map_one, mul_one] at h
    have h' : (7920 : ℂ)⁻¹ ≠ 0 := by norm_num
    exact (mul_eq_zero.mp (by exact_mod_cast h)).resolve_left h'
  rw [sum_eq_sum_orders _ _ hD (fun d => ((cz d : ℂ) * (cz d : ℂ)))
    (fun x => by rw [hc x, map_intCast])] at hnorm
  rw [sum_eq_sum_orders _ _ hD (fun d => (cz d : ℂ)) hc] at horth
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3, 4, 5, 6, 8, 11} : Finset ℕ) by decide),
    Finset.sum_insert (show (2 : ℕ) ∉ ({3, 4, 5, 6, 8, 11} : Finset ℕ) by decide),
    Finset.sum_insert (show (3 : ℕ) ∉ ({4, 5, 6, 8, 11} : Finset ℕ) by decide),
    Finset.sum_insert (show (4 : ℕ) ∉ ({5, 6, 8, 11} : Finset ℕ) by decide),
    Finset.sum_insert (show (5 : ℕ) ∉ ({6, 8, 11} : Finset ℕ) by decide),
    Finset.sum_insert (show (6 : ℕ) ∉ ({8, 11} : Finset ℕ) by decide),
    Finset.sum_insert (show (8 : ℕ) ∉ ({11} : Finset ℕ) by decide), Finset.sum_singleton,
    hN1, hN2, hN3, hN4, hN5, hN6, hN8, hN11, cz] at hnorm horth
  norm_num at hnorm horth
  have hnormZ : 440 * A ^ 2 + 990 * S ^ 2 + 1584 * W ^ 2 + 1980 * U ^ 2 = 4400 := by
    have : ((440 * A ^ 2 + 990 * S ^ 2 + 1584 * W ^ 2 + 1980 * U ^ 2 : ℤ) : ℂ) = 4400 := by
      push_cast
      linear_combination hnorm
    exact_mod_cast this
  have horthZ : 440 * A + 990 * S + 1584 * W + 1980 * U = 2420 := by
    have : ((440 * A + 990 * S + 1584 * W + 1980 * U : ℤ) : ℂ) = 2420 := by
      push_cast
      linear_combination horth
    exact_mod_cast this
  have hvals := degree_ten_integer_solution A S W U hnormZ horthZ ⟨kA, by exact_mod_cast hkA⟩
    ⟨kS, by exact_mod_cast hkS⟩ ⟨kW, by exact_mod_cast hkW⟩ ⟨kU, by exact_mod_cast hkU⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hvals
  refine ⟨fun g hg => ?_, fun g hg => ?_, fun g hg => ?_, fun g hg => ?_, h11⟩
  · rw [hc g, hg]
    simp [cz]
  · rw [hc g, hg]
    simp [cz]
  · rw [hc g, hg]
    simp [cz]
  · rw [hc g, hg]
    simp [cz]

theorem character_eq_ten_iff [Fintype G]
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 8, 11} : Finset ℕ))
    (hodd : ∀ R : Subgroup G, R.Normal → Odd (Nat.card R) → R = ⊥)
    {χ : G → ℂ} (hχ : χ ∈ CFSG.BlocksIrr G) (hχ1 : χ 1 = 10) (hrat : ∀ g, ∃ q : ℚ, χ g = q)
    (h2 : ∀ g, orderOf g = 2 → χ g = 2) (h6 : ∀ g, orderOf g = 6 → χ g = -1) :
    ∀ g, χ g = 10 → g = 1 := by
  obtain ⟨V, _, _, _, ρ, -, hρχ⟩ := hχ
  have hK := ker_eq_bot_of_involution ρ hodd fun u hu => by
    rw [hρχ, h2 u hu, hχ1]
    norm_num
  have hdim : (Module.finrank ℂ V : ℚ) = 10 := by
    have h := Representation.char_one ρ
    rw [hρχ, hχ1] at h
    exact_mod_cast h.symm
  intro g hg
  by_contra hg1
  have hρ : ρ g ≠ 1 := fun h => hg1 (by
    have hmem : g ∈ MonoidHom.ker ρ := h
    rw [hK] at hmem
    exact hmem)
  have hpp : ∀ p a : ℕ, p.Prime → orderOf g = p ^ a → False := by
    intro p a hp hord
    obtain ⟨q, hq⟩ := hrat g
    have hq' : ρ.character g = q := by rw [hρχ]; exact hq
    have hgp : g ^ (p ^ a) = 1 := by rw [← hord, pow_orderOf_eq_one]
    obtain ⟨-, -, -, -, hlt⟩ := character_trace_gap ρ hp hgp hq'
    have hlt' := hlt hρ
    rw [hdim] at hlt'
    have h10 : (q : ℂ) = 10 := by rw [← hq, hg]
    have h10' : q = 10 := by exact_mod_cast h10
    rw [h10'] at hlt'
    exact lt_irrefl _ hlt'
  have h := horders g
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h | h | h | h | h
  · exact hg1 (orderOf_eq_one_iff.mp h)
  · rw [h2 g h] at hg
    norm_num at hg
  · exact hpp 3 1 Nat.prime_three (by rw [h]; norm_num)
  · exact hpp 2 2 Nat.prime_two (by rw [h]; norm_num)
  · exact hpp 5 1 (by norm_num) (by rw [h]; norm_num)
  · rw [h6 g h] at hg
    norm_num at hg
  · exact hpp 2 3 Nat.prime_two (by rw [h]; norm_num)
  · exact hpp 11 1 (by norm_num) (by rw [h]; norm_num)

theorem degree_ten_characters (t : G) {χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ θ₁ θ₂ : G → ℂ}
    (hall : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ∈ [1, χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, θ₁, θ₂])
    (hd₂ : χ₂ 1 = 11) (hd₅ : χ₅ 1 = 55) (hd₆ : χ₆ 1 = 44) (hd₇ : χ₇ 1 = 45) (he₁ : θ₁ 1 = 16)
    (he₂ : θ₂ 1 = 16) (ht₃ : χ₃ t = -2) (ht₄ : χ₄ t = -2) :
    (∀ ψ ∈ CFSG.BlocksIrr G, ψ 1 = 10 → ψ t = 2 → ψ = χ₁) ∧
    (∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ χ₁ → ψ ≠ χ₃ → ψ ≠ χ₄ →
      ∃ d : ℕ, 10 < d ∧ ψ 1 = d) := by
  refine ⟨fun ψ hψ hψ1 hψt => ?_, fun ψ hψ h1 hχ₁ hχ₃ hχ₄ => ?_⟩
  · have hmem := hall ψ hψ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num at hψ1
    · rfl
    · rw [hd₂] at hψ1; norm_num at hψ1
    · rw [ht₃] at hψt; norm_num at hψt
    · rw [ht₄] at hψt; norm_num at hψt
    · rw [hd₅] at hψ1; norm_num at hψ1
    · rw [hd₆] at hψ1; norm_num at hψ1
    · rw [hd₇] at hψ1; norm_num at hψ1
    · rw [he₁] at hψ1; norm_num at hψ1
    · rw [he₂] at hψ1; norm_num at hψ1
  · have hmem := hall ψ hψ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h1
    · exact absurd rfl hχ₁
    · exact ⟨11, by norm_num, by rw [hd₂]; norm_num⟩
    · exact absurd rfl hχ₃
    · exact absurd rfl hχ₄
    · exact ⟨55, by norm_num, by rw [hd₅]; norm_num⟩
    · exact ⟨44, by norm_num, by rw [hd₆]; norm_num⟩
    · exact ⟨45, by norm_num, by rw [hd₇]; norm_num⟩
    · exact ⟨16, by norm_num, by rw [he₁]; norm_num⟩
    · exact ⟨16, by norm_num, by rw [he₂]; norm_num⟩

end Characters

section Core

variable {G : Type} [Group G] [Fintype G] {t : G}

theorem order7920_profile_of_core (hG : Nat.card G = 7920) (hperf : commutator G = ⊤)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) (h10 : Nat.card (ConjClasses G) = 10)
    {χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ θ₁ θ₂ : G → ℂ} (hχ₁ : χ₁ ∈ CFSG.BlocksIrr G) (hne1 : χ₁ ≠ 1)
    (hall : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ∈ [1, χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, θ₁, θ₂])
    (hd₁ : χ₁ 1 = 10) (hd₂ : χ₂ 1 = 11) (hd₅ : χ₅ 1 = 55) (hd₆ : χ₆ 1 = 44) (hd₇ : χ₇ 1 = 45)
    (he₁ : θ₁ 1 = 16) (he₂ : θ₂ 1 = 16) (ht₁ : χ₁ t = 2) (ht₃ : χ₃ t = -2) (ht₄ : χ₄ t = -2)
    {s : G} (hs : orderOf s = 6) (hs₁ : χ₁ s = -1) :
    (∀ A : Subgroup G, Nat.card A = 11 →
      Subgroup.centralizer (A : Set G) = A ∧ Nat.card (Subgroup.normalizer (A : Set G)) = 55) ∧
    (∀ P : Subgroup G, Nat.card P = 5 →
      Subgroup.centralizer (P : Set G) = P ∧
      ∃ F : Subgroup G, IsCyclic F ∧ Nat.card F = 4 ∧ F ≤ Subgroup.normalizer (P : Set G) ∧
        P ⊓ F = ⊥ ∧ Subgroup.normalizer (P : Set G) = P ⊔ F ∧
        F ⊓ Subgroup.centralizer (P : Set G) = ⊥) ∧
    (∃ g : Fin 10 → G, (∀ x : G, ∃ i, IsConj (g i) x) ∧
      (∀ i j, IsConj (g i) (g j) → i = j) ∧
      (∀ i, orderOf (g i) = ![1, 2, 3, 4, 5, 6, 8, 8, 11, 11] i) ∧
      (∀ i, Nat.card (ConjClasses.mk (g i)).carrier =
        ![1, 165, 440, 990, 1584, 1320, 990, 990, 720, 720] i)) ∧
    (∀ d, Nat.card {x : G // orderOf x = d} =
      if d = 1 then 1 else if d = 2 then 165 else if d = 3 then 440 else if d = 4 then 990
      else if d = 5 then 1584 else if d = 6 then 1320 else if d = 8 then 1980
      else if d = 11 then 1440 else 0) ∧
    (∀ R : Subgroup G, R.Normal → Odd (Nat.card R) → R = ⊥) ∧
    (∀ ψ ∈ CFSG.BlocksIrr G, ψ 1 = 10 → ψ t = 2 → ψ = χ₁) ∧
    (∀ g, ∃ q : ℚ, χ₁ g = q) ∧ (∀ g, χ₁ g = 10 → g = 1) ∧
    (∀ g, orderOf g = 2 ∨ orderOf g = 4 → χ₁ g = 2) ∧ (∀ g, orderOf g = 3 → χ₁ g = 1) ∧
    (∀ g, orderOf g = 5 ∨ orderOf g = 8 → χ₁ g = 0) ∧
    (∀ g, orderOf g = 6 ∨ orderOf g = 11 → χ₁ g = -1) ∧
    (∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ χ₁ → ψ ≠ χ₃ → ψ ≠ χ₄ →
      ∃ d : ℕ, 10 < d ∧ ψ 1 = d) := by
  obtain ⟨h11, -, hN11, hcl11, hsize11, -, -, -, -, hN2, hN4, hN6, hN8, -, -⟩ :=
    order7920_classes hG hperf hinv ht φ
  obtain ⟨horders, hconj3, hconj5, hcent5, hsize3, hsize5, hN3, hN5, -, -⟩ :=
    order7920_odd_classes hG hperf hinv ht φ h10
  have hodd : ∀ R : Subgroup G, R.Normal → Odd (Nat.card R) → R = ⊥ :=
    fun R hR hRodd => odd_normal_eq_bot hG hsize3 hsize5 hsize11 R hR hRodd
  obtain ⟨huniq, hgap⟩ := degree_ten_characters t hall hd₂ hd₅ hd₆ hd₇ he₁ he₂ ht₃ ht₄
  have hcls : ∀ g h : G, IsConj g h → χ₁ g = χ₁ h := fun g h hgh => by
    obtain ⟨V, _, _, _, ρ, -, hρχ⟩ := hχ₁
    obtain ⟨c, rfl⟩ := isConj_iff.mp hgh
    rw [← hρχ, Representation.char_conj]
  have hrat : ∀ g, ∃ q : ℚ, χ₁ g = q :=
    character_rat_of_unique (by rw [hG]; norm_num) ht hχ₁
      (fun ψ hψ h1 h2 => huniq ψ hψ (h1.trans hd₁) (h2.trans ht₁))
  have h2 : ∀ g, orderOf g = 2 → χ₁ g = 2 := fun g hg => by
    rw [← hcls t g (hinv t g ht hg), ht₁]
  have h6 : ∀ g, orderOf g = 6 → χ₁ g = -1 := fun g hg => by
    rw [← hcls s g (isConj_of_orderOf_eq_four_or_six hinv ht φ (hs.trans hg.symm)
      (Or.inr hs)), hs₁]
  have hfaith := character_eq_ten_iff horders hodd hχ₁ hd₁ hrat h2 h6
  have hconj4 : ∀ u v : G, orderOf u = 4 → orderOf v = 4 → IsConj u v := fun u v hu hv =>
    isConj_of_orderOf_eq_four_or_six hinv ht φ (hu.trans hv.symm) (Or.inl hu)
  obtain ⟨h8a, h8b, h8n, h8c⟩ := order_eight_classes hinv ht φ
  set x₈ : G := ((φ.symm a0 : Subgroup.centralizer ({t} : Set G)) : G) with hx₈
  have hx₈inv : ((φ.symm a0⁻¹ : Subgroup.centralizer ({t} : Set G)) : G) = x₈⁻¹ := by
    rw [hx₈, map_inv, Subgroup.coe_inv]
  rw [hx₈inv] at h8b h8n h8c
  obtain ⟨v3, v4, v5, v8, v11⟩ := degree_ten_character_values hG horders hN2 hN3 hN4 hN5 hN6
    hN8 hN11 hconj3 hconj4 hconj5 h8a h8c hχ₁ hd₁ hne1 hrat hfaith h2 h6
  obtain ⟨a, a', ha, ha', haa', h11c⟩ := exists_reps_of_card_classes_eq_two
    (fun g : G => orderOf g = 11) hcl11
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x₃, hx₃⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hG]; norm_num)
  obtain ⟨x₅, hx₅⟩ := exists_prime_orderOf_dvd_card' (G := G) 5 (by rw [hG]; norm_num)
  have hord : ∀ y : G23, orderOf ((φ.symm y : Subgroup.centralizer ({t} : Set G)) : G) =
      orderOf y := fun y => by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  set x₄ : G := ((φ.symm (a0 ^ 2) : Subgroup.centralizer ({t} : Set G)) : G) with hx₄
  set x₆ : G := ((φ.symm c0 : Subgroup.centralizer ({t} : Set G)) : G) with hx₆
  have hx₄o : orderOf x₄ = 4 := by rw [hx₄, hord, orderOf_a0_sq]
  have hx₆o : orderOf x₆ = 6 := by rw [hx₆, hord, orderOf_c0]
  have hsizeEv := fun (g : G) (hg : Even (orderOf g)) =>
    card_conjClass_of_even_orderOf hG hinv ht φ hg
  let g : Fin 10 → G := ![1, t, x₃, x₄, x₅, x₆, x₈, x₈⁻¹, a, a']
  have hgord : ∀ i, orderOf (g i) = ![1, 2, 3, 4, 5, 6, 8, 8, 11, 11] i := by
    intro i
    fin_cases i
    exacts [orderOf_one, ht, hx₃, hx₄o, hx₅, hx₆o, h8a, h8b, ha, ha']
  refine ⟨fun A hA => h11 A hA, fun P hP => ?_, ⟨g, fun x => ?_, fun i j hij => ?_, hgord,
    fun i => ?_⟩, fun d => ?_, hodd, huniq, hrat, hfaith, ?_, v3, ?_, ?_, hgap⟩
  · obtain ⟨hC, -, F, hF⟩ := five_subgroup_facts hG hcent5 hconj5 P hP
    exact ⟨hC, F, hF⟩
  ·
    have h := horders x
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h | h | h
    · exact ⟨0, by rw [orderOf_eq_one_iff.mp h]; exact IsConj.refl _⟩
    · exact ⟨1, hinv t x ht h⟩
    · exact ⟨2, hconj3 x₃ x hx₃ h⟩
    · exact ⟨3, hconj4 x₄ x hx₄o h⟩
    · exact ⟨4, hconj5 x₅ x hx₅ h⟩
    · exact ⟨5, isConj_of_orderOf_eq_four_or_six hinv ht φ (hx₆o.trans h.symm) (Or.inr hx₆o)⟩
    · rcases h8c x h with h' | h'
      · exact ⟨6, h'⟩
      · exact ⟨7, h'⟩
    · rcases h11c x h with h' | h'
      · exact ⟨8, h'⟩
      · exact ⟨9, h'⟩
  ·
    have hoij := orderOf_eq_of_isConj hij
    rw [hgord i, hgord j] at hoij
    fin_cases i <;> fin_cases j <;> simp at hoij ⊢
    · exact h8n hij
    · exact h8n hij.symm
    · exact haa' hij
    · exact haa' hij.symm
  ·
    fin_cases i
    · show Nat.card (ConjClasses.mk (1 : G)).carrier = 1
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨1, ConjClasses.mem_carrier_mk⟩, fun y => Subtype.ext ?_⟩
      have hy := y.2
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left] at hy
      exact hy
    · exact (hsizeEv t (by rw [ht]; decide)).1 ht
    · exact hsize3 x₃ hx₃
    · exact (hsizeEv x₄ (by rw [hx₄o]; decide)).2.1 hx₄o
    · exact hsize5 x₅ hx₅
    · exact (hsizeEv x₆ (by rw [hx₆o]; decide)).2.2.1 hx₆o
    · exact (hsizeEv x₈ (by rw [h8a]; decide)).2.2.2 h8a
    · exact (hsizeEv x₈⁻¹ (by rw [h8b]; decide)).2.2.2 h8b
    · exact hsize11 a ha
    · exact hsize11 a' ha'
  ·
    have hzero : ∀ d, d ∉ ({1, 2, 3, 4, 5, 6, 8, 11} : Finset ℕ) →
        Nat.card {x : G // orderOf x = d} = 0 := by
      intro d hd
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun x => hd (x.2 ▸ horders x.1)⟩
    have hN1 : Nat.card {g : G // orderOf g = 1} = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      exact ⟨⟨1, orderOf_one⟩, fun g => Subtype.ext (orderOf_eq_one_iff.mp g.2)⟩
    by_cases hd1 : d = 1
    · subst hd1; rw [hN1]; simp
    by_cases hd2 : d = 2
    · subst hd2; rw [hN2]; simp
    by_cases hd3 : d = 3
    · subst hd3; rw [hN3]; simp
    by_cases hd4 : d = 4
    · subst hd4; rw [hN4]; simp
    by_cases hd5 : d = 5
    · subst hd5; rw [hN5]; simp
    by_cases hd6 : d = 6
    · subst hd6; rw [hN6]; simp
    by_cases hd8 : d = 8
    · subst hd8; rw [hN8]; simp
    by_cases hd11 : d = 11
    · subst hd11; rw [hN11]; simp
    rw [hzero d (by simp [hd1, hd2, hd3, hd4, hd5, hd6, hd8, hd11])]
    simp [hd1, hd2, hd3, hd4, hd5, hd6, hd8, hd11]
  · rintro g (hg | hg)
    · exact h2 g hg
    · exact v4 g hg
  · rintro g (hg | hg)
    · exact v5 g hg
    · exact v8 g hg
  · rintro g (hg | hg)
    · exact h6 g hg
    · exact v11 g hg

end Core

end Order7920

end CFSG.Semidihedral.GL2Recognition
