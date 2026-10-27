module

public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalOrder504Sylow
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ComponentClassification.LiteratureLocal.Order504

open Subgroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_isConj_mul_card_centralizer [Fintype G] [DecidableEq G] (t : G) :
    (Finset.univ.filter (fun g => IsConj t g)).card * Nat.card (centralizer ({t} : Set G)) =
      Nat.card G := by
  have h1 := MulAction.index_stabilizer (ConjAct G) t
  have h2 := (MulAction.stabilizer (ConjAct G) t).card_mul_index
  rw [h1, ← Subgroup.nat_card_centralizer_nat_card_stabilizer] at h2
  have h3 : (MulAction.orbit (ConjAct G) t).ncard =
      (Finset.univ.filter (fun g => IsConj t g)).card := by
    rw [← Nat.card_coe_set_eq, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun g => ?_
    rw [ConjAct.mem_orbit_conjAct, isConj_comm]
  rw [← h3, mul_comm, h2]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

omit [Finite G] in
theorem card_centralizer_eq_of_isConj {t g : G} (h : IsConj t g) :
    Nat.card (centralizer ({g} : Set G)) = Nat.card (centralizer ({t} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hmap : (centralizer ({t} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({g} : Set G) := by
    ext y
    rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      ← hc]
    simp only [MulAut.conj_symm_apply]
    constructor
    · intro hy
      calc y * (c * t * c⁻¹) = c * ((c⁻¹ * y * c) * t) * c⁻¹ := by group
        _ = c * (t * (c⁻¹ * y * c)) * c⁻¹ := by rw [hy]
        _ = c * t * c⁻¹ * y := by group
    · intro hy
      calc c⁻¹ * y * c * t = c⁻¹ * (y * (c * t * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * t * c⁻¹ * y) * c := by rw [hy]
        _ = t * (c⁻¹ * y * c) := by group
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj c).injective]

omit [Finite G] in
theorem orderOf_eq_of_isConj {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := h
  exact SemiconjBy.orderOf_eq _ hc

omit [Finite G] in
theorem mem_of_sq_eq_one_of_mem_normalizer {S : Sylow 2 G} {s : G} (hs : s ^ 2 = 1)
    (hsN : s ∈ normalizer ((S : Subgroup G) : Set G)) : s ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 (zpowers s) := by
    have hdvd : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one hs
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hzN : zpowers s ≤ normalizer ((S : Subgroup G) : Set G) := (zpowers_le).mpr hsN
  have hsup : IsPGroup 2 (zpowers s ⊔ (S : Subgroup G) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hz S.isPGroup' hzN
  have heq := S.is_maximal' hsup le_sup_right
  rw [← heq]
  exact mem_sup_left (mem_zpowers s)

section Order504

variable [IsSimpleGroup G] (hG : Nat.card G = 504)
include hG

omit [IsSimpleGroup G] in
theorem sylow_seven_inf_eq_bot {P Q : Sylow 7 G} (hne : P ≠ Q) : (P : Subgroup G) ⊓ Q = ⊥ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hP := card_sylow_seven_subgroup hG P
  have hdvd : Nat.card ((P : Subgroup G) ⊓ Q : Subgroup G) ∣ 7 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : (P : Subgroup G) ⊓ Q ≤ P)
    rwa [hP] at this
  rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exfalso
    apply hne
    apply Sylow.ext
    have h1 : (P : Subgroup G) ⊓ Q = P :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hP])
    have h2 : (P : Subgroup G) ⊓ Q = Q :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, card_sylow_seven_subgroup hG Q])
    exact h1.symm.trans h2

theorem conj_eq_inv_of_mem_normalizer {P : Sylow 7 G} {t : G} (ht : orderOf t = 2)
    (htN : t ∈ normalizer ((P : Subgroup G) : Set G)) {y : G} (hy : y ∈ (P : Subgroup G)) :
    t * y * t⁻¹ = y⁻¹ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_cases hy1 : y = 1
  · subst hy1
    simp
  have hP := card_sylow_seven_subgroup hG P
  have hyo : orderOf y = 7 := by
    have h := Subgroup.orderOf_dvd_natCard (P : Subgroup G) hy
    rw [hP] at h
    rcases (Nat.dvd_prime (by norm_num)).mp h with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have hPz : (P : Subgroup G) = zpowers y := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · exact (zpowers_le).mpr hy
    · rw [hP, Nat.card_zpowers, hyo]
  have hty : t * y * t⁻¹ ∈ zpowers y := by
    rw [← hPz]
    exact (mem_normalizer_iff.mp htN y).mp hy
  rw [← mem_powers_iff_mem_zpowers] at hty
  obtain ⟨n, hn⟩ := hty
  have hn' : t * y * t⁻¹ = y ^ (n % 7) := by
    rw [← hn, ← hyo, pow_mod_orderOf]
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one _
  set m := n % 7 with hm
  have hm7 : m < 7 := Nat.mod_lt n (by norm_num)
  have hmm : y ^ (m * m) = y := by
    calc y ^ (m * m) = (y ^ m) ^ m := pow_mul y m m
      _ = (t * y * t⁻¹) ^ m := by rw [hn']
      _ = t * y ^ m * t⁻¹ := conj_pow
      _ = t * (t * y * t⁻¹) * t⁻¹ := by rw [hn']
      _ = t ^ 2 * y * (t ^ 2)⁻¹ := by rw [pow_two]; group
      _ = y := by rw [ht2]; group
  have hy7 : y ^ 7 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have hdvd : 7 ∣ m * m + 6 := by
    rw [← hyo]
    apply orderOf_dvd_of_pow_eq_one
    calc y ^ (m * m + 6) = y ^ (m * m) * y ^ 6 := pow_add _ _ _
      _ = y * y ^ 6 := by rw [hmm]
      _ = y ^ (6 + 1) := (pow_succ' y 6).symm
      _ = 1 := hy7
  interval_cases m
  · simp at hdvd
  · exfalso
    have htC : t ∈ centralizer ({y} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      rw [pow_one] at hn'
      calc t * y = t * y * t⁻¹ * t := by group
        _ = y * t := by rw [hn']
    rw [centralizer_of_orderOf_eq_seven hG hyo] at htC
    have := orderOf_dvd_of_mem_zpowers htC
    rw [ht, hyo] at this
    norm_num at this
  · omega
  · omega
  · omega
  · omega
  · rw [hn']
    exact eq_inv_of_mul_eq_one_left ((pow_succ y 6).symm.trans hy7)

theorem not_seven_dvd_card_centralizer_involution {t : G} (ht : orderOf t = 2) :
    ¬ 7 ∣ Nat.card (centralizer ({t} : Set G)) := by
  intro h7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({t} : Set G)) 7 h7
  have hy' : orderOf (y : G) = 7 := by rw [Subgroup.orderOf_coe]; exact hy
  have htC : t ∈ centralizer ({(y : G)} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.mp y.2).symm
  rw [centralizer_of_orderOf_eq_seven hG hy'] at htC
  have := orderOf_dvd_of_mem_zpowers htC
  rw [ht, hy'] at this
  norm_num at this

theorem card_orderOf_seven_ge [Fintype G] [DecidableEq G] :
    216 ≤ (Finset.univ.filter (fun g : G => orderOf g = 7)).card := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let _ : Fintype (Sylow 7 G) := Fintype.ofFinite _
  let T : Sylow 7 G → Finset G := fun P => ((P : Subgroup G) : Set G).toFinset.erase 1
  have hT : ∀ P, (T P).card = 6 := by
    intro P
    rw [Finset.card_erase_of_mem (by simp), ← Nat.card_eq_card_toFinset,
      show Nat.card (((P : Subgroup G) : Set G)) = Nat.card P from rfl,
      card_sylow_seven_subgroup hG P]
  have hdisj : ∀ P ∈ (Finset.univ : Finset (Sylow 7 G)), ∀ Q ∈ (Finset.univ : Finset (Sylow 7 G)),
      P ≠ Q → Disjoint (T P) (T Q) := by
    intro P _ Q _ hPQ
    rw [Finset.disjoint_left]
    intro g hgP hgQ
    simp only [T, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hgP hgQ
    have hg : g ∈ (P : Subgroup G) ⊓ Q := ⟨hgP.2, hgQ.2⟩
    rw [sylow_seven_inf_eq_bot hG hPQ, mem_bot] at hg
    exact hgP.1 hg
  have hsub : (Finset.univ.biUnion T) ⊆ Finset.univ.filter (fun g : G => orderOf g = 7) := by
    intro g hg
    obtain ⟨P, -, hgP⟩ := Finset.mem_biUnion.mp hg
    simp only [T, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hgP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h := Subgroup.orderOf_dvd_natCard (P : Subgroup G) hgP.2
    rw [card_sylow_seven_subgroup hG P] at h
    rcases (Nat.dvd_prime (by norm_num)).mp h with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hgP.1
    · exact h
  have hcard := Finset.card_biUnion hdisj
  rw [Finset.sum_congr rfl (fun P _ => hT P), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_sylow_seven hG, smul_eq_mul] at hcard
  exact (show 216 = 36 * 6 by norm_num) ▸ hcard ▸ Finset.card_le_card hsub

theorem card_three_elements_ge [Fintype G] [DecidableEq G] :
    224 ≤ (Finset.univ.filter (fun g : G => g ≠ 1 ∧ g ^ 9 = 1)).card := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fintype (Sylow 3 G) := Fintype.ofFinite _
  let T : Sylow 3 G → Finset G := fun R => ((R : Subgroup G) : Set G).toFinset.erase 1
  have hT : ∀ R, (T R).card = 8 := by
    intro R
    rw [Finset.card_erase_of_mem (by simp), ← Nat.card_eq_card_toFinset,
      show Nat.card (((R : Subgroup G) : Set G)) = Nat.card R from rfl,
      card_sylow_three_subgroup hG R]
  have hdisj : ∀ P ∈ (Finset.univ : Finset (Sylow 3 G)), ∀ Q ∈ (Finset.univ : Finset (Sylow 3 G)),
      P ≠ Q → Disjoint (T P) (T Q) := by
    intro P _ Q _ hPQ
    rw [Finset.disjoint_left]
    intro g hgP hgQ
    simp only [T, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hgP hgQ
    have hg : g ∈ (P : Subgroup G) ⊓ Q := ⟨hgP.2, hgQ.2⟩
    rw [sylow_three_inf_eq_bot hG hPQ, mem_bot] at hg
    exact hgP.1 hg
  have hsub : (Finset.univ.biUnion T) ⊆
      Finset.univ.filter (fun g : G => g ≠ 1 ∧ g ^ 9 = 1) := by
    intro g hg
    obtain ⟨R, -, hgR⟩ := Finset.mem_biUnion.mp hg
    simp only [T, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hgR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hgR.1, ?_⟩
    have h := Subgroup.orderOf_dvd_natCard (R : Subgroup G) hgR.2
    rw [card_sylow_three_subgroup hG R] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hcard := Finset.card_biUnion hdisj
  rw [Finset.sum_congr rfl (fun R _ => hT R), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_sylow_three hG, smul_eq_mul] at hcard
  exact (show 224 = 28 * 8 by norm_num) ▸ hcard ▸ Finset.card_le_card hsub

theorem card_even_orderOf_le [Fintype G] [DecidableEq G] :
    (Finset.univ.filter (fun g : G => Even (orderOf g))).card ≤ 63 := by
  classical
  set A := Finset.univ.filter (fun g : G => orderOf g = 7)
  set B := Finset.univ.filter (fun g : G => g ≠ 1 ∧ g ^ 9 = 1)
  set E := Finset.univ.filter (fun g : G => Even (orderOf g))
  have hA : 216 ≤ A.card := card_orderOf_seven_ge hG
  have hB : 224 ≤ B.card := card_three_elements_ge hG
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro g hgA hgB
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hgA hgB
    have := orderOf_dvd_of_pow_eq_one hgB.2
    rw [hgA] at this
    norm_num at this
  have hAE : Disjoint (A ∪ B) E := by
    rw [Finset.disjoint_left]
    intro g hg hgE
    simp only [A, B, E, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hg hgE
    rcases hg with hg | hg
    · rw [hg] at hgE
      exact absurd hgE (by decide)
    · have h9 : orderOf g ∣ 9 := orderOf_dvd_of_pow_eq_one hg.2
      exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat (by decide) h9)) hgE
  have h1 : (1 : G) ∉ A ∪ B ∪ E := by
    simp only [A, B, E, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      orderOf_one]
    simp
  have hle : (insert (1 : G) (A ∪ B ∪ E)).card ≤ Nat.card G := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem h1, Finset.card_union_of_disjoint hAE,
    Finset.card_union_of_disjoint hAB, hG] at hle
  omega

theorem card_centralizer_le_twelve {x t : G} (hx : orderOf x = 7) (ht : orderOf t = 2)
    (htx : t * x * t⁻¹ = x⁻¹) : Nat.card (centralizer ({t} : Set G)) ≤ 12 := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype (Sylow 7 G) := Fintype.ofFinite _
  obtain ⟨P0, hP0⟩ := exists_sylow_seven_eq_zpowers hG hx
  set C := centralizer ({t} : Set G) with hC
  have htC : t ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have htN : t ∈ normalizer ((P0 : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, hP0, MonoidHom.map_zpowers]
    show zpowers (t * x * t⁻¹) = zpowers x
    rw [htx, zpowers_inv]
  have hstab : Nat.card (MulAction.stabilizer C P0) = 2 := by
    have hst : MulAction.stabilizer C P0 =
        (normalizer ((P0 : Subgroup G) : Set G)).subgroupOf C := by
      ext c
      rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, Subgroup.smul_def,
        Sylow.smul_eq_iff_mem_normalizer]
      exact Iff.rfl
    have hcard : Nat.card (MulAction.stabilizer C P0) =
        Nat.card (normalizer ((P0 : Subgroup G) : Set G) ⊓ C : Subgroup G) := by
      rw [hst, ← Subgroup.subgroupOf_map_subtype,
        Subgroup.card_map_of_injective C.subtype_injective]
    rw [hcard]
    set D := (normalizer ((P0 : Subgroup G) : Set G) ⊓ C : Subgroup G)
    have hD14 : Nat.card D ∣ 14 :=
      card_normalizer_sylow_seven hG P0 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hD7 : ¬ 7 ∣ Nat.card D := fun h =>
      not_seven_dvd_card_centralizer_involution hG ht
        (h.trans (Subgroup.card_dvd_of_le inf_le_right))
    have hD2 : 2 ∣ Nat.card D := ht ▸ Subgroup.orderOf_dvd_natCard D ⟨htN, htC⟩
    have : Nat.card D ≤ 14 := Nat.le_of_dvd (by norm_num) hD14
    interval_cases (Nat.card D) <;> omega
  set F := Finset.univ.filter
    (fun P : Sylow 7 G => t ∈ normalizer ((P : Subgroup G) : Set G)) with hF
  have horbit : (MulAction.orbit C P0).ncard ≤ F.card := by
    rw [← Set.ncard_coe_finset F]
    apply Set.ncard_le_ncard _ (Finset.finite_toSet F)
    rintro P ⟨c, rfl⟩
    simp only [hF, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    rw [Subgroup.smul_def, ← mul_smul,
      show t * (c : G) = (c : G) * t from (mem_centralizer_singleton_iff.mp c.2).symm, mul_smul,
      Sylow.smul_eq_iff_mem_normalizer.mpr htN]
  have hCorb : Nat.card C = (MulAction.orbit C P0).ncard * 2 := by
    rw [← hstab, ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]
  let U : Sylow 7 G → Finset G := fun P => (((P : Subgroup G) : Set G).toFinset.erase 1).image
    (fun y => t * y)
  have hUcard : ∀ P, (U P).card = 6 := by
    intro P
    rw [Finset.card_image_of_injective _ (mul_right_injective t),
      Finset.card_erase_of_mem (by simp),
      ← Nat.card_eq_card_toFinset, show Nat.card (((P : Subgroup G) : Set G)) = Nat.card P from rfl,
      card_sylow_seven_subgroup hG P]
  have hUdisj : ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → Disjoint (U P) (U Q) := by
    intro P _ Q _ hPQ
    rw [Finset.disjoint_left]
    intro g hgP hgQ
    simp only [U, Finset.mem_image, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hgP hgQ
    obtain ⟨y, ⟨hy1, hyP⟩, rfl⟩ := hgP
    obtain ⟨y', ⟨-, hyQ⟩, hyy⟩ := hgQ
    have hyy' : y' = y := mul_left_cancel hyy
    subst hyy'
    have hy : y' ∈ (P : Subgroup G) ⊓ Q := ⟨hyP, hyQ⟩
    rw [sylow_seven_inf_eq_bot hG hPQ, mem_bot] at hy
    exact hy1 hy
  set K := Finset.univ.filter (fun g => IsConj t g) with hK
  have hUsub : F.biUnion U ⊆ K.erase t := by
    intro g hg
    obtain ⟨P, hPF, hgP⟩ := Finset.mem_biUnion.mp hg
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hPF
    simp only [U, Finset.mem_image, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hgP
    obtain ⟨y, ⟨hy1, hyP⟩, rfl⟩ := hgP
    rw [Finset.mem_erase]
    refine ⟨fun h => hy1 (by simpa using h), ?_⟩
    simp only [hK, Finset.mem_filter, Finset.mem_univ, true_and]
    have hinv := conj_eq_inv_of_mem_normalizer hG ht hPF hyP
    have hy7 : y ^ 7 = 1 := by
      have h := Subgroup.orderOf_dvd_natCard (P : Subgroup G) hyP
      rw [card_sylow_seven_subgroup hG P] at h
      exact orderOf_dvd_iff_pow_eq_one.mp h
    refine isConj_iff.mpr ⟨y ^ 3, ?_⟩
    have h4 : (y ^ 3)⁻¹ = y ^ 4 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add]
      exact hy7
    have h44 : t * y ^ 4 * t⁻¹ = y⁻¹ ^ 4 := by rw [← conj_pow, hinv]
    calc y ^ 3 * t * (y ^ 3)⁻¹ = y ^ 3 * (t * y ^ 4 * t⁻¹) * t := by rw [h4]; group
      _ = y ^ 3 * y⁻¹ ^ 4 * t := by rw [h44]
      _ = y⁻¹ * t := by group
      _ = t * y * t⁻¹ * t := by rw [hinv]
      _ = t * y := by group
  have hUtot : (F.biUnion U).card = F.card * 6 := by
    rw [Finset.card_biUnion hUdisj, Finset.sum_congr rfl (fun P _ => hUcard P), Finset.sum_const,
      smul_eq_mul]
  have hKcard : K.card * Nat.card C = Nat.card G := card_isConj_mul_card_centralizer t
  have hKt : t ∈ K := by
    rw [hK, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, IsConj.refl t⟩
  have hKle := Finset.card_le_card hUsub
  rw [hUtot, Finset.card_erase_of_mem hKt] at hKle
  rw [hG] at hKcard
  have hpos : 0 < K.card := Finset.card_pos.mpr ⟨t, hKt⟩
  set c := Nat.card C
  set o := (MulAction.orbit C P0).ncard
  have hK3 : 3 * c + 1 ≤ K.card := by omega
  have hprod : (3 * c + 1) * c ≤ 504 := by
    rw [← hKcard]
    exact Nat.mul_le_mul_right c hK3
  nlinarith

theorem card_centralizer_eq_eight {x t : G} (hx : orderOf x = 7) (ht : orderOf t = 2)
    (htx : t * x * t⁻¹ = x⁻¹) :
    Nat.card (centralizer ({t} : Set G)) = 8 ∧ ∀ g : G, Even (orderOf g) → IsConj t g := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fintype G := Fintype.ofFinite G
  have hc12 := card_centralizer_le_twelve hG hx ht htx
  have hc2 : 2 ∣ Nat.card (centralizer ({t} : Set G)) :=
    ht ▸ Subgroup.orderOf_dvd_natCard _ (mem_centralizer_singleton_iff.mpr rfl)
  have hc504 : Nat.card (centralizer ({t} : Set G)) ∣ 504 :=
    hG ▸ Subgroup.card_subgroup_dvd_card _
  have hc7 := not_seven_dvd_card_centralizer_involution hG ht
  set K := Finset.univ.filter (fun g => IsConj t g) with hK
  set E := Finset.univ.filter (fun g : G => Even (orderOf g)) with hE
  have hk : K.card * Nat.card (centralizer ({t} : Set G)) = Nat.card G :=
    card_isConj_mul_card_centralizer t
  rw [hG] at hk
  have hKE : K ⊆ E := by
    intro g hg
    simp only [hK, hE, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    have hg' : IsConj t g := hg
    rw [← orderOf_eq_of_isConj hg', ht]
    decide
  have hEcard : E.card ≤ 63 := card_even_orderOf_le hG
  have hK63 : K.card ≤ 63 := (Finset.card_le_card hKE).trans hEcard
  have hcases : Nat.card (centralizer ({t} : Set G)) = 8 ∨
      Nat.card (centralizer ({t} : Set G)) = 12 := by
    have hc8 : 8 ≤ Nat.card (centralizer ({t} : Set G)) := by nlinarith
    interval_cases (Nat.card (centralizer ({t} : Set G))) <;> omega
  rcases hcases with h8 | h12
  · refine ⟨h8, ?_⟩
    rw [h8] at hk
    have heq : K = E := Finset.eq_of_subset_of_card_le hKE (by omega)
    intro g hg
    have hgE : g ∈ E := by simp [hE, hg]
    rw [← heq] at hgE
    simpa [hK] using hgE
  · exfalso
    rw [h12] at hk
    have hK42 : K.card = 42 := by omega
    have hw : ∀ g ∈ K, ∃ w : G, w * g = g * w ∧ orderOf w = 3 := by
      intro g hg
      simp only [hK, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      have hcg : Nat.card (centralizer ({g} : Set G)) = 12 :=
        (card_centralizer_eq_of_isConj hg).trans h12
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({g} : Set G)) 3
        (by rw [hcg]; norm_num)
      exact ⟨w, mem_centralizer_singleton_iff.mp w.2, by rw [Subgroup.orderOf_coe]; exact hw⟩
    choose! w hwc hwo using hw
    have hgo : ∀ g ∈ K, orderOf g = 2 := fun g hg => by
      simp only [hK, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      have hg' : IsConj t g := hg
      rw [← orderOf_eq_of_isConj hg', ht]
    have hcube : ∀ g ∈ K, (g * w g) ^ 3 = g := by
      intro g hg
      have hcomm : Commute g (w g) := (hwc g hg).symm
      have hw3 : w g ^ 3 = 1 := by rw [← hwo g hg]; exact pow_orderOf_eq_one _
      have hg2 : g ^ 2 = 1 := by rw [← hgo g hg]; exact pow_orderOf_eq_one g
      rw [hcomm.mul_pow, hw3, mul_one, pow_succ, hg2, one_mul]
    have hord : ∀ g ∈ K, orderOf (g * w g) = 6 := by
      intro g hg
      have hcomm : Commute g (w g) := (hwc g hg).symm
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hgo g hg, hwo g hg]; norm_num),
        hgo g hg, hwo g hg]
    set I := K.image (fun g => g * w g) with hI
    have hIcard : I.card = 42 := by
      rw [hI, Finset.card_image_of_injOn, hK42]
      intro g hg g' hg' h
      have := congrArg (· ^ 3) h
      simp only at this
      rw [hcube g hg, hcube g' hg'] at this
      exact this
    have hIE : I ⊆ E := by
      intro y hy
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hy
      simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hord g hg]
      decide
    have hdisj : Disjoint K I := by
      rw [Finset.disjoint_left]
      intro y hyK hyI
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hyI
      have h2 := hgo _ hyK
      rw [hord g hg] at h2
      norm_num at h2
    have := Finset.card_le_card (Finset.union_subset hKE hIE)
    rw [Finset.card_union_of_disjoint hdisj, hK42, hIcard] at this
    omega

theorem exists_involution_class :
    ∃ t : G, orderOf t = 2 ∧ Nat.card (centralizer ({t} : Set G)) = 8 ∧
      ∀ g : G, Even (orderOf g) → IsConj t g := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 7 (by rw [hG]; norm_num)
  obtain ⟨t, ht, htx⟩ := exists_inverting_involution hG hx
  exact ⟨t, ht, card_centralizer_eq_eight hG hx ht htx⟩

theorem sq_eq_one_of_mem_sylow_two (S : Sylow 2 G) {s : G} (hs : s ∈ (S : Subgroup G)) :
    s ^ 2 = 1 := by
  obtain ⟨t, ht, -, hconj⟩ := exists_involution_class hG
  by_cases hs1 : s = 1
  · rw [hs1, one_pow]
  have hdvd : orderOf s ∣ 2 ^ 3 := by
    have h := Subgroup.orderOf_dvd_natCard (S : Subgroup G) hs
    rwa [card_sylow_two_subgroup hG S] at h
  have heven : Even (orderOf s) := by
    obtain ⟨k, -, hks⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hks)) hs1
    · rw [hks]
      exact Nat.even_pow.mpr ⟨even_two, hk0.ne'⟩
  have hs2 : orderOf s = 2 := (orderOf_eq_of_isConj (hconj s heven)).symm.trans ht
  rw [← hs2]
  exact pow_orderOf_eq_one s

theorem sylow_two_comm (S : Sylow 2 G) {a b : G} (ha : a ∈ (S : Subgroup G))
    (hb : b ∈ (S : Subgroup G)) : a * b = b * a := by
  have h1 := sq_eq_one_of_mem_sylow_two hG S ha
  have h2 := sq_eq_one_of_mem_sylow_two hG S hb
  have h3 := sq_eq_one_of_mem_sylow_two hG S (mul_mem ha hb)
  have ha' : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← pow_two, h1]
  have hb' : b⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← pow_two, h2]
  have hab' : (a * b)⁻¹ = a * b := by rw [inv_eq_iff_mul_eq_one, ← pow_two, h3]
  calc a * b = (a * b)⁻¹ := hab'.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha', hb']

theorem sylow_two_inf_eq_bot {S S' : Sylow 2 G} (hne : S ≠ S') :
    (S : Subgroup G) ⊓ S' = ⊥ := by
  obtain ⟨t, ht, hct, hconj⟩ := exists_involution_class hG
  rw [eq_bot_iff]
  rintro s ⟨hsS, hsS'⟩
  rw [mem_bot]
  by_contra hs1
  have hs2 : s ^ 2 = 1 := sq_eq_one_of_mem_sylow_two hG S hsS
  have hso : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  have hcs : Nat.card (centralizer ({s} : Set G)) = 8 :=
    (card_centralizer_eq_of_isConj (hconj s (by rw [hso]; decide))).trans hct
  have hle : ∀ Q : Sylow 2 G, s ∈ (Q : Subgroup G) →
      (Q : Subgroup G) = centralizer ({s} : Set G) := by
    intro Q hsQ
    apply Subgroup.eq_of_le_of_card_ge
    · intro q hq
      rw [mem_centralizer_singleton_iff]
      exact sylow_two_comm hG Q hq hsQ
    · rw [hcs, card_sylow_two_subgroup hG Q]
  exact hne (Sylow.ext ((hle S hsS).trans (hle S' hsS').symm))

theorem normalizer_sylow_two_stronglyEmbedded (S : Sylow 2 G) :
    normalizer ((S : Subgroup G) : Set G) ≠ ⊤ ∧
      Even (Nat.card (normalizer ((S : Subgroup G) : Set G))) ∧
      ∀ g ∉ normalizer ((S : Subgroup G) : Set G),
        Odd (Nat.card (normalizer ((S : Subgroup G) : Set G) ⊓
          (normalizer ((S : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom :
            Subgroup G)) := by
  set M := normalizer ((S : Subgroup G) : Set G) with hM
  have hS8 := card_sylow_two_subgroup hG S
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact not_normal_of_card (H := (S : Subgroup G)) (by rw [hS8]; norm_num)
      (by rw [hS8, hG]; norm_num) (normalizer_eq_top_iff.mp h)
  · have h8 : 8 ∣ Nat.card M := hS8 ▸ Subgroup.card_dvd_of_le le_normalizer
    exact even_iff_two_dvd.mpr ((show 2 ∣ 8 by norm_num).trans h8)
  · intro g hg
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card'
      (G := (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G)) 2 (even_iff_two_dvd.mp hodd)
    have hso : orderOf (s : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hs
    have hs2 : (s : G) ^ 2 = 1 := hso ▸ pow_orderOf_eq_one (s : G)
    obtain ⟨hsM, hsMg⟩ := s.2
    have hsS : (s : G) ∈ (S : Subgroup G) := mem_of_sq_eq_one_of_mem_normalizer hs2 hsM
    have hsMg' : (s : G) ∈ M.map (MulAut.conj g).toMonoidHom := hsMg
    rw [Subgroup.mem_map_equiv] at hsMg'
    have hconj2 : ((MulAut.conj g).symm (s : G)) ^ 2 = 1 := by
      rw [← map_pow, hs2, map_one]
    have hsS' := mem_of_sq_eq_one_of_mem_normalizer hconj2 hsMg'
    have hsgS : (s : G) ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.smul_def] using hsS'
    by_cases hgS : g • S = S
    · exact hg (Sylow.smul_eq_iff_mem_normalizer.mp hgS)
    · have hbot := sylow_two_inf_eq_bot hG (Ne.symm hgS)
      have hmem : (s : G) ∈ (S : Subgroup G) ⊓ ((g • S : Sylow 2 G) : Subgroup G) :=
        ⟨hsS, hsgS⟩
      rw [hbot, mem_bot] at hmem
      rw [hmem, orderOf_one] at hso
      norm_num at hso

end Order504

end CFSG.ComponentClassification.LiteratureLocal.Order504
