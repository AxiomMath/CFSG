module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem factorization_eq_one_of_dvd_of_not_sq_dvd {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hdvd : p ∣ n) (hndvd : ¬ p ^ 2 ∣ n) : n.factorization p = 1 := by
  have h1 := hp.factorization_pos_of_dvd hn hdvd
  have h2 : n.factorization p < 2 := by
    by_contra h
    exact hndvd ((hp.pow_dvd_iff_le_factorization hn).2 (not_lt.1 h))
  omega

theorem card_filter_orderOf_eq_prime [Fintype G] [DecidableEq G] {p : ℕ} [hp : Fact p.Prime]
    (hP : (Nat.card G).factorization p = 1) [Fintype (Sylow p G)] :
    (Finset.univ.filter fun g : G => orderOf g = p).card = Fintype.card (Sylow p G) * (p - 1) := by
  classical
  have hcardP : ∀ P : Sylow p G, Nat.card (P : Subgroup G) = p := fun P => by
    rw [P.card_eq_multiplicity, hP, pow_one]
  have hord : ∀ (P : Sylow p G) (g : G), g ∈ P → g ≠ 1 → orderOf g = p := by
    intro P g hg hg1
    have hdvd : orderOf g ∣ p := by
      rw [← hcardP P, ← Subgroup.orderOf_mk g hg]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hp.out).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg1
    · exact h
  have huniq : ∀ (P P' : Sylow p G) (g : G), g ∈ P → g ∈ P' → g ≠ 1 → P = P' := by
    intro P P' g hg hg' hg1
    have hzp : ∀ Q : Sylow p G, g ∈ Q → Subgroup.zpowers g = Q := by
      intro Q hgQ
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hgQ) ?_
      rw [hcardP Q, Nat.card_zpowers, hord P g hg hg1]
    exact Sylow.ext ((hzp P hg).symm.trans (hzp P' hg'))
  have hex : ∀ g : G, orderOf g = p → ∃ P : Sylow p G, g ∈ P := by
    intro g hg
    have hpg : IsPGroup p (Subgroup.zpowers g) := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [Nat.card_zpowers, hg, pow_one]⟩
    obtain ⟨P, hP⟩ := hpg.exists_le_sylow
    exact ⟨P, hP (Subgroup.mem_zpowers g)⟩
  let T : Sylow p G → Finset G := fun P => Finset.univ.filter fun g => g ∈ P ∧ g ≠ 1
  have hS : (Finset.univ.filter fun g : G => orderOf g = p) = Finset.univ.biUnion T := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, T]
    constructor
    · intro hg
      obtain ⟨P, hgP⟩ := hex g hg
      refine ⟨P, hgP, fun h1 => ?_⟩
      rw [h1, orderOf_one] at hg
      exact hp.out.one_lt.ne hg
    · rintro ⟨P, hgP, hg1⟩
      exact hord P g hgP hg1
  have hdisj : (Set.univ : Set (Sylow p G)).PairwiseDisjoint T := by
    intro P _ P' _ hPP'
    rw [Function.onFun, Finset.disjoint_left]
    intro g hgP hgP'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, T] at hgP hgP'
    exact hPP' (huniq P P' g hgP.1 hgP'.1 hgP.2)
  have hT : ∀ P : Sylow p G, (T P).card = p - 1 := by
    intro P
    have hfilter : (Finset.univ.filter fun g : G => g ∈ P) = (P : Set G).toFinset := by
      ext g
      simp
    have hcard : (Finset.univ.filter fun g : G => g ∈ P).card = p := by
      rw [hfilter, Set.toFinset_card, ← Nat.card_eq_fintype_card]
      exact hcardP P
    have hT' : T P = (Finset.univ.filter fun g : G => g ∈ P).erase 1 := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, T]
      tauto
    rw [hT', Finset.card_erase_of_mem (by simp [one_mem]), hcard]
  rw [hS, Finset.card_biUnion (fun P _ P' _ h => hdisj (Set.mem_univ P) (Set.mem_univ P') h),
    Finset.sum_congr rfl fun P _ => hT P, Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem ne_bot_ne_top_of_card [Finite G] {N : Subgroup G} (h1 : Nat.card N ≠ 1)
    (h2 : Nat.card N ≠ Nat.card G) : N ≠ ⊥ ∧ N ≠ ⊤ := by
  refine ⟨fun h => h1 ?_, fun h => h2 ?_⟩
  · rw [h, Subgroup.card_bot]
  · rw [h, Subgroup.card_top]

theorem factorization_eq_of_pow_dvd {n p k : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hdvd : p ^ k ∣ n)
    (hndvd : ¬ p ^ (k + 1) ∣ n) : n.factorization p = k := by
  have h1 : k ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn).1 hdvd
  have h2 : n.factorization p < k + 1 := by
    by_contra h
    exact hndvd ((hp.pow_dvd_iff_le_factorization hn).2 (not_lt.1 h))
  omega

theorem exists_normal_of_card_sylow_eq_one [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (h1 : Nat.card (Sylow p G) = 1) (hf : (Nat.card G).factorization p = 1) (hpG : p ≠ Nat.card G) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  have : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.1 h1).1
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  refine ⟨P, P.normal_of_subsingleton, ne_bot_ne_top_of_card ?_ ?_⟩
  · rw [P.card_eq_multiplicity, hf, pow_one]
    exact hp.out.one_lt.ne'
  · rw [P.card_eq_multiplicity, hf, pow_one]
    exact hpG

theorem card_sylow_dvd_and_modEq [Finite G] {p : ℕ} [Fact p.Prime] {m : ℕ}
    (hm : ∀ P : Sylow p G, (P : Subgroup G).index = m) :
    Nat.card (Sylow p G) ∣ m ∧ Nat.card (Sylow p G) ≡ 1 [MOD p] := by
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  exact ⟨hm P ▸ P.card_dvd_index, card_sylow_modEq_one p G⟩

theorem index_sylow_eq [Finite G] {p : ℕ} [Fact p.Prime] {k m : ℕ}
    (hf : (Nat.card G).factorization p = k) (hG : Nat.card G = p ^ k * m) (P : Sylow p G) :
    (P : Subgroup G).index = m := by
  have h := (P : Subgroup G).index_mul_card
  rw [P.card_eq_multiplicity, hf, hG, mul_comm (p ^ k)] at h
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos k) h

theorem order_thirty_not_simple [Finite G] (hG : Nat.card G = 30) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hf5 : (Nat.card G).factorization 5 = 1 := by
    rw [hG]
    exact factorization_eq_of_pow_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf3 : (Nat.card G).factorization 3 = 1 := by
    rw [hG]
    exact factorization_eq_of_pow_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hn5 : Nat.card (Sylow 5 G) = 1 ∨ Nat.card (Sylow 5 G) = 6 := by
    obtain ⟨hdvd, hmod⟩ := card_sylow_dvd_and_modEq (p := 5) (G := G)
      (index_sylow_eq (m := 6) hf5 (by rw [hG]; norm_num))
    have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Sylow 5 G) = n at hdvd hmod hpos hle ⊢
    interval_cases n <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hdvd hmod; decide)
  have hn3 : Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 10 := by
    obtain ⟨hdvd, hmod⟩ := card_sylow_dvd_and_modEq (p := 3) (G := G)
      (index_sylow_eq (m := 10) hf3 (by rw [hG]; norm_num))
    have hpos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Sylow 3 G) = n at hdvd hmod hpos hle ⊢
    interval_cases n <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hdvd hmod; decide)
  rcases hn5 with h5 | h5
  · exact exists_normal_of_card_sylow_eq_one h5 hf5 (by rw [hG]; norm_num)
  rcases hn3 with h3 | h3
  · exact exists_normal_of_card_sylow_eq_one h3 hf3 (by rw [hG]; norm_num)
  exfalso
  have : Fintype (Sylow 5 G) := Fintype.ofFinite _
  have : Fintype (Sylow 3 G) := Fintype.ofFinite _
  have hc5 := card_filter_orderOf_eq_prime (G := G) (p := 5) hf5
  have hc3 := card_filter_orderOf_eq_prime (G := G) (p := 3) hf3
  rw [Fintype.card_eq_nat_card, h5] at hc5
  rw [Fintype.card_eq_nat_card, h3] at hc3
  have hdisj : Disjoint (Finset.univ.filter fun g : G => orderOf g = 5)
      (Finset.univ.filter fun g : G => orderOf g = 3) := by
    rw [Finset.disjoint_filter]
    intro g _ h5' h3'
    rw [h5'] at h3'
    exact absurd h3' (by norm_num)
  have hunion := Finset.card_union_of_disjoint hdisj
  have hle := Finset.card_le_univ ((Finset.univ.filter fun g : G => orderOf g = 5) ∪
    (Finset.univ.filter fun g : G => orderOf g = 3))
  rw [hunion, hc5, hc3, ← Nat.card_eq_fintype_card, hG] at hle
  norm_num at hle

theorem order_fifty_six_not_simple [Finite G] (hG : Nat.card G = 56) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf7 : (Nat.card G).factorization 7 = 1 := by
    rw [hG]
    exact factorization_eq_of_pow_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf2 : (Nat.card G).factorization 2 = 3 := by
    rw [hG]
    exact factorization_eq_of_pow_dvd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hn7 : Nat.card (Sylow 7 G) = 1 ∨ Nat.card (Sylow 7 G) = 8 := by
    obtain ⟨hdvd, hmod⟩ := card_sylow_dvd_and_modEq (p := 7) (G := G)
      (index_sylow_eq (m := 8) hf7 (by rw [hG]; norm_num))
    have hpos : 0 < Nat.card (Sylow 7 G) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Sylow 7 G) = n at hdvd hmod hpos hle ⊢
    interval_cases n <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hdvd hmod; decide)
  rcases hn7 with h7 | h7
  · exact exists_normal_of_card_sylow_eq_one h7 hf7 (by rw [hG]; norm_num)
  have : Fintype (Sylow 7 G) := Fintype.ofFinite _
  have hc7 := card_filter_orderOf_eq_prime (G := G) (p := 7) hf7
  rw [Fintype.card_eq_nat_card, h7] at hc7
  have hcard2 : ∀ P : Sylow 2 G, Nat.card (P : Subgroup G) = 8 := fun P => by
    rw [P.card_eq_multiplicity, hf2]
    norm_num
  have hcompl : ∀ P : Sylow 2 G,
      ((P : Subgroup G) : Set G).toFinset = Finset.univ.filter fun g : G => ¬ orderOf g = 7 := by
    intro P
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G))
      (fun g : G => orderOf g = 7)
    rw [hc7, Finset.card_univ, ← Nat.card_eq_fintype_card, hG] at hsplit
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      rw [Set.mem_toFinset] at hg
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ g, fun h7' => ?_⟩
      have hdvd : orderOf g ∣ 8 := by
        rw [← hcard2 P, ← Subgroup.orderOf_mk g hg]
        exact orderOf_dvd_natCard _
      rw [h7'] at hdvd
      exact absurd hdvd (by norm_num)
    · rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
      change _ ≤ Nat.card (P : Subgroup G)
      rw [hcard2 P]
      omega
  have hsub : Subsingleton (Sylow 2 G) := ⟨fun P P' => Sylow.ext (SetLike.coe_injective (by
    rw [← Set.toFinset_inj, hcompl P, hcompl P']))⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
  refine ⟨P, P.normal_of_subsingleton, ne_bot_ne_top_of_card ?_ ?_⟩
  · rw [hcard2 P]
    norm_num
  · rw [hcard2 P, hG]
    norm_num

theorem nonabelian_simple_Sylow_count_minimum [Finite G] (hs : IsSimpleGroup G)
    (hna : ∃ x y : G, x * y ≠ y * x) {p : ℕ} (hp : p.Prime) (_hpG : p ∣ Nat.card G) {a b : ℕ}
    (ha : 1 ≤ a) (hpb : ¬ p ∣ b) (hab : Nat.card G = p ^ a * b) :
    Nat.card (Sylow p G) ∣ b ∧ Nat.card (Sylow p G) ≡ 1 [MOD p] ∧ 5 ≤ Nat.card (Sylow p G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hab
    exact Nat.card_pos.ne' hab
  have hf : (Nat.card G).factorization p = a := by
    rw [hab, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hb0, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpb,
      add_zero]
  obtain ⟨hdvd, hmod⟩ := card_sylow_dvd_and_modEq (p := p) (G := G) (index_sylow_eq hf hab)
  refine ⟨hdvd, hmod, ?_⟩
  by_contra hlt
  push Not at hlt
  have hcardP : ∀ P : Sylow p G, Nat.card (P : Subgroup G) = p ^ a := fun P => by
    rw [P.card_eq_multiplicity, hf]
  let φ := MulAction.toPermHom G (Sylow p G)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ φ.normal_ker with hker | hker
  ·
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
    have : Group.IsSolvable (Equiv.Perm (Sylow p G)) := Equiv.Perm.isSolvable (by omega)
    have hsolv : Group.IsSolvable G := Group.isSolvable_of_isSolvable_injective hinj
    obtain ⟨x, y, hxy⟩ := hna
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable (G := G)).2 hsolv x y)
  ·
    obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
    have hPn : (P : Subgroup G).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro g _
      have hg : g ∈ φ.ker := hker ▸ Subgroup.mem_top g
      rw [MonoidHom.mem_ker] at hg
      have := congrArg (fun σ : Equiv.Perm (Sylow p G) => σ P) hg
      exact Sylow.smul_eq_iff_mem_normalizer.1 this
    have h1 : Nat.card (Sylow p G) = 1 := by
      have := Sylow.unique_of_normal P hPn
      exact Nat.card_unique
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hPn with hP | hP
    · have h := hcardP P
      rw [hP, Subgroup.card_bot] at h
      have : 1 < p ^ a := Nat.one_lt_pow (by omega) hp.one_lt
      omega
    · have hpg : IsPGroup p G := by
        have := P.isPGroup'
        rw [hP] at this
        exact this.of_equiv Subgroup.topEquiv
      have : Nontrivial G := hs.toNontrivial
      have hZ := hpg.center_nontrivial
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (Subgroup.center G) inferInstance
        with hZ' | hZ'
      · rw [hZ'] at hZ
        exact (not_nontrivial_iff_subsingleton.2 (inferInstance : Subsingleton (⊥ : Subgroup G)))
          hZ
      · obtain ⟨x, y, hxy⟩ := hna
        have hx : x ∈ Subgroup.center G := hZ' ▸ Subgroup.mem_top x
        exact hxy (Subgroup.mem_center_iff.1 hx y).symm

end CFSG.GroupTheory
