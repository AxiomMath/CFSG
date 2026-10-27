module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Semidihedral.Principal

theorem mul_pow_three_of_conj {Q : Type*} [Group Q] {a c : Q} {r : ℕ}
    (h : c * a * c⁻¹ = a ^ r) (i : ℕ) :
    (a ^ i * c) ^ 3 = a ^ (i * (1 + r + r ^ 2)) * c ^ 3 := by
  have hc : ∀ m : ℕ, c * a ^ m = a ^ (r * m) * c := by
    intro m
    rw [← mul_inv_eq_iff_eq_mul, ← conj_pow, h, ← pow_mul]
  calc (a ^ i * c) ^ 3 = a ^ i * (c * a ^ i) * (c * a ^ i) * c := by
        rw [pow_three']; simp only [mul_assoc]
    _ = a ^ i * (a ^ (r * i) * c) * (a ^ (r * i) * c) * c := by rw [hc i]
    _ = a ^ i * a ^ (r * i) * (c * a ^ (r * i)) * c * c := by group
    _ = a ^ i * a ^ (r * i) * (a ^ (r * (r * i)) * c) * c * c := by rw [hc (r * i)]
    _ = a ^ (i + r * i + r * (r * i)) * c ^ 3 := by
        rw [pow_three', pow_add, pow_add]; simp only [mul_assoc]
    _ = a ^ (i * (1 + r + r ^ 2)) * c ^ 3 := by ring_nf

theorem conj_pow_iterate {Q : Type*} [Group Q] {a c : Q} {r : ℕ}
    (h : c * a * c⁻¹ = a ^ r) (j : ℕ) : c ^ j * a * (c ^ j)⁻¹ = a ^ (r ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc c ^ (j + 1) * a * (c ^ (j + 1))⁻¹ = c * (c ^ j * a * (c ^ j)⁻¹) * c⁻¹ := by
          rw [pow_succ']; group
      _ = (c * a * c⁻¹) ^ (r ^ j) := by rw [ih, conj_pow]
      _ = a ^ (r ^ (j + 1)) := by rw [h, ← pow_mul, pow_succ']

theorem nine_le_card_cube_eq {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 27)
    (hna : ¬ IsMulCommutative Q) {a : Q} (ha : orderOf a = 9) :
    9 ≤ Nat.card {g : Q // g ^ 3 = a ^ 3} := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := Subgroup.zpowers a with hA
  have hAcard : Nat.card A = 9 := by rw [hA, Nat.card_zpowers, ha]
  have hindex : A.index = 3 := by
    have := A.card_mul_index
    rw [hAcard, hQ] at this
    omega
  have hnormal : A.Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hindex, hQ]; norm_num)
  obtain ⟨b, hb⟩ : ∃ b : Q, b ∉ A := by
    by_contra h
    push Not at h
    have : A = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [this, Subgroup.index_top] at hindex
    omega
  have hmemA : ∀ y ∈ A, ∃ m < 9, a ^ m = y := by
    intro y hy
    obtain ⟨m, hm, hm'⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp hy)
    rw [ha] at hm
    exact ⟨m, Finset.mem_range.mp hm, hm'⟩
  obtain ⟨r, hr9, hr⟩ := hmemA _ (hnormal.conj_mem a (Subgroup.mem_zpowers a) b)
  have hb3 : b ^ 3 ∈ A := by
    have hcardQ : Nat.card (Q ⧸ A) = 3 := hindex
    have h3 : ((b : Q ⧸ A)) ^ 3 = 1 := by rw [← hcardQ]; exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h3
    exact h3
  obtain ⟨s, hs9, hs⟩ := hmemA _ hb3
  have hr' : b * a * b⁻¹ = a ^ r := hr.symm
  have hr3 : a ^ (r ^ 3) = a ^ 1 := by
    rw [← conj_pow_iterate hr' 3, ← hs, pow_one]
    group
  have hrs : a ^ (r * s) = a ^ s := by
    rw [pow_mul, ← hr', conj_pow, hs]
    group
  rw [pow_eq_pow_iff_modEq, ha] at hr3 hrs
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply hna
    have hab : Commute a b := by
      rw [pow_one, mul_inv_eq_iff_eq_mul] at hr'
      exact hr'.symm
    have hcomm : ({a, b} : Set Q).Pairwise Commute := by
      intro x hx y hy _
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      exacts [Commute.refl _, hab, hab.symm, Commute.refl _]
    have hcl := Subgroup.isMulCommutative_closure hcomm
    have hAle : A ≤ Subgroup.closure {a, b} :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have hbmem : b ∈ Subgroup.closure ({a, b} : Set Q) := Subgroup.subset_closure (by simp)
    have htop : Subgroup.closure ({a, b} : Set Q) = ⊤ := by
      have hdvd1 := Subgroup.card_dvd_of_le hAle
      have hdvd2 : Nat.card (Subgroup.closure ({a, b} : Set Q)) ∣ 27 := by
        rw [← hQ]; exact Subgroup.card_subgroup_dvd_card _
      rw [hAcard] at hdvd1
      have hne : Nat.card (Subgroup.closure ({a, b} : Set Q)) ≠ 9 := by
        intro h9
        exact hb ((Subgroup.eq_of_le_of_card_ge hAle (by rw [h9, hAcard])) ▸ hbmem)
      have h27 : Nat.card (Subgroup.closure ({a, b} : Set Q)) = 27 := by
        have hle := Nat.le_of_dvd (by norm_num) hdvd2
        interval_cases h : Nat.card (Subgroup.closure ({a, b} : Set Q)) <;> omega
      exact (Subgroup.card_eq_iff_eq_top _).mp (by rw [h27, hQ])
    refine ⟨⟨fun x y => ?_⟩⟩
    have hx : x ∈ Subgroup.closure ({a, b} : Set Q) := htop ▸ Subgroup.mem_top x
    have hy : y ∈ Subgroup.closure ({a, b} : Set Q) := htop ▸ Subgroup.mem_top y
    exact congrArg Subtype.val (hcl.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hr47 : r = 4 ∨ r = 7 := by
    unfold Nat.ModEq at hr3
    interval_cases r <;> simp_all
  have hs036 : s = 0 ∨ s = 3 ∨ s = 6 := by
    unfold Nat.ModEq at hrs
    rcases hr47 with rfl | rfl <;> omega
  obtain ⟨t, ht3, hts⟩ : ∃ t < 3, (3 * t + s) % 9 = 0 := by
    rcases hs036 with rfl | rfl | rfl
    exacts [⟨0, by norm_num, by norm_num⟩, ⟨2, by norm_num, by norm_num⟩,
      ⟨1, by norm_num, by norm_num⟩]
  set c := a ^ t * b with hc
  have hcA : c ∉ A := by
    intro h
    apply hb
    have := A.mul_mem (A.inv_mem (A.pow_mem (Subgroup.mem_zpowers a) t)) h
    rwa [hc, inv_mul_cancel_left] at this
  have hcconj : c * a * c⁻¹ = a ^ r := by
    rw [hc, mul_inv_rev]
    calc a ^ t * b * a * (b⁻¹ * (a ^ t)⁻¹) = a ^ t * (b * a * b⁻¹) * (a ^ t)⁻¹ := by group
      _ = a ^ t * a ^ r * (a ^ t)⁻¹ := by rw [hr']
      _ = a ^ r := by rw [(Commute.pow_pow_self a t r).eq, mul_inv_cancel_right]
  have hc3 : c ^ 3 = 1 := by
    rw [hc, mul_pow_three_of_conj hr' t, ← hs, ← pow_add, pow_eq_one_iff_modEq, ha]
    unfold Nat.ModEq
    rcases hr47 with rfl | rfl <;> interval_cases t <;> omega
  let x : Fin 3 × Fin 3 → Q := fun uj => a ^ (1 + 3 * (uj.1 : ℕ)) * c ^ (uj.2 : ℕ)
  have hx3 : ∀ uj, (x uj) ^ 3 = a ^ 3 := by
    rintro ⟨u, j⟩
    simp only [x]
    have hcj3 : (c ^ (j : ℕ)) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hc3, one_pow]
    rw [mul_pow_three_of_conj (conj_pow_iterate hcconj j), hcj3, mul_one, pow_eq_pow_iff_modEq,
      ha]
    unfold Nat.ModEq
    rcases hr47 with rfl | rfl <;> fin_cases u <;> fin_cases j <;> decide
  have hπc : orderOf (c : Q ⧸ A) = 3 := by
    have h1 : (c : Q ⧸ A) ≠ 1 := fun h => hcA ((QuotientGroup.eq_one_iff c).mp h)
    have h3 : (c : Q ⧸ A) ^ 3 = 1 := by rw [← QuotientGroup.mk_pow, hc3, QuotientGroup.mk_one]
    exact orderOf_eq_prime h3 h1
  have ha1 : (a : Q ⧸ A) = 1 := (QuotientGroup.eq_one_iff a).mpr (Subgroup.mem_zpowers a)
  have hinj : Function.Injective x := by
    rintro ⟨u, j⟩ ⟨u', j'⟩ h
    simp only [x] at h
    have hj : (j : ℕ) = j' := by
      have h' := congrArg (fun g : Q => (g : Q ⧸ A)) h
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow, ha1, one_pow, one_mul] at h'
      exact pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hπc]; exact j.isLt)
        (by rw [Set.mem_Iio, hπc]; exact j'.isLt) h'
    have hjj : j = j' := Fin.ext hj
    subst hjj
    have hu : a ^ (1 + 3 * (u : ℕ)) = a ^ (1 + 3 * (u' : ℕ)) := mul_right_cancel h
    have := pow_injOn_Iio_orderOf (x := a) (by rw [Set.mem_Iio, ha]; omega)
      (by rw [Set.mem_Iio, ha]; omega) hu
    have huu : u = u' := Fin.ext (by omega)
    rw [huu]
  calc 9 = Nat.card (Fin 3 × Fin 3) := by simp
    _ ≤ Nat.card {g : Q // g ^ 3 = a ^ 3} :=
      Nat.card_le_card_of_injective (fun uj => ⟨x uj, hx3 uj⟩)
        (fun p q h => hinj (congrArg Subtype.val h))

theorem orderOf_eq_nine_of_pow_three {G : Type*} [Group G] {g h : G} (hg : g ^ 3 = h)
    (hh : orderOf h = 3) : orderOf g = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : h ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hh
    omega
  have := orderOf_eq_prime_pow (p := 3) (n := 1) (x := g) (by rw [pow_one, hg]; exact h1)
    (by rw [show 3 ^ (1 + 1) = 3 * 3 by norm_num, pow_mul, hg, ← hh, pow_orderOf_eq_one])
  simpa using this

theorem order_twenty_seven_nine_cycle_fusion_inequality {G : Type*} [Group G] [Finite G]
    (P : Sylow 3 G) (hP : Nat.card (P : Subgroup G) = 27)
    (hPna : ¬ IsMulCommutative (P : Subgroup G)) (h9 : ∃ g ∈ (P : Subgroup G), orderOf g = 9)
    (hconj : ∀ x y : G, orderOf x = 3 → orderOf y = 3 → IsConj x y) :
    9 * Nat.card {g : G // orderOf g = 3} ≤ Nat.card {g : G // orderOf g = 9} ∧
      ∀ D : Subgroup G, Nat.card D = 3 →
        3 ≤ Nat.card {C : Subgroup G // IsCyclic C ∧ Nat.card C = 9 ∧ D ≤ C} := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨a, haP, ha⟩ := h9
  have hcore : 9 ≤ Nat.card {g : G // g ^ 3 = a ^ 3} := by
    have h := nine_le_card_cube_eq (Q := (P : Subgroup G)) hP hPna (a := ⟨a, haP⟩)
      (by rw [Subgroup.orderOf_mk]; exact ha)
    refine le_trans h (Nat.card_le_card_of_injective
      (fun g => ⟨((g.1 : (P : Subgroup G)) : G), by
        rw [← Subgroup.coe_pow, g.2]; rfl⟩) ?_)
    intro g g' hgg
    have hval := congrArg Subtype.val hgg
    simp only at hval
    exact Subtype.ext (Subtype.ext hval)
  have ha3 : orderOf (a ^ 3) = 3 := by
    rw [orderOf_pow' a (by norm_num), ha]
    norm_num
  have hfiber : ∀ h : G, orderOf h = 3 → 9 ≤ Nat.card {g : G // g ^ 3 = h} := by
    intro h hh
    obtain ⟨x, hx⟩ := isConj_iff.mp (hconj (a ^ 3) h ha3 hh)
    refine le_trans hcore (le_of_eq (Nat.card_congr
      ((MulAut.conj x).toEquiv.subtypeEquiv fun g => ?_)))
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    rw [conj_pow, ← hx]
    constructor
    · intro hg
      rw [hg]
    · intro hg
      simpa using hg
  refine ⟨?_, fun D hD => ?_⟩
  · let f : {g : G // orderOf g = 9} → {g : G // orderOf g = 3} := fun g =>
      ⟨g.1 ^ 3, by rw [orderOf_pow' _ (by norm_num), g.2]; norm_num⟩
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
    calc 9 * Nat.card {g : G // orderOf g = 3}
        = ∑ _h : {g : G // orderOf g = 3}, 9 := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card,
            mul_comm]
      _ ≤ ∑ h, Nat.card {g // f g = h} := Finset.sum_le_sum fun h _ => by
          refine le_trans (hfiber h.1 h.2) (le_of_eq (Nat.card_congr ?_))
          exact {
            toFun := fun g => ⟨⟨g.1, orderOf_eq_nine_of_pow_three g.2 h.2⟩, Subtype.ext g.2⟩
            invFun := fun g => ⟨g.1.1, congrArg Subtype.val g.2⟩
            left_inv := fun g => rfl
            right_inv := fun g => rfl }
  · obtain ⟨h, hhD, hh1⟩ : ∃ h ∈ D, h ≠ 1 := by
      rcases D.bot_or_exists_ne_one with hbot | hex
      · rw [hbot, Subgroup.card_bot] at hD
        omega
      · exact hex
    have hh : orderOf h = 3 := by
      have hdvd := D.orderOf_dvd_natCard hhD
      rw [hD] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hh1
      · exact h3
    have hDz : D = Subgroup.zpowers h :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hhD)
        (by rw [hD, Nat.card_zpowers, hh])).symm
    let S := {C : Subgroup G // IsCyclic C ∧ Nat.card C = 9 ∧ D ≤ C}
    let φ : {g : G // g ^ 3 = h} → S := fun g => ⟨Subgroup.zpowers g.1, inferInstance, by
        rw [Nat.card_zpowers, orderOf_eq_nine_of_pow_three g.2 hh], by
        rw [hDz, Subgroup.zpowers_le]
        exact Subgroup.mem_zpowers_iff.mpr ⟨3, by rw [zpow_ofNat]; exact g.2⟩⟩
    have hle := Finset.card_le_mul_card_image (f := φ) Finset.univ 3 (by
      intro C hC
      obtain ⟨g₀, -, rfl⟩ := Finset.mem_image.mp hC
      have hg₀ := orderOf_eq_nine_of_pow_three g₀.2 hh
      calc (Finset.univ.filter fun g => φ g = φ g₀).card
          = ((Finset.univ.filter fun g => φ g = φ g₀).map
              (Function.Embedding.subtype _)).card := (Finset.card_map _).symm
        _ ≤ ({g₀.1, g₀.1 ^ 4, g₀.1 ^ 7} : Finset G).card := by
          apply Finset.card_le_card
          intro y hy
          obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hy
          have hzp : Subgroup.zpowers g.1 = Subgroup.zpowers g₀.1 :=
            congrArg Subtype.val (Finset.mem_filter.mp hg).2
          have hmem : g.1 ∈ Subgroup.zpowers g₀.1 := hzp ▸ Subgroup.mem_zpowers g.1
          obtain ⟨e, he, hge⟩ := Finset.mem_image.mp
            ((mem_zpowers_iff_mem_range_orderOf).mp hmem)
          rw [hg₀, Finset.mem_range] at he
          have hcube : g₀.1 ^ (3 * e) = g₀.1 ^ 3 := by
            rw [pow_mul', hge, g.2, g₀.2]
          rw [pow_eq_pow_iff_modEq, hg₀] at hcube
          unfold Nat.ModEq at hcube
          simp only [Function.Embedding.subtype_apply, Finset.mem_insert, Finset.mem_singleton]
          rw [← hge]
          interval_cases e <;> simp_all
        _ ≤ 3 := Finset.card_le_three)
    have hcardS : (Finset.univ.image φ).card ≤ Nat.card S := by
      rw [Nat.card_eq_fintype_card]
      exact Finset.card_le_univ _
    have := hfiber h hh
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ] at this
    change 3 ≤ Nat.card S
    omega

end CFSG.Semidihedral.Principal
