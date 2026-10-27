module

public import CFSG.Fischer.Uniq.Graph
public import CFSG.Timmesfeld.Basic

public section

namespace CFSG.EvenSmallLie.ThreeTransposition

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {G : Type} [Group G]

@[expose] def IsOddTranspositionSet (D : Set G) : Prop :=
  ∀ a ∈ D, ∀ b ∈ D, Odd (orderOf (a * b)) ∨ orderOf (a * b) = 2

@[expose] def IsThreeTranspositionSet (E : Set G) : Prop :=
  (∀ x ∈ E, orderOf x = 2) ∧ (∀ g ∈ Subgroup.closure E, ∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧
    ∀ x ∈ E, ∀ y ∈ E, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ)

theorem isOddTranspositionSet_of_orders {E : Set G}
    (h : ∀ x ∈ E, ∀ y ∈ E, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ)) : IsOddTranspositionSet E := by
  intro a ha b hb
  rcases h a ha b hb with h1 | h2 | h3
  · exact Or.inl (by rw [h1]; exact odd_one)
  · exact Or.inr h2
  · exact Or.inl (by rw [Set.mem_singleton_iff.1 h3]; exact ⟨1, rfl⟩)

section Involutions

theorem mul_self_of_orderOf {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  rw [← sq, ← hx, pow_orderOf_eq_one]

theorem inv_of_orderOf {x : G} (hx : orderOf x = 2) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (mul_self_of_orderOf hx)

theorem ne_one_of_orderOf {x : G} (hx : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  simp at hx

theorem mem_zpowers_iff_of_mul_self {K : Type*} [Group K] {u z : K} (hu : u * u = 1) :
    z ∈ Subgroup.zpowers u ↔ z = 1 ∨ z = u := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · exact Or.inl (by rw [zpow_mul, zpow_two, hu, one_zpow])
    · exact Or.inr (by rw [zpow_add_one, zpow_mul, zpow_two, hu, one_zpow, one_mul])
  · rintro (rfl | rfl)
    exacts [⟨0, zpow_zero _⟩, ⟨1, zpow_one _⟩]

theorem commute_iff_orderOf_mul {x y : G} (hx : x * x = 1) (hy : y * y = 1) :
    x * y = y * x ↔ orderOf (x * y) = 1 ∨ orderOf (x * y) = 2 := by
  rw [← Nat.dvd_prime Nat.prime_two, orderOf_dvd_iff_pow_eq_one,
    ← Timmesfeld.commute_iff_mul_sq_eq_one hx hy]
  rfl

theorem orderOf_mul_of_commute {x y : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x ≠ y)
    (hc : x * y = y * x) : orderOf (x * y) = 2 := by
  rcases (commute_iff_orderOf_mul hx hy).1 hc with h | h
  · refine absurd ?_ hxy
    rw [orderOf_eq_one_iff] at h
    rw [← inv_eq_of_mul_eq_one_right hy, eq_inv_iff_mul_eq_one, h]
  · exact h

theorem commute_of_mem_closure_of_pairwise {S : Set G}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {x y : G} (hx : x ∈ Subgroup.closure S)
    (hy : y ∈ Subgroup.closure S) : x * y = y * x := by
  have hSC : S ⊆ Subgroup.centralizer S := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => hS b hb a ha
  have hyC : y ∈ Subgroup.centralizer S :=
    Subgroup.centralizer_le hSC (Subgroup.closure_le_centralizer_centralizer S hy)
  have hxC : Subgroup.closure S ≤ Subgroup.centralizer {y} := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hyC a ha
  exact Subgroup.mem_centralizer_singleton_iff.1 (hxC hx)

end Involutions

section Dihedral

variable {u v : G}

theorem inv_mul_mul_eq (hu : u * u = 1) (hv : v * v = 1) : (u * v)⁻¹ * u = u * (u * v) := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hv, inv_eq_of_mul_eq_one_right hu, mul_assoc, hu,
    mul_one, ← mul_assoc, hu, one_mul]

theorem conj_mul_pow_eq (hu : u * u = 1) (hv : v * v = 1) (i j : ℕ) :
    (u * v)⁻¹ ^ i * (u * (u * v) ^ j) * ((u * v)⁻¹ ^ i)⁻¹ = u * (u * v) ^ (j + 2 * i) := by
  induction i generalizing j with
  | zero => simp
  | succ i ih =>
    have h1 : (u * v)⁻¹ * (u * (u * v) ^ j) * ((u * v)⁻¹)⁻¹ = u * (u * v) ^ (j + 2) := by
      calc (u * v)⁻¹ * (u * (u * v) ^ j) * ((u * v)⁻¹)⁻¹
          = ((u * v)⁻¹ * u) * ((u * v) ^ j * (u * v)) := by simp only [inv_inv, mul_assoc]
        _ = u * ((u * v) * (u * v) ^ (j + 1)) := by
          rw [inv_mul_mul_eq hu hv, ← pow_succ, mul_assoc]
        _ = u * (u * v) ^ (j + 2) := by rw [← pow_succ']
    calc (u * v)⁻¹ ^ (i + 1) * (u * (u * v) ^ j) * ((u * v)⁻¹ ^ (i + 1))⁻¹
        = (u * v)⁻¹ ^ i * ((u * v)⁻¹ * (u * (u * v) ^ j) * ((u * v)⁻¹)⁻¹) *
            ((u * v)⁻¹ ^ i)⁻¹ := by
          rw [pow_succ, mul_inv_rev ((u * v)⁻¹ ^ i) (u * v)⁻¹]
          simp only [mul_assoc]
      _ = u * (u * v) ^ (j + 2 * (i + 1)) := by
          rw [h1, ih, show j + 2 + 2 * i = j + 2 * (i + 1) by ring]

theorem exists_conj_eq_mul_pow (hu : u * u = 1) (hv : v * v = 1) (j : ℕ) :
    (∃ g ∈ Subgroup.closure ({u, v} : Set G), g * u * g⁻¹ = u * (u * v) ^ j) ∨
      ∃ g ∈ Subgroup.closure ({u, v} : Set G), g * v * g⁻¹ = u * (u * v) ^ j := by
  have hmem : (u * v)⁻¹ ∈ Subgroup.closure ({u, v} : Set G) :=
    Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
  · refine Or.inl ⟨(u * v)⁻¹ ^ i, Subgroup.pow_mem _ hmem i, ?_⟩
    have h := conj_mul_pow_eq hu hv i 0
    rwa [pow_zero, mul_one, zero_add] at h
  · refine Or.inr ⟨(u * v)⁻¹ ^ i, Subgroup.pow_mem _ hmem i, ?_⟩
    have h := conj_mul_pow_eq hu hv i 1
    rwa [pow_one, ← mul_assoc u u v, hu, one_mul, add_comm 1] at h

theorem dihedral_center (hu : u * u = 1) (hv : v * v = 1) {k : ℕ}
    (hk : orderOf (u * v) = k + k) (hk0 : 0 < k) :
    (u * v) ^ k ≠ 1 ∧ (u * v) ^ k * (u * v) ^ k = 1 ∧ u * (u * v) ^ k = (u * v) ^ k * u ∧
      v * (u * v) ^ k = (u * v) ^ k * v := by
  have hz1 : (u * v) ^ k ≠ 1 := by
    intro h1
    have h2 := Nat.le_of_dvd hk0 (orderOf_dvd_of_pow_eq_one h1)
    omega
  have hz2 : (u * v) ^ k * (u * v) ^ k = 1 := by
    rw [← pow_add, ← hk, pow_orderOf_eq_one]
  have hzu : u * (u * v) ^ k = (u * v) ^ k * u := by
    have e := Timmesfeld.mul_zpow_mul_eq_zpow_neg_mul hu hv (k : ℤ)
    rw [zpow_natCast, zpow_neg, zpow_natCast, inv_eq_of_mul_eq_one_right hz2] at e
    exact e
  refine ⟨hz1, hz2, hzu, ?_⟩
  have hc : Commute (u * (u * v)) ((u * v) ^ k) :=
    Commute.mul_left (hzu : Commute u _) (Commute.self_pow (u * v) k)
  rw [← mul_assoc, hu, one_mul] at hc
  exact hc

end Dihedral

section OneOne

variable {D : Set G}

theorem IsOddTranspositionSet.commute_of_commute_mul (hD2 : ∀ x ∈ D, orderOf x = 2)
    (hodd : IsOddTranspositionSet D) {a b c : G} (ha : a ∈ D) (hb : b ∈ LocalClass D a)
    (hc : c ∈ D) (hcab : c * (a * b) = a * b * c) : c * a = a * c := by
  by_contra hca
  have ha2 := mul_self_of_orderOf (hD2 a ha)
  have hb2 := mul_self_of_orderOf (hD2 b hb.1)
  have hc2 := mul_self_of_orderOf (hD2 c hc)
  have hm : Odd (orderOf (c * a)) := by
    rcases hodd c hc a ha with h | h
    · exact h
    · exact absurd ((commute_iff_orderOf_mul hc2 ha2).2 (Or.inr h)) hca
  have hab : orderOf (a * b) = 2 :=
    orderOf_mul_of_commute ha2 hb2 (fun h => hb.2.1 h.symm) hb.2.2.symm
  have hcomm : Commute (c * a) (a * b) :=
    (Commute.mul_right (hcab.symm : Commute (a * b) c)
      ((Commute.refl a).mul_left (hb.2.2 : Commute b a))).symm
  have hcb : c * b = c * a * (a * b) := by rw [mul_assoc, ← mul_assoc a a b, ha2, one_mul]
  have hcop : (orderOf (c * a)).Coprime (orderOf (a * b)) := by
    rw [hab]
    exact Nat.coprime_two_right.2 hm
  have hord : orderOf (c * b) = orderOf (c * a) * 2 := by
    rw [hcb, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hab]
  rcases hodd c hc b hb.1 with h | h
  · rw [hord] at h
    exact Nat.not_odd_iff_even.2 even_two (Nat.odd_mul.1 h).2
  · rw [hord] at h
    have h1 : c * a = 1 := orderOf_eq_one_iff.1 (by omega)
    have hc' : c = a⁻¹ := eq_inv_of_mul_eq_one_left h1
    exact hca (by rw [hc', inv_mul_cancel, mul_inv_cancel])

theorem isOddTranspositionSet_iff [Finite G] (hD2 : ∀ x ∈ D, orderOf x = 2)
    (hDinv : ∀ g ∈ Subgroup.closure D, ∀ x ∈ D, g * x * g⁻¹ ∈ D) :
    IsOddTranspositionSet D ↔ ∀ a ∈ D, ∀ b ∈ LocalClass D a,
      D ∩ (Subgroup.centralizer {a * b} : Set G) =
        (D ∩ (Subgroup.centralizer {a} : Set G)) ∩ (D ∩ (Subgroup.centralizer {b} : Set G)) := by
  constructor
  · intro hodd a ha b hb
    have hab' : a ∈ LocalClass D b := ⟨ha, fun h => hb.2.1 h.symm, hb.2.2.symm⟩
    ext c
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hc, hcab⟩
      refine ⟨⟨hc, hodd.commute_of_commute_mul hD2 ha hb hc hcab⟩, hc,
        hodd.commute_of_commute_mul hD2 hb.1 hab' hc ?_⟩
      rw [hb.2.2]
      exact hcab
    · rintro ⟨⟨hc, hca⟩, -, hcb⟩
      exact ⟨hc, by rw [← mul_assoc, hca, mul_assoc, hcb, ← mul_assoc]⟩
  · intro h a ha d hd
    have ha2 := mul_self_of_orderOf (hD2 a ha)
    have hd2 := mul_self_of_orderOf (hD2 d hd)
    by_cases hm : Odd (orderOf (a * d))
    · exact Or.inl hm
    right
    obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.1 hm
    have hk0 : 0 < k := by
      have := orderOf_pos (a * d)
      omega
    obtain ⟨hz1, -, hza, hzd⟩ := dihedral_center ha2 hd2 hk hk0
    have hdzD : d * (a * d) ^ k ∈ D := by
      have e : d * (a * d) ^ k = a * (a * d) ^ (k + 1) := by
        rw [pow_succ', ← mul_assoc, ← mul_assoc a a d, ha2, one_mul]
      have hcl : Subgroup.closure ({a, d} : Set G) ≤ Subgroup.closure D := by
        refine Subgroup.closure_mono ?_
        rintro x (rfl | rfl)
        exacts [ha, hd]
      rw [e]
      rcases exists_conj_eq_mul_pow ha2 hd2 (k + 1) with ⟨g, hg, hgx⟩ | ⟨g, hg, hgx⟩
      · exact hgx ▸ hDinv g (hcl hg) a ha
      · exact hgx ▸ hDinv g (hcl hg) d hd
    have hdz : d * (a * d) ^ k ∈ LocalClass D d := by
      refine ⟨hdzD, fun e => hz1 (mul_left_cancel (e.trans (mul_one d).symm)), ?_⟩
      rw [mul_assoc, ← hzd, ← mul_assoc]
    have haz : a ∈ D ∩ (Subgroup.centralizer {d * (d * (a * d) ^ k)} : Set G) := by
      refine ⟨ha, ?_⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← mul_assoc d d, hd2,
        one_mul]
      exact hza
    rw [h d hd _ hdz] at haz
    have had : a * d = d * a := Subgroup.mem_centralizer_singleton_iff.1 haz.1.2
    rcases (commute_iff_orderOf_mul ha2 hd2).1 had with h1 | h2
    · exact absurd (h1 ▸ odd_one) hm
    · exact h2

end OneOne

section OneTwo

variable {D : Set G}

theorem IsOddTranspositionSet.subset {E : Set G} (hD : IsOddTranspositionSet D) (hE : E ⊆ D) :
    IsOddTranspositionSet E :=
  fun a ha b hb => hD a (hE ha) b (hE hb)

theorem IsOddTranspositionSet.commute_of_mem_pGroup (hD2 : ∀ x ∈ D, orderOf x = 2)
    (hD : IsOddTranspositionSet D) {P : Subgroup G} (hP : IsPGroup 2 P) {a b : G} (ha : a ∈ D)
    (haP : a ∈ P) (hb : b ∈ D) (hbP : b ∈ P) : a * b = b * a := by
  have ha2 := mul_self_of_orderOf (hD2 a ha)
  have hb2 := mul_self_of_orderOf (hD2 b hb)
  rw [commute_iff_orderOf_mul ha2 hb2]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨a * b, P.mul_mem haP hbP⟩
  have hk' : orderOf (a * b) = 2 ^ k := by rw [← hk, ← Subgroup.orderOf_coe]
  rcases hD a ha b hb with h | h
  · left
    rw [hk'] at h ⊢
    rcases k with _ | k
    · rfl
    · exact absurd h (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero k⟩))
  · exact Or.inr h

theorem IsOddTranspositionSet.locallyConjugate (hD2 : ∀ x ∈ D, orderOf x = 2)
    (hD : IsOddTranspositionSet D) {a b : G} (ha : a ∈ D) (hb : b ∈ D) :
    a * b = b * a ∨ ∃ g ∈ Subgroup.closure ({a, b} : Set G), g * a * g⁻¹ = b := by
  have ha2 := mul_self_of_orderOf (hD2 a ha)
  have hb2 := mul_self_of_orderOf (hD2 b hb)
  rcases hD a ha b hb with h | h
  · exact Or.inr (Timmesfeld.exists_conj_of_odd_orderOf_mul ha2 hb2 h)
  · exact Or.inl ((commute_iff_orderOf_mul ha2 hb2).2 (Or.inr h))

theorem IsOddTranspositionSet.connected_of_not_transitive (hD2 : ∀ x ∈ D, orderOf x = 2)
    (hD : IsOddTranspositionSet D)
    (hnt : ¬ ∀ a ∈ D, ∀ b ∈ D, ∃ g ∈ Subgroup.closure D, g * a * g⁻¹ = b) :
    (commGraph D).Connected := by
  push Not at hnt
  obtain ⟨a, ha, b, hb, hab⟩ := hnt
  let O : Set G := {u | ∃ g ∈ Subgroup.closure D, g * a * g⁻¹ = u}
  have hcomm : ∀ u ∈ D, u ∈ O → ∀ v ∈ D, v ∉ O → u * v = v * u := by
    rintro u hu ⟨g, hg, rfl⟩ v hv hvO
    rcases hD.locallyConjugate hD2 hu hv with h | ⟨k, hk, hkv⟩
    · exact h
    · refine absurd ⟨k * g, Subgroup.mul_mem _ (Subgroup.closure_mono ?_ hk) hg, ?_⟩ hvO
      · rintro x (rfl | rfl)
        exacts [hu, hv]
      · rw [← hkv]
        group
  have haO : a ∈ O := ⟨1, Subgroup.one_mem _, by group⟩
  have hbO : b ∉ O := fun ⟨g, hg, h⟩ => hab g hg h
  have hab' : (commGraph D).Reachable ⟨a, ha⟩ ⟨b, hb⟩ :=
    commGraph_reachable_of_commute (hcomm a ha haO b hb hbO)
  have hall : ∀ x : D, (commGraph D).Reachable ⟨a, ha⟩ x := by
    rintro ⟨x, hx⟩
    by_cases hxO : x ∈ O
    · exact hab'.trans (commGraph_reachable_of_commute (hcomm x hx hxO b hb hbO).symm)
    · exact commGraph_reachable_of_commute (hcomm a ha haO x hx hxO)
  rw [SimpleGraph.connected_iff]
  exact ⟨fun x y => (hall x).symm.trans (hall y), ⟨⟨a, ha⟩⟩⟩

end OneTwo

end CFSG.EvenSmallLie.ThreeTransposition
