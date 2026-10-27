module

public import CFSG.CharacterTheory.Semidihedral.Principal.ExactGL2CharacterColumns
public import CFSG.CharacterTheory.Semidihedral.Principal.GL2ThreeProfile

public section

open scoped Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.GL2ThreeCharacters
open CFSG.Semidihedral.FourPointMatrices (normalUnit normalUnit_surjective)
open CFSG.TwoRankLowerBound.Helpers (orderOf_eq_of_isConj)

section Classes

variable {G : Type*} [Group G]

theorem orderOf_conj (c g : G) : orderOf (c * g * c⁻¹) = orderOf g := by
  have h := MulEquiv.orderOf_eq (MulAut.conj c) g
  rwa [MulAut.conj_apply] at h

theorem orderOf_pred_of_isConj (Q : ℕ → Prop) {g h : G} (hgh : IsConj g h)
    (hg : Q (orderOf g)) : Q (orderOf h) :=
  (orderOf_eq_of_isConj hgh) ▸ hg

theorem card_centralizer_conj (c g : G) :
    Nat.card (Subgroup.centralizer ({c * g * c⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  have h := card_centralizer_mulEquiv (MulAut.conj c) g
  rw [MulAut.conj_apply] at h
  exact h.symm

theorem nonempty_centralizer_mulEquiv_of_isConj {g h : G} (hgh : IsConj g h) :
    Nonempty (Subgroup.centralizer ({g} : Set G) ≃* Subgroup.centralizer ({h} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hgh
  refine ⟨
    { toFun := fun x => ⟨c * x * c⁻¹, ?_⟩
      invFun := fun y => ⟨c⁻¹ * y * c, ?_⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }⟩
  · have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c * ↑x * c⁻¹ * (c * g * c⁻¹) = c * (↑x * g) * c⁻¹ := by group
      _ = c * (g * ↑x) * c⁻¹ := by rw [hx]
      _ = c * g * c⁻¹ * (c * ↑x * c⁻¹) := by group
  · have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c⁻¹ * ↑y * c * g = c⁻¹ * (↑y * (c * g * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * g * c⁻¹) * ↑y) * c := by rw [hy]
      _ = g * (c⁻¹ * ↑y * c) := by group

theorem isConj_of_isConj_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {a b : A}
    (h : IsConj (e a) (e b)) : IsConj a b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨e.symm c, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc]

theorem isConj_coe {H : Subgroup G} {x y : H} (h : IsConj x y) : IsConj (x : G) (y : G) :=
  H.subtype.map_isConj h

theorem card_eq_mul_of_card_fiber {α β : Type*} [Finite α] [Finite β] (F : α → β) (k : ℕ)
    (h : ∀ b, Nat.card {a // F a = b} = k) : Nat.card α = k * Nat.card β := by
  have := Fintype.ofFinite β
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv F), Nat.card_sigma,
    Finset.sum_congr rfl fun b _ => h b, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_comm, Nat.card_eq_fintype_card]

theorem card_eq_mul_card_classes [Finite G] (P : G → Prop)
    (hP : ∀ g h : G, IsConj g h → P g → P h)
    (s : ℕ) (hs : ∀ g : G, P g → Nat.card (ConjClasses.mk g).carrier = s) :
    Nat.card {g : G // P g} =
      s * Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g} := by
  refine card_eq_mul_of_card_fiber
    (fun g : {g : G // P g} => (⟨ConjClasses.mk g.1, g.1, rfl, g.2⟩ :
      {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g})) s ?_
  rintro ⟨c, g, rfl, hg⟩
  rw [← hs g hg]
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, ConjClasses.mem_carrier_iff_mk_eq.mpr
        (congrArg Subtype.val x.2)⟩
      invFun := fun y => ⟨⟨y.1, hP g y.1 (ConjClasses.mk_eq_mk_iff_isConj.mp
          (ConjClasses.mem_carrier_iff_mk_eq.mp y.2)).symm hg⟩,
        Subtype.ext (ConjClasses.mem_carrier_iff_mk_eq.mp y.2)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem card_classes_or [Finite G] (P Q : G → Prop)
    (hP : ∀ g h : G, IsConj g h → P g → P h)
    (hPQ : ∀ g, P g → ¬ Q g) :
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ (P g ∨ Q g)} =
      Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g} +
        Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ Q g} := by
  have hdisj : Disjoint (fun c : ConjClasses G => ∃ g, ConjClasses.mk g = c ∧ P g)
      (fun c => ∃ g, ConjClasses.mk g = c ∧ Q g) := by
    intro r hrP hrQ c hrc
    obtain ⟨g, rfl, hg⟩ := hrP c hrc
    obtain ⟨h, hh, hhQ⟩ := hrQ _ hrc
    exact hPQ h (hP g h (ConjClasses.mk_eq_mk_iff_isConj.mp hh.symm) hg) hhQ
  rw [← Nat.card_sum, ← Nat.card_congr (subtypeOrEquiv _ _ hdisj)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  constructor
  · rintro ⟨g, rfl, hg | hg⟩
    · exact Or.inl ⟨g, rfl, hg⟩
    · exact Or.inr ⟨g, rfl, hg⟩
  · rintro (⟨g, rfl, hg⟩ | ⟨g, rfl, hg⟩)
    · exact ⟨g, rfl, Or.inl hg⟩
    · exact ⟨g, rfl, Or.inr hg⟩

theorem card_classes_of_forall (P : G → Prop) (hP : ∀ g, P g) :
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g} =
      Nat.card (ConjClasses G) := by
  refine Nat.card_congr (Equiv.subtypeUnivEquiv fun c => ?_)
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  exact ⟨g, rfl, hP g⟩

theorem card_classes_congr {P Q : G → Prop} (h : ∀ g, P g ↔ Q g) :
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g} =
      Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ Q g} := by
  simp only [h]

theorem card_classes_orderOf_eq_one :
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ orderOf g = 1} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨ConjClasses.mk 1, 1, rfl, orderOf_one⟩, ?_⟩
  rintro ⟨c, g, rfl, hg⟩
  rw [orderOf_eq_one_iff] at hg
  subst hg
  rfl

theorem card_classes_eq_one (P : G → Prop) {x : G} (hx : P x) (h : ∀ g, P g → IsConj x g) :
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨ConjClasses.mk x, x, rfl, hx⟩, ?_⟩
  rintro ⟨c, g, rfl, hg⟩
  exact Subtype.ext (ConjClasses.mk_eq_mk_iff_isConj.mpr (h g hg).symm)

theorem card_classes_eq_two (P : G → Prop) {x y : G} (hx : P x) (hy : P y) (hxy : ¬ IsConj x y)
    (h : ∀ g, P g → IsConj x g ∨ IsConj y g) :
    Nat.card {c : ConjClasses G // ∃ g, ConjClasses.mk g = c ∧ P g} = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨ConjClasses.mk x, x, rfl, hx⟩, ⟨ConjClasses.mk y, y, rfl, hy⟩, fun he => hxy
    (ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val he)), ?_⟩
  ext ⟨c, g, rfl, hg⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases h g hg with h' | h'
  · exact Or.inl (Subtype.ext (ConjClasses.mk_eq_mk_iff_isConj.mpr h'.symm))
  · exact Or.inr (Subtype.ext (ConjClasses.mk_eq_mk_iff_isConj.mpr h'.symm))

theorem card_orderOf_mem_eq_sum [Finite G] (S : Finset ℕ) :
    Nat.card {g : G // orderOf g ∈ S} = ∑ k ∈ S, Nat.card {g : G // orderOf g = k} := by
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_card_fiberwise (f := orderOf)
      (s := Finset.univ.filter fun g : G => orderOf g ∈ S) (t := S)
      fun g hg => (Finset.mem_filter.mp hg).2]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  congr 1
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  intro h
  rw [h]
  exact hk

theorem card_eq_sum_card_orderOf [Finite G] (S : Finset ℕ) (hS : ∀ g : G, orderOf g ∈ S) :
    Nat.card G = ∑ k ∈ S, Nat.card {g : G // orderOf g = k} := by
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := orderOf) (t := S) fun g _ => hS g]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Classes

section GL2

@[expose] def classOrder : Fin 8 → ℕ := ![1, 2, 4, 3, 6, 2, 8, 8]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem coordinateOrder_eq_classOrder : ∀ i : Coord,
    GL2ThreeStructure.coordinateOrder i = classOrder (classOf (normalUnit i)) := by
  decide

theorem orderOf_eq_classOrder (g : G23) : orderOf g = classOrder (classOf g) := by
  obtain ⟨i, rfl⟩ := normalUnit_surjective g
  rw [GL2ThreeStructure.normalUnit_order]
  exact coordinateOrder_eq_classOrder i

theorem card_conjClass_eq_classSize (g : G23) :
    Nat.card (ConjClasses.mk g).carrier = classSize (classOf g) := by
  rw [← nat_card_classOf]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun h => ?_)
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_classOf]

theorem card_centralizer_mul_classSize (g : G23) :
    Nat.card (Subgroup.centralizer ({g} : Set G23)) * classSize (classOf g) = 48 := by
  have h := CFSG.LyonsUnitaryFour.card_conjClass_mul_card_centralizer g
  rw [card_conjClass_eq_classSize, card_G23] at h
  rw [mul_comm]
  exact h

theorem classOrder_facts : ∀ j : Fin 8,
    (classOrder j = 3 → j = 3) ∧ (classOrder j = 4 → j = 2) ∧ (classOrder j = 6 → j = 4) ∧
      (classOrder j = 8 → j = 6 ∨ j = 7) := by
  decide

theorem card_centralizer_GL2 (g : G23) :
    (orderOf g = 3 → Nat.card (Subgroup.centralizer ({g} : Set G23)) = 6) ∧
    (orderOf g = 4 → Nat.card (Subgroup.centralizer ({g} : Set G23)) = 8) ∧
    (orderOf g = 6 → Nat.card (Subgroup.centralizer ({g} : Set G23)) = 6) ∧
    (orderOf g = 8 → Nat.card (Subgroup.centralizer ({g} : Set G23)) = 8) := by
  have h := card_centralizer_mul_classSize g
  rw [orderOf_eq_classOrder]
  obtain ⟨h3, h4, h6, h8⟩ := classOrder_facts (classOf g)
  refine ⟨fun hg => ?_, fun hg => ?_, fun hg => ?_, fun hg => ?_⟩
  · rw [h3 hg] at h
    change Nat.card _ * 8 = 48 at h
    omega
  · rw [h4 hg] at h
    change Nat.card _ * 6 = 48 at h
    omega
  · rw [h6 hg] at h
    change Nat.card _ * 8 = 48 at h
    omega
  · rcases h8 hg with h' | h' <;> rw [h'] at h <;> change Nat.card _ * 6 = 48 at h <;> omega

theorem isConj_GL2_of_orderOf_eq {g h : G23} (hgh : orderOf g = orderOf h)
    (hk : orderOf g = 4 ∨ orderOf g = 6) : IsConj g h := by
  rw [isConj_iff_classOf]
  rw [orderOf_eq_classOrder, orderOf_eq_classOrder] at hgh
  rw [orderOf_eq_classOrder] at hk
  obtain ⟨-, h4, h6, -⟩ := classOrder_facts (classOf g)
  obtain ⟨-, h4', h6', -⟩ := classOrder_facts (classOf h)
  rcases hk with hk | hk
  · rw [h4 hk, h4' (hgh ▸ hk)]
  · rw [h6 hk, h6' (hgh ▸ hk)]

theorem classOf_a0 : classOf a0 = 6 := by decide

theorem classOf_a0_inv : classOf a0⁻¹ = 7 := by decide

theorem a0_pow_four : a0 ^ 4 = -1 := by decide

theorem isConj_a0_of_orderOf_eq_eight {g : G23} (hg : orderOf g = 8) :
    IsConj a0 g ∨ IsConj a0⁻¹ g := by
  rw [isConj_iff_classOf, isConj_iff_classOf, classOf_a0, classOf_a0_inv]
  rw [orderOf_eq_classOrder] at hg
  rcases (classOrder_facts (classOf g)).2.2.2 hg with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem not_isConj_a0_a0_inv : ¬ IsConj a0 a0⁻¹ := by
  rw [isConj_iff_classOf, classOf_a0, classOf_a0_inv]
  decide

theorem card_centralizer_neg_one :
    Nat.card (Subgroup.centralizer ({(-1 : G23)} : Set G23)) = 48 := by
  have h := card_centralizer_mul_classSize (-1)
  rw [classOf_neg_one] at h
  change Nat.card _ * 1 = 48 at h
  omega

end GL2

section Involution

variable {G : Type*} [Group G] {t : G}

theorem self_mem_centralizer (t : G) : t ∈ Subgroup.centralizer ({t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem mulEquiv_self_eq_neg_one (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) :
    φ ⟨t, self_mem_centralizer t⟩ = -1 := by
  have hcen : φ ⟨t, self_mem_centralizer t⟩ ∈ Subgroup.center G23 := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2)
  rw [GL2ThreeStructure.centerH, GL2ThreeStructure.mem_zpowers_z_iff] at hcen
  rcases hcen with h | h
  · exfalso
    have h1 : (⟨t, self_mem_centralizer t⟩ : Subgroup.centralizer ({t} : Set G)) = 1 :=
      φ.injective (h.trans φ.map_one.symm)
    have : t = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at ht
    norm_num at ht
  · rw [h, GL2_three_neg_one_eq_Z]

theorem mem_centralizer_of_pow_eq {g : G} {k : ℕ} (hk : g ^ k = t) :
    g ∈ Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
  exact ((Commute.refl g).pow_right k).eq

theorem centralizer_le_of_pow_eq {g : G} {k : ℕ} (hk : g ^ k = t) :
    Subgroup.centralizer ({g} : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  rw [← hk]
  exact ((Commute.pow_right hx k).eq)

end Involution


section EvenOrder

theorem GL2_even_order_of_pow_half_eq_neg_one {h : G23} (hh : Even (orderOf h))
    (hpow : h ^ (orderOf h / 2) = -1) :
    (orderOf h = 2 ∨ orderOf h = 4 ∨ orderOf h = 6 ∨ orderOf h = 8) ∧ (orderOf h = 2 → h = -1) := by
  have hmem := GL2ThreeStructure.order_exhaustive h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  refine ⟨?_, fun h2 => ?_⟩
  · rcases hmem with h1 | h1 | h1 | h1 | h1 | h1
    · rw [h1] at hh
      exact absurd hh (by decide)
    · exact Or.inl h1
    · rw [h1] at hh
      exact absurd hh (by decide)
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
  · rw [h2] at hpow
    simpa using hpow

variable {G : Type*} [Group G] {t : G}

theorem exists_conj_pow_half_eq [Finite G]
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    {g : G} (hg : Even (orderOf g)) : ∃ c : G, (c * g * c⁻¹) ^ (orderOf g / 2) = t := by
  have hu : orderOf (g ^ (orderOf g / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' (even_iff_two_dvd.mp hg)
  obtain ⟨c, hc⟩ := isConj_iff.mp (hinv _ t hu ht)
  exact ⟨c, by rw [conj_pow, hc]⟩

theorem mulEquiv_facts_of_pow_eq (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) {g : G} {k : ℕ} (hk : g ^ k = t) :
    orderOf (φ ⟨g, mem_centralizer_of_pow_eq hk⟩) = orderOf g ∧
      φ ⟨g, mem_centralizer_of_pow_eq hk⟩ ^ k = -1 ∧
      Nat.card (Subgroup.centralizer ({g} : Set G)) =
        Nat.card (Subgroup.centralizer ({φ ⟨g, mem_centralizer_of_pow_eq hk⟩} : Set G23)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  · rw [← map_pow, ← mulEquiv_self_eq_neg_one ht φ]
    congr 1
    exact Subtype.ext (by simp [hk])
  · rw [← card_centralizer_mulEquiv φ]
    exact card_centralizer_eq_of_le (Subgroup.centralizer ({t} : Set G))
      ⟨g, mem_centralizer_of_pow_eq hk⟩ (centralizer_le_of_pow_eq hk)

theorem card_centralizer_of_even_orderOf [Finite G]
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) {g : G} (hg : Even (orderOf g)) :
    (orderOf g = 2 ∨ orderOf g = 4 ∨ orderOf g = 6 ∨ orderOf g = 8) ∧
    (orderOf g = 2 → Nat.card (Subgroup.centralizer ({g} : Set G)) = 48) ∧
    (orderOf g = 4 → Nat.card (Subgroup.centralizer ({g} : Set G)) = 8) ∧
    (orderOf g = 6 → Nat.card (Subgroup.centralizer ({g} : Set G)) = 6) ∧
    (orderOf g = 8 → Nat.card (Subgroup.centralizer ({g} : Set G)) = 8) := by
  obtain ⟨c, hc⟩ := exists_conj_pow_half_eq hinv ht hg
  obtain ⟨hord, hpow, hcard⟩ := mulEquiv_facts_of_pow_eq ht φ hc
  generalize φ ⟨c * g * c⁻¹, mem_centralizer_of_pow_eq hc⟩ = h at hord hpow hcard
  rw [card_centralizer_conj] at hcard
  rw [orderOf_conj] at hord
  rw [hcard, ← hord]
  rw [← hord] at hpow hg
  obtain ⟨hmem, h2⟩ := GL2_even_order_of_pow_half_eq_neg_one hg hpow
  obtain ⟨-, h4, h6, h8⟩ := card_centralizer_GL2 h
  refine ⟨hmem, fun h' => ?_, h4, h6, h8⟩
  rw [h2 h']
  exact card_centralizer_neg_one

theorem isConj_of_orderOf_eq_four_or_six [Finite G]
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) {g₁ g₂ : G} (h12 : orderOf g₁ = orderOf g₂)
    (hk : orderOf g₁ = 4 ∨ orderOf g₁ = 6) : IsConj g₁ g₂ := by
  have hev : Even (orderOf g₁) := by rcases hk with h | h <;> rw [h] <;> decide
  obtain ⟨c₁, hc₁⟩ := exists_conj_pow_half_eq hinv ht hev
  obtain ⟨c₂, hc₂⟩ := exists_conj_pow_half_eq hinv ht (h12 ▸ hev)
  obtain ⟨hord₁, -, -⟩ := mulEquiv_facts_of_pow_eq ht φ hc₁
  obtain ⟨hord₂, -, -⟩ := mulEquiv_facts_of_pow_eq ht φ hc₂
  have hconj : IsConj (φ ⟨c₁ * g₁ * c₁⁻¹, mem_centralizer_of_pow_eq hc₁⟩)
      (φ ⟨c₂ * g₂ * c₂⁻¹, mem_centralizer_of_pow_eq hc₂⟩) := by
    apply isConj_GL2_of_orderOf_eq
    · rw [hord₁, hord₂, orderOf_conj, orderOf_conj, h12]
    · rw [hord₁, orderOf_conj]
      exact hk
  have hG := isConj_coe (isConj_of_isConj_mulEquiv φ hconj)
  exact (isConj_iff.mpr ⟨c₁, rfl⟩).trans (hG.trans (isConj_iff.mpr ⟨c₂, rfl⟩).symm)

theorem mulEquiv_symm_neg_one (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) :
    ((φ.symm (-1) : Subgroup.centralizer ({t} : Set G)) : G) = t := by
  rw [← mulEquiv_self_eq_neg_one ht φ, MulEquiv.symm_apply_apply]

theorem order_eight_classes [Finite G]
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) :
    orderOf ((φ.symm a0 : Subgroup.centralizer ({t} : Set G)) : G) = 8 ∧
    orderOf ((φ.symm a0⁻¹ : Subgroup.centralizer ({t} : Set G)) : G) = 8 ∧
    ¬ IsConj ((φ.symm a0 : Subgroup.centralizer ({t} : Set G)) : G)
      ((φ.symm a0⁻¹ : Subgroup.centralizer ({t} : Set G)) : G) ∧
    ∀ g : G, orderOf g = 8 →
      IsConj ((φ.symm a0 : Subgroup.centralizer ({t} : Set G)) : G) g ∨
        IsConj ((φ.symm a0⁻¹ : Subgroup.centralizer ({t} : Set G)) : G) g := by
  have hord : ∀ y : G23, orderOf ((φ.symm y : Subgroup.centralizer ({t} : Set G)) : G) =
      orderOf y := fun y => by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  refine ⟨by rw [hord, orderOf_a0], by rw [hord, orderOf_inv, orderOf_a0], ?_, ?_⟩
  · intro hconj
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hpow : ∀ y : G23, y ^ 4 = -1 →
        ((φ.symm y : Subgroup.centralizer ({t} : Set G)) : G) ^ 4 = t := by
      intro y hy
      rw [← Subgroup.coe_pow, ← map_pow, hy, mulEquiv_symm_neg_one ht φ]
    have h1 := hpow a0 a0_pow_four
    have h2 := hpow a0⁻¹ (by rw [inv_pow, a0_pow_four, inv_neg_one])
    have hct : c * t * c⁻¹ = t :=
      calc c * t * c⁻¹ = c * ((φ.symm a0 : Subgroup.centralizer ({t} : Set G)) : G) ^ 4 * c⁻¹ := by
            rw [h1]
        _ = (c * ((φ.symm a0 : Subgroup.centralizer ({t} : Set G)) : G) * c⁻¹) ^ 4 := conj_pow.symm
        _ = t := by rw [hc, h2]
    have hcC : c ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc c * t = c * t * c⁻¹ * c := by group
        _ = t * c := by rw [hct]
    apply not_isConj_a0_a0_inv
    refine isConj_iff.mpr ⟨φ ⟨c, hcC⟩, ?_⟩
    apply φ.symm.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact Subtype.ext hc
  · intro g hg
    have hev : Even (orderOf g) := by rw [hg]; decide
    obtain ⟨c, hc⟩ := exists_conj_pow_half_eq hinv ht hev
    obtain ⟨hord', -, -⟩ := mulEquiv_facts_of_pow_eq ht φ hc
    have hback : ∀ y : G23, IsConj y (φ ⟨c * g * c⁻¹, mem_centralizer_of_pow_eq hc⟩) →
        IsConj ((φ.symm y : Subgroup.centralizer ({t} : Set G)) : G) g := by
      intro y hy
      rw [← MulEquiv.apply_symm_apply φ y] at hy
      exact (isConj_coe (isConj_of_isConj_mulEquiv φ hy)).trans (isConj_iff.mpr ⟨c, rfl⟩).symm
    have h8 : orderOf (φ ⟨c * g * c⁻¹, mem_centralizer_of_pow_eq hc⟩) = 8 := by
      rw [hord', orderOf_conj, hg]
    rcases isConj_a0_of_orderOf_eq_eight h8 with h | h
    · exact Or.inl (hback _ h)
    · exact Or.inr (hback _ h)

theorem nonempty_centralizer_involution_mulEquiv
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) {u : G} (hu : orderOf u = 2) :
    Nonempty (Subgroup.centralizer ({u} : Set G) ≃* G23) := by
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_of_isConj (hinv u t hu ht)
  exact ⟨e.trans φ⟩

theorem card_centralizer_involution
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) {u : G} (hu : orderOf u = 2) :
    Nat.card (Subgroup.centralizer ({u} : Set G)) = 48 := by
  obtain ⟨e⟩ := nonempty_centralizer_involution_mulEquiv hinv ht φ hu
  rw [Nat.card_congr e.toEquiv, card_G23]

end EvenOrder

end CFSG.Semidihedral.GL2Recognition
