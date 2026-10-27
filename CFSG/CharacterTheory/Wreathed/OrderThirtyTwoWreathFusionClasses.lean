module

public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusionCoordinates
public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionAction

public noncomputable section

namespace CFSG.Wreathed.OrderThirtyTwo

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.AdaptedBaseFusion

universe u

@[expose] def orbitRel (p q : ZMod 4 × ZMod 4) : Prop :=
  q = p ∨ q = cycleMap p ∨ q = cycleMap (cycleMap p) ∨ q = swapMap p ∨
    q = swapMap (cycleMap p) ∨ q = swapMap (cycleMap (cycleMap p))

instance (p q : ZMod 4 × ZMod 4) : Decidable (orbitRel p q) := by
  unfold orbitRel
  infer_instance

@[expose] def coordClass : Fin 5 → List (ZMod 4 × ZMod 4) :=
  ![[(0, 0)], [(2, 2), (2, 0), (0, 2)], [(1, 1), (3, 0), (0, 3)], [(3, 3), (1, 0), (0, 1)],
    [(1, 3), (3, 1), (1, 2), (2, 1), (3, 2), (2, 3)]]

theorem coordClass_cover : ∀ p : ZMod 4 × ZMod 4, ∃ i, p ∈ coordClass i := by decide

theorem coordClass_disjoint :
    ∀ (p : ZMod 4 × ZMod 4) (i j : Fin 5), p ∈ coordClass i → p ∈ coordClass j → i = j := by
  decide

theorem orbitRel_iff :
    ∀ p q : ZMod 4 × ZMod 4, orbitRel p q ↔ ∃ i, p ∈ coordClass i ∧ q ∈ coordClass i := by
  decide

theorem swapMap_eq : ∀ p : ZMod 4 × ZMod 4,
    p.1.val • ((0, 1) : ZMod 4 × ZMod 4) + p.2.val • ((1, 0) : ZMod 4 × ZMod 4) = swapMap p := by
  decide

theorem cycleMap_eq : ∀ p : ZMod 4 × ZMod 4,
    p.1.val • ((0, 1) : ZMod 4 × ZMod 4) + p.2.val • ((3, 3) : ZMod 4 × ZMod 4) =
      cycleMap p := by
  decide

@[expose] def baseClasses {G : Type u} [Group G] (a σ υ : G) : Fin 5 → Set G :=
  ![{1}, {a ^ 2, σ ^ 2, υ ^ 2}, {a, σ⁻¹, υ⁻¹}, {a⁻¹, σ, υ},
    {σ * υ⁻¹, (σ * υ⁻¹)⁻¹, σ * υ ^ 2, σ ^ 2 * υ, σ ^ 3 * υ ^ 2, σ ^ 2 * υ ^ 3}]

variable {G : Type u} [Group G]

theorem conj_pow_eq (k x : G) (n : ℕ) : k⁻¹ * x ^ n * k = (k⁻¹ * x * k) ^ n := by
  have h := conj_pow (a := k⁻¹) (b := x) (i := n)
  rw [inv_inv] at h
  exact h.symm

theorem conj_mul_eq (k x y : G) : k⁻¹ * (x * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by
  group

variable [Finite G] {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ 2)} {σ υ g : G}
  (h : IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ 2)))
    (wreathModelHom S e (Original.z (2 ^ 2))) σ υ g)
include h

theorem orderOf_left_eq : orderOf σ = 4 := orderOf_left h

theorem orderOf_right_eq : orderOf υ = 4 := orderOf_right h

theorem left_pow_four : σ ^ 4 = 1 := by
  rw [← orderOf_left_eq h]
  exact pow_orderOf_eq_one σ

theorem right_pow_four : υ ^ 4 = 1 := by
  rw [← orderOf_right_eq h]
  exact pow_orderOf_eq_one υ

omit [Finite G] in
theorem commute_left_right' : Commute σ υ :=
  modelBase_commute S e _ _ h.left_mem h.right_mem

theorem coord_inj {p q : ZMod 4 × ZMod 4} (hpq : coord σ υ p = coord σ υ q) : p = q :=
  coord_injective (left_pow_four h) (right_pow_four h) (commute_left_right' h)
    (orderOf_left_eq h) (orderOf_right_eq h) (zpowers_left_inf_right h) hpq

theorem exists_coord_of_mem {u : G} (hu : u ∈ modelBase S e) :
    ∃ p : ZMod 4 × ZMod 4, u = coord σ υ p := by
  rw [← h.closure_eq] at hu
  exact exists_coord (left_pow_four h) (right_pow_four h) (commute_left_right' h) hu

omit [Finite G] in
theorem coord_mem_base (p : ZMod 4 × ZMod 4) : coord σ υ p ∈ modelBase S e :=
  coord_mem h.left_mem h.right_mem p

theorem swap_coord (p : ZMod 4 × ZMod 4) :
    (wreathModelHom S e (Original.z (2 ^ 2)))⁻¹ * coord σ υ p *
      wreathModelHom S e (Original.z (2 ^ 2)) = coord σ υ (swapMap p) := by
  set W := wreathModelHom S e (Original.z (2 ^ 2))
  have hW : W⁻¹ = W := swap_inv S e
  have hσW : W⁻¹ * σ * W = υ := h.conj_swap
  have hυW : W⁻¹ * υ * W = σ := by
    rw [← hσW, hW]
    calc W * (W * σ * W) * W = (W * W) * σ * (W * W) := by simp only [mul_assoc]
      _ = σ := by rw [show W * W = 1 by rw [← mul_inv_cancel W, hW], one_mul, mul_one]
  have hc := commute_left_right' h
  rw [coord, conj_mul_eq, conj_pow_eq, conj_pow_eq, hσW, hυW, ← swapMap_eq,
    ← coord_mul (left_pow_four h) (right_pow_four h) hc,
    ← coord_pow (left_pow_four h) (right_pow_four h) hc,
    ← coord_pow (left_pow_four h) (right_pow_four h) hc, coord_left, coord_right]

theorem cycle_coord (p : ZMod 4 × ZMod 4) :
    g⁻¹ * coord σ υ p * g = coord σ υ (cycleMap p) := by
  have hc := commute_left_right' h
  have ha : (wreathModelHom S e (Original.a (2 ^ 2)))⁻¹ = coord σ υ (3, 3) := by
    rw [← h.mul_eq, show ((3, 3) : ZMod 4 × ZMod 4) = -((1, 0) + (0, 1)) by decide,
      ← coord_inv (left_pow_four h) (right_pow_four h) hc,
      ← coord_mul (left_pow_four h) (right_pow_four h) hc, coord_left, coord_right]
  rw [coord, conj_mul_eq, conj_pow_eq, conj_pow_eq, h.conj_left, h.conj_right, ha,
    ← cycleMap_eq, ← coord_mul (left_pow_four h) (right_pow_four h) hc,
    ← coord_pow (left_pow_four h) (right_pow_four h) hc,
    ← coord_pow (left_pow_four h) (right_pow_four h) hc, coord_right]

theorem isConj_coord_iff (p q : ZMod 4 × ZMod 4) :
    IsConj (coord σ υ p) (coord σ υ q) ↔ orbitRel p q := by
  constructor
  · intro hpq
    obtain ⟨φ, hφ, hφpq⟩ := (isConj_iff_exists h le_rfl ⟨_, coord_mem_base h p⟩
      ⟨_, coord_mem_base h q⟩).mp hpq
    have hval := congrArg Subtype.val hφpq
    rcases mem_closure_swapAut_aut h hφ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (coord_inj h hval).symm
    · rw [h.aut_apply_coe, cycle_coord h] at hval
      exact Or.inr (Or.inl (coord_inj h hval).symm)
    · change (h.aut (h.aut ⟨_, coord_mem_base h p⟩) : G) = _ at hval
      rw [h.aut_apply_coe, h.aut_apply_coe, cycle_coord h, cycle_coord h] at hval
      exact Or.inr (Or.inr (Or.inl (coord_inj h hval).symm))
    · rw [swapAut_apply_coe, swap_coord h] at hval
      exact Or.inr (Or.inr (Or.inr (Or.inl (coord_inj h hval).symm)))
    · change (swapAut S e (h.aut ⟨_, coord_mem_base h p⟩) : G) = _ at hval
      rw [swapAut_apply_coe, h.aut_apply_coe, cycle_coord h, swap_coord h] at hval
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (coord_inj h hval).symm))))
    · change (swapAut S e (h.aut (h.aut ⟨_, coord_mem_base h p⟩)) : G) = _ at hval
      rw [swapAut_apply_coe, h.aut_apply_coe, h.aut_apply_coe, cycle_coord h, cycle_coord h,
        swap_coord h] at hval
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (coord_inj h hval).symm))))
  · intro hpq
    rw [isConj_iff]
    rcases hpq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, by rw [one_mul, inv_one, mul_one]⟩
    · exact ⟨g⁻¹, by rw [inv_inv, cycle_coord h]⟩
    · refine ⟨g⁻¹ * g⁻¹, ?_⟩
      calc g⁻¹ * g⁻¹ * coord σ υ p * (g⁻¹ * g⁻¹)⁻¹ = g⁻¹ * (g⁻¹ * coord σ υ p * g) * g := by
            simp only [mul_inv_rev, inv_inv, mul_assoc]
        _ = _ := by rw [cycle_coord h, cycle_coord h]
    · refine ⟨(wreathModelHom S e (Original.z (2 ^ 2)))⁻¹, ?_⟩
      rw [inv_inv, swap_coord h]
    · refine ⟨(wreathModelHom S e (Original.z (2 ^ 2)))⁻¹ * g⁻¹, ?_⟩
      calc (wreathModelHom S e (Original.z (2 ^ 2)))⁻¹ * g⁻¹ * coord σ υ p *
            ((wreathModelHom S e (Original.z (2 ^ 2)))⁻¹ * g⁻¹)⁻¹ =
          (wreathModelHom S e (Original.z (2 ^ 2)))⁻¹ * (g⁻¹ * coord σ υ p * g) *
            wreathModelHom S e (Original.z (2 ^ 2)) := by
            simp only [mul_inv_rev, inv_inv, mul_assoc]
        _ = _ := by rw [cycle_coord h, swap_coord h]
    · refine ⟨(wreathModelHom S e (Original.z (2 ^ 2)))⁻¹ * g⁻¹ * g⁻¹, ?_⟩
      calc (wreathModelHom S e (Original.z (2 ^ 2)))⁻¹ * g⁻¹ * g⁻¹ * coord σ υ p *
            ((wreathModelHom S e (Original.z (2 ^ 2)))⁻¹ * g⁻¹ * g⁻¹)⁻¹ =
          (wreathModelHom S e (Original.z (2 ^ 2)))⁻¹ * (g⁻¹ * (g⁻¹ * coord σ υ p * g) * g) *
            wreathModelHom S e (Original.z (2 ^ 2)) := by
            simp only [mul_inv_rev, inv_inv, mul_assoc]
        _ = _ := by rw [cycle_coord h, cycle_coord h, swap_coord h]

theorem mem_baseClasses_iff (i : Fin 5) (y : G) :
    y ∈ baseClasses (wreathModelHom S e (Original.a (2 ^ 2))) σ υ i ↔
      ∃ r ∈ coordClass i, y = coord σ υ r := by
  have hσ := left_pow_four h
  have hυ := right_pow_four h
  have hc := commute_left_right' h
  have hinv : ∀ r : ZMod 4 × ZMod 4, (coord σ υ r)⁻¹ = coord σ υ (-r) := coord_inv hσ hυ hc
  have hmul : ∀ r r' : ZMod 4 × ZMod 4, coord σ υ r * coord σ υ r' = coord σ υ (r + r') :=
    coord_mul hσ hυ hc
  have hpow : ∀ (r : ZMod 4 × ZMod 4) (k : ℕ), coord σ υ r ^ k = coord σ υ (k • r) :=
    coord_pow hσ hυ hc
  have hA : wreathModelHom S e (Original.a (2 ^ 2)) = coord σ υ (1, 1) := by
    rw [← h.mul_eq, show ((1, 1) : ZMod 4 × ZMod 4) = (1, 0) + (0, 1) by decide, ← hmul,
      coord_left, coord_right]
  have e1 : (1 : G) = coord σ υ (0, 0) := coord_zero.symm
  have e2 : wreathModelHom S e (Original.a (2 ^ 2)) ^ 2 = coord σ υ (2, 2) := by
    rw [hA, hpow]
    rfl
  have e3 : σ ^ 2 = coord σ υ (2, 0) := by
    rw [show ((2, 0) : ZMod 4 × ZMod 4) = 2 • (1, 0) by decide, ← hpow, coord_left]
  have e4 : υ ^ 2 = coord σ υ (0, 2) := by
    rw [show ((0, 2) : ZMod 4 × ZMod 4) = 2 • (0, 1) by decide, ← hpow, coord_right]
  have e5 : σ⁻¹ = coord σ υ (3, 0) := by
    rw [show ((3, 0) : ZMod 4 × ZMod 4) = -(1, 0) by decide, ← hinv, coord_left]
  have e6 : υ⁻¹ = coord σ υ (0, 3) := by
    rw [show ((0, 3) : ZMod 4 × ZMod 4) = -(0, 1) by decide, ← hinv, coord_right]
  have e7 : (wreathModelHom S e (Original.a (2 ^ 2)))⁻¹ = coord σ υ (3, 3) := by
    rw [hA, hinv]
    rfl
  have e8 : σ * υ⁻¹ = coord σ υ (1, 3) := by
    rw [e6, show ((1, 3) : ZMod 4 × ZMod 4) = (1, 0) + (0, 3) by decide, ← hmul, coord_left]
  have e9 : (σ * υ⁻¹)⁻¹ = coord σ υ (3, 1) := by
    rw [e8, hinv]
    rfl
  have e10 : σ * υ ^ 2 = coord σ υ (1, 2) := by
    rw [e4, show ((1, 2) : ZMod 4 × ZMod 4) = (1, 0) + (0, 2) by decide, ← hmul, coord_left]
  have e11 : σ ^ 2 * υ = coord σ υ (2, 1) := by
    rw [e3, show ((2, 1) : ZMod 4 × ZMod 4) = (2, 0) + (0, 1) by decide, ← hmul, coord_right]
  have e12 : σ ^ 3 * υ ^ 2 = coord σ υ (3, 2) := by
    rw [e4, show ((3, 2) : ZMod 4 × ZMod 4) = 3 • (1, 0) + (0, 2) by decide, ← hmul, ← hpow,
      coord_left]
  have e13 : σ ^ 2 * υ ^ 3 = coord σ υ (2, 3) := by
    rw [e3, show ((2, 3) : ZMod 4 × ZMod 4) = (2, 0) + 3 • (0, 1) by decide, ← hmul, ← hpow,
      coord_right]
  fin_cases i <;>
    simp only [baseClasses, coordClass, Set.mem_insert_iff, Set.mem_singleton_iff,
      List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp, exists_eq_left,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  · rw [e1]
  · rw [e2, e3, e4]
  · rw [hA, e5, e6]
  · rw [e7, coord_left, coord_right]
  · rw [e9, e8, e10, e11, e12, e13]

theorem mem_baseClasses_coord_iff (i : Fin 5) (p : ZMod 4 × ZMod 4) :
    coord σ υ p ∈ baseClasses (wreathModelHom S e (Original.a (2 ^ 2))) σ υ i ↔
      p ∈ coordClass i := by
  rw [mem_baseClasses_iff h]
  constructor
  · rintro ⟨r, hr, hpr⟩
    rwa [coord_inj h hpr]
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem baseClasses_subset (i : Fin 5) :
    baseClasses (wreathModelHom S e (Original.a (2 ^ 2))) σ υ i ⊆ modelBase S e := by
  intro y hy
  obtain ⟨r, -, rfl⟩ := (mem_baseClasses_iff h i y).mp hy
  exact coord_mem_base h r

theorem a_eq_coord : wreathModelHom S e (Original.a (2 ^ 2)) = coord σ υ (1, 1) := by
  rw [← h.mul_eq, show ((1, 1) : ZMod 4 × ZMod 4) = (1, 0) + (0, 1) by decide,
    ← coord_mul (left_pow_four h) (right_pow_four h) (commute_left_right' h), coord_left,
    coord_right]

theorem b_eq_coord : σ * υ⁻¹ = coord σ υ (1, 3) := by
  have hc := commute_left_right' h
  rw [show ((1, 3) : ZMod 4 × ZMod 4) = (1, 0) + -(0, 1) by decide,
    ← coord_mul (left_pow_four h) (right_pow_four h) hc,
    ← coord_inv (left_pow_four h) (right_pow_four h) hc, coord_left, coord_right]

theorem coord_inv' (r : ZMod 4 × ZMod 4) : (coord σ υ r)⁻¹ = coord σ υ (-r) :=
  coord_inv (left_pow_four h) (right_pow_four h) (commute_left_right' h) r

theorem coord_pow' (r : ZMod 4 × ZMod 4) (k : ℕ) : coord σ υ r ^ k = coord σ υ (k • r) :=
  coord_pow (left_pow_four h) (right_pow_four h) (commute_left_right' h) r k

theorem coord_zpow' (r : ZMod 4 × ZMod 4) (k : ℤ) : coord σ υ r ^ k = coord σ υ (k • r) :=
  coord_zpow (left_pow_four h) (right_pow_four h) (commute_left_right' h) r k

theorem existsUnique_mem_baseClasses {u : G} (hu : u ∈ modelBase S e) :
    ∃! i, u ∈ baseClasses (wreathModelHom S e (Original.a (2 ^ 2))) σ υ i := by
  obtain ⟨p, rfl⟩ := exists_coord_of_mem h hu
  obtain ⟨i, hi⟩ := coordClass_cover p
  exact ⟨i, (mem_baseClasses_coord_iff h i p).mpr hi,
    fun j hj => coordClass_disjoint p j i ((mem_baseClasses_coord_iff h j p).mp hj) hi⟩

theorem isConj_iff_mem_baseClasses {u v : G} (hu : u ∈ modelBase S e) (hv : v ∈ modelBase S e) :
    IsConj u v ↔ ∃ i, u ∈ baseClasses (wreathModelHom S e (Original.a (2 ^ 2))) σ υ i ∧
      v ∈ baseClasses (wreathModelHom S e (Original.a (2 ^ 2))) σ υ i := by
  obtain ⟨p, rfl⟩ := exists_coord_of_mem h hu
  obtain ⟨q, rfl⟩ := exists_coord_of_mem h hv
  rw [isConj_coord_iff h, orbitRel_iff]
  simp only [mem_baseClasses_coord_iff h]

end CFSG.Wreathed.OrderThirtyTwo
