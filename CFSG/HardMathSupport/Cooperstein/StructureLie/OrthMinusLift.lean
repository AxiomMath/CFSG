module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthMinusPlane
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthCentLift

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput CFSG.LieType.Steinberg.SpinFrame

variable {n : ℕ} {K : Type} [Field K]

@[expose] def PlaneId (G : Matrix (SM n) (SM n) K) : Prop :=
  ∀ x y, ((∃ u, x = pl n u) ∨ (∃ u, y = pl n u)) → G x y = if x = y then 1 else 0

variable {G X : Matrix (SM n) (SM n) K}

theorem iota_ne_pl (x : Fin (n - 1) ⊕ Fin (n - 1)) (u : Fin 2) : iota x ≠ pl n u := by
  rcases x with a | a <;> simp [iota, pl]

theorem PlaneId.col_plane (hG : PlaneId G) (x : Fin (n - 1) ⊕ Fin (n - 1)) (u : Fin 2) :
    G (iota x) (pl n u) = 0 := by
  rw [hG _ _ (Or.inr ⟨u, rfl⟩), if_neg (iota_ne_pl x u)]

theorem PlaneId.row_plane (hG : PlaneId G) (x : Fin (n - 1) ⊕ Fin (n - 1)) (u : Fin 2) :
    G (pl n u) (iota x) = 0 := by
  rw [hG _ _ (Or.inl ⟨u, rfl⟩), if_neg (iota_ne_pl x u).symm]

theorem planeId_mul (hG : PlaneId G) (hX : PlaneId X) : PlaneId (G * X) := by
  rintro x y (⟨u, rfl⟩ | ⟨u, rfl⟩)
  · rw [Matrix.mul_apply]
    simp only [hG (pl n u) _ (Or.inl ⟨u, rfl⟩), ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact hX _ _ (Or.inl ⟨u, rfl⟩)
  · rw [Matrix.mul_apply]
    simp only [hX _ (pl n u) (Or.inr ⟨u, rfl⟩), mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hG _ _ (Or.inr ⟨u, rfl⟩)

theorem restr_mul (hG : PlaneId G) (hX : PlaneId X) : restr (G * X) = restr G * restr X := by
  ext x y
  have h1 := hG.col_plane x
  have h2 := hX.row_plane y
  simp only [pl] at h1 h2
  rcases x with a | a <;> rcases y with a' | a' <;>
    simp [restr, Matrix.mul_apply, Fintype.sum_sum_type, iota_ne_pl, h1, h2, iota, pl] at h1 h2 ⊢ <;>
    simp [h1, h2]

theorem eq_one_of_restr_one (hG : PlaneId G) (h : restr G = 1) : G = 1 := by
  ext x y
  rcases x with a | a | u
  · rcases y with a' | a' | u'
    · simpa [restr, iota, Matrix.one_apply] using congrFun (congrFun h (.inl a)) (.inl a')
    · simpa [restr, iota, Matrix.one_apply] using congrFun (congrFun h (.inl a)) (.inr a')
    · exact (hG _ _ (Or.inr ⟨u', rfl⟩)).trans (by simp [Matrix.one_apply, pl])
  · rcases y with a' | a' | u'
    · simpa [restr, iota, Matrix.one_apply] using congrFun (congrFun h (.inr a)) (.inl a')
    · simpa [restr, iota, Matrix.one_apply] using congrFun (congrFun h (.inr a)) (.inr a')
    · exact (hG _ _ (Or.inr ⟨u', rfl⟩)).trans (by simp [Matrix.one_apply, pl])
  · exact (hG _ _ (Or.inl ⟨u, rfl⟩)).trans (by rw [Matrix.one_apply]; rfl)

section LongRoot

variable {b c : K}

theorem minusPos_ne_inr_inr (a : Fin (n - 1)) (r : Bool) (u : Fin 2) :
    minusPos n a r ≠ (Sum.inr (Sum.inr u) : SM n) := minusPos_ne_pl a r u

theorem inr_inr_ne_minusPos (a : Fin (n - 1)) (r : Bool) (u : Fin 2) :
    (Sum.inr (Sum.inr u) : SM n) ≠ minusPos n a r := (minusPos_ne_pl a r u).symm

theorem planeId_longRoot {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (r : K) :
    PlaneId (mat n ((minusFrame n b c).longRoot hij s t (Multiplicative.ofAdd r))) := by
  rintro x y (⟨u, rfl⟩ | ⟨u, rfl⟩) <;>
    simp [mat_longRoot_apply, minusPos_ne_inr_inr, inr_inr_ne_minusPos, pl] <;> rfl

theorem restr_longRoot {a b' : Fin (n - 1)} (hab : a ≠ b') (r : K) (z y : Fin (n - 1) ⊕ Fin (n - 1)) :
    restr (mat n ((minusFrame n b c).longRoot hab true true (Multiplicative.ofAdd r))) z y =
      (1 : Matrix (Fin (n - 1) ⊕ Fin (n - 1)) (Fin (n - 1) ⊕ Fin (n - 1)) K) z y +
        (if z = kap a true ∧ y = bar (kap b' true) then r else 0) -
          (if z = kap b' true ∧ y = bar (kap a true) then r else 0) := by
  simp only [restr, mat_longRoot_apply, Bool.not_true, ← iota_kap, iota_injective.eq_iff, bar_kap,
    Matrix.one_apply]
  have e1 : kap a true ≠ kap b' true := fun e => hab (kap_inj e).1
  have e2 : kap a false ≠ kap b' false := fun e => hab (kap_inj e).1
  by_cases h1 : z = kap a true <;> by_cases h2 : y = kap b' false <;>
    by_cases h3 : z = kap b' true <;> by_cases h4 : y = kap a false <;>
    simp [h1, h2, h3, h4, eq_comm, e1, e2, e1.symm, e2.symm]

end LongRoot

@[expose] def PT {m : ℕ} (A : Set (Fin m)) : Set (Fin m ⊕ Fin m) := {p | ∃ a ∈ A, p = kap a true}

theorem PT_disj {m : ℕ} (A : Set (Fin m)) : ∀ p ∈ PT A, bar p ∉ PT A := by
  rintro p ⟨a, ha, rfl⟩ ⟨b, hb, h⟩
  rw [bar_kap] at h
  obtain ⟨rfl, h2⟩ := kap_inj h
  simp at h2

theorem kap_true_mem_PT {m : ℕ} {A : Set (Fin m)} {a : Fin m} (ha : a ∈ A) : kap a true ∈ PT A :=
  ⟨a, ha, rfl⟩

section Lift

variable {b c : K}

theorem lift_minus [CharP K 2] [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (R : Subgroup (spinGroup (quadMinus n K b c))) (A : Set (Fin (n - 1)))
    (hroot : ∀ a ∈ A, ∀ b' ∈ A, ∀ hab : a ≠ b', ∀ r : K,
      (minusFrame n b c).longRoot hab true true (Multiplicative.ofAdd r) ∈ R) :
    ∀ (N : ℕ) (k : spinGroup (quadMinus n K b c)), PlaneId (mat n k) →
      Shape (restr (mat n k)) (PT A) → cntBlock (restr (mat n k)) (PT A) = N → k ∈ R := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k hP hS hN
    have hd := PT_disj A
    by_cases hN0 : N = 0
    · subst hN0
      have hz : ∀ p ∈ PT A, ∀ q ∈ PT A, restr (mat n k) p (bar q) = 0 := by
        intro p hp q hq
        by_contra hne
        unfold cntBlock at hN
        have : (p, q) ∈ Finset.univ.filter fun pq : (Fin (n - 1) ⊕ Fin (n - 1)) × (Fin (n - 1) ⊕ Fin (n - 1)) =>
            pq.1 ∈ PT A ∧ pq.2 ∈ PT A ∧ restr (mat n k) pq.1 (bar pq.2) ≠ 0 := by
          simp [hp, hq, hne]
        rw [Finset.card_eq_zero] at hN
        simp [hN] at this
      have h1 : restr (mat n k) = 1 := by
        ext x y
        by_cases hxy : x ∈ PT A ∧ bar y ∈ PT A
        · have := hz x hxy.1 (bar y) hxy.2
          rw [bar_bar] at this
          rw [this]
          have : x ≠ y := fun e => hd x hxy.1 (by rw [e]; exact hxy.2)
          simp [Matrix.one_apply, this]
        · rw [hS.delta x y hxy]
          simp [Matrix.one_apply]
      have h2 : mat n k = 1 := eq_one_of_restr_one hP h1
      have hk : k = 1 := mat_injective hirr (h2.trans (mat_one n).symm)
      rw [hk]
      exact R.one_mem
    · have hpos : 0 < cntBlock (restr (mat n k)) (PT A) := by omega
      unfold cntBlock at hpos
      obtain ⟨⟨p, q⟩, hm⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      obtain ⟨hp, hq, hc⟩ := hm
      obtain ⟨a, ha, rfl⟩ := hp
      obtain ⟨b', hb, rfl⟩ := hq
      have hab : a ≠ b' := by
        rintro rfl
        exact hc (hS.diag _ (kap_true_mem_PT ha))
      have hpP : kap a true ∈ PT A := kap_true_mem_PT ha
      have hqP : kap b' true ∈ PT A := kap_true_mem_PT hb
      have hpq : kap a true ≠ kap b' true := fun e => hab (kap_inj e).1
      set c' := -restr (mat n k) (kap a true) (bar (kap b' true)) with hc'
      have hx : (minusFrame n b c).longRoot hab true true (Multiplicative.ofAdd c') ∈ R :=
        hroot a ha b' hb hab c'
      have hX := restr_longRoot (b := b) (c := c) hab c'
      obtain ⟨hS', hlt⟩ := peel_shape hd hS hpP hqP hpq hc _ hX
      have hPx := planeId_longRoot (b := b) (c := c) hab true true c'
      rw [← restr_mul hP hPx, ← mat_mul] at hS' hlt
      have key := ih _ (by omega) (k * (minusFrame n b c).longRoot hab true true (Multiplicative.ofAdd c'))
        (by rw [mat_mul]; exact planeId_mul hP hPx) hS' rfl
      have hk : k = (k * (minusFrame n b c).longRoot hab true true (Multiplicative.ofAdd c')) *
          ((minusFrame n b c).longRoot hab true true (Multiplicative.ofAdd c'))⁻¹ :=
        (mul_inv_cancel_right _ _).symm
      rw [hk]
      exact R.mul_mem key (R.inv_mem hx)

end Lift

end CFSG.HardMathSupport.Cooperstein.StructureLie
