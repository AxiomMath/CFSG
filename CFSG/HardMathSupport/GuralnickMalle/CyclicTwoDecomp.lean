module

public import CFSG.GroupTheory.SteinbergCBHHBNilpotentCentralizer

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module

variable {K : Type*} [Field K]

theorem sub_one_comp_sub_one_eq_zero {V : Type*} [AddCommGroup V] [Module K V]
    [CharP K 2] (T : V →ₗ[K] V) (hT : T.comp T = 1) :
    (T - 1).comp (T - 1) = 0 := by
  ext v
  change T (T v - v) - (T v - v) = 0
  have h := congrArg (fun f : V →ₗ[K] V => f v) hT
  simp only [LinearMap.comp_apply, Module.End.one_apply] at h
  have hv : v + v = 0 := by
    have h2 : (2 : K) • v = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    rwa [two_smul] at h2
  have htv : T v + T v = 0 := by
    have h2 : (2 : K) • (T v) = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    rwa [two_smul] at h2
  rw [map_sub, h, sub_eq_add_neg, sub_eq_add_neg]
  have hneg : ∀ x : V, -x = x := by
    intro x
    rw [← neg_one_smul K x, CharTwo.neg_eq (1 : K), one_smul]
  simp only [sub_eq_add_neg, hneg]
  have hcomm : v + T v + (T v + v) = v + v + (T v + T v) := by abel
  rw [hcomm, hv, htv, add_zero]

noncomputable def consBlockEquiv (a b : ℕ) :
    ((Fin 2 → K) × ((Fin a → K) × (Fin b → K × K))) ≃ₗ[K]
      ((Fin a → K) × (Fin (b + 1) → K × K)) :=
  LinearEquiv.trans
    (LinearEquiv.trans
      (LinearEquiv.trans
        ((LinearEquiv.prodAssoc K (Fin 2 → K) (Fin a → K) (Fin b → K × K)).symm)
        (LinearEquiv.prodCongr (LinearEquiv.prodComm K (Fin 2 → K) (Fin a → K))
          (LinearEquiv.refl K (Fin b → K × K))))
      (LinearEquiv.prodAssoc K (Fin a → K) (Fin 2 → K) (Fin b → K × K)))
    (LinearEquiv.trans
      (LinearEquiv.prodCongr (LinearEquiv.refl K (Fin a → K))
        (LinearEquiv.prodCongr (LinearEquiv.finTwoArrow (R := K) (M := K))
          (LinearEquiv.refl K (Fin b → K × K))))
      (LinearEquiv.prodCongr (LinearEquiv.refl K (Fin a → K))
        (Fin.consLinearEquiv K (fun _ : Fin (b + 1) => K × K))))

@[simp]
theorem consBlockEquiv_apply (a b : ℕ) (c : Fin 2 → K) (x : Fin a → K)
    (y : Fin b → K × K) :
    consBlockEquiv (K := K) a b (c, (x, y)) = (x, Fin.cons (c 0, c 1) y) := by
  rfl

theorem consBlockEquiv_intertwines (a b : ℕ) (c : Fin 2 → K) (x : Fin a → K)
    (y : Fin b → K × K) :
    consBlockEquiv (K := K) a b
        (CFSG.GroupTheory.HallHigmanB.shiftOp 2 c, (0, fun j => (0, (y j).1))) =
      (0, fun i => (0, ((consBlockEquiv (K := K) a b (c, (x, y))).2 i).1)) := by
  rw [consBlockEquiv_apply, consBlockEquiv_apply]
  have h0 : CFSG.GroupTheory.HallHigmanB.shiftOp (K := K) 2 c 0 = 0 := by
    rw [CFSG.GroupTheory.HallHigmanB.shiftOp_apply]
    simp
  have h1 : CFSG.GroupTheory.HallHigmanB.shiftOp (K := K) 2 c 1 = c 0 := by
    rw [CFSG.GroupTheory.HallHigmanB.shiftOp_apply]
    simp
  rw [h0, h1]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i <;> simp

theorem exists_decomposition_sq_zero_aux (d : ℕ) :
    ∀ (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = d → ∀ N : V →ₗ[K] V, N.comp N = 0 →
      ∃ (a b : ℕ) (e : V ≃ₗ[K] ((Fin a → K) × (Fin b → K × K))),
        ∀ v, e (N v) = (0, fun i => (0, ((e v).2 i).1)) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro V _ _ _ hdim N hN
    by_cases hN0 : N = 0
    · refine ⟨finrank K V, 0, ?_, ?_⟩
      · exact (Module.finBasis K V).equivFun.trans
          (LinearEquiv.prodUnique (R := K) (M := Fin (finrank K V) → K)
            (M₂ := Fin 0 → K × K)).symm
      · intro v
        have hNv : N v = 0 := by rw [hN0, LinearMap.zero_apply]
        rw [hNv, map_zero]
        refine Prod.ext rfl ?_
        funext i
        exact i.elim0
    · have hN2 : N ^ 2 = 0 := by
        rwa [pow_two, Module.End.mul_eq_comp]
      have hN1 : N ^ (2 - 1) ≠ 0 := by simpa using hN0
      obtain ⟨W', N', Φ, hN'2, hΦ⟩ :=
        CFSG.GroupTheory.HallHigmanB.exists_equiv_shift_prod (K := K) N (r := 2)
          (by norm_num) hN2 hN1
      have hN'comp : N'.comp N' = 0 := by
        rwa [pow_two, Module.End.mul_eq_comp] at hN'2
      have hdimΦ : finrank K V = finrank K ((Fin 2 → K) × W') :=
        LinearEquiv.finrank_eq Φ
      have hdimprod : finrank K ((Fin 2 → K) × W') = 2 + finrank K W' := by
        rw [Module.finrank_prod, Module.finrank_fin_fun]
      have hW'lt : finrank K W' < d := by
        have h := hdim.symm.trans (hdimΦ.trans hdimprod)
        omega
      obtain ⟨a', b', e', he'⟩ := ih (finrank K W') hW'lt W' rfl N' hN'comp
      refine ⟨a', b' + 1, ?_, ?_⟩
      · exact (Φ.trans ((LinearEquiv.refl K (Fin 2 → K)).prodCongr e')).trans
          (consBlockEquiv (K := K) a' b')
      · intro v
        have hΦv : Φ (N v) =
            (CFSG.GroupTheory.HallHigmanB.shiftOp 2 (Φ v).1, N' (Φ v).2) := by
          have h := congrArg (fun f : V →ₗ[K] ((Fin 2 → K) × W') => f v) hΦ
          simpa [LinearMap.comp_apply, LinearMap.prodMap_apply] using h
        have hew : e' (N' (Φ v).2) =
            (0, fun j => (0, ((e' (Φ v).2).2 j).1)) := he' (Φ v).2
        simpa [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, hΦv, hew] using
          consBlockEquiv_intertwines (K := K) a' b' (Φ v).1
            ((e' (Φ v).2).1) ((e' (Φ v).2).2)

theorem exists_decomposition_sq_zero {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : V →ₗ[K] V) (hN : N.comp N = 0) :
    ∃ (a b : ℕ) (e : V ≃ₗ[K] ((Fin a → K) × (Fin b → K × K))),
      ∀ v, e (N v) = (0, fun i => (0, ((e v).2 i).1)) :=
  exists_decomposition_sq_zero_aux (K := K) (finrank K V) V rfl N hN

theorem exists_decomposition_involution {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [CharP K 2] (T : V →ₗ[K] V) (hT : T.comp T = 1) :
    ∃ (a b : ℕ) (e : V ≃ₗ[K] ((Fin a → K) × (Fin b → K × K))),
      ∀ v, e (T v) =
        ((e v).1, fun i => (((e v).2 i).1, ((e v).2 i).1 + ((e v).2 i).2)) := by
  obtain ⟨a, b, e, he⟩ :=
    exists_decomposition_sq_zero (K := K) (T - 1)
      (sub_one_comp_sub_one_eq_zero (K := K) T hT)
  refine ⟨a, b, e, ?_⟩
  intro v
  have hTv : T v = v + (T - 1) v := by
    have h : T = 1 + (T - 1) := by abel
    have := congrArg (fun f : V →ₗ[K] V => f v) h
    simpa using this
  rw [hTv, map_add, he v]
  refine Prod.ext ?_ ?_
  · simp
  · funext i
    refine Prod.ext ?_ ?_
    · simp
    · simp [add_comm]

noncomputable def stdN (a b : ℕ) :
    ((Fin a → K) × (Fin b → K × K)) →ₗ[K] ((Fin a → K) × (Fin b → K × K)) :=
  LinearMap.prod (0 : ((Fin a → K) × (Fin b → K × K)) →ₗ[K] (Fin a → K))
    (LinearMap.pi fun i : Fin b =>
      ((0 : (K × K) →ₗ[K] K).prod (LinearMap.fst K K K)).comp
        ((LinearMap.proj i).comp (LinearMap.snd _ _ _)))

@[simp]
theorem stdN_apply (a b : ℕ) (x : Fin a → K) (y : Fin b → K × K) :
    stdN (K := K) a b (x, y) = (0, fun i => (0, (y i).1)) := by
  refine Prod.ext rfl ?_
  funext i
  simp [stdN]

theorem one_add_stdN_apply (a b : ℕ) (x : Fin a → K) (y : Fin b → K × K) :
    ((1 + stdN (K := K) a b) (x, y)) =
      (x, fun i => ((y i).1, (y i).1 + (y i).2)) := by
  rw [LinearMap.add_apply, Module.End.one_apply, stdN_apply]
  refine Prod.ext ?_ ?_
  · simp
  · funext i
    refine Prod.ext ?_ ?_
    · simp
    · simp [add_comm]

def fixedSubmodule (a b : ℕ) : Submodule K ((Fin a → K) × (Fin b → K × K)) where
  carrier := {z | ∀ i : Fin b, (z.2 i).1 = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i; simp [hx i, hy i]
  smul_mem' := by intro c x hx i; simp [hx i]

theorem ker_stdN (a b : ℕ) :
    LinearMap.ker (stdN (K := K) a b) = fixedSubmodule (K := K) a b := by
  ext z
  rcases z with ⟨x, y⟩
  constructor
  · intro hz i
    have h := congrArg (fun w => (w.2 i).2) hz
    rw [stdN_apply] at h
    simpa using h
  · intro hz
    rw [LinearMap.mem_ker]
    rw [stdN_apply]
    refine Prod.ext rfl ?_
    funext i
    simpa using hz i

noncomputable def fixedSubmoduleEquiv (a b : ℕ) :
    fixedSubmodule (K := K) a b ≃ₗ[K] ((Fin a → K) × (Fin b → K)) where
  toFun z := (z.1.1, fun i => (z.1.2 i).2)
  invFun p := ⟨(p.1, fun i => (0, p.2 i)), by intro i; rfl⟩
  map_add' := by
    intro x y
    ext i <;> simp
  map_smul' := by
    intro c x
    ext i <;> simp
  left_inv := by
    intro z
    refine Subtype.ext ?_
    refine Prod.ext rfl ?_
    funext i
    refine Prod.ext ?_ rfl
    exact (z.2 i).symm
  right_inv := by
    intro p
    ext i <;> simp

theorem finrank_fixedSubmodule (a b : ℕ) :
    finrank K (fixedSubmodule (K := K) a b) = a + b := by
  rw [LinearEquiv.finrank_eq (fixedSubmoduleEquiv (K := K) a b)]
  simp [Module.finrank_prod, Module.finrank_fin_fun]

theorem finrank_fixed_eq {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : V →ₗ[K] V) {a b : ℕ} (e : V ≃ₗ[K] ((Fin a → K) × (Fin b → K × K)))
    (he : ∀ v, e (T v) =
      ((e v).1, fun i => (((e v).2 i).1, ((e v).2 i).1 + ((e v).2 i).2))) :
    finrank K (LinearMap.ker (T - 1)) = a + b := by
  have he' : ∀ v, e (T v) = (1 + stdN (K := K) a b) (e v) := by
    intro v
    rw [he v, one_add_stdN_apply]
  have hmap : (LinearMap.ker (T - 1)).map e.toLinearMap =
      fixedSubmodule (K := K) a b := by
    rw [← ker_stdN]
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      change stdN (K := K) a b (e v) = 0
      have hTv : T v = v := by
        have hv' : (T - 1) v = 0 := (LinearMap.mem_ker.mp hv)
        exact sub_eq_zero.mp hv'
      have h2 : (1 + stdN (K := K) a b) (e v) = e v := by
        rw [← he' v, hTv]
      have h3 : e v + stdN (K := K) a b (e v) = e v := by
        simpa [LinearMap.add_apply, Module.End.one_apply] using h2
      have h4 : stdN (K := K) a b (e v) = 0 := by
        have h5 : e v + stdN (K := K) a b (e v) =
            e v + (0 : (Fin a → K) × (Fin b → K × K)) := by
          simpa using h3.symm
        exact add_left_cancel h5
      exact h4
    · intro hz
      refine ⟨e.symm z, ?_, by simp⟩
      change (T - 1) (e.symm z) = 0
      have hz' : stdN (K := K) a b z = 0 := (LinearMap.mem_ker.mp hz)
      have h2 : (1 + stdN (K := K) a b) z = z := by
        rw [LinearMap.add_apply, Module.End.one_apply, hz', add_zero]
      have h1 : e (T (e.symm z)) = (1 + stdN (K := K) a b) z := by
        rw [he' (e.symm z), LinearEquiv.apply_symm_apply]
      have hT : T (e.symm z) = e.symm z := by
        apply e.injective
        rw [h1, h2, LinearEquiv.apply_symm_apply]
      exact sub_eq_zero.mpr hT
  calc
    finrank K (LinearMap.ker (T - 1))
        = finrank K ((LinearMap.ker (T - 1)).map e.toLinearMap) :=
          (LinearEquiv.finrank_map_eq e (LinearMap.ker (T - 1))).symm
    _ = finrank K (fixedSubmodule (K := K) a b) := by rw [hmap]
    _ = a + b := finrank_fixedSubmodule a b

theorem finrank_eq_add_two_mul {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {a b : ℕ}
    (e : V ≃ₗ[K] ((Fin a → K) × (Fin b → K × K))) :
    finrank K V = a + 2 * b := by
  rw [LinearEquiv.finrank_eq e, Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_pi_fintype]
  simp [Module.finrank_prod, Module.finrank_fin_fun, Finset.sum_const, Nat.mul_comm]
