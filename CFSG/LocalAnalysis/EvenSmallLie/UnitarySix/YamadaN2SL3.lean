module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Model

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped commutatorElement

theorem st3_mul_st3 {a b : Fin 3} (hab : a ≠ b) (c d : F4) :
    st3 a b c * st3 a b d = st3 a b (c + d) :=
  stT_add _ hab c d

theorem st3_comm {a b d : Fin 3} (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) (c c' : F4) :
    ⁅st3 a b c, st3 b d c'⁆ = st3 a d (c * c') := by
  rw [st3, st3, stT_comm _ hab hbd (fun h => had (h.2.symm)), ite_eq_left rfl]

theorem comm_mem_left {G : Type*} [Group G] {N : Subgroup G} [hN : N.Normal] {x : G}
    (hx : x ∈ N) (y : G) : ⁅x, y⁆ ∈ N := by
  rw [commutatorElement_def]
  have h1 := hN.conj_mem _ (inv_mem hx) y
  have h2 := mul_mem hx h1
  simpa [mul_assoc] using h2

theorem comm_mem_right {G : Type*} [Group G] {N : Subgroup G} [hN : N.Normal] {x : G}
    (hx : x ∈ N) (y : G) : ⁅y, x⁆ ∈ N := by
  rw [commutatorElement_def]
  exact mul_mem (hN.conj_mem x hx y) (inv_mem hx)

theorem f4_cases (c : F4) : c = 0 ∨ c = 1 ∨ c = F4.ω ∨ c = 1 + F4.ω := by
  rcases c with ⟨k⟩
  fin_cases k
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (f4_ext rfl)))

theorem st3_mem_of_gen {N : Subgroup SL3} {a b : Fin 3} (hab : a ≠ b)
    (h1 : st3 a b 1 ∈ N) (hω : st3 a b F4.ω ∈ N) (c : F4) : st3 a b c ∈ N := by
  rcases f4_cases c with rfl | rfl | rfl | rfl
  · rw [st3, stT_zero]; exact one_mem _
  · exact h1
  · exact hω
  · rw [← st3_mul_st3 hab]; exact mul_mem h1 hω

theorem eq_top_of_st3 {N : Subgroup SL3} (h : ∀ a b : Fin 3, a ≠ b → ∀ c, st3 a b c ∈ N) :
    N = ⊤ := by
  rw [eq_top_iff, ← closure_stT (F := F4) (m := 2) (by norm_num), Subgroup.closure_le]
  rintro _ ⟨⟨a, b, c⟩, rfl⟩
  by_cases hab : a = b
  · subst hab
    change stT _ a a c ∈ N
    rw [stT_diag]; exact one_mem _
  · exact h a b hab c

theorem eq_top_of_E {N : Subgroup SL3} [N.Normal] (h01 : ∀ c, st3 0 1 c ∈ N)
    (h02 : ∀ c, st3 0 2 c ∈ N) : N = ⊤ := by
  have h12 : ∀ c, st3 1 2 c ∈ N := fun c => by
    have := comm_mem_right (h02 1) (st3 1 0 c)
    rwa [st3_comm (by decide) (by decide) (by decide), mul_one] at this
  have h21 : ∀ c, st3 2 1 c ∈ N := fun c => by
    have := comm_mem_right (h01 1) (st3 2 0 c)
    rwa [st3_comm (by decide) (by decide) (by decide), mul_one] at this
  have h10 : ∀ c, st3 1 0 c ∈ N := fun c => by
    have := comm_mem_left (h12 c) (st3 2 0 1)
    rwa [st3_comm (by decide) (by decide) (by decide), mul_one] at this
  have h20 : ∀ c, st3 2 0 c ∈ N := fun c => by
    have := comm_mem_left (h21 c) (st3 1 0 1)
    rwa [st3_comm (by decide) (by decide) (by decide), mul_one] at this
  refine eq_top_of_st3 fun a b hab c => ?_
  fin_cases a <;> fin_cases b
  all_goals first | exact absurd rfl hab | skip
  · exact h01 c
  · exact h02 c
  · exact h10 c
  · exact h12 c
  · exact h20 c
  · exact h21 c

theorem eq_top_of_ET {N : Subgroup SL3} [N.Normal] (h10 : ∀ c, st3 1 0 c ∈ N)
    (h20 : ∀ c, st3 2 0 c ∈ N) : N = ⊤ := by
  have h12 : ∀ c, st3 1 2 c ∈ N := fun c => by
    have := comm_mem_left (h10 c) (st3 0 2 1)
    rwa [st3_comm (by decide) (by decide) (by decide), mul_one] at this
  have h21 : ∀ c, st3 2 1 c ∈ N := fun c => by
    have := comm_mem_left (h20 c) (st3 0 1 1)
    rwa [st3_comm (by decide) (by decide) (by decide), mul_one] at this
  have h01 : ∀ c, st3 0 1 c ∈ N := fun c => by
    have := comm_mem_right (h21 1) (st3 0 2 c)
    rwa [st3_comm (by decide) (by decide) (by decide), mul_one] at this
  have h02 : ∀ c, st3 0 2 c ∈ N := fun c => by
    have := comm_mem_right (h12 1) (st3 0 1 c)
    rwa [st3_comm (by decide) (by decide) (by decide), mul_one] at this
  exact eq_top_of_E h01 h02

theorem f4_factA : ∀ x y : F4, x * frobF4 x = 1 → y * frobF4 x = 0 → y = 0 := by
  intro x y h1 h2
  rcases x with ⟨i⟩; rcases y with ⟨j⟩
  have c1 := congrArg F4.code h1
  have c2 := congrArg F4.code h2
  revert c1 c2
  fin_cases i <;> fin_cases j <;> intro c1 c2 <;>
    first | rfl | exact absurd c1 (by decide) | exact absurd c2 (by decide)

theorem f4_factB : ∀ x y : F4, x * frobF4 y = 1 → y * frobF4 y = 1 → x = y := by
  intro x y h1 h2
  rcases x with ⟨i⟩; rcases y with ⟨j⟩
  have c1 := congrArg F4.code h1
  have c2 := congrArg F4.code h2
  revert c1 c2
  fin_cases i <;> fin_cases j <;> intro c1 c2 <;>
    first | rfl | exact absurd c1 (by decide)

@[expose] noncomputable def omegaI : SL3 :=
  ⟨Matrix.diagonal fun _ => F4.ω, by rw [det_diagonal, Fin.prod_univ_three]; exact f4_ext rfl⟩

theorem omegaI_mem_center : omegaI ∈ Subgroup.center SL3 := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change (g : M3) * Matrix.diagonal (fun _ => F4.ω) = Matrix.diagonal (fun _ => F4.ω) * (g : M3)
  rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, mul_one, Matrix.smul_mul, one_mul]

theorem zpowers_omegaI_le_center : Subgroup.zpowers omegaI ≤ Subgroup.center SL3 :=
  Subgroup.zpowers_le.mpr omegaI_mem_center

theorem coe_omegaI_pow (k : ℕ) :
    ((omegaI ^ k : SL3) : M3) = Matrix.diagonal fun _ => F4.ω ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, coe_SL3_mul, ih]
    change Matrix.diagonal _ * Matrix.diagonal _ = _
    rw [diagonal_mul_diagonal, pow_succ]

theorem mem_zpowers_of_scalar (a : SL3) (c : F4) (h : (a : M3) = Matrix.diagonal fun _ => c) :
    a ∈ Subgroup.zpowers omegaI := by
  have hdet : c * c * c = 1 := by
    have := a.2
    rw [h, det_diagonal, Fin.prod_univ_three] at this
    exact this
  rcases f4_cases c with rfl | rfl | rfl | rfl
  · exact absurd (congrArg F4.code hdet) (by decide)
  · have : a = omegaI ^ 0 := Subtype.ext (by rw [h, coe_omegaI_pow]; rfl)
    rw [this]; exact Subgroup.npow_mem_zpowers _ _
  · have : a = omegaI ^ 1 := Subtype.ext (by rw [h, coe_omegaI_pow]; rfl)
    rw [this]; exact Subgroup.npow_mem_zpowers _ _
  · have : a = omegaI ^ 2 := Subtype.ext (by
      rw [h, coe_omegaI_pow]; congr 1)
    rw [this]; exact Subgroup.npow_mem_zpowers _ _

theorem kr_entry {A B C D : M3} (h : kr A B = kr C D) (i j k l : Fin 3) :
    A i k * B j l = C i k * D j l := by
  have := congrFun (congrFun h (finProdFinEquiv (i, j))) (finProdFinEquiv (k, l))
  rwa [kr_apply, kr_apply] at this

theorem conjP_reF9_injective {A B : Matrix (Fin 9) (Fin 9) F4}
    (h : conjP (reF9 A) = conjP (reF9 B)) : A = B :=
  reF9_injective (conjP_injective h)

theorem eq_diagonal_of {a : M3} (hoff : ∀ i k, i ≠ k → a i k = 0) (hdiag : ∀ i, a i i = a 0 0) :
    a = Matrix.diagonal fun _ => a 0 0 := by
  ext i k
  by_cases hik : i = k
  · subst hik; rw [diagonal_apply_eq, hdiag]
  · rw [diagonal_apply_ne _ hik, hoff i k hik]

theorem mem_zpowers_of_rhoA_eq_one {a : SL3} (h : rhoA a = 1) :
    a ∈ Subgroup.zpowers omegaI := by
  have hk : kact a = kact 1 := by rw [kact_eq_rhoN, h, rhoN_one, map_one]
  rw [kact_eq, kact_eq, coe_SL3_one, map_one] at hk
  have hkr := conjP_reF9_injective hk
  rw [kr_one] at hkr
  have e := kr_entry (hkr.trans kr_one.symm)
  have h1 : ∀ i, (a : M3) i i * frobF4 ((a : M3) i i) = 1 := fun i => by
    have := e i i i i; rw [frob3_apply, one_apply_eq] at this
    exact this.trans (one_mul 1)
  have h2 : ∀ i k, i ≠ k → (a : M3) i k * frobF4 ((a : M3) k k) = 0 := fun i k hik => by
    have := e i k k k; rwa [frob3_apply, one_apply_ne hik, zero_mul] at this
  have h3 : ∀ i, (a : M3) 0 0 * frobF4 ((a : M3) i i) = 1 := fun i => by
    have := e 0 i 0 i; rw [frob3_apply, one_apply_eq, one_apply_eq] at this
    exact this.trans (one_mul 1)
  exact mem_zpowers_of_scalar a _ (eq_diagonal_of
    (fun i k hik => f4_factA _ _ (h1 k) (h2 i k hik)) fun i => (f4_factB _ _ (h3 i) (h1 i)).symm)

theorem mem_zpowers_of_lft_eq_rgt {a b : SL3} (h : lft a = rgt b) :
    a ∈ Subgroup.zpowers omegaI := by
  rw [lft_apply, rgt_apply] at h
  have e := kr_entry (conjP_reF9_injective h)
  set c := (((b⁻¹ : SL3) : M3))ᵀ
  have hoff : ∀ i k, i ≠ k → (a : M3) i k = 0 := fun i k hik => by
    have := e i 0 k 0; rwa [one_apply_eq, mul_one, one_apply_ne hik, zero_mul] at this
  have hdiag : ∀ i, (a : M3) i i = c 0 0 := fun i => by
    have := e i 0 i 0; rwa [one_apply_eq, mul_one, one_apply_eq, one_mul] at this
  exact mem_zpowers_of_scalar a _ (eq_diagonal_of hoff fun i => by rw [hdiag i, hdiag 0])

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
