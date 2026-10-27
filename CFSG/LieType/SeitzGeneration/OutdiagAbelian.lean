module

public import CFSG.LieType.SeitzGeneration.OutdiagCube
public import CFSG.RankThree.PartOne.CTP.SeitzDiag
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def planeFix (x y : GL (Fin n) F) : Set (SpecialLinearGroup (Fin n) F) :=
  FixSL (x : Matrix (Fin n) (Fin n) F) ∪ FixSL (y : Matrix (Fin n) (Fin n) F) ∪
    FixSL ((x * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ∪
    FixSL ((x * y ^ 2 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)

theorem commute_scalarGL (c : Fˣ) (g : GL (Fin n) F) :
    Commute (Matrix.GeneralLinearGroup.scalar (Fin n) c) g := by
  show _ * _ = _ * _
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _

theorem coe_scalarGL_mul (c : Fˣ) (g : GL (Fin n) F) :
    ((Matrix.GeneralLinearGroup.scalar (Fin n) c * g : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = (c : F) • (g : Matrix (Fin n) (Fin n) F) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]

theorem intertwine_pow_left {P g D : Matrix (Fin n) (Fin n) F} (h : P * g = D * P) (k : ℕ) :
    P * g ^ k = D ^ k * P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', ← Matrix.mul_assoc, h, Matrix.mul_assoc, ih,
      Matrix.mul_assoc]

theorem intertwine_mul_left {P g g' D D' : Matrix (Fin n) (Fin n) F} (h : P * g = D * P)
    (h' : P * g' = D' * P) : P * (g * g') = (D * D') * P := by
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, h', Matrix.mul_assoc]

section Abelian

theorem closure_planeFix_abelian [Finite F] (hF3 : 3 ∣ Nat.card F - 1)
    (hζ : ∃ ζ : F, IsPrimitiveRoot ζ 3) {x y : GL (Fin 3) F} (hxy : x * y = y * x) {α β : F}
    (hα : α ≠ 0) (hβ : β ≠ 0) (hx3 : ((x ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = α • 1)
    (hy3 : ((y ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = β • 1)
    (hind : ∀ a b : ℕ,
      (∃ c : F, ((x ^ a * y ^ b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = c • 1) →
        3 ∣ a ∧ 3 ∣ b) :
    Subgroup.closure (planeFix x y) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Commute x y := hxy
  obtain ⟨a, b, s, hs0, hab, hs3⟩ := exists_cube_line hF3 (w := 1) (fun g => Commute.one_left g)
    (one_pow 3) (by rw [one_mul]; exact hxy.symm) hα hβ hx3 hy3
  set g₀ : GL (Fin 3) F := x ^ a * y ^ b with hg₀
  set X₁ : Matrix (Fin 3) (Fin 3) F := s⁻¹ • (g₀ : Matrix (Fin 3) (Fin 3) F) with hX₁
  have hX₁3 : X₁ ^ 3 = 1 := by
    rw [hX₁, smul_pow, ← Units.val_pow_eq_pow_val, hs3, smul_smul, ← mul_pow, inv_mul_cancel₀ hs0,
      one_pow, one_smul]
  have hX₁s : ∀ c : F, X₁ ≠ c • (1 : Matrix (Fin 3) (Fin 3) F) := by
    intro c hcX
    have h1 : ((x ^ a * y ^ b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (s * c) • 1 := by
      have : (g₀ : Matrix (Fin 3) (Fin 3) F) = s • X₁ := by
        rw [hX₁, smul_smul, mul_inv_cancel₀ hs0, one_smul]
      rw [← hg₀, this, hcX, smul_smul]
    have := hind a b ⟨_, h1⟩
    omega
  have hcomm : ∀ h : GL (Fin 3) F, Commute x h → Commute y h →
      X₁ * (h : Matrix (Fin 3) (Fin 3) F) = (h : Matrix (Fin 3) (Fin 3) F) * X₁ := by
    intro h hxh hyh
    have h1 : Commute g₀ h := ((hxh.pow_left a).mul_left (hyh.pow_left b))
    have h2 : (g₀ : Matrix (Fin 3) (Fin 3) F) * h = h * g₀ := congrArg Units.val h1.eq
    rw [hX₁, Matrix.smul_mul, Matrix.mul_smul, h2]
  have hcube : ∀ (h : GL (Fin 3) F) (lam : F), Commute x h → Commute y h →
      ((h ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = lam • 1 → ∃ μ : F, μ ^ 3 = lam := by
    intro h lam hxh hyh hh3
    refine exists_cube_of_commute hζ hX₁3 hX₁s (hcomm h hxh hyh) ?_
    rw [← Units.val_pow_eq_pow_val]; exact hh3
  obtain ⟨μx, hμx⟩ := hcube x α (Commute.refl x) hc.symm hx3
  obtain ⟨μy, hμy⟩ := hcube y β hc (Commute.refl y) hy3
  have hμx0 : μx ≠ 0 := by rintro rfl; exact hα (by rw [← hμx]; norm_num)
  have hμy0 : μy ≠ 0 := by rintro rfl; exact hβ (by rw [← hμy]; norm_num)
  obtain ⟨ux, hux⟩ : ∃ u : Fˣ, (u : F) = μx⁻¹ := ⟨Units.mk0 _ (inv_ne_zero hμx0), rfl⟩
  obtain ⟨uy, huy⟩ : ∃ u : Fˣ, (u : F) = μy⁻¹ := ⟨Units.mk0 _ (inv_ne_zero hμy0), rfl⟩
  obtain ⟨xn, hxn⟩ : ∃ g : GL (Fin 3) F, g = Matrix.GeneralLinearGroup.scalar (Fin 3) ux * x :=
    ⟨_, rfl⟩
  obtain ⟨yn, hyn⟩ : ∃ g : GL (Fin 3) F, g = Matrix.GeneralLinearGroup.scalar (Fin 3) uy * y :=
    ⟨_, rfl⟩
  have hx3' : (x : Matrix (Fin 3) (Fin 3) F) ^ 3 = α • 1 := by
    rw [← Units.val_pow_eq_pow_val]; exact hx3
  have hy3' : (y : Matrix (Fin 3) (Fin 3) F) ^ 3 = β • 1 := by
    rw [← Units.val_pow_eq_pow_val]; exact hy3
  have hxn3 : xn ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hxn, coe_scalarGL_mul, smul_pow, hx3', smul_smul, hux, ← hμx,
      ← mul_pow, inv_mul_cancel₀ hμx0, one_pow, one_smul, Units.val_one]
  have hyn3 : yn ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hyn, coe_scalarGL_mul, smul_pow, hy3', smul_smul, huy, ← hμy,
      ← mul_pow, inv_mul_cancel₀ hμy0, one_pow, one_smul, Units.val_one]
  have hxyn : Commute xn yn := by
    rw [hxn, hyn]
    exact Commute.mul_left (Commute.mul_right (commute_scalarGL ux _) (commute_scalarGL ux _))
      (Commute.mul_right (commute_scalarGL uy x).symm hc)
  have hpair : ({xn, yn} : Set (GL (Fin 3) F)).Pairwise Commute := by
    rw [Set.pairwise_pair]; exact fun _ => ⟨hxyn, hxyn.symm⟩
  have hcomE : IsMulCommutative (Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F))) :=
    Subgroup.isMulCommutative_closure hpair
  have hcommE : ∀ u ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F)),
      ∀ v ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F)), u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hcomE.is_comm.comm (⟨u, hu⟩ :
      Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F))) ⟨v, hv⟩)
  have hexpE : ∀ u ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F)), u ^ 3 = 1 := by
    intro u hu
    refine Subgroup.closure_induction (p := fun u _ => u ^ 3 = 1) ?_ (by simp) ?_ ?_ hu
    · intro u hu
      rcases hu with rfl | hu
      · exact hxn3
      · rw [Set.mem_singleton_iff] at hu
        rw [hu]; exact hyn3
    · intro u v hu hv hu3 hv3
      rw [Commute.mul_pow (hcommE u hu v hv), hu3, hv3, one_mul]
    · intro u hu hu3
      rw [inv_pow, hu3, inv_one]
  obtain ⟨P, hP⟩ := exists_conj_diagonal_of_exponent_prime (p := 3) hζ _ hcommE hexpE
  have hxnE : xn ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hynE : yn ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hdiag : ∀ g ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) F)),
      ((P : Matrix (Fin 3) (Fin 3) F) * g =
        diagonal (fun i => ((P * g * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i) * P) := by
    intro g hg
    have hA : ((P * g * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        diagonal (fun i => ((P * g * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · rw [diagonal_apply_ne _ hij]; exact hP g hg i j hij
    rw [← hA, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul,
      Matrix.mul_one]
  set a : Fin 3 → F := fun i => ((P * xn * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i
    with ha
  set b : Fin 3 → F := fun i => ((P * yn * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i
    with hb
  have hPx : (P : Matrix (Fin 3) (Fin 3) F) * xn = diagonal a * P := hdiag xn hxnE
  have hPy : (P : Matrix (Fin 3) (Fin 3) F) * yn = diagonal b * P := hdiag yn hynE
  have hcube1 : ∀ (g : GL (Fin 3) F) (d : Fin 3 → F),
      (P : Matrix (Fin 3) (Fin 3) F) * g = diagonal d * P → g ^ 3 = 1 → ∀ i, d i ^ 3 = 1 := by
    intro g d hPg hg3 i
    have h1 := intertwine_pow_left hPg 3
    rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one, Matrix.mul_one, diagonal_pow] at h1
    have h2 : (diagonal (d ^ 3) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      calc (diagonal (d ^ 3) : Matrix (Fin 3) (Fin 3) F)
          = diagonal (d ^ 3) * (P : Matrix (Fin 3) (Fin 3) F) *
            ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
            rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        _ = 1 := by rw [← h1, Units.mul_inv]
    have := congrFun (congrFun h2 i) i
    simpa using this
  have ha3 := hcube1 xn a hPx hxn3
  have hb3 := hcube1 yn b hPy hyn3
  have hline : ∀ t : ℕ, ((xn * yn ^ t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((ux : F) * (uy : F) ^ t) • ((x * y ^ t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro t
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hxn, hyn, coe_scalarGL_mul, coe_scalarGL_mul,
      smul_pow, Units.val_mul, Units.val_pow_eq_pow_val, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
  have hxline : ((xn : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (ux : F) • (x : Matrix (Fin 3) (Fin 3) F) := by rw [hxn, coe_scalarGL_mul]
  have hyline : ((yn : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (uy : F) • (y : Matrix (Fin 3) (Fin 3) F) := by rw [hyn, coe_scalarGL_mul]
  have hux0 : (ux : F) ≠ 0 := ux.ne_zero
  have huy0 : (uy : F) ≠ 0 := uy.ne_zero
  have hmem : ∀ (i j : Fin 3) (hij : i ≠ j) (c : F),
      conjUnit P⁻¹ (SpecialLinearGroup.transvection hij c) ∈
        Subgroup.closure (planeFix x y) := by
    intro i j hij c
    have haj : a j ≠ 0 := fun h => by have := ha3 j; rw [h] at this; norm_num at this
    have hbj : b j ≠ 0 := fun h => by have := hb3 j; rw [h] at this; norm_num at this
    have hr : (a i * (a j)⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, ha3 i, ha3 j, inv_one, one_mul]
    have hu : (b i * (b j)⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, hb3 i, hb3 j, inv_one, one_mul]
    refine Subgroup.subset_closure ?_
    rcases cube_roots_cases hr hu with h | h | h | h
    ·
      have hD : a i = a j := (mul_inv_eq_one₀ haj).1 h
      have := mem_FixSL_conj_transvection hPx hij hD c
      rw [hxline, mem_FixSL_smul hux0] at this
      exact Or.inl (Or.inl (Or.inl this))
    · have hD : b i = b j := (mul_inv_eq_one₀ hbj).1 h
      have := mem_FixSL_conj_transvection hPy hij hD c
      rw [hyline, mem_FixSL_smul huy0] at this
      exact Or.inl (Or.inl (Or.inr this))
    · have hD : a i * b i = a j * b j := by
        field_simp at h
        linear_combination h
      have hP' : (P : Matrix (Fin 3) (Fin 3) F) *
          ((xn * yn : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          diagonal (fun k => a k * b k) * P := by
        rw [Units.val_mul, intertwine_mul_left hPx hPy, diagonal_mul_diagonal]
      have := mem_FixSL_conj_transvection hP' hij hD c
      have h1 : ((xn * yn : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          ((ux : F) * (uy : F)) • ((x * y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        simpa only [pow_one] using hline 1
      rw [h1, mem_FixSL_smul (mul_ne_zero hux0 huy0)] at this
      exact Or.inl (Or.inr this)
    · have hD : a i * b i ^ 2 = a j * b j ^ 2 := by
        field_simp at h
        linear_combination h
      have hP' : (P : Matrix (Fin 3) (Fin 3) F) *
          ((xn * yn ^ 2 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          diagonal (fun k => a k * b k ^ 2) * P := by
        rw [Units.val_mul, Units.val_pow_eq_pow_val,
          intertwine_mul_left hPx (intertwine_pow_left hPy 2), diagonal_pow, diagonal_mul_diagonal]
        rfl
      have := mem_FixSL_conj_transvection hP' hij hD c
      rw [hline 2, mem_FixSL_smul (mul_ne_zero hux0 (pow_ne_zero 2 huy0))] at this
      exact Or.inr this
  exact eq_top_of_conj_transvections P⁻¹ hmem

end Abelian

end CFSG.LieType.SeitzGeneration
