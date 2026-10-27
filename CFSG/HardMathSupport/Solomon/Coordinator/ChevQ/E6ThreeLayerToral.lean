module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeHeisSL3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.LieType.SeitzGeneration

section Toral

variable {K : Type*} [Field K]

theorem conjSL_eq_one_of_eq_smul_one {z : GL (Fin 3) K} {c : K}
    (h : (z : Matrix (Fin 3) (Fin 3) K) = c • 1) : conjSL z = 1 :=
  MulEquiv.ext fun _ => conjSL_apply_eq_self_iff.2 (by
    rw [h, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])

theorem conjUnit_transvection_mem_planeClosure {P g : GL (Fin 3) K} {D : Fin 3 → K}
    (hPg : (P : Matrix (Fin 3) (Fin 3) K) * g = diagonal D * P) {i j : Fin 3} (hij : i ≠ j)
    (hD : D i = D j) (c : K) {A : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))}
    (hg : conjSL g ∈ A) (hg1 : conjSL g ≠ 1) :
    conjUnit P⁻¹ (SpecialLinearGroup.transvection hij c) ∈ planeClosure A := by
  have hPi : ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * P = 1 := Units.inv_mul P
  have hiP : (P : Matrix (Fin 3) (Fin 3) K) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := Units.mul_inv P
  have hg' : (g : Matrix (Fin 3) (Fin 3) K) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal D := by
    calc (g : Matrix (Fin 3) (Fin 3) K) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((P : Matrix (Fin 3) (Fin 3) K) * g) *
          ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [← Matrix.mul_assoc, hPi, Matrix.one_mul]
      _ = _ := by rw [hPg, Matrix.mul_assoc, Matrix.mul_assoc, hiP, Matrix.mul_one]
  have hk : ((SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * diagonal D =
      diagonal D * ((SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
    rw [SpecialLinearGroup.transvection_coe]
    exact (diagonal_commute_one_add_single hD c).symm
  exact mem_planeClosure_of_commute_gl hg hg1
    (commute_conjUnit_of_intertwine (P := P⁻¹) hg' hk).symm

end Toral

theorem planeGen_of_toralPair {K : Type*} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    {x y : GL (Fin 3) K} (hxy : x * y = y * x)
    (hx3 : ∃ α : K, (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1)
    (hy3 : ∃ β : K, (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = β • 1)
    (hind : ∀ a b : ℕ, ¬ (3 ∣ a ∧ 3 ∣ b) → conjSL x ^ a * conjSL y ^ b ≠ 1)
    {A : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))} (hx : conjSL x ∈ A)
    (hy : conjSL y ∈ A) : PlaneGen A := by
  have hζ := exists_isPrimitiveRoot_three h3
  obtain ⟨α, hα3⟩ := hx3
  obtain ⟨β, hβ3⟩ := hy3
  have hα : α ≠ 0 := ne_zero_of_pow_three_eq_smul hα3
  have hβ : β ≠ 0 := ne_zero_of_pow_three_eq_smul hβ3
  have hx3 : ((x ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = α • 1 := by
    rw [Units.val_pow_eq_pow_val]; exact hα3
  have hy3 : ((y ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = β • 1 := by
    rw [Units.val_pow_eq_pow_val]; exact hβ3
  have hc : Commute x y := hxy
  have hx1 : conjSL x ≠ 1 := by simpa using hind 1 0 (by omega)
  have hy1 : conjSL y ≠ 1 := by simpa using hind 0 1 (by omega)
  have hxy1 : conjSL x * conjSL y ≠ 1 := by simpa using hind 1 1 (by omega)
  have hxy2 : conjSL x * conjSL y ^ 2 ≠ 1 := by simpa using hind 1 2 (by omega)
  have hind' : ∀ a b : ℕ,
      (∃ c : K, ((x ^ a * y ^ b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) →
        3 ∣ a ∧ 3 ∣ b := by
    rintro a b ⟨c, hcab⟩
    by_contra hab
    refine hind a b hab ?_
    have h1 : conjSL (x ^ a * y ^ b) = conjSL x ^ a * conjSL y ^ b := by
      rw [map_mul, map_pow, map_pow]
    rw [← h1]
    exact conjSL_eq_one_of_eq_smul_one hcab
  obtain ⟨m, n, s, hs0, hmn, hs3⟩ :=
    CFSG.LieType.SeitzGeneration.exists_cube_line h3 (w := 1) (fun g => Commute.one_left g)
      (one_pow 3) (by rw [one_mul]; exact hxy.symm) hα hβ hx3 hy3
  set g₀ : GL (Fin 3) K := x ^ m * y ^ n with hg₀
  set X₁ : Matrix (Fin 3) (Fin 3) K := s⁻¹ • (g₀ : Matrix (Fin 3) (Fin 3) K) with hX₁
  have hX₁3 : X₁ ^ 3 = 1 := by
    rw [hX₁, smul_pow, ← Units.val_pow_eq_pow_val, hs3, smul_smul, ← mul_pow, inv_mul_cancel₀ hs0,
      one_pow, one_smul]
  have hX₁s : ∀ c : K, X₁ ≠ c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro c hcX
    have h1 : ((x ^ m * y ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (s * c) • 1 := by
      have : (g₀ : Matrix (Fin 3) (Fin 3) K) = s • X₁ := by
        rw [hX₁, smul_smul, mul_inv_cancel₀ hs0, one_smul]
      rw [← hg₀, this, hcX, smul_smul]
    have := hind' m n ⟨_, h1⟩
    omega
  have hcomm : ∀ h : GL (Fin 3) K, Commute x h → Commute y h →
      X₁ * (h : Matrix (Fin 3) (Fin 3) K) = (h : Matrix (Fin 3) (Fin 3) K) * X₁ := by
    intro h hxh hyh
    have h1 : Commute g₀ h := ((hxh.pow_left m).mul_left (hyh.pow_left n))
    have h2 : (g₀ : Matrix (Fin 3) (Fin 3) K) * h = h * g₀ := congrArg Units.val h1.eq
    rw [hX₁, Matrix.smul_mul, Matrix.mul_smul, h2]
  have hcube : ∀ (h : GL (Fin 3) K) (lam : K), Commute x h → Commute y h →
      ((h ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = lam • 1 → ∃ μ : K, μ ^ 3 = lam := by
    intro h lam hxh hyh hh3
    refine exists_cube_of_commute hζ hX₁3 hX₁s (hcomm h hxh hyh) ?_
    rw [← Units.val_pow_eq_pow_val]; exact hh3
  obtain ⟨μx, hμx⟩ := hcube x α (Commute.refl x) hc.symm hx3
  obtain ⟨μy, hμy⟩ := hcube y β hc (Commute.refl y) hy3
  have hμx0 : μx ≠ 0 := by rintro rfl; exact hα (by rw [← hμx]; norm_num)
  have hμy0 : μy ≠ 0 := by rintro rfl; exact hβ (by rw [← hμy]; norm_num)
  obtain ⟨ux, hux⟩ : ∃ u : Kˣ, (u : K) = μx⁻¹ := ⟨Units.mk0 _ (inv_ne_zero hμx0), rfl⟩
  obtain ⟨uy, huy⟩ : ∃ u : Kˣ, (u : K) = μy⁻¹ := ⟨Units.mk0 _ (inv_ne_zero hμy0), rfl⟩
  obtain ⟨xn, hxn⟩ : ∃ g : GL (Fin 3) K, g = Matrix.GeneralLinearGroup.scalar (Fin 3) ux * x :=
    ⟨_, rfl⟩
  obtain ⟨yn, hyn⟩ : ∃ g : GL (Fin 3) K, g = Matrix.GeneralLinearGroup.scalar (Fin 3) uy * y :=
    ⟨_, rfl⟩
  have hxn3 : xn ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hxn, coe_scalarGL_mul, smul_pow, hα3, smul_smul, hux, ← hμx,
      ← mul_pow, inv_mul_cancel₀ hμx0, one_pow, one_smul, Units.val_one]
  have hyn3 : yn ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hyn, coe_scalarGL_mul, smul_pow, hβ3, smul_smul, huy, ← hμy,
      ← mul_pow, inv_mul_cancel₀ hμy0, one_pow, one_smul, Units.val_one]
  have hxyn : Commute xn yn := by
    rw [hxn, hyn]
    exact Commute.mul_left (Commute.mul_right (commute_scalarGL ux _) (commute_scalarGL ux _))
      (Commute.mul_right (commute_scalarGL uy x).symm hc)
  have hxnc : conjSL xn = conjSL x := by rw [hxn, map_mul, conjSL_scalar, one_mul]
  have hync : conjSL yn = conjSL y := by rw [hyn, map_mul, conjSL_scalar, one_mul]
  have hpair : ({xn, yn} : Set (GL (Fin 3) K)).Pairwise Commute := by
    rw [Set.pairwise_pair]; exact fun _ => ⟨hxyn, hxyn.symm⟩
  have hcomE : IsMulCommutative (Subgroup.closure ({xn, yn} : Set (GL (Fin 3) K))) :=
    Subgroup.isMulCommutative_closure hpair
  have hcommE : ∀ u ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) K)),
      ∀ v ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) K)), u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hcomE.is_comm.comm (⟨u, hu⟩ :
      Subgroup.closure ({xn, yn} : Set (GL (Fin 3) K))) ⟨v, hv⟩)
  have hexpE : ∀ u ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) K)), u ^ 3 = 1 := by
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
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime (p := 3)
    hζ _ hcommE hexpE
  have hxnE : xn ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) K)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hynE : yn ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) K)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hdiag : ∀ g ∈ Subgroup.closure ({xn, yn} : Set (GL (Fin 3) K)),
      ((P : Matrix (Fin 3) (Fin 3) K) * g =
        diagonal (fun i => ((P * g * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i) * P) := by
    intro g hg
    have hA : ((P * g * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal (fun i => ((P * g * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · rw [diagonal_apply_ne _ hij]; exact hP g hg i j hij
    rw [← hA, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul,
      Matrix.mul_one]
  set da : Fin 3 → K := fun i => ((P * xn * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i
    with hda
  set db : Fin 3 → K := fun i => ((P * yn * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i
    with hdb
  have hPx : (P : Matrix (Fin 3) (Fin 3) K) * xn = diagonal da * P := hdiag xn hxnE
  have hPy : (P : Matrix (Fin 3) (Fin 3) K) * yn = diagonal db * P := hdiag yn hynE
  have hcube1 : ∀ (g : GL (Fin 3) K) (d : Fin 3 → K),
      (P : Matrix (Fin 3) (Fin 3) K) * g = diagonal d * P → g ^ 3 = 1 → ∀ i, d i ^ 3 = 1 := by
    intro g d hPg hg3 i
    have h1 := intertwine_pow_left hPg 3
    rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one, Matrix.mul_one, diagonal_pow] at h1
    have h2 : (diagonal (d ^ 3) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      calc (diagonal (d ^ 3) : Matrix (Fin 3) (Fin 3) K)
          = diagonal (d ^ 3) * (P : Matrix (Fin 3) (Fin 3) K) *
            ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
            rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        _ = 1 := by rw [← h1, Units.mul_inv]
    have := congrFun (congrFun h2 i) i
    simpa using this
  have ha3 := hcube1 xn da hPx hxn3
  have hb3 := hcube1 yn db hPy hyn3
  have hmem : ∀ (i j : Fin 3) (hij : i ≠ j) (c : K),
      conjUnit P⁻¹ (SpecialLinearGroup.transvection hij c) ∈ planeClosure A := by
    intro i j hij c
    have haj : da j ≠ 0 := fun h => by have := ha3 j; rw [h] at this; norm_num at this
    have hbj : db j ≠ 0 := fun h => by have := hb3 j; rw [h] at this; norm_num at this
    have hr : (da i * (da j)⁻¹) ^ 3 = 1 := by
      rw [mul_pow, inv_pow, ha3 i, ha3 j, inv_one, one_mul]
    have hu : (db i * (db j)⁻¹) ^ 3 = 1 := by
      rw [mul_pow, inv_pow, hb3 i, hb3 j, inv_one, one_mul]
    rcases cube_roots_cases hr hu with h | h | h | h
    ·
      have hD : da i = da j := (mul_inv_eq_one₀ haj).1 h
      exact conjUnit_transvection_mem_planeClosure hPx hij hD c (by rw [hxnc]; exact hx)
        (by rw [hxnc]; exact hx1)
    ·
      have hD : db i = db j := (mul_inv_eq_one₀ hbj).1 h
      exact conjUnit_transvection_mem_planeClosure hPy hij hD c (by rw [hync]; exact hy)
        (by rw [hync]; exact hy1)
    ·
      have hD : da i * db i = da j * db j := by
        field_simp at h
        linear_combination h
      have hP' : (P : Matrix (Fin 3) (Fin 3) K) *
          ((xn * yn : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          diagonal (fun k => da k * db k) * P := by
        rw [Units.val_mul, intertwine_mul_left hPx hPy, diagonal_mul_diagonal]
      have hl : conjSL (xn * yn) = conjSL x * conjSL y := by rw [map_mul, hxnc, hync]
      exact conjUnit_transvection_mem_planeClosure hP' hij hD c
        (by rw [hl]; exact A.mul_mem hx hy) (by rw [hl]; exact hxy1)
    ·
      have hD : da i * db i ^ 2 = da j * db j ^ 2 := by
        field_simp at h
        linear_combination h
      have hP' : (P : Matrix (Fin 3) (Fin 3) K) *
          ((xn * yn ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          diagonal (fun k => da k * db k ^ 2) * P := by
        rw [Units.val_mul, Units.val_pow_eq_pow_val,
          intertwine_mul_left hPx (intertwine_pow_left hPy 2), diagonal_pow, diagonal_mul_diagonal]
        rfl
      have hl : conjSL (xn * yn ^ 2) = conjSL x * conjSL y ^ 2 := by
        rw [map_mul, map_pow, hxnc, hync]
      exact conjUnit_transvection_mem_planeClosure hP' hij hD c
        (by rw [hl]; exact A.mul_mem hx (A.pow_mem hy 2)) (by rw [hl]; exact hxy2)
  exact eq_top_of_conj_transvections P⁻¹ hmem

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
