module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4QGen

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix Polynomial Module

namespace GenLocL4Q

variable {F : Type} [Field F]

theorem exists_sum_sq_eq_one [Finite F] (hF : ringChar F ≠ 2) {c m : F} (hc : c ≠ 0) (hm : m ≠ 0) :
    ∃ a b : F, a ^ 2 * c + b ^ 2 * m = 1 := by
  classical
  have := Fintype.ofFinite F
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  have hf : (C c * X ^ 2 : F[X]).degree = 2 := by
    rw [degree_C_mul hc]; exact degree_X_pow 2
  have hg : (C m * X ^ 2 - C 1 : F[X]).degree = 2 := by
    have h1 : (C m * X ^ 2 : F[X]).degree = 2 := by rw [degree_C_mul hm]; exact degree_X_pow 2
    rw [degree_sub_eq_left_of_degree_lt (by rw [h1]; exact lt_of_le_of_lt degree_C_le (by norm_num))]
    exact h1
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  refine ⟨a, b, ?_⟩
  simp at hab
  linear_combination hab

theorem isCompl_ker_sq_one {V : Type*} [AddCommGroup V] [Module F V] (h2 : (2 : F) ≠ 0)
    {f : Module.End F V} (hf : f * f = 1) :
    IsCompl (LinearMap.ker (f - 1)) (LinearMap.ker (f + 1)) := by
  have hf' : ∀ v, f (f v) = v := fun v => by
    have := congrArg (fun g : Module.End F V => g v) hf
    simpa using this
  constructor
  · rw [Submodule.disjoint_def]
    intro v h1 h2'
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at h2'
    rw [h1] at h2'
    have : (2 : F) • v = 0 := by rw [two_smul]; exact h2'
    exact (smul_eq_zero.1 this).resolve_left h2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v = (2 : F)⁻¹ • (v + f v) + (2 : F)⁻¹ • (v - f v) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul F v, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [hv]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, hf',
        sub_eq_zero, add_comm]
    · rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_smul, map_sub, hf',
        ← smul_add]
      simp


theorem exists_two_indep (h2 : (2 : F) ≠ 0) {ℓ w : Matrix (Fin 4) (Fin 4) F} (hℓ : ℓ * ℓ = 1)
    (hw : IsUnit w) (hwℓ : w * ℓ = -(ℓ * w)) :
    ∃ p q : Fin 4 → F, ℓ *ᵥ p = p ∧ ℓ *ᵥ q = q ∧ LinearIndependent F ![p, q, w *ᵥ p, w *ᵥ q] := by
  classical
  set f : Module.End F (Fin 4 → F) := Matrix.toLin' ℓ with hf
  set g : Module.End F (Fin 4 → F) := Matrix.toLin' w with hg
  have hff : f * f = 1 := by
    rw [hf, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hℓ, Matrix.toLin'_one]; rfl
  have hgf : ∀ u, g (f u) = -f (g u) := fun u => by
    have := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A *ᵥ u) hwℓ
    simp only [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec] at this
    simpa [hf, hg] using this
  have hginj : Function.Injective g := by
    have := Matrix.mulVec_injective_iff_isUnit.2 hw
    intro a b hab
    exact this (by simpa [hg] using hab)
  have hC := isCompl_ker_sq_one h2 hff
  set Vp := LinearMap.ker (f - 1) with hVp
  set Vm := LinearMap.ker (f + 1) with hVm
  have hmemp : ∀ u, u ∈ Vp ↔ f u = u := fun u => by
    rw [hVp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hmemm : ∀ u, u ∈ Vm ↔ f u = -u := fun u => by
    rw [hVm, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]
  have hdim : finrank F Vp + finrank F Vm = 4 := by
    rw [Submodule.finrank_add_eq_of_isCompl hC]; simp
  have hfg : ∀ u, f (g u) = -g (f u) := fun u => by rw [hgf]; simp
  have hpm : ∀ u ∈ Vp, g u ∈ Vm := fun u hu => by
    rw [hmemm, hfg, (hmemp u).1 hu]
  have hmp : ∀ u ∈ Vm, g u ∈ Vp := fun u hu => by
    rw [hmemp, hfg, (hmemm u).1 hu]; simp
  let gpm : Vp →ₗ[F] Vm := g.restrict hpm
  let gmp : Vm →ₗ[F] Vp := g.restrict hmp
  have hgpm : Function.Injective gpm := fun a b hab => Subtype.ext (hginj (congrArg Subtype.val hab))
  have hgmp : Function.Injective gmp := fun a b hab => Subtype.ext (hginj (congrArg Subtype.val hab))
  have h1 := LinearMap.finrank_le_finrank_of_injective hgpm
  have h2' := LinearMap.finrank_le_finrank_of_injective hgmp
  have hd2 : finrank F Vp = 2 := by omega
  let b := Module.finBasisOfFinrankEq F Vp hd2
  have hbind : LinearIndependent F (fun i => ((b i : Vp) : Fin 4 → F)) :=
    b.linearIndependent.map' Vp.subtype (Submodule.ker_subtype _)
  refine ⟨(b 0 : Fin 4 → F), (b 1 : Fin 4 → F), ?_, ?_, ?_⟩
  · simpa [hf] using (hmemp _).1 (b 0).2
  · simpa [hf] using (hmemp _).1 (b 1).2
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hc
    have hgp : w *ᵥ (b 0 : Fin 4 → F) = g (b 0 : Fin 4 → F) := by simp [hg]
    have hgq : w *ᵥ (b 1 : Fin 4 → F) = g (b 1 : Fin 4 → F) := by simp [hg]
    rw [hgp, hgq] at hc
    have hs : c 0 • (b 0 : Fin 4 → F) + c 1 • (b 1 : Fin 4 → F) ∈ Vp :=
      Vp.add_mem (Vp.smul_mem _ (b 0).2) (Vp.smul_mem _ (b 1).2)
    have ht : g (c 2 • (b 0 : Fin 4 → F) + c 3 • (b 1 : Fin 4 → F)) ∈ Vm :=
      hpm _ (Vp.add_mem (Vp.smul_mem _ (b 0).2) (Vp.smul_mem _ (b 1).2))
    have hsum : (c 0 • (b 0 : Fin 4 → F) + c 1 • (b 1 : Fin 4 → F)) +
        g (c 2 • (b 0 : Fin 4 → F) + c 3 • (b 1 : Fin 4 → F)) = 0 := by
      rw [map_add, map_smul, map_smul]; rw [← hc]; abel
    have hs' : c 0 • (b 0 : Fin 4 → F) + c 1 • (b 1 : Fin 4 → F) ∈ Vm := by
      have : c 0 • (b 0 : Fin 4 → F) + c 1 • (b 1 : Fin 4 → F) =
          -g (c 2 • (b 0 : Fin 4 → F) + c 3 • (b 1 : Fin 4 → F)) := eq_neg_of_add_eq_zero_left hsum
      rw [this]; exact Vm.neg_mem ht
    have hs0 : c 0 • (b 0 : Fin 4 → F) + c 1 • (b 1 : Fin 4 → F) = 0 :=
      (Submodule.disjoint_def.1 hC.1) _ hs hs'
    have ht0 : g (c 2 • (b 0 : Fin 4 → F) + c 3 • (b 1 : Fin 4 → F)) = 0 := by
      rw [hs0, zero_add] at hsum; exact hsum
    have ht1 : c 2 • (b 0 : Fin 4 → F) + c 3 • (b 1 : Fin 4 → F) = 0 :=
      hginj (by rw [ht0, map_zero])
    have key := Fintype.linearIndependent_iff.1 hbind
    have k1 := key ![c 0, c 1] (by simpa [Fin.sum_univ_two] using hs0)
    have k2 := key ![c 2, c 3] (by simpa [Fin.sum_univ_two] using ht1)
    intro i
    fin_cases i
    · simpa using k1 0
    · simpa using k1 1
    · simpa using k2 0
    · simpa using k2 1

theorem exists_regular_basis [Finite F] (hF : ringChar F ≠ 2) {c m : F} (hc : c ≠ 0) (hm : m ≠ 0)
    {x y : Matrix (Fin 4) (Fin 4) F} (hx : x * x = c • 1) (hy : y * y = m • 1)
    (hxy : x * y = -(y * x)) :
    ∃ R : Matrix (Fin 4) (Fin 4) F, IsUnit R ∧ x * R = R * Xr c ∧ y * R = R * Yr m := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨a, b, hab⟩ := exists_sum_sq_eq_one hF hc hm
  obtain ⟨w, hwdef⟩ : ∃ w : Matrix (Fin 4) (Fin 4) F, w = x * y := ⟨_, rfl⟩
  have hyx : y * x = -w := by rw [hwdef, hxy]; simp
  have hxw : x * w = c • y := by rw [hwdef, ← Matrix.mul_assoc, hx, smul_mul_assoc, one_mul]
  have hwx : w * x = -(c • y) := by
    rw [hwdef, Matrix.mul_assoc, hyx, hwdef, Matrix.mul_neg, ← Matrix.mul_assoc, hx, smul_mul_assoc, one_mul]
  have hyw : y * w = -(m • x) := by
    rw [hwdef, ← Matrix.mul_assoc, hyx, hwdef, Matrix.neg_mul, Matrix.mul_assoc, hy, mul_smul_comm, mul_one]
  have hwy : w * y = m • x := by rw [hwdef, Matrix.mul_assoc, hy, mul_smul_comm, mul_one]
  have hww : w * w = (-(c * m)) • (1 : Matrix (Fin 4) (Fin 4) F) := by
    have : w * w = w * (x * y) := by rw [← hwdef]
    rw [this, ← Matrix.mul_assoc, hwx, Matrix.neg_mul, smul_mul_assoc, hy, smul_smul, ← neg_smul]
  set ℓ : Matrix (Fin 4) (Fin 4) F := a • x + b • y with hℓdef
  have hℓ : ℓ * ℓ = 1 := by
    have : ℓ * ℓ = (a ^ 2 * c + b ^ 2 * m) • (1 : Matrix (Fin 4) (Fin 4) F) := by
      rw [hℓdef]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
      rw [hx, hy, hyx, ← hwdef]
      module
    rw [this, hab, one_smul]
  have hωne : (-(c * m)) ≠ 0 := by simp [hc, hm]
  have hwunit : IsUnit w := by
    have h1 : w * ((-(c * m))⁻¹ • w) = 1 := by
      rw [mul_smul_comm, hww, smul_smul, inv_mul_cancel₀ hωne, one_smul]
    exact (Matrix.isUnit_iff_isUnit_det w).2 (Matrix.isUnit_det_of_right_inverse h1)
  have hwℓ : w * ℓ = -(ℓ * w) := by
    rw [hℓdef]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    rw [hwx, hwy, hxw, hyw]
    module
  obtain ⟨p, q, hp, hq, hind⟩ := exists_two_indep h2 hℓ hwunit hwℓ
  have hxℓ : x * ℓ = (a * c) • (1 : Matrix (Fin 4) (Fin 4) F) + b • w := by
    rw [hℓdef, mul_add, mul_smul_comm, mul_smul_comm, hx, ← hwdef]
    module
  have hyℓ : y * ℓ = (b * m) • (1 : Matrix (Fin 4) (Fin 4) F) - a • w := by
    rw [hℓdef, mul_add, mul_smul_comm, mul_smul_comm, hy, hyx]
    module
  have hxu : ∀ u : Fin 4 → F, ℓ *ᵥ u = u → x *ᵥ u = (a * c) • u + b • (w *ᵥ u) := by
    intro u hu
    calc x *ᵥ u = x *ᵥ (ℓ *ᵥ u) := by rw [hu]
      _ = (x * ℓ) *ᵥ u := by rw [Matrix.mulVec_mulVec]
      _ = _ := by rw [hxℓ]; simp [Matrix.add_mulVec, Matrix.smul_mulVec]
  have hyu : ∀ u : Fin 4 → F, ℓ *ᵥ u = u → y *ᵥ u = (b * m) • u - a • (w *ᵥ u) := by
    intro u hu
    calc y *ᵥ u = y *ᵥ (ℓ *ᵥ u) := by rw [hu]
      _ = (y * ℓ) *ᵥ u := by rw [Matrix.mulVec_mulVec]
      _ = _ := by rw [hyℓ]; simp [Matrix.sub_mulVec, Matrix.smul_mulVec]
  have hWW : ∀ u : Fin 4 → F, w *ᵥ (w *ᵥ u) = (-(c * m)) • u := by
    intro u
    rw [Matrix.mulVec_mulVec, hww, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hxW : ∀ u : Fin 4 → F, x *ᵥ (w *ᵥ u) = -(w *ᵥ (x *ᵥ u)) := by
    intro u
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have : x * w = -(w * x) := by rw [hxw, hwx, neg_neg]
    rw [this, Matrix.neg_mulVec]
  have hyW : ∀ u : Fin 4 → F, y *ᵥ (w *ᵥ u) = -(w *ᵥ (y *ᵥ u)) := by
    intro u
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have : y * w = -(w * y) := by rw [hyw, hwy]
    rw [this, Matrix.neg_mulVec]
  have hkey : ∀ k : Fin 4 → F, k 0 • p + k 1 • q + k 2 • (w *ᵥ p) + k 3 • (w *ᵥ q) = 0 → ∀ i, k i = 0 := by
    intro k hk
    have := Fintype.linearIndependent_iff.1 hind k
    refine this ?_
    simpa [Fin.sum_univ_four, add_assoc] using hk
  obtain ⟨v, hvdef⟩ : ∃ v : Fin 4 → F, v = p + w *ᵥ q := ⟨_, rfl⟩
  have hxv : x *ᵥ v = (a * c) • p + (-(b * (-(c * m)))) • q + b • (w *ᵥ p) + (-(a * c)) • (w *ᵥ q) := by
    have e1 := hxu p hp
    have e3 := hxu q hq
    have e4 : w *ᵥ (x *ᵥ q) = (a * c) • (w *ᵥ q) + b • ((-(c * m)) • q) := by
      rw [e3, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hWW]
    rw [hvdef, Matrix.mulVec_add, e1, hxW, e4]
    module
  have hyv : y *ᵥ v = (b * m) • p + (a * (-(c * m))) • q + (-a) • (w *ᵥ p) + (-(b * m)) • (w *ᵥ q) := by
    have e1 := hyu p hp
    have e3 := hyu q hq
    have e4 : w *ᵥ (y *ᵥ q) = (b * m) • (w *ᵥ q) - a • ((-(c * m)) • q) := by
      rw [e3, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hWW]
    rw [hvdef, Matrix.mulVec_add, e1, hyW, e4]
    module
  have hwv : w *ᵥ v = (-(c * m)) • q + w *ᵥ p := by
    rw [hvdef, Matrix.mulVec_add, hWW]; module
  have hxyv : x *ᵥ (y *ᵥ v) = w *ᵥ v := by
    rw [Matrix.mulVec_mulVec, hwdef]
  let R : Matrix (Fin 4) (Fin 4) F := Matrix.of fun i j => (![v, x *ᵥ v, y *ᵥ v, w *ᵥ v] j) i
  have hR : ∀ g : Fin 4 → F, R *ᵥ g = g 0 • v + g 1 • (x *ᵥ v) + g 2 • (y *ᵥ v) + g 3 • (w *ᵥ v) := by
    intro g
    ext i
    simp [R, Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm]
  have hRinj : Function.Injective R.mulVec := by
    have hinj : Function.Injective (Matrix.mulVecLin R) := by
      rw [injective_iff_map_eq_zero]
      intro g hg
      have hg' : R *ᵥ g = 0 := hg
      rw [hR, hxv, hyv, hwv, hvdef] at hg'
      have hk := hkey ![g 0 + g 1 * (a * c) + g 2 * (b * m),
        g 1 * (-(b * (-(c * m)))) + g 2 * (a * (-(c * m))) + g 3 * (-(c * m)),
        g 1 * b + g 2 * (-a) + g 3, g 0 + g 1 * (-(a * c)) + g 2 * (-(b * m))] (by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          rw [← hg']; module)
      have k0 := hk 0
      have k1 := hk 1
      have k2 := hk 2
      have k3 := hk 3
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at k0 k1 k2 k3
      have g0z : g 0 = 0 := by
        have : (2 : F) * g 0 = 0 := by linear_combination k0 + k3
        exact (mul_eq_zero.1 this).resolve_left h2
      have e1 : -(g 1 * b) + g 2 * a + g 3 = 0 := by
        have : (-(c * m)) * (-(g 1 * b) + g 2 * a + g 3) = 0 := by linear_combination k1
        exact (mul_eq_zero.1 this).resolve_left hωne
      have g3z : g 3 = 0 := by
        have : (2 : F) * g 3 = 0 := by linear_combination e1 + k2
        exact (mul_eq_zero.1 this).resolve_left h2
      have e2 : g 1 * b - g 2 * a = 0 := by linear_combination k2 - g3z
      have e3 : g 1 * (a * c) + g 2 * (b * m) = 0 := by linear_combination k0 - g0z
      have g1z : g 1 = 0 := by linear_combination a * e3 + m * b * e2 - g 1 * hab
      have g2z : g 2 = 0 := by linear_combination b * e3 - a * c * e2 - g 2 * hab
      ext i
      fin_cases i <;> simp [g0z, g1z, g2z, g3z]
    exact hinj
  have hRunit : IsUnit R := Matrix.mulVec_injective_iff_isUnit.1 hRinj
  have hxx : x *ᵥ (x *ᵥ v) = c • v := by
    rw [Matrix.mulVec_mulVec, hx, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hxw' : x *ᵥ (w *ᵥ v) = c • (y *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hxw, Matrix.smul_mulVec]
  have hyy : y *ᵥ (y *ᵥ v) = m • v := by
    rw [Matrix.mulVec_mulVec, hy, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hyx' : y *ᵥ (x *ᵥ v) = -(w *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hyx, Matrix.neg_mulVec]
  have hyw' : y *ᵥ (w *ᵥ v) = -(m • (x *ᵥ v)) := by
    rw [Matrix.mulVec_mulVec, hyw, Matrix.neg_mulVec, Matrix.smul_mulVec]
  have hMR : ∀ (M : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4),
      (M * R) i j = (M *ᵥ (![v, x *ᵥ v, y *ᵥ v, w *ᵥ v] j)) i := by
    intro M i j
    simp [R, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hRN : ∀ (N : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4),
      (R * N) i j = ∑ k, (![v, x *ᵥ v, y *ᵥ v, w *ᵥ v] k) i * N k j := by
    intro N i j
    simp [R, Matrix.mul_apply]
  refine ⟨R, hRunit, ?_, ?_⟩
  · ext i j
    rw [hMR, hRN]
    fin_cases j
    · simp [Fin.sum_univ_four, Xr]
    · simp [Fin.sum_univ_four, Xr, hxx, mul_comm]
    · simp [Fin.sum_univ_four, Xr, hxyv]
    · simp [Fin.sum_univ_four, Xr, hxw', mul_comm]
  · ext i j
    rw [hMR, hRN]
    fin_cases j
    · simp [Fin.sum_univ_four, Yr]
    · simp [Fin.sum_univ_four, Yr, hyx']
    · simp [Fin.sum_univ_four, Yr, hyy, mul_comm]
    · simp [Fin.sum_univ_four, Yr, hyw', mul_comm]

end GenLocL4Q

end CFSG.GH74.Generic.BProg.B2
