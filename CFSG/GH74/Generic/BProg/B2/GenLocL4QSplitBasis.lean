module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4QSplit

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.ComponentClassification Module

namespace GenLocL4Q

variable {F : Type} [Field F]

theorem pair_indep {c : F} (hc : ¬ IsSquare c) {x : Matrix (Fin 4) (Fin 4) F} (hx : x * x = c • 1)
    {u : Fin 4 → F} (hu : u ≠ 0) (g0 g1 : F) (h : g0 • u + g1 • (x *ᵥ u) = 0) : g0 = 0 ∧ g1 = 0 := by
  have hxx : x *ᵥ (x *ᵥ u) = c • u := by
    rw [Matrix.mulVec_mulVec, hx, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h1 : g0 • (x *ᵥ u) + (g1 * c) • u = 0 := by
    have := congrArg (fun w => x *ᵥ w) h
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hxx, Matrix.mulVec_zero] at this
    rw [← this]; module
  have h2 : (g0 * g0 - c * (g1 * g1)) • u = 0 := by
    have e : (g0 * g0 - c * (g1 * g1)) • u =
        g0 • (g0 • u + g1 • (x *ᵥ u)) - g1 • (g0 • (x *ᵥ u) + (g1 * c) • u) := by
      module
    rw [e, h, h1]; simp
  have h3 : g0 * g0 - c * (g1 * g1) = 0 := (smul_eq_zero.1 h2).resolve_right hu
  have hg1 : g1 = 0 := by
    by_contra hne
    apply hc
    refine ⟨g0 / g1, ?_⟩
    field_simp
    linear_combination (-1 : F) * h3
  refine ⟨?_, hg1⟩
  rw [hg1, zero_smul, add_zero] at h
  exact (smul_eq_zero.1 h).resolve_right hu

theorem eq_zero_of_mulVec_eq_zero' {M : Matrix (Fin 4) (Fin 4) F} (h : ∀ u : Fin 4 → F, M *ᵥ u = 0) : M = 0 := by
  ext i j
  have := congr_fun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem exists_eigvec {z : Matrix (Fin 4) (Fin 4) F} (hz : z * z = 1) (ε : F) (hε : ε = 1 ∨ ε = -1)
    (hzn : ∀ l : F, z ≠ l • 1) :
    ∃ e : Fin 4 → F, e ≠ 0 ∧ z *ᵥ e = ε • e := by
  by_contra hcon
  have hcon' : ∀ e : Fin 4 → F, e ≠ 0 → z *ᵥ e ≠ ε • e := fun e he h => hcon ⟨e, he, h⟩
  have hall : ∀ u : Fin 4 → F, (z + ε • 1) *ᵥ u = 0 := by
    intro u
    by_contra hne
    apply hcon' ((z + ε • 1) *ᵥ u) hne
    rw [Matrix.mulVec_mulVec]
    have : z * (z + ε • 1) = ε • (z + ε • 1) := by
      rw [mul_add, hz, mul_smul_comm, mul_one, smul_add, smul_smul]
      rcases hε with h | h <;> subst h <;> simp [add_comm]
    rw [this, Matrix.smul_mulVec]
  have h0 := eq_zero_of_mulVec_eq_zero' hall
  apply hzn (-ε)
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left (by simpa using h0)

theorem exists_split_basis [Finite F] (hF : ringChar F ≠ 2) {c m : F} (hc : ¬ IsSquare c) (hm : m ≠ 0)
    {x y z : Matrix (Fin 4) (Fin 4) F} (hx : x * x = c • 1) (hy : y * y = m • 1) (hz : z * z = 1)
    (hxy : x * y = -(y * x)) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (hzn : ∀ l : F, z ≠ l • 1) :
    ∃ (p s' : F) (R : Matrix (Fin 4) (Fin 4) F), IsUnit R ∧ p ^ 2 - c * s' ^ 2 = m ∧
      x * R = R * bd (C2 c) (C2 c) ∧ y * R = R * bd (Y1 c p s') (Y1 c p s') ∧
      z * R = R * bd 1 (-1) := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hc0 : c ≠ 0 := by rintro rfl; exact hc ⟨0, by simp⟩
  obtain ⟨e, he0, hze⟩ := exists_eigvec hz 1 (Or.inl rfl) hzn
  obtain ⟨f0, hf00, hzf0⟩ := exists_eigvec hz (-1) (Or.inr rfl) hzn
  rw [one_smul] at hze
  rw [neg_smul, one_smul] at hzf0
  set g : Module.End F (Fin 4 → F) := Matrix.toLin' z with hg
  have hgg : g * g = 1 := by
    rw [hg, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hz, Matrix.toLin'_one]; rfl
  have hC := isCompl_ker_sq_one h2 hgg
  set Vp := LinearMap.ker (g - 1) with hVp
  set Vm := LinearMap.ker (g + 1) with hVm
  have hmemp : ∀ u, u ∈ Vp ↔ z *ᵥ u = u := fun u => by
    rw [hVp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]; simp [hg]
  have hmemm : ∀ u, u ∈ Vm ↔ z *ᵥ u = -u := fun u => by
    rw [hVm, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]; simp [hg]
  have hdim : finrank F Vp + finrank F Vm = 4 := by
    rw [Submodule.finrank_add_eq_of_isCompl hC]; simp
  have hxmul : ∀ u : Fin 4 → F, x *ᵥ (x *ᵥ u) = c • u := fun u => by
    rw [Matrix.mulVec_mulVec, hx, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hxz' : ∀ u : Fin 4 → F, z *ᵥ (x *ᵥ u) = x *ᵥ (z *ᵥ u) := fun u => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hxz]
  have hyz' : ∀ u : Fin 4 → F, z *ᵥ (y *ᵥ u) = y *ᵥ (z *ᵥ u) := fun u => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hyz]
  have hxe : x *ᵥ e ∈ Vp := (hmemp _).2 (by rw [hxz', hze])
  have hep : e ∈ Vp := (hmemp _).2 hze
  have hxf : x *ᵥ f0 ∈ Vm := (hmemm _).2 (by rw [hxz', hzf0, Matrix.mulVec_neg])
  have hfm : f0 ∈ Vm := (hmemm _).2 hzf0
  have hindE : LinearIndependent F ![e, x *ᵥ e] :=
    LinearIndependent.pair_iff.2 (fun g0 g1 h => pair_indep hc hx he0 g0 g1 h)
  have hindF : LinearIndependent F ![f0, x *ᵥ f0] :=
    LinearIndependent.pair_iff.2 (fun g0 g1 h => pair_indep hc hx hf00 g0 g1 h)
  have hspE : Submodule.span F (Set.range ![e, x *ᵥ e]) ≤ Vp := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hep
    · exact hxe
  have hspF : Submodule.span F (Set.range ![f0, x *ᵥ f0]) ≤ Vm := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hfm
    · exact hxf
  have hfE : finrank F (Submodule.span F (Set.range ![e, x *ᵥ e])) = 2 := by
    rw [finrank_span_eq_card hindE]; simp
  have hfF : finrank F (Submodule.span F (Set.range ![f0, x *ᵥ f0])) = 2 := by
    rw [finrank_span_eq_card hindF]; simp
  have h1 := Submodule.finrank_mono hspE
  have h2' := Submodule.finrank_mono hspF
  have hVp2 : finrank F Vp = 2 := by omega
  have hVm2 : finrank F Vm = 2 := by omega
  have hspEq : Submodule.span F (Set.range ![e, x *ᵥ e]) = Vp :=
    Submodule.eq_of_le_of_finrank_eq hspE (by rw [hfE, hVp2])
  have hye : y *ᵥ e ∈ Vp := (hmemp _).2 (by rw [hyz', hze])
  rw [← hspEq, Submodule.mem_span_range_iff_exists_fun] at hye
  obtain ⟨cf, hcf⟩ := hye
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hcf
  set p : F := cf 0 with hp
  set s' : F := cf 1 with hs'
  have hye' : y *ᵥ e = p • e + s' • (x *ᵥ e) := hcf.symm
  have hyx : ∀ u : Fin 4 → F, y *ᵥ (x *ᵥ u) = -(x *ᵥ (y *ᵥ u)) := fun u => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.neg_mulVec]
    congr 1
    have : y * x = -(x * y) := by rw [hxy]; simp
    exact this
  have hymul : ∀ u : Fin 4 → F, y *ᵥ (y *ᵥ u) = m • u := fun u => by
    rw [Matrix.mulVec_mulVec, hy, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hyxe : y *ᵥ (x *ᵥ e) = -(p • (x *ᵥ e) + (s' * c) • e) := by
    rw [hyx, hye', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hxmul]
    congr 1
    module
  have hpm : p ^ 2 - c * s' ^ 2 = m := by
    have h3 : y *ᵥ (y *ᵥ e) = (p ^ 2 - c * s' ^ 2) • e := by
      conv_lhs => rw [hye']
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hyxe, hye']
      module
    rw [hymul] at h3
    have : (m - (p ^ 2 - c * s' ^ 2)) • e = 0 := by rw [sub_smul, h3, sub_self]
    have h4 := (smul_eq_zero.1 this).resolve_right he0
    linear_combination (-1 : F) * h4
  obtain ⟨f, hfm', hf0, hyf⟩ : ∃ f : Fin 4 → F, f ∈ Vm ∧ f ≠ 0 ∧ y *ᵥ f = p • f + s' • (x *ᵥ f) := by
    have hex : ∃ u ∈ Vm, y *ᵥ u + p • u - s' • (x *ᵥ u) ≠ 0 := by
      by_contra hcon
      have hall : ∀ u ∈ Vm, y *ᵥ u + p • u - s' • (x *ᵥ u) = 0 := fun u hu => by
        by_contra hne; exact hcon ⟨u, hu, hne⟩
      have hA := hall f0 hfm
      have hB := hall (x *ᵥ f0) hxf
      have hyf0 : y *ᵥ f0 = -(p • f0) + s' • (x *ᵥ f0) := by
        calc y *ᵥ f0 = (y *ᵥ f0 + p • f0 - s' • (x *ᵥ f0)) + (-(p • f0) + s' • (x *ᵥ f0)) := by module
          _ = _ := by rw [hA, zero_add]
      rw [hyx, hyf0, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, Matrix.mulVec_smul, hxmul] at hB
      have key : (-(2 * s' * c)) • f0 + (2 * p) • (x *ᵥ f0) = 0 := by
        rw [← hB]; module
      obtain ⟨k1, k2⟩ := pair_indep hc hx hf00 _ _ key
      have hp0 : p = 0 := by
        rcases mul_eq_zero.1 k2 with h | h
        · exact absurd h h2
        · exact h
      have hs0 : s' = 0 := by
        have : 2 * s' * c = 0 := by linear_combination (-1 : F) * k1
        rcases mul_eq_zero.1 this with h | h
        · rcases mul_eq_zero.1 h with h' | h'
          · exact absurd h' h2
          · exact h'
        · exact absurd h hc0
      apply hm
      rw [← hpm, hp0, hs0]; ring
    obtain ⟨u, hu, hne⟩ := hex
    refine ⟨y *ᵥ u + p • u - s' • (x *ᵥ u), ?_, hne, ?_⟩
    · rw [hmemm]
      have hzu : z *ᵥ u = -u := (hmemm u).1 hu
      rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hyz', hxz', hzu]
      simp only [Matrix.mulVec_neg, smul_neg]
      module
    · have e : y *ᵥ (y *ᵥ u + p • u - s' • (x *ᵥ u)) - p • (y *ᵥ u + p • u - s' • (x *ᵥ u)) -
          s' • (x *ᵥ (y *ᵥ u + p • u - s' • (x *ᵥ u))) = (m - (p ^ 2 - c * s' ^ 2)) • u := by
        simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hymul, hxmul, hyx]
        module
      rw [hpm, sub_self, zero_smul] at e
      exact (eq_add_of_sub_eq (sub_eq_zero.1 e)).trans (add_comm _ _)
  have hzf : z *ᵥ f = -f := (hmemm _).1 hfm'
  have hxf2 : x *ᵥ f ∈ Vm := (hmemm _).2 (by rw [hxz', hzf, Matrix.mulVec_neg])
  let R : Matrix (Fin 4) (Fin 4) F := Matrix.of fun i j => (![e, x *ᵥ e, f, x *ᵥ f] j) i
  have hR : ∀ g : Fin 4 → F, R *ᵥ g =
      g 0 • e + g 1 • (x *ᵥ e) + g 2 • f + g 3 • (x *ᵥ f) := by
    intro g
    ext i
    simp [R, Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm]
  have hRinj : Function.Injective R.mulVec := by
    have hinj : Function.Injective (Matrix.mulVecLin R) := by
      rw [injective_iff_map_eq_zero]
      intro g hg
      have hg' : R *ᵥ g = 0 := hg
      rw [hR] at hg'
      have ha : g 0 • e + g 1 • (x *ᵥ e) ∈ Vp :=
        Vp.add_mem (Vp.smul_mem _ hep) (Vp.smul_mem _ hxe)
      have hb : g 2 • f + g 3 • (x *ᵥ f) ∈ Vm :=
        Vm.add_mem (Vm.smul_mem _ hfm') (Vm.smul_mem _ hxf2)
      have hsum : (g 0 • e + g 1 • (x *ᵥ e)) + (g 2 • f + g 3 • (x *ᵥ f)) = 0 := by
        rw [← hg']; module
      have ha' : g 0 • e + g 1 • (x *ᵥ e) ∈ Vm := by
        have : g 0 • e + g 1 • (x *ᵥ e) = -(g 2 • f + g 3 • (x *ᵥ f)) := eq_neg_of_add_eq_zero_left hsum
        rw [this]; exact Vm.neg_mem hb
      have ha0 : g 0 • e + g 1 • (x *ᵥ e) = 0 := (Submodule.disjoint_def.1 hC.1) _ ha ha'
      have hb0 : g 2 • f + g 3 • (x *ᵥ f) = 0 := by rw [ha0, zero_add] at hsum; exact hsum
      obtain ⟨k0, k1⟩ := pair_indep hc hx he0 _ _ ha0
      obtain ⟨k2, k3⟩ := pair_indep hc hx hf0 _ _ hb0
      ext i
      fin_cases i <;> simp [k0, k1, k2, k3]
    exact hinj
  have hRunit : IsUnit R := Matrix.mulVec_injective_iff_isUnit.1 hRinj
  have hMR : ∀ (M : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4),
      (M * R) i j = (M *ᵥ (![e, x *ᵥ e, f, x *ᵥ f] j)) i := by
    intro M i j
    simp [R, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hRN : ∀ (N : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4),
      (R * N) i j = ∑ k, (![e, x *ᵥ e, f, x *ᵥ f] k) i * N k j := by
    intro N i j
    simp [R, Matrix.mul_apply]
  have hyxe : y *ᵥ (x *ᵥ e) = -(p • (x *ᵥ e) + (s' * c) • e) := by
    rw [hyx, hye', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hxmul]
    congr 1
    module
  have hyxf : y *ᵥ (x *ᵥ f) = -(p • (x *ᵥ f) + (s' * c) • f) := by
    rw [hyx, hyf, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hxmul]
    congr 1
    module
  refine ⟨p, s', R, hRunit, hpm, ?_, ?_, ?_⟩
  · ext i j
    rw [hMR, hRN]
    fin_cases j
    · simp [Fin.sum_univ_four, bd, C2]
    · simp [Fin.sum_univ_four, bd, C2, hxmul, mul_comm]
    · simp [Fin.sum_univ_four, bd, C2]
    · simp [Fin.sum_univ_four, bd, C2, hxmul, mul_comm]
  · ext i j
    rw [hMR, hRN]
    fin_cases j
    · simp [Fin.sum_univ_four, bd, Y1, hye']; ring
    · simp [Fin.sum_univ_four, bd, Y1, hyxe]; ring
    · simp [Fin.sum_univ_four, bd, Y1, hyf]; ring
    · simp [Fin.sum_univ_four, bd, Y1, hyxf]; ring
  · ext i j
    rw [hMR, hRN]
    fin_cases j
    · simp [Fin.sum_univ_four, bd, hze]
    · simp [Fin.sum_univ_four, bd, hxz', hze]
    · simp [Fin.sum_univ_four, bd, hzf]
    · simp [Fin.sum_univ_four, bd, hxz', hzf, Matrix.mulVec_neg]

theorem top_of_conj {R : Matrix (Fin 4) (Fin 4) F} (hR : IsUnit R)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (h : (Γ.comap (CatalogueBHigherLinearAction.slConjugation 4 F hR.unit).toMonoidHom) = ⊤) : Γ = ⊤ := by
  rw [eq_top_iff]
  intro g _
  let φ : MulAut (Matrix.SpecialLinearGroup (Fin 4) F) :=
    CatalogueBHigherLinearAction.slConjugation 4 F hR.unit
  have hmem : φ.symm g ∈ Γ.comap φ.toMonoidHom := h ▸ Subgroup.mem_top _
  have : φ (φ.symm g) ∈ Γ := hmem
  rwa [MulEquiv.apply_symm_apply] at this

theorem top_of_rank3_split [Finite F] (hF : ringChar F ≠ 2) {c m s : F} (hc : ¬ IsSquare c) (hm : m ≠ 0)
    (hs : s ≠ 0) {x y z : Matrix (Fin 4) (Fin 4) F} (hx : x * x = c • 1) (hy : y * y = m • 1)
    (hz : z * z = (s * s) • 1) (hxy : x * y = -(y * x)) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (hzn : ∀ l : F, z ≠ l • 1) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (H1 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * x = x * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * y = y * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H2 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * x = x * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (y * z) = (y * z) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H3 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * y = y * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (x * z) = (x * z) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H4 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * (x * y) = (x * y) * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (x * z) = (x * z) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ) :
    Γ = ⊤ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hc0 : c ≠ 0 := by rintro rfl; exact hc ⟨0, by simp⟩
  set z' : Matrix (Fin 4) (Fin 4) F := s⁻¹ • z with hz'
  have hzz' : z' * z' = 1 := by
    rw [hz', smul_mul_assoc, Matrix.mul_smul, hz, smul_smul, smul_smul]
    have : s⁻¹ * s⁻¹ * (s * s) = 1 := by field_simp
    rw [this, one_smul]
  have hxz'' : x * z' = z' * x := by rw [hz', Matrix.mul_smul, smul_mul_assoc, hxz]
  have hyz'' : y * z' = z' * y := by rw [hz', Matrix.mul_smul, smul_mul_assoc, hyz]
  have hzn' : ∀ l : F, z' ≠ l • 1 := by
    intro l hl
    apply hzn (s * l)
    have : z = s • z' := by rw [hz', smul_smul, mul_inv_cancel₀ hs, one_smul]
    rw [this, hl, smul_smul]
  obtain ⟨p, s', R, hRu, hpm, hxR, hyR, hzR⟩ :=
    exists_split_basis hF hc hm hx hy hzz' hxy hxz'' hyz'' hzn'
  have hzR' : z * R = R * (s • bd 1 (-1)) := by
    have : z = s • z' := by rw [hz', smul_smul, mul_inv_cancel₀ hs, one_smul]
    rw [this, smul_mul_assoc, hzR, Matrix.mul_smul]
  have hRu' : (hRu.unit : Matrix (Fin 4) (Fin 4) F) = R := hRu.unit_spec
  have inter_mul : ∀ {a b A B : Matrix (Fin 4) (Fin 4) F}, a * R = R * A → b * R = R * B →
      (a * b) * R = R * (A * B) := fun {a b A B} ha hb => by
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  have hyzR : (y * z) * R = R * (s • bd (Y1 c p s') (-(Y1 c p s'))) := by
    have := inter_mul hyR hzR'
    rw [this, Matrix.mul_smul, bd_mul]
    simp
  have hxzR : (x * z) * R = R * (s • bd (C2 c) (-(C2 c))) := by
    have := inter_mul hxR hzR'
    rw [this, Matrix.mul_smul, bd_mul]
    simp
  have hxyR : (x * y) * R = R * bd (C2 c * Y1 c p s') (C2 c * Y1 c p s') := by
    have := inter_mul hxR hyR
    rw [this, bd_mul]
  have hsm : ∀ (g K : Matrix (Fin 4) (Fin 4) F), g * K = K * g → g * (s • K) = (s • K) * g := by
    intro g K h
    rw [Matrix.mul_smul, smul_mul_assoc, h]
  have hm' : p ^ 2 - c * s' ^ 2 ≠ 0 := by rw [hpm]; exact hm
  apply top_of_conj hRu
  refine top_of_split_model h2 hc0 hm' _ ?_ ?_ ?_ ?_
  · intro g hg1 hg2
    exact H1 _ (slConj_commute (by rw [hRu']; exact hxR) g hg1)
      (slConj_commute (by rw [hRu']; exact hyR) g hg2)
  · intro g hg1 hg2
    exact H2 _ (slConj_commute (by rw [hRu']; exact hxR) g hg1)
      (slConj_commute (by rw [hRu']; exact hyzR) g (hsm _ _ hg2))
  · intro g hg1 hg2
    exact H3 _ (slConj_commute (by rw [hRu']; exact hyR) g hg1)
      (slConj_commute (by rw [hRu']; exact hxzR) g (hsm _ _ hg2))
  · intro g hg1 hg2
    exact H4 _ (slConj_commute (by rw [hRu']; exact hxyR) g hg1)
      (slConj_commute (by rw [hRu']; exact hxzR) g (hsm _ _ hg2))

end GenLocL4Q

end CFSG.GH74.Generic.BProg.B2
