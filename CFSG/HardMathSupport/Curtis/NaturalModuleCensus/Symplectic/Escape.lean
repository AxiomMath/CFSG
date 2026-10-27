module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Basic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.Adapters.SpecialLinearPerfect

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {r : ℕ} {K : Type} [Field K]

theorem exists_statedSp_pair {x y x' y' : Fin r ⊕ Fin r → K}
    (h : pairedSympForm K r x y = 1) (h' : pairedSympForm K r x' y' = 1) :
    ∃ g : StatedSp r K, spMat g *ᵥ x = x' ∧ spMat g *ᵥ y = y' := by
  obtain ⟨φ, hφ, hφy, hφx⟩ := exists_isometry_apply_pair (B := pairedSympForm K r)
    SymplecticFlag.pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate (e := y)
    (f := x) (e' := y') (f' := x') h h'
  have hM := (map_isometryGroup_eq_statedSp (K := K) (r := r)) ▸
    Subgroup.mem_map_of_mem (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
      (Pi.basisFun K (Fin r ⊕ Fin r))).toMonoidHom hφ
  refine ⟨⟨_, hM⟩, ?_, ?_⟩
  · have := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec
      (Pi.basisFun K (Fin r ⊕ Fin r)) φ x
    simpa [hφx] using this
  · have := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec
      (Pi.basisFun K (Fin r ⊕ Fin r)) φ y
    simpa [hφy] using this


theorem pairedSympForm_single_inr_right (j : Fin r) (u : Fin r ⊕ Fin r → K) :
    pairedSympForm K r u (Pi.single (Sum.inr j) 1) = u (Sum.inl j) := by
  rw [pairedSympForm_apply]
  simp [dotProduct, Pi.single_apply]

theorem exists_pairedSympForm_eq_one {a : Fin r ⊕ Fin r → K} (ha0 : a ≠ 0) :
    ∃ z, pairedSympForm K r a z = 1 := by
  by_contra hcon
  push Not at hcon
  apply ha0
  refine SymplecticFlag.pairedSympForm_nondegenerate.1 a fun y => ?_
  by_contra hy
  apply hcon ((pairedSympForm K r a y)⁻¹ • y)
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]

theorem exists_fixed_dual {p : ℕ} {v : StatedSp r K} (hvp : v ^ p = 1) (hp : (p : K) ≠ 0)
    {a z : Fin r ⊕ Fin r → K} (hva : spMat v *ᵥ a = a) (hz : pairedSympForm K r a z = 1) :
    ∃ b0, spMat v *ᵥ b0 = b0 ∧ pairedSympForm K r a b0 = 1 := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hpow : ∀ j : ℕ, spMat v ^ j *ᵥ a = a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', ← mulVec_mulVec, ih, hva]
  refine ⟨(p : K)⁻¹ • ∑ j ∈ Finset.range p, spMat v ^ j *ᵥ z, ?_, ?_⟩
  · rw [mulVec_smul, mulVec_sum]
    congr 1
    have hf : spMat v ^ p *ᵥ z = spMat v ^ 0 *ᵥ z := by
      simp only [← spMat_pow, hvp, spMat_one, pow_zero]
    have h1 := Finset.sum_range_succ (fun j => spMat v ^ j *ᵥ z) p
    have h2 := Finset.sum_range_succ' (fun j => spMat v ^ j *ᵥ z) p
    have h3 : ∑ j ∈ Finset.range p, spMat v *ᵥ (spMat v ^ j *ᵥ z) =
        ∑ j ∈ Finset.range p, spMat v ^ (j + 1) *ᵥ z := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mulVec_mulVec, pow_succ']
    rw [h3]
    have := h1.symm.trans h2
    rw [hf] at this
    exact (add_right_cancel this).symm
  · rw [map_smul, map_sum, smul_eq_mul]
    have : ∀ j ∈ Finset.range p, pairedSympForm K r a (spMat v ^ j *ᵥ z) = 1 := by
      intro j _
      have := pairedSympForm_spMat_mulVec (v ^ j) a z
      rw [spMat_pow, hpow j] at this
      rw [this, hz]
    rw [Finset.sum_congr rfl this]
    simp [hp]


theorem commute_lam_of_fixes (i : Fin r) {M : StatedSp r K}
    (he : spMat M *ᵥ Pi.single (Sum.inl i) 1 = Pi.single (Sum.inl i) 1)
    (hf : spMat M *ᵥ Pi.single (Sum.inr i) 1 = Pi.single (Sum.inr i) 1)
    (s : Matrix.SpecialLinearGroup (Fin 2) K) : Commute M (lam i s) := by
  have hl : ∀ u, (spMat M *ᵥ u) (Sum.inl i) = u (Sum.inl i) := by
    intro u
    rw [← pairedSympForm_single_inr_right i (spMat M *ᵥ u), ← pairedSympForm_single_inr_right i u]
    conv_lhs => rw [← hf]
    exact pairedSympForm_spMat_mulVec M u _
  have hr : ∀ u, (spMat M *ᵥ u) (Sum.inr i) = u (Sum.inr i) := by
    intro u
    rw [← pairedSympForm_single_inl i (spMat M *ᵥ u), ← pairedSympForm_single_inl i u]
    conv_lhs => rw [← he]
    exact pairedSympForm_spMat_mulVec M _ u
  have hS : IsSupp {x : Fin r ⊕ Fin r | x ≠ Sum.inl i ∧ x ≠ Sum.inr i} (spMat M) := by
    intro x y hxy
    have hcol : ∀ y, spMat M x y = (spMat M *ᵥ Pi.single y 1) x := by
      intro y; rw [mulVec_single_one]; rfl
    have hx : x = Sum.inl i ∨ x = Sum.inr i → spMat M x y = (1 : Matrix _ _ K) x y := by
      intro hx
      rw [hcol]
      rcases hx with rfl | rfl
      · rw [hl]; simp [Pi.single_apply, one_apply, eq_comm]
      · rw [hr]; simp [Pi.single_apply, one_apply, eq_comm]
    have hy : y = Sum.inl i ∨ y = Sum.inr i → spMat M x y = (1 : Matrix _ _ K) x y := by
      intro hy
      rw [hcol]
      rcases hy with rfl | rfl
      · rw [he]; simp [Pi.single_apply, one_apply]
      · rw [hf]; simp [Pi.single_apply, one_apply]
    rcases hxy with h | h
    · exact hx (by by_contra hc; push Not at hc; exact h ⟨hc.1, hc.2⟩)
    · exact hy (by by_contra hc; push Not at hc; exact h ⟨hc.1, hc.2⟩)
  refine statedSp_commute (hS.commute (isSupp_lam i s) ?_)
  rw [Set.disjoint_left]
  rintro x ⟨h1, h2⟩ hx
  rcases hx with rfl | rfl
  · exact h1 rfl
  · exact h2 rfl


@[expose] def lowerTransvection (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_lowerTransvection :
    (lowerTransvection K : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] := rfl

theorem lam_transvection_mulVec (i : Fin r) :
    spMat (lam i (lowerTransvection K)) *ᵥ Pi.single (Sum.inl i) 1 =
      Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1 := by
  rw [spMat, coe_lam, coe_lowerTransvection, mulVec_single_one]
  funext x
  by_cases h1 : x = Sum.inl i
  · subst h1
    simp [Matrix.col_apply, pairMat_apply_fst]
  by_cases h2 : x = Sum.inr i
  · subst h2
    simp [Matrix.col_apply, pairMat_apply_snd Sum.inl_ne_inr]
  · simp [Matrix.col_apply, pairMat_apply_of_ne h1 h2, one_apply, h1, h2]

theorem exists_perfect_escape [Finite K] (hK : 4 ≤ Nat.card K) {p : ℕ} {v : StatedSp r K}
    (hvp : v ^ p = 1) (hp : (p : K) ≠ 0) {a : Fin r ⊕ Fin r → K} (ha0 : a ≠ 0)
    (hva : spMat v *ᵥ a = a) :
    ∃ (W : Subgroup (StatedSp r K)) (b : Fin r ⊕ Fin r → K),
      W ≤ Subgroup.centralizer ({v} : Set (StatedSp r K)) ∧ ⁅W, W⁆ = W ∧
        pairedSympForm K r a b = 1 ∧ ∃ w ∈ W, spMat w *ᵥ a = a + b := by
  obtain ⟨x0, -⟩ := Function.ne_iff.1 ha0
  obtain ⟨i0, -⟩ : ∃ i : Fin r, True := by
    rcases x0 with i | i
    · exact ⟨i, trivial⟩
    · exact ⟨i, trivial⟩
  obtain ⟨z, hz⟩ := exists_pairedSympForm_eq_one ha0
  obtain ⟨b0, hb0v, hab0⟩ := exists_fixed_dual hvp hp hva hz
  obtain ⟨g, hge, hgf⟩ := exists_statedSp_pair (r := r) (K := K)
    (pairedSympForm_single i0) hab0
  have hginv : ∀ u, spMat g⁻¹ *ᵥ (spMat g *ᵥ u) = u := by
    intro u; rw [mulVec_mulVec, spMat_inv_mul, one_mulVec]
  have hginv' : ∀ u, spMat g *ᵥ (spMat g⁻¹ *ᵥ u) = u := by
    intro u; rw [mulVec_mulVec, spMat_mul_inv, one_mulVec]
  have hcomm : ∀ s, Commute (g⁻¹ * v * g) (lam i0 s) := by
    intro s
    refine commute_lam_of_fixes i0 ?_ ?_ s
    · rw [spMat_mul, spMat_mul, ← mulVec_mulVec, ← mulVec_mulVec, hge, hva, ← hge, hginv]
    · rw [spMat_mul, spMat_mul, ← mulVec_mulVec, ← mulVec_mulVec, hgf, hb0v, ← hgf, hginv]
  have htop : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ :=
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK).commutator_eq_top
  refine ⟨(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)).map
    ((MulAut.conj g).toMonoidHom.comp (lam i0)), b0, ?_, ?_, hab0,
    g * lam i0 (lowerTransvection K) * g⁻¹, ⟨lowerTransvection K, trivial, rfl⟩, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := (hcomm s).eq
    simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass]
    calc h * (g * lam i0 s * g⁻¹) = g * ((g⁻¹ * h * g) * lam i0 s) * g⁻¹ := by group
      _ = g * (lam i0 s * (g⁻¹ * h * g)) * g⁻¹ := by rw [this]
      _ = _ := by group
  · rw [← Subgroup.map_commutator, htop]
  · rw [spMat_mul, spMat_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    have h2 : spMat g⁻¹ *ᵥ a = Pi.single (Sum.inl i0) 1 := by rw [← hge, hginv]
    rw [h2, lam_transvection_mulVec, mulVec_add, hge, hgf]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
