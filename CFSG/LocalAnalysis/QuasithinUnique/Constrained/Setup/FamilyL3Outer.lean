module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyInnerAction
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddHigherLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyWeights
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Sym

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Assembly.LowTwoRank

section Transport

variable {X : Type*} [Group X] {K : Type} [Field K]

structure CoverData3 (K : Type) [Field K] (L : Subgroup X) where
  φ : SpecialLinearGroup (Fin 3) K →* ↥L
  surj : Function.Surjective φ
  ker_central : ∀ g ∈ φ.ker, g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)
  ψ : (↥L ⧸ Subgroup.center ↥L) ≃* projectiveSL 3 K
  hψ : ∀ g, ψ (QuotientGroup.mk (φ g)) = proj 3 K g

variable {L : Subgroup X} (D : CoverData3 K L)

@[expose] noncomputable def CoverData3.beta {g : X} (hg : g ∈ Subgroup.normalizer (L : Set X)) :
    MulAut (projectiveSL 3 K) :=
  MulAut.congr D.ψ (normConjQ hg)

theorem CoverData3.beta_proj {g : X} (hg : g ∈ Subgroup.normalizer (L : Set X))
    (x : SpecialLinearGroup (Fin 3) K) :
    D.beta hg (proj 3 K x) = D.ψ (QuotientGroup.mk (normConj hg (D.φ x))) := by
  rw [← D.hψ x]
  simp [CoverData3.beta, normConjQ_mk]

theorem CoverData3.beta_mul {g h : X} (hg : g ∈ Subgroup.normalizer (L : Set X))
    (hh : h ∈ Subgroup.normalizer (L : Set X)) :
    D.beta (Subgroup.mul_mem _ hg hh) = D.beta hg * D.beta hh := by
  unfold CoverData3.beta
  rw [normConjQ_mul, map_mul]

theorem CoverData3.beta_sq {g : X} (hg : g ∈ Subgroup.normalizer (L : Set X)) (hg2 : g * g = 1) :
    D.beta hg * D.beta hg = 1 := by
  unfold CoverData3.beta
  rw [← map_mul, normConjQ_sq hg hg2, map_one]

end Transport

section Outer

variable {W : Type} [CommGroup W] {K : Type} [Field K]
  {L : Subgroup (MulAut W)} (D : CoverData3 K L)

theorem CoverData3.conj_eq (hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K))
    {b : MulAut W} (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (τ : MulAut (SpecialLinearGroup (Fin 3) K)) (h : D.beta hb = descendAut 3 K τ)
    (x : SpecialLinearGroup (Fin 3) K) :
    b * ((D.φ x : ↥L) : MulAut W) * b⁻¹ = ((D.φ (τ x) : ↥L) : MulAut W) := by
  have key : ((normConj hb : MulAut ↥L) : ↥L →* ↥L).comp D.φ =
      D.φ.comp (τ : SpecialLinearGroup (Fin 3) K →* SpecialLinearGroup (Fin 3) K) := by
    refine hom_eq_of_central_diff hperf _ _ fun x => ?_
    have h1 := D.beta_proj hb x
    rw [h, descendAut_proj, ← D.hψ (τ x)] at h1
    have h2 := D.ψ.injective h1
    exact QuotientGroup.eq.1 h2.symm
  have := DFunLike.congr_fun key x
  exact congrArg (fun z : ↥L => (z : MulAut W)) this

open CFSG.ComponentClassification

theorem conjAut_scalar (c : Kˣ) : conjAut 3 K (GeneralLinearGroup.scalar (Fin 3) c) = 1 := by
  unfold conjAut
  rw [MonoidHom.comp_apply, CatalogueBHigherLinearAction.slConjugation_scalar, map_one]

theorem exists_sl_of_sq_scalar [Finite K] (A : GL (Fin 3) K) (c : Kˣ)
    (hAA : (A : Matrix (Fin 3) (Fin 3) K) * A = (c : K) • 1) :
    ∃ Asl : SpecialLinearGroup (Fin 3) K, conjAut 3 K A = descendAut 3 K (MulAut.conj Asl) := by
  set d := (A : Matrix (Fin 3) (Fin 3) K).det with hd
  have hd0 : d ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)).ne_zero
  have hdc : d ^ 2 = (c : K) ^ 3 := by
    have := congrArg Matrix.det hAA
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one] at this
    simpa [pow_two] using this
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  set s : K := d / c with hs
  have hs0 : s ≠ 0 := div_ne_zero hd0 hc0
  have hs3 : s ^ 3 = d := by
    rw [hs, div_pow, ← hdc]
    field_simp
  have hdetA' : ((s⁻¹ : K) • (A : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
    rw [Matrix.det_smul, ← hd]
    simp only [Fintype.card_fin, inv_pow, hs3]
    exact inv_mul_cancel₀ hd0
  let Asl : SpecialLinearGroup (Fin 3) K := ⟨(s⁻¹ : K) • (A : Matrix (Fin 3) (Fin 3) K), hdetA'⟩
  have hscalM : ∀ u : Kˣ, ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (u : K) • (1 : Matrix (Fin 3) (Fin 3) K) := fun u => by
    rw [smul_one_eq_diagonal]; rfl
  have hAscal : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 s hs0) *
      Matrix.SpecialLinearGroup.toGL Asl := by
    apply Units.ext
    rw [Units.val_mul, hscalM]
    show (A : Matrix (Fin 3) (Fin 3) K) = (s • (1 : Matrix (Fin 3) (Fin 3) K)) *
      ((s⁻¹ : K) • (A : Matrix (Fin 3) (Fin 3) K))
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hs0, one_smul]
  refine ⟨Asl, ?_⟩
  have hsl : CatalogueBHigherLinearAction.slConjugation 3 K (Matrix.SpecialLinearGroup.toGL Asl) =
      MulAut.conj Asl := by
    ext g i j
    rw [CatalogueBHigherLinearAction.slConjugation_matrix, MulAut.conj_apply,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    congr 3
  rw [hAscal, map_mul, conjAut_scalar, one_mul]
  unfold conjAut
  rw [MonoidHom.comp_apply, hsl]

theorem CoverData3.mem_of_conjAut [Finite K]
    (hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K)) (hW : ∀ w : W, w * w = 1)
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1) (A : GL (Fin 3) K)
    (hβ : D.beta hb = conjAut 3 K A) : b ∈ L := by
  have hsq : conjAut 3 K A * conjAut 3 K A = 1 := by rw [← hβ]; exact D.beta_sq hb hb2
  have h1 : conjAut 3 K (A * A) * fieldAut 3 K 1 = 1 := by
    rw [map_one, mul_one, map_mul]; exact hsq
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) (A * A) 1 h1
  have hscal : ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [smul_one_eq_diagonal]; rfl
  have hAA : (A : Matrix (Fin 3) (Fin 3) K) * A = (c : K) • 1 := by
    rw [← hscal, hc, Units.val_mul]
  obtain ⟨Asl, hAsl⟩ := exists_sl_of_sq_scalar A c hAA
  have hrel := D.conj_eq hperf hb (MulAut.conj Asl) (hβ.trans hAsl)
  have hbl : ∀ y ∈ L, b * y * b⁻¹ = (D.φ Asl : MulAut W) * y * (D.φ Asl : MulAut W)⁻¹ := by
    intro y hy
    obtain ⟨x, hx⟩ := D.surj ⟨y, hy⟩
    have := hrel x
    rw [hx, MulAut.conj_apply, map_mul, map_mul, map_inv, hx] at this
    simpa using this
  exact mem_of_inner_action hW hL hodd (D.φ Asl).2 hb2 hbl

open CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear

theorem CoverData3.dichotomy [Finite K] (h2 : (2 : K) ≠ 0) (hσ : ∀ σ : K ≃+* K, σ = 1)
    (hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K)) (hW : ∀ w : W, w * w = 1)
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1) :
    b ∈ L ∨ ∃ A : GL (Fin 3) K, (A : Matrix (Fin 3) (Fin 3) K)ᵀ = A ∧
      D.beta hb = conjAut 3 K A * dualAut 3 K := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hβ⟩ := hform (D.beta hb)
  rw [hσ σ] at hβ
  interval_cases ε
  · left
    rw [pow_zero, mul_one, map_one, mul_one] at hβ
    exact D.mem_of_conjAut hperf hW hL hodd hb hb2 A hβ
  · right
    rw [pow_one, map_one, mul_one] at hβ
    refine ⟨A, ?_, hβ⟩
    have hsq : (conjAut 3 K A * fieldAut 3 K 1 * dualAut 3 K) ^ 2 = 1 := by
      rw [map_one, mul_one, pow_two, ← hβ]; exact D.beta_sq hb hb2
    rcases transpose_eq_or_eq_neg_of_sq (le_refl 3) A hsq with h | h
    · exact h
    · exfalso
      have hdet := congrArg Matrix.det h
      rw [Matrix.det_transpose, Matrix.det_neg] at hdet
      have hd0 : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)).ne_zero
      simp only [Fintype.card_fin] at hdet
      apply hd0
      have h22 : (2 : K) * (A : Matrix (Fin 3) (Fin 3) K).det = 0 := by
        linear_combination hdet
      exact (mul_eq_zero.1 h22).resolve_left h2

theorem CoverData3.mul_mem_of_dual [Finite K]
    (hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K)) (hW : ∀ w : W, w * w = 1)
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {a a' : MulAut W}
    (ha : a ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (ha' : a' ∈ Subgroup.normalizer (L : Set (MulAut W))) {A A' : GL (Fin 3) K}
    (hβ : D.beta ha = conjAut 3 K A * dualAut 3 K)
    (hβ' : D.beta ha' = conjAut 3 K A' * dualAut 3 K) (hsq : a * a' * (a * a') = 1) :
    a * a' ∈ L := by
  obtain ⟨hcc, -, -, -, hdc, -⟩ := standard_automorphism_transport (n := 3) (K := K)
  refine D.mem_of_conjAut hperf hW hL hodd (Subgroup.mul_mem _ ha ha') hsq
    (A * GeneralLinearGroup.inverseTranspose A') ?_
  rw [D.beta_mul ha ha', hβ, hβ', ← hcc, ← hdc A']
  simp only [mul_assoc]

theorem CoverData3.outer_rank [Fintype K] [DecidableEq K] {p : ℕ} [Fact p.Prime] [CharP K p]
    [Finite W] [Fact (∀ w : W, w * w = 1)] (h2 : (2 : K) ≠ 0)
    (hK : ∀ k : K, ∃ n : ℕ, (n : K) = k) (hodd : Odd (Fintype.card K))
    (hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K)) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1) (A : GL (Fin 3) K)
    (hA : (A : Matrix (Fin 3) (Fin 3) K)ᵀ = A) (hβ : D.beta hb = conjAut 3 K A * dualAut 3 K) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (sub1 (binaryLin b))) := by
  obtain ⟨v, hv0, hvadd, hvinv, hvfaith⟩ := exists_inverted_vgroup (p := p) h2 A hA
  let σA : MulAut (SpecialLinearGroup (Fin 3) K) :=
    CatalogueBHigherLinearAction.slConjugation 3 K A * CatalogueBGraphForm.slGraphAut 3 K
  have hdesc : descendAut 3 K σA = conjAut 3 K A * dualAut 3 K := by
    simp only [σA, map_mul]; rfl
  have hrel := D.conj_eq hperf hb σA (hβ.trans hdesc.symm)
  have hσv : ∀ a, σA (v a) = (v a)⁻¹ := by
    intro a
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have := hvinv a
    simp only [σA, MulAut.mul_apply]
    rw [CatalogueBHigherLinearAction.slConjugation_matrix,
      CatalogueBGraphForm.slGraphAut_matrix]
    exact congrFun (congrFun this i) j
  have hvneg : ∀ a, v (-a) = (v a)⁻¹ := by
    intro a
    apply eq_inv_of_mul_eq_one_right
    rw [← hvadd, add_neg_cancel, hv0]
  let ρ' : K × K → (Additive W ≃ₗ[ZMod 2] Additive W) := fun a =>
    binaryLin ((D.φ (v a) : ↥L) : MulAut W)
  have hV : IsVAct ρ' := ⟨by simp [ρ', hv0], fun x y => by simp [ρ', hvadd]⟩
  have hfaith : ∀ x, ρ' x = 1 → x = 0 := by
    intro x hx
    have h1 : ((D.φ (v x) : ↥L) : MulAut W) = 1 :=
      binaryLin_injective (by rw [map_one]; exact hx)
    have h2' : D.φ (v x) = 1 := Subtype.ext h1
    exact hvfaith x (D.ker_central _ (MonoidHom.mem_ker.2 h2'))
  have hs : binaryLin b * binaryLin b = 1 := by rw [← map_mul, hb2, map_one]
  have hsρ : ∀ a, binaryLin b * ρ' a * binaryLin b = ρ' (-a) := by
    intro a
    have h1 : b * ((D.φ (v a) : ↥L) : MulAut W) * b = ((D.φ (v (-a)) : ↥L) : MulAut W) := by
      have := hrel (v a)
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
      rw [hσv, hbinv] at this
      rw [this, hvneg, map_inv, Subgroup.coe_inv]
    show binaryLin b * binaryLin ((D.φ (v a) : ↥L) : MulAut W) * binaryLin b =
      binaryLin ((D.φ (v (-a)) : ↥L) : MulAut W)
    rw [← map_mul, ← map_mul, h1]
  obtain ⟨o, o', hne, ho, ho'⟩ := exists_two_lines hV hodd hfaith
  have hdet : det2 (lineRep o) (lineRep o') ≠ 0 := det2_lineRep hne
  have hdet' : det2 (lineRep o') (lineRep o) ≠ 0 := det2_lineRep hne.symm
  have hne' : lineRep o ≠ lineRep o' := fun h => hdet (by rw [h]; simp [det2]; ring)
  classical
  have := card_le_finrank_range_sub1 hV hodd hK hs hsρ {lineRep o, lineRep o'}
    (by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact lineRep_ne_zero _
      · rw [Finset.mem_singleton.1 hu]; exact lineRep_ne_zero _)
    (by
      intro u hu w hw huw
      rcases Finset.mem_insert.1 hu with rfl | hu <;>
        rcases Finset.mem_insert.1 hw with rfl | hw
      · exact absurd rfl huw
      · rw [Finset.mem_singleton.1 hw]; exact hdet
      · rw [Finset.mem_singleton.1 hu]
        exact hdet'
      · rw [Finset.mem_singleton.1 hu, Finset.mem_singleton.1 hw] at huw
        exact absurd rfl huw)
    (by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact ho
      · rw [Finset.mem_singleton.1 hu]; exact ho')
  rwa [Finset.card_pair hne'] at this

end Outer

end CFSG.QuasithinUnique.Setup.Family
