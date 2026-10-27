module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinMod
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section MidBlock

variable {K : Type} [Field K] {k : ℕ}

theorem stdRhoMat_mul' (hk : 2 ≤ k) {g h : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    (hg : ∀ a : StdMid hk, g a.1 (idxU hk) = 0) (hh : ∀ b : StdMid hk, h (idxV hk) b.1 = 0) :
    stdRhoMat hk (g * h) = stdRhoMat hk g * stdRhoMat hk h := by
  ext a b
  simp only [stdRhoMat, submatrix_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x => x ≠ idxU hk ∧ x ≠ idxV hk)]
  have hzero : ∑ i : {x : Fin (2 + k) // ¬ (x ≠ idxU hk ∧ x ≠ idxV hk)},
      g a.1 i.1 * h i.1 b.1 = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases not_and_or.mp i.2 with hi | hi <;> push Not at hi
    · rw [hi, hg a, zero_mul]
    · rw [hi, hh b, mul_zero]
  rw [hzero, add_zero]

abbrev StdEnds (hk : 2 ≤ k) : Type := {x : Fin (2 + k) // ¬ (x ≠ idxU hk ∧ x ≠ idxV hk)}

variable (K) in
@[expose] noncomputable def midEmbed (hk : 2 ≤ k) :
    Matrix (StdMid hk) (StdMid hk) K →* Matrix (Fin (2 + k)) (Fin (2 + k)) K where
  toFun A := Matrix.reindex (Equiv.sumCompl _) (Equiv.sumCompl _)
    (fromBlocks A 0 0 (1 : Matrix (StdEnds hk) (StdEnds hk) K))
  map_one' := by
    rw [fromBlocks_one, reindex_apply, submatrix_one_equiv]
  map_mul' A B := by
    rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
    simp

theorem midEmbed_apply_mid (hk : 2 ≤ k) (A : Matrix (StdMid hk) (StdMid hk) K)
    (a b : StdMid hk) : midEmbed K hk A a.1 b.1 = A a b := by
  change (fromBlocks A 0 0 (1 : Matrix (StdEnds hk) (StdEnds hk) K)).submatrix
    (Equiv.sumCompl _).symm (Equiv.sumCompl _).symm a.1 b.1 = A a b
  rw [submatrix_apply, Equiv.sumCompl_symm_apply_pos, Equiv.sumCompl_symm_apply_pos,
    fromBlocks_apply₁₁]

theorem midEmbed_apply_of_end (hk : 2 ≤ k) (A : Matrix (StdMid hk) (StdMid hk) K)
    {x y : Fin (2 + k)} (h : ¬ (x ≠ idxU hk ∧ x ≠ idxV hk) ∨ ¬ (y ≠ idxU hk ∧ y ≠ idxV hk)) :
    midEmbed K hk A x y = (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x y := by
  change (fromBlocks A 0 0 (1 : Matrix (StdEnds hk) (StdEnds hk) K)).submatrix
    (Equiv.sumCompl _).symm (Equiv.sumCompl _).symm x y = _
  have hpos : ∀ {z : Fin (2 + k)} (hz : z ≠ idxU hk ∧ z ≠ idxV hk),
      (Equiv.sumCompl (fun x => x ≠ idxU hk ∧ x ≠ idxV hk)).symm z = Sum.inl ⟨z, hz⟩ :=
    fun hz => Equiv.sumCompl_symm_apply_of_pos (p := fun x => x ≠ idxU hk ∧ x ≠ idxV hk) hz
  have hneg : ∀ {z : Fin (2 + k)} (hz : ¬ (z ≠ idxU hk ∧ z ≠ idxV hk)),
      (Equiv.sumCompl (fun x => x ≠ idxU hk ∧ x ≠ idxV hk)).symm z = Sum.inr ⟨z, hz⟩ :=
    fun hz => Equiv.sumCompl_symm_apply_of_neg (p := fun x => x ≠ idxU hk ∧ x ≠ idxV hk) hz
  rw [submatrix_apply]
  by_cases hx : x ≠ idxU hk ∧ x ≠ idxV hk <;> by_cases hy : y ≠ idxU hk ∧ y ≠ idxV hk
  · exact absurd hy (h.resolve_left (not_not.mpr hx))
  · rw [hpos hx, hneg hy, fromBlocks_apply₁₂, Matrix.zero_apply, one_apply_ne]
    rintro rfl
    exact hy hx
  · rw [hneg hx, hpos hy, fromBlocks_apply₂₁, Matrix.zero_apply, one_apply_ne]
    rintro rfl
    exact hx hy
  · rw [hneg hx, hneg hy, fromBlocks_apply₂₂, one_apply, one_apply]
    simp only [Subtype.ext_iff]

theorem stdRhoMat_midEmbed (hk : 2 ≤ k) (A : Matrix (StdMid hk) (StdMid hk) K) :
    stdRhoMat hk (midEmbed K hk A) = A := by
  ext a b
  rw [stdRhoMat, submatrix_apply, midEmbed_apply_mid]

variable (K) in
@[expose] noncomputable def midGL (hk : 2 ≤ k) : GL (StdMid hk) K →* GL (Fin (2 + k)) K :=
  Units.map (midEmbed K hk)

theorem coe_midGL (hk : 2 ≤ k) (A : GL (StdMid hk) K) :
    ((midGL K hk A : GL (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      midEmbed K hk (A : Matrix (StdMid hk) (StdMid hk) K) :=
  rfl


theorem midEmbed_mulVec_u (hk : 2 ≤ k) (A : Matrix (StdMid hk) (StdMid hk) K) :
    midEmbed K hk A *ᵥ Pi.single (idxU hk) 1 = Pi.single (idxU hk) 1 := by
  ext x
  rw [mulVec_single_one, col_apply, midEmbed_apply_of_end hk A (Or.inr fun h => h.1 rfl)]
  simp only [Pi.single_apply, one_apply]

theorem vecMul_midEmbed_v (hk : 2 ≤ k) (A : Matrix (StdMid hk) (StdMid hk) K) :
    Pi.single (idxV hk) 1 ᵥ* midEmbed K hk A = Pi.single (idxV hk) 1 := by
  ext y
  rw [single_one_vecMul, row_apply, midEmbed_apply_of_end hk A (Or.inl fun h => h.2 rfl)]
  simp only [Pi.single_apply, one_apply, eq_comm]

theorem coe_slConjugation_midGL_inv (hk : 2 ≤ k) (A : GL (StdMid hk) K)
    (g : SpecialLinearGroup (Fin (2 + k)) K) :
    ((CatalogueBHigherLinearAction.slConjugation (2 + k) K (midGL K hk A)⁻¹ g :
      SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      midEmbed K hk ((A⁻¹ : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K) *
        (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
          midEmbed K hk (A : Matrix (StdMid hk) (StdMid hk) K) := by
  rw [coe_slConjugation, inv_inv, ← map_inv, coe_midGL, coe_midGL]

theorem slConjugation_midGL_mem_stdX (hk : 2 ≤ k) (A : GL (StdMid hk) K)
    {g : SpecialLinearGroup (Fin (2 + k)) K} (hg : g ∈ stdX K hk) :
    CatalogueBHigherLinearAction.slConjugation (2 + k) K (midGL K hk A)⁻¹ g ∈ stdX K hk := by
  refine ⟨?_, ?_⟩
  · rw [coe_slConjugation_midGL_inv, ← mulVec_mulVec, ← mulVec_mulVec, midEmbed_mulVec_u,
      hg.1, midEmbed_mulVec_u]
  · rw [coe_slConjugation_midGL_inv, ← vecMul_vecMul, ← vecMul_vecMul, vecMul_midEmbed_v,
      hg.2, vecMul_midEmbed_v]

theorem stdRhoMat_slConjugation_midGL (hk : 2 ≤ k) (A : GL (StdMid hk) K)
    {g : SpecialLinearGroup (Fin (2 + k)) K} (hg : g ∈ stdX K hk) :
    stdRhoMat hk ((CatalogueBHigherLinearAction.slConjugation (2 + k) K (midGL K hk A)⁻¹ g :
      SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      ((A⁻¹ : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K) *
        stdRhoMat hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
          (A : Matrix (StdMid hk) (StdMid hk) K) := by
  have hcol : ∀ (M : Matrix (StdMid hk) (StdMid hk) K) (a : StdMid hk),
      midEmbed K hk M a.1 (idxU hk) = 0 := fun M a => by
    rw [midEmbed_apply_of_end hk M (Or.inr fun h => h.1 rfl), one_apply_ne a.2.1]
  have hrow : ∀ (M : Matrix (StdMid hk) (StdMid hk) K) (b : StdMid hk),
      midEmbed K hk M (idxV hk) b.1 = 0 := fun M b => by
    rw [midEmbed_apply_of_end hk M (Or.inl fun h => h.2 rfl), one_apply_ne (Ne.symm b.2.2)]
  have hgM : ∀ b : StdMid hk, ((g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
      midEmbed K hk (A : Matrix (StdMid hk) (StdMid hk) K)) (idxV hk) b.1 = 0 := by
    intro b
    have h1 : ((g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
        midEmbed K hk (A : Matrix (StdMid hk) (StdMid hk) K)) (idxV hk) b.1 =
        (Pi.single (idxV hk) 1 ᵥ* ((g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
          midEmbed K hk (A : Matrix (StdMid hk) (StdMid hk) K))) b.1 := by
      rw [single_one_vecMul, row_apply]
    rw [h1, ← vecMul_vecMul, hg.2, vecMul_midEmbed_v, Pi.single_eq_of_ne b.2.2]
  rw [coe_slConjugation_midGL_inv, Matrix.mul_assoc, stdRhoMat_mul' hk (hcol _) hgM,
    stdRhoMat_mul' hk (fun a => by
      have := congrFun hg.1 a.1
      rwa [mulVec_single_one, col_apply, Pi.single_eq_of_ne a.2.1] at this) (hrow _),
    stdRhoMat_midEmbed, stdRhoMat_midEmbed, Matrix.mul_assoc]

end MidBlock

section Shapes

variable {K : Type} [Field K] {k : ℕ}

@[expose] def MidBlockShape (hk : 2 ≤ k) (S : Matrix (StdMid hk) (StdMid hk) K) : Prop :=
  ∀ a b : StdMid hk, ¬ (IsBlockOne k a.1 ∧ IsBlockOne k b.1) →
    S a b = (1 : Matrix (StdMid hk) (StdMid hk) K) a b

@[expose] def MidTorusShape (hk : 2 ≤ k) (μ : K) (S : Matrix (StdMid hk) (StdMid hk) K) : Prop :=
  ∀ a b : StdMid hk, (IsBlockOne k a.1 ∨ IsBlockOne k b.1) → S a b = if a = b then μ else 0

theorem blockOneShape_iff_mid (hk : 2 ≤ k) (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) :
    BlockOneShape hk M ↔ MidBlockShape hk (stdRhoMat hk M) := by
  constructor
  · intro h a b hab
    rw [stdRhoMat, submatrix_apply, h a.1 b.1 a.2.1 a.2.2 b.2.1 b.2.2 hab, one_apply, one_apply]
    simp only [Subtype.ext_iff]
  · intro h x y hxu hxv hyu hyv hxy
    have := h ⟨x, hxu, hxv⟩ ⟨y, hyu, hyv⟩ hxy
    rw [stdRhoMat, submatrix_apply, one_apply] at this
    rw [this, one_apply]
    simp only [Subtype.ext_iff]

theorem torusOneShape_iff_mid (hk : 2 ≤ k) (μ : K) (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) :
    TorusOneShape hk μ M ↔ MidTorusShape hk μ (stdRhoMat hk M) := by
  constructor
  · intro h a b hab
    rw [stdRhoMat, submatrix_apply, h a.1 b.1 a.2.1 a.2.2 b.2.1 b.2.2 hab]
    simp only [Subtype.ext_iff]
  · intro h x y hxu hxv hyu hyv hxy
    have := h ⟨x, hxu, hxv⟩ ⟨y, hyu, hyv⟩ hxy
    rw [stdRhoMat, submatrix_apply] at this
    rw [this]
    simp only [Subtype.ext_iff]

theorem MidBlockShape.map {hk : 2 ≤ k} {S : Matrix (StdMid hk) (StdMid hk) K}
    (h : MidBlockShape hk S) (σ : K ≃+* K) : MidBlockShape hk (S.map σ) := by
  intro a b hab
  rw [map_apply, h a b hab, one_apply]
  split_ifs <;> simp

theorem MidBlockShape.transpose {hk : 2 ≤ k} {S : Matrix (StdMid hk) (StdMid hk) K}
    (h : MidBlockShape hk S) : MidBlockShape hk S.transpose := by
  intro a b hab
  rw [transpose_apply, h b a (fun h' => hab ⟨h'.2, h'.1⟩), one_apply, one_apply]
  simp only [eq_comm]

theorem MidBlockShape.of_mul_eq_one {hk : 2 ≤ k} {S T : Matrix (StdMid hk) (StdMid hk) K}
    (h : MidBlockShape hk S) (h1 : S * T = 1) (h2 : T * S = 1) : MidBlockShape hk T := by
  intro a b hab
  by_cases ha : IsBlockOne k a.1
  · have hb : ¬ IsBlockOne k b.1 := fun hb => hab ⟨ha, hb⟩
    have e := congrFun (congrFun h2 a) b
    rw [Matrix.mul_apply, Finset.sum_eq_single b (fun c _ hc => by
        rw [h c b (fun h' => hb h'.2), one_apply_ne hc, mul_zero])
      (fun h' => absurd (Finset.mem_univ _) h'), h b b (fun h' => hb h'.2), one_apply_eq,
      mul_one] at e
    exact e
  · have e := congrFun (congrFun h1 a) b
    rw [Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by
        rw [h a c (fun h' => ha h'.1), one_apply_ne (Ne.symm hc), zero_mul])
      (fun h' => absurd (Finset.mem_univ _) h'), h a a (fun h' => ha h'.1), one_apply_eq,
      one_mul] at e
    exact e

theorem MidTorusShape.map {hk : 2 ≤ k} {μ : K} {S : Matrix (StdMid hk) (StdMid hk) K}
    (h : MidTorusShape hk μ S) (σ : K ≃+* K) : MidTorusShape hk (σ μ) (S.map σ) := by
  intro a b hab
  rw [map_apply, h a b hab]
  split_ifs <;> simp

theorem MidTorusShape.transpose {hk : 2 ≤ k} {μ : K} {S : Matrix (StdMid hk) (StdMid hk) K}
    (h : MidTorusShape hk μ S) : MidTorusShape hk μ S.transpose := by
  intro a b hab
  rw [transpose_apply, h b a hab.symm]
  simp only [eq_comm]

theorem MidTorusShape.of_mul_eq_one {hk : 2 ≤ k} {μ : K} {S T : Matrix (StdMid hk) (StdMid hk) K}
    (h : MidTorusShape hk μ S) (h1 : S * T = 1) (h2 : T * S = 1) : MidTorusShape hk μ⁻¹ T := by
  intro a b hab
  rcases hab with ha | hb
  · have hrow : ∀ c, μ * T a c = (1 : Matrix (StdMid hk) (StdMid hk) K) a c := by
      intro c
      have e := congrFun (congrFun h1 a) c
      rw [Matrix.mul_apply, Finset.sum_eq_single a (fun d _ hd => by
          rw [h a d (Or.inl ha), ite_eq_right (Ne.symm hd), zero_mul])
        (fun h' => absurd (Finset.mem_univ _) h'), h a a (Or.inl ha), ite_eq_left rfl] at e
      exact e
    have e := hrow b
    by_cases hab : a = b
    · subst hab
      rw [one_apply_eq] at e
      rw [ite_eq_left rfl]
      exact eq_inv_of_mul_eq_one_right e
    · have hμ : μ ≠ 0 := fun h0 => by
        have := hrow a
        rw [h0, zero_mul, one_apply_eq] at this
        exact zero_ne_one this
      rw [one_apply_ne hab] at e
      rw [ite_eq_right hab]
      exact (mul_eq_zero.mp e).resolve_left hμ
  · have hcol : ∀ c, T c b * μ = (1 : Matrix (StdMid hk) (StdMid hk) K) c b := by
      intro c
      have e := congrFun (congrFun h2 c) b
      rw [Matrix.mul_apply, Finset.sum_eq_single b (fun d _ hd => by
          rw [h d b (Or.inr hb), ite_eq_right hd, mul_zero])
        (fun h' => absurd (Finset.mem_univ _) h'), h b b (Or.inr hb), ite_eq_left rfl] at e
      exact e
    have e := hcol a
    by_cases hab : a = b
    · subst hab
      rw [one_apply_eq] at e
      rw [ite_eq_left rfl]
      exact eq_inv_of_mul_eq_one_left e
    · have hμ : μ ≠ 0 := fun h0 => by
        have := hcol b
        rw [h0, mul_zero, one_apply_eq] at this
        exact zero_ne_one this
      rw [one_apply_ne hab] at e
      rw [ite_eq_right hab]
      exact (mul_eq_zero.mp e).resolve_right hμ

end Shapes

section IndexAut

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {K : Type*}
  [Field K]

variable (K) in
@[expose] noncomputable def slIndexEquiv (e : ι ≃ κ) :
    SpecialLinearGroup ι K ≃* SpecialLinearGroup κ K where
  toFun g := ⟨reindexAlgEquiv K K e (g : Matrix ι ι K), by rw [det_reindexAlgEquiv]; exact g.2⟩
  invFun g := ⟨(reindexAlgEquiv K K e).symm (g : Matrix κ κ K), by
    rw [symm_reindexAlgEquiv, det_reindexAlgEquiv]; exact g.2⟩
  left_inv g := Subtype.ext (AlgEquiv.symm_apply_apply _ _)
  right_inv g := Subtype.ext (AlgEquiv.apply_symm_apply _ _)
  map_mul' g h := Subtype.ext (by
    change reindexAlgEquiv K K e ((g : Matrix ι ι K) * (h : Matrix ι ι K)) =
      reindexAlgEquiv K K e (g : Matrix ι ι K) * reindexAlgEquiv K K e (h : Matrix ι ι K)
    rw [map_mul])

theorem coe_slIndexEquiv (e : ι ≃ κ) (g : SpecialLinearGroup ι K) :
    ((slIndexEquiv K e g : SpecialLinearGroup κ K) : Matrix κ κ K) =
      reindexAlgEquiv K K e (g : Matrix ι ι K) :=
  rfl

theorem exists_matrix_form_of_mulAut_slIndex [Finite K] (hn : 3 ≤ Fintype.card ι)
    (β : MulAut (SpecialLinearGroup ι K)) :
    ∃ (A : GL ι K) (σ : K ≃+* K),
      (∀ g : SpecialLinearGroup ι K, (β g : Matrix ι ι K) =
        (A : Matrix ι ι K) * (g : Matrix ι ι K).map σ * ((A⁻¹ : GL ι K) : Matrix ι ι K)) ∨
      (∀ g : SpecialLinearGroup ι K, (β g : Matrix ι ι K) =
        (A : Matrix ι ι K) * ((g⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K).transpose.map σ *
          ((A⁻¹ : GL ι K) : Matrix ι ι K)) := by
  set e := Fintype.equivFin ι
  set Φ := slIndexEquiv K e
  obtain ⟨A', σ, h⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl hn ((Φ.symm.trans β).trans Φ)
  set R : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K →* Matrix ι ι K :=
    ((reindexAlgEquiv K K e).symm : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K →*
      Matrix ι ι K)
  have hR : ∀ M, R M = (reindexAlgEquiv K K e).symm M := fun M => rfl
  have hβ : ∀ g : SpecialLinearGroup ι K, (β g : Matrix ι ι K) =
      R ((((Φ.symm.trans β).trans Φ) (Φ g) : SpecialLinearGroup (Fin (Fintype.card ι)) K) :
        Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K) := by
    intro g
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hR,
      coe_slIndexEquiv, AlgEquiv.symm_apply_apply]
  have hmap : ∀ M : Matrix ι ι K, R ((reindexAlgEquiv K K e M).map σ) = M.map σ := by
    intro M
    ext i j
    rw [hR, symm_reindexAlgEquiv, coe_reindexAlgEquiv, coe_reindexAlgEquiv]
    simp
  refine ⟨Units.map R A', σ, ?_⟩
  rcases h with h | h
  · left
    intro g
    rw [hβ, h, map_mul, map_mul, coe_slIndexEquiv, hmap, Units.coe_map, Units.coe_map_inv]
  · right
    intro g
    have htr : ∀ M : Matrix ι ι K,
        (reindexAlgEquiv K K e M).transpose = reindexAlgEquiv K K e M.transpose := fun M => by
      rw [coe_reindexAlgEquiv, transpose_reindex]
    rw [hβ, h, map_mul, map_mul, ← map_inv, coe_slIndexEquiv, htr, hmap, Units.coe_map,
      Units.coe_map_inv]

end IndexAut

section Induced

theorem exists_mulAut_comp_eq_of_ker {X S : Type*} [Group X] [Finite X] [Group S] (ψ : X →* S)
    (hψ : Function.Surjective ψ) (γ : MulAut X) (hγ : ∀ x, ψ x = 1 → ψ (γ x) = 1) :
    ∃ β : MulAut S, ∀ x, β (ψ x) = ψ (γ x) := by
  have hle : ψ.ker.map (γ : X →* X) ≤ ψ.ker := by
    rintro _ ⟨x, hx, rfl⟩
    exact hγ x hx
  have heq : ψ.ker.map (γ : X →* X) = ψ.ker :=
    Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective γ.injective).ge
  set e := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  have he : ∀ x, e (QuotientGroup.mk x) = ψ x := fun x => rfl
  refine ⟨(e.symm.trans (QuotientGroup.congr ψ.ker ψ.ker γ heq)).trans e, fun x => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, ← he x, MulEquiv.symm_apply_apply,
    QuotientGroup.congr_mk, he]

end Induced

end CFSG.ComponentClassification.RankTwoClassical
