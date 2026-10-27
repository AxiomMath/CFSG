module

public import CFSG.GH74.Generic.BProg.B2.GenLocBasic
public import CFSG.GH74.Generic.BProg.B2.GenLocL2SL
public import CFSG.GH74.Generic.BProg.B2.GenLocL3Blk

public noncomputable section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.AutL2Facts Matrix
open scoped MatrixGroups

namespace GenLocL3Good

variable {K : Type} [Field K]

@[expose] def diag2 (a b : Kˣ) : GL (Fin 2) K :=
  ⟨Matrix.diagonal ![(a : K), (b : K)], Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((b⁻¹ : Kˣ) : K)],
    by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp,
    by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp⟩

@[expose] def diag3 (u : Fin 3 → Kˣ) : GL (Fin 3) K :=
  ⟨Matrix.diagonal fun a => (u a : K), Matrix.diagonal fun a => (((u a)⁻¹ : Kˣ) : K),
    by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h],
    by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]⟩

theorem coe_diag2 (a b : Kˣ) : ((diag2 a b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    Matrix.diagonal ![(a : K), (b : K)] := rfl

theorem coe_diag2_inv (a b : Kˣ) : (((diag2 a b)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((b⁻¹ : Kˣ) : K)] := rfl

theorem coe_diag3 (u : Fin 3 → Kˣ) : ((diag3 u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    Matrix.diagonal fun a => (u a : K) := rfl

theorem coe_diag3_inv (u : Fin 3 → Kˣ) : (((diag3 u)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    Matrix.diagonal fun a => (((u a)⁻¹ : Kˣ) : K) := rfl

theorem isDiag_diag3 (u : Fin 3 → Kˣ) :
    ((diag3 u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
  rw [coe_diag3]
  exact Matrix.isDiag_diagonal _

theorem exists_diag3 {x : GL (Fin 3) K}
    (hx : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) : ∃ u : Fin 3 → Kˣ, x = diag3 u := by
  have hd0 : ∀ a, (x : Matrix (Fin 3) (Fin 3) K) a a ≠ 0 := GenLocL3Blk.diag_ne_zero hx
  refine ⟨fun a => Units.mk0 _ (hd0 a), ?_⟩
  apply Units.ext
  rw [coe_diag3]
  exact hx.diagonal_diag.symm

@[expose] def Jgl : GL (Fin 2) K :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_Jgl : ((Jgl : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl

theorem coe_Jgl_inv : (((Jgl : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![0, -1; 1, 0] := rfl

theorem inv_transpose_eq (g : SL(2, K)) :
    (g⁻¹).transpose =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 K Jgl g := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.coe_inv, coe_Jgl, coe_Jgl_inv, Matrix.adjugate_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem conj_blk (u : Fin 3 → Kˣ) (i : Fin 2) (g : SL(2, K)) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K (diag3 u)
      (GenLocL3Blk.blkHom i g) = GenLocL3Blk.blkHom i
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 K
        (diag2 (u (GenLocL3Blk.pos i 0)) (u (GenLocL3Blk.pos i 1))) g) := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, GenLocL3Blk.coe_blkHom, GenLocL3Blk.coe_blkHom,
    LinearFlag.coe_slConjugation, coe_diag3, coe_diag3_inv, coe_diag2, coe_diag2_inv]
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [GenLocL3Blk.blkMat, GenLocL3Blk.pos, Matrix.mul_apply, Matrix.diagonal_apply]

theorem conjAut_phi_eq (u : Fin 3 → Kˣ) (i : Fin 2) (g : SL(2, K)) :
    LinearFlag.conjAut 3 K (diag3 u) (GenLocL3Blk.phi i g) = GenLocL3Blk.phi i
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 K
        (diag2 (u (GenLocL3Blk.pos i 0)) (u (GenLocL3Blk.pos i 1))) g) := by
  unfold GenLocL3Blk.phi
  simp only [MonoidHom.comp_apply]
  rw [LinearFlag.conjAut_proj, conj_blk]

theorem dualAut_phi_eq (i : Fin 2) (g : SL(2, K)) :
    LinearFlag.dualAut 3 K (GenLocL3Blk.phi i g) = GenLocL3Blk.phi i
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 K Jgl g) := by
  rw [GenLocL3Blk.dualAut_phi, inv_transpose_eq]

theorem exists_rest (i : Fin 2) :
    ∃ ρ : frameStab 3 K →* MulAut SL(2, K), ∀ (y : frameStab 3 K) (g : SL(2, K)),
      (y : MulAut (LinearFlag.projectiveSL 3 K)) (GenLocL3Blk.phi i g) =
        GenLocL3Blk.phi i (ρ y g) :=
  GenLocL3Blk.exists_restrict_action (GenLocL3Blk.phi i) (GenLocL3Blk.phi_injective i)
    (frameStab 3 K).subtype fun y g => GenLocL3Blk.stable_phi y.2 i g

@[expose] def rest (i : Fin 2) : frameStab 3 K →* MulAut SL(2, K) :=
  Classical.choose (exists_rest i)

theorem rest_spec (i : Fin 2) (y : frameStab 3 K) (g : SL(2, K)) :
    (y : MulAut (LinearFlag.projectiveSL 3 K)) (GenLocL3Blk.phi i g) =
      GenLocL3Blk.phi i (rest i y g) :=
  Classical.choose_spec (exists_rest i) y g

theorem rest_eq_of_apply {i : Fin 2} {y : frameStab 3 K} {τ : MulAut SL(2, K)}
    (h : ∀ g, (y : MulAut (LinearFlag.projectiveSL 3 K)) (GenLocL3Blk.phi i g) =
      GenLocL3Blk.phi i (τ g)) : rest i y = τ := by
  refine MulEquiv.ext fun g => ?_
  apply GenLocL3Blk.phi_injective i
  rw [← rest_spec, h]

theorem rest_conjAut (u : Fin 3 → Kˣ) (i : Fin 2) :
    rest i ⟨LinearFlag.conjAut 3 K (diag3 u),
        GenLocL3NFAux.conjAut_mem_frameStab (isDiag_diag3 u)⟩ =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 K
        (diag2 (u (GenLocL3Blk.pos i 0)) (u (GenLocL3Blk.pos i 1))) :=
  rest_eq_of_apply fun g => conjAut_phi_eq u i g

theorem rest_dualAut (i : Fin 2) :
    rest i ⟨LinearFlag.dualAut 3 K, GenLocL3NFAux.dualAut_mem_frameStab⟩ =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 K Jgl :=
  rest_eq_of_apply fun g => dualAut_phi_eq i g

@[expose] def toFrame {A : Type} [Group A] (α : A →* MulAut (LinearFlag.projectiveSL 3 K))
    (hα : α.range ≤ frameStab 3 K) : A →* frameStab 3 K :=
  α.codRestrict (frameStab 3 K) fun a => hα ⟨a, rfl⟩

theorem gammaAct_eq_top_of_blocks {A : Type} [Group A]
    (α : A →* MulAut (LinearFlag.projectiveSL 3 K)) (hα : α.range ≤ frameStab 3 K)
    (h : ∀ i : Fin 2, gammaAct ((rest i).comp (toFrame α hα)) = ⊤) : gammaAct α = ⊤ := by
  refine gammaAct_eq_top_of_equivariant α (fun _ : Fin 2 => SL(2, K)) (fun i => GenLocL3Blk.phi i)
    (fun i => (rest i).comp (toFrame α hα)) (fun i a g => rest_spec i (toFrame α hα a) g) ?_ h
  rw [eq_top_iff, ← GenLocL3Blk.range_phi_sup]
  exact sup_le (le_iSup (fun i : Fin 2 => (GenLocL3Blk.phi (K := K) i).range) 0)
    (le_iSup (fun i : Fin 2 => (GenLocL3Blk.phi (K := K) i).range) 1)

@[expose] def noDual (K : Type) [Field K] : Subgroup (MulAut (LinearFlag.projectiveSL 3 K)) where
  carrier := {y | ∃ (x : GL (Fin 3) K) (σ : K ≃+* K),
    ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag ∧
      y = LinearFlag.conjAut 3 K x * LinearFlag.fieldAut 3 K σ}
  mul_mem' := by
    rintro _ _ ⟨x, σ, hx, rfl⟩ ⟨x', τ, hx', rfl⟩
    refine ⟨x * GeneralLinearGroup.map (σ : K →+* K) x', σ * τ, ?_, ?_⟩
    · rw [Units.val_mul]
      exact GenLocL3NFFrame.isDiag_mul' hx (GenLocL3NFFrame.isDiag_map_gl σ hx')
    · have s1 := LinearFlag.fieldAut_mul_conjAut (n := 3) (K := K) σ x'
      calc LinearFlag.conjAut 3 K x * LinearFlag.fieldAut 3 K σ *
            (LinearFlag.conjAut 3 K x' * LinearFlag.fieldAut 3 K τ)
          = LinearFlag.conjAut 3 K x * (LinearFlag.fieldAut 3 K σ * LinearFlag.conjAut 3 K x') *
            LinearFlag.fieldAut 3 K τ := by simp only [mul_assoc]
        _ = _ := by rw [s1, map_mul, map_mul]; simp only [mul_assoc]
  one_mem' := ⟨1, 1, by rw [Units.val_one]; exact Matrix.isDiag_one, by simp⟩
  inv_mem' := by
    rintro _ ⟨x, σ, hx, rfl⟩
    refine ⟨GeneralLinearGroup.map ((σ⁻¹ : K ≃+* K) : K →+* K) x⁻¹, σ⁻¹,
      GenLocL3NFFrame.isDiag_map_gl σ⁻¹ (GenLocL3NFFrame.isDiag_inv_gl hx), ?_⟩
    have s1 := LinearFlag.fieldAut_mul_conjAut (n := 3) (K := K) σ⁻¹ x⁻¹
    have h1 : (LinearFlag.conjAut 3 K x * LinearFlag.fieldAut 3 K σ)⁻¹ =
        LinearFlag.fieldAut 3 K σ⁻¹ * LinearFlag.conjAut 3 K x⁻¹ := by
      rw [_root_.mul_inv_rev]; simp
    rw [h1, s1]

theorem frameStab_cases {y : MulAut (LinearFlag.projectiveSL 3 K)} (hy : y ∈ frameStab 3 K) :
    y ∈ noDual K ∨ ∃ h ∈ noDual K, y = h * LinearFlag.dualAut 3 K := by
  obtain ⟨x, σ, ε, hx, hε, rfl⟩ := GenLocL3NFFrame.mem_frameStab_iff.1 hy
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · exact Or.inl ⟨x, σ, hx, by rw [pow_zero, mul_one]⟩
  · exact Or.inr ⟨_, ⟨x, σ, hx, rfl⟩, by rw [pow_one]⟩

theorem adm_comap_noDual {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (α : A →* MulAut (LinearFlag.projectiveSL 3 K)) (hα : α.range ≤ frameStab 3 K) :
    pRank 2 A - 1 ≤ pRank 2 ↥((noDual K).comap α) := by
  rw [GenLocBasic.adm_iff_index hA]
  by_cases htop : (noDual K).comap α = ⊤
  · rw [htop, Subgroup.index_top]
    norm_num
  · have : ∃ a, a ∉ (noDual K).comap α := by
      by_contra h
      push Not at h
      exact htop (eq_top_iff.2 fun a _ => h a)
    obtain ⟨a, ha⟩ := this
    have hidx : ((noDual K).comap α).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨a⁻¹, fun b => ?_⟩
      by_cases hb : b ∈ (noDual K).comap α
      · right
        refine ⟨hb, fun h => ha ?_⟩
        have := ((noDual K).comap α).mul_mem (((noDual K).comap α).inv_mem hb) h
        simpa using this
      · left
        refine ⟨?_, hb⟩
        have hb' := frameStab_cases (hα ⟨b, rfl⟩)
        have ha' := frameStab_cases (hα ⟨a, rfl⟩)
        rcases hb' with hb' | ⟨h', hh', hbe⟩
        · exact absurd hb' hb
        rcases ha' with ha' | ⟨h, hh, hae⟩
        · exact absurd ha' ha
        change α (b * a⁻¹) ∈ noDual K
        rw [map_mul, map_inv, hbe, hae, _root_.mul_inv_rev, ← mul_assoc, mul_assoc h',
          mul_inv_cancel, mul_one]
        exact (noDual K).mul_mem hh' ((noDual K).inv_mem hh)
    rw [hidx]

theorem scalar_of_commute_sl2 (M : Matrix (Fin 2) (Fin 2) K)
    (h : ∀ g : SL(2, K), M * (g : Matrix (Fin 2) (Fin 2) K) = (g : Matrix (Fin 2) (Fin 2) K) * M) :
    ∃ c : K, M = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  let g1 : SL(2, K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let g2 : SL(2, K) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have e1 := h g1
  have e2 := h g2
  have e10 := congrFun (congrFun e1 0) 0
  have e11 := congrFun (congrFun e1 0) 1
  have e20 := congrFun (congrFun e2 0) 0
  simp [g1, g2, Matrix.mul_apply, Fin.sum_univ_two] at e10 e11 e20
  refine ⟨M 0 0, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> first | assumption | linear_combination (-1 : K) * e11

theorem det_sq_aux (S S' Dm D' : Matrix (Fin 2) (Fin 2) K) (hSS : S' * S = 1) (hDD : D' * Dm = 1)
    (hdetS : S.det = 1)
    (key : ∀ g : SL(2, K), S * (g : Matrix (Fin 2) (Fin 2) K) * S' =
      Dm * (g : Matrix (Fin 2) (Fin 2) K) * D') : IsSquare Dm.det := by
  have hDD' : Dm * D' = 1 := mul_eq_one_comm.1 hDD
  obtain ⟨c, hc⟩ := scalar_of_commute_sl2 (D' * S) (fun g => by
    have h1 := key g
    have e1 : D' * (S * (g : Matrix (Fin 2) (Fin 2) K) * S') * S = D' * S * g := by
      rw [show D' * (S * (g : Matrix (Fin 2) (Fin 2) K) * S') * S =
        D' * S * (g : Matrix (Fin 2) (Fin 2) K) * (S' * S) by simp only [Matrix.mul_assoc], hSS,
        Matrix.mul_one]
    have e2 : D' * (Dm * (g : Matrix (Fin 2) (Fin 2) K) * D') * S =
        (g : Matrix (Fin 2) (Fin 2) K) * (D' * S) := by
      rw [show D' * (Dm * (g : Matrix (Fin 2) (Fin 2) K) * D') * S =
        (D' * Dm) * (g : Matrix (Fin 2) (Fin 2) K) * (D' * S) by simp only [Matrix.mul_assoc], hDD,
        Matrix.one_mul]
    rw [← e1, h1, e2])
  have hs1 : S = c • Dm := by
    have h2 := congrArg (fun M => Dm * M) hc
    simp only [← Matrix.mul_assoc, hDD', Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at h2
    rw [h2]
  have hdet : c * c * Dm.det = 1 := by
    rw [hs1, Matrix.det_smul, Fintype.card_fin] at hdetS
    rw [← hdetS]; ring
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0] at hdet; simp at hdet
  refine ⟨c⁻¹, ?_⟩
  field_simp
  linear_combination hdet

theorem isSquare_det_of_mem_inn (D : GL (Fin 2) K)
    (h : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 K D ∈
      (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range) :
    IsSquare ((D : Matrix (Fin 2) (Fin 2) K).det) := by
  obtain ⟨s, hs⟩ := h
  refine det_sq_aux ((s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
    ((s⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) (D : Matrix (Fin 2) (Fin 2) K)
    ((D⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ?_ ?_ s.2 ?_
  · rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  · rw [← Units.val_mul, inv_mul_cancel]; rfl
  · intro g
    have := congrArg (fun φ : MulAut SL(2, K) =>
      ((φ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) hs
    simpa [MulAut.conj_apply, LinearFlag.coe_slConjugation] using this

theorem gammaAct_sl2_of_not_inner_odd
    [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) (hfodd : Odd f)
    {A : Type} [Group A] [Finite A] (β : A →* MulAut SL(2, K)) (hA : IsRank23 A)
    (hni : ¬ β.range ≤ (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range) : gammaAct β = ⊤ := by
  have hf1 : 1 ≤ f := hfodd.pos
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h3 : 3 < Nat.card K := by
    rw [hK]
    omega
  have hOPP : IsOddPrimePower (Nat.card K) := isOddPrimePower_of hp hp2 hf1 hK
  by_cases hker : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ β.ker
  · obtain ⟨E, hE, hle⟩ := hker
    exact gammaAct_eq_top_of_le_ker β hE hle
  push Not at hker
  obtain ⟨hD, hγ, -⟩ := range_reduction β hA (fun E hE hle => hker E hE hle)
  rw [hγ]
  have : Finite ↥β.range := Finite.of_surjective _ β.rangeRestrict_surjective
  rcases hD.2 with hr2 | hr3
  · have h4 : Nat.card β.range = 4 := by
      rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr2]
      norm_num
    rcases GenLocL2SL.gammaAct_sl2_core hp hp2 hK h5 hD.1 h4 β.range.subtype with h | ⟨-, hinn⟩
    · exact h
    · exfalso
      apply hni
      rwa [Subgroup.range_subtype] at hinn
  · exfalso
    have h8 : Nat.card β.range = 8 := by
      rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr3]
      norm_num
    set ι : ↥β.range →* PGammaL2 K :=
      (GLS.IVK.Lifted.gammaOf hodd h3).comp β.range.subtype with hι
    have hιinj : Function.Injective ι :=
      (GLS.IVK.Lifted.gammaOf_injective hodd h3).comp Subtype.val_injective
    set E' : Subgroup (PGammaL2 K) := ι.range with hE'
    have hDsq : ∀ x : β.range, x * x = 1 := fun x =>
      WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD.1 x
    have hE2 : ∀ x ∈ E', x * x = 1 := by
      rintro _ ⟨x, rfl⟩
      rw [← map_mul, hDsq x, map_one]
    have hle := GenLocL2.pGammaL2_card_le_four_of_sq_of_odd hp hp2 hfodd hK E' hE2
    have hE8 : Nat.card E' = 8 := by
      rw [hE', ← h8]
      exact (Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv).symm
    omega

end GenLocL3Good

end CFSG.GH74.Generic.BProg.B2
