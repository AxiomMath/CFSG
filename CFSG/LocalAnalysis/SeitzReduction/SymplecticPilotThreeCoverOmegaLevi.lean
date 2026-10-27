module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverOddModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverOmega

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear blockDiagSL
  mem_blockDiagSL)
open CFSG.SeitzReduction.F4Pilot (gramSUToSL coe_gramSUToSL gramSUToSL_injective)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open scoped MatrixGroups

section Block

variable {K' : Type} [Field K'] {f : ℕ} (h : UnitaryFieldData 2 f K')

theorem eq_of_unitary_block {a b c d w x y z : K'} (h1 : h.bar a * w + h.bar c * y = 1)
    (h2 : h.bar a * x + h.bar c * z = 0) (h3 : h.bar b * w + h.bar d * y = 0)
    (h4 : h.bar b * x + h.bar d * z = 1) (h5 : a * d - b * c = 1) :
    w = h.bar d ∧ x = -h.bar c ∧ y = -h.bar b ∧ z = h.bar a := by
  have hE : h.bar a * h.bar d - h.bar b * h.bar c = 1 := by
    have := congrArg h.bar h5
    rwa [map_sub, map_mul, map_mul, map_one] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-w) * hE + h.bar d * h1 - h.bar c * h3
  · linear_combination (-x) * hE + h.bar d * h2 - h.bar c * h4
  · linear_combination (-y) * hE + h.bar a * h3 - h.bar b * h1
  · linear_combination (-z) * hE + h.bar a * h4 - h.bar b * h2

theorem lambdaUMat_eq (A : SpecialLinearGroup (Fin 2) K') :
    lambdaUMat h A = !![(A : Matrix (Fin 2) (Fin 2) K') 0 0, (A : Matrix (Fin 2) (Fin 2) K') 0 1,
      0, 0; (A : Matrix (Fin 2) (Fin 2) K') 1 0, (A : Matrix (Fin 2) (Fin 2) K') 1 1, 0, 0;
      0, 0, h.bar ((A : Matrix (Fin 2) (Fin 2) K') 1 1),
        h.bar (-(A : Matrix (Fin 2) (Fin 2) K') 1 0);
      0, 0, h.bar (-(A : Matrix (Fin 2) (Fin 2) K') 0 1),
        h.bar ((A : Matrix (Fin 2) (Fin 2) K') 0 0)] := by
  ext i j
  obtain ⟨u, rfl⟩ := (spModelIdx 2).surjective i
  obtain ⟨v, rfl⟩ := (spModelIdx 2).surjective j
  rw [lambdaUMat_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, CFSG.RankThree.CentralLift.leviUMat_apply]
  rcases u with a | a <;> rcases v with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] <;> rfl

theorem eq_lambdaUMat_of_blockDiag {g : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K'}
    (hu : (g.map h.bar)ᵀ * blockSwapJ (2 * 2) 2 * g = blockSwapJ (2 * 2) 2)
    (hblk : ∀ i j, (i ∈ twBlockSL 0 ↔ j ∉ twBlockSL 0) → g i j = 0)
    {A : SpecialLinearGroup (Fin 2) K'}
    (hA : (A : Matrix (Fin 2) (Fin 2) K') = !![g 0 0, g 0 1; g 1 0, g 1 1]) :
    g = lambdaUMat h A := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h1 := A.2
    rw [hA, Matrix.det_fin_two_of] at h1
    exact h1
  have hg : g = !![g 0 0, g 0 1, 0, 0; g 1 0, g 1 1, 0, 0; 0, 0, g 2 2, g 2 3;
      0, 0, g 3 2, g 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hblk, twBlockSL]
  have hu' := hu
  rw [hg] at hu'
  have e02 := congrFun (congrFun hu' 0) 2
  have e03 := congrFun (congrFun hu' 0) 3
  have e12 := congrFun (congrFun hu' 1) 2
  have e13 := congrFun (congrFun hu' 1) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, blockSwapJ] at e02 e03 e12 e13
  obtain ⟨hw, hx, hy, hz⟩ := eq_of_unitary_block h e02 e03 e12 e13 hdet
  rw [lambdaUMat_eq, hA]
  conv_lhs => rw [hg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hw, hx, hy, hz]

end Block

section Levi

variable {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2]
  {C₀ : GL (Fin (2 * 2)) K'}
  (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)

theorem gramSUToSL_mem_blockDiagSL_of_mem_centralizer_uTwTorus (hk : 4 ≤ Nat.card h.fixedField)
    {g : gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')}
    (hg : g ∈ centralizer (uTwTorus h hC₀ :
      Set (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')))) :
    gramSUToSL h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') g ∈
      blockDiagSL (K := K') (twBlockSL 0) := by
  have : Finite h.fixedField :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  obtain ⟨κ₀, hκ₀⟩ := exists_units_ne_one_of_four_le hk
  have hne := coe_units_ne_inv_of_ne_one hκ₀
  have e3 : ((κ₀ : h.fixedField) : K') ≠ (((κ₀⁻¹ : h.fixedFieldˣ) : h.fixedField) : K') :=
    fun e => hne (Subtype.ext e)
  have hd : uModelSU h hC₀ (tauSp (rootTorusHom h.fixedField 2 0 κ₀)) ∈ uTwTorus h hC₀ :=
    ⟨_, ⟨_, ⟨κ₀, rfl⟩, rfl⟩, rfl⟩
  have hc := mem_centralizer_iff.1 hg _ hd
  have hc' := congrArg (gramSUToSL h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) hc
  rw [map_mul, map_mul] at hc'
  rw [mem_blockDiagSL]
  intro i j hij
  apply eq_zero_of_commute_diagonal (d := gramSUToSL h _ (uModelSU h hC₀
    (tauSp (rootTorusHom h.fixedField 2 0 κ₀))))
    (by rw [coe_gramSUToSL]; exact coe_uModelSU_tauSp_rootTorusHom_zero h hC₀ κ₀) hc'
  fin_cases i <;> fin_cases j <;> simp [twBlockSL] at hij ⊢ <;>
    first | exact e3 | exact e3.symm | (simpa using e3) | (simpa using e3.symm)

theorem perfectCore_centralizer_uTwTorus_le (hk : 4 ≤ Nat.card h.fixedField) :
    perfectCore (centralizer (uTwTorus h hC₀ :
        Set (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')))) ≤ (lambdaU h hC₀).range := by
  have : Finite K' := h.finite
  set C := centralizer (uTwTorus h hC₀ :
    Set (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')))
  set ρ := gramSUToSL h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')
  set I : Finset (Fin (2 * 2)) := twBlockSL 0 with hI
  have hCρ : C.map ρ ≤ blockDiagSL (K := K') I := by
    rintro _ ⟨g, hg, rfl⟩
    exact gramSUToSL_mem_blockDiagSL_of_mem_centralizer_uTwTorus h hC₀ hk hg
  have hcomm : (⁅C, C⁆).map ρ ≤ blockSpecialLinear (K := K') I ⊔ blockSpecialLinear Iᶜ := by
    rw [Subgroup.map_commutator]
    exact (Subgroup.commutator_mono hCρ hCρ).trans (LinearPilot.commutator_blockDiagSL_le _)
  have hPC : perfectCore C ≤ ⁅C, C⁆ := by
    rw [← perfectCore_perfect C]
    exact Subgroup.commutator_mono (perfectCore_le C) (perfectCore_le C)
  intro g hg
  have hg1 : ρ g ∈ blockSpecialLinear (K := K') I ⊔ blockSpecialLinear Iᶜ :=
    hcomm ⟨g, hPC hg, rfl⟩
  have hg2 : ρ g ∈ blockDiagSL (K := K') I := hCρ ⟨g, perfectCore_le C hg, rfl⟩
  have hcomm' : ∀ (x : blockSpecialLinear (K := K') I) (y : blockSpecialLinear (K := K') Iᶜ),
      Commute ((blockSpecialLinear (K := K') I).subtype x)
        ((blockSpecialLinear (K := K') Iᶜ).subtype y) := fun x y =>
    LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right x.2 y.2
  have hr := MonoidHom.noncommCoprod_range _ _ hcomm'
  simp only [range_subtype] at hr
  rw [← hr] at hg1
  obtain ⟨⟨a, b⟩, hab⟩ := hg1
  change (a : SpecialLinearGroup (Fin (2 * 2)) K') * b = ρ g at hab
  have ha := mem_blockSpecialLinear.1 a.2
  have hb := mem_blockSpecialLinear.1 b.2
  have hentry : ∀ i j, j ∈ I → ((ρ g : SpecialLinearGroup (Fin (2 * 2)) K') :
      Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') i j =
        ((a : SpecialLinearGroup (Fin (2 * 2)) K') :
          Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') i j := by
    intro i j hj
    rw [← hab, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Finset.sum_eq_single j]
    · rw [hb j j (Or.inl (by simpa using hj)), Matrix.one_apply_eq, mul_one]
    · intro m _ hmj
      rw [hb m j (Or.inr (by simpa using hj)), Matrix.one_apply_ne hmj, mul_zero]
    · intro h0
      exact absurd (Finset.mem_univ j) h0
  have hamat : ((a : SpecialLinearGroup (Fin (2 * 2)) K') :
      Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') =
      !![(a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 0 0,
        (a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 0 1, 0, 0;
        (a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 1 0,
        (a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hI, twBlockSL]
  have hadet : (a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 0 0 *
      (a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 1 1 -
      (a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 0 1 *
      (a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 1 0 = 1 := by
    have h1 := (a : SpecialLinearGroup (Fin (2 * 2)) K').2
    rw [hamat] at h1
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ] at h1
    have hv : (![0, 0, 0, 1] : Fin 4 → K') (Fin.succAbove 1 2) = 1 := rfl
    linear_combination h1 + ((a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 0 1 *
      (a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 1 0) * hv
  set A : SpecialLinearGroup (Fin 2) K' :=
    ⟨!![(a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 0 0,
      (a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 0 1;
      (a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 1 0,
      (a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 1 1],
      by rw [Matrix.det_fin_two_of]; exact hadet⟩ with hAdef
  have hA : (A : Matrix (Fin 2) (Fin 2) K') =
      !![((g : GL (Fin (2 * 2)) K') : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 0 0,
        ((g : GL (Fin (2 * 2)) K') : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 0 1;
        ((g : GL (Fin (2 * 2)) K') : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 1 0,
        ((g : GL (Fin (2 * 2)) K') : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') 1 1] := by
    have e : ∀ i j, j ∈ I →
        ((g : GL (Fin (2 * 2)) K') : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') i j =
        (a : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') i j := fun i j hj => hentry i j hj
    rw [e 0 0 (by decide), e 0 1 (by decide), e 1 0 (by decide), e 1 1 (by decide)]
  obtain ⟨hu, -⟩ := mem_gramSU.1 g.2
  have hu' : (((g : GL (Fin (2 * 2)) K') : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K').map h.bar)ᵀ *
      blockSwapJ (2 * 2) 2 * ((g : GL (Fin (2 * 2)) K') : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') =
        blockSwapJ (2 * 2) 2 := by
    rw [← hC₀]
    exact hu
  have hgA := eq_lambdaUMat_of_blockDiag h hu'
    (fun i j hij => (mem_blockDiagSL.1 hg2) i j hij) hA
  refine ⟨A, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [coe_lambdaU]
  exact hgA.symm

theorem perfectCore_centralizer_uTwTorus_eq (hk : 4 ≤ Nat.card h.fixedField) :
    perfectCore (centralizer (uTwTorus h hC₀ :
        Set (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')))) = (lambdaU h hC₀).range :=
  le_antisymm (perfectCore_centralizer_uTwTorus_le h hC₀ hk)
    (range_lambdaU_le_perfectCore_centralizer_uTwTorus h hC₀ (hk.trans (natCard_fixedField_le h)))

end Levi

section Piece

open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore
  centralizerPerfectCore_le_centralizer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

omit [Finite G] in
theorem map_tauSp_rootTorusSp_eq {k : Type} [Field k] [CharP k 2] (ι : K ≃+* k) :
    ((rootTorusSp K 0).map tauSp).map (statedSpMap (ι : K →+* k) 2) =
      (rootTorusSp k 0).map tauSp := by
  ext x
  constructor
  · rintro ⟨_, ⟨_, ⟨κ, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, (statedSpMap_tauSp_rootTorusHom (ι : K →+* k) 0 κ).symm⟩
  · rintro ⟨_, ⟨μ, rfl⟩, rfl⟩
    set κ : Kˣ := Units.map (ι.symm : k →+* K) μ with hκ
    have hμ : Units.map (ι : K →+* k) κ = μ := by
      ext
      simp [hκ]
    refine ⟨_, ⟨_, ⟨κ, rfl⟩, rfl⟩, ?_⟩
    change statedSpMap (ι : K →+* k) 2 (tauSp (rootTorusHom K 2 0 κ)) = _
    rw [statedSpMap_tauSp_rootTorusHom, hμ]

theorem pieceCore_two_eq_map_lambdaU_of_N1 {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K')
    [CharP h.fixedField 2] {C₀ : GL (Fin (2 * 2)) K'}
    (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)
    (ι : K ≃+* h.fixedField) (Φ : gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') →* G)
    (hrange : Φ.range = neighbourCore e 0)
    (hker : Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')))
    (hN1 : ∀ x : StatedSp 2 K,
      Φ (uModelSU h hC₀ (statedSpMap (ι : K →+* h.fixedField) 2 (tauSp x))) =
        ((e.symm ((complSpEquiv 0 x : complSp K 0) : StatedSp 3 K) : L) : G)) :
    pieceCore e ({2} : Finset (Fin 3)) = (lambdaU h hC₀).range.map Φ := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : Finite K' := h.finite
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hkK : Nat.card h.fixedField = Nat.card K := (Nat.card_congr ι.toEquiv).symm
  have hk4 : 4 ≤ Nat.card h.fixedField := hkK ▸ hK4
  have hΦE : ∀ x, Φ x ∈ neighbourCore e 0 := fun x => hrange ▸ ⟨x, rfl⟩
  set Φ' := Φ.codRestrict _ hΦE with hΦ'
  have hΦ's : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hker' : Φ'.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) := by
    rw [hΦ', MonoidHom.ker_codRestrict]
    exact hker
  set Y := modelToG e ((rootTorusSp K 0).map (complSpHom (K := K) 0)) with hYdef
  have hY : Y ≤ neighbourCore e 0 := by
    refine (UnitaryPilot.modelToG_mono e ?_).trans
      (modelToG_complSp_le_neighbourCore e hK4 (by norm_num) 0)
    rintro _ ⟨x, -, rfl⟩
    exact (complSpEquiv 0 x).2
  rw [pieceCore_eq e (k := 0) (by decide), inf_centralizer_eq_of_le_sup (H := neighbourCore e 0)
    (X := modelToG e (rootTorusSp K 0)) (Y := Y) (centralizerPerfectCore_le_centralizer _)
    (UnitaryPilot.modelToG_mono e map_rootTorusSp_zero_le_leviTorusSp_two)
    (by
      rw [← UnitaryPilot.modelToG_sup]
      exact UnitaryPilot.modelToG_mono e leviTorusSp_two_le_sup),
    perfectCore_inf_centralizer_eq_map hY]
  have hTY := map_uModelSU_eq_of_N1 e 0 h hC₀ ι tauSp Φ hΦE hN1 (rootTorusSp K 0)
  rw [map_tauSp_rootTorusSp_eq ι, ← hΦ'] at hTY
  have hcore : perfectCore (centralizer ((Y.subgroupOf (neighbourCore e 0) :
      Subgroup (neighbourCore e 0)) : Set (neighbourCore e 0))) = (lambdaU h hC₀).range.map Φ' := by
    rw [← perfectCore_centralizer_uTwTorus_eq h hC₀ hk4]
    apply le_antisymm
    · exact le_map_perfectCore_centralizer Φ' hΦ's hker' (uTwTorus h hC₀) (perfectCore_perfect _)
        (by rw [uTwTorus, hTY]; exact perfectCore_le _)
    · have h2 := map_perfectCore_centralizer_le Φ' (uTwTorus h hC₀)
      rw [uTwTorus, hTY] at h2
      exact h2
  rw [hcore, Subgroup.map_map]
  rfl

end Piece

end CFSG.SeitzReduction.SymplecticPilot
