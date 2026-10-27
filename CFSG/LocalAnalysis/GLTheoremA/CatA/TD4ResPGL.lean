module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4ResDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieTwoEig
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912L3InnerDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2LinRes
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.GenNormality
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCent
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjKer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescTD4

open CFSG.Open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.PGLModel (projImage)
open Matrix

variable {π : Bool} {f : ℕ} {F : Type} [Field F] [Finite F]

private theorem odd_card_ker_projOf (hF : PiField π 2 f F) (hq : ModThree π (2 ^ f))
    (hf : 1 ≤ f) : Odd (Nat.card ↥(projOf (glPi π 3 (2 ^ f) F)).ker) := by
  rw [ker_projOf_eq_subgroupOf (glPi π 3 (2 ^ f) F)]
  have hdvd : Nat.card ↥((StatedScalars (Fin 3) F).subgroupOf
      (glPi π 3 (2 ^ f) F)) ∣ qSubPi π (2 ^ f) := by
    refine CFSG.SectionRank.OddCover.card_scalars_dvd (K := F) (n := 3) (by norm_num)
      (glPi π 3 (2 ^ f) F) (m := qSubPi π (2 ^ f)) ?_
    intro x c hc
    have hsc : GeneralLinearGroup.scalar (Fin 3) c ∈ glPi π 3 (2 ^ f) F := by
      rw [← hc]
      exact (x : ↥(glPi π 3 (2 ^ f) F)).2
    exact (mem_rootsOfUnity _ _).mp ((scalar_mem_glPi_iff hF c).mp hsc)
  rw [← Nat.not_even_iff_odd]
  intro he
  exact (Nat.not_even_iff_odd.mpr
    (CFSG.LocalAnalysis.GLTheoremA.KD1912.odd_qSubPi_two_pow (ε := π)
      (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hf))))
    (he.trans_dvd hdvd)

private theorem exists_sq_one_lift (hF : PiField π 2 f F) (hq : ModThree π (2 ^ f))
    (hf : 1 ≤ f) {s : ↥(projImage (glPi π 3 (2 ^ f) F))} (hs2 : s ^ 2 = 1) :
    ∃ U : ↥(glPi π 3 (2 ^ f) F), projOf _ U = s ∧ U ^ 2 = 1 :=
  CFSG.Alternating.Multipliers.exists_lift_sq_eq_one
    (ker_projOf_le_center (glPi π 3 (2 ^ f) F)) (odd_card_ker_projOf hF hq hf)
    (MonoidHom.mem_range.mpr ((projOf_surjective _) s)) hs2

private theorem mul_comm_of_proj_comm (hF : PiField π 2 f F) (hq : ModThree π (2 ^ f))
    (hf : 1 ≤ f) {x s : ↥(projImage (glPi π 3 (2 ^ f) F))}
    {X U : ↥(glPi π 3 (2 ^ f) F)} (hX : projOf _ X = x) (hU : projOf _ U = s)
    (hU2 : U ^ 2 = 1) (hxs : x * s = s * x) :
    (X : GL (Fin 3) F) * (U : GL (Fin 3) F) = (U : GL (Fin 3) F) * (X : GL (Fin 3) F) := by
  have hproj : projOf _ (X * U * X⁻¹ * U⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hX, hU]
    calc x * s * x⁻¹ * s⁻¹ = s * x * x⁻¹ * s⁻¹ := by rw [hxs]
      _ = 1 := by group
  have hker : (X * U * X⁻¹ * U⁻¹ : ↥(glPi π 3 (2 ^ f) F)) ∈ (projOf _).ker :=
    (MonoidHom.mem_ker).mpr hproj
  rw [mem_ker_projOf] at hker
  obtain ⟨c, hc⟩ := hker
  have hcoe : ((X * U * X⁻¹ * U⁻¹ : ↥(glPi π 3 (2 ^ f) F)) : GL (Fin 3) F) =
      (X : GL (Fin 3) F) * (U : GL (Fin 3) F) * (X : GL (Fin 3) F)⁻¹ *
        (U : GL (Fin 3) F)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe] at hc
  have hconj : (X : GL (Fin 3) F) * (U : GL (Fin 3) F) * (X : GL (Fin 3) F)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) c * (U : GL (Fin 3) F) := by
    calc (X : GL (Fin 3) F) * (U : GL (Fin 3) F) * (X : GL (Fin 3) F)⁻¹ =
        (X : GL (Fin 3) F) * (U : GL (Fin 3) F) * (X : GL (Fin 3) F)⁻¹ *
          (U : GL (Fin 3) F)⁻¹ * (U : GL (Fin 3) F) := by simp [mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin 3) c * (U : GL (Fin 3) F) := by rw [hc]
  have hU2' : (U : GL (Fin 3) F) * (U : GL (Fin 3) F) = 1 := by
    have := congrArg (fun y : ↥(glPi π 3 (2 ^ f) F) => (y : GL (Fin 3) F)) hU2
    simpa only [Subgroup.coe_mul, Subgroup.coe_one, pow_two] using this
  have hleft : ((X : GL (Fin 3) F) * (U : GL (Fin 3) F) * (X : GL (Fin 3) F)⁻¹) *
      ((X : GL (Fin 3) F) * (U : GL (Fin 3) F) * (X : GL (Fin 3) F)⁻¹) = 1 := by
    calc (X : GL (Fin 3) F) * (U : GL (Fin 3) F) * (X : GL (Fin 3) F)⁻¹ *
          ((X : GL (Fin 3) F) * (U : GL (Fin 3) F) * (X : GL (Fin 3) F)⁻¹) =
        (X : GL (Fin 3) F) * ((U : GL (Fin 3) F) * (U : GL (Fin 3) F)) *
          (X : GL (Fin 3) F)⁻¹ := by group
      _ = 1 := by rw [hU2']; group
  have hright : (GeneralLinearGroup.scalar (Fin 3) c * (U : GL (Fin 3) F)) *
      (GeneralLinearGroup.scalar (Fin 3) c * (U : GL (Fin 3) F)) =
        GeneralLinearGroup.scalar (Fin 3) (c * c) := by
    calc (GeneralLinearGroup.scalar (Fin 3) c * (U : GL (Fin 3) F)) *
          (GeneralLinearGroup.scalar (Fin 3) c * (U : GL (Fin 3) F)) =
        GeneralLinearGroup.scalar (Fin 3) c * (GeneralLinearGroup.scalar (Fin 3) c) *
          ((U : GL (Fin 3) F) * (U : GL (Fin 3) F)) := by
          rw [show GeneralLinearGroup.scalar (Fin 3) c * (U : GL (Fin 3) F) *
              (GeneralLinearGroup.scalar (Fin 3) c * (U : GL (Fin 3) F)) =
              GeneralLinearGroup.scalar (Fin 3) c *
                ((U : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c) *
                  (U : GL (Fin 3) F) by group,
            (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (U : GL (Fin 3) F)).eq]
          group
      _ = GeneralLinearGroup.scalar (Fin 3) (c * c) := by rw [hU2', map_mul]; simp
  rw [hconj] at hleft
  have hcc : c * c = 1 := by
    have hscale : GeneralLinearGroup.scalar (Fin 3) (c * c) = 1 := hright.symm.trans hleft
    have := congrArg (fun g : GL (Fin 3) F => ((g : Matrix (Fin 3) (Fin 3) F)) 0 0) hscale
    exact Units.ext (by simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this)
  have hcroot : c ∈ rootsOfUnity (qSubPi π (2 ^ f)) F := by
    refine (scalar_mem_glPi_iff hF c).mp ?_
    rw [hc]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (X * U * X⁻¹ * U⁻¹ : ↥(glPi π 3 (2 ^ f) F)).2
  have hc1 : c = 1 := by
    have hmem : (⟨c, hcroot⟩ : ↥(rootsOfUnity (qSubPi π (2 ^ f)) F)) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hcc
    have hodd : Odd (Nat.card ↥(rootsOfUnity (qSubPi π (2 ^ f)) F)) := by
      rw [card_rootsOfUnity_qSubPi hF hq]
      exact CFSG.LocalAnalysis.GLTheoremA.KD1912.odd_qSubPi_two_pow (ε := π)
        (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hf))
    exact congrArg Subtype.val
      (CFSG.Alternating.Multipliers.eq_one_of_sq_eq_one_of_odd hodd hmem)
  rw [hc1, map_one, one_mul] at hconj
  calc (X : GL (Fin 3) F) * (U : GL (Fin 3) F) =
      ((X : GL (Fin 3) F) * (U : GL (Fin 3) F) * (X : GL (Fin 3) F)⁻¹) *
        (X : GL (Fin 3) F) := by group
    _ = (U : GL (Fin 3) F) * (X : GL (Fin 3) F) := by rw [hconj]

private theorem not_type123_three_of_commuting_involution [CharP F 2]
    {X U : GL (Fin 3) F} (hU2 : U * U = 1) (hU1 : U ≠ 1) (hXU : X * U = U * X)
    (h3 : Type123 π (2 ^ f) F X 3) : False := by
  obtain ⟨-, -, hirr⟩ := h3
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hUU : (U : Matrix (Fin 3) (Fin 3) F) * U = 1 := by
    have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hU2
    simpa [Units.val_mul, Units.val_one] using this
  let N : Matrix (Fin 3) (Fin 3) F := (U : Matrix (Fin 3) (Fin 3) F) - 1
  have hUadd : (U : Matrix (Fin 3) (Fin 3) F) + U = 0 := by
    rw [← two_smul F (U : Matrix (Fin 3) (Fin 3) F), h2, zero_smul]
  have h1add : (1 : Matrix (Fin 3) (Fin 3) F) + 1 = 0 := by
    rw [← two_smul F (1 : Matrix (Fin 3) (Fin 3) F), h2, zero_smul]
  have hN2 : N * N = 0 := by
    dsimp only [N]
    rw [show (((U : Matrix (Fin 3) (Fin 3) F) - 1) *
          ((U : Matrix (Fin 3) (Fin 3) F) - 1)) =
        (U : Matrix (Fin 3) (Fin 3) F) * U -
          ((U : Matrix (Fin 3) (Fin 3) F) + U) + 1 by noncomm_ring]
    rw [hUU, hUadd, sub_zero]
    exact h1add
  have hN0 : N ≠ 0 := by
    intro hN
    apply hU1
    apply Units.ext
    exact sub_eq_zero.mp hN
  let W : Submodule F (Fin 3 → F) := LinearMap.ker (Matrix.toLin' N)
  have hWbot : W ≠ ⊥ := by
    intro hbot
    apply hN0
    have hker : ∀ v : Fin 3 → F, N *ᵥ v = 0 → v = 0 :=
      Matrix.ker_toLin'_eq_bot_iff.mp (show LinearMap.ker (Matrix.toLin' N) = ⊥ from hbot)
    ext i j
    have hzero := hker (N *ᵥ (Pi.single j 1 : Fin 3 → F)) (by
      calc N *ᵥ (N *ᵥ (Pi.single j 1 : Fin 3 → F)) =
          (N * N) *ᵥ (Pi.single j 1 : Fin 3 → F) :=
            (Matrix.mulVec_mulVec (Pi.single j 1) N N)
        _ = 0 := by rw [hN2, Matrix.zero_mulVec])
    simpa [Matrix.mulVec_single] using congrFun hzero i
  have hWtop : W ≠ ⊤ := by
    intro htop
    apply hN0
    ext i j
    have hv : (Pi.single j 1 : Fin 3 → F) ∈ W := by
      rw [htop]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv
    simpa [Matrix.mulVec_single] using congrFun hv i
  have hNX : N * (X : Matrix (Fin 3) (Fin 3) F) =
      (X : Matrix (Fin 3) (Fin 3) F) * N := by
    have hXUm : (X : Matrix (Fin 3) (Fin 3) F) * (U : Matrix (Fin 3) (Fin 3) F) =
        (U : Matrix (Fin 3) (Fin 3) F) * (X : Matrix (Fin 3) (Fin 3) F) := by
      have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hXU
      simpa [Units.val_mul] using this
    dsimp only [N]
    rw [sub_mul, mul_sub, mul_one, one_mul, hXUm]
  have hinv : ∀ v ∈ W, (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W := by
    intro v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv ⊢
    calc N *ᵥ ((X : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        (N * (X : Matrix (Fin 3) (Fin 3) F)) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = ((X : Matrix (Fin 3) (Fin 3) F) * N) *ᵥ v := by rw [hNX]
      _ = (X : Matrix (Fin 3) (Fin 3) F) *ᵥ (N *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  rcases hirr W hinv with h | h
  · exact hWbot h
  · exact hWtop h

private theorem not_type123_one_of_commuting_involution [CharP F 2]
    (hF : PiField π 2 f F) (hq : ModThree π (2 ^ f))
    {X U : GL (Fin 3) F} (hU2 : U * U = 1) (hU1 : U ≠ 1) (hXU : X * U = U * X)
    (h1 : Type123 π (2 ^ f) F X 1) : False := by
  obtain ⟨τ, hτ, hτ1, z, hz, g, -, hD⟩ := h1
  obtain ⟨ζ, -, hζ⟩ := exists_scalar_of_mem_zPi hF hq hτ hτ1 hz
  have hzU : z * U = U * z := by
    rw [← hζ]
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ U).eq.symm
  have hXzU : (X * z) * U = U * (X * z) := by
    calc X * z * U = X * (z * U) := by group
      _ = X * (U * z) := by rw [hzU]
      _ = (X * U) * z := by group
      _ = (U * X) * z := by rw [hXU]
      _ = U * (X * z) := by group
  have hconjXz : g⁻¹ * (X * z) * g = diagTau hτ := hD
  have hU'comm : (g⁻¹ * U * g) * (g⁻¹ * (X * z) * g) =
      (g⁻¹ * (X * z) * g) * (g⁻¹ * U * g) := by
    calc (g⁻¹ * U * g) * (g⁻¹ * (X * z) * g) =
        g⁻¹ * (U * (X * z)) * g := by group
      _ = g⁻¹ * ((X * z) * U) * g := by rw [← hXzU]
      _ = (g⁻¹ * (X * z) * g) * (g⁻¹ * U * g) := by group
  have hcommDiag : (g⁻¹ * U * g) * diagTau hτ = diagTau hτ * (g⁻¹ * U * g) := by
    rw [← hconjXz]
    exact hU'comm
  have hU'2 : (g⁻¹ * U * g) * (g⁻¹ * U * g) = 1 := by
    calc (g⁻¹ * U * g) * (g⁻¹ * U * g) = g⁻¹ * (U * U) * g := by group
      _ = 1 := by rw [hU2]; group
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  have hττ : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  have hd : Function.Injective ![τ, τ ^ 2, 1] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one] at hij ⊢
    all_goals first
      | rfl
      | exact absurd hij hτ1 | exact absurd hij.symm hτ1
      | exact absurd hij hτ2 | exact absurd hij.symm hτ2
      | exact absurd hij hττ | exact absurd hij.symm hττ
  have hU'2m : ((g⁻¹ * U * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ * U * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    have := congrArg (fun y : GL (Fin 3) F => (y : Matrix (Fin 3) (Fin 3) F)) hU'2
    simpa [Units.val_mul, Units.val_one] using this
  have hcommDiagM : ((g⁻¹ * U * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((diagTau hτ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((diagTau hτ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((g⁻¹ * U * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun y : GL (Fin 3) F => (y : Matrix (Fin 3) (Fin 3) F)) hcommDiag
    simpa [Units.val_mul] using this
  rw [coe_diagTau_eq_diagonal hτ] at hcommDiagM
  have hU'm : ((g⁻¹ * U * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.HDescLinRes.eq_one_of_commute_diagonal_of_mul_self_eq_one
      hd hcommDiagM.symm hU'2m
  have hconjU : g⁻¹ * U * g = 1 := Units.ext hU'm
  have hUeq : U = 1 := by
    calc U = g * (g⁻¹ * U * g) * g⁻¹ := by group
      _ = 1 := by rw [hconjU]; group
  exact hU1 hUeq

private theorem blockSL2_inf_statedScalars_eq_bot (hF : PiField π 2 f F) :
    CFSG.LocalAnalysis.GLTheoremA.KD1426Lie.blockSL2 hF ⊓ StatedScalars (Fin 3) F = ⊥ := by
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨hbB, hbS⟩ := Subgroup.mem_inf.mp hb
  obtain ⟨C, hC, rfl⟩ := Subgroup.mem_map.mp hbB
  obtain ⟨ζ, hζ⟩ := hbS
  have hπ : π = false → UnitaryFieldData 2 f F := fun h => by subst h; exact hF.unitary
  have hdetC : GeneralLinearGroup.det C = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    exact ((mem_slPi_iff hπ).mp hC).2
  have h00' : ((blockHom C : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
    rw [coe_blockHom, blockMat]
    rw [show ((GeneralLinearGroup.det C)⁻¹ : Fˣ) = 1 by rw [hdetC, inv_one]]
    rfl
  have hζ1 : ζ = 1 := by
    have h := congrArg (fun g : GL (Fin 3) F => ((g : Matrix (Fin 3) (Fin 3) F)) 0 0) hζ
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h
    rw [h00'] at h
    exact Units.ext h
  have hb1 : blockHom C = 1 := by rw [← hζ, hζ1, map_one]
  exact Subgroup.mem_bot.mpr hb1

private theorem exists_block_form_of_mem_glPi_inf_centralizer_diagE
    (hF : PiField π 2 f F) {e : Fˣ} (he1 : e ≠ 1) {q : GL (Fin 3) F}
    (hqH : q ∈ glPi π 3 (2 ^ f) F)
    (hqC : q ∈ Subgroup.centralizer ({diagE e} : Set (GL (Fin 3) F))) :
    ∃ (a : Fˣ) (B : GL (Fin 2) F), B ∈ glPi π 2 (2 ^ f) F ∧
      (q : Matrix (Fin 3) (Fin 3) F) = blockMat (a : F) (B : Matrix (Fin 2) (Fin 2) F) := by
  have hπ : π = false → UnitaryFieldData 2 f F := fun h => by subst h; exact hF.unitary
  have he1' : (e : F) ≠ 1 := fun h => he1 (Units.ext h)
  rw [Subgroup.mem_centralizer_singleton_iff] at hqC
  have hcomm := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hqC
  simp only [Units.val_mul, coe_diagE] at hcomm
  let d : Fin 3 → F := ![(e : F), (1 : F), (1 : F)]
  have hcomm' : (q : Matrix (Fin 3) (Fin 3) F) * diagonal d =
      diagonal d * (q : Matrix (Fin 3) (Fin 3) F) := by simpa [d] using hcomm
  have hz := fun i j (hij : d i ≠ d j) =>
    entry_eq_zero_of_commute_diagonal (i := i) (j := j) hcomm' hij
  have hq01 := hz 0 1 (by simp [d, he1'])
  have hq02 := hz 0 2 (by simp [d, he1'])
  have hq10 := hz 1 0 (by simp [d, he1'.symm])
  have hq20 := hz 2 0 (by simp [d, he1'.symm])
  set a : F := (q : Matrix (Fin 3) (Fin 3) F) 0 0 with ha
  set Bm : Matrix (Fin 2) (Fin 2) F :=
    !![(q : Matrix (Fin 3) (Fin 3) F) 1 1, (q : Matrix (Fin 3) (Fin 3) F) 1 2;
      (q : Matrix (Fin 3) (Fin 3) F) 2 1, (q : Matrix (Fin 3) (Fin 3) F) 2 2] with hBm
  have hqmat : (q : Matrix (Fin 3) (Fin 3) F) = blockMat a Bm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockMat, ha, hBm, hq01, hq02, hq10, hq20]
  have hdetq : (q : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
    (q.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) F →* F)).ne_zero
  have hdetB : Bm.det ≠ 0 := by
    intro h0
    apply hdetq
    rw [hqmat, det_blockMat, h0, mul_zero]
  have hdetq' : a * Bm.det = (q : Matrix (Fin 3) (Fin 3) F).det := by
    rw [hqmat, det_blockMat]
  have ha0 : a ≠ 0 := fun h0 => hdetq (by rw [← hdetq', h0, zero_mul])
  set aU : Fˣ := Units.mk0 a ha0 with haU
  set B : GL (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero Bm hdetB with hBU
  have hBv : (B : Matrix (Fin 2) (Fin 2) F) = Bm := GeneralLinearGroup.val_mkOfDetNeZero Bm hdetB
  have hBmem : B ∈ glPi π 2 (2 ^ f) F := by
    cases π
    · have h := hF.unitary
      rw [mem_glPi_false h, hBv]
      have hu := (mem_glPi_false h).mp hqH
      rw [hqmat, blockMat_map _ (map_zero _), blockMat_transpose, blockMat_mul,
        ← blockMat_one] at hu
      ext i j
      have := congrFun (congrFun hu i.succ) j.succ
      fin_cases i <;> fin_cases j <;> simpa [blockMat] using this
    · exact mem_glPi_true _ _
  refine ⟨aU, B, hBmem, ?_⟩
  rw [hqmat, haU, hBU, Units.val_mk0, GeneralLinearGroup.val_mkOfDetNeZero]

private theorem blockSL2_conj_mem (hF : PiField π 2 f F) {e : Fˣ} (he1 : e ≠ 1)
    {q b : GL (Fin 3) F}
    (hq : q ∈ glPi π 3 (2 ^ f) F ⊓
      Subgroup.centralizer ({diagE e} : Set (GL (Fin 3) F)))
    (hb : b ∈ CFSG.LocalAnalysis.GLTheoremA.KD1426Lie.blockSL2 hF) :
    q * b * q⁻¹ ∈ CFSG.LocalAnalysis.GLTheoremA.KD1426Lie.blockSL2 hF := by
  have hπ : π = false → UnitaryFieldData 2 f F := fun h => by subst h; exact hF.unitary
  obtain ⟨a, B, hBmem, hqmat⟩ :=
    exists_block_form_of_mem_glPi_inf_centralizer_diagE hF he1 (Subgroup.mem_inf.mp hq).1
      (Subgroup.mem_inf.mp hq).2
  obtain ⟨D, hD, rfl⟩ := Subgroup.mem_map.mp hb
  have hDdet : GeneralLinearGroup.det D = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    exact ((mem_slPi_iff hπ).mp hD).2
  have hbm : ((blockHom D : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blockMat (1 : F) (D : Matrix (Fin 2) (Fin 2) F) := by
    rw [coe_blockHom, hDdet, inv_one]
    rfl
  let A : GL (Fin 2) F := B * D * B⁻¹
  have hAsl : A ∈ slPi π 2 (2 ^ f) F :=
    CFSG.LocalAnalysis.GLTheoremA.KD1426Lie.conj_mem_slPi_two hF hBmem hD
  have hAdet : GeneralLinearGroup.det A = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    exact ((mem_slPi_iff hπ).mp hAsl).2
  have hblockA : ((blockHom A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blockMat (1 : F) ((B * D * B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [coe_blockHom, hAdet, inv_one, Units.val_one]
  have hqeq : q * blockHom D = blockHom A * q := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hqmat, hbm, hblockA, blockMat_mul, blockMat_mul]
    simp [mul_assoc]
  have hres : q * blockHom D * q⁻¹ = blockHom A := by
    calc q * blockHom D * q⁻¹ = (q * blockHom D) * q⁻¹ := by group
      _ = (blockHom A * q) * q⁻¹ := by rw [hqeq]
      _ = blockHom A := by group
  rw [hres]
  exact Subgroup.mem_map.mpr ⟨A, hAsl, rfl⟩

private theorem exists_scalar_commutator_lift (hF : PiField π 2 f F) (hq : ModThree π (2 ^ f))
    {x : ↥(projImage (glPi π 3 (2 ^ f) F))} {X : ↥(glPi π 3 (2 ^ f) F)}
    (hXmap : projOf _ X = x) {c : ↥(projImage (glPi π 3 (2 ^ f) F))}
    (hc : c ∈ Subgroup.centralizer ({x} : Set ↥(projImage (glPi π 3 (2 ^ f) F))))
    {h : ↥(glPi π 3 (2 ^ f) F)} (hhmap : projOf _ h = c) :
    ∃ t : Fˣ, (h : GL (Fin 3) F) * (X : GL (Fin 3) F) * (h : GL (Fin 3) F)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) t * (X : GL (Fin 3) F) := by
  obtain ⟨t, ht⟩ : ∃ t : Fˣ, GeneralLinearGroup.scalar (Fin 3) t =
      ((h * X * h⁻¹ * X⁻¹ : ↥(glPi π 3 (2 ^ f) F)) : GL (Fin 3) F) := by
    have hproj : projOf _ (h * X * h⁻¹ * X⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hhmap, hXmap]
      have hcx : (c : ↥(projImage (glPi π 3 (2 ^ f) F))) * x =
          x * (c : ↥(projImage (glPi π 3 (2 ^ f) F))) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hc
        exact hc
      rw [hcx]
      group
    exact (mem_ker_projOf (h * X * h⁻¹ * X⁻¹)).mp ((MonoidHom.mem_ker).mpr hproj)
  have ht' : (h : GL (Fin 3) F) * (X : GL (Fin 3) F) * (h : GL (Fin 3) F)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) t * (X : GL (Fin 3) F) := by
    have hcoe : ((h * X * h⁻¹ * X⁻¹ : ↥(glPi π 3 (2 ^ f) F)) : GL (Fin 3) F) =
        (h : GL (Fin 3) F) * (X : GL (Fin 3) F) * (h : GL (Fin 3) F)⁻¹ *
          (X : GL (Fin 3) F)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe] at ht
    calc (h : GL (Fin 3) F) * (X : GL (Fin 3) F) * (h : GL (Fin 3) F)⁻¹ =
        ((h : GL (Fin 3) F) * (X : GL (Fin 3) F) * (h : GL (Fin 3) F)⁻¹ *
          (X : GL (Fin 3) F)⁻¹) * (X : GL (Fin 3) F) := by group
      _ = GeneralLinearGroup.scalar (Fin 3) t * (X : GL (Fin 3) F) := by rw [← ht]
  exact ⟨t, ht'⟩

private theorem conj_lift_comm_diagE (hF : PiField π 2 f F) (hq : ModThree π (2 ^ f))
    {x : ↥(projImage (glPi π 3 (2 ^ f) F))} {X : ↥(glPi π 3 (2 ^ f) F)}
    (hXmap : projOf _ X = x) {e : Fˣ} (he1 : e ≠ 1)
    {z : GL (Fin 3) F} (hz : z ∈ zPi π 3 (2 ^ f) F) {g : GL (Fin 3) F}
    (hD : g⁻¹ * ((X : GL (Fin 3) F) * z) * g = diagE e)
    {c : ↥(projImage (glPi π 3 (2 ^ f) F))}
    (hc : c ∈ Subgroup.centralizer ({x} : Set ↥(projImage (glPi π 3 (2 ^ f) F))))
    {h : ↥(glPi π 3 (2 ^ f) F)} (hhmap : projOf _ h = c) :
    (g⁻¹ * (h : GL (Fin 3) F) * g) * diagE e =
      diagE e * (g⁻¹ * (h : GL (Fin 3) F) * g) := by
  haveI : CharP F 2 := hF.charP
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hF hq
  obtain ⟨t, ht'⟩ := exists_scalar_commutator_lift hF hq hXmap hc hhmap
  obtain ⟨ζ, -, hζ⟩ := exists_scalar_of_mem_zPi hF hq hτ hτ1 hz
  have hDsc : g⁻¹ * ((X : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) ζ) * g =
      diagE e := by
    simpa only [← hζ] using hD
  have hgX : g⁻¹ * (X : GL (Fin 3) F) * g =
      GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * diagE e := by
    calc g⁻¹ * (X : GL (Fin 3) F) * g =
        (g⁻¹ * (X : GL (Fin 3) F) * g * GeneralLinearGroup.scalar (Fin 3) ζ) *
          (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by group
      _ = (g⁻¹ * (X : GL (Fin 3) F) * (g * GeneralLinearGroup.scalar (Fin 3) ζ)) *
          (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by
          rw [show g⁻¹ * (X : GL (Fin 3) F) * g * GeneralLinearGroup.scalar (Fin 3) ζ =
              g⁻¹ * (X : GL (Fin 3) F) * (g * GeneralLinearGroup.scalar (Fin 3) ζ) by group]
      _ = (g⁻¹ * (X : GL (Fin 3) F) * (GeneralLinearGroup.scalar (Fin 3) ζ * g)) *
          (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by
          rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ g).eq]
      _ = (g⁻¹ * ((X : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) ζ) * g) *
          (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by group
      _ = diagE e * (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by rw [hDsc]
      _ = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * diagE e := by
          rw [show (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ =
              GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ from
                (map_inv (GeneralLinearGroup.scalar (Fin 3)) ζ).symm,
            (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ⁻¹ (diagE e)).eq]
  have hdiag : diagE e = GeneralLinearGroup.scalar (Fin 3) ζ *
      (g⁻¹ * (X : GL (Fin 3) F) * g) := by
    rw [hgX, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  let q : GL (Fin 3) F := g⁻¹ * (h : GL (Fin 3) F) * g
  have hqXq : q * (g⁻¹ * (X : GL (Fin 3) F) * g) * q⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) t * (g⁻¹ * (X : GL (Fin 3) F) * g) := by
    dsimp only [q]
    calc (g⁻¹ * (h : GL (Fin 3) F) * g) *
          (g⁻¹ * (X : GL (Fin 3) F) * g) * (g⁻¹ * (h : GL (Fin 3) F) * g)⁻¹ =
        g⁻¹ * ((h : GL (Fin 3) F) * (X : GL (Fin 3) F) * (h : GL (Fin 3) F)⁻¹) * g := by group
      _ = g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) t * (X : GL (Fin 3) F)) * g := by rw [ht']
      _ = GeneralLinearGroup.scalar (Fin 3) t * (g⁻¹ * (X : GL (Fin 3) F) * g) := by
          rw [show g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) t * (X : GL (Fin 3) F)) * g =
              (g⁻¹ * GeneralLinearGroup.scalar (Fin 3) t) * (X : GL (Fin 3) F) * g by group,
            (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar t g⁻¹).eq]
          group
  have hqdiag : q * diagE e * q⁻¹ = GeneralLinearGroup.scalar (Fin 3) t * diagE e := by
    rw [hdiag]
    calc q * (GeneralLinearGroup.scalar (Fin 3) ζ *
          (g⁻¹ * (X : GL (Fin 3) F) * g)) * q⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) ζ *
          (q * (g⁻¹ * (X : GL (Fin 3) F) * g) * q⁻¹) := by
          rw [show q * (GeneralLinearGroup.scalar (Fin 3) ζ *
              (g⁻¹ * (X : GL (Fin 3) F) * g)) * q⁻¹ =
              (q * GeneralLinearGroup.scalar (Fin 3) ζ) *
                (g⁻¹ * (X : GL (Fin 3) F) * g) * q⁻¹ by group,
            (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ q).eq]
          group
      _ = GeneralLinearGroup.scalar (Fin 3) ζ *
          (GeneralLinearGroup.scalar (Fin 3) t * (g⁻¹ * (X : GL (Fin 3) F) * g)) := by
          rw [hqXq]
      _ = GeneralLinearGroup.scalar (Fin 3) t *
          (GeneralLinearGroup.scalar (Fin 3) ζ * (g⁻¹ * (X : GL (Fin 3) F) * g)) := by
          rw [show GeneralLinearGroup.scalar (Fin 3) ζ *
              (GeneralLinearGroup.scalar (Fin 3) t * (g⁻¹ * (X : GL (Fin 3) F) * g)) =
              (GeneralLinearGroup.scalar (Fin 3) ζ * GeneralLinearGroup.scalar (Fin 3) t) *
                (g⁻¹ * (X : GL (Fin 3) F) * g) by group,
            show GeneralLinearGroup.scalar (Fin 3) ζ * GeneralLinearGroup.scalar (Fin 3) t =
              GeneralLinearGroup.scalar (Fin 3) t * GeneralLinearGroup.scalar (Fin 3) ζ by
              rw [← map_mul, ← map_mul, mul_comm]]
          group
  have htrace := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F).trace) hqdiag
  simp only [Units.val_mul] at htrace
  rw [Matrix.trace_units_conj] at htrace
  rw [← Units.val_mul] at htrace
  have htsc : GeneralLinearGroup.scalar (Fin 3) t * diagE e =
      diagE e * GeneralLinearGroup.scalar (Fin 3) t :=
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar t (diagE e)).eq.symm
  rw [htsc, trace_mul_scalar, trace_diagE] at htrace
  have hte : (e : F) = (t : F) * (e : F) := by
    simpa [h2] using htrace
  have he0 : (e : F) ≠ 0 := e.ne_zero
  have ht1 : t = 1 := by
    apply Units.ext
    have : (t : F) * (e : F) = 1 * (e : F) := by rw [← hte, one_mul]
    exact mul_right_cancel₀ he0 this
  calc q * diagE e = (q * diagE e * q⁻¹) * q := by group
    _ = diagE e * q := by rw [hqdiag, ht1, map_one, one_mul]

private theorem layer_ne_bot_of_type_two (hF : PiField π 2 f F) (hq : ModThree π (2 ^ f))
    (hq4 : 4 ≤ 2 ^ f)
    {x : ↥(projImage (glPi π 3 (2 ^ f) F))} {X : ↥(glPi π 3 (2 ^ f) F)}
    (hXmap : projOf _ X = x)
    {e : Fˣ} (he3 : (e : F) ^ 3 = 1) (he1 : e ≠ 1)
    {z : GL (Fin 3) F} (hz : z ∈ zPi π 3 (2 ^ f) F)
    {g : GL (Fin 3) F} (hg : g ∈ glPi π 3 (2 ^ f) F)
    (hD : g⁻¹ * ((X : GL (Fin 3) F) * z) * g = diagE e) :
    GLAPLayer 3 (Subgroup.centralizer ({x} : Set ↥(projImage (glPi π 3 (2 ^ f) F)))) ≠ ⊥ := by
  have hπ : π = false → UnitaryFieldData 2 f F := fun h => by subst h; exact hF.unitary
  have hf : 1 ≤ f := hF.one_le
  have hq2 : 2 < 2 ^ f := by omega
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hF hq
  let H := glPi π 3 (2 ^ f) F
  let gH : ↥H := ⟨g, hg⟩
  have hzp : zPi π 3 (2 ^ f) F ≤ H := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  let zH : ↥H := ⟨z, hzp hz⟩
  have hzproj : projOf H zH = 1 := by
    exact (mem_ker_projOf zH).mpr (mem_statedScalars_of_mem_zPi hF hq hτ hτ1 hz)
  have hdiagH : diagE e ∈ H :=
    CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagE_mem_glPi hF (fun hπf => by
      subst hπf
      exact pow_succ_eq_one_of_modThree hq he3)
  let dE : ↥H := ⟨diagE e, hdiagH⟩
  have hD' : gH⁻¹ * (X * zH) * gH = dE := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hD
  have hXz : X * zH = gH * dE * gH⁻¹ := by
    calc X * zH = gH * (gH⁻¹ * (X * zH) * gH) * gH⁻¹ := by group
      _ = gH * dE * gH⁻¹ := by rw [hD']
  have hx_diag : x = (projOf H gH) * (projOf H dE) * (projOf H gH)⁻¹ := by
    calc x = projOf H X := hXmap.symm
      _ = projOf H (X * zH) := by rw [map_mul, hzproj, mul_one]
      _ = projOf H (gH * dE * gH⁻¹) := by rw [hXz]
      _ = projOf H gH * projOf H dE * (projOf H gH)⁻¹ := by rw [map_mul, map_mul, map_inv]
  let B : Subgroup (GL (Fin 3) F) := CFSG.LocalAnalysis.GLTheoremA.KD1426Lie.blockSL2 hF
  have hB_le_slPi : B ≤ slPi π 3 (2 ^ f) F :=
    CFSG.LocalAnalysis.GLTheoremA.KD1426Lie.blockSL2_le_slPi hF
  have hB_le_H : B ≤ H := le_trans hB_le_slPi (slPi_le_glPi hπ)
  let BH : Subgroup ↥H := B.subgroupOf H
  let Bconj : Subgroup ↥H := BH.map (MulAut.conj gH).toMonoidHom
  let L : Subgroup ↥(projImage H) := Bconj.map (projOf H)
  let C : Subgroup ↥(projImage H) := Subgroup.centralizer ({x} : Set ↥(projImage H))
  have hLC : L ≤ C := by
    intro l hl
    obtain ⟨b, hb, hlb⟩ := Subgroup.mem_map.mp hl
    obtain ⟨b₀, hb₀, hb₀val⟩ := Subgroup.mem_map.mp hb
    have hb₀B : (b₀ : GL (Fin 3) F) ∈ B := Subgroup.mem_subgroupOf.mp hb₀
    have hb₀C : ((b₀ : ↥H) : GL (Fin 3) F) * diagE e = diagE e * ((b₀ : ↥H) : GL (Fin 3) F) := by
      have := CFSG.LocalAnalysis.GLTheoremA.KD1426Lie.blockSL2_le_centralizer hF e hb₀B
      rwa [Subgroup.mem_centralizer_singleton_iff] at this
    have hb₀d : (b₀ : ↥H) * dE = dE * (b₀ : ↥H) := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using hb₀C
    rw [Subgroup.mem_centralizer_singleton_iff]
    set gbar : ↥(projImage H) := projOf H gH
    set dbar : ↥(projImage H) := projOf H dE
    have hbmap : projOf H ((MulAut.conj gH).toMonoidHom b₀) = gbar * projOf H b₀ * gbar⁻¹ := by
      dsimp only [gbar]
      rw [show (MulAut.conj gH).toMonoidHom b₀ = gH * b₀ * gH⁻¹ from rfl, map_mul, map_mul,
        map_inv]
    have hb₀bar : projOf H b₀ * dbar = dbar * projOf H b₀ := by
      dsimp only [dbar]
      rw [← map_mul, ← map_mul, hb₀d]
    rw [← hlb, ← hb₀val, hbmap, hx_diag]
    calc (gbar * projOf H b₀ * gbar⁻¹) * (gbar * dbar * gbar⁻¹) =
        gbar * projOf H b₀ * dbar * gbar⁻¹ := by group
      _ = gbar * (projOf H b₀ * dbar) * gbar⁻¹ := by group
      _ = gbar * (dbar * projOf H b₀) * gbar⁻¹ := by rw [hb₀bar]
      _ = gbar * dbar * projOf H b₀ * gbar⁻¹ := by group
      _ = gbar * dbar * gbar⁻¹ * (gbar * projOf H b₀ * gbar⁻¹) := by group
  have hN : (L.subgroupOf C).Normal := by
    refine ⟨fun l hl c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    obtain ⟨b, hb, hlb⟩ := Subgroup.mem_map.mp hl
    obtain ⟨b₀, hb₀, hb₀val⟩ := Subgroup.mem_map.mp hb
    have hb₀B : (b₀ : GL (Fin 3) F) ∈ B := Subgroup.mem_subgroupOf.mp hb₀
    obtain ⟨h, hhmap⟩ := projOf_surjective H (c : ↥(projImage H))
    let q : GL (Fin 3) F := g⁻¹ * (h : GL (Fin 3) F) * g
    have hqcomm := conj_lift_comm_diagE hF hq hXmap he1 hz hD c.2 hhmap
    have hqH : q ∈ H := mul_mem (mul_mem (inv_mem hg) h.2) hg
    have hqC : q ∈ Subgroup.centralizer ({diagE e} : Set (GL (Fin 3) F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hqcomm
    have hconjB : q * (b₀ : GL (Fin 3) F) * q⁻¹ ∈ B :=
      blockSL2_conj_mem hF he1 (Subgroup.mem_inf.mpr ⟨hqH, hqC⟩) hb₀B
    let qH' : ↥H := ⟨q * (b₀ : GL (Fin 3) F) * q⁻¹, hB_le_H hconjB⟩
    have hh_eq : (h : ↥H) = gH * ⟨q, hqH⟩ * gH⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      dsimp only [gH, q]
      group
    have hprod : h * b * h⁻¹ = gH * qH' * gH⁻¹ := by
      rw [← hb₀val, hh_eq]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((MulAut.conj gH).toMonoidHom b₀ : ↥H) = gH * b₀ * gH⁻¹ from rfl]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      dsimp only [qH']
      group
    have hmem : (MulAut.conj gH).toMonoidHom qH' ∈ Bconj :=
      Subgroup.mem_map.mpr ⟨qH', Subgroup.mem_subgroupOf.mpr hconjB, rfl⟩
    have hval : ((c * l * c⁻¹ : ↥C) : ↥(projImage H)) =
        projOf H (h * b * h⁻¹) := by
      calc ((c * l * c⁻¹ : ↥C) : ↥(projImage H)) =
          (c : ↥(projImage H)) * (l : ↥(projImage H)) * (c : ↥(projImage H))⁻¹ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        _ = projOf H h * projOf H b * (projOf H h)⁻¹ := by
            rw [← hhmap, ← hlb]
        _ = projOf H (h * b * h⁻¹) := by
            rw [map_mul, map_mul, map_inv]
    rw [hval, hprod]
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  let φB : ↥B →* ↥(projImage H) :=
    (projOf H).comp ((MulAut.conj gH).toMonoidHom.comp (Subgroup.inclusion hB_le_H))
  have hφBinj : Function.Injective φB := by
    intro b c hbc
    let bH : ↥H := (Subgroup.inclusion hB_le_H) b
    let cH : ↥H := (Subgroup.inclusion hB_le_H) c
    have hbc' : projOf H ((MulAut.conj gH) bH) = projOf H ((MulAut.conj gH) cH) := by
      apply Subtype.ext
      simpa only [φB, MonoidHom.comp_apply, bH, cH, MulEquiv.coe_toMonoidHom] using
        congrArg Subtype.val hbc
    have hker : (MulAut.conj gH) (bH * cH⁻¹) ∈ (projOf H).ker := by
      rw [MonoidHom.mem_ker]
      calc projOf H ((MulAut.conj gH) (bH * cH⁻¹)) =
          projOf H ((MulAut.conj gH) bH) * (projOf H ((MulAut.conj gH) cH))⁻¹ := by
            rw [map_mul, map_inv, map_mul, map_inv]
        _ = 1 := by rw [hbc']; group
    have hkerS : (((MulAut.conj gH) (bH * cH⁻¹) : ↥H) : GL (Fin 3) F) ∈
        StatedScalars (Fin 3) F := (mem_ker_projOf _).mp hker
    have hxeq : ((bH * cH⁻¹ : ↥H) : GL (Fin 3) F) =
        g⁻¹ * (((MulAut.conj gH) (bH * cH⁻¹) : ↥H) : GL (Fin 3) F) * g := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((MulAut.conj gH) (bH * cH⁻¹) : ↥H) = gH * (bH * cH⁻¹) * gH⁻¹ from rfl]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      dsimp only [gH, bH, cH, Subgroup.coe_inclusion]
      group
    have hscalar : ((bH * cH⁻¹ : ↥H) : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F := by
      rw [hxeq]
      exact (inv_conj_mem_statedScalars_iff (g := (gH : GL (Fin 3) F))
        (((MulAut.conj gH) (bH * cH⁻¹) : ↥H) : GL (Fin 3) F)).mpr hkerS
    have hBmem : ((bH * cH⁻¹ : ↥H) : GL (Fin 3) F) ∈ B := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      simp only [bH, cH, Subgroup.coe_inclusion]
      exact mul_mem b.2 (inv_mem c.2)
    have hone : ((bH * cH⁻¹ : ↥H) : GL (Fin 3) F) = 1 := by
      have hmem : ((bH * cH⁻¹ : ↥H) : GL (Fin 3) F) ∈ B ⊓ StatedScalars (Fin 3) F :=
        Subgroup.mem_inf.mpr ⟨hBmem, hscalar⟩
      rw [blockSL2_inf_statedScalars_eq_bot hF] at hmem
      simpa using hmem
    have hbcH : bH = cH := by
      have h1 : bH * cH⁻¹ = 1 := Subtype.ext hone
      calc bH = (bH * cH⁻¹) * cH := by group
        _ = 1 * cH := by rw [h1]
        _ = cH := one_mul cH
    exact Subtype.ext (by
      simpa only [bH, cH, Subgroup.coe_inclusion] using congrArg Subtype.val hbcH)
  have hrange : φB.range = L := by
    ext l
    constructor
    · rintro ⟨b, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(MulAut.conj gH) ⟨(b : GL (Fin 3) F), hB_le_H b.2⟩,
        Subgroup.mem_map.mpr ⟨⟨(b : GL (Fin 3) F), hB_le_H b.2⟩,
          Subgroup.mem_subgroupOf.mpr b.2, rfl⟩, rfl⟩
    · intro hl
      obtain ⟨b, hb, hbl⟩ := Subgroup.mem_map.mp hl
      obtain ⟨b₀, hb₀, hb₀val⟩ := Subgroup.mem_map.mp hb
      refine ⟨⟨(b₀ : GL (Fin 3) F), Subgroup.mem_subgroupOf.mp hb₀⟩, ?_⟩
      apply Subtype.ext
      rw [← hbl, ← hb₀val]
      rfl
  let e : ↥B ≃* ↥L :=
    (MonoidHom.ofInjective hφBinj).trans (MulEquiv.subgroupCongr hrange)
  have hLq : CFSG.Open.IsQuasisimple ↥L :=
    CFSG.LocalAnalysis.GLTheoremA.KD1426Common.isQuasisimple_of_mulEquiv e
      (CFSG.LocalAnalysis.GLTheoremA.KD1426Lie.blockSL2_quasisimple hF hq hq2)
  have h3B : 3 ∣ Nat.card ↥B :=
    CFSG.LocalAnalysis.GLTheoremA.KD1426Lie.three_dvd_card_blockSL2 hF hq he3 he1
  have h3L : 3 ∣ Nat.card ↥L := by
    rw [← Nat.card_congr e.toEquiv]
    exact h3B
  have hLdvd : 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.three_dvd_card_quotient_center hLq.1 h3L
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_normal_quasisimple
    Nat.prime_three hLC hN hLq hLdvd

theorem glaPLayer_centralizer_ne_bot_projImage_glPi (hF : PiField π 2 f F)
    (hq : ModThree π (2 ^ f)) (hq4 : 4 ≤ 2 ^ f)
    {x s : ↥(projImage (glPi π 3 (2 ^ f) F))} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hs : orderOf s = 2) (hxs : x * s = s * x) :
    GLAPLayer 3 (Subgroup.centralizer ({x} : Set ↥(projImage (glPi π 3 (2 ^ f) F)))) ≠ ⊥ := by
  have hf : 1 ≤ f := hF.one_le
  haveI : CharP F 2 := hF.charP
  have hs2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  obtain ⟨X, hXmap⟩ := projOf_surjective _ x
  obtain ⟨U, hUmap, hU2⟩ := exists_sq_one_lift hF hq hf hs2
  have hU2m : (U : GL (Fin 3) F) * (U : GL (Fin 3) F) = 1 := by
    have := congrArg (fun y : ↥(glPi π 3 (2 ^ f) F) => (y : GL (Fin 3) F)) hU2
    simpa only [Subgroup.coe_mul, Subgroup.coe_one, pow_two] using this
  have hUX : (X : GL (Fin 3) F) * (U : GL (Fin 3) F) =
      (U : GL (Fin 3) F) * (X : GL (Fin 3) F) :=
    mul_comm_of_proj_comm hF hq hf hXmap hUmap hU2 hxs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have hU1 : U ≠ 1 := by
    intro h
    apply hs1
    rw [← hUmap, h]
    rfl
  have hU1m : (U : GL (Fin 3) F) ≠ 1 := fun h => hU1 (Subtype.ext h)
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hF hq
  have hXH : (X : GL (Fin 3) F) ∈ glPi π 3 (2 ^ f) F := X.2
  have hXZ : (X : GL (Fin 3) F) ∉ zPi π 3 (2 ^ f) F := by
    intro hz
    have hsc := mem_statedScalars_of_mem_zPi hF hq hτ hτ1 hz
    apply hx1
    apply Subtype.ext
    rw [← hXmap, coe_projOf, mk_eq_one_iff_mem_statedScalars.mpr hsc]
    rfl
  have hX3 : (X : GL (Fin 3) F) ^ 3 ∈ zPi π 3 (2 ^ f) F := by
    let Zx : ↥(glPi π 3 (2 ^ f) F) := X ^ 3
    have hproj : projOf _ Zx = 1 := by
      dsimp only [Zx]
      rw [map_pow, hXmap, hx3]
    have hcenter : Zx ∈ Subgroup.center (glPi π 3 (2 ^ f) F) :=
      ker_projOf_le_center (glPi π 3 (2 ^ f) F) ((MonoidHom.mem_ker).mpr hproj)
    have hmem : (X : GL (Fin 3) F) ^ 3 ∈ zPi π 3 (2 ^ f) F :=
      Subgroup.mem_map.mpr ⟨Zx, hcenter, rfl⟩
    simpa only [Zx, Subgroup.coe_pow] using hmem
  rcases type123_exhaust hF hq hXH hXZ hX3 with h1 | h2 | h3
  · exact absurd h1 (not_type123_one_of_commuting_involution hF hq hU2m hU1m hUX)
  ·
    obtain ⟨e, he3, he1, z, hz, g, hg, hD⟩ := h2
    exact layer_ne_bot_of_type_two hF hq hq4 hXmap he3 he1 hz hg hD
  · exact absurd h3 (not_type123_three_of_commuting_involution hU2m hU1m hUX)


theorem pglThreeInvGood_holds : PGLThreeInvGood := by
  constructor
  · intro n hn2 hneven F _ _ hcard x s hx3 hx1 hs hxs
    have hf : 1 ≤ n := by omega
    have hF : PiField true 2 n F :=
      ⟨Nat.prime_two, hf, by simpa [piCard] using hcard⟩
    have hq : ModThree true (2 ^ n) := CFSG.two_pow_mod_three_of_even hneven
    have hq4 : 4 ≤ 2 ^ n := by
      have h : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      norm_num at h
      exact h
    exact glaPLayer_centralizer_ne_bot_projImage_glPi hF hq hq4 hx3 hx1 hs hxs
  · intro n hn2 hnodd F _ _ hcard x s hx3 hx1 hs hxs
    have hf : 1 ≤ n := by omega
    have hF : PiField false 2 n F :=
      ⟨Nat.prime_two, hf, by simpa [piCard] using hcard⟩
    have hq : ModThree false (2 ^ n) := CFSG.two_pow_mod_three_of_odd hnodd
    have hq4 : 4 ≤ 2 ^ n := by
      have h : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      norm_num at h
      exact h
    exact glaPLayer_centralizer_ne_bot_projImage_glPi hF hq hq4 hx3 hx1 hs hxs

end CFSG.LocalAnalysis.GLTheoremA.HDescTD4
