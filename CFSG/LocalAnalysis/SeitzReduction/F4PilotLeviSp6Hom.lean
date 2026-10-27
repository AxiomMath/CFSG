module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Chevalley (baseChangeGL baseChangeGL_pinnedX baseChangeGL_injective)
open scoped Matrix

section SpDescent

variable {K₀ K : Type} [Field K₀] [Field K]

theorem isSymplectic_of_mem_statedSp {n : ℕ} {A : GL (Fin n ⊕ Fin n) K}
    (hA : A ∈ StatedSp n K) :
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Matrix.fromBlocks 0 1 (-1) 0 := by
  induction hA using closure_induction with
  | mem A hA => exact hA
  | one => simp
  | mul A B _ _ hA hB =>
    rw [Units.val_mul, Matrix.transpose_mul]
    calc (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
          (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
            ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
              (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
        = (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
            ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
              (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) *
                (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.fromBlocks 0 1 (-1) 0 := by rw [hA, hB]
  | inv A _ hA =>
    set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := A.val with hM
    set N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := (A⁻¹).val with hN
    have hAA : M * N = 1 := by
      rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc Nᵀ * Matrix.fromBlocks 0 1 (-1) 0 * N
        = Nᵀ * (Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M) * N := by rw [hA]
      _ = (M * N)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * (M * N) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Matrix.fromBlocks 0 1 (-1) 0 := by
          rw [hAA, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem statedSpMap_comp {K₁ : Type} [Field K₁] (κ : K₀ →+* K₁) (ι : K₁ →+* K) (n : ℕ)
    (g : StatedSp n K₀) :
    statedSpMap ι n (statedSpMap κ n g) = statedSpMap (ι.comp κ) n g := by
  ext i j
  simp [coe_statedSpMap]

theorem range_statedSpMap_eq_eqLocus (ι : K₀ →+* K) (σ : K →+* K)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) (n : ℕ) :
    (statedSpMap ι n).range = MonoidHom.eqLocus (statedSpMap σ n) (MonoidHom.id _) := by
  ext A
  constructor
  · rintro ⟨B, rfl⟩
    change statedSpMap σ n (statedSpMap ι n B) = statedSpMap ι n B
    have hσι : σ.comp ι = ι := RingHom.ext fun x => (hfix (ι x)).2 ⟨x, rfl⟩
    rw [statedSpMap_comp, hσι]
  · intro hA
    change statedSpMap σ n A = A at hA
    have hent : ∀ i j, ∃ b : K₀, ι b =
        ((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) i j := by
      intro i j
      have h := congrArg (fun g : StatedSp n K =>
        ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) i j) hA
      simp only [coe_statedSpMap, coe_map_GL, Matrix.map_apply] at h
      exact (hfix _).1 h
    choose b hb using hent
    set B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K₀ := Matrix.of b with hB
    have hBA :
        B.map ι = ((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
      ext i j
      simp [hB, hb]
    have hdet : B.det ≠ 0 := by
      intro h0
      have h1 := RingHom.map_det ι B
      rw [h0, map_zero, RingHom.mapMatrix_apply, hBA] at h1
      exact (Matrix.GeneralLinearGroup.det (A : GL (Fin n ⊕ Fin n) K)).ne_zero (by
        rw [Matrix.GeneralLinearGroup.val_det_apply]
        exact h1.symm)
    set B' : GL (Fin n ⊕ Fin n) K₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero B hdet
    have hB' : (B' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K₀) = B := rfl
    have hsp : B' ∈ StatedSp n K₀ := by
      refine subset_closure ?_
      change (B' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K₀)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
          (B' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K₀) = Matrix.fromBlocks 0 1 (-1) 0
      rw [← isSymplectic_map_iff ι, hB', hBA]
      exact isSymplectic_of_mem_statedSp A.2
    refine ⟨⟨B', hsp⟩, ?_⟩
    ext i j
    simp only [coe_statedSpMap, coe_map_GL, Matrix.map_apply, hB']
    rw [← hBA, Matrix.map_apply]

end SpDescent

section RootElements


variable {K M : Type} [Field K] [Field M]

theorem coe_f4Par_eq_pinnedX {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (c : K) :
    ((Adjoint.f4Par K γ c : adjointGroup .F4 K) : ModGL .F4 K) =
      pinnedX .F4 K γ (((Chevalley.rootOperatorFamily .F4).pinnedFamilySign γ : K) * c) := by
  have h := (Chevalley.rootOperatorFamily .F4).pinnedX_eq_eltUnit K hγ
    (((Chevalley.rootOperatorFamily .F4).pinnedFamilySign γ : K) * c)
  rw [← mul_assoc, (Chevalley.rootOperatorFamily .F4).pinnedFamilySign_mul_self K γ,
    one_mul] at h
  change ((Adjoint.xPar (Chevalley.rootOperatorFamily .F4) γ c : adjointGroup .F4 K) :
    ModGL .F4 K) = _
  rw [Adjoint.xPar_of_isRoot hγ, h]
  rfl

theorem baseChangeGL_f4Par (ι : K →+* M) (γ : Fin (Tag.rank .F4) → ℤ) (c : K) :
    baseChangeGL ι ((Adjoint.f4Par K γ c : adjointGroup .F4 K) : ModGL .F4 K) =
      ((Adjoint.f4Par M γ (ι c) : adjointGroup .F4 M) : ModGL .F4 M) := by
  by_cases hγ : IsRoot .F4 γ
  · rw [coe_f4Par_eq_pinnedX hγ, coe_f4Par_eq_pinnedX hγ, baseChangeGL_pinnedX, map_mul,
      map_intCast]
  · change baseChangeGL ι ((Adjoint.xPar (Chevalley.rootOperatorFamily .F4) γ c :
        adjointGroup .F4 K) : ModGL .F4 K) =
      ((Adjoint.xPar (Chevalley.rootOperatorFamily .F4) γ (ι c) : adjointGroup .F4 M) :
        ModGL .F4 M)
    rw [Adjoint.xPar_of_not_isRoot hγ, Adjoint.xPar_of_not_isRoot hγ]
    simp

end RootElements

section Levi


variable {K M : Type} [Field K] [Field M]

theorem map_rootSpan_baseChangeGL_le {τ : Tag} (ι : K →+* M) (S : Set (Fin τ.rank → ℤ)) :
    (rootSpan τ K S).map (baseChangeGL ι) ≤ rootSpan τ M S := by
  rw [rootSpan, Subgroup.map_iSup]
  refine iSup_le fun α => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hα => ?_
  rw [rootSubgroup, MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  rw [baseChangeGL_pinnedX]
  exact le_iSup₂ (f := fun α (_ : α ∈ S) => rootSubgroup τ M α) α hα (subset_closure ⟨ι c, rfl⟩)

theorem baseChangeGL_mem_rootSpan_c3LeviRoots (ι : K →+* M) (g : C3Levi K) :
    baseChangeGL ι ((g : adjointGroup .F4 K) : ModGL .F4 K) ∈ rootSpan .F4 M c3LeviRoots :=
  map_rootSpan_baseChangeGL_le ι c3LeviRoots ⟨_, mem_C3Levi_iff.1 g.2, rfl⟩

@[expose] noncomputable def c3LeviBaseChange (ι : K →+* M) : ↥(C3Levi K) →* ↥(C3Levi M) :=
  (((baseChangeGL ι).comp ((adjointGroup .F4 K).subtype.comp (C3Levi K).subtype)).codRestrict
      (adjointGroup .F4 M) fun g => iSup₂_le (fun α _ => rootSubgroup_le_adjointGroup α)
        (baseChangeGL_mem_rootSpan_c3LeviRoots ι g)).codRestrict
    (C3Levi M) fun g => mem_C3Levi_iff.2 (baseChangeGL_mem_rootSpan_c3LeviRoots ι g)

theorem coe_c3LeviBaseChange (ι : K →+* M) (g : C3Levi K) :
    (((c3LeviBaseChange ι g : C3Levi M) : adjointGroup .F4 M) : ModGL .F4 M) =
      baseChangeGL ι ((g : adjointGroup .F4 K) : ModGL .F4 K) :=
  rfl

theorem c3LeviBaseChange_injective (ι : K →+* M) : Function.Injective (c3LeviBaseChange ι) :=
  fun _ _ hgh => Subtype.ext (Subtype.ext (baseChangeGL_injective ι
    (congrArg (fun x : C3Levi M => ((x : adjointGroup .F4 M) : ModGL .F4 M)) hgh)))

theorem baseChangeGL_baseChangeGL {τ : Tag} {N : Type} [Field N] (ι : K →+* M) (κ : M →+* N)
    (g : ModGL τ K) : baseChangeGL κ (baseChangeGL ι g) = baseChangeGL (κ.comp ι) g := by
  refine Units.ext ?_
  rw [Chevalley.coe_baseChangeGL, Chevalley.coe_baseChangeGL, Chevalley.coe_baseChangeGL]
  have h : Adjoint.BaseChange (κ.comp ι) (g : Module.End K (RootModule τ K))
      (Chevalley.baseChangeEnd κ (Chevalley.baseChangeEnd ι (g : Module.End K (RootModule τ K)))) :=
    fun b => by
      rw [← Chevalley.baseChange_baseChangeEnd κ _ b, ← Chevalley.baseChange_baseChangeEnd ι _ b]
      ext a
      simp
  exact h.unique (Chevalley.baseChange_baseChangeEnd _ _)

theorem c3LeviBaseChange_comp {N : Type} [Field N] (ι : K →+* M) (κ : M →+* N) (g : C3Levi K) :
    c3LeviBaseChange κ (c3LeviBaseChange ι g) = c3LeviBaseChange (κ.comp ι) g := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_c3LeviBaseChange, coe_c3LeviBaseChange, coe_c3LeviBaseChange, baseChangeGL_baseChangeGL]

end Levi

section Naturality


variable {K M : Type} [Field K] [Finite K] [CharP K 2] [Field M] [Finite M] [CharP M 2]

theorem c3LeviBaseChange_c3LeviEquiv (ι : K →+* M) (g : StatedSp 3 K) :
    c3LeviBaseChange ι (c3LeviEquiv K g) = c3LeviEquiv M (statedSpMap ι 3 g) := by
  have hle : ⨆ v ∈ roots (isFiniteType_cartanC 3) ∅, Symplectic.rootGroup 3 K v ≤
      MonoidHom.eqLocus ((c3LeviBaseChange ι).comp (c3LeviEquiv K).toMonoidHom)
        ((c3LeviEquiv M).toMonoidHom.comp (statedSpMap ι 3)) := by
    refine iSup₂_le fun v hv x hx => ?_
    obtain ⟨c, rfl⟩ := ((Sp.isParametrization (n := 3) (F := K) v hv).1 x).1 hx
    refine Subtype.ext (Subtype.ext ?_)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [coe_c3LeviBaseChange, c3LeviEquiv_x, baseChangeGL_f4Par, statedSpMap_x, c3LeviEquiv_x]
  rw [(Symplectic.isCTGroupDatum 3 K).iSup_eq_top] at hle
  exact hle (mem_top g)

theorem map_c3LeviBaseChange_eq (ι : K →+* M) :
    (⊤ : Subgroup (C3Levi K)).map (c3LeviBaseChange ι) =
      ((statedSpMap ι 3).range).map (c3LeviEquiv M).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨x, -, rfl⟩
    obtain ⟨g, rfl⟩ := (c3LeviEquiv K).surjective x
    exact ⟨statedSpMap ι 3 g, ⟨g, rfl⟩, (c3LeviBaseChange_c3LeviEquiv ι g).symm⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨c3LeviEquiv K g, mem_top _, c3LeviBaseChange_c3LeviEquiv ι g⟩

theorem map_c3LeviBaseChange_eq_eqLocus {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (ι : K₀ →+* K) (σ : K →+* K) (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) :
    (⊤ : Subgroup (C3Levi K₀)).map (c3LeviBaseChange ι) =
      MonoidHom.eqLocus (c3LeviBaseChange σ) (MonoidHom.id _) := by
  rw [map_c3LeviBaseChange_eq, range_statedSpMap_eq_eqLocus ι σ hfix]
  ext y
  obtain ⟨g, rfl⟩ := (c3LeviEquiv K).surjective y
  constructor
  · rintro ⟨h, hh, he⟩
    have hgh : h = g := (c3LeviEquiv K).injective he
    subst hgh
    change c3LeviBaseChange σ (c3LeviEquiv K h) = c3LeviEquiv K h
    rw [c3LeviBaseChange_c3LeviEquiv]
    exact congrArg (c3LeviEquiv K) hh
  · intro hg
    change c3LeviBaseChange σ (c3LeviEquiv K g) = c3LeviEquiv K g at hg
    refine ⟨g, ?_, rfl⟩
    change statedSpMap σ 3 g = g
    apply (c3LeviEquiv K).injective
    rw [← c3LeviBaseChange_c3LeviEquiv, hg]

end Naturality

end CFSG.SeitzReduction.F4Pilot
