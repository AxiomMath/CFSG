module

public import CFSG.GF2Type.SmithTypeE.DMod.PlaneAct
public import CFSG.LargeExtraspecial.SMod20Rho

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6
open CFSG.LargeExtraspecial.SMod20 (exists_linear_of_gram)

attribute [local irreducible] tvCols tvLin

section Rho

theorem ext_wtV {L L' : V →ₗ[ZMod 2] V}
    (h : ∀ i : Fin 75735, L (wtV i.val) = L' (wtV i.val)) : L = L' :=
  LinearMap.ext_on_range span_wtV h

theorem span_wtV_smul (g : TD6) :
    Submodule.span (ZMod 2) (Set.range fun i : Fin 75735 => wtV (g • i).val) = ⊤ := by
  have : (Set.range fun i : Fin 75735 => wtV (g • i).val) =
      Set.range fun i : Fin 75735 => wtV i.val := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨g • i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨g⁻¹ • i, by show wtV (g • g⁻¹ • i).val = wtV i.val; rw [smul_inv_smul]⟩
  rw [this, span_wtV]

theorem fModel_wtV_smul (g : TD6) (i j : Fin 75735) :
    fModel (wtV (g • i).val) (wtV (g • j).val) = fModel (wtV i.val) (wtV j.val) := by
  rw [fModel_wtV (g • i).2 (g • j).2, fModel_wtV i.2 j.2]
  by_cases h : Opp i.val j.val
  · simp only [h, (opp_smul g i j).mpr h, ↓reduceIte]
  · simp only [h, mt (opp_smul g i j).mp h, ↓reduceIte]

theorem exists_rhoLin (g : TD6) :
    ∃ L : V →ₗ[ZMod 2] V, ∀ i : Fin 75735, L (wtV i.val) = wtV (g • i).val :=
  exists_linear_of_gram (K := ZMod 2) (W := V) (W' := V) (ι := Fin 75735) fModel fModel span_wtV
    (span_wtV_smul g) (fun _ hv => fModel_nondegenerate hv) (fun i j => fModel_wtV_smul g i j)

@[expose] noncomputable def rhoLin (g : TD6) : V →ₗ[ZMod 2] V :=
  Classical.choose (exists_rhoLin g)

theorem rhoLin_wtV (g : TD6) (i : Fin 75735) : rhoLin g (wtV i.val) = wtV (g • i).val :=
  Classical.choose_spec (exists_rhoLin g) i

theorem rhoLin_mul (g h : TD6) : rhoLin (g * h) = rhoLin g ∘ₗ rhoLin h :=
  ext_wtV fun i => by rw [LinearMap.comp_apply, rhoLin_wtV, rhoLin_wtV, rhoLin_wtV, mul_smul]

theorem rhoLin_one : rhoLin 1 = LinearMap.id :=
  ext_wtV fun i => by rw [rhoLin_wtV, one_smul, LinearMap.id_apply]

@[expose] noncomputable def rhoMod : TD6 →* (V ≃ₗ[ZMod 2] V) where
  toFun g := LinearEquiv.ofLinearMap (rhoLin g) (rhoLin g⁻¹)
    (by rw [← rhoLin_mul, mul_inv_cancel, rhoLin_one])
    (by rw [← rhoLin_mul, inv_mul_cancel, rhoLin_one])
  map_one' := LinearEquiv.ext fun v => by
    show rhoLin 1 v = v
    rw [rhoLin_one, LinearMap.id_apply]
  map_mul' g h := LinearEquiv.ext fun v => by
    show rhoLin (g * h) v = rhoLin g (rhoLin h v)
    rw [rhoLin_mul, LinearMap.comp_apply]

theorem rhoMod_wtV (g : TD6) (i : Fin 75735) : rhoMod g (wtV i.val) = wtV (g • i).val :=
  rhoLin_wtV g i

theorem rhoMod_tvP (k : Fin 365211) : rhoMod ⟨tvP k, tvP_mem k⟩ = tvEquiv k.val := by
  apply LinearEquiv.toLinearMap_injective
  refine ext_wtV fun i => ?_
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, rhoMod_wtV, tvP_smul]
  exact (tvEquiv_wtV k.2 i.2).2.symm

theorem rhoMod_conj_tvEquiv (g : TD6) (k : Fin 365211) :
    rhoMod g * tvEquiv k.val * (rhoMod g)⁻¹ =
      tvEquiv ((g : Equiv.Perm (Fin 365211)) k).val := by
  rw [← rhoMod_tvP, ← rhoMod_tvP, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg rhoMod (Subtype.ext (mul_tvP_mul_inv g.2 k))

theorem fModel_rhoMod (g : TD6) (v w : V) : fModel (rhoMod g v) (rhoMod g w) = fModel v w := by
  have key : fModel.compl₁₂ (rhoMod g : V →ₗ[ZMod 2] V) (rhoMod g : V →ₗ[ZMod 2] V) = fModel := by
    refine LinearMap.ext_on_range span_wtV fun i => ?_
    refine LinearMap.ext_on_range span_wtV fun j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, rhoMod_wtV]
    exact fModel_wtV_smul g i j
  have := congrArg (fun B : LinearMap.BilinForm (ZMod 2) V => B v w) key
  simpa using this

theorem rhoMod_injective : Function.Injective (rhoMod : TD6 →* (V ≃ₗ[ZMod 2] V)) := by
  haveI := isSimpleGroup_TD6
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal rhoMod.ker with h | h
  · exact h
  · exfalso
    have hg : omegaTD6 siegel0 ∈ rhoMod.ker := by
      rw [h]
      trivial
    rw [MonoidHom.mem_ker] at hg
    have h0 : (0 : ℕ) < 75735 := by norm_num
    have hfix : (omegaTD6 siegel0) • (⟨0, h0⟩ : Fin 75735) = ⟨0, h0⟩ := by
      apply Fin.ext
      apply wtV_injective ((omegaTD6 siegel0 • (⟨0, h0⟩ : Fin 75735)).2) h0
      rw [← rhoMod_wtV, hg]
      rfl
    have hmap := map_planeSub_smul (omegaTD6 siegel0) ⟨0, h0⟩
    rw [hfix, MulEquiv.symm_apply_apply] at hmap
    have hq1 : qf 1 = false := by decide
    have hq2 : qf 2 = false := by decide
    have hb12 : bf 1 2 = false := by decide
    have hmem : dec12 64 ∈ planeSub 0 := by
      show dec12 64 ∈ planeSpan pbArr[0]!
      rw [pbArr_zero, mem_planeSpan_fBasis_iff, fst_dec12_eq_zero_iff]
      decide
    have hmem' : siegelEquiv (dec12 1) (dec12 2) (dec12 64) ∈ planeSub 0 := by
      rw [← hmap]
      exact Submodule.mem_map_of_mem hmem
    rw [siegelEquiv_dec12 hq1 hq2 hb12, show sgl 1 2 64 = 66 by decide] at hmem'
    have hF : dec12 66 ∈ planeSpan fBasis := by
      show dec12 66 ∈ planeSpan fBasis
      have : planeSub 0 = planeSpan fBasis := by
        show planeSpan pbArr[0]! = _
        rw [pbArr_zero]
      rwa [this] at hmem'
    rw [mem_planeSpan_fBasis_iff, fst_dec12_eq_zero_iff] at hF
    exact absurd (hF 1 (by norm_num)) (by decide)

end Rho

end CFSG.GF2Type.SmithTypeE.DMod
