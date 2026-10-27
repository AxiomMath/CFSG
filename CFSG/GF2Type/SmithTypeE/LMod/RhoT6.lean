module

public import CFSG.GF2Type.SmithTypeE.LMod.T6
public import CFSG.GF2Type.SmithTypeE.LMod.Rho

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6
open CFSG.LargeExtraspecial.SMod20 (V decode exists_linear_of_gram)

section Rho

theorem ext_wtV {L L' : V →ₗ[ZMod 2] V}
    (h : ∀ i : Fin 1395, L (wtV i.val) = L' (wtV i.val)) : L = L' :=
  LinearMap.ext_on_range span_wtV h

theorem span_wtV_smul (g : T6) :
    Submodule.span (ZMod 2) (Set.range fun i : Fin 1395 => wtV (g • i).val) = ⊤ := by
  have : (Set.range fun i : Fin 1395 => wtV (g • i).val) =
      Set.range fun i : Fin 1395 => wtV i.val := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨g • i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨g⁻¹ • i, by show wtV (g • g⁻¹ • i).val = wtV i.val; rw [smul_inv_smul]⟩
  rw [this, span_wtV]

theorem fModel_wtV_smul (g : T6) (i j : Fin 1395) :
    fModel (wtV (g • i).val) (wtV (g • j).val) = fModel (wtV i.val) (wtV j.val) := by
  rw [fModel_wtV (g • i).2 (g • j).2, fModel_wtV i.2 j.2]
  by_cases h : Opp i.val j.val
  · simp only [h, (opp_smul g i j).mpr h, ↓reduceIte]
  · simp only [h, mt (opp_smul g i j).mp h, ↓reduceIte]

theorem exists_rhoLin (g : T6) :
    ∃ L : V →ₗ[ZMod 2] V, ∀ i : Fin 1395, L (wtV i.val) = wtV (g • i).val :=
  exists_linear_of_gram (K := ZMod 2) (W := V) (W' := V) (ι := Fin 1395) fModel fModel span_wtV
    (span_wtV_smul g) (fun _ hv => fModel_nondegenerate hv) (fun i j => fModel_wtV_smul g i j)

@[expose] noncomputable def rhoLin (g : T6) : V →ₗ[ZMod 2] V :=
  Classical.choose (exists_rhoLin g)

theorem rhoLin_wtV (g : T6) (i : Fin 1395) : rhoLin g (wtV i.val) = wtV (g • i).val :=
  Classical.choose_spec (exists_rhoLin g) i

theorem rhoLin_mul (g h : T6) : rhoLin (g * h) = rhoLin g ∘ₗ rhoLin h :=
  ext_wtV fun i => by rw [LinearMap.comp_apply, rhoLin_wtV, rhoLin_wtV, rhoLin_wtV, mul_smul]

theorem rhoLin_one : rhoLin 1 = LinearMap.id :=
  ext_wtV fun i => by rw [rhoLin_wtV, one_smul, LinearMap.id_apply]

@[expose] noncomputable def rhoMod : T6 →* (V ≃ₗ[ZMod 2] V) where
  toFun g := LinearEquiv.ofLinearMap (rhoLin g) (rhoLin g⁻¹)
    (by rw [← rhoLin_mul, mul_inv_cancel, rhoLin_one])
    (by rw [← rhoLin_mul, inv_mul_cancel, rhoLin_one])
  map_one' := LinearEquiv.ext fun v => by
    show rhoLin 1 v = v
    rw [rhoLin_one, LinearMap.id_apply]
  map_mul' g h := LinearEquiv.ext fun v => by
    show rhoLin (g * h) v = rhoLin g (rhoLin h v)
    rw [rhoLin_mul, LinearMap.comp_apply]

theorem rhoMod_wtV (g : T6) (i : Fin 1395) : rhoMod g (wtV i.val) = wtV (g • i).val :=
  rhoLin_wtV g i

theorem rhoMod_tvP (k : Fin 1953) : rhoMod ⟨tvP k, tvP_mem k⟩ = tvEquiv k.val := by
  apply LinearEquiv.toLinearMap_injective
  refine ext_wtV fun i => ?_
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, rhoMod_wtV, tvP_smul, tvEquiv_wtV k.2 i.2]

theorem rhoMod_conj_tvEquiv (g : T6) (k : Fin 1953) :
    rhoMod g * tvEquiv k.val * (rhoMod g)⁻¹ = tvEquiv ((g : Equiv.Perm (Fin 1953)) k).val := by
  rw [← rhoMod_tvP, ← rhoMod_tvP, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg rhoMod (Subtype.ext (mul_tvP_mul_inv g.2 k))

theorem fModel_rhoMod (g : T6) (v w : V) : fModel (rhoMod g v) (rhoMod g w) = fModel v w := by
  have key : fModel.compl₁₂ (rhoMod g : V →ₗ[ZMod 2] V) (rhoMod g : V →ₗ[ZMod 2] V) = fModel := by
    refine LinearMap.ext_on_range span_wtV fun i => ?_
    refine LinearMap.ext_on_range span_wtV fun j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, rhoMod_wtV]
    exact fModel_wtV_smul g i j
  have := congrArg (fun B : LinearMap.BilinForm (ZMod 2) V => B v w) key
  simpa using this

end Rho

end CFSG.GF2Type.SmithTypeE.LMod
