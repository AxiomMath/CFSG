module

public import CFSG.GF2Type.SmithTypeE.DMod.TD6
public import CFSG.GF2Type.SmithTypeE.DMod.Rho

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6 CFSG.RankThree.OrthogonalInvolutions

attribute [local irreducible] tvCols tvLin

section Planes


theorem planes_inv {σ : V12 ≃ₗ[ZMod 2] V12}
    (h : ∀ i < 75735, ∃ j < 75735, Submodule.map σ.toLinearMap (planeSub i) = planeSub j) :
    ∀ i < 75735, ∃ j < 75735, Submodule.map σ⁻¹.toLinearMap (planeSub i) = planeSub j := by
  choose f hf hm using h
  let F : Fin 75735 → Fin 75735 := fun i => ⟨f i.val i.2, hf i.val i.2⟩
  have hF : Function.Injective F := by
    intro a b hab
    have hab' : f a.val a.2 = f b.val b.2 := congrArg Fin.val hab
    have h1 : Submodule.map σ.toLinearMap (planeSub a.val) =
        Submodule.map σ.toLinearMap (planeSub b.val) := by
      rw [hm a.val a.2, hm b.val b.2, hab']
    exact Fin.ext (planeSub_injective a.2 b.2 (Submodule.map_injective_of_injective σ.injective h1))
  intro i hi
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp hF) ⟨i, hi⟩
  have hfa : f a.val a.2 = i := congrArg Fin.val ha
  refine ⟨a.val, a.2, ?_⟩
  have h1 := hm a.val a.2
  rw [hfa] at h1
  rw [← h1, ← Submodule.map_comp]
  have : σ⁻¹.toLinearMap ∘ₗ σ.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x => LinearEquiv.symm_apply_apply σ x
  rw [this, Submodule.map_id]

theorem exists_map_planeSub {σ : V12 ≃ₗ[ZMod 2] V12}
    (hσ : σ ∈ Subgroup.closure (Set.range fun k : Fin 365211 => siegelK k.val)) :
    ∀ i < 75735, ∃ j < 75735, Submodule.map σ.toLinearMap (planeSub i) = planeSub j := by
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    intro i hi
    exact ⟨planeImg k.val i, (tvEquiv_wtV k.2 hi).1, map_planeSub_siegelK k.2 hi⟩
  | one =>
    intro i hi
    refine ⟨i, hi, ?_⟩
    have : (1 : V12 ≃ₗ[ZMod 2] V12).toLinearMap = LinearMap.id := rfl
    rw [this, Submodule.map_id]
  | mul x y _ _ hx hy =>
    intro i hi
    obtain ⟨j, hj, hm⟩ := hy i hi
    obtain ⟨l, hl, hm'⟩ := hx j hj
    refine ⟨l, hl, ?_⟩
    have h : (x * y).toLinearMap = x.toLinearMap ∘ₗ y.toLinearMap := rfl
    rw [h, Submodule.map_comp, hm, hm']
  | inv x _ hx => exact planes_inv hx

theorem exists_map_planeSub_omega (σ : ↥(CFSG.Open.timmesfeldOmegaPlus 6)) (i : Fin 75735) :
    ∃ j : Fin 75735, Submodule.map σ.1.toLinearMap (planeSub i.val) = planeSub j.val := by
  have hσ : σ.1 ∈ Subgroup.closure (Set.range fun k : Fin 365211 => siegelK k.val) :=
    omega_le_closure_siegelK (by rw [← omegaPlus_eq_omegaGroup]; exact σ.2)
  obtain ⟨j, hj, hm⟩ := exists_map_planeSub hσ i.val i.2
  exact ⟨⟨j, hj⟩, hm⟩

@[expose] noncomputable def planeActOmega (σ : ↥(CFSG.Open.timmesfeldOmegaPlus 6))
    (i : Fin 75735) : Fin 75735 :=
  Classical.choose (exists_map_planeSub_omega σ i)

theorem map_planeSub_planeActOmega (σ : ↥(CFSG.Open.timmesfeldOmegaPlus 6)) (i : Fin 75735) :
    Submodule.map σ.1.toLinearMap (planeSub i.val) = planeSub (planeActOmega σ i).val :=
  Classical.choose_spec (exists_map_planeSub_omega σ i)

theorem planeActOmega_eq_iff (σ : ↥(CFSG.Open.timmesfeldOmegaPlus 6)) (i j : Fin 75735) :
    planeActOmega σ i = j ↔ Submodule.map σ.1.toLinearMap (planeSub i.val) = planeSub j.val := by
  rw [map_planeSub_planeActOmega]
  exact ⟨fun h => by rw [h], fun h => Fin.ext (planeSub_injective (planeActOmega σ i).2 j.2 h)⟩

noncomputable instance planeAction : MulAction TD6 (Fin 75735) where
  smul g i := planeActOmega (omegaTD6.symm g) i
  one_smul i := by
    show planeActOmega (omegaTD6.symm 1) i = i
    rw [map_one, planeActOmega_eq_iff]
    have : ((1 : ↥(CFSG.Open.timmesfeldOmegaPlus 6)).1).toLinearMap = LinearMap.id := rfl
    rw [this, Submodule.map_id]
  mul_smul g h i := by
    show planeActOmega (omegaTD6.symm (g * h)) i =
      planeActOmega (omegaTD6.symm g) (planeActOmega (omegaTD6.symm h) i)
    rw [map_mul, planeActOmega_eq_iff]
    have e : ((omegaTD6.symm g * omegaTD6.symm h).1).toLinearMap =
        (omegaTD6.symm g).1.toLinearMap ∘ₗ (omegaTD6.symm h).1.toLinearMap := rfl
    rw [e, Submodule.map_comp, map_planeSub_planeActOmega, map_planeSub_planeActOmega]

theorem plane_smul_def (g : TD6) (i : Fin 75735) : g • i = planeActOmega (omegaTD6.symm g) i := rfl

theorem map_planeSub_smul (g : TD6) (i : Fin 75735) :
    Submodule.map (omegaTD6.symm g).1.toLinearMap (planeSub i.val) = planeSub (g • i).val :=
  map_planeSub_planeActOmega _ _

theorem tvP_smul (k : Fin 365211) (i : Fin 75735) :
    (⟨tvP k, tvP_mem k⟩ : TD6) • i = ⟨planeImg k.val i.val, (tvEquiv_wtV k.2 i.2).1⟩ := by
  have hsym : omegaTD6.symm ⟨tvP k, tvP_mem k⟩ =
      ⟨siegelK k.val, siegelK_mem_omega k.2⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (omegaTD6_siegelK k).symm
  rw [plane_smul_def, hsym, planeActOmega_eq_iff]
  exact map_planeSub_siegelK k.2 i.2

theorem opp_smul (g : TD6) (i j : Fin 75735) : Opp (g • i).val (g • j).val ↔ Opp i.val j.val := by
  unfold Opp
  rw [← map_planeSub_smul, ← map_planeSub_smul]
  exact disjoint_map_iff _ _ _

end Planes

end CFSG.GF2Type.SmithTypeE.DMod
