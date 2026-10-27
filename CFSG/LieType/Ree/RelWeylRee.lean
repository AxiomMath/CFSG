module

public import CFSG.LieType.Chevalley.RelativeWeyl
public import CFSG.LieType.Ree.EndoRoots
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootSpace
open scoped RealInnerProductSpace

section Graph

variable {τ : Tag} {ψ : RootSpace τ ≃ₗᵢ[ℝ] RootSpace τ} {π : Equiv.Perm (Fin τ.rank)}
  {c : Fin τ.rank → ℝ}

theorem map_weylAct_simple_of_single (hc : ∀ i, c i ≠ 0)
    (hψ : ∀ i, ψ (ofLattice (Pi.single i 1)) = c i • ofLattice (Pi.single (π i) 1))
    (i : Fin τ.rank) (x : RootSpace τ) :
    ψ (weylAct τ (simple τ i) x) = weylAct τ (simple τ (π i)) (ψ x) := by
  rw [weylAct_simple_eq, weylAct_simple_eq, map_sub, map_smul, hψ, smul_smul]
  have h1 : ⟪ofLattice (Pi.single i 1), x⟫ = c i * ⟪ofLattice (Pi.single (π i) 1), ψ x⟫ := by
    rw [← LinearIsometryEquiv.inner_map_map ψ, hψ, real_inner_smul_left]
  have h2 : ⟪ofLattice (Pi.single i 1 : Fin τ.rank → ℤ), ofLattice (Pi.single i 1)⟫ =
      c i * c i * ⟪ofLattice (Pi.single (π i) 1 : Fin τ.rank → ℤ),
        ofLattice (Pi.single (π i) 1)⟫ := by
    rw [← LinearIsometryEquiv.inner_map_map ψ, hψ, real_inner_smul_left, real_inner_smul_right,
      mul_assoc]
  have hne : ⟪ofLattice (Pi.single (π i) 1 : Fin τ.rank → ℤ),
      ofLattice (Pi.single (π i) 1)⟫ ≠ 0 :=
    inner_self_ne_zero.2 (ofLattice_single_ne_zero _)
  rw [h1, h2]
  congr 2
  field_simp [hc i]

theorem map_weylAct_of_single (hc : ∀ i, c i ≠ 0)
    (hψ : ∀ i, ψ (ofLattice (Pi.single i 1)) = c i • ofLattice (Pi.single (π i) 1))
    (δ : WeylGroup τ →* WeylGroup τ) (hδ : ∀ i, δ (simple τ i) = simple τ (π i))
    (w : WeylGroup τ) (x : RootSpace τ) :
    ψ (weylAct τ w x) = weylAct τ (δ w) (ψ x) := by
  induction w using (coxeterSystem τ).simple_induction_left generalizing x with
  | one => simp only [map_one, LinearIsometryEquiv.coe_one, id]
  | mul_simple_left w i ih =>
    rw [weylAct_mul_apply, map_weylAct_simple_of_single hc hψ, ih, map_mul, hδ,
      weylAct_mul_apply]

end Graph

namespace ReeTag

variable (t : ReeTag)

@[expose] noncomputable def reeScale (i : Fin t.tag.rank) : ℝ :=
  (t.scale i : ℝ) / Real.sqrt t.prime

theorem reeScale_pos (i : Fin t.tag.rank) : 0 < t.reeScale i := by
  have hs : 0 < t.scale i := by
    unfold scale
    split_ifs
    · exact t.fact_prime.out.pos
    · exact one_pos
  have hp : (0 : ℝ) < t.prime := by exact_mod_cast t.fact_prime.out.pos
  exact div_pos (by exact_mod_cast hs) (Real.sqrt_pos.2 hp)

theorem scale_mul_cartan_perm (i j : Fin t.tag.rank) :
    (t.scale i : ℤ) * t.scale j * t.scale (t.perm i) * t.tag.cartan (t.perm i) (t.perm j) =
      t.prime * t.scale i * t.tag.cartan i j := by
  revert i j
  cases t <;> decide

theorem reeScale_form (i j : Fin t.tag.rank) :
    t.reeScale i * t.reeScale j * formMatrix t.tag (t.perm i) (t.perm j) =
      formMatrix t.tag i j := by
  obtain ⟨κ, -, hκ⟩ := exists_formMatrix_eq t.tag
  have hp : (0 : ℝ) < t.prime := by exact_mod_cast t.fact_prime.out.pos
  have hsq : Real.sqrt t.prime ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have h := congrArg (fun z : ℤ => (z : ℝ)) (t.scale_mul_cartan_perm i j)
  push_cast at h
  rw [hκ, hκ, symmetrizer_apply_self, symmetrizer_apply_self, reeScale, reeScale]
  push_cast
  field_simp
  rw [Real.sq_sqrt hp.le]
  linear_combination κ * h

@[expose] noncomputable def reeIsometry : RootSpace t.tag ≃ₗᵢ[ℝ] RootSpace t.tag :=
  graphIsometry t.perm t.reeScale (fun i => (t.reeScale_pos i).ne') t.reeScale_form

theorem reeIsometry_single (i : Fin t.tag.rank) :
    t.reeIsometry (ofLattice (Pi.single i 1)) =
      t.reeScale i • ofLattice (Pi.single (t.perm i) 1) :=
  graphIsometry_single _ _ i

theorem reeIsometry_weylAct (w : WeylGroup t.tag) (x : RootSpace t.tag) :
    t.reeIsometry (weylAct t.tag w x) = weylAct t.tag (t.weylPerm w) (t.reeIsometry x) :=
  map_weylAct_of_single (fun i => (t.reeScale_pos i).ne') t.reeIsometry_single
    t.weylPerm.toMonoidHom weylPerm_simple w x

theorem perm_symm_apply (i : Fin t.tag.rank) : t.perm.symm i = t.perm i :=
  (Equiv.symm_apply_eq _).2 (perm_perm t i).symm

theorem reeScale_perm_mul (i : Fin t.tag.rank) : t.reeScale (t.perm i) * t.reeScale i = 1 := by
  have h : (t.scale (t.perm i) : ℝ) * t.scale i = t.prime := by
    have : t.scale (t.perm i) * t.scale i = t.prime := by
      revert i
      cases t <;> decide
    exact_mod_cast this
  have hp : (0 : ℝ) < t.prime := by exact_mod_cast t.fact_prime.out.pos
  rw [reeScale, reeScale, div_mul_div_comm, h, Real.mul_self_sqrt hp.le, div_self hp.ne']

theorem reeIsometry_reeIsometry (x : RootSpace t.tag) :
    t.reeIsometry (t.reeIsometry x) = x := by
  ext l
  rw [reeIsometry, graphIsometry_apply, graphIsometry_apply, perm_symm_apply, perm_symm_apply,
    perm_perm, ← mul_assoc, reeScale_perm_mul, one_mul]

theorem reeIsometry_sq : t.reeIsometry ^ 2 = 1 :=
  LinearIsometryEquiv.ext fun x => by
    rw [pow_two, LinearIsometryEquiv.coe_mul, Function.comp_apply, reeIsometry_reeIsometry,
      LinearIsometryEquiv.coe_one, id]

@[expose] noncomputable def relWeylRee : Subgroup (WeylGroup t.tag) :=
  MonoidHom.eqLocus t.weylPerm.toMonoidHom (MonoidHom.id _)

theorem mem_relWeylRee {w : WeylGroup t.tag} : w ∈ t.relWeylRee ↔ t.weylPerm w = w :=
  Iff.rfl

theorem weylAct_mem_fixedSpace_ree {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    {x : RootSpace t.tag} (hx : x ∈ fixedSpace t.reeIsometry) :
    weylAct t.tag w x ∈ fixedSpace t.reeIsometry := by
  rw [mem_fixedSpace, reeIsometry_weylAct, (mem_relWeylRee t).1 hw, mem_fixedSpace.1 hx]

@[expose] noncomputable def reeVector : RootSpace t.tag :=
  sumPowHeight t.reeIsometry 2

theorem reeVector_mem_fixedSpace : t.reeVector ∈ fixedSpace t.reeIsometry :=
  sumPowHeight_mem_fixedSpace t.reeIsometry_sq

theorem reeVector_mem_openDominantCone : t.reeVector ∈ openDominantCone t.tag :=
  sumPowHeight_mem_openDominantCone t.reeScale_pos t.reeIsometry_single (by norm_num)

theorem inner_reeVector_pos (α : Root t.tag) (hα : 0 < height α.1) :
    0 < ⟪ofLattice α.1, t.reeVector⟫ :=
  IsRoot.inner_pos_of_mem_openDominantCone α.2 hα t.reeVector_mem_openDominantCone

@[expose] def reeOrbitWord : (t : ReeTag) → Fin t.tag.rank → List (Fin t.tag.rank)
  | .G2 => (![[0, 1, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1]] : Fin 2 → List (Fin 2))
  | .F4 => (![[0, 3], [1, 2, 1, 2], [1, 2, 1, 2], [0, 3]] : Fin 4 → List (Fin 4))

theorem reeOrbitWord_mem (i : Fin t.tag.rank) :
    (coxeterSystem t.tag).wordProd (reeOrbitWord t i) ∈ t.relWeylRee := by
  rw [mem_relWeylRee, weylPerm_wordProd]
  refine ext_single fun k => ?_
  rw [wordProd_smul, wordProd_smul]
  revert i k
  cases t <;> decide +kernel

theorem exists_improve_ree :
    ∀ y ∈ fixedSpace t.reeIsometry, y ∉ dominantCone t.tag →
      ∃ w ∈ t.relWeylRee, ⟪y, t.reeVector⟫ < ⟪weylAct t.tag w y, t.reeVector⟫ :=
  exists_improve_of_words t.reeScale_pos t.reeIsometry_single t.relWeylRee
    t.reeVector_mem_openDominantCone (reeOrbitWord t) t.reeOrbitWord_mem
    (by cases t <;> decide +kernel) (by cases t <;> decide +kernel)
    (by cases t <;> decide +kernel)

theorem relWeylRee_cover {x : RootSpace t.tag} (hx : x ∈ fixedSpace t.reeIsometry) :
    ∃ w ∈ t.relWeylRee, ∃ y ∈ fixedSpace t.reeIsometry, y ∈ dominantCone t.tag ∧
      x = weylAct t.tag w y :=
  exists_mem_dominantCone_of_improve t.relWeylRee
    (fun _ hw _ hx => t.weylAct_mem_fixedSpace_ree hw hx) _ t.exists_improve_ree hx

theorem relWeylRee_fixfree {v : RootSpace t.tag} (hv : v ∈ fixedSpace t.reeIsometry)
    (hfix : ∀ w ∈ t.relWeylRee, weylAct t.tag w v = v) : v = 0 :=
  eq_zero_of_improve t.relWeylRee _ t.exists_improve_ree hv hfix

end ReeTag

end CFSG.LieType.Ree
