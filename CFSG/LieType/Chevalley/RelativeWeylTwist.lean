module

public import CFSG.LieType.Chevalley.RelativeWeyl
public import CFSG.LieType.Chevalley.TwistMap
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

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley RootSpace
open scoped RealInnerProductSpace

theorem wordProd_smul {τ : Tag} (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd ω • v = ω.foldr (reflect τ) v := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul]
    rfl

variable (t : TwistTag)

theorem formMatrix_twist (i j : Fin t.tag.rank) :
    (1 : ℝ) * 1 * formMatrix t.tag (t.perm i) (t.perm j) = formMatrix t.tag i j := by
  obtain ⟨κ, -, hκ⟩ := exists_formMatrix_eq t.tag
  have hD : ∀ i : Fin t.tag.rank, t.tag.symmetrizer i i = 1 := by
    cases t <;> decide
  rw [one_mul, one_mul, hκ, hκ, t.cartan_perm, hD, hD]

@[expose] noncomputable def twistIsometry : RootSpace t.tag ≃ₗᵢ[ℝ] RootSpace t.tag :=
  graphIsometry t.perm (fun _ => 1) (fun _ => one_ne_zero) (formMatrix_twist t)

theorem twistIsometry_single (i : Fin t.tag.rank) :
    twistIsometry t (ofLattice (Pi.single i 1)) =
      (fun _ => (1 : ℝ)) i • ofLattice (Pi.single (t.perm i) 1) :=
  graphIsometry_single _ _ i

theorem twistIsometry_ofLattice (v : Fin t.tag.rank → ℤ) :
    twistIsometry t (ofLattice v) = ofLattice (permLattice t.perm v) := by
  ext l
  change 1 * (v (t.perm.symm l) : ℝ) = ((permLattice t.perm v) l : ℝ)
  simp [permLattice]

theorem twistIsometry_weylAct (w : WeylGroup t.tag) (x : RootSpace t.tag) :
    twistIsometry t (weylAct t.tag w x) =
      weylAct t.tag (weylTwist t w) (twistIsometry t x) := by
  have h : (twistIsometry t).toLinearEquiv.toLinearMap ∘ₗ
      (weylAct t.tag w).toLinearEquiv.toLinearMap =
      (weylAct t.tag (weylTwist t w)).toLinearEquiv.toLinearMap ∘ₗ
        (twistIsometry t).toLinearEquiv.toLinearMap := by
    refine (basis t.tag).ext fun k => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, basis_apply]
    rw [weylAct_ofLattice, twistIsometry_ofLattice, twistIsometry_ofLattice, weylAct_ofLattice,
      weylTwist_smul_permLattice]
  exact LinearMap.congr_fun h x

@[expose] noncomputable def relWeylTwist : Subgroup (WeylGroup t.tag) :=
  MonoidHom.eqLocus (weylTwist t).toMonoidHom (MonoidHom.id _)

theorem mem_relWeylTwist {w : WeylGroup t.tag} : w ∈ relWeylTwist t ↔ weylTwist t w = w :=
  Iff.rfl

theorem weylAct_mem_fixedSpace_twist {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    {x : RootSpace t.tag} (hx : x ∈ fixedSpace (twistIsometry t)) :
    weylAct t.tag w x ∈ fixedSpace (twistIsometry t) := by
  rw [mem_fixedSpace, twistIsometry_weylAct, (mem_relWeylTwist t).1 hw, mem_fixedSpace.1 hx]

theorem heightVector_mem_fixedSpace_twist :
    heightVector t.tag ∈ fixedSpace (twistIsometry t) := by
  rw [mem_fixedSpace, ← sub_eq_zero]
  refine eq_zero_of_inner_single_eq_zero fun j => ?_
  rw [inner_sub_right, inner_single_map (c := fun _ => (1 : ℝ)) (fun _ => one_pos)
    (twistIsometry_single t)]
  simp [inner_ofLattice_heightVector, height_single]

@[expose] def twistOrbitWord : (t : TwistTag) → Fin t.tag.rank → List (Fin t.tag.rank)
  | .E6 => (![[0, 5], [1], [2, 4], [3], [2, 4], [0, 5]] : Fin 6 → List (Fin 6))
  | .D4 => (![[0, 1, 3], [0, 1, 3], [2], [0, 1, 3]] : Fin 4 → List (Fin 4))

theorem twistOrbitWord_mem (i : Fin t.tag.rank) :
    (coxeterSystem t.tag).wordProd (twistOrbitWord t i) ∈ relWeylTwist t := by
  rw [mem_relWeylTwist, weylTwist_wordProd]
  refine ext_single fun k => ?_
  rw [wordProd_smul, wordProd_smul]
  revert i k
  cases t <;> decide +kernel

theorem exists_improve_twist :
    ∀ y ∈ fixedSpace (twistIsometry t), y ∉ dominantCone t.tag →
      ∃ w ∈ relWeylTwist t, ⟪y, heightVector t.tag⟫ <
        ⟪weylAct t.tag w y, heightVector t.tag⟫ :=
  exists_improve_of_words (c := fun _ => (1 : ℝ)) (fun _ => one_pos) (twistIsometry_single t)
    (relWeylTwist t) heightVector_mem_openDominantCone (twistOrbitWord t) (twistOrbitWord_mem t)
    (by cases t <;> decide +kernel) (by cases t <;> decide +kernel)
    (by cases t <;> decide +kernel)

theorem relWeylTwist_cover {x : RootSpace t.tag} (hx : x ∈ fixedSpace (twistIsometry t)) :
    ∃ w ∈ relWeylTwist t, ∃ y ∈ fixedSpace (twistIsometry t), y ∈ dominantCone t.tag ∧
      x = weylAct t.tag w y :=
  exists_mem_dominantCone_of_improve (relWeylTwist t)
    (fun _ hw _ hx => weylAct_mem_fixedSpace_twist t hw hx) _ (exists_improve_twist t) hx

theorem relWeylTwist_fixfree {v : RootSpace t.tag} (hv : v ∈ fixedSpace (twistIsometry t))
    (hfix : ∀ w ∈ relWeylTwist t, weylAct t.tag w v = v) : v = 0 :=
  eq_zero_of_improve (relWeylTwist t) _ (exists_improve_twist t) hv hfix

end CFSG.LieType.Chevalley
