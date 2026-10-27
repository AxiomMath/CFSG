module

public import CFSG.LieType.Chevalley.E7Three.Automizer
public import CFSG.LieType.Chevalley.E7Three.FourCube
public import CFSG.Mathlib.GroupTheory.MulAutProd

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.FourAutomizer

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.RankThree.PartOne.KA5L
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley.E7Three.Weyl CFSG.LieType.Chevalley.E7Three.Cube
  CFSG.LieType.Chevalley.E7Three.Multiplicity CFSG.LieType.Chevalley.E7Three.FourCube
  CFSG.LieType.Chevalley.E7Three.Automizer CFSG.LieType.Chevalley.E7Three.CoordinateActions
  CFSG.LieType.Chevalley.E7Three.TriangularActions

variable {K : Type} [Field K] [CharP K 2]

@[expose] def fourCubeEquiv (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    Four ≃* (fourCubeHom ζ hζ.pow_eq_one).range :=
  MonoidHom.ofInjective (fourCubeHom_injective ζ hζ)

@[expose] def extendToFourCube (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    MulAut D →* MulAut (fourCubeHom ζ hζ.pow_eq_one).range :=
  (MulAut.congr (fourCubeEquiv ζ hζ)).toMonoidHom.comp
    (MulAut.prodLeftHom (G := D) (H := Multiplicative (ZMod 3)))

theorem extendToFourCube_injective (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    Function.Injective (extendToFourCube ζ hζ) :=
  (MulAut.congr (fourCubeEquiv ζ hζ)).injective.comp MulAut.prodLeftHom_injective

theorem extend_mem_of_conj_eq (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) (φ : MulAut D)
    (n : adjointGroup .E7 K)
    (hn : n ∈ Subgroup.normalizer ((cubeHom ζ hζ.pow_eq_one).range : Set (adjointGroup .E7 K)))
    (hconj : MulAut.congr (cubeEquiv ζ hζ) φ = ggConjAut (cubeHom ζ hζ.pow_eq_one).range hn)
    (hm : n * multiplicityWord ζ * n⁻¹ = multiplicityWord ζ) :
    extendToFourCube ζ hζ φ ∈ ggAutomizer (⊤ : Subgroup (adjointGroup .E7 K))
      (fourCubeHom ζ hζ.pow_eq_one).range := by
  classical
  let E := (fourCubeHom ζ hζ.pow_eq_one).range
  let Q : adjointGroup .E7 K →* adjointGroup .E7 K := (MulAut.conj n).toMonoidHom
  have hc (d : D) : Q (cubeHom ζ hζ.pow_eq_one d) = cubeHom ζ hζ.pow_eq_one (φ d) := by
    have he := congrArg (fun a : MulAut (cubeHom ζ hζ.pow_eq_one).range =>
      ((a (cubeEquiv ζ hζ d) : (cubeHom ζ hζ.pow_eq_one).range) : adjointGroup .E7 K)) hconj
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      ggConjAut_apply] at he
    exact he.symm
  have hv : Q (multiplicityWord ζ) = multiplicityWord ζ := hm
  have hall (p : Four) : Q (fourCubeHom ζ hζ.pow_eq_one p) =
      fourCubeHom ζ hζ.pow_eq_one (MulAut.prodLeftHom φ p) := by
    simp only [fourCubeHom_apply, MulAut.prodLeftHom_apply, Q.map_mul, Q.map_pow, hc, hv]
  have hclose : ∀ y : adjointGroup .E7 K, y ∈ E → n * y * n⁻¹ ∈ E := by
    intro y hy
    obtain ⟨p, rfl⟩ := hy
    change Q (fourCubeHom ζ hζ.pow_eq_one p) ∈ E
    rw [hall]
    exact ⟨_, rfl⟩
  letI : Fintype E := MonoidHom.fintypeRange (fourCubeHom ζ hζ.pow_eq_one)
  have hn4 : n ∈ Subgroup.normalizer (E : Set (adjointGroup .E7 K)) :=
    Subgroup.mem_normalizer_fintype hclose
  apply mem_ggAutomizer_iff.mpr
  refine ⟨n, Subgroup.mem_top _, hn4, ?_⟩
  intro b
  obtain ⟨p, rfl⟩ := (fourCubeEquiv ζ hζ).surjective b
  simp only [extendToFourCube, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  change fourCubeHom ζ hζ.pow_eq_one (MulAut.prodLeftHom φ p) =
    n * fourCubeHom ζ hζ.pow_eq_one p * n⁻¹
  exact (hall p).symm

theorem a5CycleElement_conj_multiplicityWord (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    a5CycleElement * multiplicityWord ζ * a5CycleElement⁻¹ = multiplicityWord ζ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [multiplicityWord_val ζ hζ]
  change canonicalRep (coxeterSystem .E7) K a5Cycle * rootDiagUnit .E7 (cubeChar ζ multiplicityExp) *
    (canonicalRep (coxeterSystem .E7) K a5Cycle)⁻¹ = rootDiagUnit .E7 (cubeChar ζ multiplicityExp)
  rw [CFSG.LieType.Chevalley.canonicalRep_conj_rootDiagUnit, weylTuple_a5Cycle_multiplicity ζ hζ]

theorem moveElement_conj_multiplicityWord (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    moveElement * multiplicityWord ζ * moveElement⁻¹ = multiplicityWord ζ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [multiplicityWord_val ζ hζ]
  change canonicalRep (coxeterSystem .E7) K move * rootDiagUnit .E7 (cubeChar ζ multiplicityExp) *
    (canonicalRep (coxeterSystem .E7) K move)⁻¹ = rootDiagUnit .E7 (cubeChar ζ multiplicityExp)
  exact move_conj_multiplicity ζ hζ

theorem u_mem_fourCube_automizer (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    extendToFourCube ζ hζ u ∈ ggAutomizer (⊤ : Subgroup (adjointGroup .E7 K))
      (fourCubeHom ζ hζ.pow_eq_one).range := by
  exact extend_mem_of_conj_eq ζ hζ u (a5CycleElement (K := K))
    (a5CycleElement_mem_normalizer ζ hζ.pow_eq_one) (u_eq_conj_a5Cycle ζ hζ)
    (a5CycleElement_conj_multiplicityWord ζ hζ.pow_eq_one)

theorem v_mem_fourCube_automizer (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    extendToFourCube ζ hζ v ∈ ggAutomizer (⊤ : Subgroup (adjointGroup .E7 K))
      (fourCubeHom ζ hζ.pow_eq_one).range := by
  obtain ⟨n, hn, heq, -, hm⟩ := exists_fourier_eq_conj ζ hζ
  exact extend_mem_of_conj_eq ζ hζ v n hn heq hm

theorem w_mem_fourCube_automizer (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    extendToFourCube ζ hζ w ∈ ggAutomizer (⊤ : Subgroup (adjointGroup .E7 K))
      (fourCubeHom ζ hζ.pow_eq_one).range := by
  exact extend_mem_of_conj_eq ζ hζ w (moveElement (K := K))
    (moveElement_mem_normalizer ζ hζ.pow_eq_one) (w_eq_conj_move ζ hζ)
    (moveElement_conj_multiplicityWord ζ hζ.pow_eq_one)

theorem threeFiveOne_dvd_fourCube_automizer (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    351 ∣ Nat.card (ggAutomizer (⊤ : Subgroup (adjointGroup .E7 K))
      (fourCubeHom ζ hζ.pow_eq_one).range) := by
  classical
  let E := (fourCubeHom ζ hζ.pow_eq_one).range
  letI : Fintype E := MonoidHom.fintypeRange (fourCubeHom ζ hζ.pow_eq_one)
  let H := ggAutomizer (⊤ : Subgroup (adjointGroup .E7 K)) E
  let ψ := extendToFourCube ζ hζ
  let S := H.comap ψ
  have hu : u ∈ S := u_mem_fourCube_automizer ζ hζ
  have hv : v ∈ S := v_mem_fourCube_automizer ζ hζ
  have hw : w ∈ S := w_mem_fourCube_automizer ζ hζ
  have hd : 351 ∣ Nat.card S := threeFiveOne_dvd_card_of_u_v_w hu hv hw
  have hcard : Nat.card (S.map ψ) = Nat.card S :=
    Subgroup.card_map_of_injective (extendToFourCube_injective ζ hζ)
  have hle : S.map ψ ≤ H := Subgroup.map_comap_le _ _
  have hd' : 351 ∣ Nat.card (S.map ψ) := by rwa [hcard]
  exact hd'.trans (Subgroup.card_dvd_of_le hle)

theorem threeFiveOne_dvd_fourCube_automizer_ambient (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    351 ∣ Nat.card (ggAutomizer (adjointGroup .E7 K)
      ((fourCubeHom ζ hζ.pow_eq_one).range.map (adjointGroup .E7 K).subtype)) := by
  let E := (fourCubeHom ζ hζ.pow_eq_one).range
  let f := (adjointGroup .E7 K).subtype
  have hm := F4AutWeyl.ggAutomizer_map_eq (f := f) Subtype.val_injective
    (⊤ : Subgroup (adjointGroup .E7 K)) E (rfl : E.map f = E.map f)
  rw [Subgroup.map_top, Subgroup.range_subtype] at hm
  have hcard : Nat.card (ggAutomizer (adjointGroup .E7 K) (E.map f)) =
      Nat.card (ggAutomizer (⊤ : Subgroup (adjointGroup .E7 K)) E) := by
    rw [hm]
    exact Subgroup.card_map_of_injective
      (MulAut.congr ((E.equivMapOfInjective f Subtype.val_injective).trans
        (MulEquiv.subgroupCongr rfl))).injective
  change 351 ∣ Nat.card (ggAutomizer (adjointGroup .E7 K) (E.map f))
  rw [hcard]
  exact threeFiveOne_dvd_fourCube_automizer ζ hζ

end CFSG.LieType.Chevalley.E7Three.FourAutomizer
