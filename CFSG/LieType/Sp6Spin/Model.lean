module

public import CFSG.LieType.D4Small.SpinSeven
public import CFSG.LieType.D4Small.Om8Datum
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaModel
public import CFSG.RankThree.PartOne.AUTSL.KF1513

public section

namespace CFSG.LieType.Sp6Spin

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.RankThree.PartOne.AUTSL
open CFSG.SeitzReduction.F4Pilot
open CFSG.Open
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply coe_quadPlus toStdD)
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def fixRho (K : Type) [Field K] [Finite K] [CharP K 2] : Subgroup (Om8 K) :=
  MonoidHom.eqLocus (AutOm.plusRefl (K := K) one_le_four).toMonoidHom (MonoidHom.id (Om8 K))

theorem mem_fixRho_iff (g : Om8 K) :
    g ∈ fixRho K ↔ ((g : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
        (AutOm.pvec 0 true + AutOm.pvec 0 false) =
          AutOm.pvec 0 true + AutOm.pvec 0 false := by
  change AutOm.plusRefl (K := K) one_le_four g = g ↔ _
  rw [AutOm.plusRefl]
  rw [reflAut_eq_self_iff (Q := coordinateQuadPlus 4 K)
    (regular_coordinateQuadPlus 4 K (by norm_num)).1
    (AutOm.plusUnitVector_form one_le_four) (AutOm.plusUnitVector_form_ne_zero one_le_four)]
  rw [AutOm.plusUnitVector_eq one_le_four]
  rfl

theorem spinSeven_eq : spinSeven K = (fixRho K).map (theta : MulAut (Om8 K)).toMonoidHom := rfl

theorem natCard_fixRho : Nat.card (fixRho K) = Nat.card (StatedSp 3 K) := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hf, hK⟩ := FiniteField.card K 2
  have hf' : 1 ≤ (f : ℕ) := f.pos
  have hK' : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hK
  have hreg := regular_coordinateQuadPlus 4 K (by norm_num)
  have hcomm := commutator_coordinateQuadPlus 4 K (by norm_num)
  have h : matrixDerivedScalars (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 K)) = ⊥ := by
    apply CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.matrixDerivedScalars_eq_bot_of_charTwo
    refine ⟨AutOm.vPlus one_le_four, ?_⟩
    change coordinateQuadPlus 4 K (AutOm.vPlus one_le_four) ≠ 0
    rw [AutOm.plusUnitVector_form one_le_four]
    exact one_ne_zero
  have hv : quadPlus 4 K (Pi.single (Sum.inl (0 : Fin 4)) (1 : K) +
      Pi.single (Sum.inr (0 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) = 1 := by
    rw [quadPlus_apply]
    simp only [Pi.add_apply, Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]
    rw [Finset.sum_eq_single (0 : Fin 4)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      simp at h
  have hvvec : reindexVectorEquiv (plusIndexEquiv 4)
      (Pi.single (Sum.inl (0 : Fin 4)) (1 : K) + Pi.single (Sum.inr (0 : Fin 4)) (1 : K) :
        Fin 4 ⊕ Fin 4 → K) = AutOm.pvec (0 : Fin 4) true + AutOm.pvec (0 : Fin 4) false := by
    rw [map_add, AutOm.pvec_true, AutOm.pvec_false, AutOm.reindex_single, AutOm.reindex_single]
  let Q' := reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 K)
  have hcast' : matrixDerived Q' = Om8 K := by
    unfold Om8 coordinateQuadPlus
    rfl
  let f' : matrixDerived Q' →* Om8 K :=
    { toFun := Eq.mp hcast'
      map_one' := by cases hcast'; rfl
      map_mul' := by intro a b; cases hcast'; rfl }
  let R : Subgroup (matrixDerived Q') := (fixRho K).comap f'
  have hmemR : ∀ z : matrixDerived Q', z ∈ R ↔ Eq.mp hcast' z ∈ fixRho K := fun z => Iff.rfl
  let e : StatedOmega (StatedQuadPlus 4 K) ≃* matrixDerived Q' :=
    statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)
  let β : MulAut (StatedOmega (StatedQuadPlus 4 K)) :=
    omegaSymmetryAut (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) h
      (Pi.single (Sum.inl (0 : Fin 4)) (1 : K) + Pi.single (Sum.inr (0 : Fin 4)) (1 : K) :
        Fin 4 ⊕ Fin 4 → K)
  have hfe : ∀ x : StatedOmega (StatedQuadPlus 4 K),
      Eq.mp hcast' (e x) = (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K)
        (coe_quadPlus 4 K) x : Om8 K) := by
    intro x
    cases hcast'
    rfl
  have key : ∀ x : StatedOmega (StatedQuadPlus 4 K), β x = x ↔ e x ∈ R := by
    intro x
    rw [hmemR, mem_fixRho_iff, hfe]
    have hβ : β x = x ↔ x ∈ fixedSubgroup β := Iff.rfl
    rw [hβ]
    dsimp only [β]
    have h2 := mem_fixedSubgroup_omegaSymmetryAut_iff (plusIndexEquiv 4) (quadPlus 4 K)
      (coe_quadPlus 4 K) h (Pi.single (Sum.inl (0 : Fin 4)) (1 : K) +
        Pi.single (Sum.inr (0 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) hreg.1 hv x
    rw [h2, ← hvvec]
    have h3 := statedDerivedReindexEquiv_mulVec (plusIndexEquiv 4) (quadPlus 4 K)
      (coe_quadPlus 4 K) x (Pi.single (Sum.inl (0 : Fin 4)) (1 : K) +
        Pi.single (Sum.inr (0 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K)
    rw [h3, (reindexVectorEquiv (K := K) (plusIndexEquiv 4)).injective.eq_iff]
  have hfix : fixedSubgroup (MulAut.congr e β) = R := by
    ext y
    change (MulAut.congr e β) y = y ↔ y ∈ R
    have hc : (MulAut.congr e β) y = e (β (e.symm y)) := by
      rw [MulAut.congr_apply]
      rfl
    have h1 : e (β (e.symm y)) = y ↔ β (e.symm y) = e.symm y := by
      constructor
      · intro h
        apply e.injective
        rw [h, e.apply_symm_apply]
      · intro h
        rw [h, e.apply_symm_apply]
    rw [hc, h1, key, e.apply_symm_apply]
  have hmap : fixedSubgroup (MulAut.congr e β) = (fixedSubgroup β).map e.toMonoidHom := by
    ext y
    change (MulAut.congr e β) y = y ↔ y ∈ (fixedSubgroup β).map e.toMonoidHom
    rw [Subgroup.mem_map]
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      have h1 : e (β (e.symm y)) = y := by
        have hc : (MulAut.congr e β) y = e (β (e.symm y)) := by
          rw [MulAut.congr_apply]
          rfl
        rw [hc] at hy
        exact hy
      have h2 : e (β (e.symm y)) = e (e.symm y) := by rw [h1, e.apply_symm_apply]
      exact e.injective h2
    · rintro ⟨x, hx, rfl⟩
      change e (β (e.symm (e x))) = e x
      rw [e.symm_apply_apply]
      exact congrArg e hx
  have hcard2 : Nat.card (fixedSubgroup (MulAut.congr e β)) = Nat.card (fixedSubgroup β) := by
    rw [hmap]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective (fixedSubgroup β) e.toMonoidHom e.injective).symm
  have hbij : Function.Bijective (f' : matrixDerived Q' → Om8 K) := by
    cases hcast'
    exact Function.bijective_id
  let ef : matrixDerived Q' ≃* Om8 K := MulEquiv.ofBijective f' hbij
  have hmapR : R.map ef.toMonoidHom = fixRho K := by
    ext z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hr
    · intro hz
      refine ⟨ef.symm z, ?_, ef.apply_symm_apply z⟩
      change f' (ef.symm z) ∈ fixRho K
      rw [show f' (ef.symm z) = z from by
        change ef (ef.symm z) = z
        exact ef.apply_symm_apply z]
      exact hz
  have hcardR : Nat.card R = Nat.card (fixRho K) := by
    rw [← hmapR]
    exact Nat.card_congr (Subgroup.equivMapOfInjective R ef.toMonoidHom ef.injective)
  have hcard3 : Nat.card (fixedSubgroup β) = Nat.card (StatedSp 3 K) := by
    obtain ⟨esp⟩ := nonempty_fixedSubgroup_omegaSymmetryAut_mulEquiv hf' hK' (by norm_num)
      (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) hreg.1 hreg.2 hcomm h hv
    exact Nat.card_congr esp.toEquiv
  calc Nat.card (fixRho K) = Nat.card R := hcardR.symm
    _ = Nat.card (fixedSubgroup (MulAut.congr e β)) := by rw [hfix]
    _ = Nat.card (fixedSubgroup β) := hcard2
    _ = Nat.card (StatedSp 3 K) := hcard3

theorem natCard_spinSeven : Nat.card (spinSeven K) = Nat.card (StatedSp 3 K) := by
  rw [spinSeven_eq]
  calc Nat.card ((fixRho K).map (theta : MulAut (Om8 K)).toMonoidHom)
      = Nat.card (fixRho K) := by
        exact Nat.card_congr (Subgroup.equivMapOfInjective (fixRho K)
          (theta : MulAut (Om8 K)).toMonoidHom (theta : MulAut (Om8 K)).injective).symm
    _ = Nat.card (StatedSp 3 K) := natCard_fixRho

section FieldOnly

variable {K : Type} [Field K] [CharP K 2]

theorem X8_mulVec_pvec {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) (c : K) (k : Fin 4) (b : Bool) :
    ((X8 γ c : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
        AutOm.pvec k b =
      AutOm.pvec k b + (if k = j ∧ b = !t then c • AutOm.pvec i s else 0) +
        (if k = i ∧ b = !s then c • AutOm.pvec j t else 0) := by
  have h' : ((X8 γ c : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ AutOm.pvec k b =
        D4Rank.act (X8 γ c) (AutOm.pvec k b) := rfl
  rw [h']
  refine (act_X8_pvec hij h c k b).trans ?_
  rw [sub_eq_add_neg, D4Rank.neg_vec]

end FieldOnly

private theorem refl0_rootD : refl0 rootD = rootC := by decide

private theorem refl0_rootC : refl0 rootC = rootD := by decide

private theorem commute_X8_rootC_rootD (c d : K) :
    Commute (X8 rootC c) (X8 rootD d) := by
  rw [show rootC = fromStd (lv 0 3 false true) from by decide,
    show rootD = fromStd (lv 0 3 true true) from by decide]
  exact commute_X8 (isD4Root_lv 0 3 false true (by decide))
    (isD4Root_lv 0 3 true true (by decide)) (by decide) c d

theorem X8_mem_fixRho {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) (hi : i ≠ 0) (hj : j ≠ 0) (c : K) : X8 γ c ∈ fixRho K := by
  rw [mem_fixRho_iff]
  rw [Matrix.mulVec_add, X8_mulVec_pvec hij h c 0 true,
    X8_mulVec_pvec hij h c 0 false]
  have h0i : (0 : Fin 4) ≠ i := fun h' => hi h'.symm
  have h0j : (0 : Fin 4) ≠ j := fun h' => hj h'.symm
  simp [h0i, h0j]

@[expose] noncomputable def Y (c : K) : Om8 K := X8 rootD c * X8 rootC c

theorem Y_mem_fixRho (c : K) : Y c ∈ fixRho K := by
  change AutOm.plusRefl (K := K) one_le_four (Y c) = Y c
  rw [Y, map_mul, plusRefl_X8 rootD_mem c, plusRefl_X8 rootC_mem c, refl0_rootD,
    refl0_rootC]
  exact commute_X8_rootC_rootD c c

theorem theta_Y (c : K) : theta (Y c) = X8 rootA c * X8 rootD c := by
  rw [Y, map_mul, theta_X8 rootD_mem c, theta_X8 rootC_mem c, tri_rootD, tri_rootC]

end CFSG.LieType.Sp6Spin
