module

public import CFSG.LieType.Universal.SpinOmega.CommutatorEquiv
public import CFSG.LieType.Universal.Spin.Chevalley.Plus
public import CFSG.LieType.Universal.Spin.PlusCT.Weyl
public import CFSG.LieType.Universal.Spin.Generation.Datum
public import CFSG.LieType.CurtisTits.Reduction
public import CFSG.RankThree.PartOne.KC.OrthogonalHypCoordinates
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.LieType.Universal.Spin

open QuadraticMap CFSG.LieType.CurtisTits CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {n : ℕ}

namespace HypFrame

def hypPair (Fr : HypFrame Q n) (i : Fin n) : HypPair Q where
  e := Fr.vec i true
  f := Fr.vec i false
  Q_e := Fr.map_vec i true
  Q_f := Fr.map_vec i false
  polar_ef := Fr.polar_vec_not i true

omit [FiniteDimensional K V] in
private theorem hypPair_orth (Fr : HypFrame Q n) :
    ∀ i j, i ≠ j → (Fr.hypPair i).Orth (Fr.hypPair j) := by
  intro i j hij
  exact ⟨Fr.polar_vec_of_ne hij true true, Fr.polar_vec_of_ne hij true false,
    Fr.polar_vec_of_ne hij false true, Fr.polar_vec_of_ne hij false false⟩

private theorem pairsPerp_hypPair_eq_bot (Fr : HypFrame Q n)
    (hdim : Module.finrank K V = 2 * n) : pairsPerp Fr.hypPair = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  have h := (hypCoordEquiv Fr.hypPair_orth).finrank_eq
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
    Fintype.card_fin, hdim] at h
  omega

noncomputable def isometryQuadPlus (Fr : HypFrame Q n) (hdim : Module.finrank K V = 2 * n) :
    Q.IsometryEquiv (quadPlus n K) :=
  hypCoordSplitIsometry Fr.hypPair_orth (Fr.pairsPerp_hypPair_eq_bot hdim)

private theorem isometryQuadPlus_apply (Fr : HypFrame Q n)
    (hdim : Module.finrank K V = 2 * n) (v : V) :
    Fr.isometryQuadPlus hdim v =
      hypCoordSplitEquiv Fr.hypPair_orth (Fr.pairsPerp_hypPair_eq_bot hdim) v :=
  rfl

theorem isometryQuadPlus_vec (Fr : HypFrame Q n) (hdim : Module.finrank K V = 2 * n)
    (i : Fin n) (s : Bool) : Fr.isometryQuadPlus hdim (Fr.vec i s) = plusVec n K i s := by
  rw [isometryQuadPlus_apply]
  cases s
  · exact hypCoordSplitEquiv_f Fr.hypPair_orth (Fr.pairsPerp_hypPair_eq_bot hdim) i
  · exact hypCoordSplitEquiv_e Fr.hypPair_orth (Fr.pairsPerp_hypPair_eq_bot hdim) i

end HypFrame

theorem coe_commutatorEquivSpinPlus_symm_longRoot (Fr : HypFrame Q n)
    (hdim : Module.finrank K V = 2 * n) (hn : 3 ≤ n) (h2 : (2 : K) = 0) {i j : Fin n}
    (hij : i ≠ j) (s t : Bool) (c : K) :
    (((commutatorEquivSpinPlusOfIsometry (Fr.isometryQuadPlus hdim) hn h2).symm
        ((plusFrame n K hn).longRoot hij s t (.ofAdd c)) :
        ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
      V ≃ₗ[K] V) = spinAction Q (Fr.longRoot hij s t (.ofAdd c)) := by
  set e := Fr.isometryQuadPlus hdim
  set X := (plusFrame n K hn).longRoot hij s t (.ofAdd c) with hX
  set g : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    (commutatorEquivSpinPlusOfIsometry e hn h2).symm X with hg
  have hXg : commutatorEquivSpinPlusOfIsometry e hn h2 g = X := by
    rw [hg]
    exact MulEquiv.apply_symm_apply _ _
  have h := spinAction_commutatorEquivSpinPlusOfIsometry_apply e hn h2 g
  rw [hXg] at h
  apply LinearEquiv.ext
  intro v
  apply e.injective
  have hL : e.toLinearEquiv (spinAction Q (Fr.longRoot hij s t (.ofAdd c)) v) =
      e.toLinearEquiv v +
        (c * polar (quadPlus n K) (e v) (plusVec n K j t)) • plusVec n K i s -
        (c * polar (quadPlus n K) (e v) (plusVec n K i s)) • plusVec n K j t := by
    rw [Fr.spinAction_longRoot]
    rw [map_sub, map_add, map_smul, map_smul]
    rw [← e.polar_apply v (Fr.vec j t), ← e.polar_apply v (Fr.vec i s)]
    rw [HypFrame.isometryQuadPlus_vec Fr hdim j t,
      HypFrame.isometryQuadPlus_vec Fr hdim i s]
    rw [show e.toLinearEquiv (Fr.vec i s) = plusVec n K i s from
      HypFrame.isometryQuadPlus_vec Fr hdim i s,
      show e.toLinearEquiv (Fr.vec j t) = plusVec n K j t from
      HypFrame.isometryQuadPlus_vec Fr hdim j t]
  have h' : e.toLinearEquiv ((g : V ≃ₗ[K] V) v) = spinAction (quadPlus n K) X (e v) := by
    rw [h, LinearEquiv.autCongr_apply_apply]
    change e.toLinearEquiv ((g : V ≃ₗ[K] V) v) =
      e.toLinearEquiv ((g : V ≃ₗ[K] V) (e.toLinearEquiv.symm (e.toLinearEquiv v)))
    rw [LinearEquiv.symm_apply_apply]
  rw [h', hL, hX]
  rw [HypFrame.spinAction_longRoot (F := plusFrame n K hn) hij s t c (e v)]
  rw [plusFrame_vec]
  simp only [QuadraticMap.IsometryEquiv.coe_toLinearEquiv]

theorem commutator_eq_iSup_simpleRoot (Fr : HypFrame Q n) (hdim : Module.finrank K V = 2 * n)
    (hn : 3 ≤ n) (h2 : (2 : K) = 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      ⨆ k : Fin n,
        (((spinAction Q).comp
            (Fr.longRoot (rootIdxD_ne n (by omega) k) true (rootSignD n k))).range ⊔
          ((spinAction Q).comp
            (Fr.longRoot (rootIdxD_ne n (by omega) k).symm (!rootSignD n k) false)).range) := by
  set e := Fr.isometryQuadPlus hdim
  set ψ : spinGroup (quadPlus n K) ≃*
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    (commutatorEquivSpinPlusOfIsometry e hn h2).symm
  set φ : spinGroup (quadPlus n K) →* (V ≃ₗ[K] V) :=
    (Subgroup.subtype _).comp ψ.toMonoidHom
  have hgen : ⨆ k : Fin n, ((rootD K hn k).range ⊔ (negRootD K hn k).range) = ⊤ := by
    have hgen0 := plusDatum_iSup_eq_top n K hn
    have hK := plusDatum_isCTGroupDatum hn hgen0
    have hΦ := CFSG.LieType.RootSystem.isCTRootSystem (isFiniteType_cartanD n) ∅
    have hlevi := iSup_leviAmalgam_eq_top hΦ hK
    have htop : ⨆ k : Fin n, rankOne (plusRootGroup n K hn) k = ⊤ := by
      refine eq_top_iff.mpr ?_
      rw [← hlevi]
      exact iSup_le fun J => iSup₂_le fun j _ =>
        le_iSup (fun i => rankOne (plusRootGroup n K hn) i) j
    simpa [rankOne, plusRootGroup_single, plusRootGroup_neg_single] using htop
  have hφtop : (⊤ : Subgroup (spinGroup (quadPlus n K))).map φ =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rw [show φ = (Subgroup.subtype _).comp ψ.toMonoidHom from rfl, ← Subgroup.map_map,
      Subgroup.map_top_of_surjective _ ψ.surjective, Subgroup.map_top, Subgroup.range_subtype]
  have hrootD : ∀ k : Fin n,
      φ.comp (rootD K hn k) =
        (spinAction Q).comp
          (Fr.longRoot (rootIdxD_ne n (by omega) k) true (rootSignD n k)) := by
    intro k
    refine MonoidHom.ext fun x => ?_
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective x
    exact coe_commutatorEquivSpinPlus_symm_longRoot Fr hdim hn h2
      (rootIdxD_ne n (by omega) k) true (rootSignD n k) c
  have hnegRootD : ∀ k : Fin n,
      φ.comp (negRootD K hn k) =
        (spinAction Q).comp
          (Fr.longRoot (rootIdxD_ne n (by omega) k).symm (!rootSignD n k) false) := by
    intro k
    refine MonoidHom.ext fun x => ?_
    obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective x
    exact coe_commutatorEquivSpinPlus_symm_longRoot Fr hdim hn h2
      (rootIdxD_ne n (by omega) k).symm (!rootSignD n k) false c
  calc
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆
        = (⊤ : Subgroup (spinGroup (quadPlus n K))).map φ := hφtop.symm
    _ = (⨆ k : Fin n, ((rootD K hn k).range ⊔ (negRootD K hn k).range)).map φ := by
          rw [hgen]
    _ = ⨆ k : Fin n, (((rootD K hn k).range ⊔ (negRootD K hn k).range).map φ) :=
          Subgroup.map_iSup φ _
    _ = ⨆ k : Fin n, (((rootD K hn k).range.map φ) ⊔ ((negRootD K hn k).range.map φ)) := by
          refine iSup_congr fun k => ?_
          rw [Subgroup.map_sup]
    _ = ⨆ k : Fin n,
          (((spinAction Q).comp
              (Fr.longRoot (rootIdxD_ne n (by omega) k) true (rootSignD n k))).range ⊔
            ((spinAction Q).comp
              (Fr.longRoot (rootIdxD_ne n (by omega) k).symm (!rootSignD n k) false)).range) := by
          refine iSup_congr fun k => ?_
          rw [← MonoidHom.range_comp (f := rootD K hn k) (g := φ), hrootD k,
            ← MonoidHom.range_comp (f := negRootD K hn k) (g := φ), hnegRootD k]

end CFSG.LieType.Universal.Spin
