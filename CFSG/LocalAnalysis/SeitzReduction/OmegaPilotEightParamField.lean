module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightParamRoot
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFourAniso

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus StatedSp)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived
  coordinateFieldMap)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  minusIndexEquiv regular_coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl fieldAutT)
open CFSG.SeitzReduction.TwistedE6Pilot (isExtension_coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti
  commutator_centralizerPerfectCore)
open scoped MatrixGroups

section Normalized

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {b c : K}

structure MinusNormalizedCover (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) {F : Type} [Field F] (k₀ : Subfield F) (φ : K ≃+* k₀)
    (σ : F ≃+* F)
    (hQσ : ∀ v, coordinateQuadMinus (2 + 1) F (by omega) ((φ b : k₀) : F) ((φ c : k₀) : F)
        (coordinateFieldMap _ σ v) =
      σ (coordinateQuadMinus (2 + 1) F (by omega) ((φ b : k₀) : F) ((φ c : k₀) : F) v)) where
  π : minusNeighbourCore e (2 : Fin (2 + 1)) →*
    matrixProjectiveDerived (coordinateQuadMinus (2 + 1) F (by omega) ((φ b : k₀) : F)
      ((φ c : k₀) : F))
  surjective : Function.Surjective π
  ker_le : π.ker ≤ center (minusNeighbourCore e (2 : Fin (2 + 1)))
  conj_t : ∀ x, π ((minusNeighbourCore e (2 : Fin (2 + 1))).normalizerMonoidHom
    ⟨t, mem_normalizer_minusNeighbourCore e htC 2⟩ x) =
      fieldAutT _ σ hQσ (π x)
  perp_le : modelToG e (minusPairPerp (K := K) (n := 2 + 2) (by omega) b c 2) ≤
    minusNeighbourCore e (2 : Fin (2 + 1))
  perp : ∀ d, π (Subgroup.inclusion perp_le d) =
    incl k₀ (isExtension_coordinateQuadMinus k₀ (by omega) (φ b) (φ c))
      (minusPairPerpFieldEquivOfLe (r := 2) le_rfl hirr e 2 φ d)

end Normalized

section Piece

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {b c : K}

omit [Finite K] [CharP K 2] in
theorem minusLevelCore_le_minusNeighbourCore_two
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c)) :
    minusLevelCore e ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1))) ≤
      minusNeighbourCore e (2 : Fin (2 + 1)) :=
  centralizerPerfectCore_anti (UnitaryPilot.modelToG_mono e
    (minusPairTorus_le_minusLevelTorus (by decide)))

theorem modelToG_frameLeviProj_le_minusLevelCore (hq : 4 ≤ Nat.card K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c)) :
    modelToG e (frameLeviProj (coordinateQuadMinus (2 + 2) K (by omega) b c)
        (minusFrameLeft (by omega)) (minusFrameRight (by omega)) ⟨0, by omega⟩ ⟨1, by omega⟩) ≤
      minusLevelCore e ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1))) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus (2 + 2) K b c le_rfl hirr
  have h := isHypFrame_minus K (n := 2 + 2) (by omega) b c
  exact UnitaryPilot.modelToG_le_centralizerPerfectCore e
    (h.frameLeviProj_le_centralizer (by simp) (by simp))
    (h.commutator_frameLeviProj (by simp) hq hQ hT)

end Piece

section Facts

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {b c : K} {hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c)} {t : G}
  {htC : t ∈ centralizer (L : Set G)} {F : Type} [Field F] [Finite F] [CharP F 2]
  {k₀ : Subfield F} {φ : K ≃+* k₀} {σ : F ≃+* F}
  {hQσ : ∀ v, coordinateQuadMinus (2 + 1) F (by omega) ((φ b : k₀) : F) ((φ c : k₀) : F)
      (coordinateFieldMap _ σ v) =
    σ (coordinateQuadMinus (2 + 1) F (by omega) ((φ b : k₀) : F) ((φ c : k₀) : F) v)}

omit [Finite K] [CharP K 2] [Finite F] [CharP F 2] in
theorem liftParam_subtype_liftParam (ι : K →+* F) (hφ : ∀ x, ((φ x : k₀) : F) = ι x)
    {m : ℕ} (s : Fin m → Kˣ) :
    liftParam k₀.subtype (liftParam φ.toRingHom s) = liftParam ι s := by
  funext l
  apply Units.ext
  simp [liftParam, hφ]

theorem MinusNormalizedCover.apply_frameHom
    (N : MinusNormalizedCover hirr e htC k₀ φ σ hQσ) (ι : K →+* F)
    (hφ : ∀ x, ((φ x : k₀) : F) = ι x) {t' : Fin (2 + 1) → Kˣ} (ht' : t' 2 = 1)
    (hmem : ((e.symm ((isHypFrame_minus K (n := 2 + 2) (by omega) b c).frameHom t') : L) : G) ∈
      minusNeighbourCore e (2 : Fin (2 + 1))) :
    N.π ⟨_, hmem⟩ = (isHypFrame_minus F (n := 2 + 1) (by omega) ((φ b : k₀) : F)
      ((φ c : k₀) : F)).frameHom (liftParam ι (restrictParam 2 t')) := by
  have : CharP k₀ 2 := RingHom.charP k₀.subtype Subtype.val_injective 2
  have hgD := symm_mem_modelToG e (frameHom_mem_minusPairPerp (n := 2 + 2) ht')
  have h1 : (⟨_, hmem⟩ : minusNeighbourCore e (2 : Fin (2 + 1))) =
      Subgroup.inclusion N.perp_le ⟨_, hgD⟩ := rfl
  rw [h1, N.perp]
  have h2 := minusPairPerpFieldEquivOfLe_frameHom (r := 2) le_rfl hirr e 2 φ ht' hgD
  refine (congrArg (incl k₀ (isExtension_coordinateQuadMinus k₀ (by omega) (φ b) (φ c))) h2).trans
    ?_
  rw [incl_frameHom_minus k₀ (n := 2 + 1) (by omega) (φ b) (φ c),
    liftParam_subtype_liftParam ι hφ]

theorem MinusNormalizedCover.apply_minusRootElt
    (N : MinusNormalizedCover hirr e htC k₀ φ σ hQσ) (ι : K →+* F)
    (hφ : ∀ x, ((φ x : k₀) : F) = ι x) (hK : 3 ≤ Nat.card K) (hF : 3 ≤ Nat.card F)
    {p' q' : Fin 2} (hpq' : p' ≠ q') {i j : Fin (2 + 2 - 1)}
    (hi : avoid (M := 2) (N := 2 + 1) (by omega) 2 p' = i)
    (hj : avoid (M := 2) (N := 2 + 1) (by omega) 2 q' = j) (x : K)
    (hmem : ((e.symm (minusRootElt (n := 2 + 2) le_rfl hirr i j x) : L) : G) ∈
      minusNeighbourCore e (2 : Fin (2 + 1))) :
    N.π ⟨_, hmem⟩ = minusLeviProj (n := 2 + 1) (by omega) ((φ b : k₀) : F) ((φ c : k₀) : F)
      (commutator_SL2_eq_top_of_charTwo hF)
      (Matrix.SpecialLinearGroup.transvection hpq' (-(ι x))) := by
  subst hi hj
  have : CharP k₀ 2 := RingHom.charP k₀.subtype Subtype.val_injective 2
  have : Finite k₀ := Subtype.finite
  have hk : 3 ≤ Nat.card k₀ := by
    rw [← Nat.card_congr φ.toEquiv]
    exact hK
  have hgD : ((e.symm (minusRootElt (n := 2 + 2) le_rfl hirr (avoid (M := 2) (N := 2 + 1)
      (by omega) 2 p') (avoid (M := 2) (N := 2 + 1) (by omega) 2 q') x) : L) : G) ∈
        modelToG e (minusPairPerp (K := K) (n := 2 + 2) (by omega) b c 2) :=
    symm_mem_modelToG e (minusRootElt_mem_minusPairPerp (n := 2 + 2) le_rfl hirr
      (fun h => hpq' (avoid_injective (M := 2) (N := 2 + 1) (by omega) 2 h))
      (avoid_ne (M := 2) (N := 2 + 1) (by omega) 2 p').symm
      (avoid_ne (M := 2) (N := 2 + 1) (by omega) 2 q').symm x)
  have h1 : (⟨_, hmem⟩ : minusNeighbourCore e (2 : Fin (2 + 1))) =
      Subgroup.inclusion N.perp_le ⟨_, hgD⟩ := rfl
  rw [h1, N.perp]
  have h2 := minusPairPerpFieldEquivOfLe_minusRootElt hirr e 2 φ
    (commutator_SL2_eq_top_of_charTwo hK) (commutator_SL2_eq_top_of_charTwo hk) hpq' x hgD
  refine (congrArg (incl k₀ (isExtension_coordinateQuadMinus k₀ (by omega) (φ b) (φ c))) h2).trans
    ?_
  rw [incl_minusLeviProj (n := 2 + 1) (by omega) k₀ (φ b) (φ c)
      (commutator_SL2_eq_top_of_charTwo hk) (commutator_SL2_eq_top_of_charTwo hF),
    map_transvection_eq, map_neg]
  congr 3
  exact hφ x

end Facts

theorem succAbove_two_mem_zero_one : ∀ i : Fin 2,
    (2 : Fin (2 + 1)).succAbove i ∈
      ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1))) := by
  decide

theorem card_minusPlanes_zero_one :
    ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1))).card = 2 := by
  decide

theorem card_castSuccPlanes_preimagePlanes_two :
    (castSuccPlanes (preimagePlanes (2 : Fin (2 + 1))
      ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1))))).card = 2 := by
  decide

section Image

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {b c : K} {hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c)} {t : G}
  {htC : t ∈ centralizer (L : Set G)} {F : Type} [Field F] [Finite F] [CharP F 2]
  {k₀ : Subfield F} {φ : K ≃+* k₀} {σ : F ≃+* F}
  {hQσ : ∀ v, coordinateQuadMinus (2 + 1) F (by omega) ((φ b : k₀) : F) ((φ c : k₀) : F)
      (coordinateFieldMap _ σ v) =
    σ (coordinateQuadMinus (2 + 1) F (by omega) ((φ b : k₀) : F) ((φ c : k₀) : F) v)}

theorem MinusNormalizedCover.range_le_map (N : MinusNormalizedCover hirr e htC k₀ φ σ hQσ)
    (ι : K →+* F) (hφ : ∀ x, ((φ x : k₀) : F) = ι x) (hF : 3 ≤ Nat.card F) :
    (minusLeviProj (n := 2 + 1) (by omega) ((φ b : k₀) : F) ((φ c : k₀) : F)
        (commutator_SL2_eq_top_of_charTwo hF)).range ≤
      ((minusLevelCore e ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1)))).subgroupOf
        (minusNeighbourCore e (2 : Fin (2 + 1)))).map N.π := by
  set h := isHypFrame_minus K (n := 2 + 2) (by omega) b c with hh
  set X := modelToG e (minusPairTorus (K := K) (n := 2 + 2) (by omega) b c 2) with hX
  set T := modelToG e (minusLevelTorus (K := K) (n := 2 + 2) (by omega) b c
    ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1)))) with hT
  have hXT : X ≤ modelToG e (frameTorusOf (coordinateQuadMinus (2 + 2) K (by omega) b c)
      (minusFrameLeft (by omega)) (minusFrameRight (by omega))
      (levelParam ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1))))) :=
    UnitaryPilot.modelToG_mono e (minusPairTorus_le_minusLevelTorus (by simp))
  have hN : ∀ d : T, (d : G) ∈ normalizer (minusNeighbourCore e (2 : Fin (2 + 1)) : Set G) :=
    fun d => mem_normalizer_centralizerPerfectCore_of_mem_frame h e hXT d.2
  let τ : T → Fin (2 + 1) → Kˣ := fun d =>
    (exists_param_of_mem_modelToG_frameTorusOf h e d.2).choose
  have hτ : ∀ d : T, τ d ∈ levelParam ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1))) ∧
      ((e.symm (h.frameHom (τ d)) : L) : G) = d :=
    fun d => (exists_param_of_mem_modelToG_frameTorusOf h e d.2).choose_spec
  set δ : (Fin (2 + 1) → Kˣ) → matrixProjectiveDerived (coordinateQuadMinus (2 + 1) F (by omega)
      ((φ b : k₀) : F) ((φ c : k₀) : F)) := fun s =>
    (isHypFrame_minus F (n := 2 + 1) (by omega) ((φ b : k₀) : F) ((φ c : k₀) : F)).frameHom
      (liftParam ι (restrictParam 2 s)) with hδdef
  have hδ : ∀ s : Fin (2 + 1) → Kˣ, δ (s * (Pi.mulSingle 2 (s 2))⁻¹) = δ s := by
    intro s
    simp only [hδdef]
    congr 2
    funext i
    rw [restrictParam_apply, restrictParam_apply, Pi.mul_apply, Pi.inv_apply,
      Pi.mulSingle_eq_of_ne (Fin.succAbove_ne 2 i), inv_one, mul_one]
  have hnorm : ∀ s : Fin (2 + 1) → Kˣ, s 2 = 1 →
      ∀ hmem : ((e.symm (h.frameHom s) : L) : G) ∈ minusNeighbourCore e (2 : Fin (2 + 1)),
        N.π ⟨_, hmem⟩ = δ s := fun s hs hmem => N.apply_frameHom ι hφ hs hmem
  let α : T → MulAut (minusNeighbourCore e (2 : Fin (2 + 1))) := fun d =>
    (minusNeighbourCore e (2 : Fin (2 + 1))).normalizerMonoidHom ⟨d, hN d⟩
  let β : T → MulAut (matrixProjectiveDerived (coordinateQuadMinus (2 + 1) F (by omega)
      ((φ b : k₀) : F) ((φ c : k₀) : F))) := fun d => MulAut.conj (δ (τ d))
  have hαβ : ∀ d x, N.π (α d x) = β d (N.π x) := by
    intro d x
    have hN' : ((e.symm (h.frameHom (τ d)) : L) : G) ∈
        normalizer (minusNeighbourCore e (2 : Fin (2 + 1)) : Set G) := by
      rw [(hτ d).2]
      exact hN d
    have heq : (⟨(d : G), hN d⟩ : normalizer (minusNeighbourCore e (2 : Fin (2 + 1)) : Set G)) =
        ⟨_, hN'⟩ := Subtype.ext (hτ d).2.symm
    change N.π ((minusNeighbourCore e (2 : Fin (2 + 1))).normalizerMonoidHom ⟨d, hN d⟩ x) =
      MulAut.conj (δ (τ d)) (N.π x)
    rw [heq, conj_of_normalized_minus e 2 N.π N.perp_le δ hδ hnorm (τ d) hN' x,
      MulAut.conj_apply]
  have hmain := map_centralizerPerfectCore_subgroupOf_eq_of_le (X := X) (T := T)
    (minusLevelCore_le_minusNeighbourCore_two e) N.π N.surjective N.ker_le α
    (fun d x => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _) β hαβ
  refine le_trans ?_ hmain.ge
  apply CFSG.Quasithin.le_perfectCore_of_perfect
  · rintro _ ⟨A, rfl⟩ d
    have hs : ∀ i j : Fin (2 + 1 - 1), liftParam ι (restrictParam 2 (τ d)) i =
        liftParam ι (restrictParam 2 (τ d)) j := by
      intro i j
      simp only [liftParam, restrictParam_apply]
      congr 1
      exact (hτ d).1 _ (succAbove_two_mem_zero_one i) _ (succAbove_two_mem_zero_one j)
    have hcomm := commute_frameHom_minusLeviProj (n := 2 + 1) (by omega) ((φ b : k₀) : F)
      ((φ c : k₀) : F) (commutator_SL2_eq_top_of_charTwo hF) hs A
    show MulAut.conj (δ (τ d)) _ = _
    rw [MulAut.conj_apply, hcomm.eq, mul_inv_cancel_right]
  · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
      commutator_SL2_eq_top_of_charTwo hF]

theorem MinusNormalizedCover.card_map (N : MinusNormalizedCover hirr e htC k₀ φ σ hQσ)
    (ι : K →+* F) (hφ : ∀ x, ((φ x : k₀) : F) = ι x) (hq : 4 ≤ Nat.card K)
    (hFK : Nat.card F = Nat.card K ^ 2) :
    Nat.card (((minusLevelCore e ({⟨0, by omega⟩, ⟨1, by omega⟩} :
        Finset (Fin (2 + 2 - 1)))).subgroupOf (minusNeighbourCore e (2 : Fin (2 + 1)))).map N.π) =
      Nat.card (SpecialLinearGroup (Fin 2) F) := by
  have hF4 : 4 ≤ Nat.card F := by rw [hFK]; nlinarith
  obtain ⟨α, hα⟩ := exists_root_of_card_eq_sq ι hFK hirr
  have hαF : α ^ 2 + ((φ b : k₀) : F) * α + ((φ c : k₀) : F) = 0 := by
    rw [hφ, hφ]
    exact hα
  have hβ0 : ((φ b : k₀) : F) ≠ 0 := by
    rw [hφ]
    exact (map_ne_zero ι).2 (coeff_ne_zero_of_irreducible hirr)
  have hαα := root_ne_other_of_ne_zero (α := α) hβ0
  set B := minusPlusBridge (r := 2) (by omega) hαF hαα with hB
  set π0 := B.toMonoidHom.comp N.π with hπ0
  have hs0 : Function.Surjective π0 := B.surjective.comp N.surjective
  have hk0 : π0.ker ≤ center (minusNeighbourCore e (2 : Fin (2 + 1))) := by
    intro x hx
    apply N.ker_le
    exact (MulEquiv.map_eq_one_iff B).1 hx
  have hn0 : ∀ t' : Fin (2 + 1) → Kˣ, t' 2 = 1 →
      ∀ hmem : ((e.symm ((isHypFrame_minus K (n := 2 + 2) (by omega) b c).frameHom t') : L) :
        G) ∈ minusNeighbourCore e (2 : Fin (2 + 1)),
        ((π0 ⟨_, hmem⟩ : StatedOmega (StatedQuadPlus (2 + 1) F)) :
          GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) = minusNeighbourDiag ι 2 t' := by
    intro t' ht' hmem
    change ((B (N.π ⟨_, hmem⟩) : StatedOmega (StatedQuadPlus (2 + 1) F)) :
      GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) = _
    rw [N.apply_frameHom ι hφ ht' hmem, hB, minusPlusBridge_frameHom, minusNeighbourDiag_apply]
  set C := MinusFieldCover.ofNormalized (e := e) (ι := ι) (k := 2) π0 hs0 hk0 N.perp_le hn0
  have hmap := C.map_levelCore hq hF4
    (J := ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1)))) (by simp)
    card_minusPlanes_zero_one.ge
  set U := (minusLevelCore e ({⟨0, by omega⟩, ⟨1, by omega⟩} :
    Finset (Fin (2 + 2 - 1)))).subgroupOf (minusNeighbourCore e (2 : Fin (2 + 1))) with hU
  have h1 : Nat.card (U.map N.π) = Nat.card (U.map C.π) := by
    rw [← Subgroup.card_map_of_injective (K := U.map N.π) (f := B.toMonoidHom) B.injective,
      Subgroup.map_map]
    rfl
  have h2 : Nat.card (U.map C.π) = Nat.card ((U.map C.π).map
      (StatedOmega (StatedQuadPlus (2 + 1) F)).subtype) :=
    (Subgroup.card_map_of_injective (StatedOmega (StatedQuadPlus (2 + 1) F)).subtype_injective).symm
  rw [h1, h2, hmap, siegelBlockGL,
    Subgroup.card_map_of_injective (StatedSp (2 + 1) F).subtype_injective,
    ← Nat.card_congr (SymplecticPilot.siegelBlockEquiv _).toEquiv,
    card_castSuccPlanes_preimagePlanes_two]

end Image

theorem avoid_two_zero :
    avoid (M := 2) (N := 2 + 1) (by omega) 2 0 = (⟨0, by omega⟩ : Fin (2 + 2 - 1)) := by
  decide

theorem avoid_two_one :
    avoid (M := 2) (N := 2 + 1) (by omega) 2 1 = (⟨1, by omega⟩ : Fin (2 + 2 - 1)) := by
  decide

theorem sl2Upper_eq_transvection {R : Type*} [Field R] (x : R) :
    CFSG.LocalAnalysis.ComponentInitial.sl2Upper R x =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.transvection_coe]

theorem sl2Lower_eq_transvection {R : Type*} [Field R] (x : R) :
    CFSG.LocalAnalysis.ComponentInitial.sl2Lower R x =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.transvection_coe]

theorem inclusion_conj_eq_normalizerMonoidHom {G : Type*} [Group G] {U E : Subgroup G}
    (hUE : U ≤ E) {t : G} (htE : t ∈ normalizer (E : Set G)) (u : U)
    (hmem : t * (u : G) * t⁻¹ ∈ U) :
    Subgroup.inclusion hUE ⟨_, hmem⟩ = E.normalizerMonoidHom ⟨t, htE⟩ (Subgroup.inclusion hUE u) :=
  Subtype.ext (by rw [Subgroup.normalizerMonoidHom_apply_apply_coe]; rfl)

theorem ker_comp_inclusion_le_center {G M : Type*} [Group G] [Group M] {U E : Subgroup G}
    (hUE : U ≤ E) (π : E →* M) (hπ : π.ker ≤ center E) :
    (π.comp (Subgroup.inclusion hUE)).ker ≤ center U := by
  intro u hu
  have h2 := hπ (MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hu))
  rw [mem_center_iff] at h2 ⊢
  intro v
  have h3 := congrArg Subtype.val (h2 (Subgroup.inclusion hUE v))
  exact Subtype.ext h3

theorem exists_mulEquiv_SL2_of_range_eq
    {F : Type} [Field F] [Finite F]
    (hF5 : 5 ≤ Nat.card F) (hF9 : Nat.card F ≠ 9) {U M : Type*} [Group U] [Group M]
    [Group.IsPerfect U] (πU : U →* M) (ρ : SpecialLinearGroup (Fin 2) F →* M)
    (hρ : Function.Injective ρ) (hrange : πU.range = ρ.range) (hker : πU.ker ≤ center U) :
    ∃ Θ : U ≃* SpecialLinearGroup (Fin 2) F, ∀ u, πU u = ρ (Θ u) := by
  have hmem : ∀ u, πU u ∈ ρ.range := fun u => hrange ▸ ⟨u, rfl⟩
  let ρe := MonoidHom.ofInjective hρ
  let θ : U →* SpecialLinearGroup (Fin 2) F :=
    ρe.symm.toMonoidHom.comp (πU.codRestrict ρ.range hmem)
  have hθ : ∀ u, ρ (θ u) = πU u := by
    intro u
    have h1 : ρe (θ u) = ⟨πU u, hmem u⟩ := ρe.apply_symm_apply _
    exact congrArg Subtype.val h1
  have hθs : Function.Surjective θ := by
    intro A
    obtain ⟨u, hu⟩ := hrange.ge ⟨A, rfl⟩
    exact ⟨u, hρ ((hθ u).trans hu)⟩
  have hker' : θ.ker ≤ center U := by
    intro u hu
    apply hker
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [← hθ, hu, map_one]
  obtain ⟨s, hs⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SL2Closed.sl2_exists_section_of_central hF5 hF9 hθs hker'
  have hbot := CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section θ hker' s hs
  have hθinj : Function.Injective θ := (MonoidHom.ker_eq_bot_iff θ).mp hbot
  exact ⟨MulEquiv.ofBijective θ ⟨hθinj, hθs⟩, fun u => (hθ u).symm⟩

section Param


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {b c : K} {hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c)} {t : G}
  {htC : t ∈ centralizer (L : Set G)} {F : Type} [Field F] [Finite F] [CharP F 2]
  {k₀ : Subfield F} {φ : K ≃+* k₀} {σ : F ≃+* F}
  {hQσ : ∀ v, coordinateQuadMinus (2 + 1) F (by omega) ((φ b : k₀) : F) ((φ c : k₀) : F)
      (coordinateFieldMap _ σ v) =
    σ (coordinateQuadMinus (2 + 1) F (by omega) ((φ b : k₀) : F) ((φ c : k₀) : F) v)}

theorem MinusNormalizedCover.nonempty_minusRootFieldParam
    (N : MinusNormalizedCover hirr e htC k₀ φ σ hQσ) (ι : K →+* F)
    (hφ : ∀ x, ((φ x : k₀) : F) = ι x) (hq : 4 ≤ Nat.card K)
    (hFK : Nat.card F = Nat.card K ^ 2) :
    Nonempty (MinusRootFieldParam (n := 2 + 2) le_rfl hirr e t ι σ ⟨0, by omega⟩
      ⟨1, by omega⟩) := by
  have hF4 : 4 ≤ Nat.card F := by rw [hFK]; nlinarith
  have hF3 : 3 ≤ Nat.card F := by omega
  have hK3 : 3 ≤ Nat.card K := by omega
  have hF5 : 5 ≤ Nat.card F := by rw [hFK]; nlinarith
  have hF9 : Nat.card F ≠ 9 := by
    intro h9
    rw [hFK] at h9
    nlinarith
  set U := minusLevelCore e ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1)))
    with hUdef
  set E := minusNeighbourCore e (2 : Fin (2 + 1)) with hEdef
  have hUE : U ≤ E := minusLevelCore_le_minusNeighbourCore_two e
  have hYU := modelToG_frameLeviProj_le_minusLevelCore hq hirr e
  set ρ := minusLeviProj (n := 2 + 1) (by omega) ((φ b : k₀) : F) ((φ c : k₀) : F)
    (commutator_SL2_eq_top_of_charTwo hF3) with hρ
  have hρinj : Function.Injective ρ := minusLeviProj_injective _ _ _ _
  have himg : (U.subgroupOf E).map N.π = ρ.range := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (N.range_le_map ι hφ hF3)
    rw [N.card_map ι hφ hq hFK, ← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
  set πU : U →* _ := N.π.comp (Subgroup.inclusion hUE) with hπU
  have hπUrange : πU.range = ρ.range := by
    rw [hπU, MonoidHom.range_comp, Subgroup.inclusion_range, himg]
  have hπUker : πU.ker ≤ center U := ker_comp_inclusion_le_center hUE N.π N.ker_le
  have : Group.IsPerfect U := Subgroup.isPerfect_iff.mpr (commutator_centralizerPerfectCore _)
  obtain ⟨Θ, hΘ⟩ := exists_mulEquiv_SL2_of_range_eq hF5 hF9 πU ρ hρinj hπUrange hπUker
  have huniq : ∀ (u : U) (A : SpecialLinearGroup (Fin 2) F),
      N.π (Subgroup.inclusion hUE u) = ρ A → u = Θ.symm A := by
    intro u A h
    rw [MulEquiv.eq_symm_apply]
    apply hρinj
    rw [← h]
    exact (hΘ u).symm
  have hΘρ : ∀ A, N.π (Subgroup.inclusion hUE (Θ.symm A)) = ρ A := by
    intro A
    have h1 := hΘ (Θ.symm A)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hroot : ∀ {p' q' : Fin 2} (hpq' : p' ≠ q') {i j : Fin (2 + 2 - 1)}
      (hi : avoid (M := 2) (N := 2 + 1) (by omega) 2 p' = i)
      (hj : avoid (M := 2) (N := 2 + 1) (by omega) 2 q' = j) (x : K)
      (hmemU : ((e.symm (minusRootElt (n := 2 + 2) le_rfl hirr i j x) : L) : G) ∈ U),
      (⟨_, hmemU⟩ : U) = Θ.symm (Matrix.SpecialLinearGroup.transvection hpq' (-(ι x))) := by
    intro p' q' hpq' i j hi hj x hmemU
    apply huniq
    exact N.apply_minusRootElt ι hφ hK3 hF3 hpq' hi hj x (hUE hmemU)
  refine ⟨⟨U.subtype.comp Θ.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 Θ.symm.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  ·
    intro A
    have htop : (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)) ≤
        (modelToG e (frameLeviProj (coordinateQuadMinus (2 + 2) K (by omega) b c)
          (minusFrameLeft (by omega)) (minusFrameRight (by omega)) ⟨0, by omega⟩
          ⟨1, by omega⟩)).comap ((U.subtype.comp Θ.symm.toMonoidHom).comp
            (Matrix.SpecialLinearGroup.map ι)) := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower, Subgroup.closure_le]
      rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · have hmemY := symm_mem_modelToG e (minusRootElt_mem_frameLeviProj (n := 2 + 2) le_rfl hirr
          ⟨0, by omega⟩ ⟨1, by omega⟩ (-x))
        have h := hroot (p' := 0) (q' := 1) (by decide) avoid_two_zero avoid_two_one (-x)
          (hYU hmemY)
        rw [map_neg, neg_neg] at h
        simp only [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply,
          MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
        rw [sl2Upper_eq_transvection, map_transvection_eq, ← h]
        exact hmemY
      · have hmemY := symm_mem_modelToG e (minusRootElt_swap_mem_frameLeviProj (n := 2 + 2) le_rfl
          hirr ⟨0, by omega⟩ ⟨1, by omega⟩ (-x))
        have h := hroot (p' := 1) (q' := 0) (by decide) avoid_two_one avoid_two_zero (-x)
          (hYU hmemY)
        rw [map_neg, neg_neg] at h
        simp only [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply,
          MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
        rw [sl2Lower_eq_transvection, map_transvection_eq, ← h]
        exact hmemY
    exact htop (Subgroup.mem_top A)
  ·
    have hmemY := symm_mem_modelToG e (minusRootElt_mem_frameLeviProj (n := 2 + 2) le_rfl hirr
      ⟨0, by omega⟩ ⟨1, by omega⟩ 1)
    have h := hroot (p' := 0) (q' := 1) (by decide) avoid_two_zero avoid_two_one 1 (hYU hmemY)
    have h1 : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (-(ι 1)) =
        LinearPilot.upperUnit 1 := by
      rw [map_one, CharTwo.neg_eq]
      rfl
    rw [h1] at h
    change ((Θ.symm (LinearPilot.upperUnit 1) : U) : G) = _
    rw [← h]
  ·
    intro A
    have htU : t ∈ normalizer (U : Set G) :=
      UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e htC _
    have hmem : t * ((Θ.symm A : U) : G) * t⁻¹ ∈ U :=
      (mem_normalizer_iff.1 htU _).1 (Θ.symm A).2
    have h := huniq ⟨_, hmem⟩ (Matrix.SpecialLinearGroup.map σ.toRingHom A) (by
      rw [inclusion_conj_eq_normalizerMonoidHom hUE (mem_normalizer_minusNeighbourCore e htC 2)
        (Θ.symm A) hmem, N.conj_t, hΘρ]
      exact fieldAutT_minusLeviProj (n := 2 + 1) (by omega) _ _ _ σ hQσ A)
    exact congrArg Subtype.val h

end Param

end CFSG.SeitzReduction.OmegaPilot
