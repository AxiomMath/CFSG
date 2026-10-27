module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightInputsHR8
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Bridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFourMain

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  minusIndexEquiv)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG
  SUmCatalogueClausesAt)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl fieldAutT)
open CFSG.SeitzReduction.TwistedE6Pilot (isExtension_coordinateQuadMinus
  coordinateQuadMinus_fieldMap_of_fixed)

section Perp

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem minusPairPerpEquivOfLe_frameHom {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) {t : Fin (n - 1) → Kˣ}
    (ht : t k = 1) :
    ((minusPairPerpEquivOfLe hn hirr k ⟨(isHypFrame_minus K (by omega) b c).frameHom t,
        frameHom_mem_minusPairPerp ht⟩ :
      orthDerived (coordinateQuadMinus (n - 1) K (by omega) b c)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) =
      frameLin (minusFrameLeft (n := n - 1) (by omega)) (minusFrameRight (n := n - 1) (by omega))
        (fun l => t (avoid (by omega) k l)) := by
  ext w x
  rw [minusPairPerpEquivOfLe_apply hn hirr k _
    ⟨frameLin (minusFrameLeft (by omega)) (minusFrameRight (by omega)) t,
      (isHypFrame_minus K (by omega) b c).frameLin_mem_orthDerived t⟩
    (minusFrameLin_mem_stabSub (by omega) b c ht) rfl w x]
  change frameLin (minusFrameLeft (by omega)) (minusFrameRight (by omega)) t
      (Function.extend (minusPerpCoord (by omega) k) w 0) (minusPerpCoord (by omega) k x) =
    frameLin (minusFrameLeft (n := n - 1) (by omega)) (minusFrameRight (n := n - 1) (by omega))
      (fun l => t (avoid (by omega) k l)) w x
  rw [frameLin_apply, frameLin_apply, (minusPerpCoord_injective _ k).extend_apply,
    frameEntry_minusPerpCoord]

@[expose] noncomputable def minusPairPerpModelEquivOfLe {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    minusPairPerp (K := K) (by omega : 1 ≤ n) b c k ≃*
      matrixProjectiveDerived (coordinateQuadMinus (n - 1) K (by omega) b c) :=
  (minusPairPerpEquivOfLe hn hirr k).trans (MulEquiv.ofBijective (projHom _)
    ⟨projHom_injective (isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n - 1) b c
      (⟨0, by omega⟩ : Fin (n - 1 - 1))).exists_ne_zero, projHom_surjective _⟩)

theorem minusPairPerpModelEquivOfLe_frameHom {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) {t : Fin (n - 1) → Kˣ}
    (ht : t k = 1) :
    minusPairPerpModelEquivOfLe hn hirr k ⟨(isHypFrame_minus K (by omega) b c).frameHom t,
        frameHom_mem_minusPairPerp ht⟩ =
      (isHypFrame_minus K (n := n - 1) (by omega) b c).frameHom
        (fun l => t (avoid (by omega) k l)) := by
  change projHom (coordinateQuadMinus (n - 1) K (by omega) b c)
      (minusPairPerpEquivOfLe hn hirr k ⟨_, frameHom_mem_minusPairPerp ht⟩) =
    projHom (coordinateQuadMinus (n - 1) K (by omega) b c)
      ⟨frameLin (minusFrameLeft (n := n - 1) (by omega)) (minusFrameRight (n := n - 1) (by omega))
        (fun l => t (avoid (by omega) k l)),
        (isHypFrame_minus K (n := n - 1) (by omega) b c).frameLin_mem_orthDerived _⟩
  congr 1
  exact Subtype.ext (minusPairPerpEquivOfLe_frameHom hn hirr k ht)

variable {G : Type} [Group G] {L : Subgroup G} {r : ℕ} {b c : K}

@[expose] noncomputable def minusPairPerpFieldEquivOfLe (hr : 2 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c))
    (k : Fin (r + 1)) {k₀ : Type} [Field k₀] (φ : K ≃+* k₀) :
    (((minusPairPerp (K := K) (n := r + 2) (by omega) b c k).map e.symm.toMonoidHom).map
        L.subtype : Subgroup G) ≃*
      matrixProjectiveDerived (coordinateQuadMinus (r + 1) k₀ (by omega) (φ b) (φ c)) :=
  (modelToGEquiv e (minusPairPerp (K := K) (n := r + 2) (by omega) b c k)).symm.trans
    ((minusPairPerpModelEquivOfLe (n := r + 2) (by omega) hirr k).trans
      (minusCongr φ (n := r + 1) (by omega) b c))

theorem minusPairPerpFieldEquivOfLe_frameHom (hr : 2 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c))
    (k : Fin (r + 1)) {k₀ : Type} [Field k₀] [Finite k₀] [CharP k₀ 2] (φ : K ≃+* k₀)
    {t : Fin (r + 1) → Kˣ} (ht : t k = 1)
    (hmem : ((e.symm ((isHypFrame_minus K (n := r + 2) (by omega) b c).frameHom t) : L) : G) ∈
      ((minusPairPerp (K := K) (n := r + 2) (by omega) b c k).map e.symm.toMonoidHom).map
        L.subtype) :
    minusPairPerpFieldEquivOfLe hr hirr e k φ ⟨_, hmem⟩ =
      (isHypFrame_minus k₀ (n := r + 1) (by omega) (φ b) (φ c)).frameHom
        (liftParam φ.toRingHom (restrictParam k t)) := by
  have h1 : (modelToGEquiv e (minusPairPerp (K := K) (n := r + 2) _ b c k)).symm
      ⟨_, hmem⟩ = ⟨(isHypFrame_minus K (n := r + 2) _ b c).frameHom t,
        frameHom_mem_minusPairPerp ht⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have h2 := minusPairPerpModelEquivOfLe_frameHom (n := r + 2) (by omega) hirr k ht
  have h2' : minusPairPerpModelEquivOfLe (n := r + 2) (by omega) hirr k
      ⟨(isHypFrame_minus K (n := r + 2) (by omega) b c).frameHom t,
        frameHom_mem_minusPairPerp ht⟩ =
      (isHypFrame_minus K (n := r + 1) (by omega) b c).frameHom (restrictParam k t) := h2
  have h3 := minusCongr_frameHom φ (n := r + 1) (by omega) b c (restrictParam k t)
  calc minusPairPerpFieldEquivOfLe hr hirr e k φ ⟨_, hmem⟩
      = minusCongr φ (n := r + 1) _ b c (minusPairPerpModelEquivOfLe (n := r + 2)
          _ hirr k ((modelToGEquiv e
            (minusPairPerp (K := K) (n := r + 2) _ b c k)).symm ⟨_, hmem⟩)) := rfl
    _ = _ := by rw [h1, h2', h3]

end Perp

section Normalization

open CFSG.LocalAnalysis.ComponentInitial (LinearFlag.projectiveSL LinearFlag.fieldAut
  LinearFlag.dualAut)

@[expose] def MinusNormalizationThreeInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F), orderOf σ = 2 →
    ∀ (k : Subfield F) (hσk : ∀ x, x ∈ k ↔ σ x = x) (b c : k),
      (∀ s : k, s ^ 2 + b * s + c ≠ 0) →
    ∀ (Kc : Type) [Group Kc] (τ : MulAut Kc) (K' : Type) [Field K'] [Finite K'],
      Nat.card K' = Nat.card F →
      ∀ (eK : Kc ≃* LinearFlag.projectiveSL 4 K') (φ : K' ≃+* K'), (∀ x, φ x = x ^ Nat.card k) →
        MulAut.congr eK τ = LinearFlag.fieldAut 4 K' φ * LinearFlag.dualAut 4 K' →
      ∀ (A : Type) [Group A] (ε : A →* Kc), Function.Injective ε → ε.range ≤ fixedSubgroup τ →
      ∀ j : A ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 1) k (by omega) b c),
        ∃ ψ : Kc ≃* matrixProjectiveDerived
            (coordinateQuadMinus (2 + 1) F (by omega) (b : F) (c : F)),
          (∀ a, ψ (ε a) = incl k (isExtension_coordinateQuadMinus k (by omega) b c) (j a)) ∧
          MulAut.congr ψ τ = fieldAutT (coordinateQuadMinus (2 + 1) F (by omega) (b : F) (c : F))
            σ (coordinateQuadMinus_fieldMap_of_fixed (by omega) ((hσk b).1 b.2)
              ((hσk c).1 c.2))

end Normalization

section Cover


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nonempty_minusFieldCover_four_of_normalization (hnorm : MinusNormalizationThreeInput)
    (hset : SeitzSetting G L) (hcat : SUmCatalogueClausesAt 4) {f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hrow : OmegaRowAt t (modelToG e (minusPairTorus (K := K) (n := 2 + 2) (by omega) b c 0))
      (modelToG e (minusPairPerp (K := K) (n := 2 + 2) (by omega) b c 0)) .field)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nonempty (MinusFieldCover (r := 2) e ι 0) := by
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hFK : Nat.card F = Nat.card K ^ 2 := by rw [hF, hKc, ← pow_mul, mul_comm]
  set X := modelToG e (minusPairTorus (K := K) (n := 2 + 2) (by omega) b c 0) with hXdef
  set D := modelToG e (minusPairPerp (K := K) (n := 2 + 2) (by omega) b c 0) with hDdef
  obtain ⟨htX, Kc, hKcomp, hDKK, hiff⟩ := hrow
  have hKt := hiff.1 rfl
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_minusPairTorus_of_seitzSetting_of_four_le (X := X)
    (D := D) hset hKc hq le_rfl hirr 0 e htC ht rfl htX rfl
  obtain ⟨-, -, -, -, -, -, hDC, -, -, -⟩ :=
    neighbour_data_minusPairTorus_of_four_le (X := X) (D := D) hKc hq le_rfl hirr 0 e htC rfl rfl
  have hDK : ⁅(D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Kc⁆ ≠ ⊥ := by
    rw [hKt, sup_idem] at hDKK
    intro hbot
    apply ne_bot_of_isQuasisimple hcomp.2.2
    rw [eq_bot_iff, ← SymplecticPilot.commutator_eq_self_of_isQuasisimple hcomp.2.2, ← hbot]
    exact Subgroup.commutator_mono le_rfl hDKK
  obtain ⟨hsN, -, -, ⟨K', _, _, hK', eK, φ, hφ, hτ⟩, q, hqs, hqker, -, -, ⟨htE, hqt⟩, hDE, hqinj,
    -⟩ := neighbourCore_minusPairTorus_four (X := X) (D := D) hset hcat hKc hq hirr 0 e htC ht rfl
      htX rfl Kc hKcomp hDK hKt
  have hσk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [hfix, RingHom.mem_fieldRange, Set.mem_range]
  have : CharP ι.fieldRange 2 := RingHom.charP ι.fieldRange.subtype Subtype.val_injective 2
  have hirr₀ : ∀ s : ι.fieldRange, s ^ 2 + ι.rangeRestrictFieldEquiv b * s +
      ι.rangeRestrictFieldEquiv c ≠ 0 := by
    intro s hs
    apply hirr (ι.rangeRestrictFieldEquiv.symm s)
    apply ι.rangeRestrictFieldEquiv.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs
  have hk₀ : Nat.card ι.fieldRange = 2 ^ f :=
    (Nat.card_congr ι.rangeRestrictFieldEquiv.toEquiv).symm.trans hKc
  have hφk : ∀ x, φ x = x ^ Nat.card ι.fieldRange := fun x => by rw [hk₀]; exact hφ x
  have hεfix : (q.comp (Subgroup.inclusion hDE)).range ≤
      fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩) := by
    rintro _ ⟨d, rfl⟩
    change Kc.normalizerMonoidHom ⟨_, hsN⟩ (q (Subgroup.inclusion hDE d)) =
      q (Subgroup.inclusion hDE d)
    rw [← hqt]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change t * (d : G) * t⁻¹ = d
    rw [mem_centralizer_iff.1 (hDC d.2).2 t (Set.mem_singleton t), mul_inv_cancel_right]
  obtain ⟨ψ, hψ, -⟩ := hnorm F σ hσ ι.fieldRange hσk (ι.rangeRestrictFieldEquiv b)
    (ι.rangeRestrictFieldEquiv c) hirr₀ Kc (Kc.normalizerMonoidHom ⟨_, hsN⟩) K'
    (hK'.trans hF.symm) eK φ hφk hτ _ (q.comp (Subgroup.inclusion hDE)) hqinj hεfix
    (minusPairPerpFieldEquivOfLe (r := 2) le_rfl hirr e 0 ι.rangeRestrictFieldEquiv)
  have hφb : ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F) = ι b :=
    RingHom.rangeRestrictFieldEquiv_apply_coe ι b
  have hφc : ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F) = ι c :=
    RingHom.rangeRestrictFieldEquiv_apply_coe ι c
  obtain ⟨α, hα⟩ := exists_root_of_card_eq_sq ι hFK hirr
  have hαF : α ^ 2 + ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F) * α +
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F) = 0 := by
    rw [hφb, hφc]
    exact hα
  have hβ0 : ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F) ≠ 0 := by
    rw [hφb]
    exact (map_ne_zero ι).2 (coeff_ne_zero_of_irreducible hirr)
  have hαα := root_ne_other_of_ne_zero (α := α) hβ0
  let π0 := (minusPlusBridge (r := 2) (by omega) hαF hαα).toMonoidHom.comp (ψ.toMonoidHom.comp q)
  have hs0 : Function.Surjective π0 :=
    (minusPlusBridge (r := 2) (by omega) hαF hαα).surjective.comp (ψ.surjective.comp hqs)
  have hk0 : π0.ker ≤ center (minusNeighbourCore e 0) := by
    intro x hx
    have hx' : ψ (q x) = 1 := by
      have h1 := MonoidHom.mem_ker.1 hx
      simp only [π0, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
      exact (MulEquiv.map_eq_one_iff _).1 h1
    have h2 : x ∈ q.ker := MonoidHom.mem_ker.2 ((MulEquiv.map_eq_one_iff ψ).1 hx')
    rw [hqker] at h2
    exact h2
  have hD0 : modelToG e (minusPairPerp (K := K) (n := 2 + 2) (by omega) b c 0) ≤
      minusNeighbourCore e 0 := hDE
  have hn0 : ∀ t' : Fin (2 + 1) → Kˣ, t' 0 = 1 →
      ∀ hmem : ((e.symm ((isHypFrame_minus K (n := 2 + 2) (by omega) b c).frameHom t') : L) :
        G) ∈ minusNeighbourCore e 0,
        ((π0 ⟨_, hmem⟩ : StatedOmega (StatedQuadPlus (2 + 1) F)) :
          GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) = minusNeighbourDiag ι 0 t' := by
    intro t' ht' hmem
    have hgD := symm_mem_modelToG e (frameHom_mem_minusPairPerp (n := 2 + 2) ht')
    have hjf := minusPairPerpFieldEquivOfLe_frameHom (r := 2) le_rfl hirr e 0
      ι.rangeRestrictFieldEquiv ht' hgD
    have hinc := incl_frameHom_minus ι.fieldRange (n := 2 + 1) (by omega)
      (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c)
      (liftParam ι.rangeRestrictFieldEquiv.toRingHom (restrictParam 0 t'))
    have hbr := minusPlusBridge_frameHom (r := 2) (by omega) hαF hαα
      (liftParam ι.fieldRange.subtype
        (liftParam ι.rangeRestrictFieldEquiv.toRingHom (restrictParam 0 t')))
    have hw : liftParam ι.fieldRange.subtype
        (liftParam ι.rangeRestrictFieldEquiv.toRingHom (restrictParam 0 t')) =
        liftParam ι (restrictParam 0 t') := by
      funext l
      apply Units.ext
      simp [liftParam]
    change (((minusPlusBridge (r := 2) (by omega) hαF hαα)
      (ψ ((q.comp (Subgroup.inclusion hDE)) ⟨_, hgD⟩)) :
        StatedOmega (StatedQuadPlus (2 + 1) F)) : GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) = _
    rw [hψ]
    erw [hjf]
    rw [hinc, hbr, hw, minusNeighbourDiag_apply]
  exact ⟨MinusFieldCover.ofNormalized (e := e) (ι := ι) (k := 0) π0 hs0 hk0 hD0 hn0⟩

theorem omegaMinusFourCoverInput_of_normalization (hnorm : MinusNormalizationThreeInput)
    (hcat : SUmCatalogueClausesAt 4) : OmegaMinusFourCoverInput := by
  intro G _ _ L hset f K _ _ _ b c hirr hKc hf2 e t ht hKt hrow F _ _ _ ι σ hσ hfix
  exact nonempty_minusFieldCover_four_of_normalization hnorm hset hcat hKc
    ((LinearPilot.four_le_card_iff_two_le hKc).2 hf2) hirr e
    (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) ht (hrow 0) ι hσ hfix

end Cover

end CFSG.SeitzReduction.OmegaPilot
