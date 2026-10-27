module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullFixedSet
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorNativeRootLift
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedCentralizer

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.BenderSuzuki.PFAppendixIII CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull

universe u

variable {G : Type u} [Group G]

theorem originalPointRoot_conj {H : Subgroup G} (z w : G) {g : G} (hg : g ∈ H) :
    (originalPointRoot H z w).map (MulAut.conj g⁻¹).toMonoidHom =
      originalPointRoot H z (g⁻¹ * w * g) := by
  have hφ : ∀ y, (MulAut.conj g⁻¹).toMonoidHom y = g⁻¹ * y * g := fun y => by
    simp
  rw [originalPointRoot, originalPointRoot, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨⟨⟨c, rfl⟩, hxw⟩, hxH⟩, rfl⟩
    rw [hφ]
    refine ⟨⟨⟨c * g, ?_⟩, ?_⟩, H.mul_mem (H.mul_mem (H.inv_mem hg) hxH) hg⟩
    · simp only [rightConjugateElem]
      group
    · have hcomm : Commute (rightConjugateElem z c) w :=
        Subgroup.mem_centralizer_singleton_iff.mp hxw
      have := hcomm.map (MulAut.conj g⁻¹).toMonoidHom
      rw [hφ, hφ] at this
      exact Subgroup.mem_centralizer_singleton_iff.mpr this
  · rintro ⟨⟨⟨c, rfl⟩, hyw⟩, hyH⟩
    refine ⟨g * rightConjugateElem z c * g⁻¹, ⟨⟨⟨c * g⁻¹, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [rightConjugateElem]
      group
    · have hcomm : Commute (rightConjugateElem z c) (g⁻¹ * w * g) :=
        Subgroup.mem_centralizer_singleton_iff.mp hyw
      have := hcomm.map (MulAut.conj g).toMonoidHom
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hw : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
      rw [hw] at this
      exact this
    · exact H.mul_mem (H.mul_mem hg hyH) (H.inv_mem hg)
    · rw [hφ]
      group

theorem card_originalPointRoot_conj {H : Subgroup G} (z w : G) {g : G} (hg : g ∈ H) :
    Nat.card (originalPointRoot H z (g⁻¹ * w * g)) = Nat.card (originalPointRoot H z w) := by
  rw [← originalPointRoot_conj z w hg]
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem not_centralizer_le_conj {H : Subgroup G} {w g : G} (hg : g ∈ H)
    (hescape : ¬ Subgroup.centralizer ({w} : Set G) ≤ H) :
    ¬ Subgroup.centralizer ({g⁻¹ * w * g} : Set G) ≤ H := by
  intro hle
  apply hescape
  intro c hc
  have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer ({g⁻¹ * w * g} : Set G) := by
    have hcomm : Commute c w := Subgroup.mem_centralizer_singleton_iff.mp hc
    have := hcomm.map (MulAut.conj g⁻¹).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
    exact Subgroup.mem_centralizer_singleton_iff.mpr this
  have := H.mul_mem (H.mul_mem hg (hle hc')) (H.inv_mem hg)
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using this

theorem mem_pairPointStabilizer_conj {H : Subgroup G} (beta : rightCosetSpace H) {g : G}
    (hg : g ∈ H) (x : G) :
    x ∈ pairPointStabilizer H beta ↔
      g⁻¹ * x * g ∈ pairPointStabilizer H (rightCosetTranslate H beta g) := by
  have hbase : ∀ y : G, y ∈ rightCosetStabilizer H (rightCosetMk H 1) ↔ y ∈ H := fun y => by
    rw [rightCosetStabilizer_base]
  have hβ : ∀ y : G, y ∈ rightCosetStabilizer H beta ↔
      g⁻¹ * y * g ∈ rightCosetStabilizer H (rightCosetTranslate H beta g) := by
    intro y
    rw [mem_rightCosetStabilizer_iff, mem_rightCosetStabilizer_iff, rightCosetTranslate_mul,
      show g * (g⁻¹ * y * g) = y * g by group, ← rightCosetTranslate_mul]
    constructor
    · intro hy
      rw [hy]
    · intro hy
      have := congrArg (fun ω => rightCosetTranslate H ω g⁻¹) hy
      simpa only [rightCosetTranslate_mul, mul_inv_cancel, mul_one, mul_inv_cancel_right,
        rightCosetTranslate_one] using this
  constructor
  · rintro ⟨hxα, hxβ⟩
    exact ⟨(hbase _).mpr (H.mul_mem (H.mul_mem (H.inv_mem hg) ((hbase x).mp hxα)) hg),
      (hβ x).mp hxβ⟩
  · rintro ⟨hxα, hxβ⟩
    refine ⟨(hbase x).mpr ?_, (hβ x).mpr hxβ⟩
    have := H.mul_mem (H.mul_mem hg ((hbase _).mp hxα)) (H.inv_mem hg)
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using this

variable [Finite G]

theorem exists_point_conj_of_mem_class {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) {u v : G} (huH : u ∈ H) (hu : orderOf u = 2)
    (hvH : v ∈ H) (hv : v ∈ involutionPointClass u) :
    ∃ g ∈ H, g⁻¹ * u * g = v := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hSH : (S : Subgroup G) ≤ H := by
    intro s hs
    apply point_centralizer_le h.local_datum
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzcenter) ⟨s, hs⟩)
  have hfusion := (unique_central_sylow_involution_centralizers_transitive_fixed_set S H hSH z
    hzS hzcenter h.local_datum.distinguished_order h.local_datum.unique_containment u huH
    hu).2.2
  have hvH' : v ∈ involutionPointClass u ∩ (H : Set G) := ⟨hv, hvH⟩
  rw [hfusion] at hvH'
  obtain ⟨g, hg⟩ := hvH'
  exact ⟨g, g.2, hg⟩

theorem twoRank_pairPointStabilizer_conj {H : Subgroup G} (beta : rightCosetSpace H) {g : G}
    (hg : g ∈ H) :
    twoRank (pairPointStabilizer H (rightCosetTranslate H beta g)) =
      twoRank (pairPointStabilizer H beta) := by
  let φ : pairPointStabilizer H beta →* pairPointStabilizer H (rightCosetTranslate H beta g) :=
    ((MulAut.conj g⁻¹).toMonoidHom.domRestrict (pairPointStabilizer H beta)).codRestrict
      (pairPointStabilizer H (rightCosetTranslate H beta g)) fun x => by
        have := (mem_pairPointStabilizer_conj beta hg x).mp x.2
        simpa using this
  let ψ : pairPointStabilizer H (rightCosetTranslate H beta g) →* pairPointStabilizer H beta :=
    ((MulAut.conj g).toMonoidHom.domRestrict
      (pairPointStabilizer H (rightCosetTranslate H beta g))).codRestrict
      (pairPointStabilizer H beta) fun y => by
        have : g * (y : G) * g⁻¹ ∈ pairPointStabilizer H beta :=
          (mem_pairPointStabilizer_conj beta hg _).mpr (by
            rw [show g⁻¹ * (g * (y : G) * g⁻¹) * g = y by group]
            exact y.2)
        simpa using this
  have hφ : Function.Injective φ := fun x y hxy => by
    have := congrArg Subtype.val hxy
    simp only [φ, MonoidHom.codRestrict_apply, MonoidHom.domRestrict_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hψ : Function.Injective ψ := fun x y hxy => by
    have := congrArg Subtype.val hxy
    simp only [ψ, MonoidHom.codRestrict_apply, MonoidHom.domRestrict_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  exact le_antisymm (CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_injective ψ hψ)
    (CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_injective φ hφ)

theorem point_conj_partner_pair {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    {u v : G} (huE : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hvH : v ∈ H) (hv : v ∈ involutionPointClass u) :
    ∃ beta' : pointRightCosetSpace H, beta' ≠ rightCosetMk H 1 ∧
      twoRank (pairPointStabilizer H beta') = 1 ∧ v ∈ pairPointStabilizer H beta' ∧
      ¬ Subgroup.centralizer ({v} : Set G) ≤ H ∧
      Nat.card (elementFixedSet H v) = Nat.card (elementFixedSet H u) ∧
      Nat.card (originalPointRoot H z v) = Nat.card (originalPointRoot H z u) := by
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huE
  obtain ⟨g, hgH, rfl⟩ := exists_point_conj_of_mem_class h huH hu hvH hv
  refine ⟨rightCosetTranslate H beta g, ?_, ?_, (mem_pairPointStabilizer_conj beta hgH u).mp huE,
    not_centralizer_le_conj hgH hescape, ?_, card_originalPointRoot_conj z u hgH⟩
  · intro hβ
    apply hbeta
    have := congrArg (fun ω => rightCosetTranslate H ω g⁻¹) hβ
    simp only [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one] at this
    rw [this, rightCosetTranslate_mk, one_mul]
    exact Quotient.sound (by
      change QuotientGroup.rightRel H g⁻¹ 1
      rw [QuotientGroup.rightRel_apply, one_mul]
      exact H.inv_mem (H.inv_mem hgH))
  · rw [twoRank_pairPointStabilizer_conj beta hgH, hpairRank]
  · exact conjugate_elementFixedSet_card H u g

end CFSG.ProperTwoGeneratedCore.RankOnePair
