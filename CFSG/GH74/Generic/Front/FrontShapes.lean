module

public import CFSG.GH74.Generic.Front.B5
public import CFSG.GH74.Generic.Front.Sch
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint Subgroup

theorem normal_of_layer_eq {X : Type*} [Group X] {K : Subgroup X} (h : layer X = K) :
    K.Normal := by
  rw [← h, CFSG.layer_eq_componentClassification]
  exact CFSG.ComponentClassification.Layer.normal X

variable {G : Type} [Group G] [Finite G]

theorem b5_of_shapeModel (hD : FrontDataStatement) (hO : OuterStatement) (hgen : Gen4 G) {x : G}
    (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K)
    (hmodel : ShapeModel ↥K) : NoNoncentralInvolutionConj x K := by
  obtain ⟨D⟩ := hD ↥K hmodel
  have hfr : Q8Frame ↥K := ⟨D.φ, D.inj, D.w, D.w_sq, D.w_swap⟩
  obtain ⟨hxK, hlayer, hcentK, -, -, -⟩ := frame_B2 hgen hx hKc hfr
  have hKn : K.Normal := normal_of_layer_eq hlayer
  have hcentle : Subgroup.centralizer (K : Set (CentralizerBar x)) ≤ K := by
    rw [hcentK]
    exact (Subgroup.zpowers_le).2 hxK
  exact noNoncentralInvolutionConj_of_data hgen hx hKc D
    (goodSub_le_of_outerStatement hO K hmodel hcentle)

theorem generic_front_end_full (hD : FrontDataStatement) (hO : OuterStatement)
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) {x : G}
    (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K)
    (hmodel : ShapeModel ↥K) :
    xbar x ∈ K ∧ layer (CentralizerBar x) = K ∧
      centralizer (K : Set (CentralizerBar x)) = Subgroup.zpowers (xbar x) ∧
      pCore 2 (CentralizerBar x) = Subgroup.zpowers (xbar x) ∧
      fittingSubgroup (CentralizerBar x) = Subgroup.zpowers (xbar x) ∧
      generalizedFitting (CentralizerBar x) = K ∧
      IsCentralInvolution x ∧
      (∃ T : Sylow 2 G, x ∈ (T : Subgroup G) ∧ (∀ t ∈ (T : Subgroup G), t * x = x * t) ∧
        ∀ c ∈ (T : Subgroup G), (∀ t ∈ (T : Subgroup G), t * c = c * t) →
          c ∈ Subgroup.zpowers x) ∧
      NoNoncentralInvolutionConj x K ∧
      ∃ (v : G) (hv : v ∈ centralizer ({x} : Set G)), IsConj x v ∧ v ≠ x ∧ v * v = 1 ∧
        barOf hv ≠ 1 ∧ barOf hv ≠ xbar x ∧ barOf hv ∉ K := by
  have hB5 := b5_of_shapeModel hD hO hgen hx hKc hmodel
  obtain ⟨D⟩ := hD ↥K hmodel
  have hfr : Q8Frame ↥K := ⟨D.φ, D.inj, D.w, D.w_sq, D.w_swap⟩
  obtain ⟨hxK, hl, hc, hp, hf, hfs⟩ := frame_B2 hgen hx hKc hfr
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer ({x} : Set G))) := inferInstance
  obtain ⟨T, -, hxT, hcomm, hZ⟩ := frame_sylow_centralizer_isSylow hgen hx hfr S
  exact ⟨hxK, hl, hc, hp, hf, hfs, frame_isCentralInvolution hgen hx hfr, ⟨T, hxT, hcomm, hZ⟩, hB5,
    exists_outer_involution hs hn hgen hx hfr hB5⟩

end CFSG.GH74.Generic
