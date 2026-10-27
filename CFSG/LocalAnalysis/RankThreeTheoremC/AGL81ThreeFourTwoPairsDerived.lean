module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.CentralAlphaOut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open Subgroup

variable {Y : Type} [Group Y]

theorem threeFourTwo_range_subgroupOf (K Y₀ : Subgroup Y) :
    (K.subtype.comp (Y₀.subgroupOf K).subtype).range = K ⊓ Y₀ := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem threeFourTwo_false_of_solvable {K Y₀ J : Subgroup Y}
    (hsol : Group.IsSolvable (Y₀.subgroupOf K)) (hJ : J ≤ K ⊓ Y₀) (hJp : ⁅J, J⁆ = J)
    (hJ1 : J ≠ ⊥) : False := by
  set φ : (Y₀.subgroupOf K) →* Y := K.subtype.comp (Y₀.subgroupOf K).subtype with hφ
  have hsol' : Group.IsSolvable φ.range := Group.isSolvable_of_surjective φ.rangeRestrict_surjective
  rw [threeFourTwo_range_subgroupOf] at hsol'
  haveI : Group.IsSolvable J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJ)
  haveI : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJp
  haveI : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJ1
  exact Group.IsPerfect.not_isSolvable J inferInstance

theorem threeFourTwo_equiv_commutator {K Y₀ J : Subgroup Y}
    (hsimp : IsSimpleGroup (commutator (Y₀.subgroupOf K))) (hJ : J ≤ K ⊓ Y₀)
    (hJs : IsSubnormal J (K ⊓ Y₀)) (hJp : ⁅J, J⁆ = J) (hJ1 : J ≠ ⊥) :
    Nonempty (J ≃* commutator (Y₀.subgroupOf K)) := by
  set φ : (Y₀.subgroupOf K) →* Y := K.subtype.comp (Y₀.subgroupOf K).subtype with hφdef
  have hφ : Function.Injective φ := K.subtype_injective.comp (Y₀.subgroupOf K).subtype_injective
  set D := (commutator (Y₀.subgroupOf K)).map φ with hD
  have hDeq : D = ⁅K ⊓ Y₀, K ⊓ Y₀⁆ := by
    rw [hD, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
      threeFourTwo_range_subgroupOf]
  have hDle : D ≤ K ⊓ Y₀ := by
    rw [← threeFourTwo_range_subgroupOf K Y₀, MonoidHom.range_eq_map]
    exact Subgroup.map_mono le_top
  have hJD : J ≤ D := by
    rw [hDeq, ← hJp]
    exact Subgroup.commutator_mono hJ hJ
  have hJsD : IsSubnormal J D := by
    have h1 := hJs.inf_of_le hDle
    rwa [inf_eq_left.2 hJD] at h1
  let eD := (commutator (Y₀.subgroupOf K)).equivMapOfInjective φ hφ
  have hDs : IsSimpleGroup D := MulEquiv.isSimpleGroup eD.symm
  have hJeq : J = D := (hJsD.eq_bot_or_eq_of_isSimpleGroup hDs).resolve_left hJ1
  exact ⟨(MulEquiv.subgroupCongr hJeq).trans eD.symm⟩

variable [Finite Y]

theorem threeFourTwo_not_dvd_index {p : ℕ} [Fact p.Prime] {K Y₀ : Subgroup Y} [K.Normal]
    (R : Sylow p Y) (hRY : (R : Subgroup Y) ≤ Y₀) : ¬ p ∣ (Y₀.subgroupOf K).index := by
  intro h
  apply CFSG.AGLEmbedding.not_dvd_relIndex_sylow_of_normal R K
  show p ∣ ((R : Subgroup Y).subgroupOf K).index
  exact h.trans (Subgroup.index_dvd_of_le fun x hx => hRY hx)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

end
