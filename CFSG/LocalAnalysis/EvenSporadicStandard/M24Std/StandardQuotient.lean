module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.StandardCentralizer
public import CFSG.Open.FusionDefs
import CFSG.LocalAnalysis.SeitzReduction.Inheritance
import CFSG.Walter.Cited.OddQuotient
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCoreQuotient

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

theorem odd_natCard_fusionOddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) :=
  DisconnectedInvolutionGraph.Helpers.oddCore_odd

theorem standardComponentOddCore_quotient_fusionOddCore_eq_bot (X : Type*) [Group X] [Finite X] :
    standardComponentOddCore (X ⧸ fusionOddCore X) = ⊥ := by
  have h := @DisconnectedInvolutionGraph.Helpers.oddCore_quotient_eq_bot X _ _
  exact h

theorem disjoint_fusionOddCore {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hHq : CFSG.Open.IsQuasisimple H) (hZ : center H = ⊥) : Disjoint H (fusionOddCore X) := by
  rw [disjoint_def]
  intro x hxH hxO
  have hmem : (⟨x, hxH⟩ : H) ∈ (CFSG.oddCore X).subgroupOf H := mem_subgroupOf.2 hxO
  have h := SeitzReduction.oddCore_subgroupOf_le_center hHq hmem
  rw [hZ, mem_bot] at h
  exact congrArg Subtype.val h

theorem nonempty_map_fusionOddCore_mulEquiv {X : Type*} [Group X] {H : Subgroup X}
    (hd : Disjoint H (fusionOddCore X)) :
    Nonempty (H.map (QuotientGroup.mk' (fusionOddCore X)) ≃* H) := by
  set π := QuotientGroup.mk' (fusionOddCore X) with hπ
  have hinj : Function.Injective (π.subgroupMap H) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : π (x : X) = 1 := congrArg Subtype.val hx
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subtype.ext ((disjoint_def.1 hd) x.2 h1)
  exact ⟨(MulEquiv.ofBijective (π.subgroupMap H) ⟨hinj, π.subgroupMap_surjective H⟩).symm⟩

theorem centralizer_mk_fusionOddCore_eq {X : Type*} [Group X] [Finite X] {z : X}
    {H : Subgroup X} (hz : orderOf z = 2) (hC : centralizer ({z} : Set X) = H ⊔ zpowers z)
    (hz' : z ∈ centralizer (H : Set X)) :
    centralizer ({QuotientGroup.mk' (fusionOddCore X) z} : Set (X ⧸ fusionOddCore X)) =
      H.map (QuotientGroup.mk' (fusionOddCore X)) ⊔
        zpowers (QuotientGroup.mk' (fusionOddCore X) z) := by
  have htt : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  apply le_antisymm
  · have h := CFSG.Walter.Suzuki.centralizer_mk_le_map (fusionOddCore X)
      (odd_natCard_fusionOddCore X) htt
    rw [hC, Subgroup.map_sup, MonoidHom.map_zpowers] at h
    exact h
  · refine sup_le ?_ (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
    rintro _ ⟨h, hh, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 (SeitzReduction.le_centralizer_of_mem_centralizer hz' hh)]

theorem standardQuotient_of_normal {X : Type*} [Group X] [Finite X] {z : X} {H : Subgroup X}
    (hz : orderOf z = 2) (hH : IsSimpleGroup H) (hnab : ∃ a b : H, a * b ≠ b * a)
    (hHt : H ≤ centralizer ({z} : Set X))
    (hHn : (H.subgroupOf (centralizer ({z} : Set X))).Normal)
    (hsyl : ∀ U : Subgroup X, IsPGroup 2 U →
      U ≤ centralizer ({z} : Set X) ⊓ centralizer (H : Set X) → Nat.card U ≤ 2) :
    standardComponentOddCore (X ⧸ fusionOddCore X) = ⊥ ∧
      standardComponentIsStandard (H.map (QuotientGroup.mk' (fusionOddCore X))) ∧
      (∃ S : Sylow 2 (centralizer
        (H.map (QuotientGroup.mk' (fusionOddCore X)) : Set (X ⧸ fusionOddCore X))),
        IsCyclic S) ∧
      Disjoint H (fusionOddCore X) ∧
      Nonempty (H.map (QuotientGroup.mk' (fusionOddCore X)) ≃* H) := by
  obtain ⟨hHq, hZ⟩ := isQuasisimple_center_eq_bot_of_isSimpleGroup hnab
  have hstd : standardComponentIsStandard (H.map (QuotientGroup.mk' (fusionOddCore X))) :=
    SeitzReduction.standardComponentIsStandard_map_oddCore hz hHt hHn hHq hsyl
  have hK2 : ∀ U : Subgroup (X ⧸ fusionOddCore X), IsPGroup 2 U →
      U ≤ centralizer (H.map (QuotientGroup.mk' (fusionOddCore X)) :
        Set (X ⧸ fusionOddCore X)) → Nat.card U ≤ 2 :=
    fun U hU hUD =>
      SeitzReduction.card_le_two_of_le_centralizer_map_oddCore hz hHt hHn hHq hsyl hU hUD
  have hd := disjoint_fusionOddCore hHq hZ
  exact ⟨standardComponentOddCore_quotient_fusionOddCore_eq_bot X, hstd,
    exists_isCyclic_sylow_of_card_le_two hK2, hd, nonempty_map_fusionOddCore_mulEquiv hd⟩

theorem standardQuotient_of_centralizer_eq {X : Type*} [Group X] [Finite X] {z : X}
    {H : Subgroup X} (hz : orderOf z = 2) (hH : IsSimpleGroup H)
    (hnab : ∃ a b : H, a * b ≠ b * a) (hC : centralizer ({z} : Set X) = H ⊔ zpowers z)
    (hz' : z ∈ centralizer (H : Set X)) :
    standardComponentOddCore (X ⧸ fusionOddCore X) = ⊥ ∧
      standardComponentIsStandard (H.map (QuotientGroup.mk' (fusionOddCore X))) ∧
      (∃ S : Sylow 2 (centralizer
        (H.map (QuotientGroup.mk' (fusionOddCore X)) : Set (X ⧸ fusionOddCore X))),
        IsCyclic S) ∧
      Disjoint H (fusionOddCore X) ∧
      Nonempty (H.map (QuotientGroup.mk' (fusionOddCore X)) ≃* H) ∧
      centralizer ({QuotientGroup.mk' (fusionOddCore X) z} : Set (X ⧸ fusionOddCore X)) =
        H.map (QuotientGroup.mk' (fusionOddCore X)) ⊔
          zpowers (QuotientGroup.mk' (fusionOddCore X) z) := by
  obtain ⟨-, hZ⟩ := isQuasisimple_center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨h1, h2, h3, h4, h5⟩ := standardQuotient_of_normal hz hH hnab
    (SeitzReduction.le_centralizer_of_mem_centralizer hz')
    (subgroupOf_normal_of_centralizer_eq hC hz')
    (fun U hU hUle => card_le_two_of_centralizer_eq hz hZ hC hz' U hU (hUle.trans inf_le_right))
  exact ⟨h1, h2, h3, h4, h5, centralizer_mk_fusionOddCore_eq hz hC hz'⟩

end CFSG.EvenSporadicStandard.M24Std
