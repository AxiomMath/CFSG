module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecM11
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuCase
public import CFSG.GH74.Generic.S45.LSporMathB
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamSpor
public import CFSG.Walter.J1Props.Facts
public import CFSG.Walter.Models
public import CFSG.Sporadic.SmallOddCore.J2Local
public import CFSG.Sporadic.Schreier.PairJ3Faithful
public import CFSG.Sporadic.Schreier.J4SNoComp
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.BkIvk73Q
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Kill
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Ly
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.KFacts
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGEven
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndB
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSmall
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.Sporadic.Schreier (centralizerIn)

theorem endKnownGroupsInputOn_M11
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .M11) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  refine false_of_card_centralizer_lt hK hKs hKt hD hDd hD8 ?_
  have e' : X ≃* NativeSporadic.M11 := e
  have hord : orderOf ((e' z : NativeSporadic.M11) : Equiv.Perm (Fin 11)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hK.1]
  rw [GH74.GLS.IVK.GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M11 e' z,
    Sp4Rec.m11_card_centralizerIn _ (e' z).2 hord]
  norm_num

theorem endKnownGroupsInputOn_M12
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .M12) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  refine false_of_card_centralizer_lt hK hKs hKt hD hDd hD8 ?_
  have e' : X ≃* NativeSporadic.M12 := e
  have hord : orderOf ((e' z : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hK.1]
  rw [GH74.GLS.IVK.GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M12 e' z]
  rcases GH74.GLS.m12_inv_centralizer_card _ (e' z).2 hord with h | h <;> rw [h] <;> norm_num

theorem endKnownGroupsInputOn_M22
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .M22) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  refine false_of_card_centralizer_lt hK hKs hKt hD hDd hD8 ?_
  have e' : X ≃* NativeSporadic.M22 := e
  have hord : orderOf ((e' z : NativeSporadic.M22) : Equiv.Perm (Fin 22)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hK.1]
  rw [GH74.GLS.IVK.GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M22 e' z,
    GH74.Generic.S45.LSporB.m22_inner_centralizer_card _ (e' z).2 hord]
  norm_num

theorem endKnownGroupsInputOn_M23
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .M23) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  exact false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_M23
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    ((RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
      RestrictedStd.Spor.isoInvariant_not_three_dvd RestrictedStd.Spor.m23_centralizerIn_comps e z
      hK.1).mono fun Y _ h => RestrictedStd.Spor.not_small_of_not_three h)

theorem endKnownGroupsInputOn_M24
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .M24) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  exact false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_M24
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    ((RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
      RestrictedStd.Spor.isoInvariant_not_three_dvd RestrictedStd.Spor.m24_centralizerIn_comps e z
      hK.1).mono fun Y _ h => RestrictedStd.Spor.not_small_of_not_three h)

theorem endKnownGroupsInputOn_J1
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .J1) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  refine false_of_card_centralizer_lt hK hKs hKt hD hDd hD8 ?_
  let ψ : X ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  have h := CFSG.Walter.J1Props.card_centralizer_of_orderOf_eq_two (x := ψ z)
    (by rw [MulEquiv.orderOf_eq, hK.1])
  rw [← Nat.card_congr (RestrictedStd.Spor.centralizerEquiv ψ z).toEquiv] at h
  rw [h]
  norm_num

theorem endKnownGroupsInputOn_J2
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .J2) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  have hcore := oddCore_centralizer_eq_bot_of_sporadicOddCoreFree
    CatalogueU.sporadicOddCoreFree_J2 (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1
  have hKc : Assembly.IsComponentOf K (centralizer ({z} : Set X)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hK.2.1).2
      (isComponent_of_oddCore hK hcore).1
  have h12 :=
    Sporadic.SmallOddCore.cti_j2_involution_local_components_ambient_centralizer_order_twelve
      ⟨e⟩ hK.1 hKc
  exact false_of_le_of_not_eight_dvd hK hcore hD hDd hD8 inf_le_right (by rw [h12]; decide)

theorem endKnownGroupsInputOn_J3
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .J3) := by
  intro X _ _ hXs ⟨e⟩ z t K P D hK _ _ _ _ _ _ ht hzt _ _ _ _ _ _ _ hsolv
  by_cases h1 : z * t = 1
  ·
    obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_of_isTwoComponentAt hK
    have htop : centralizer ({z * t} : Set X) = ⊤ := by
      rw [h1]
      exact eq_top_iff.mpr fun g _ => mem_centralizer_singleton_iff.mpr (by group)
    have : Group.IsSolvable X := by
      rw [htop] at hsolv
      exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup X).subtype)
        fun g => ⟨⟨g, mem_top g⟩, rfl⟩
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr this) a b)
  have hx2 : orderOf (z * t) = 2 := by
    refine orderOf_eq_prime ?_ h1
    have hz2 : z ^ 2 = 1 := by rw [← hK.1, pow_orderOf_eq_one]
    have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
    rw [(show Commute z t from hzt).mul_pow, hz2, ht2, mul_one]
  let ψ : X ≃* Sporadic.Schreier.j3P := e.trans Sporadic.Schreier.j3PermEquiv
  let E : ↥(centralizer ({z * t} : Set X)) ≃* ↥(centralizerIn Sporadic.Schreier.j3P
      ((ψ (z * t) : Sporadic.Schreier.j3P) : Equiv.Perm (Fin 6156))) :=
    (RestrictedStd.Spor.centralizerEquiv ψ (z * t)).trans
      (RestrictedStd.Spor.centralizerSubtypeEquiv _ (ψ (z * t)))
  obtain ⟨hperf, hcard⟩ := GH74.GLS.IVK.j3_inner_centralizer_data _ (ψ (z * t)).2
    (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx2])
  have : Group.IsPerfect ↥(centralizerIn Sporadic.Schreier.j3P
      ((ψ (z * t) : Sporadic.Schreier.j3P) : Equiv.Perm (Fin 6156))) :=
    Subgroup.isPerfect_iff.mpr hperf
  have : Nontrivial ↥(centralizerIn Sporadic.Schreier.j3P
      ((ψ (z * t) : Sporadic.Schreier.j3P) : Equiv.Perm (Fin 6156))) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  exact Group.IsPerfect.not_isSolvable _ (Group.isSolvable_of_surjective (f := E.toMonoidHom)
    E.surjective)

theorem endKnownGroupsInputOn_J4
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .J4) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  exact false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_J4
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    fun B hB => absurd hB (RestrictedStd.Spor.j4NoComponentsInput X ⟨e⟩ z hK.1 B)

end CFSG.ComponentClassification.Foote5
