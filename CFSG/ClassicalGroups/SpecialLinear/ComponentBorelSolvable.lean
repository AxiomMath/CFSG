module

public import CFSG.ClassicalGroups.SpecialLinear.QuasisimpleCoverUncond
public import CFSG.ClassicalGroups.SpecialLinear.QuasisimpleCartanRank
public import CFSG.LieType.SteinbergBRTriangularSolvable
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.GroupTheory.SylowTwoOfConj

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix

theorem isSolvable_normalizer_sylow_of_component
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : Nat) (hm : 1 <= m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.A m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.A m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hne : ¬ (m = 2 ∧ Q.card = 4))
    {U : Subgroup L} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    Group.IsSolvable ↥(Subgroup.normalizer (U : Set L)) := by
  classical
  obtain ⟨F, hFld, hFfin, hFchar, π, hFcard, hπsurj, hker⟩ :=
    exists_central_cover_specialLinear_of_ne_two_four hL m hm Q hQ hv e hne
  letI : Field F := hFld
  letI : Finite F := hFfin
  letI : CharP F 2 := hFchar
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SL := Matrix.SpecialLinearGroup (Fin (m + 1)) F
  let Z : Subgroup SL := π.ker
  let W : Subgroup SL := U.comap π
  let U0 : Subgroup SL :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular (m + 1) F
  have hU2 : IsPGroup 2 U := hU.2.1
  have hZcenter : Z ≤ Subgroup.center SL := hker
  have hoddF : Odd (Nat.card F - 1) := odd_card_sub_one_of_char_two
  have hcenter_dvd : Nat.card (Subgroup.center SL) ∣ Nat.card F - 1 := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_scalars_dvd
      (n := m + 1) (K := F) (by omega)
  have hZodd : Odd (Nat.card Z) :=
    Odd.of_dvd_nat hoddF ((Subgroup.card_dvd_of_le hZcenter).trans hcenter_dvd)
  have hC : ¬ 2 ∣ Nat.card Z := hZodd.not_two_dvd_nat
  let Uhat : Subgroup SL := CFSG.LieType.CentralExt.liftSubgroup 2 π U
  have hUhat2 : IsPGroup 2 Uhat :=
    CFSG.LieType.CentralExt.liftSubgroup_isPGroup hZcenter hU2
  have hUhatleW : Uhat ≤ W :=
    CFSG.LieType.CentralExt.liftSubgroup_le_comap hZcenter hU2
  have hZleW : Z ≤ W := by
    intro z hz
    rw [Subgroup.mem_comap]
    have hz1 : π z = 1 := (MonoidHom.mem_ker).1 hz
    rw [hz1]
    exact U.one_mem
  have hWindexOdd : ¬ 2 ∣ W.index := by
    rw [Subgroup.index_comap_of_surjective (H := U) hπsurj]
    have h := hU.2.2
    change ¬ 2 ∣ U.relIndex ⊤ at h
    rwa [Subgroup.relIndex_top_right] at h
  have hWcard : Nat.card W = Nat.card Z * Nat.card Uhat := by
    rw [← Nat.card_congr
      (CFSG.LieType.CentralExt.kerProdLiftSubgroupEquiv hπsurj hZcenter hC hU2).toEquiv,
      Nat.card_prod]
  have hWdecomp : W = Z ⊔ Uhat := by
    refine le_antisymm ?_ (sup_le hZleW hUhatleW)
    intro w hw
    obtain ⟨⟨z, u⟩, hzu⟩ :=
      (CFSG.LieType.CentralExt.kerProdLiftSubgroupEquiv hπsurj hZcenter hC hU2).surjective
        ⟨w, hw⟩
    have hwval : (z : SL) * (u : SL) = w := by
      have h := congrArg Subtype.val hzu
      simpa [CFSG.LieType.CentralExt.kerProdLiftSubgroupEquiv_apply] using h
    rw [← hwval]
    exact mul_mem (Subgroup.mem_sup_left z.2) (Subgroup.mem_sup_right u.2)
  have hUhatnormW : W ≤ Subgroup.normalizer (Uhat : Set SL) := by
    rw [hWdecomp]
    exact sup_le (hZcenter.trans (Subgroup.center_le_normalizer (Uhat : Set SL)))
      Subgroup.le_normalizer
  have hUhatsubcard : Nat.card (Uhat.subgroupOf W) = Nat.card Uhat :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUhatleW).toEquiv
  have hUhatIndexW : ¬ 2 ∣ (Uhat.subgroupOf W).index := by
    have h := Subgroup.card_mul_index (H := Uhat.subgroupOf W)
    have hmul : Nat.card Uhat * (Uhat.subgroupOf W).index = Nat.card Uhat * Nat.card Z := by
      calc Nat.card Uhat * (Uhat.subgroupOf W).index
          = Nat.card (Uhat.subgroupOf W) * (Uhat.subgroupOf W).index := by rw [hUhatsubcard]
        _ = Nat.card W := h
        _ = Nat.card Z * Nat.card Uhat := hWcard
        _ = Nat.card Uhat * Nat.card Z := by ring
    have hidx : (Uhat.subgroupOf W).index = Nat.card Z :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul
    rw [hidx]
    exact hZodd.not_two_dvd_nat
  have hUhatSylW : CFSG.QuasithinUnique.IsSylowTwoOf Uhat W :=
    ⟨hUhatleW, hUhat2, hUhatIndexW⟩
  have hUhatIndexSL : ¬ 2 ∣ Uhat.index := by
    rw [← Subgroup.relIndex_mul_index hUhatleW]
    exact Nat.Prime.not_dvd_mul Nat.prime_two hUhatIndexW hWindexOdd
  have hUhatSylSL : CFSG.QuasithinUnique.IsSylowTwoOf Uhat ⊤ := by
    refine ⟨le_top, hUhat2, ?_⟩
    have h := hUhatIndexSL
    rw [← Subgroup.relIndex_top_right] at h
    exact h
  have hU0 : CFSG.QuasithinUnique.IsSylowTwoOf U0 ⊤ :=
    CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (K := F) (n := m + 1) (by omega)
  obtain ⟨g, -, hg⟩ := CFSG.GroupTheory.exists_eq_conjSub_of_isSylowTwoOf
    (P := Uhat) (P' := U0) hUhatSylSL hU0
  have hFcardpow : Nat.card F = 2 ^ Q.exponent := by
    rw [hFcard, TauCeti.PrimePower.card_def, hQ]
  have hB : Subgroup.normalizer (U0 : Set SL) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular (m + 1) F :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.normalizer_unitriangular
  have hBsolv : Group.IsSolvable
      ↥(CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular (m + 1) F) :=
    CFSG.LieType.SteinbergBR.isSolvable_upperTriangular_of_card Nat.prime_two hFcardpow (m + 1)
  have hNU0solv : Group.IsSolvable ↥(Subgroup.normalizer (U0 : Set SL)) := by
    rw [hB]
    exact hBsolv
  have hNU0eq : Subgroup.normalizer (U0 : Set SL) =
      CFSG.Quasithin.conjSub g (Subgroup.normalizer (Uhat : Set SL)) := by
    rw [hg, CFSG.Quasithin.conjSub_normalizer]
  have hNUhatsolv : Group.IsSolvable ↥(Subgroup.normalizer (Uhat : Set SL)) := by
    haveI : Group.IsSolvable ↥(Subgroup.normalizer (U0 : Set SL)) := hNU0solv
    let en : ↥(Subgroup.normalizer (Uhat : Set SL)) ≃*
        ↥(Subgroup.normalizer (U0 : Set SL)) :=
      (Subgroup.equivMapOfInjective (Subgroup.normalizer (Uhat : Set SL))
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
        (MulEquiv.subgroupCongr hNU0eq.symm)
    exact Group.isSolvable_of_surjective (f := en.symm.toMonoidHom) en.symm.surjective
  have hNWle : Subgroup.normalizer (W : Set SL) ≤ Subgroup.normalizer (Uhat : Set SL) := by
    intro n hn
    have hnW : CFSG.Quasithin.conjSub n W = W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
    have hQleW : CFSG.Quasithin.conjSub n Uhat ≤ W := by
      calc CFSG.Quasithin.conjSub n Uhat ≤ CFSG.Quasithin.conjSub n W :=
            CFSG.Quasithin.conjSub_mono n hUhatleW
        _ = W := hnW
    have hQp : IsPGroup 2 (CFSG.Quasithin.conjSub n Uhat) :=
      hUhat2.map (MulAut.conj n).toMonoidHom
    have hQnorm : CFSG.Quasithin.conjSub n Uhat ≤
        Subgroup.normalizer (Uhat : Set SL) := hQleW.trans hUhatnormW
    have hsup2 : IsPGroup 2 (Uhat ⊔ CFSG.Quasithin.conjSub n Uhat : Subgroup SL) :=
      hUhat2.to_sup_of_normal_left' hQp hQnorm
    have hsupW : Uhat ⊔ CFSG.Quasithin.conjSub n Uhat ≤ W :=
      sup_le hUhatleW hQleW
    have hsupEq : Uhat ⊔ CFSG.Quasithin.conjSub n Uhat = Uhat :=
      CFSG.GroupTheory.eq_of_isSylowTwoOf_of_le hUhatSylW hsup2 hsupW le_sup_left
    have hQleU : CFSG.Quasithin.conjSub n Uhat ≤ Uhat :=
      (le_sup_right : CFSG.Quasithin.conjSub n Uhat ≤
        Uhat ⊔ CFSG.Quasithin.conjSub n Uhat).trans (le_of_eq hsupEq)
    have hcard : Nat.card (CFSG.Quasithin.conjSub n Uhat) = Nat.card Uhat :=
      Subgroup.card_map_of_injective (MulAut.conj n).injective
    have hconjEq : CFSG.Quasithin.conjSub n Uhat = Uhat :=
      Subgroup.eq_of_le_of_card_ge hQleU (le_of_eq hcard.symm)
    have hconjEqInv : CFSG.Quasithin.conjSub n⁻¹ Uhat = Uhat := by
      have h : Uhat = CFSG.Quasithin.conjSub n⁻¹ Uhat := by
        have h' := congrArg (CFSG.Quasithin.conjSub n⁻¹) hconjEq
        simpa [CFSG.Quasithin.conjSub_conjSub_inv] using h'
      exact h.symm
    exact CFSG.Quasithin.F7.mem_normalizer_of_conj_le
      (le_of_eq hconjEq) (le_of_eq hconjEqInv)
  have hWsolv : Group.IsSolvable ↥(Subgroup.normalizer (W : Set SL)) := by
    haveI : Group.IsSolvable ↥(Subgroup.normalizer (Uhat : Set SL)) := hNUhatsolv
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hNWle) (Subgroup.inclusion_injective hNWle)
  have hNmap : Subgroup.normalizer (U : Set L) =
      (Subgroup.normalizer (W : Set SL)).map π := by
    have h1 : (Subgroup.normalizer (U : Set L)).comap π =
        Subgroup.normalizer (W : Set SL) := by
      rw [Subgroup.comap_normalizer_eq_of_surjective (H := U) hπsurj]
    rw [← h1]
    exact (Subgroup.map_comap_eq_self_of_surjective hπsurj
      (Subgroup.normalizer (U : Set L))).symm
  have hmapSolv : Group.IsSolvable ↥((Subgroup.normalizer (W : Set SL)).map π) := by
    haveI : Group.IsSolvable ↥(Subgroup.normalizer (W : Set SL)) := hWsolv
    exact Group.isSolvable_of_surjective
      (π.subgroupMap_surjective (Subgroup.normalizer (W : Set SL)))
  rw [hNmap]
  exact hmapSolv

end CFSG.ClassicalGroups.SpecialLinear

end
