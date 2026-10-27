module

public import CFSG.ClassicalGroups.SpecialLinear.QuasisimpleCoverUncond
public import CFSG.ClassicalGroups.SpecialLinear.QuasisimpleCartanRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.QuasithinUnique CFSG.LieType.CentralExt

theorem odd_centralizer_centralizes_of_component_A
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 3 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.A m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.A m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {U : Subgroup L} (hU2 : IsPGroup 2 U) (hUmax : IsSylowTwoOf U ⊤)
    {x : L} (hxodd : Odd (orderOf x)) (hxc : x ∈ Subgroup.centralizer (U : Set L))
    (hSL : ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = Q.card →
      ∀ (V : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F)),
        IsSylowTwoOf V ⊤ →
        ∀ y : Matrix.SpecialLinearGroup (Fin (m + 1)) F, Odd (orderOf y) →
          y ∈ Subgroup.centralizer (V : Set _) →
            y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) :
    ∀ l : L, x * l = l * x := by
  classical
  have hne : ¬ (m = 2 ∧ Q.card = 4) := by omega
  obtain ⟨F, hFfield, hFfinite, hFchar, π, hFcard, hπsurj, hker⟩ :=
    CFSG.ClassicalGroups.SpecialLinear.exists_central_cover_specialLinear_of_ne_two_four
      hL m (by omega) Q hQ hv e hne
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  letI : CharP F 2 := hFchar
  let SL := Matrix.SpecialLinearGroup (Fin (m + 1)) F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsubtop_index : ∀ H : Subgroup SL, (H.subgroupOf ⊤).index = H.index := by
    intro H
    have h := Subgroup.index_map_of_injective (H := H.subgroupOf ⊤)
      (f := (⊤ : Subgroup SL).subtype) Subtype.coe_injective
    simpa [Subgroup.map_subgroupOf_eq_of_le le_top] using h.symm
  have hoddF : Odd (Nat.card F - 1) :=
    CFSG.ClassicalGroups.SpecialLinear.odd_card_sub_one_of_char_two
  have hcenter_dvd : Nat.card (Subgroup.center SL) ∣ Nat.card F - 1 := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_scalars_dvd (n := m + 1)
      (K := F) (by omega)
  have hker_dvd : Nat.card π.ker ∣ Nat.card (Subgroup.center SL) :=
    Subgroup.card_dvd_of_le hker
  have hker_odd : Odd (Nat.card π.ker) :=
    Odd.of_dvd_nat hoddF (hker_dvd.trans hcenter_dvd)
  have hC : ¬ 2 ∣ Nat.card π.ker := hker_odd.not_two_dvd_nat
  let Û : Subgroup SL := liftSubgroup 2 π U
  have hÛ2 : IsPGroup 2 Û := liftSubgroup_isPGroup hker hU2
  have hsubtop_index_L : ∀ H : Subgroup L, (H.subgroupOf ⊤).index = H.index := by
    intro H
    have h := Subgroup.index_map_of_injective (H := H.subgroupOf ⊤)
      (f := (⊤ : Subgroup L).subtype) Subtype.coe_injective
    simpa [Subgroup.map_subgroupOf_eq_of_le le_top] using h.symm
  have hUindex : ¬ 2 ∣ U.index := by
    rw [← hsubtop_index_L U]
    exact hUmax.2.2
  have hrel : Û.relIndex (U.comap π) = Nat.card π.ker := by
    have hcard : Nat.card (U.comap π) = Nat.card π.ker * Nat.card Û := by
      rw [← Nat.card_prod,
        ← Nat.card_congr (kerProdLiftSubgroupEquiv hπsurj hker hC hU2).toEquiv]
    have h := Subgroup.relIndex_mul_card (H := Û) (K := U.comap π)
    rw [inf_eq_left.mpr (liftSubgroup_le_comap hker hU2), hcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hindex : Û.index = Nat.card π.ker * (U.comap π).index := by
    rw [← Subgroup.relIndex_mul_index (liftSubgroup_le_comap hker hU2), hrel]
  have hÛsylow : IsSylowTwoOf Û ⊤ := by
    refine ⟨le_top, hÛ2, ?_⟩
    have hcomap : (U.comap π).index = U.index := Subgroup.index_comap_of_surjective (H := U) (f := π) hπsurj
    rw [hsubtop_index Û, hindex, hcomap]
    exact Nat.Prime.not_dvd_mul Nat.prime_two hC hUindex
  obtain ⟨xhat, hxhat⟩ := hπsurj x
  have hxhat_odd : Odd (orderOf xhat) := by
    have hmem : xhat ^ orderOf x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, hxhat, pow_orderOf_eq_one]
    have hpow : xhat ^ (orderOf x * Nat.card π.ker) = 1 := by
      have h := congrArg Subtype.val (pow_card_eq_one' (G := π.ker)
        (x := ⟨xhat ^ orderOf x, hmem⟩))
      simpa [Subtype.ext_iff, pow_mul] using h
    exact Odd.of_dvd_nat (hxodd.mul hker_odd) (orderOf_dvd_of_pow_eq_one hpow)
  have hxhat_central : xhat ∈ Subgroup.centralizer (Û : Set SL) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    change y ∈ liftSubgroup 2 π U at hy
    rw [← range_pLiftHom (p := 2) hπsurj hker hC hU2] at hy
    obtain ⟨u, rfl⟩ := hy
    rw [pLiftHom_apply]
    have hu : ∃ n : ℕ, orderOf (u : L) = 2 ^ n :=
      exists_orderOf_eq_pow_of_mem hU2 u
    have hxcomm : x * (u : L) * x⁻¹ = (u : L) := by
      have h := (Subgroup.mem_centralizer_iff.mp hxc) (u : L) u.2
      calc x * (u : L) * x⁻¹ = ((u : L) * x) * x⁻¹ := by rw [h]
        _ = (u : L) := by group
    have hconj := conj_pLift (p := 2) (π := π) hπsurj hker hC xhat hu
    rw [hxhat, hxcomm] at hconj
    have hcomm : pLift 2 π (u : L) * xhat = xhat * pLift 2 π (u : L) := by
      calc pLift 2 π (u : L) * xhat
          = (xhat * pLift 2 π (u : L) * xhat⁻¹) * xhat := by rw [hconj]
        _ = xhat * pLift 2 π (u : L) := by group
    exact hcomm
  have hxhat_center : xhat ∈ Subgroup.center SL :=
    hSL F hFcard Û hÛsylow xhat hxhat_odd hxhat_central
  intro l
  obtain ⟨s, rfl⟩ := hπsurj l
  calc x * π s = π xhat * π s := by rw [hxhat]
    _ = π (xhat * s) := by rw [map_mul]
    _ = π (s * xhat) := by
      rw [← Subgroup.mem_center_iff.mp hxhat_center s]
    _ = π s * π xhat := by rw [map_mul]
    _ = π s * x := by rw [hxhat]

end CFSG.LocalAnalysis.RankThreeUC.S15

end
