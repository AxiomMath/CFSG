module

public import CFSG.GH74.QTGen4.U42.PairLift
public import CFSG.GH74.QTGen4.U42.PairCharacters
public import CFSG.GH74.QTGen4.U42.PairTwist

public section

namespace CFSG.GH74.QTGen4.U42

theorem pair_extension {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    {H B T U : Subgroup G} {H' B' T' U' : Subgroup G'}
    (h : PairCore H B T U) (h' : PairCore H' B' T' U') (hUB : U ≤ ⁅B, B⁆)
    (e : ↥U ≃* U0) (lam : ↥B ≃* ↥B')
    (hT : ∀ b : ↥B, (b : G) ∈ T ↔ ((lam b : ↥B') : G') ∈ T')
    (hU : ∀ b : ↥B, (b : G) ∈ U ↔ ((lam b : ↥B') : G') ∈ U') :
    ∃ θ : ↥H ≃* ↥H', ∀ b : ↥B, ((θ ⟨b, h.B_le_H b.2⟩ : ↥H') : G') = ((lam b : ↥B') : G') := by
  let e' := pairUCoords h h' e lam hU
  obtain ⟨α, hα⟩ := exists_pair_action_lift h h' e lam hT hU
  let B0 := B.subgroupOf H
  let iB : ↥B0 ≃* ↥B := Subgroup.subgroupOfEquivOfLe h.B_le_H
  let β : ↥B0 →* ↥H' := (Subgroup.inclusion h'.B_le_H).comp
    (lam.toMonoidHom.comp iB.toMonoidHom)
  let Z' := Subgroup.zpowers (zH h' e')
  have hZ' : Z' ≤ Subgroup.center ↥H' := Subgroup.zpowers_le.mpr (zH_mem_center h' e')
  letI : CommGroup ↥Z' :=
    { (inferInstance : Group ↥Z') with
      mul_comm := fun x y => Subtype.ext ((Subgroup.mem_center_iff.mp (hZ' x.2) y).symm) }
  have hβ : ∀ b : ↥B0, nuHom h'.U_normal e' (β b) = nuHom h.U_normal e (b : ↥H) := by
    intro b
    exact (nuHom_lam h h' e lam hU (iB b)).symm
  have hmod : ∀ b : ↥B0, (α (b : ↥H))⁻¹ * β b ∈ Z' := by
    intro b
    apply (nu_eq_one_iff_mem_zpowers h' h'.U_normal e' _).mp
    change nuHom h'.U_normal e' ((α (b : ↥H))⁻¹ * β b) = 1
    rw [map_mul, map_inv, hα, hβ, inv_mul_cancel]
  let δ : ↥B0 →* ↥Z' := PairTwist.centralDiscrepancy B0 α β Z' hZ' hmod
  have hδU : ∀ b : ↥B0, ((b : ↥H) : G) ∈ U → δ b = 1 := by
    intro b hb
    let δB : ↥B →* ↥Z' := δ.comp iB.symm.toMonoidHom
    have hc : δB (iB b) = 1 :=
      hom_trivial_of_mem_commutator_subgroup B δB (iB b) (hUB hb)
    change δ (iB.symm (iB b)) = 1 at hc
    simpa only [MulEquiv.symm_apply_apply] using hc
  have hA : ∀ a : ↥Z', a ^ 2 = 1 := by
    intro a
    apply Subtype.ext
    exact sq_eq_one_of_mem_zpowers (zH h' e') (zH_orderOf h' e') a a.2
  obtain ⟨N, hN, hUN, hNB, hcube⟩ := exists_pair_normal_three h e
  letI : N.Normal := hN
  have hδN : ∀ b : ↥B0, (b : ↥H) ∈ N → δ b = 1 :=
    hom_trivial_of_cube_mem B0 (U.subgroupOf H) N δ hA hδU (fun b hb => hcube (b : ↥H) hb)
  obtain ⟨χ, hχB⟩ := extend_hom_of_sup_eq_top B0 N (by simpa only [sup_comm] using hNB) δ hδN
  have hzU : ((zH h e : ↥H) : G) ∈ U := (e.symm zc).2
  have hzB : zH h e ∈ B0 := h.T_le_B (h.U_le_T hzU)
  let bz : ↥B0 := ⟨zH h e, hzB⟩
  have hχz : χ (zH h e) = 1 := (hχB bz).trans (hδU bz hzU)
  have hkill : ∀ x : ↥H, α x ∈ Z' → χ x = 1 :=
    PairTwist.kills_central_preimage α Z' χ (zH h e) hχz
      (fun x hx => (pair_action_lift_kernel_iff h h' e lam hU α hα x).mp hx)
  let θ := PairTwist.twist α Z' hZ' χ hkill
  refine ⟨θ, ?_⟩
  intro b
  let b0 : ↥B0 := ⟨⟨(b : G), h.B_le_H b.2⟩, b.2⟩
  have heq : θ (b0 : ↥H) = β b0 :=
    PairTwist.twist_eq_on B0 α β Z' hZ' hmod χ hkill hχB b0
  exact congrArg (fun x : ↥H' => (x : G')) heq

end CFSG.GH74.QTGen4.U42
