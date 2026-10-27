module
public import CFSG.LieType.AlgebraicGroups.ClosedIdentityComponentFunctorial

public section
namespace CFSG.LieType.AlgebraicGroups
open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
variable {τ : Tag} {k : Type} [Field k]
theorem closedIdentityComponent_le_normalizerAction_ker
    (E K : Subgroup (ModGL τ k)) [Finite E] :
    let N := normalizer (E : Set (ModGL τ k)) ⊓ K
    (closedIdentityComponent N).subgroupOf N ≤
      (E.normalizerMonoidHom.comp (inclusion inf_le_left)).ker := by
  intro N n hn
  have hc : (n : ModGL τ k) ∈ centralizer (E : Set (ModGL τ k)) :=
    closedIdentityComponent_normalizer_inf_le_centralizer E K hn
  have h : inclusion (show N ≤ normalizer (E : Set (ModGL τ k)) from inf_le_left) n ∈
      E.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    exact hc
  exact h

@[expose] noncomputable def finiteNormalizerComponentAction
    (E K : Subgroup (ModGL τ k)) [Finite E] :
    let N := normalizer (E : Set (ModGL τ k)) ⊓ K
    (N ⧸ (closedIdentityComponent N).subgroupOf N) →* MulAut E :=
  QuotientGroup.lift _ (E.normalizerMonoidHom.comp (inclusion inf_le_left))
    (closedIdentityComponent_le_normalizerAction_ker E K)

theorem finite_normalizer_component_quotient
    (E K : Subgroup (ModGL τ k)) :
    let N := normalizer (E : Set (ModGL τ k)) ⊓ K
    Finite (N ⧸ (closedIdentityComponent N).subgroupOf N) := by
  intro N
  infer_instance

theorem finiteNormalizerComponentAction_mk
    (E K : Subgroup (ModGL τ k)) [Finite E]
    (n : ↥(normalizer (E : Set (ModGL τ k)) ⊓ K)) :
    finiteNormalizerComponentAction E K (QuotientGroup.mk n) =
      E.normalizerMonoidHom (inclusion inf_le_left n) := rfl

theorem finiteNormalizerComponentAction_ker
    (E K : Subgroup (ModGL τ k)) [Finite E] :
    let N := normalizer (E : Set (ModGL τ k)) ⊓ K
    (finiteNormalizerComponentAction E K).ker =
      ((centralizer (E : Set (ModGL τ k))).subgroupOf N).map
        (QuotientGroup.mk' ((closedIdentityComponent N).subgroupOf N)) := by
  let N := normalizer (E : Set (ModGL τ k)) ⊓ K
  let f : N →* MulAut E := E.normalizerMonoidHom.comp (inclusion inf_le_left)
  have hker : f.ker = (centralizer (E : Set (ModGL τ k))).subgroupOf N := by
    ext n
    have h := congrArg (fun S : Subgroup (normalizer (E : Set (ModGL τ k))) =>
      inclusion (show N ≤ normalizer (E : Set (ModGL τ k)) from inf_le_left) n ∈ S)
        (normalizerMonoidHom_ker (H := E))
    exact Iff.of_eq h
  dsimp only [finiteNormalizerComponentAction]
  rw [QuotientGroup.ker_lift]
  exact congrArg (Subgroup.map (QuotientGroup.mk' ((closedIdentityComponent N).subgroupOf N))) hker

theorem isPGroup_finiteNormalizerComponentAction_ker
    (G E H : Subgroup (ModGL τ k)) [Finite E] (hHE : H ≤ E)
    (hcomponents : IsPGroup 3 (↥(G ⊓ centralizer (E : Set (ModGL τ k))) ⧸
      (closedIdentityComponent (G ⊓ centralizer (E : Set (ModGL τ k)))).subgroupOf
        (G ⊓ centralizer (E : Set (ModGL τ k))))) :
    let K := closedIdentityComponent (G ⊓ centralizer (H : Set (ModGL τ k)))
    IsPGroup 3 (finiteNormalizerComponentAction E K).ker := by
  let K := closedIdentityComponent (G ⊓ centralizer (H : Set (ModGL τ k)))
  let N := normalizer (E : Set (ModGL τ k)) ⊓ K
  let C := G ⊓ centralizer (E : Set (ModGL τ k))
  let S := closedIdentityComponent C
  let π : N →* N ⧸ (closedIdentityComponent N).subgroupOf N :=
    QuotientGroup.mk' ((closedIdentityComponent N).subgroupOf N)
  have hNS : closedIdentityComponent N = S :=
    closedIdentityComponent_normalizer_inf_hyperplane_eq G E H hHE
  change IsPGroup 3 (finiteNormalizerComponentAction E K).ker
  rw [finiteNormalizerComponentAction_ker]
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro q
  obtain ⟨n, hn, hnq⟩ := q.2
  have hnC : (n : ModGL τ k) ∈ C :=
    ⟨(closedIdentityComponent_le _ n.2.2).1, hn⟩
  let c : C := ⟨n, hnC⟩
  let ρ := QuotientGroup.mk' (S.subgroupOf C)
  have hpC : IsPGroup 3 (C ⧸ S.subgroupOf C) := hcomponents
  obtain ⟨j, hj⟩ := hpC.exists_pow_pow_eq_one (ρ c)
  have hcS : (n : ModGL τ k) ^ (3 ^ j) ∈ S := by
    have hj' : ρ (c ^ (3 ^ j)) = 1 := by rw [map_pow]; exact hj
    have h : c ^ (3 ^ j) ∈ S.subgroupOf C :=
      (QuotientGroup.eq_one_iff _).mp hj'
    exact h
  have hpn : π n ^ (3 ^ j) = 1 := by
    rw [← map_pow]
    have hnS : n ^ (3 ^ j) ∈ S.subgroupOf N := hcS
    have hsub : (closedIdentityComponent N).subgroupOf N = S.subgroupOf N :=
      congrArg (fun B : Subgroup (ModGL τ k) => B.subgroupOf N) hNS
    exact (QuotientGroup.eq_one_iff _).mpr (hsub.symm ▸ hnS)
  refine ⟨j, Subtype.ext ?_⟩
  change (q : N ⧸ (closedIdentityComponent N).subgroupOf N) ^ (3 ^ j) = 1
  rw [← hnq]
  exact hpn
end CFSG.LieType.AlgebraicGroups
