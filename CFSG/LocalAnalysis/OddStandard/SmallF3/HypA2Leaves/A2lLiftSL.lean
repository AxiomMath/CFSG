module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSLCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.TypU

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification

theorem a2l_isPerfect_of_isSLTwoOver {A : Type} [Group A] {q₀ : ℕ} (h5 : 5 ≤ q₀)
    (h : HarrisLit.IsSLTwoOver q₀ A) : Group.IsPerfect A := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  haveI := Fintype.finite ‹Fintype F›
  refine ClassicalInvolution.isPerfect_of_equiv_sl2 ?_ e
  rw [Nat.card_eq_fintype_card, hF]
  omega

theorem a2l_lift_sl2 (hGA : TBLit.GriessMultipliersOdd) {K K' : Type} [Group K] [Finite K]
    [Group K'] (π : K →* K') (hπ : Function.Surjective π) (hker : π.ker ≤ center K)
    (h2 : IsPGroup 2 π.ker) {q₀ : ℕ} (hodd : Odd q₀) (h5 : 5 ≤ q₀) (N' : Subgroup K')
    (hN' : HarrisLit.IsSLTwoOver q₀ ↥N') :
    ∃ N : Subgroup K, HarrisLit.IsSLTwoOver q₀ ↥N ∧ N.map π = N' ∧ ⁅N, N⁆ = N ∧
      ∀ x ∈ N, π x = 1 → x = 1 := by
  haveI : Group.IsPerfect ↥N' := a2l_isPerfect_of_isSLTwoOver h5 hN'
  let M : Subgroup K := N'.comap π
  let f : ↥M →* ↥N' := (π.comp M.subtype).codRestrict N' fun x => x.2
  have hf : Function.Surjective f := fun r => by
    obtain ⟨x, hx⟩ := hπ r
    exact ⟨⟨x, show π x ∈ N' by rw [hx]; exact r.2⟩, Subtype.ext hx⟩
  have hfk : ∀ x : ↥M, f x = 1 → π x.1 = 1 := fun x hx => congrArg Subtype.val hx
  have hfker : f.ker ≤ center ↥M := fun x hx => by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker (hfk x hx)) y.1)
  have hf2 : IsPGroup 2 ↥f.ker := by
    refine h2.of_injective ((M.subtype.comp f.ker.subtype).codRestrict π.ker fun x => ?_) ?_
    · exact hfk x.1 x.2
    · intro x y hxy
      have h1 := Subtype.ext_iff.1 hxy
      exact Subtype.ext (Subtype.ext h1)
  have hSL := a2l_isSLTwoOver_commutator_of_cover hGA hodd h5 hN' f hf hfker hf2
  let D : Subgroup ↥M := commutator ↥M
  have eN : ↥D ≃* ↥(D.map M.subtype) := D.equivMapOfInjective M.subtype M.subtype_injective
  have hN1 : HarrisLit.IsSLTwoOver q₀ ↥(D.map M.subtype) :=
    HypA2.isSLTwoOver_of_mulEquiv eN hSL
  have hmap : (D.map M.subtype).map π = N' := by
    apply le_antisymm
    · rintro _ ⟨y, ⟨d, -, rfl⟩, rfl⟩
      exact d.2
    · intro r hr
      have hmem : (⟨r, hr⟩ : ↥N') ∈ D.map f := by
        rw [CentralExtensions.derived_map_eq_top f hf]
        exact Subgroup.mem_top _
      obtain ⟨d, hd, hdr⟩ := Subgroup.mem_map.1 hmem
      exact ⟨d.1, ⟨d, hd, rfl⟩, congrArg Subtype.val hdr⟩
  haveI : Group.IsPerfect ↥(D.map M.subtype) := a2l_isPerfect_of_isSLTwoOver h5 hN1
  refine ⟨D.map M.subtype, hN1, hmap, ?_, ?_⟩
  · exact LocalAnalysis.ComponentInitial.commutator_self_of_commutator_eq_top
      Group.IsPerfect.commutator_eq_top
  · let ρ : ↥(D.map M.subtype) →* ↥N' :=
      (π.comp (D.map M.subtype).subtype).codRestrict N' fun x => hmap ▸ ⟨x.1, x.2, rfl⟩
    have hρ : Function.Surjective ρ := fun r => by
      have hr : (r : K') ∈ (D.map M.subtype).map π := by
        rw [hmap]
        exact r.2
      obtain ⟨x, hx, hxr⟩ := hr
      exact ⟨⟨x, hx⟩, Subtype.ext hxr⟩
    have hcard : Nat.card ↥(D.map M.subtype) = Nat.card ↥N' := by
      rw [GS82PumpInputs.Residue.card_of_isSLTwoOver hN1,
        GS82PumpInputs.Residue.card_of_isSLTwoOver hN']
    have hbij := hρ.bijective_of_nat_card_le hcard.le
    intro x hx hx1
    have h1 : ρ ⟨x, hx⟩ = ρ 1 := by
      rw [map_one]
      exact Subtype.ext hx1
    exact congrArg Subtype.val (hbij.1 h1)

end CFSG.OddStandard.SmallF3.HypA2Leaves
