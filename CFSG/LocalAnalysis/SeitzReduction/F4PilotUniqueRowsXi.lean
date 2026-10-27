module

public import CFSG.LieType.Chevalley.E6SecondGraphFixedSubgroup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSmallLie.Setup

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.E6SecondGraphFixed (SecondGraphFixedSubgroup)

theorem card_eqLocus_secondGraph_lt {Gm : Type*} [Group Gm] {C J : Subgroup Gm} {P t₀ : Gm}
    {H : Type*} [Group H] {e : J ≃* H} (hsec : SecondGraphFixedSubgroup C J P t₀ e)
    (hZ : center H = ⊥) [Finite J] {η : MulAut C} (hη : ∀ g : C, (η g : Gm) = P * g * P⁻¹)
    (hx : t₀ ∈ C) :
    Nat.card ((MulAut.conj (⟨t₀, hx⟩ : C) * η).toMonoidHom.eqLocus (MonoidHom.id C)) <
      Nat.card J := by
  obtain ⟨htJ, hJC, η₀, -, huniq, -, -, hfix, -, hord, -⟩ := hsec
  have hηη₀ : η = η₀ := huniq η hη
  subst hηη₀
  have : Finite (J.subgroupOf C) := Finite.of_equiv _ (subgroupOfEquivOfLe hJC).symm.toEquiv
  set F := (MulAut.conj (⟨t₀, hx⟩ : C) * η).toMonoidHom.eqLocus (MonoidHom.id C) with hF
  have hFJ : F ≤ J.subgroupOf C := fun g hg => mem_subgroupOf.2 ((hfix g).1 hg).1
  have hne : ∃ x : J, x * ⟨t₀, htJ⟩ ≠ ⟨t₀, htJ⟩ * x := by
    by_contra hcon
    push Not at hcon
    have hcen : (⟨t₀, htJ⟩ : J) ∈ center J := mem_center_iff.2 hcon
    have h1 : e ⟨t₀, htJ⟩ ∈ center H := (MulEquivClass.apply_mem_center_iff e).2 hcen
    rw [hZ, mem_bot] at h1
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  obtain ⟨x, hx'⟩ := hne
  have hlt : F < J.subgroupOf C := lt_of_le_of_ne hFJ fun h => by
    have hxF : (⟨x, hJC x.2⟩ : C) ∈ F := by
      rw [h]
      exact mem_subgroupOf.2 x.2
    exact hx' (Subtype.ext ((hfix _).1 hxF).2.symm)
  calc Nat.card F < Nat.card (J.subgroupOf C) := Subgroup.card_lt_of_lt hlt
    _ = Nat.card J := Nat.card_congr (subgroupOfEquivOfLe hJC).toEquiv

end CFSG.SeitzReduction.F4Pilot
