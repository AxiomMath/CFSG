module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25
public import CFSG.ClassicalInvolution.Q3.Q3T7F25M8

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

namespace C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section Statements


@[expose] def Mix14R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t →
    ∀ (K' W : Subgroup Y) (S₁ : Sylow 2 Y) (R₁ R₂ : Subgroup Y) (t₁ u₁ u₂ : Y),
      T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t t₁
        u₁ u₂ →
      (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) =
        Subgroup.zpowers t →
      ∀ a ∈ (S₁ : Subgroup Y), a * a = 1 → IsFAut R₂ a →
        ∃ x ∈ R₁, (a * x) * (a * x) = 1 ∧ IsFAut R₁ (a * x)

@[expose] def ZStarFFR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t →
    ∀ (K' W : Subgroup Y) (S₁ : Sylow 2 Y) (R₁ R₂ : Subgroup Y) (t₁ u₁ u₂ : Y),
      T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t t₁
        u₁ u₂ →
      (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) =
        Subgroup.zpowers t →
      ∀ b ∈ (S₁ : Subgroup Y), b * b = 1 → IsFAut R₁ b → IsFAut R₂ b →
        t ∈ zStarOf (Subgroup.centralizer ({b} : Set Y))

theorem c25_16invR_of_parts {r n : ℕ} (h6 : C25_6R r n) (hm : Mix14R r n) (hz : ZStarFFR r n) :
    C25_16invR r n := by
  intro Y _ _ R S t hP K' W S₁ R₁ R₂ t₁ u₁ u₂ hyp a haS ha2 hF
  have h11 := Perp25.c25_11_of_zStar_swap hyp
    fun t' ht'S ht'2 hg ht'R hnf a ha2 ha1 haA hat =>
      h6 Y R S t hP K' W S₁ R₁ R₂ t₁ u₁ u₂ hyp t' ht'S ht'2 hg ht'R hnf a ha2 ha1 haA hat
  obtain ⟨x, hxR, hx2, hFx⟩ := hm Y R S t hP K' W S₁ R₁ R₂ t₁ u₁ u₂ hyp h11 a haS ha2 hF
  obtain ⟨t', hT⟩ := T7F25.Asc77.T7T.exists_hyp25T hyp
  have hbS : a * x ∈ (S₁ : Subgroup Y) := (S₁ : Subgroup Y).mul_mem haS (hT.hRS hxR)
  have hF₂ : IsFAut R₂ (a * x) :=
    T7U.isFAut_mul_of_centralizes (fun y hy => (hT.hcomm x hxR y hy)) hF
  exact T7F25.Asc77.C25V.false_of_zStar_ff h11 hyp hbS hx2 hFx hF₂
    (hz Y R S t hP K' W S₁ R₁ R₂ t₁ u₁ u₂ hyp h11 (a * x) hbS hx2 hFx hF₂)

end Statements

end C2516

end CFSG.CGT.PushingUpLit.SolKNA.R4
