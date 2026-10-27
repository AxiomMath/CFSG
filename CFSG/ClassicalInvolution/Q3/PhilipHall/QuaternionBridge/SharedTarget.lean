module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.Reduction
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.Subnormal

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open scoped commutatorElement


@[expose] def Q8TwinRecogEx (Ex : ∀ (Y : Type) [Group Y] [Finite Y], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup ↥(genFittingFStar Y) →
    (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) → CIT3Below (Nat.card Y) →
    TightBelow (Nat.card Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      IsSubnormal (tightCore R) (Subgroup.centralizer ({t} : Set Y)) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) → TightHasLift R t ∨ Ex Y

@[expose] def Q8ExGood (Ex : ∀ (Y : Type) [Group Y] [Finite Y], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Ex Y →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      IsSubnormal (tightCore R) (Subgroup.centralizer ({t} : Set Y)) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) → GoodThreeElement R t

theorem q8TwinGood_of_recogEx {Ex : ∀ (Y : Type) [Group Y] [Finite Y], Prop}
    (h : Q8TwinRecogEx Ex) (hx : Q8ExGood Ex) (Y : Type) [Group Y] [Finite Y]
    (hF : IsSimpleGroup ↥(genFittingFStar Y)) (hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a)
    (hbelow : CIT3Below (Nat.card Y)) (hbelowT : TightBelow (Nat.card Y))
    (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (hd : Q8TwinDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) (hgen : TightSelfGen R)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hA : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hsub : IsSubnormal (tightCore R) (Subgroup.centralizer ({t} : Set Y)))
    (htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R) :
    TightHasLift R t ∨ GoodThreeElement R t := by
  rcases h Y hF hnab hbelow hbelowT R S t hd hq8 hgen hΩ hA hsub htw with hl | he
  · exact Or.inl hl
  · exact Or.inr (hx Y he R S t hd hq8 hgen hΩ hA hsub htw)

theorem tightCentTwinLift_of_q8RecogEx {Ex : ∀ (Y : Type) [Group Y] [Finite Y], Prop}
    (h : Q8TwinRecogEx Ex) (hx : Q8ExGood Ex) (n : ℕ) : TightCentTwinLift n := by
  intro hA hb Y _ _ hn R S t hd hc hE2 hQ _ c hcZ hc1 hy _
  obtain ⟨y, hy⟩ := hy
  have B := q8Bridge_of_centTwin hd hc hE2 hQ hcZ hc1 hy
  have hle : Nat.card (Y ⧸ TA3.fstarCenter Y) ≤ n := by rw [← hn]; exact B.quot.card_lt.le
  rcases q8TwinGood_of_recogEx h hx _ B.simple B.nonab (cit3Below_mono hle hA)
      (tightBelow_mono hle hb) _ _ _ B.quot.datum B.quot.cls.1 B.quot.cls.2.1 B.quot.hyp B.aEmpty
      (isSubnormal_tightCore_map hd B.central B.two B.not_mem) B.quot.twin with hl | hg
  · exact good_of_hasLift_twin hd B.central B.two B.not_mem hl
  · exact good_of_twin hd B.central B.two B.not_mem hg

theorem tightTwistAllTwin_of_q8RecogEx {Ex : ∀ (Y : Type) [Group Y] [Finite Y], Prop}
    (h : Q8TwinRecogEx Ex) (hx : Q8ExGood Ex) (n : ℕ) : TightTwistAllTwin n := by
  intro hA hb Y _ _ hn R S t hd hc hE2 htw hall _ _
  have B := q8Bridge_of_twisted hd hc hE2 htw hall
  have hle : Nat.card (Y ⧸ genFittingFitting Y) ≤ n := by rw [← hn]; exact B.quot.card_lt.le
  rcases q8TwinGood_of_recogEx h hx _ B.simple B.nonab (cit3Below_mono hle hA)
      (tightBelow_mono hle hb) _ _ _ B.quot.datum B.quot.cls.1 B.quot.cls.2.1 B.quot.hyp B.aEmpty
      (isSubnormal_tightCore_map hd B.central B.two B.not_mem) B.quot.twin with hl | hg
  · exact good_of_hasLift_twin hd B.central B.two B.not_mem hl
  · exact good_of_twin hd B.central B.two B.not_mem hg

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
