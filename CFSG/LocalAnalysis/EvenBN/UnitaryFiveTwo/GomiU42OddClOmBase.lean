module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddCl
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClDisp
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveClTwoPart

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Module CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.SeitzReduction.RankOne.ClTwoPart

section Central

variable {X : Type*} [Group X] [Finite X]

theorem u42_card_fixed_onNormalCentralQuotient_dvd (N Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center X) (ψ : MulAut X) (hN : N.map ψ.toMonoidHom = N)
    (hZ : Z.map ψ.toMonoidHom = Z) :
    Nat.card (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)) ∣
      Nat.card (fixedSubgroup ψ) := by
  have h1 := card_fixed_onQuotient_dvd (Z.subgroupOf N) (central_subgroupOf N Z hcentral)
    (restrictAutomorphism N ψ hN) (restricted_central_invariant N Z ψ hN hZ)
  refine h1.trans ?_
  rw [Nat.card_congr (fixedNormalEquiv N ψ hN).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

end Central

section Orthogonal

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem u42_finite_orthogonalGroup (Q : QuadraticForm K V) :
    Finite (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => g.toEquiv)
      (fun g h hgh => LinearEquiv.ext fun x => by simpa using congrArg (fun e : V ≃ V => e x) hgh)
  exact Finite.of_injective (fun g : TauCeti.QuadraticMap.orthogonalGroup Q => g.val)
    Subtype.val_injective

theorem u42_card_scalarSigns_subgroupOf_dvd_two (Q : QuadraticForm K V) :
    Nat.card ((scalarSigns Q).subgroupOf (orthogonalDerived Q)) ∣ 2 := by
  have hle : Nat.card ((scalarSigns Q).subgroupOf (orthogonalDerived Q)) ≤
      Nat.card (scalarSigns Q) :=
    Nat.card_le_card_of_injective (fun x => (⟨(x : orthogonalDerived Q).val, x.2⟩ : scalarSigns Q))
      (fun a b hab => by
        have h' := congrArg (fun x : scalarSigns Q =>
          (x : TauCeti.QuadraticMap.orthogonalGroup Q)) hab
        exact Subtype.ext (Subtype.ext h'))
  exact dvd_two_of_pos_of_le_two Nat.card_pos (hle.trans (card_scalarSigns_le_two Q))

theorem u42_omega_fixed_constraints (Q : QuadraticForm K V) (hidx : (orthogonalDerived Q).index = 4)
    (ψ : MulAut (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hN : (orthogonalDerived Q).map ψ.toMonoidHom = orthogonalDerived Q)
    (hZ : (scalarSigns Q).map ψ.toMonoidHom = scalarSigns Q)
    {J : Subgroup ↥(fixedSubgroup (onNormalCentralQuotient (orthogonalDerived Q) (scalarSigns Q)
      ψ hN hZ))}
    (h : U42Hyp (onNormalCentralQuotient (orthogonalDerived Q) (scalarSigns Q) ψ hN hZ) J) :
    25920 ∣ Nat.card (fixedSubgroup ψ) ∧
      Nat.card (fixedSubgroup ψ) ∣
        4 * Nat.card ((scalarSigns Q).subgroupOf (orthogonalDerived Q)) * 51840 := by
  haveI := u42_finite_orthogonalGroup Q
  refine ⟨h.dvd_card.trans (u42_card_fixed_onNormalCentralQuotient_dvd (orthogonalDerived Q)
    (scalarSigns Q) (scalarSigns_central Q) ψ hN hZ), ?_⟩
  have h1 := card_fixed_dvd_onNormalCentralQuotient (orthogonalDerived Q) (scalarSigns Q) ψ hN hZ
  rw [hidx] at h1
  refine h1.trans ?_
  rw [mul_assoc]
  exact Nat.mul_dvd_mul_left 4 (Nat.mul_dvd_mul_left _ h.card_dvd)

theorem u42_omega_fixed_bounds (Q : QuadraticForm K V) (h2 : (2 : K) ≠ 0)
    (hidx : (orthogonalDerived Q).index = 4) (ψ : MulAut (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hN : (orthogonalDerived Q).map ψ.toMonoidHom = orthogonalDerived Q)
    (hZ : (scalarSigns Q).map ψ.toMonoidHom = scalarSigns Q)
    {J : Subgroup ↥(fixedSubgroup (onNormalCentralQuotient (orthogonalDerived Q) (scalarSigns Q)
      ψ hN hZ))}
    (h : U42Hyp (onNormalCentralQuotient (orthogonalDerived Q) (scalarSigns Q) ψ hN hZ) J) :
    25920 ∣ Nat.card (fixedSubgroup ψ) ∧ Nat.card (fixedSubgroup ψ) ∣ 414720 ∧
      (Odd (finrank K V) → Nat.card (fixedSubgroup ψ) ∣ 207360) := by
  obtain ⟨h1, h3⟩ := u42_omega_fixed_constraints Q hidx ψ hN hZ h
  refine ⟨h1, ?_, fun hodd => ?_⟩
  · refine h3.trans ?_
    have := Nat.mul_dvd_mul_right
      (Nat.mul_dvd_mul_left 4 (u42_card_scalarSigns_subgroupOf_dvd_two Q)) 51840
    have e : 4 * 2 * 51840 = 414720 := by norm_num
    rw [e] at this
    exact this
  · refine h3.trans ?_
    rw [card_scalarSigns_subgroupOf_orthogonalDerived_of_odd h2 Q hodd]

end Orthogonal

section Intertwine

theorem U42Hyp.of_intertwining {G H : Type} [Group G] [Group H] [Finite G] (e : G ≃* H)
    (α : MulAut G) (β : MulAut H) (h : ∀ x, e (α x) = β (e x))
    {J : Subgroup ↥(fixedSubgroup α)} (hJ : U42Hyp α J) :
    ∃ J' : Subgroup ↥(fixedSubgroup β), U42Hyp β J' := by
  have hβ : MulAut.congr e α = β := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    change e (α (e.symm (e x))) = β (e x)
    rw [e.symm_apply_apply, h]
  subst hβ
  exact ⟨_, U42Hyp.congr e α J hJ⟩

theorem U42Hyp.exists_of_eq {S : Type} [Group S] {σ σ' : MulAut S} (h : σ = σ')
    {J : Subgroup ↥(fixedSubgroup σ)} (hJ : U42Hyp σ J) :
    ∃ J' : Subgroup ↥(fixedSubgroup σ'), U42Hyp σ' J' := by
  subst h
  exact ⟨J, hJ⟩

end Intertwine

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
