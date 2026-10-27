module

public import CFSG.CGT.PushingUpLit.SixThreeC
public import CFSG.GroupTheory.ConjugatePairSubnormality

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_of_isSubnormal_of_le [Finite G] {Y D H : Subgroup G}
    (hNo : SubTwo.NoTwoQuotient Y) (hD : IsPGroup 2 D)
    (hYD : Y ≤ Subgroup.normalizer (D : Set G)) (hYH : Y ≤ H) (hDH : D ≤ H)
    (hs : (Y.subgroupOf H).IsSubnormal) : D ≤ Subgroup.normalizer (Y : Set G) :=
  SubTwo.le_normalizer_of_isSubnormal_sup hNo hD hYD
    (CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (sup_le hYH hDH) hs)

theorem commutator_le_oTwoIn_of_normalizes {Y D : Subgroup G} (hD : IsPGroup 2 D)
    (hDY : D ≤ Subgroup.normalizer (Y : Set G)) (hYD : Y ≤ Subgroup.normalizer (D : Set G)) :
    ⁅D, Y⁆ ≤ oTwoIn Y := by
  have h1 : ⁅D, Y⁆ ≤ Y := Subgroup.le_normalizer_iff_commutator_le_right.mp hDY
  have h2 : ⁅D, Y⁆ ≤ D := Subgroup.le_normalizer_iff_commutator_le_left.mp hYD
  have hDY' : D ⊓ Y ≤ oTwoIn Y :=
    le_oTwoIn_of_isPGroup inf_le_right (hD.to_le inf_le_left)
      (le_trans (le_inf hYD Subgroup.le_normalizer) Subgroup.inf_normalizer_le_normalizer_inf)
  exact fun x hx => hDY' ⟨h2 hx, h1 hx⟩

theorem commutator_eq_U_of_isSubnormal [Finite G] {Y D H : Subgroup G} (hY : IsShortGroup ↥Y)
    (hD : IsPGroup 2 D) (hYD : Y ≤ Subgroup.normalizer (D : Set G)) (hYH : Y ≤ H) (hDH : D ≤ H)
    (hs : (Y.subgroupOf H).IsSubnormal) :
    D ≤ Subgroup.normalizer (Y : Set G) ∧ ⁅D, Y⁆ ≤ oTwoIn Y ∧
      (⁅D, Y⁆ = ⊥ ∨ ⁅D, Y⁆ = ⁅oTwoIn Y, Y⁆) := by
  have hNo := SubTwo.noTwoQuotient_of_oResidualTwo hY.residual_eq
  have hDY := le_normalizer_of_isSubnormal_of_le hNo hD hYD hYH hDH hs
  have hle := commutator_le_oTwoIn_of_normalizes hD hDY hYD
  refine ⟨hDY, hle, ?_⟩
  by_cases hbot : ⁅D, Y⁆ = ⊥
  · exact Or.inl hbot
  · exact Or.inr (commutator_eq_U hY hD hYD hle hbot)

theorem stabSeries_inf_le [Finite G] {V Q : Subgroup G} [V.Normal] [Q.Normal]
    (hQ2 : IsPGroup 2 Q) (hchar : Subgroup.centralizer (Q : Set G) ≤ Q)
    (hmax : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ Q) :
    stabSeries V (Q ⊓ Subgroup.centralizer (V : Set G)) ≤ Q := by
  set Q₁ : Subgroup G := Q ⊓ Subgroup.centralizer (V : Set G) with hQ₁
  refine hmax _ inferInstance ?_
  refine isPGroup_two_of_no_odd_prime_orderOf fun x hx p hp hp2 hord => ?_
  set R := Subgroup.zpowers x with hR
  have hRS : R ≤ stabSeries V Q₁ := Subgroup.zpowers_le.mpr hx
  have hodd : Odd (orderOf x) := hord ▸ hp.odd_of_ne_two hp2
  have hRN : ∀ N : Subgroup G, N.Normal → R ≤ Subgroup.normalizer (N : Set G) := fun N _ => by
    rw [Subgroup.normalizer_eq_top N]
    exact le_top
  have hQ₁2 : IsPGroup 2 Q₁ := hQ2.to_le inf_le_left
  have hcop₁ := coprime_card_zpowers_of_odd hodd hQ₁2
  have hdouble₁ : ⁅⁅Q₁, R⁆, R⁆ = ⊥ := by
    have h1 : ⁅Q₁, R⁆ ≤ V := by
      refine Subgroup.commutator_le.mpr fun q hq r hr => ?_
      rw [← commutatorElement_inv]
      exact V.inv_mem ((hRS hr).2 q hq)
    have h2 : ⁅V, R⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun r hr => (hRS hr).1
    exact eq_bot_iff.mpr ((Subgroup.commutator_mono h1 le_rfl).trans h2.le)
  have hbot₁ := CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot Q₁ R
    (hRN Q₁ inferInstance) hcop₁ hdouble₁
  have hQR : ⁅Q, R⁆ ≤ Q₁ := by
    refine Subgroup.commutator_le.mpr fun q hq r hr => ?_
    have hrC : r ∈ Subgroup.centralizer (V : Set G) := (hRS hr).1
    refine ⟨?_, ?_⟩
    · have h1 : q * (r * q⁻¹ * r⁻¹) = ⁅q, r⁆ := by
        simp only [commutatorElement_def]
        group
      rw [← h1]
      exact Q.mul_mem hq ((inferInstance : Q.Normal).conj_mem _ (Q.inv_mem hq) r)
    · have h1 : (q * r * q⁻¹) * r⁻¹ = ⁅q, r⁆ := by
        simp only [commutatorElement_def]
      rw [← h1]
      exact (Subgroup.centralizer (V : Set G)).mul_mem
        ((inferInstance : (Subgroup.centralizer (V : Set G)).Normal).conj_mem _ hrC q)
        ((Subgroup.centralizer (V : Set G)).inv_mem hrC)
  have hdouble : ⁅⁅Q, R⁆, R⁆ = ⊥ :=
    eq_bot_iff.mpr ((Subgroup.commutator_mono hQR le_rfl).trans hbot₁.le)
  have hcop := coprime_card_zpowers_of_odd hodd hQ2
  have hbot := CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot Q R
    (hRN Q inferInstance) hcop hdouble
  have hxc : x ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hQR' : Q ≤ Subgroup.centralizer (R : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    exact ((Subgroup.mem_centralizer_iff.mp (hQR' hq)) x (Subgroup.mem_zpowers x)).symm
  have hxQ : x ∈ Q := hchar hxc
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨x, hxQ⟩
  rw [Subgroup.orderOf_mk, hord] at hk
  have := (Nat.Prime.pow_eq_iff hp).mp hk.symm
  exact hp2 this.1.symm

theorem centralizer_le_centralizerModCore [Finite G] {Q V Y H : Subgroup G} [Q.Normal] [V.Normal]
    (hQ2 : IsPGroup 2 Q) (hchar : Subgroup.centralizer (Q : Set G) ≤ Q)
    (hmax : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ Q) (hVQ : V ≤ Q)
    (hVC : V ≤ Subgroup.centralizer (V : Set G)) (hY : IsShortGroup ↥Y) (hYH : Y ≤ H)
    (hCH : Subgroup.centralizer (V : Set G) ≤ H) (hs : (Y.subgroupOf H).IsSubnormal)
    (hne : ⁅V, Y⁆ ≠ ⊥) : Subgroup.centralizer (V : Set G) ≤ centralizerModCore Y := by
  set Q₁ : Subgroup G := Q ⊓ Subgroup.centralizer (V : Set G) with hQ₁
  have hNo := SubTwo.noTwoQuotient_of_oResidualTwo hY.residual_eq
  have hYN : ∀ N : Subgroup G, N.Normal → Y ≤ Subgroup.normalizer (N : Set G) := fun N _ => by
    rw [Subgroup.normalizer_eq_top N]
    exact le_top
  have hQ₁2 : IsPGroup 2 Q₁ := hQ2.to_le inf_le_left
  have hQ₁H : Q₁ ≤ H := inf_le_right.trans hCH
  have hVQ₁ : V ≤ Q₁ := le_inf hVQ hVC
  have hVH : V ≤ H := hVC.trans hCH
  have hV2 : IsPGroup 2 V := hQ2.to_le hVQ
  obtain ⟨-, -, hVU⟩ := commutator_eq_U_of_isSubnormal hY hV2 (hYN V inferInstance) hYH hVH hs
  obtain ⟨hQ₁Y, -, hQ₁U⟩ :=
    commutator_eq_U_of_isSubnormal hY hQ₁2 (hYN Q₁ inferInstance) hYH hQ₁H hs
  have hVU' : ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆ := hVU.resolve_left hne
  have hQ₁ne : ⁅Q₁, Y⁆ ≠ ⊥ := fun h => hne (eq_bot_iff.mpr
    ((Subgroup.commutator_mono hVQ₁ le_rfl).trans h.le))
  have hQ₁U' : ⁅Q₁, Y⁆ = ⁅oTwoIn Y, Y⁆ := hQ₁U.resolve_left hQ₁ne
  have hVV : ⁅V, Y⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp (hYN V inferInstance)
  have hQV : ⁅Q₁, Y⁆ ≤ V := by rw [hQ₁U', ← hVU']; exact hVV
  have hstab : ⁅Subgroup.centralizer (V : Set G), Y⁆ ≤ stabSeries V Q₁ :=
    commutator_le_stabSeries hQV le_rfl
  have hCQ : ⁅Subgroup.centralizer (V : Set G), Y⁆ ≤ Q₁ :=
    le_inf ((hstab.trans (stabSeries_inf_le hQ2 hchar hmax)))
      (Subgroup.commutator_le_left _ _)
  exact le_centralizerModCore_of_commutator_le hNo hQ₁2 hQ₁Y hCQ

end CFSG.CGT.PushingUpLit.CGT6
