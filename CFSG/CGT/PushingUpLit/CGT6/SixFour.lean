module

public import CFSG.CGT.PushingUpLit.NineChoiceJ
public import CFSG.CGT.PushingUpLit.SixThreeShort
public import CFSG.CGT.PushingUpLit.ThreeFromEightOneCore

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open CFSG.Assembly (KProper InCatalog)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

@[expose] def SixFourHyps [Finite G] (Y : Subgroup G) (T : Sylow 2 G) (R U₀ : Subgroup G) :
    Prop :=
  InClassX ↥Y ∧ Y = ⁅jIn (T : Subgroup G), Y⁆ ∧ IsSylowOf 2 R (centralizerModCore Y) ∧
    oTwoIn (Subgroup.normalizer (R : Set G)) = R ∧ ⁅oTwoIn Y, Y⁆ ≤ U₀ ∧
    U₀ ≤ (T : Subgroup G) ∧ Y ≤ Subgroup.normalizer (U₀ : Set G) ∧
    (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G))).IsSubnormal

@[expose] def SixFourConcl [Finite G] (Y : Subgroup G) : Prop :=
  ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ Arrow Y X

theorem le_normalizer_of_commutator_eq {Y J : Subgroup G} (h : ⁅J, Y⁆ = Y) :
    J ≤ Subgroup.normalizer (Y : Set G) := by
  have key : ∀ j ∈ J, ∀ y ∈ Y, j * y * j⁻¹ ∈ Y := by
    intro j hj y hy
    have h1 : ⁅j, y⁆ ∈ ⁅J, Y⁆ := Subgroup.commutator_mem_commutator hj hy
    rw [h] at h1
    have h2 : j * y * j⁻¹ = ⁅j, y⁆ * y := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact Y.mul_mem h1 hy
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key j hj y, fun hy => ?_⟩
  have := key j⁻¹ (J.inv_mem hj) _ hy
  simpa [mul_assoc] using this

theorem le_of_oTwoIn_normalizer_eq [Finite G] {R Q : Subgroup G} [Q.Normal] (hQ : IsPGroup 2 Q)
    (hR : oTwoIn (Subgroup.normalizer (R : Set G)) = R) : Q ≤ R := by
  have hR2 : IsPGroup 2 R := hR ▸ ThreeFromEight.isPGroup_oTwoIn _
  have hP : IsPGroup 2 (Q ⊔ R : Subgroup G) := hQ.to_sup_of_normal_left hR2
  have hQn : Subgroup.normalizer (Q : Set G) = ⊤ := Subgroup.normalizer_eq_top Q
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left Q R (by rw [hQn]; exact le_top)
  have hM : Q ⊓ Subgroup.normalizer (R : Set G) ≤ oTwoIn (Subgroup.normalizer (R : Set G)) := by
    refine le_oTwoIn_of_isPGroup inf_le_right (hQ.to_le inf_le_left) ?_
    exact le_trans (le_inf (by rw [hQn]; exact le_top) Subgroup.le_normalizer)
      Subgroup.inf_normalizer_le_normalizer_inf
  have key : (Q ⊔ R : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) ≤ R := by
    rintro x ⟨hxP, hxN⟩
    have hx : x ∈ (Q : Set G) * (R : Set G) := by
      rw [← hmul]
      exact hxP
    obtain ⟨q, hq, r, hr, rfl⟩ := hx
    have hrN : r ∈ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer hr
    have hqN : q ∈ Subgroup.normalizer (R : Set G) := by
      have := (Subgroup.normalizer (R : Set G)).mul_mem hxN
        ((Subgroup.normalizer (R : Set G)).inv_mem hrN)
      simpa using this
    have hqR : q ∈ R := by
      have := hM ⟨hq, hqN⟩
      rwa [hR] at this
    exact R.mul_mem hqR hr
  have h := Nine.eq_of_inf_normalizer_le hP le_sup_right key
  exact le_sup_left.trans h.ge

end CFSG.CGT.PushingUpLit.CGT6
