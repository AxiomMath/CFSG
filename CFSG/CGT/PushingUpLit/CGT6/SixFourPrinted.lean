module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.CGT6.SixSixteenPR
public import CFSG.CGT.PushingUpLit.SixThreeV

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open CFSG.Assembly (KProper InCatalog)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem commutatorElement_central_mul {Q : Type*} [Group Q] {z w : Q}
    (hz : z ∈ Subgroup.center Q) (hw : w ∈ Subgroup.center Q) (x y : Q) :
    ⁅z * x, w * y⁆ = ⁅x, y⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  calc z * x * (w * y) * (z * x)⁻¹ * (w * y)⁻¹
      = z * (x * w * y * x⁻¹) * z⁻¹ * y⁻¹ * w⁻¹ := by group
    _ = (x * w * y * x⁻¹) * z * z⁻¹ * y⁻¹ * w⁻¹ := by rw [← hz' (x * w * y * x⁻¹)]
    _ = (w * x * y * x⁻¹ * y⁻¹) * w⁻¹ := by rw [hw' x]; group
    _ = w * (x * y * x⁻¹ * y⁻¹) * w⁻¹ := by group
    _ = (x * y * x⁻¹ * y⁻¹) * w * w⁻¹ := by rw [← hw' (x * y * x⁻¹ * y⁻¹)]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem isSubnormal_le_center_or_eq_top_of_quasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) {S : Subgroup Q} (hS : S.IsSubnormal) :
    S ≤ Subgroup.center Q ∨ S = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  have h1 : (S.map (QuotientGroup.mk' (Subgroup.center Q))).IsSubnormal :=
    hS.map (QuotientGroup.mk'_surjective _)
  rcases h1.eq_bot_or_top_of_isSimpleGroup hsimple with hbot | htop
  · left
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  · right
    have hsup : S ⊔ Subgroup.center Q = ⊤ := by
      have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) S
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
      exact h2.symm
    have hle : commutator Q ≤ S := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      have hx : x ∈ S ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top x
      have hy : y ∈ S ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top y
      obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
      obtain ⟨n', hn', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
      have e : ⁅n * z, n' * z'⁆ = ⁅n, n'⁆ := by
        rw [Subgroup.mem_center_iff.mp hz n, Subgroup.mem_center_iff.mp hz' n']
        exact commutatorElement_central_mul hz hz' n n'
      rw [e, commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem hn hn') (S.inv_mem hn)) (S.inv_mem hn')
    rw [hperf.commutator_eq_top] at hle
    exact top_le_iff.mp hle

theorem not_comm_of_simple_card_sixty {S : Type*} [Group S] [IsSimpleGroup S] [Finite S]
    (hc : Nat.card S = 60) : ¬ ∀ a b : S, a * b = b * a := by
  intro hcomm
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (by rw [hc]; norm_num)
  have hN : (Subgroup.zpowers s).Normal :=
    ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers s) with h | h
  · have hs1 : s = 1 := Subgroup.zpowers_eq_bot.mp h
    rw [hs1, orderOf_one] at hs
    omega
  · have h2 : Nat.card (Subgroup.zpowers s) = Nat.card S := by
      rw [h]
      exact Subgroup.card_top
    rw [Nat.card_zpowers, hs, hc] at h2
    omega

theorem isSubnormal_of_clause [Finite G] {Y R U₀ X : Subgroup G} [R.Normal]
    (hY : IsShortGroup ↥Y) (hcR : Subgroup.centralizer (R : Set G) ≤ R)
    (hR : IsSylowOf 2 R (centralizerModCore Y)) (hU₀2 : IsPGroup 2 U₀)
    (hU : ⁅oTwoIn Y, Y⁆ ≤ U₀) (hYU : Y ≤ Subgroup.normalizer (U₀ : Set G))
    (hYs : (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G))).IsSubnormal) (hYX : Y ≤ X)
    (hXU : X ≤ Subgroup.normalizer ((⁅oTwoIn Y, Y⁆ : Subgroup G) : Set G)) :
    (Y.subgroupOf X).IsSubnormal := by
  have hR2 : IsPGroup 2 R := hR.2.1
  have hU₀C : U₀ ≤ centralizerModCore Y := by
    obtain ⟨hnorm, hcomm, -⟩ :=
      commutator_eq_U_of_isSubnormal hY hU₀2 hYU hYU Subgroup.le_normalizer hYs
    exact fun g hg => ⟨hnorm hg, fun x hx => hcomm (Subgroup.commutator_mem_commutator hg hx)⟩
  have hU₀R : U₀ ≤ R := by
    have hP2 : IsPGroup 2 (R ⊔ U₀ : Subgroup G) := hR2.to_sup_of_normal_left hU₀2
    have hPC : R ⊔ U₀ ≤ centralizerModCore Y := sup_le hR.1 hU₀C
    exact le_sup_right.trans (Nine.le_of_isSylowOf_of_le hR hP2 le_sup_left hPC)
  obtain ⟨hRU, -, -, -⟩ := step_two hY hR2 hcR hR.1
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.normalizer_eq_top R]
    exact le_top
  let A : Subgroup G := actsTrivially X R (⁅oTwoIn Y, Y⁆) hXU
  have hYA : Y ≤ A := fun y hy => by
    refine ⟨hYX hy, fun r hr => ?_⟩
    have h1 : ⁅r, y⁆ ∈ ⁅R, Y⁆ := Subgroup.commutator_mem_commutator hr hy
    rw [hRU] at h1
    rw [← commutatorElement_inv]
    exact (⁅oTwoIn Y, Y⁆).inv_mem h1
  have hAX : A ≤ X := fun a ha => ha.1
  have hXA : X ≤ Subgroup.normalizer (A : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun h =>
      ⟨fun hh => conj_mem_actsTrivially hXR hXU hg hh, fun hh => by
        have := conj_mem_actsTrivially hXR hXU (X.inv_mem hg) hh
        simpa [mul_assoc] using this⟩
  have hconj : ∀ a ∈ A, ∀ u ∈ U₀, a * u * a⁻¹ ∈ U₀ := by
    intro a ha u hu
    have h1 : ⁅a, u⁆ ∈ ⁅oTwoIn Y, Y⁆ := ha.2 u (hU₀R hu)
    have e : a * u * a⁻¹ = ⁅a, u⁆ * u := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact U₀.mul_mem (hU h1) hu
  have hAN : A ≤ Subgroup.normalizer (U₀ : Set G) := fun a ha =>
    Subgroup.mem_normalizer_iff.mpr fun u =>
      ⟨hconj a ha u, fun hu => by
        have := hconj a⁻¹ (A.inv_mem ha) _ hu
        simpa [mul_assoc] using this⟩
  have hYsA : (Y.subgroupOf A).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hAN hYs
  have hAsX : (A.subgroupOf X).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hAX).mpr hXA).isSubnormal
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans hYA hAX hYsA hAsX

end CFSG.CGT.PushingUpLit.CGT6
