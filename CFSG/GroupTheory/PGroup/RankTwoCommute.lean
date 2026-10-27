module

public import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem two_le_pRank_of_commute {p : ℕ} [Fact p.Prime] {H : Subgroup G} {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) (hxp : orderOf x = p) (hyp : orderOf y = p)
    (hxy : Commute x y) (hyx : y ∉ Subgroup.zpowers x) :
    2 ≤ CFSG.Open.pRank p H := by
  have hp := Fact.out (p := p.Prime)
  have hxcard : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hxp]
  have hcomm : ∀ a ∈ Subgroup.zpowers x, a * y = y * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (hxy.zpow_left n).eq
  obtain ⟨hea, hcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute hxcard hyp hyx hcomm
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ H :=
    sup_le (Subgroup.zpowers_le.mpr hx) (Subgroup.zpowers_le.mpr hy)
  exact CFSG.SectionRank.le_pRank hp.one_lt hle hea (by simpa using hcard)

theorem isElemAbelian_sup_zpowers_of_mem_isElemAbelian {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H] {A : Subgroup H}
    (hA : CFSG.Open.IsElemAbelian p A) {x y : H} (hx : x ∈ A) (hy : y ∈ A)
    (hxord : orderOf x = p) (hyord : orderOf y = p)
    (hxy : y ∉ Subgroup.zpowers x) :
    CFSG.Open.IsElemAbelian p (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ∧
      Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup H) = p ^ 2 := by
  haveI : IsMulCommutative ↥A := hA.1
  have hcomm : ∀ a ∈ Subgroup.zpowers x, a * y = y * a := by
    intro a ha
    have haA : a ∈ A := Subgroup.zpowers_le.mpr hx ha
    exact congrArg Subtype.val (mul_comm' (⟨a, haA⟩ : A) ⟨y, hy⟩)
  have h := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (r := p) (X := Subgroup.zpowers x) (by rw [Nat.card_zpowers, hxord]) hyord hxy hcomm
  refine ⟨h.1, ?_⟩
  exact h.2

end CFSG.GroupTheory

namespace CFSG.RankTwoShapes

universe u

@[expose] def TwoRankLeTwo (Q : Type u) [Group Q] : Prop :=
  ∀ E : Subgroup Q, IsMulCommutative E → (∀ e ∈ E, e ^ 2 = 1) → Nat.card E ≤ 4

variable {Q : Type u} [Group Q] [Finite Q]

theorem sq_eq_one_mem_of_central_four (hrank : TwoRankLeTwo Q)
    (V : Subgroup Q) (hVZ : V ≤ Subgroup.center Q) (hVexp : ∀ v ∈ V, v ^ 2 = 1)
    (hVcard : Nat.card V = 4) (t : Q) (ht : t ^ 2 = 1) : t ∈ V := by
  by_contra htV
  let E := Subgroup.closure ((V : Set Q) ∪ {t})
  have hpair : ((V : Set Q) ∪ {t}).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact (Subgroup.mem_center_iff.mp (hVZ ha) b).symm
    · rw [Set.mem_singleton_iff] at hb; subst hb
      exact (Subgroup.mem_center_iff.mp (hVZ ha) b).symm
    · rw [Set.mem_singleton_iff] at ha; subst ha
      exact Subgroup.mem_center_iff.mp (hVZ hb) a
    · rw [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; exact Commute.refl _
  have hEcomm : IsMulCommutative E := Subgroup.isMulCommutative_closure hpair
  have hEexp : ∀ w ∈ E, w ^ 2 = 1 := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      rcases hw with hw | hw
      · exact hVexp w hw
      · rw [Set.mem_singleton_iff] at hw; rw [hw]; exact ht
    | one => exact one_pow 2
    | mul a b ha hb pa pb =>
      have hc : Commute a b :=
        congrArg (fun z : E => (z : Q)) (hEcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      rw [hc.mul_pow, pa, pb, one_mul]
    | inv a ha pa => rw [inv_pow, pa, inv_one]
  have hVE : V < E := by
    refine lt_of_le_of_ne (fun v hv => Subgroup.subset_closure (Or.inl hv)) ?_
    intro hVeq
    exact htV (hVeq ▸ Subgroup.subset_closure (Or.inr rfl))
  have hlt : Nat.card V < Nat.card E := Subgroup.card_lt_of_lt hVE
  have hle := hrank E hEcomm hEexp
  omega

end CFSG.RankTwoShapes
