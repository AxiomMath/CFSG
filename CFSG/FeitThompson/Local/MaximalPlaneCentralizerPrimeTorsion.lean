module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p : ℕ} {R : Type*} [Group R] {E : Subgroup R}

theorem mem_of_maximal_of_mem_centralizer_of_pow_eq_one
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E) {x : R}
    (hx : x ∈ centralizer (E : Set R)) (hxp : x ^ p = 1) : x ∈ E := by
  have hEcomm := hE.prop.1
  have hcomm : ∀ a ∈ (E : Set R) ∪ {x}, ∀ b ∈ (E : Set R) ∪ {x}, a * b = b * a := by
    rintro a (ha | ha) b (hb | hb)
    · exact setLike_mul_comm ha hb
    · rw [Set.mem_singleton_iff] at hb
      exact hb ▸ (mem_centralizer_iff.1 hx) a ha
    · rw [Set.mem_singleton_iff] at ha
      exact ha ▸ ((mem_centralizer_iff.1 hx) b hb).symm
    · rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
  have hclos : IsMulCommutative (closure ((E : Set R) ∪ {x})) :=
    Subgroup.isMulCommutative_closure fun a ha b hb _ => hcomm a ha b hb
  have hES : E ≤ closure ((E : Set R) ∪ {x}) := fun a ha => subset_closure (Or.inl ha)
  have hexp : ∀ y ∈ closure ((E : Set R) ∪ {x}), y ^ p = 1 := by
    intro y hy
    induction hy using closure_induction with
    | mem z hz =>
        rcases hz with hz | hz
        · exact hE.prop.2 z hz
        · rw [Set.mem_singleton_iff] at hz
          exact hz ▸ hxp
    | one => exact one_pow p
    | mul a b ha hb iha ihb =>
        have hab : Commute a b := setLike_mul_comm (s := closure ((E : Set R) ∪ {x})) ha hb
        rw [hab.mul_pow, iha, ihb, one_mul]
    | inv a _ iha => rw [inv_pow, iha, inv_one]
  exact hE.le_of_ge ⟨hclos, hexp⟩ hES (subset_closure (Or.inr rfl))

theorem setOf_pow_eq_one_centralizer_of_maximal
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E) :
    {x ∈ (centralizer (E : Set R) : Set R) | x ^ p = 1} = (E : Set R) := by
  have hEcomm := hE.prop.1
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro x ⟨hx, hxp⟩
    exact mem_of_maximal_of_mem_centralizer_of_pow_eq_one hE hx hxp
  · intro x hx
    exact ⟨Subgroup.le_centralizer E hx, hE.prop.2 x hx⟩

theorem closure_setOf_pow_eq_one_centralizer_of_maximal
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E) :
    closure {x ∈ (centralizer (E : Set R) : Set R) | x ^ p = 1} = E := by
  rw [setOf_pow_eq_one_centralizer_of_maximal hE, closure_eq]

theorem setOf_pow_eq_one_center_subset_of_maximal
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E) :
    {z ∈ (center R : Set R) | z ^ p = 1} ⊆ (E : Set R) := by
  rintro z ⟨hz, hzp⟩
  exact mem_of_maximal_of_mem_centralizer_of_pow_eq_one hE
    (Subgroup.center_le_centralizer _ hz) hzp

theorem elementaryAbelianPRank_centralizer_of_maximal [Finite R] (hp : p.Prime)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hcard : Nat.card E = p ^ 2) :
    elementaryAbelianPRank p (centralizer (E : Set R)) = 2 := by
  have hEcomm := hE.prop.1
  have hEC : E ≤ centralizer (E : Set R) := Subgroup.le_centralizer E
  refine Nat.le_antisymm (elementaryAbelianPRank_le fun d hd => ?_)
    (le_elementaryAbelianPRank hp.one_lt ?_)
  ·
    obtain ⟨A, hAcomm, hAexp, hAcard⟩ := (mem_elementaryAbelianRanks_iff_exists_subgroup hp).1 hd
    have hmap : A.map (centralizer (E : Set R)).subtype ≤ E := by
      rintro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      refine (setOf_pow_eq_one_centralizer_of_maximal hE).subset ⟨a.2, ?_⟩
      simpa using congrArg Subtype.val (hAexp a ha)
    have hcard2 : Nat.card (A.map (centralizer (E : Set R)).subtype) = p ^ d := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hAcard]
    have hdvd : p ^ d ∣ p ^ 2 := by
      rw [← hcard, ← hcard2]
      exact Subgroup.card_dvd_of_le hmap
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
  ·
    let _ : CommGroup E := IsMulCommutative.instCommGroup
    obtain ⟨f⟩ := nonempty_mulEquiv_pi_of_exponent (d := 2) (G := (E : Subgroup R)) hp
      (fun x => Subtype.ext (hE.prop.2 x.1 x.2)) hcard
    exact mem_elementaryAbelianRanks.2
      ⟨E.subgroupOf (centralizer (E : Set R)), ⟨(subgroupOfEquivOfLe hEC).trans f⟩⟩

end

end CFSG.FeitThompson
