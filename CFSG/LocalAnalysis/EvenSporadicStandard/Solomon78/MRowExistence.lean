module

public import CFSG.Monster.Existence.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.General
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimSylow

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Monster.Existence

theorem eq_one_or_eq_of_card_eq_two {A : Type*} [Group A] (hc : Nat.card A = 2) {x : A}
    (hx : x ≠ 1) (y : A) : y = 1 ∨ y = x := by
  obtain ⟨u, v, huv, hU⟩ := Nat.card_eq_two_iff.1 hc
  have hm : ∀ w : A, w = u ∨ w = v := fun w => by
    have : w ∈ ({u, v} : Set A) := hU ▸ Set.mem_univ w
    simpa using this
  rcases hm 1 with h1 | h1 <;> rcases hm x with h2 | h2 <;> rcases hm y with h3 | h3 <;>
    simp_all

variable {G : Type} [Group G]

theorem centerInvolutionsAt_of_isTwoACentralizer {a : G} (ha : orderOf a = 2)
    (h : IsTwoACentralizer a) {z : G} (hza : z * a = a * z)
    (hzc : ∀ y : G, y * a = a * y → z * y = y * z) : z = 1 ∨ z = a := by
  obtain ⟨-, hZ, -⟩ := h
  have hz : z ∈ (center (cent a)).map (cent a).subtype := by
    refine Subgroup.mem_map.2 ⟨⟨z, mem_centralizer_singleton_iff.2 hza⟩, ?_, rfl⟩
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hzc g (mem_centralizer_singleton_iff.1 g.2)).symm
  rw [hZ] at hz
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hz
  rcases zpow_eq_one_or_self_of_orderOf_eq_two ha k with h1 | h1
  · exact Or.inl (hk.symm.trans h1)
  · exact Or.inr (hk.symm.trans h1)

theorem centerInvolutionsAt_of_isTwoBCentralizer {a : G} (ha : orderOf a = 2)
    (h : IsTwoBCentralizer a) {z : G}
    (hzc : ∀ y : G, y * a = a * y → z * y = y * z) : z = 1 ∨ z = a := by
  obtain ⟨hext, -, hself, -, -, -⟩ := h
  set Q : Subgroup (cent a) := pCore 2 (cent a) with hQ
  have hQ' : inSubgroup (pCore 2) (cent a) = Q.map (cent a).subtype := rfl
  have hQC : ∀ y ∈ Q.map (cent a).subtype, y * a = a * y := fun y hy =>
    mem_centralizer_singleton_iff.1 (map_subtype_le Q hy)
  have hzQ : z ∈ Q.map (cent a).subtype := by
    have : z ∈ centralizer (inSubgroup (pCore 2) (cent a) : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      rw [hQ'] at hy
      exact (hzc y (hQC y hy)).symm
    exact hQ' ▸ hself this
  have haQ : a ∈ Q.map (cent a).subtype := by
    have : a ∈ centralizer (inSubgroup (pCore 2) (cent a) : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      rw [hQ'] at hy
      exact hQC y hy
    exact hQ' ▸ hself this
  obtain ⟨qz, hqz, hqzz⟩ := hzQ
  obtain ⟨qa, hqa, hqaa⟩ := haQ
  have hqaa' : ((qa : cent a) : G) = a := hqaa
  have hqzz' : ((qz : cent a) : G) = z := hqzz
  have hxc : (⟨qa, hqa⟩ : Q) ∈ center Q := by
    rw [mem_center_iff]
    intro g
    refine Subtype.ext (Subtype.ext ?_)
    show ((g : cent a) : G) * ((qa : cent a) : G) = ((qa : cent a) : G) * ((g : cent a) : G)
    rw [hqaa']
    exact mem_centralizer_singleton_iff.1 (g : cent a).2
  have hyc : (⟨qz, hqz⟩ : Q) ∈ center Q := by
    rw [mem_center_iff]
    intro g
    refine Subtype.ext (Subtype.ext ?_)
    show ((g : cent a) : G) * ((qz : cent a) : G) = ((qz : cent a) : G) * ((g : cent a) : G)
    rw [hqzz']
    exact (hzc _ (mem_centralizer_singleton_iff.1 (g : cent a).2)).symm
  have hcard : Nat.card (center Q) = 2 := hext.2.2.2
  have hx1 : (⟨⟨qa, hqa⟩, hxc⟩ : center Q) ≠ 1 := by
    intro h1
    have h2 : qa = 1 := congrArg (fun w : center Q => ((w : Q) : cent a)) h1
    apply ne_one_of_orderOf_eq_two ha
    rw [← hqaa', h2]
    rfl
  rcases eq_one_or_eq_of_card_eq_two hcard hx1 ⟨⟨qz, hqz⟩, hyc⟩ with h1 | h1
  · left
    have h2 : qz = 1 := congrArg (fun w : center Q => ((w : Q) : cent a)) h1
    rw [← hqzz', h2]
    rfl
  · right
    have h2 : qz = qa := congrArg (fun w : center Q => ((w : Q) : cent a)) h1
    rw [← hqzz', h2, hqaa']

theorem centerInvolutions_of_clauses {a₀ z₀ : G}
    (hcls : ∀ t : G, orderOf t = 2 → IsConj a₀ t ∨ IsConj z₀ t)
    (hA : ∀ α : G, IsConj a₀ α → IsTwoACentralizer α)
    (hB : ∀ ζ : G, IsConj z₀ ζ → IsTwoBCentralizer ζ) : CenterInvolutions G := by
  intro a z ha hzz hza hzc
  rcases hcls a ha with h | h
  · exact centerInvolutionsAt_of_isTwoACentralizer ha (hA a h) hza hzc
  · exact centerInvolutionsAt_of_isTwoBCentralizer ha (hB a h) hzc

theorem involutionsCommute_of_clauses [Finite G] {a₀ z₀ : G} (ha₀ : orderOf a₀ = 2)
    (hcls : ∀ t : G, orderOf t = 2 → IsConj a₀ t ∨ IsConj z₀ t) : InvolutionsCommute G :=
  involutionsCommute_of_two_classes (fun x hx => (hcls x hx).imp IsConj.symm IsConj.symm) ha₀

end CFSG.EvenSporadicStandard.Solomon78
