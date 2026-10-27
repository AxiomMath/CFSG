module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open Subgroup

variable {G : Type*} [Group G]

theorem pow_three_eq_one_of_mem_closure {S : Set G} (hcomm : S.Pairwise Commute)
    (hS : ∀ s ∈ S, s ^ 3 = 1) {g : G} (hg : g ∈ closure S) : g ^ 3 = 1 := by
  have hab : IsMulCommutative (closure S) := isMulCommutative_closure hcomm
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [(show Commute x y from hxy).mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem isPGroup_closure_cycle {u v w y : G} (huv : u * v = v * u) (huw : u * w = w * u)
    (hvw : v * w = w * v) (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) (hw : w ^ 3 = 1) (hy : y ^ 3 = 1)
    (h1 : y * u * y⁻¹ = v) (h2 : y * v * y⁻¹ = w) (h3 : y * w * y⁻¹ = u) :
    IsPGroup 3 (closure ({u, v, w, y} : Set G)) := by
  set S : Set G := {u, v, w} with hSdef
  have hcomm : S.Pairwise Commute := by
    intro a ha b hb _
    simp only [hSdef, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | exact huv | exact huw | exact hvw
      | exact huv.symm | exact huw.symm | exact hvw.symm
  have hS3 : ∀ s ∈ S, s ^ 3 = 1 := by
    intro s hs
    simp only [hSdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact hu
    · exact hv
    · exact hw
  set E : Subgroup G := closure S with hEdef
  have hEp : IsPGroup 3 E := fun g =>
    ⟨1, Subtype.ext (by simpa using pow_three_eq_one_of_mem_closure hcomm hS3 g.2)⟩
  have himage : (MulAut.conj y : G →* G) '' S = S := by
    ext a
    simp only [hSdef, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rcases hb with rfl | rfl | rfl
      · right; left; exact h1
      · right; right; exact h2
      · left; exact h3
    · rintro (rfl | rfl | rfl)
      · exact ⟨w, Or.inr (Or.inr rfl), h3⟩
      · exact ⟨u, Or.inl rfl, h1⟩
      · exact ⟨v, Or.inr (Or.inl rfl), h2⟩
  have hmap : E.map (MulAut.conj y).toMonoidHom = E := by
    rw [hEdef, MonoidHom.map_closure]
    congr 1
  have hyN : y ∈ normalizer (E : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    have key : y * h * y⁻¹ ∈ E.map (MulAut.conj y).toMonoidHom ↔ h ∈ E :=
      Subgroup.mem_map_iff_mem (MulAut.conj y).injective
    rw [hmap] at key
    exact key.symm
  have hYp : IsPGroup 3 (zpowers y) := by
    intro g
    obtain ⟨k, hk⟩ := g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have hsup : IsPGroup 3 ↥(E ⊔ zpowers y) :=
    IsPGroup.to_sup_of_normal_left' hEp hYp ((zpowers_le).2 hyN)
  refine hsup.to_le (closure_le _ |>.2 ?_)
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact mem_sup_left (subset_closure (by simp [hSdef]))
  · exact mem_sup_left (subset_closure (by simp [hSdef]))
  · exact mem_sup_left (subset_closure (by simp [hSdef]))
  · exact mem_sup_right (mem_zpowers _)

theorem not_isCyclic_of_four_cubes {H : Type*} [Group H] [Finite H] {a b c d : H}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) (hd : d ^ 3 = 1) (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : ¬ IsCyclic H := by
  intro hcyc
  classical
  haveI := Fintype.ofFinite H
  have hle := IsCyclic.card_pow_eq_one_le (α := H) (n := 3) (by norm_num)
  have hsub : ({a, b, c, d} : Finset H) ⊆ Finset.univ.filter (fun x : H => x ^ 3 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have h4 : ({a, b, c, d} : Finset H).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
