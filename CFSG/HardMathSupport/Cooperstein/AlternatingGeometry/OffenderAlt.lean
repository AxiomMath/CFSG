module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderShape
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

theorem evenWeight_eq_evenVec (n : ℕ) : evenWeight n = Offender.evenVec (Fin n) :=
  AddSubgroup.ext fun _ => Iff.rfl

@[expose] noncomputable def altFix (n : ℕ) (E : Subgroup (Perm (Fin n))) : AddSubgroup (altHeart n) :=
  ((Offender.FixUp E).addSubgroupOf (evenWeight n)).map (QuotientAddGroup.mk' (evenWeightOnes n))

theorem evenWeightOnes_le_FixUp (n : ℕ) (E : Subgroup (Perm (Fin n))) :
    evenWeightOnes n ≤ (Offender.FixUp E).addSubgroupOf (evenWeight n) := by
  intro x hx
  have hx' : (x : Fin n → ZMod 2) ∈ AddSubgroup.zmultiples (allOnes n) := hx
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hx'
  refine ⟨x.2, fun g _ => Or.inl fun i => ?_⟩
  show (x : Fin n → ZMod 2) (g i) = (x : Fin n → ZMod 2) i
  rw [← hk]
  simp [allOnes]

theorem index_altFix (n : ℕ) (E : Subgroup (Perm (Fin n))) :
    (altFix n E).index = Offender.offIdx E := by
  have hker : (QuotientAddGroup.mk' (evenWeightOnes n)).ker ≤
      (Offender.FixUp E).addSubgroupOf (evenWeight n) := by
    rw [QuotientAddGroup.ker_mk']; exact evenWeightOnes_le_FixUp n E
  unfold altFix
  rw [AddSubgroup.index_map, sup_eq_left.2 hker,
    AddMonoidHom.range_eq_top_of_surjective _ (QuotientAddGroup.mk'_surjective _),
    AddSubgroup.index_top, mul_one]
  unfold Offender.offIdx
  rw [evenWeight_eq_evenVec]

theorem mem_evenWeightOnes_iff (n : ℕ) (x : evenWeight n) :
    x ∈ evenWeightOnes n ↔ ∃ c : ZMod 2, ∀ i, (x : Fin n → ZMod 2) i = c := by
  constructor
  · intro hx
    have hx' : (x : Fin n → ZMod 2) ∈ AddSubgroup.zmultiples (allOnes n) := hx
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hx'
    refine ⟨(k : ZMod 2), fun i => ?_⟩
    rw [← hk]
    simp [allOnes]
  · rintro ⟨c, hc⟩
    show (x : Fin n → ZMod 2) ∈ AddSubgroup.zmultiples (allOnes n)
    rw [AddSubgroup.mem_zmultiples_iff]
    rcases Offender.zmod2_cases c with rfl | rfl
    · exact ⟨0, funext fun i => by simp [hc i]⟩
    · exact ⟨1, funext fun i => by simp [hc i, allOnes]⟩

theorem zmod2_sub_aux (a b c : ZMod 2) (h : a + b = c) : a = b + c := by
  revert a b c; decide

theorem zmod2_sub_aux' (a b t : ZMod 2) (h : a = b + t) : -a + b = t := by
  subst h; revert b t; decide

theorem mem_altFix_iff (n : ℕ) (E : Subgroup (Perm (Fin n))) (v : altHeart n) :
    v ∈ altFix n E ↔ ∀ g ∈ E, ∀ x : evenWeight n, (QuotientAddGroup.mk x : altHeart n) = v →
      (QuotientAddGroup.mk (evenWeightPerm g x) : altHeart n) = v := by
  constructor
  · rintro ⟨x0, hx0, rfl⟩ g hg x hx
    obtain ⟨c1, hc1⟩ := (mem_evenWeightOnes_iff n _).1 (QuotientAddGroup.eq.1 hx)
    have hxi : ∀ i, (x : Fin n → ZMod 2) i = (x0 : Fin n → ZMod 2) i + c1 := by
      intro i
      have := hc1 i
      exact zmod2_sub_aux _ _ _ (by simpa using this)
    obtain ⟨d, hd⟩ : ∃ d : ZMod 2, ∀ i, (x0 : Fin n → ZMod 2) (g⁻¹ i) =
        (x0 : Fin n → ZMod 2) i + d := by
      rcases hx0.2 g⁻¹ (E.inv_mem hg) with h | h
      · exact ⟨0, fun i => by simpa using h i⟩
      · exact ⟨1, h⟩
    show (QuotientAddGroup.mk (evenWeightPerm g x) : altHeart n) = QuotientAddGroup.mk x0
    rw [QuotientAddGroup.eq, mem_evenWeightOnes_iff]
    refine ⟨d + c1, fun i => ?_⟩
    show -((x : Fin n → ZMod 2) (g⁻¹ i)) + (x0 : Fin n → ZMod 2) i = d + c1
    apply zmod2_sub_aux'
    rw [hxi, hd]; ring
  · intro h
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
    refine ⟨x, ?_, rfl⟩
    refine ⟨x.2, fun g hg => ?_⟩
    have h1 := h g⁻¹ (E.inv_mem hg) x rfl
    obtain ⟨c, hc⟩ := (mem_evenWeightOnes_iff n _).1 (QuotientAddGroup.eq.1 h1)
    have hx : ∀ i, (x : Fin n → ZMod 2) (g i) = (x : Fin n → ZMod 2) i + c := by
      intro i
      have := hc i
      exact zmod2_sub_aux _ _ _ (by simpa [evenWeightPerm] using this)
    rcases Offender.zmod2_cases c with rfl | rfl
    · exact Or.inl fun i => by simpa using hx i
    · exact Or.inr fun i => hx i

theorem offender_shape_altHeart {n : ℕ} (hn : n = 7 ∨ 9 ≤ n) (E : Subgroup (Perm (Fin n)))
    (hE : ∀ g ∈ E, g * g = 1) (hoff : (altFix n E).index ≤ Nat.card E) :
    Offender.OffenderShapeConcl E := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [index_altFix] at hoff
  exact Offender.offender_shape hE hoff (by simpa using hn)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
