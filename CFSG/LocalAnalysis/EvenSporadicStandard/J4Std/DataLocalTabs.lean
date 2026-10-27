module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataLocalFam
public import CFSG.Sporadic.J4.QTRankProof

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataLocal

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

attribute [local irreducible] invs commMasks prodTab fixList fixLists tabL

@[expose] def Tab (A : Subgroup J) : Set (List ℕ) := {t | ∃ a ∈ A, Acts a t}

@[expose] def elems (m : ℕ) : Set (List ℕ) :=
  {t | t = idT ∨ ∃ i < nInv, m.testBit i = true ∧ inv i = t}

theorem idT_mem_elems (m : ℕ) : idT ∈ elems m := Or.inl rfl

theorem elems_zero : elems 0 = {idT} := by
  ext t
  simp [elems]

theorem compT_idT_right {x : List ℕ} (hx : x.length = 11) : compT x idT = x := by
  unfold compT idT
  rw [List.map_map]
  apply List.ext_getElem (by simp [hx])
  intro n h1 h2
  have hn : n < 11 := by simpa [hx] using h2
  simp [Function.comp_def, actT_two_pow x hn, List.getElem?_eq_getElem h2]

theorem elems_ext (hT : chkTabs = true) {m i : ℕ}
    (hi : i ∈ cands m) :
    elems (ext m i) = elems m ∪ {t | ∃ s ∈ elems m, t = compT (inv i) s} := by
  obtain ⟨hiN, hmi, hcm⟩ := mem_cands.1 hi
  have hlen : (inv i).length = 11 :=
    (lenOK_iff (tabL_ok _ (mem_invs.1 (inv_mem hiN)).1)).1
  have hright : compT (inv i) idT = inv i := compT_idT_right hlen
  have hcomm : ∀ j, m.testBit j = true → j < nInv → commutes i j = true := fun j hj hjN => by
    rw [← commMasks_testBit hT hiN hjN]
    exact hcm j hj
  have hne : ∀ j, m.testBit j = true → i ≠ j := fun j hj hij => by
    rw [← hij, hmi] at hj
    exact absurd hj (by simp)
  ext t
  constructor
  · rintro (rfl | ⟨k, hk, hbit, rfl⟩)
    · exact Or.inl (Or.inl rfl)
    · rcases (testBit_ext m i k).1 hbit with h | rfl | ⟨j, hj, hjk⟩
      · exact Or.inl (Or.inr ⟨k, hk, h, rfl⟩)
      · exact Or.inr ⟨idT, Or.inl rfl, hright.symm⟩
      · obtain ⟨hjN, hjb⟩ := mem_bitIdx.1 hj
        obtain ⟨-, hprod⟩ := prod_spec hT hiN hjN (hne j hjb) (hcomm j hjb hjN)
        exact Or.inr ⟨inv j, Or.inr ⟨j, hjN, hjb, rfl⟩, by rw [← hjk, hprod]⟩
  · rintro (h | ⟨s, hs, rfl⟩)
    · rcases h with rfl | ⟨k, hk, hbit, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hk, (testBit_ext m i k).2 (Or.inl hbit), rfl⟩
    · rcases hs with rfl | ⟨j, hjN, hjb, rfl⟩
      · rw [hright]
        exact Or.inr ⟨i, hiN, (testBit_ext m i i).2 (Or.inr (Or.inl rfl)), rfl⟩
      · obtain ⟨hlt, hprod⟩ := prod_spec hT hiN hjN (hne j hjb) (hcomm j hjb hjN)
        rw [← hprod]
        exact Or.inr ⟨prodIdx i j, hlt, (testBit_ext m i _).2
          (Or.inr (Or.inr ⟨j, mem_bitIdx.2 ⟨hjN, hjb⟩, rfl⟩)), rfl⟩

theorem ncard_elems_le (m : ℕ) : (elems m).ncard ≤ (bitIdx m).length + 1 := by
  classical
  have hsub : elems m ⊆ ↑(insert idT (((bitIdx m).map inv).toFinset)) := by
    rintro t (rfl | ⟨i, hi, hbit, rfl⟩)
    · simp
    · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, List.mem_toFinset,
        List.mem_map]
      exact Or.inr ⟨i, mem_bitIdx.2 ⟨hi, hbit⟩, rfl⟩
  calc (elems m).ncard
      ≤ (↑(insert idT (((bitIdx m).map inv).toFinset)) : Set (List ℕ)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (insert idT (((bitIdx m).map inv).toFinset)).card := Set.ncard_coe_finset _
    _ ≤ ((bitIdx m).map inv).toFinset.card + 1 := Finset.card_insert_le _ _
    _ ≤ (bitIdx m).length + 1 := by
        have := List.toFinset_card_le ((bitIdx m).map inv)
        rw [List.length_map] at this
        omega

theorem mem_fixList {i c : ℕ} : c ∈ fixList i ↔ c < 2048 ∧ actT (inv i) c = c := by
  simp [fixList, List.mem_filter, List.mem_range]

theorem fixLists_getD {i : ℕ} (hi : i < nInv) : fixLists.getD i [] = fixList i := by
  rw [fixLists, getD_of_lt (by simpa using hi), List.getElem_map, List.getElem_range]

section Tabs


theorem Tab_sub_tabL (hM : MatFacts) {A : Subgroup J} (hA : A ≤ P0) {t : List ℕ}
    (ht : t ∈ Tab A) : t ∈ tabL := by
  obtain ⟨a, haA, hat⟩ := ht
  obtain ⟨t', ht', hat'⟩ := table_of_mem hM a (hA haA)
  exact (hat.unique hM hat') ▸ ht'

end Tabs

theorem Tab_bot (hM : MatFacts) :
    Tab (⊥ : Subgroup J) = {idT} := by
  ext t
  constructor
  · rintro ⟨a, ha, hat⟩
    rw [Subgroup.mem_bot] at ha
    subst ha
    exact hat.unique hM Acts.one
  · rintro rfl
    exact ⟨1, Subgroup.one_mem _, Acts.one⟩

theorem mem_sup_zpowers_iff {G : Type} [Group G] {B : Subgroup G} {y : G} (hy : y * y = 1)
    (hc : ∀ b ∈ B, b * y = y * b) {x : G} :
    x ∈ B ⊔ Subgroup.zpowers y ↔ ∃ b ∈ B, x = b ∨ x = y * b := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  constructor
  · intro hx
    let P : Subgroup G :=
      { carrier := {x | ∃ b ∈ B, x = b ∨ x = y * b}
        mul_mem' := by
          rintro x x' ⟨b, hb, hx⟩ ⟨b', hb', hx'⟩
          refine ⟨b * b', B.mul_mem hb hb', ?_⟩
          rcases hx with hx | hx <;> rcases hx' with hx' | hx' <;> rw [hx, hx']
          · exact Or.inl rfl
          · exact Or.inr (by rw [← mul_assoc, hc b hb, mul_assoc])
          · exact Or.inr (by rw [mul_assoc])
          · refine Or.inl ?_
            calc y * b * (y * b') = y * (b * y) * b' := by simp only [mul_assoc]
              _ = y * (y * b) * b' := by rw [hc b hb]
              _ = (y * y) * b * b' := by simp only [mul_assoc]
              _ = b * b' := by rw [hy, one_mul]
        one_mem' := ⟨1, B.one_mem, Or.inl rfl⟩
        inv_mem' := by
          rintro x ⟨b, hb, hx⟩
          refine ⟨b⁻¹, B.inv_mem hb, ?_⟩
          rcases hx with hx | hx <;> rw [hx]
          · exact Or.inl rfl
          · refine Or.inr ?_
            rw [mul_inv_rev, hyinv]
            exact hc b⁻¹ (B.inv_mem hb) }
    have hle : B ⊔ Subgroup.zpowers y ≤ P := sup_le (fun b hb => ⟨b, hb, Or.inl rfl⟩) (by
      rw [Subgroup.zpowers_le]
      exact ⟨1, B.one_mem, Or.inr (by rw [mul_one])⟩)
    exact hle hx
  · rintro ⟨b, hb, rfl | rfl⟩
    · exact Subgroup.mem_sup_left hb
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
        (Subgroup.mem_sup_left hb)

end CFSG.EvenSporadicStandard.J4Std.DataLocal
