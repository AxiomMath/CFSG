module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TCheck

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

abbrev A22 : Type := ↥m22A

section Sylow

theorem a2_card_eq
    : Nat.card A22 = 2 ^ 8 * 3465 := by
  rw [card_A]
  norm_num

theorem a2_Rl_mem {x : A22} (hx : x ∈ a2rl) : x ∈ Subgroup.closure {g | g ∈ a2rg} := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  rw [evalN, normH_eq]
  exact evalG_mem _ (fun g hg => Subgroup.subset_closure hg) w

theorem a2_sylow
    : SylowData A22 8 3465 a2rl := by
  obtain ⟨hlen, hnd, h1, hgen, hpow⟩ := a2_sylow_check
  exact SylowData.of_gens a2rg hlen hnd h1 hgen (fun x hx => a2_Rl_mem hx) hpow a2_card_eq
    (by decide)

theorem exists_E5 : ∃ E : Subgroup A22, ∀ x, x ∈ E ↔ x ∈ a2e5 := by
  obtain ⟨-, -, h1, hmul, -, -⟩ := a2_e5_check
  exact exists_subgroup_of_list a2e5 h1 hmul

noncomputable def E5 : Subgroup A22 := Classical.choose exists_E5

theorem mem_E5
    (x : A22) : x ∈ E5 ↔ x ∈ a2e5 := Classical.choose_spec exists_E5 x

theorem card_E5 : Nat.card E5 = 32 := by
  obtain ⟨hlen, hnd, -⟩ := a2_e5_check
  have hset : (E5 : Set A22) = ↑a2e5.toFinset := by
    ext x
    simp [mem_E5]
  have : Nat.card E5 = (E5 : Set A22).ncard := Nat.card_coe_set_eq _
  rw [this, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen]

theorem a2_unique32
    (B : Subgroup A22) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (hB : Nat.card B = 32) :
    ∃ g : A22, ∀ x, x ∈ B ↔ g * x * g⁻¹ ∈ E5 := by
  exact a2_sylow.unique32 E5 a2e5 mem_E5 card_E5 a2_heavy_check B hcomm hsq hB

theorem bE_mem_E5 (i : Fin 5) : bE i ∈ E5 :=
  (mem_E5 _).2 (a2_e5_check.2.2.2.2.2 i)

theorem a2e5_foldl_mem (n : ℕ) :
    ∀ (l : List ℕ) (acc : A22), acc ∈ Subgroup.closure (Set.range bE) →
      l.foldl (fun acc k => if n.testBit k then acc * (bE ⟨k % 5, by omega⟩) else acc) acc ∈
        Subgroup.closure (Set.range bE) := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons k l ih =>
    intro acc h
    apply ih
    by_cases hk : n.testBit k
    · simp only [hk, ite_true]
      exact Subgroup.mul_mem _ h (Subgroup.subset_closure ⟨⟨k % 5, by omega⟩, rfl⟩)
    · simp only [hk]
      exact h

theorem E5_eq_closure : E5 = Subgroup.closure (Set.range bE) := by
  apply le_antisymm
  · intro x hx
    have hx' := (mem_E5 x).1 hx
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hx'
    exact a2e5_foldl_mem n _ 1 (Subgroup.one_mem _)
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact bE_mem_E5 i

theorem sq_of_mem_E5 {x : A22} (hx : x ∈ E5) : x * x = 1 :=
  a2_e5_sq_check x ((mem_E5 x).1 hx)

end Sylow

section Full

theorem m22_fullgen
    (B : Subgroup S22) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (h3 : 2 < Nat.card B) :
    ∃ cs : List S22, cs.length = 2 ∧ Subgroup.closure (conjSet cs (B : Set S22)) = ⊤ := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨hok, hcover⟩ := m22_G2_check
  obtain ⟨h1, -⟩ := gen2_hyps m22rl m22conj m22G2 (p := 11) hok
    (fun ws => by simp [m22conj]) hcover
  obtain ⟨hfg, hfgc⟩ := m22_fg_check
  refine m22_sylow.gen2_top _ h1 ?_ B hcomm hsq h3
  intro t ht
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 ht
  have h2 := List.all_eq_true.1 hfgc e he
  obtain ⟨f, hf, hfe⟩ := List.any_eq_true.1 h2
  simp only [Bool.and_eq_true, beq_iff_eq] at hfe
  obtain ⟨hf1, hf2⟩ := hfe
  have hff := List.all_eq_true.1 hfg f hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hff
  obtain ⟨hwa, hwb⟩ := hff
  set x := m22rl.getD e.1 1
  set y := m22rl.getD e.2.1 1
  set g := evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1
  refine ⟨[1, g], rfl, ?_⟩
  have hgens : ∀ z ∈ [x, y, g * x * g⁻¹, g * y * g⁻¹],
      z ∈ Subgroup.closure (conjSet [1, g] ({x, y} : Set S22)) := by
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    apply Subgroup.subset_closure
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨1, by simp, x, by simp, by simp⟩
    · exact ⟨1, by simp, y, by simp, by simp⟩
    · exact ⟨g, by simp, x, by simp, rfl⟩
    · exact ⟨g, by simp, y, by simp, rfl⟩
  have hgens' : [x, y, g * x * g⁻¹, g * y * g⁻¹] =
      [m22rl.getD f.1 1, m22rl.getD f.2.1 1,
        evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1 * m22rl.getD f.1 1 *
          (evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1)⁻¹,
        evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1 * m22rl.getD f.2.1 1 *
          (evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1)⁻¹] := by
    rw [hf1, hf2]
  rw [hgens'] at hgens
  have ha := evalG_mem _ hgens f.2.2.2.1
  have hb := evalG_mem _ hgens f.2.2.2.2
  rw [hwa] at ha
  rw [hwb] at hb
  rw [eq_top_iff, ← closure_pair_eq_top m22_eq (m22a.2) (m22b.2)]
  rw [Subgroup.closure_le]
  rintro z (rfl | rfl)
  · exact ha
  · exact hb

end Full

end CFSG.QuasithinUnique.Setup.X1
