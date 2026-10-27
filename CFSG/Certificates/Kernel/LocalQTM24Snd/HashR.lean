module

public import CFSG.Certificates.Kernel.LocalQTM24Snd.Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc

public section

namespace CFSG.KC.LQT.M24Snd

open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

variable {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]

omit [One R] in
private theorem aux_hashr_mem_map (gens : List R) (x y : R) :
    y ∈ gens.map (x * ·) ↔ ∃ g ∈ gens, y = x * g := by
  constructor
  · intro h
    obtain ⟨g, hg, hgy⟩ := List.mem_map.mp h
    exact ⟨g, hg, hgy.symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact List.mem_map_of_mem hg

omit [One R] in
private theorem aux_hashr_inner (x : R) (l : List R) (acc : Std.HashSet R × List R) :
    (∀ y, y ∈ (l.foldl (fun (acc : Std.HashSet R × List R) g =>
        if acc.1.contains (x * g) then acc else (acc.1.insert (x * g), (x * g) :: acc.2)) acc).1 ↔
      (y ∈ acc.1 ∨ ∃ g ∈ l, y = x * g)) ∧
    (∀ y, y ∈ (l.foldl (fun (acc : Std.HashSet R × List R) g =>
        if acc.1.contains (x * g) then acc else (acc.1.insert (x * g), (x * g) :: acc.2)) acc).2 ↔
      (y ∈ acc.2 ∨ (y ∉ acc.1 ∧ ∃ g ∈ l, y = x * g))) := by
  induction l generalizing acc with
  | nil =>
    refine ⟨fun y => ?_, fun y => ?_⟩ <;> simp
  | cons g l ih =>
    simp only [List.foldl_cons]
    split_ifs with hc
    · have hmem : x * g ∈ acc.1 := Std.HashSet.contains_iff_mem.mp hc
      obtain ⟨ih1, ih2⟩ := ih acc
      refine ⟨fun y => ?_, fun y => ?_⟩
      · rw [ih1 y]
        simp only [List.mem_cons, exists_eq_or_imp]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inl (by rw [h]; exact hmem)
          · exact Or.inr h
      · rw [ih2 y]
        simp only [List.mem_cons, exists_eq_or_imp]
        constructor
        · rintro (h | ⟨h1, h2⟩)
          · exact Or.inl h
          · exact Or.inr ⟨h1, Or.inr h2⟩
        · rintro (h | ⟨h1, h2 | h2⟩)
          · exact Or.inl h
          · exact absurd (by rw [h2]; exact hmem) h1
          · exact Or.inr ⟨h1, h2⟩
    · have hn : x * g ∉ acc.1 := fun h => hc (Std.HashSet.contains_iff_mem.mpr h)
      have hyn : ∀ y, y = x * g → y ∉ acc.1 := fun y h hy => hn (by rw [← h]; exact hy)
      obtain ⟨ih1, ih2⟩ := ih (acc.1.insert (x * g), (x * g) :: acc.2)
      refine ⟨fun y => ?_, fun y => ?_⟩
      · rw [ih1 y]
        simp only [Std.HashSet.mem_insert, beq_iff_eq, List.mem_cons, exists_eq_or_imp]
        tauto
      · rw [ih2 y]
        simp only [Std.HashSet.mem_insert, beq_iff_eq, List.mem_cons, exists_eq_or_imp]
        have := hyn y
        tauto

omit [One R] in
private theorem aux_hashr_outer (gens : List R) (S : Std.HashSet R) (F : List R) :
    ∀ (P : List R) (acc : Std.HashSet R × List R),
      (∀ y, y ∈ acc.1 ↔ y ∈ S ∨ ∃ z ∈ P, ∃ g ∈ gens, y = z * g) →
      (∀ y, y ∈ acc.2 ↔ y ∉ S ∧ ∃ z ∈ P, ∃ g ∈ gens, y = z * g) →
      (∀ y, y ∈ (F.foldl (fun (acc : Std.HashSet R × List R) x =>
          gens.foldl (fun (acc : Std.HashSet R × List R) g =>
            if acc.1.contains (x * g) then acc else (acc.1.insert (x * g), (x * g) :: acc.2)) acc)
          acc).1 ↔
        (y ∈ S ∨ ∃ z ∈ P ++ F, ∃ g ∈ gens, y = z * g)) ∧
      (∀ y, y ∈ (F.foldl (fun (acc : Std.HashSet R × List R) x =>
          gens.foldl (fun (acc : Std.HashSet R × List R) g =>
            if acc.1.contains (x * g) then acc else (acc.1.insert (x * g), (x * g) :: acc.2)) acc)
          acc).2 ↔
        (y ∉ S ∧ ∃ z ∈ P ++ F, ∃ g ∈ gens, y = z * g)) := by
  induction F with
  | nil =>
    intro P acc h1 h2
    simp only [List.foldl_nil, List.append_nil]
    exact ⟨h1, h2⟩
  | cons x F ih =>
    intro P acc h1 h2
    simp only [List.foldl_cons]
    have hin := aux_hashr_inner x gens acc
    have e : P ++ [x] ++ F = P ++ (x :: F) := by simp
    rw [← e]
    refine ih (P ++ [x]) _ (fun y => ?_) (fun y => ?_)
    · rw [hin.1 y, h1 y]
      constructor
      · rintro ((hS | ⟨z, hz, hq⟩) | ⟨g, hg, hy⟩)
        · exact Or.inl hS
        · exact Or.inr ⟨z, List.mem_append.mpr (Or.inl hz), hq⟩
        · exact Or.inr ⟨x, List.mem_append.mpr (Or.inr (List.mem_singleton_self x)), g, hg, hy⟩
      · rintro (hS | ⟨z, hz, hq⟩)
        · exact Or.inl (Or.inl hS)
        · rcases List.mem_append.mp hz with hz | hz
          · exact Or.inl (Or.inr ⟨z, hz, hq⟩)
          · rw [List.mem_singleton.mp hz] at hq
            exact Or.inr hq
    · rw [hin.2 y, h2 y]
      constructor
      · rintro (⟨hS, z, hz, hq⟩ | ⟨hA, g, hg, hy⟩)
        · exact ⟨hS, z, List.mem_append.mpr (Or.inl hz), hq⟩
        · exact ⟨fun hS => hA ((h1 y).2 (Or.inl hS)), x,
            List.mem_append.mpr (Or.inr (List.mem_singleton_self x)), g, hg, hy⟩
      · rintro ⟨hS, z, hz, hq⟩
        rcases List.mem_append.mp hz with hz | hz
        · exact Or.inl ⟨hS, z, hz, hq⟩
        · rw [List.mem_singleton.mp hz] at hq
          by_cases hA : y ∈ acc.1
          · rcases (h1 y).1 hA with hS' | ⟨z', hz', hq'⟩
            · exact absurd hS' hS
            · exact Or.inl ⟨hS, z', hz', hq'⟩
          · exact Or.inr ⟨hA, hq⟩

theorem bfsStep_spec (gens : List R) (S : Std.HashSet R) (F : List R) :
    (∀ y, y ∈ (bfsStep gens S F).1 ↔ y ∈ S ∨ ∃ x ∈ F, ∃ g ∈ gens, y = x * g) ∧
      ∀ y, y ∈ (bfsStep gens S F).2 ↔ y ∉ S ∧ ∃ x ∈ F, ∃ g ∈ gens, y = x * g := by
  have key := aux_hashr_outer gens S F [] (S, []) (fun y => by simp) (fun y => by simp)
  rw [List.nil_append] at key
  unfold bfsStep
  exact key

theorem bfsRun_inv (gens : List R) (seeds : Set R) (k : ℕ) (S : Std.HashSet R) (F : List R)
    (h : BfsInv (fun x => gens.map (x * ·)) seeds k {x | x ∈ S} {x | x ∈ F}) (r : ℕ) :
    BfsInv (fun x => gens.map (x * ·)) seeds (k + r) {x | x ∈ (bfsRun gens r (S, F)).1}
      {x | x ∈ (bfsRun gens r (S, F)).2} := by
  induction r generalizing k S F with
  | zero =>
    rw [Nat.add_zero, bfsRun]
    exact h
  | succ r ih =>
    have hb : BfsInv (fun x => gens.map (x * ·)) seeds (k + 1)
        {x | x ∈ (bfsStep gens S F).1} {x | x ∈ (bfsStep gens S F).2} := by
      refine BfsInv.step h (fun y => ?_) (fun y hy hnS => ?_) (fun y hy => ?_)
      · show y ∈ (bfsStep gens S F).1 ↔ y ∈ S ∨ ∃ x ∈ F, y ∈ gens.map (x * ·)
        rw [(bfsStep_spec gens S F).1 y]
        simp only [aux_hashr_mem_map, iff_self]
      · obtain ⟨x, hx, hyx⟩ := hy
        exact ((bfsStep_spec gens S F).2 y).mpr ⟨hnS, x, hx, (aux_hashr_mem_map gens x y).mp hyx⟩
      · obtain ⟨_, x, hx, hyx⟩ := ((bfsStep_spec gens S F).2 y).mp hy
        exact ⟨x, hx, (aux_hashr_mem_map gens x y).mpr hyx⟩
    have e : k + (r + 1) = k + 1 + r := by omega
    have e2 : bfsRun gens (r + 1) (S, F) = bfsRun gens r (bfsStep gens S F) := by
      rw [bfsRun]
    rw [e, e2]
    exact ih (k + 1) (bfsStep gens S F).1 (bfsStep gens S F).2 hb

theorem bfsSet_inv (gens : List R) (r : ℕ) :
    BfsInv (fun x => gens.map (x * ·)) {1} r {x | x ∈ bfsSet gens r}
      {x | x ∈ (bfsRun gens r ((∅ : Std.HashSet R).insert 1, [1])).2} := by
  have h0 : BfsInv (fun x => gens.map (x * ·)) ({1} : Set R) 0
      {x | x ∈ ((∅ : Std.HashSet R).insert 1)} {x | x ∈ [(1 : R)]} := by
    have e1 : {x | x ∈ ((∅ : Std.HashSet R).insert 1)} = ({1} : Set R) := by
      ext x
      simp [Std.HashSet.mem_insert]
    have e2 : {x | x ∈ [(1 : R)]} = ({1} : Set R) := by
      ext x
      simp
    rw [e1, e2]
    exact BfsInv.init
  have h := bfsRun_inv gens {1} 0 ((∅ : Std.HashSet R).insert 1) [1] h0 r
  rw [Nat.zero_add] at h
  have e3 : bfsSet gens r = (bfsRun gens r ((∅ : Std.HashSet R).insert 1, [1])).1 := by
    rw [bfsSet]
  rw [e3]
  exact h

theorem mem_bfsSet_iff (gens : List R) (r : ℕ) (x : R) :
    x ∈ bfsSet gens r ↔ x ∈ ball (fun x => gens.map (x * ·)) {1} r :=
  ⟨fun hx => (bfsSet_inv gens r).sub x hx, fun hx => (bfsSet_inv gens r).sup x hx⟩

end CFSG.KC.LQT.M24Snd

end
