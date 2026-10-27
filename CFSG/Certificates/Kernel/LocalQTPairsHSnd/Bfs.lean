module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporBFS
public import Std.Data.HashSet.Lemmas

public section

namespace CFSG.KC.LQT.PHSnd

open CFSG.QuasithinUnique.Vol2Native.L239

variable {Γ : Type*} [Group Γ] {Ω : Type*} [MulAction Γ Ω] {E : Type*} [BEq E] [LawfulBEq E]
  [Hashable E]

private def OInv (enc : Ω → E) (x₀ : Ω) (Tr : List Ω) (st : BfsState Ω E) : Prop :=
  st.O.toList.Nodup ∧ (∀ e, st.seen.contains e = true ↔ ∃ y ∈ st.O.toList, enc y = e) ∧
    (∀ y ∈ st.O.toList, y ∈ Tr) ∧ x₀ ∈ st.O.toList

private def LoopInv (gens : List Γ) (enc : Ω → E) (x₀ : Ω) (Tr : List Ω) (i : ℕ)
    (st : BfsState Ω E) : Prop :=
  OInv enc x₀ Tr st ∧ i ≤ st.O.toList.length ∧
    ∀ x ∈ st.O.toList.take i, ∀ g ∈ gens, g • x ∈ st.O.toList

private theorem mem_of_append_eq {α : Type*} {l l' e : List α} {a : α} (h : l' = l ++ e)
    (ha : a ∈ l) : a ∈ l' := by
  rw [h]
  exact List.mem_append_left _ ha

private theorem oinv_push (enc : Ω → E) (x₀ : Ω) (Tr : List Ω) (st : BfsState Ω E)
    (z : Ω) (par lab : Array ℕ) (hI : OInv enc x₀ Tr st) (hz : z ∈ Tr)
    (hzn : ¬ st.seen.contains (enc z) = true) :
    OInv enc x₀ Tr ⟨st.O.push z, par, lab, st.seen.insert (enc z)⟩ := by
  obtain ⟨hnd, hseen, hTr, hx₀⟩ := hI
  unfold OInv
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (st.O.push z).toList.Nodup
    rw [Array.toList_push, List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    apply hzn
    exact (hseen _).2 ⟨a, ha, by rw [hab, hb]⟩
  · intro e
    change (st.seen.insert (enc z)).contains e = true ↔ ∃ y ∈ (st.O.push z).toList, enc y = e
    rw [Array.toList_push, Std.HashSet.contains_insert, Bool.or_eq_true_iff, beq_iff_eq,
      hseen e]
    constructor
    · rintro (h | ⟨y, hy, hye⟩)
      · exact ⟨z, List.mem_append_right _ (List.mem_singleton_self _), h⟩
      · exact ⟨y, List.mem_append_left _ hy, hye⟩
    · rintro ⟨y, hy, hye⟩
      rcases List.mem_append.1 hy with hy | hy
      · exact Or.inr ⟨y, hy, hye⟩
      · rw [List.mem_singleton] at hy
        subst hy
        exact Or.inl hye
  · intro y hy
    change y ∈ (st.O.push z).toList at hy
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hTr y hy
    · exact hz
  · change x₀ ∈ (st.O.push z).toList
    rw [Array.toList_push]
    exact List.mem_append_left _ hx₀

private theorem bfs_step (nrm : Ω → Ω) (hnrm : ∀ x, nrm x = x) (enc : Ω → E) (gens : List Γ)
    (x₀ : Ω) (Tr : List Ω) (hinj : ∀ a ∈ Tr, ∀ b ∈ Tr, enc a = enc b → a = b)
    (hcl : ∀ g ∈ gens, ∀ x ∈ Tr, g • x ∈ Tr) (x : Ω) (i j : ℕ) (hj : j < gens.length)
    (st : BfsState Ω E) (hI : OInv enc x₀ Tr st) (hx : x ∈ st.O.toList) :
    let st' : BfsState Ω E :=
      if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
      else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
        st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩
    OInv enc x₀ Tr st' ∧ (∃ extra, st'.O.toList = st.O.toList ++ extra) ∧
      gens.getD j 1 • x ∈ st'.O.toList := by
  obtain ⟨-, hseen, hTr, -⟩ := id hI
  have hgen : gens.getD j 1 ∈ gens := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hzTr : gens.getD j 1 • x ∈ Tr := hcl _ hgen x (hTr x hx)
  simp only [hnrm]
  by_cases hc : st.seen.contains (enc (gens.getD j 1 • x)) = true
  · rw [if_pos hc]
    obtain ⟨y, hy, hyz⟩ := (hseen _).1 hc
    have hyeq : y = gens.getD j 1 • x := hinj y (hTr y hy) _ hzTr hyz
    rw [hyeq] at hy
    exact ⟨id hI, ⟨[], by simp⟩, hy⟩
  · rw [if_neg hc]
    refine ⟨oinv_push enc x₀ Tr st (gens.getD j 1 • x) (st.par.push i) (st.lab.push j)
      (id hI) hzTr hc, ⟨[gens.getD j 1 • x], by simp⟩, ?_⟩
    change gens.getD j 1 • x ∈ (st.O.push (gens.getD j 1 • x)).toList
    rw [Array.toList_push]
    exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem bfs_fold (nrm : Ω → Ω) (hnrm : ∀ x, nrm x = x) (enc : Ω → E) (gens : List Γ)
    (x₀ : Ω) (Tr : List Ω) (hinj : ∀ a ∈ Tr, ∀ b ∈ Tr, enc a = enc b → a = b)
    (hcl : ∀ g ∈ gens, ∀ x ∈ Tr, g • x ∈ Tr) (x : Ω) (i : ℕ) (js : List ℕ) :
    (∀ j ∈ js, j < gens.length) → ∀ (st : BfsState Ω E), OInv enc x₀ Tr st →
      x ∈ st.O.toList →
      OInv enc x₀ Tr (js.foldl (fun (st : BfsState Ω E) j =>
        if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
        else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
          st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩) st) ∧
      (∃ extra, (js.foldl (fun (st : BfsState Ω E) j =>
        if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
        else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
          st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩) st).O.toList = st.O.toList ++ extra) ∧
      ∀ j ∈ js, gens.getD j 1 • x ∈ (js.foldl (fun (st : BfsState Ω E) j =>
        if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
        else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
          st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩) st).O.toList := by
  induction js with
  | nil =>
    intro _ st hI _
    exact ⟨hI, ⟨[], by simp⟩, by simp⟩
  | cons j js ih =>
    intro hjs st hI hx
    obtain ⟨h1, ⟨e1, he1⟩, h3⟩ := bfs_step nrm hnrm enc gens x₀ Tr hinj hcl x i j
      (hjs j (by simp)) st hI hx
    obtain ⟨g1, ⟨e2, he2⟩, g3⟩ := ih (fun j' hj' => hjs j' (by simp [hj'])) _ h1
      (mem_of_append_eq he1 hx)
    rw [List.foldl_cons]
    refine ⟨g1, ⟨e1 ++ e2, ?_⟩, ?_⟩
    · exact he2.trans ((congrArg (fun l : List Ω => l ++ e2) he1).trans
        (List.append_assoc _ _ _))
    · intro j' hj'
      rcases List.mem_cons.1 hj' with rfl | hj''
      · exact mem_of_append_eq he2 h3
      · exact g3 j' hj''

private theorem loop_zero (nrm : Ω → Ω) (enc : Ω → E) (gens : List Γ) (i : ℕ)
    (st : BfsState Ω E) : bfsLoop nrm enc gens 0 i st = st := by
  rw [bfsLoop]

private theorem loop_succ_lt (nrm : Ω → Ω) (enc : Ω → E) (gens : List Γ) (f i : ℕ)
    (st : BfsState Ω E) (hi : i < st.O.size) (x : Ω) (hx : st.O[i] = x) :
    bfsLoop nrm enc gens (f + 1) i st = bfsLoop nrm enc gens f (i + 1)
      ((List.range gens.length).foldl (fun (st : BfsState Ω E) j =>
        if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
        else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
          st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩) st) := by
  subst hx
  rw [bfsLoop, dif_pos hi]

private theorem loop_succ_not_lt (nrm : Ω → Ω) (enc : Ω → E) (gens : List Γ) (f i : ℕ)
    (st : BfsState Ω E) (hi : ¬ i < st.O.size) : bfsLoop nrm enc gens (f + 1) i st = st := by
  rw [bfsLoop, dif_neg hi]

private theorem loopInv_next (gens : List Γ) (enc : Ω → E) (x₀ : Ω) (Tr : List Ω) (i : ℕ)
    (st st1 : BfsState Ω E) (hi : i < st.O.size)
    (hpr : ∀ x ∈ st.O.toList.take i, ∀ g ∈ gens, g • x ∈ st.O.toList)
    (hI1 : OInv enc x₀ Tr st1) (e : List Ω) (he : st1.O.toList = st.O.toList ++ e)
    (hall : ∀ g ∈ gens, g • st.O[i] ∈ st1.O.toList) :
    LoopInv gens enc x₀ Tr (i + 1) st1 := by
  have hlen : st.O.toList.length = st.O.size := by simp
  have hlt : i < st.O.toList.length := by omega
  have hle : i + 1 ≤ st.O.toList.length := by omega
  unfold LoopInv
  refine ⟨hI1, ?_, ?_⟩
  · rw [he, List.length_append]
    omega
  · intro y hy g hg
    rw [he, List.take_append_of_le_length hle, List.take_succ_eq_append_getElem hlt,
      List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | hy
    · rw [he]
      exact List.mem_append_left _ (hpr y hy g hg)
    · have hy' : y = st.O[i] := hy
      rw [hy']
      exact hall g hg

private theorem bfs_loop (nrm : Ω → Ω) (hnrm : ∀ x, nrm x = x) (enc : Ω → E) (gens : List Γ)
    (x₀ : Ω) (Tr : List Ω) (hinj : ∀ a ∈ Tr, ∀ b ∈ Tr, enc a = enc b → a = b)
    (hcl : ∀ g ∈ gens, ∀ x ∈ Tr, g • x ∈ Tr) :
    ∀ (f i : ℕ) (st : BfsState Ω E), LoopInv gens enc x₀ Tr i st →
      ∃ i', LoopInv gens enc x₀ Tr i' (bfsLoop nrm enc gens f i st) ∧
        (i' = i + f ∨ i' = (bfsLoop nrm enc gens f i st).O.toList.length) := by
  intro f
  induction f with
  | zero =>
    intro i st hL
    refine ⟨i, ?_, Or.inl (by simp)⟩
    rw [loop_zero]
    exact hL
  | succ f ih =>
    intro i st hL
    obtain ⟨hI, hle, hpr⟩ := hL
    by_cases hi : i < st.O.size
    · have hxmem : st.O[i] ∈ st.O.toList := Array.mem_toList_iff.2 (Array.getElem_mem hi)
      obtain ⟨hI1, ⟨e, he⟩, hall⟩ := bfs_fold nrm hnrm enc gens x₀ Tr hinj hcl (st.O[i]) i
        (List.range gens.length) (fun j hj => List.mem_range.1 hj) st hI hxmem
      have hL1 := loopInv_next gens enc x₀ Tr i st _ hi hpr hI1 e he (by
        intro g hg
        obtain ⟨j, hj, hjg⟩ := List.mem_iff_getElem.1 hg
        have hgj : gens.getD j 1 = g := by rw [List.getD_eq_getElem _ _ hj, hjg]
        rw [← hgj]
        exact hall j (List.mem_range.2 hj))
      rw [loop_succ_lt nrm enc gens f i st hi (st.O[i]) rfl]
      obtain ⟨i', hL', hdis⟩ := ih (i + 1) _ hL1
      refine ⟨i', hL', ?_⟩
      rcases hdis with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
    · rw [loop_succ_not_lt nrm enc gens f i st hi]
      have hlen : st.O.toList.length = st.O.size := by simp
      refine ⟨i, ?_, Or.inr (by omega)⟩
      unfold LoopInv
      exact ⟨hI, hle, hpr⟩

theorem bfsOrbit_perm (nrm : Ω → Ω) (hnrm : ∀ x, nrm x = x) (enc : Ω → E) (gens : List Γ)
    (x₀ : Ω) (fuel : ℕ) (Tr : List Ω) (hnd : Tr.Nodup)
    (hinj : ∀ a ∈ Tr, ∀ b ∈ Tr, enc a = enc b → a = b) (h0 : x₀ ∈ Tr)
    (hcl : ∀ g ∈ gens, ∀ x ∈ Tr, g • x ∈ Tr)
    (hreach : ∀ y ∈ Tr, ∀ S : Set Ω, x₀ ∈ S → (∀ g ∈ gens, ∀ x ∈ S, g • x ∈ S) → y ∈ S)
    (hf : Tr.length ≤ fuel) :
    ((bfsOrbit nrm enc gens x₀ fuel).1).Perm Tr := by
  have hI0 : LoopInv gens enc x₀ Tr 0
      (⟨#[x₀], #[0], #[0], (∅ : Std.HashSet E).insert (enc x₀)⟩ : BfsState Ω E) := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp
    · intro e
      show (Std.HashSet.contains ((∅ : Std.HashSet E).insert (enc x₀)) e = true) ↔
        ∃ y ∈ [x₀], enc y = e
      rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
      constructor
      · intro h
        exact ⟨x₀, List.mem_singleton_self _, beq_iff_eq.1 h⟩
      · rintro ⟨y, hy, rfl⟩
        rw [List.mem_singleton.1 hy]
        exact beq_self_eq_true _
    · intro y hy
      simp at hy
      rw [hy]
      exact h0
    · simp
    · simp
    · intro x hx
      simp at hx
  obtain ⟨i', hI', hcase⟩ := bfs_loop nrm hnrm enc gens x₀ Tr hinj hcl fuel 0 _ hI0
  have hbf : (bfsOrbit nrm enc gens x₀ fuel).1 =
      (bfsLoop nrm enc gens fuel 0
        (⟨#[x₀], #[0], #[0], (∅ : Std.HashSet E).insert (enc x₀)⟩ : BfsState Ω E)).O.toList :=
    rfl
  rw [hbf]
  generalize (bfsLoop nrm enc gens fuel 0
    (⟨#[x₀], #[0], #[0], (∅ : Std.HashSet E).insert (enc x₀)⟩ : BfsState Ω E)) = st' at hI' hcase ⊢
  obtain ⟨⟨hOnd, -, hOTr, hx0⟩, hle, hproc⟩ := hI'
  rcases hcase with hcase | hcase
  · exact (List.subperm_of_subset hOnd hOTr).perm_of_length_le (by omega)
  · have hclO : ∀ g ∈ gens, ∀ x ∈ st'.O.toList, g • x ∈ st'.O.toList := by
      intro g hg x hx
      refine hproc x ?_ g hg
      rw [hcase, List.take_length]
      exact hx
    exact (List.perm_ext_iff_of_nodup hOnd hnd).2 fun a => ⟨fun ha => hOTr a ha,
      fun ha => hreach a ha _ hx0 hclO⟩

end CFSG.KC.LQT.PHSnd

end
