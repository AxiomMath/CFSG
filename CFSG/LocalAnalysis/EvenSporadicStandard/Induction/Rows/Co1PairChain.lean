module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PairGeneric
public import Certificates.Certificate27202

public section

namespace CFSG.EvenSporadicStandard.Co1Pair

open CFSG.Sporadic.Co1Schreier

@[expose] def cpWordG (g : ℕ → GL24) (w : List ℕ) : GL24 := w.foldl (fun acc l => acc * g l) 1

theorem cpWord_rep {gens : Array Native.Rows} {g : ℕ → GL24} {w : List ℕ}
    (h : ∀ l ∈ w, MRep gens[l]! (g l)) : MRep (cpWord gens w) (cpWordG g w) := by
  have key : ∀ (w : List ℕ), (∀ l ∈ w, MRep gens[l]! (g l)) → ∀ (acc : Native.Rows) (a : GL24),
      MRep acc a → MRep (w.foldl (fun acc l => Native.mul acc gens[l]!) acc)
        (w.foldl (fun x l => x * g l) a) := by
    intro w
    induction w with
    | nil => intro _ acc a ha; exact ha
    | cons l w ih =>
      intro hw acc a ha
      rw [List.foldl_cons, List.foldl_cons]
      exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ _
        (ha.mul (hw l List.mem_cons_self))
  exact key w h Native.one 1 MRep.one

theorem cpWordG_mem {g : ℕ → GL24} {H : Subgroup GL24} {w : List ℕ} (h : ∀ l ∈ w, g l ∈ H) :
    cpWordG g w ∈ H := by
  have key : ∀ (w : List ℕ), (∀ l ∈ w, g l ∈ H) → ∀ a : GL24, a ∈ H →
      w.foldl (fun x l => x * g l) a ∈ H := by
    intro w
    induction w with
    | nil => intro _ a ha; exact ha
    | cons l w ih =>
      intro hw a ha
      rw [List.foldl_cons]
      exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _
        (H.mul_mem ha (hw l List.mem_cons_self))
  exact key w h 1 H.one_mem

theorem cpOK_parts :
    cpSsRead.1.size = 5 ∧ (∀ w ∈ cpSsRead.1, ∀ l ∈ w, l < 2) ∧ cpLevelOK 0 = true ∧
      cpLevelOK 1 = true ∧ cpLevelOK 2 = true := by
  have h := Certificates.certificate27202
  simp only [cpOK, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h5, hw⟩, h0⟩, h1⟩, h2⟩ := h
  exact ⟨h5, hw, h0, h1, h2⟩

theorem cpLevelOK_parts {i : ℕ} (h : cpLevelOK i = true) :
    (cpTw i).size = cpN i ∧ (cpTw i)[0]! = [] ∧ (∀ w ∈ cpTw i, ∀ l ∈ w, cpF i ≤ l ∧ l < 7) ∧
      (cpDec i).size = cpN i * (7 - cpF i) ∧
      ∀ k < cpN i, ∀ jj < 7 - cpF i,
        (cpDec i)[k * (7 - cpF i) + jj]! / cpN i / cpN (i + 1) < cpN (i + 2) ∧
        Native.mul cpSs[cpF i + jj]! (cpTMget i k) =
          Native.mul (cpTMget i ((cpDec i)[k * (7 - cpF i) + jj]! % cpN i))
            (Native.mul (cpTMget (i + 1) ((cpDec i)[k * (7 - cpF i) + jj]! / cpN i % cpN (i + 1)))
              (cpTMget (i + 2) ((cpDec i)[k * (7 - cpF i) + jj]! / cpN i / cpN (i + 1)))) := by
  simp only [cpLevelOK, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', List.all_eq_true,
    decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, fun w hw l hl => ?_, h4, fun k hk jj hjj => ?_⟩
  · have := h3 w hw l hl
    exact this
  · have := h5 k hk jj hjj
    exact ⟨this.1, this.2⟩

theorem getElem!_append_map {α β : Type*} [Inhabited α] [Inhabited β] (pre : Array β)
    (a : Array α) (f : α → β) (j : ℕ) (hj : pre.size ≤ j) (hj' : j - pre.size < a.size) :
    (pre ++ a.map f)[j]! = f a[j - pre.size]! := by
  have h1 : j < (pre ++ a.map f).size := by simp; omega
  rw [getElem!_pos _ j h1, Array.getElem_append_right hj, Array.getElem_map, getElem!_pos a _ hj']

theorem getElem!_append_left' {β : Type*} [Inhabited β] (pre b : Array β) (j : ℕ)
    (hj : j < pre.size) : (pre ++ b)[j]! = pre[j]! := by
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_append_left hj, getElem!_pos pre j hj]

theorem getElem!_map' {α β : Type*} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β) (j : ℕ)
    (hj : j < a.size) : (a.map f)[j]! = f a[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos a _ hj]

theorem getElem!_mem' {α : Type*} [Inhabited α] (a : Array α) (j : ℕ) (hj : j < a.size) :
    a[j]! ∈ a := by
  rw [getElem!_pos a j hj]
  exact Array.getElem_mem hj

theorem arr2_get {α : Type*} [Inhabited α] (a b : α) :
    (#[a, b] : Array α)[0]! = a ∧ (#[a, b] : Array α)[1]! = b := ⟨rfl, rfl⟩

theorem arr3_get {α : Type*} [Inhabited α] (a b c : α) :
    (#[a, b, c] : Array α)[0]! = a ∧ (#[a, b, c] : Array α)[1]! = b ∧
      (#[a, b, c] : Array α)[2]! = c := ⟨rfl, rfl, rfl⟩

@[expose] def gXY (X Y : GL24) (l : ℕ) : GL24 := if l = 0 then X else Y

@[expose] def sG (X Y : GL24) (j : ℕ) : GL24 :=
  if j < 2 then gXY X Y j else cpWordG (gXY X Y) (cpSsRead.1[j - 2]!)

@[expose] def tG (X Y : GL24) (i k : ℕ) : GL24 :=
  if i < 3 then cpWordG (sG X Y) ((cpTw i)[k]!) else 1

theorem cpN_pos (i : ℕ) : 0 < cpN i := by
  rcases i with _ | _ | _ | _ | _ | i <;> simp [cpN]

theorem cpF_mono (i : ℕ) : cpF i ≤ cpF (i + 1) := by
  rcases i with _ | _ | _ | i <;> simp [cpF]

theorem rep_gXY {X Y : GL24} (hX : MRep cpX X) (hY : MRep cpY Y) {l : ℕ} (hl : l < 2) :
    MRep (#[cpX, cpY] : Array Native.Rows)[l]! (gXY X Y l) := by
  interval_cases l
  · rw [(arr2_get cpX cpY).1]
    exact hX
  · rw [(arr2_get cpX cpY).2]
    exact hY

theorem rep_cpSs {X Y : GL24} (hX : MRep cpX X) (hY : MRep cpY Y)
    {j : ℕ} (hj : j < 7) : MRep cpSs[j]! (sG X Y j) := by
  obtain ⟨h5, hw, -, -, -⟩ := cpOK_parts
  by_cases h2 : j < 2
  · have e : cpSs[j]! = (#[cpX, cpY] : Array Native.Rows)[j]! :=
      getElem!_append_left' _ _ j (by simpa using h2)
    rw [e, sG]
    simp only [h2, ↓reduceIte]
    exact rep_gXY hX hY h2
  · have hj5 : j - 2 < cpSsRead.1.size := by omega
    have e : cpSs[j]! = cpWord #[cpX, cpY] cpSsRead.1[j - 2]! :=
      getElem!_append_map _ _ _ j (by simp; omega) (by simpa using hj5)
    rw [e, sG]
    simp only [h2, ↓reduceIte]
    refine cpWord_rep fun l hl => rep_gXY hX hY (hw _ (getElem!_mem' _ _ hj5) l hl)

theorem cpLevelOK_of_lt {i : ℕ} (hi : i < 3) :
    cpLevelOK i = true := by
  obtain ⟨-, -, h0, h1, h2⟩ := cpOK_parts
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2

theorem cpTMget_eq {i k : ℕ} (hi : i < 3) (hk : k < cpN i) :
    cpTMget i k = cpWord cpSs (cpTw i)[k]! := by
  have hsz := (cpLevelOK_parts (cpLevelOK_of_lt hi)).1
  have hk' : k < (cpTw i).size := by omega
  have hrow : cpTMs[i]! = (cpTw i).map (cpWord cpSs) := by
    unfold cpTMs
    interval_cases i
    · exact (arr3_get _ _ _).1
    · exact (arr3_get _ _ _).2.1
    · exact (arr3_get _ _ _).2.2
  rw [cpTMget]
  simp only [hi, ↓reduceIte]
  rw [hrow]
  exact getElem!_map' _ _ _ hk'

theorem rep_cpTM {X Y : GL24} (hX : MRep cpX X) (hY : MRep cpY Y)
    {i k : ℕ} (hik : i < 3 → k < cpN i) : MRep (cpTMget i k) (tG X Y i k) := by
  by_cases hi : i < 3
  · have hk := hik hi
    obtain ⟨hsz, -, hlet, -, -⟩ := cpLevelOK_parts (cpLevelOK_of_lt hi)
    rw [cpTMget_eq hi hk, tG]
    simp only [hi, ↓reduceIte]
    refine cpWord_rep fun l hl => rep_cpSs hX hY (hlet _ (getElem!_mem' _ _ (by omega)) l hl).2
  · rw [cpTMget, tG]
    simp only [hi, ↓reduceIte]
    exact MRep.one

theorem cp_relations {X Y : GL24} (hX : MRep cpX X)
    (hY : MRep cpY Y) : ∀ i < 3, ∀ j, cpF i ≤ j → j < cpF 3 → ∀ k < cpN i, ∃ k' < cpN i,
      ∃ c₁ < cpN (i + 1), ∃ c₂ < cpN (i + 2),
        sG X Y j * tG X Y i k = tG X Y i k' * (tG X Y (i + 1) c₁ * tG X Y (i + 2) c₂) := by
  intro i hi j hj1 hj2 k hk
  have hF3 : cpF 3 = 7 := rfl
  rw [hF3] at hj2
  obtain ⟨-, -, -, -, hrow⟩ := cpLevelOK_parts (cpLevelOK_of_lt hi)
  have hjj : j - cpF i < 7 - cpF i := by omega
  obtain ⟨hlt, heq⟩ := hrow k hk (j - cpF i) hjj
  have hj' : cpF i + (j - cpF i) = j := by omega
  rw [hj'] at heq
  generalize (cpDec i)[k * (7 - cpF i) + (j - cpF i)]! = p at hlt heq
  have r1 : MRep (Native.mul cpSs[j]! (cpTMget i k)) (sG X Y j * tG X Y i k) :=
    (rep_cpSs hX hY hj2).mul (rep_cpTM hX hY fun _ => hk)
  have r2 : MRep (Native.mul (cpTMget i (p % cpN i)) (Native.mul
      (cpTMget (i + 1) (p / cpN i % cpN (i + 1))) (cpTMget (i + 2) (p / cpN i / cpN (i + 1)))))
      (tG X Y i (p % cpN i) * (tG X Y (i + 1) (p / cpN i % cpN (i + 1)) *
        tG X Y (i + 2) (p / cpN i / cpN (i + 1)))) :=
    (rep_cpTM hX hY fun _ => Nat.mod_lt _ (cpN_pos _)).mul
      ((rep_cpTM hX hY fun _ => Nat.mod_lt _ (cpN_pos _)).mul (rep_cpTM hX hY fun _ => hlt))
  rw [heq] at r1
  exact ⟨p % cpN i, Nat.mod_lt _ (cpN_pos _), p / cpN i % cpN (i + 1), Nat.mod_lt _ (cpN_pos _),
    p / cpN i / cpN (i + 1), hlt, r1.eq r2⟩

theorem cpChain_bound {X Y : GL24} (hX : MRep cpX X)
    (hY : MRep cpY Y) : Nat.card (Subgroup.closure ({X, Y} : Set GL24)) ≤ 251596800 := by
  have h := card_closure_le_chain (sG X Y) cpF cpN (tG X Y) cpF_mono
    (fun i hi k => by simp [tG, not_lt.2 hi])
    (fun i hi => ⟨0, cpN_pos i, by
      obtain ⟨-, h0, -⟩ := cpLevelOK_parts (cpLevelOK_of_lt hi)
      simp [tG, hi, h0, cpWordG]⟩)
    (fun i hi k hk => by
      obtain ⟨hsz, -, hlet, -, -⟩ := cpLevelOK_parts (cpLevelOK_of_lt hi)
      simp only [tG, hi, ↓reduceIte]
      refine cpWordG_mem fun l hl => ?_
      have hl' := hlet _ (getElem!_mem' _ _ (by omega)) l hl
      exact Subgroup.subset_closure ⟨l, hl', rfl⟩)
    (cp_relations hX hY)
  have hsub : Subgroup.closure ({X, Y} : Set GL24) ≤
      Subgroup.closure (sG X Y '' {j | cpF 0 ≤ j ∧ j < cpF 3}) := by
    refine Subgroup.closure_mono fun g hg => ?_
    rcases hg with rfl | rfl
    · exact ⟨0, ⟨by decide, by decide⟩, by simp [sG, gXY]⟩
    · exact ⟨1, ⟨by decide, by decide⟩, by simp [sG, gXY]⟩
  calc Nat.card (Subgroup.closure ({X, Y} : Set GL24))
      ≤ Nat.card (Subgroup.closure (sG X Y '' {j | cpF 0 ≤ j ∧ j < cpF 3})) :=
        Subgroup.card_le_of_le hsub
    _ ≤ cpN 0 * cpN 1 * cpN 2 := h
    _ = 251596800 := by decide

end CFSG.EvenSporadicStandard.Co1Pair
