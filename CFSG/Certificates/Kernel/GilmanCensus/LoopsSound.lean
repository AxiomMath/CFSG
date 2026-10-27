module

public import CFSG.Certificates.Kernel.GilmanCensus.MkDataProg
public import CFSG.Certificates.Kernel.GilmanCensus.GroupsSound
public import CFSG.Certificates.Kernel.GilmanCensus.IxSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

theorem ixLoop_eq (R : Array IVec) (hnd : (LLI R).Nodup) (v : IVec) :
    (ixLoop R R.size)[v]? = idxI v.toList (LLI R) 0 := by
  unfold ixLoop
  exact ix_fold R hnd v

theorem hsLoop_eq (H : Array (Array Nat)) :
    hsLoop H = (H.toList.flatMap fun h => [h.map fun x => x * 1 % 3, h.map fun x => x * 2 % 3]).foldl
      (fun S x => S.insert x) ∅ := by
  unfold hsLoop
  exact hs_fold H

theorem fhOkLoop_eq (F H : Array (Array Nat)) (G : Array (Array Int)) (g : Nat → Nat → Int)
    (hG : ∀ i j, G[i]![j]! = g i j) (N : Nat) (ok : Bool) :
    fhOkLoop F H G N ok = fhOkK (LL F) (LL H) g N ok := by
  unfold fhOkLoop
  exact fhOk_eq F H G g hG N ok

theorem reflLoop_eq (n N : Nat) (R : Array IVec) (G : Array (Array Int)) (ix : HashMap IVec Nat)
    (ok : Bool) : reflLoop n N R G ix ok = reflA n R G ix N ok := by
  unfold reflLoop reflA
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yield (fun st i =>
    let r := (List.range' 0 N).foldl (reflCellA n R G ix i) (st.1, #[])
    (r.1, st.2.push r.2)) _ (fun i st => by
      rw [forIn_yield (reflCellA n R G ix i) _ (fun j st => by
        unfold reflCellA
        dsimp only
        split <;> rename_i hc <;> (try simp only [hc, ↓reduceIte, Bool.false_eq_true]) <;>
          split <;> rename_i heq <;> rw [heq] <;> rfl)]
      rfl)]
  rfl

theorem fhLoop_fold (mode n : Nat) (A B : Array (Array Int)) (sc : Array Int)
    (emb : Array (Array Nat)) (AR : Array IVec) :
    fhLoop mode n A B sc emb AR = AR.toList.foldl (fhStepA mode n A B sc emb) (true, #[], #[]) := by
  unfold fhLoop
  dsimp only
  rw [forIn_yieldA (fhStepA mode n A B sc emb) _ (fun r st => by
    unfold fhStepA
    dsimp only
    split <;> rename_i heq <;> rw [heq] <;> rfl)]
  rfl

theorem fhFold_eq (mode n : Nat) (A B : Array (Array Int)) (sc : Array Int)
    (emb : Array (Array Nat)) : ∀ (l : List IVec) (st : Bool × Array (Array Nat) × Array (Array Nat)),
    (l.foldl (fhStepA mode n A B sc emb) st).1 = ((l.map Array.toList).foldl
        (fhStepK mode n (LLI A) (LLI B) sc.toList (LL emb)) (st.1, LL st.2.1, LL st.2.2)).1 ∧
      LL (l.foldl (fhStepA mode n A B sc emb) st).2.1 = ((l.map Array.toList).foldl
        (fhStepK mode n (LLI A) (LLI B) sc.toList (LL emb)) (st.1, LL st.2.1, LL st.2.2)).2.1 ∧
      LL (l.foldl (fhStepA mode n A B sc emb) st).2.2 = ((l.map Array.toList).foldl
        (fhStepK mode n (LLI A) (LLI B) sc.toList (LL emb)) (st.1, LL st.2.1, LL st.2.2)).2.2
  | [], _ => ⟨rfl, rfl, rfl⟩
  | r :: l, st => by
    rw [List.foldl_cons, List.map_cons, List.foldl_cons]
    obtain ⟨e1, e2, e3⟩ := fhStep_eq mode n A B sc emb st r
    have := fhFold_eq mode n A B sc emb l (fhStepA mode n A B sc emb st r)
    rw [e1, e2, e3] at this
    exact this

theorem fhLoop_eq (mode n : Nat) (A B : Array (Array Int)) (sc : Array Int)
    (emb : Array (Array Nat)) (AR : Array IVec) :
    (fhLoop mode n A B sc emb AR).1 = ((LLI AR).foldl
        (fhStepK mode n (LLI A) (LLI B) sc.toList (LL emb)) (true, [], [])).1 ∧
      LL (fhLoop mode n A B sc emb AR).2.1 = ((LLI AR).foldl
        (fhStepK mode n (LLI A) (LLI B) sc.toList (LL emb)) (true, [], [])).2.1 ∧
      LL (fhLoop mode n A B sc emb AR).2.2 = ((LLI AR).foldl
        (fhStepK mode n (LLI A) (LLI B) sc.toList (LL emb)) (true, [], [])).2.2 := by
  rw [fhLoop_fold]
  exact fhFold_eq mode n A B sc emb AR.toList (true, #[], #[])

end Certificates.GilmanCensusK

end
