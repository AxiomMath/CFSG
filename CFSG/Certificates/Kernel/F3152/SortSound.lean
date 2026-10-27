module

public import Certificates.Data.Kernel.F3152.Forms

public section

namespace CFSG.KS.F3152

theorem mergeK_perm : ∀ (n : Nat) (a b : List Nat), (mergeK n a b).Perm (a ++ b)
  | 0, a, b => by
    unfold mergeK
    exact List.Perm.refl _
  | _ + 1, [], b => by
    unfold mergeK
    exact List.Perm.refl _
  | _ + 1, x :: a, [] => by
    unfold mergeK
    rw [List.append_nil]
  | n + 1, x :: a, y :: b => by
    unfold mergeK
    cases Nat.blt x y
    · exact ((mergeK_perm n (x :: a) b).cons y).trans List.perm_middle.symm
    · exact (mergeK_perm n a (y :: b)).cons x

theorem pairK_perm (f : Nat) : ∀ L : List (List Nat), (pairK f L).flatten.Perm L.flatten
  | [] => by
    unfold pairK
    exact List.Perm.refl _
  | [a] => by
    unfold pairK
    exact List.Perm.refl _
  | a :: b :: l => by
    unfold pairK
    rw [List.flatten_cons, List.flatten_cons, List.flatten_cons, ← List.append_assoc]
    exact (mergeK_perm f a b).append (pairK_perm f l)

theorem passK_perm (f : Nat) : ∀ (n : Nat) (L : List (List Nat)), (passK f n L).flatten.Perm L.flatten
  | 0, L => by
    unfold passK
    exact List.Perm.refl _
  | n + 1, L => by
    unfold passK
    exact (passK_perm f n (pairK f L)).trans (pairK_perm f L)

theorem flatten_singletons : ∀ ks : List Nat, (ks.map fun k => [k]).flatten = ks
  | [] => rfl
  | k :: ks => by
    rw [List.map_cons, List.flatten_cons, flatten_singletons ks]
    rfl

theorem msortK_perm (ks : List Nat) : (msortK ks).Perm ks := by
  unfold msortK
  have h := passK_perm 8192 12 (ks.map fun k => [k])
  rw [flatten_singletons] at h
  exact h

theorem sortedK_pairwise : ∀ l : List Nat, sortedK l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [x], _ => List.pairwise_singleton _ x
  | x :: y :: l, h => by
    unfold sortedK at h
    cases hxy : Nat.blt x y
    · rw [hxy] at h
      exact absurd h Bool.false_ne_true
    · rw [hxy] at h
      have ih := sortedK_pairwise (y :: l) h
      have hlt : x < y := Nat.le_of_ble_eq_true hxy
      refine List.Pairwise.cons (fun z hz => ?_) ih
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hlt
      · exact Nat.lt_trans hlt (List.rel_of_pairwise_cons ih hz)

theorem nodup_of_sortedK {ks : List Nat} (h : sortedK (msortK ks) = true) : ks.Nodup :=
  (msortK_perm ks).nodup_iff.1 ((sortedK_pairwise _ h).imp Nat.ne_of_lt)

end CFSG.KS.F3152

end
