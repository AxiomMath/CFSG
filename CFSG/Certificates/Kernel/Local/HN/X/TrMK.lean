module

public import CFSG.Certificates.Kernel.Local.HN.X.Lib

public section

namespace CFSG.KC.LL.HNX

open CFSG.KC.Loop CFSG.KC.LL

@[expose] noncomputable def trRow (a j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (fldW (fldW a (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) (Nat.mul (nat_lit 13) j) (nat_lit 13))
      (Nat.mul (nat_lit 13) i))) (nat_lit 133)

@[expose] noncomputable def trMK (a : Nat) : Nat :=
  strictN a (fun a => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.lor acc (Nat.shiftLeft (trRow a j) (Nat.mul (nat_lit 1729) j))) (nat_lit 133))

@[expose] def orT (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.lor (orT f n) (f n)

theorem strictN_eqT (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem lorT0 (x : Nat) : Nat.lor (nat_lit 0) x = x := Nat.zero_or x

theorem shlT_shl (x a b : Nat) :
    Nat.shiftLeft (Nat.shiftLeft x a) b = Nat.shiftLeft x (Nat.add a b) :=
  (Nat.shiftLeft_add x a b).symm

theorem recT_lor (s : Nat) (F : Nat → Nat → Nat) (g : Nat → Nat)
    (hF : ∀ j acc, F j acc = Nat.lor acc (g j)) : ∀ m,
    Nat.rec (motive := fun _ => Nat) s F m = Nat.lor s (orT g m)
  | 0 => (Nat.or_zero s).symm
  | m + 1 => by
    show F m (Nat.rec (motive := fun _ => Nat) s F m) = Nat.lor s (Nat.lor (orT g m) (g m))
    rw [hF, recT_lor s F g hF m]
    exact Nat.or_assoc s (orT g m) (g m)

theorem orT_lor (f g : Nat → Nat) : ∀ m,
    orT (fun j => Nat.lor (f j) (g j)) m = Nat.lor (orT f m) (orT g m)
  | 0 => (Nat.zero_or 0).symm
  | m + 1 => by
    show Nat.lor (orT (fun j => Nat.lor (f j) (g j)) m) (Nat.lor (f m) (g m)) =
      Nat.lor (Nat.lor (orT f m) (f m)) (Nat.lor (orT g m) (g m))
    rw [orT_lor f g m]
    show (orT f m ||| orT g m) ||| (f m ||| g m) = (orT f m ||| f m) ||| (orT g m ||| g m)
    rw [Nat.or_assoc, Nat.or_assoc, ← Nat.or_assoc (orT g m) (f m), Nat.or_comm (orT g m) (f m),
      Nat.or_assoc (f m)]

theorem orT_zero (m : Nat) : orT (fun _ => 0) m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => show Nat.lor (orT (fun _ => 0) m) 0 = 0; rw [ih]; rfl

theorem orT_swap (t : Nat → Nat → Nat) (m : Nat) : ∀ n,
    orT (fun i => orT (t i) m) n = orT (fun j => orT (fun i => t i j) n) m
  | 0 => (orT_zero m).symm
  | n + 1 => by
    show Nat.lor (orT (fun i => orT (t i) m) n) (orT (t n) m) =
      orT (fun j => Nat.lor (orT (fun i => t i j) n) (t n j)) m
    rw [orT_swap t m n, orT_lor]

theorem shl_orT (f : Nat → Nat) (k : Nat) : ∀ n,
    Nat.shiftLeft (orT f n) k = orT (fun i => Nat.shiftLeft (f i) k) n
  | 0 => Nat.zero_shiftLeft k
  | n + 1 => by
    show Nat.shiftLeft (Nat.lor (orT f n) (f n)) k =
      Nat.lor (orT (fun i => Nat.shiftLeft (f i) k) n) (Nat.shiftLeft (f n) k)
    rw [← shl_orT f k n]
    exact Nat.shiftLeft_or_distrib

@[expose] noncomputable def trEnt (a i j : Nat) : Nat :=
  Nat.shiftLeft (fldW (fldW a (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) (Nat.mul (nat_lit 13) j)
    (nat_lit 13)) (Nat.add (Nat.mul (nat_lit 1729) j) (Nat.mul (nat_lit 13) i))

theorem trM_rec (a n : Nat) :
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => strictN acc (fun s => strictN (fldW a (Nat.mul (nat_lit 1729) i) (nat_lit 1729))
        (fun row => Nat.rec (motive := fun _ => Nat) s
          (fun j acc2 => Nat.lor acc2 (Nat.shiftLeft (fldW row (Nat.mul (nat_lit 13) j) (nat_lit 13))
            (Nat.add (Nat.mul (nat_lit 1729) j) (Nat.mul (nat_lit 13) i)))) (nat_lit 133)))) n =
    orT (fun i => orT (fun j => trEnt a i j) (nat_lit 133)) n :=
  (recT_lor (nat_lit 0) _ (fun i => orT (fun j => trEnt a i j) (nat_lit 133)) (fun i acc => by
    rw [strictN_eqT, strictN_eqT]
    exact recT_lor acc (fun j acc2 => Nat.lor acc2 (trEnt a i j)) (fun j => trEnt a i j)
      (fun j acc2 => rfl) (nat_lit 133)) n).trans (lorT0 _)

theorem trM_orT (a : Nat) :
    trM a = orT (fun i => orT (fun j => trEnt a i j) (nat_lit 133)) (nat_lit 133) :=
  trM_rec a 133

theorem trRow_orT (a j : Nat) :
    Nat.shiftLeft (trRow a j) (Nat.mul (nat_lit 1729) j) = orT (fun i => trEnt a i j) (nat_lit 133) := by
  have h := recT_lor (nat_lit 0) (fun i acc => Nat.lor acc (Nat.shiftLeft (fldW (fldW a
    (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) (Nat.mul (nat_lit 13) j) (nat_lit 13)) (Nat.mul (nat_lit 13) i)))
    (fun i => Nat.shiftLeft (fldW (fldW a (Nat.mul (nat_lit 1729) i)
    (nat_lit 1729)) (Nat.mul (nat_lit 13) j) (nat_lit 13)) (Nat.mul (nat_lit 13) i))
    (fun i acc2 => rfl) (nat_lit 133)
  unfold trRow
  rw [h, lorT0, shl_orT]
  congr 1
  funext i
  unfold trEnt
  exact (shlT_shl _ _ _).trans (congrArg _ (Nat.add_comm _ _))

theorem trMK_rec (a n : Nat) :
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => Nat.lor acc (Nat.shiftLeft (trRow a j) (Nat.mul (nat_lit 1729) j))) n =
    orT (fun j => orT (fun i => trEnt a i j) (nat_lit 133)) n :=
  (recT_lor (nat_lit 0) _ (fun j => orT (fun i => trEnt a i j) (nat_lit 133))
    (fun j acc => by rw [trRow_orT]) n).trans (lorT0 _)

theorem trMK_orT (a : Nat) :
    trMK a = orT (fun j => orT (fun i => trEnt a i j) (nat_lit 133)) (nat_lit 133) := by
  unfold trMK
  rw [strictN_eqT]
  exact trMK_rec a 133

theorem trM_eq (a : Nat) : trM a = trMK a := by
  rw [trM_orT, trMK_orT, orT_swap]

end CFSG.KC.LL.HNX

end
