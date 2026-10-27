module

public import Certificates.Data.Kernel.EvenBN.F4Mat
public import Certificates.Data.U52Yamada

public section

namespace CFSG.KC.F4Mat

open CFSG.KC.Enum CFSG.Fischer CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo Certificates.U52Yamada

@[expose] def f4 (c : Nat) : F4 := ⟨⟨c % 4, Nat.mod_lt _ (by decide)⟩⟩

@[expose] noncomputable def decM (N : Nat) : Matrix (Fin 5) (Fin 5) F4 :=
  Matrix.of fun i j => f4 (ent N (5 * i.val + j.val))

theorem ent_eq (N k : Nat) : ent N k = N / 4 ^ k % 4 := rfl

theorem ent_lt (N k : Nat) : ent N k < 4 := Nat.mod_lt _ (by decide)

theorem encF_succ (f : Nat → Nat) (n s : Nat) :
    encF f (n + 1) s = f s + 4 * encF f n (s + 1) := rfl

theorem ent_encF {f : Nat → Nat} (hf : ∀ t, f t < 4) :
    ∀ n s k, k < n → ent (encF f n s) k = f (s + k)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, 0, _ => by
    rw [ent_eq, encF_succ, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hf s), Nat.add_zero]
  | n + 1, s, k + 1, h => by
    have ih := ent_encF hf n (s + 1) k (by omega)
    rw [ent_eq] at ih
    rw [ent_eq, encF_succ, Nat.pow_succ, Nat.mul_comm (4 ^ k) 4, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by decide : 0 < 4), Nat.div_eq_of_lt (hf s), Nat.zero_add, ih]
    congr 1
    omega

theorem f4_code (x : F4) : f4 (code x) = x := by
  obtain ⟨c⟩ := x
  unfold f4 code
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt c.isLt)

theorem code_lt (x : F4) : code x < 4 := x.code.isLt

theorem f4_ext {a b : F4} (h : a.code.val = b.code.val) : a = b := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  congr 1
  exact Fin.ext h

theorem decM_enc (M : Matrix (Fin 5) (Fin 5) F4) : decM (enc M) = M := by
  ext i j
  change f4 (ent (enc M) (5 * i.val + j.val)) = M i j
  refine (congrArg f4 (ent_encF (f := fun t => code (M ⟨Nat.mod (Nat.div t 5) 5,
    Nat.mod_lt _ (by decide)⟩ ⟨Nat.mod t 5, Nat.mod_lt _ (by decide)⟩)) (fun t => code_lt _) 25 0 _
    (by omega))).trans ?_
  have h1 : (⟨Nat.mod (Nat.div (0 + (5 * i.val + j.val)) 5) 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) =
      i := Fin.ext (by change (0 + (5 * i.val + j.val)) / 5 % 5 = i.val; omega)
  have h2 : (⟨Nat.mod (0 + (5 * i.val + j.val)) 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = j :=
    Fin.ext (by change (0 + (5 * i.val + j.val)) % 5 = j.val; omega)
  rw [h1, h2, f4_code]

theorem mt_ok' : ∀ x < 4, ∀ y < 4,
    (f4 (ent MT (4 * x + y))).code.val = (F4.mul (f4 x) (f4 y)).code.val := by decide

theorem bt_ok' : ∀ x < 4, (f4 (ent BT x)).code.val = (F4.mul (f4 x) (f4 x)).code.val := by decide

theorem xor_ok' : ∀ a < 4, ∀ b < 4,
    (f4 (Nat.xor a b)).code.val = (F4.add (f4 a) (f4 b)).code.val ∧ Nat.xor a b < 4 := by decide

theorem mt_ok {x y : Nat} (hx : x < 4) (hy : y < 4) : f4 (ent MT (4 * x + y)) = f4 x * f4 y :=
  f4_ext (mt_ok' x hx y hy)

theorem bt_ok {x : Nat} (hx : x < 4) : f4 (ent BT x) = bar (f4 x) := by
  rw [bar_apply, pow_two]
  exact f4_ext (bt_ok' x hx)

theorem xor_ok {a b : Nat} (ha : a < 4) (hb : b < 4) :
    f4 (Nat.xor a b) = f4 a + f4 b ∧ Nat.xor a b < 4 :=
  ⟨f4_ext (xor_ok' a ha b hb).1, (xor_ok' a ha b hb).2⟩

theorem mt_eq (A B i j k : Nat) :
    f4 (mt A B i j k) = f4 (ent A (5 * i + k)) * f4 (ent B (5 * k + j)) :=
  mt_ok (ent_lt _ _) (ent_lt _ _)

theorem dotK_eq (A B i j : Nat) : f4 (dotK A B i j) =
    f4 (ent A (5 * i + 0)) * f4 (ent B (5 * 0 + j)) + f4 (ent A (5 * i + 1)) * f4 (ent B (5 * 1 + j)) +
      f4 (ent A (5 * i + 2)) * f4 (ent B (5 * 2 + j)) +
      f4 (ent A (5 * i + 3)) * f4 (ent B (5 * 3 + j)) +
      f4 (ent A (5 * i + 4)) * f4 (ent B (5 * 4 + j)) ∧ dotK A B i j < 4 := by
  have m : ∀ k, mt A B i j k < 4 := fun k => ent_lt _ _
  obtain ⟨e1, l1⟩ := xor_ok (m 0) (m 1)
  obtain ⟨e2, l2⟩ := xor_ok l1 (m 2)
  obtain ⟨e3, l3⟩ := xor_ok l2 (m 3)
  obtain ⟨e4, l4⟩ := xor_ok l3 (m 4)
  refine ⟨?_, l4⟩
  unfold dotK
  rw [e4, e3, e2, e1, mt_eq, mt_eq, mt_eq, mt_eq, mt_eq]

theorem dotK_lt (A B i j : Nat) : dotK A B i j < 4 := (dotK_eq A B i j).2

theorem strictN_app (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem decM_mulK (A B : Nat) : decM (mulK A B) = decM A * decM B := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  change f4 (ent (mulK A B) (5 * i.val + j.val)) = _
  simp only [mulK, strictN_app]
  refine (congrArg f4 (ent_encF (f := fun t => dotK A B (Nat.div t 5) (Nat.mod t 5))
    (fun t => dotK_lt _ _ _ _) 25 0 _ (by omega))).trans ?_
  have h1 : Nat.div (0 + (5 * i.val + j.val)) 5 = i.val := by
    change (0 + (5 * i.val + j.val)) / 5 = i.val
    omega
  have h2 : Nat.mod (0 + (5 * i.val + j.val)) 5 = j.val := by
    change (0 + (5 * i.val + j.val)) % 5 = j.val
    omega
  rw [h1, h2, (dotK_eq A B i.val j.val).1, Matrix.mul_apply, Fin.sum_univ_five]
  rfl

theorem invMat_eq (M : Matrix (Fin 5) (Fin 5) F4) :
    invMat M = Matrix.of fun i j => bar (M (Fin.rev j) (Fin.rev i)) := by
  have h := ofArr_invA (toArr M)
  rw [ofArr_toArr] at h
  rw [← h, invA, ofArr_toArr, ofArr_toArr]

theorem decM_invK (A : Nat) : decM (invK A) = invMat (decM A) := by
  rw [invMat_eq]
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  change f4 (ent (invK A) (5 * i.val + j.val)) =
    bar (f4 (ent A (5 * (Fin.rev j).val + (Fin.rev i).val)))
  simp only [invK, strictN_app]
  refine (congrArg f4 (ent_encF (f := fun t => ent BT (ent A (Nat.add (Nat.mul 5
    (Nat.sub 4 (Nat.mod t 5))) (Nat.sub 4 (Nat.div t 5))))) (fun t => ent_lt _ _) 25 0 _
    (by omega))).trans ?_
  have h1 : Nat.add (Nat.mul 5 (Nat.sub 4 (Nat.mod (0 + (5 * i.val + j.val)) 5)))
      (Nat.sub 4 (Nat.div (0 + (5 * i.val + j.val)) 5)) =
      5 * (Fin.rev j).val + (Fin.rev i).val := by
    change 5 * (4 - (0 + (5 * i.val + j.val)) % 5) + (4 - (0 + (5 * i.val + j.val)) / 5) = _
    rw [Fin.val_rev, Fin.val_rev]
    omega
  rw [h1]
  exact bt_ok (ent_lt _ _)

theorem chkL_spec {N : Nat} : ∀ {L : List (Nat × Nat)}, chkL N L = true → ∀ p ∈ L, ent N p.1 = p.2
  | [], _, _, hp => absurd hp List.not_mem_nil
  | (k, v) :: L, h, p, hp => by
    unfold chkL at h
    rw [strictB_app] at h
    have h' : Bool.rec (motive := fun _ => Bool) false (chkL N L) (Nat.beq (ent N k) v) = true := by
      unfold chkL
      rw [strictB_app]
      exact h
    cases e : Nat.beq (ent N k) v
    · rw [e] at h'
      exact absurd h' Bool.false_ne_true
    · rw [e] at h'
      rcases List.mem_cons.1 hp with rfl | hp
      · exact Nat.eq_of_beq_eq_true e
      · exact chkL_spec h' p hp

theorem fShape_upper : ∀ i j : Fin 5, i < j → (5 * i.val + j.val, 0) ∈ fShapeL := by decide

theorem fShape_diag : ∀ i : Fin 5, (5 * i.val + i.val, 1) ∈ fShapeL := by decide

theorem fShape_of {N : Nat} (h : chkL N fShapeL = true) : IsFShape (decM N) := by
  have hv := chkL_spec h
  refine ⟨fun i j hij => ?_, fun i => ?_, ?_, ?_, ?_⟩
  · change f4 (ent N (5 * i.val + j.val)) = 0
    rw [hv _ (fShape_upper i j hij)]
    rfl
  · change f4 (ent N (5 * i.val + i.val)) = 1
    rw [hv _ (fShape_diag i)]
    rfl
  · change f4 (ent N 11) = 0
    rw [hv (11, 0) (by decide)]
    rfl
  · change f4 (ent N 5) = 0
    rw [hv (5, 0) (by decide)]
    rfl
  · change f4 (ent N 10) = 0
    rw [hv (10, 0) (by decide)]
    rfl

end CFSG.KC.F4Mat

end
