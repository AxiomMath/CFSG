module

public import CFSG.Certificates.Kernel.Misc.YamakiLbarSound2

public section

namespace CFSG.KC.YamakiLbar

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiLbar
  CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0 CFSG.KC.YamakiA0 CFSG.KC.Misc.Spec Matrix
  CFSG.KD.YamakiA0
open CFSG.KD.Sp62 (MULF ONE)
open CFSG.KC.Sp62 (MULF_lt pkMat_MULF pkMat_inj)

theorem push_fold {α : Type} [Inhabited α] (x0 : α) (P : ℕ → ℕ) (g : α → ℕ → α) :
    ∀ k, (∀ i, 0 < i → i ≤ k → P i < i) →
      ((List.range' 1 k).foldl (fun F i => F.push (g F[P i]! i)) #[x0]).size = k + 1 ∧
      ((List.range' 1 k).foldl (fun F i => F.push (g F[P i]! i)) #[x0])[0]! = x0 ∧
      ∀ i, 0 < i → i ≤ k →
        ((List.range' 1 k).foldl (fun F i => F.push (g F[P i]! i)) #[x0])[i]! =
          g ((List.range' 1 k).foldl (fun F i => F.push (g F[P i]! i)) #[x0])[P i]! i
  | 0, _ => ⟨rfl, rfl, fun i h1 h2 => by omega⟩
  | k + 1, hP => by
    obtain ⟨s1, s2, s3⟩ := push_fold x0 P g k fun i h1 h2 => hP i h1 (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range' 1 k).foldl (fun F i => F.push (g F[P i]! i)) #[x0] = F at s1 s2 s3 ⊢
    have e : 1 + 1 * k = k + 1 := by omega
    rw [e]
    refine ⟨by simp [s1], by rw [push_lt (by omega), s2], fun i h1 h2 => ?_⟩
    have hp := hP i h1 h2
    by_cases hik : i ≤ k
    · rw [push_lt (by omega), push_lt (by omega), s3 i h1 hik]
    · have hi : i = k + 1 := by omega
      subst hi
      have := push_eq (a := F) (x := g F[P (k + 1)]! (k + 1))
      rw [s1] at this
      rw [this, push_lt (by omega)]

theorem buildF_eq (E : Enum) (hs : Array (Array ℕ)) :
    buildF E hs = (List.range' 1 (E.elems.size - 1)).foldl
      (fun F i => F.push (compA F[E.parent[i]!]! hs[E.gen[i]!]!)) #[idA ()] := by
  unfold buildF
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.add_sub_cancel,
    Nat.div_one, bind_pure]
  exact forIn_foldl _ _ _ _ fun j b => rfl

theorem z6BuildF_eq (mul : Array (Array ℕ)) (E : Enum) (img : Array ℕ) :
    z6BuildF mul E img = (List.range' 1 63).foldl
      (fun F k => F.push ((mul[F[E.parent[k]!]!]!)[img[E.gen[k]!]!]!)) #[0] := by
  unfold z6BuildF
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.add_sub_cancel,
    Nat.div_one, bind_pure]
  exact forIn_foldl _ _ _ _ fun j b => rfl

theorem buildF_facts (E : Enum) (hs : Array (Array ℕ)) (hn : 0 < E.elems.size)
    (hP : ∀ i, 0 < i → i < E.elems.size → E.parent[i]! < i) :
    (buildF E hs).size = E.elems.size ∧ (buildF E hs)[0]! = idA () ∧
      ∀ i, 0 < i → i < E.elems.size →
        (buildF E hs)[i]! = compA (buildF E hs)[E.parent[i]!]! hs[E.gen[i]!]! := by
  obtain ⟨a, b, c⟩ := push_fold (idA ()) (fun i => E.parent[i]!)
    (fun x i => compA x hs[E.gen[i]!]!) (E.elems.size - 1) fun i h1 h2 => hP i h1 (by omega)
  rw [buildF_eq]
  exact ⟨a.trans (by omega), b, fun i h1 h2 => c i h1 (by omega)⟩

theorem z6BuildF_facts (mul : Array (Array ℕ)) (E : Enum) (img : Array ℕ)
    (hP : ∀ k, 0 < k → k < 64 → E.parent[k]! < k) :
    (z6BuildF mul E img).size = 64 ∧ (z6BuildF mul E img)[0]! = 0 ∧
      ∀ k, 0 < k → k < 64 → (z6BuildF mul E img)[k]! =
        (mul[(z6BuildF mul E img)[E.parent[k]!]!]!)[img[E.gen[k]!]!]! := by
  obtain ⟨a, b, c⟩ := push_fold (0 : ℕ) (fun k => E.parent[k]!)
    (fun x k => (mul[x]!)[img[E.gen[k]!]!]!) 63 fun k h1 h2 => hP k h1 (by omega)
  rw [z6BuildF_eq]
  exact ⟨a, b, fun k h1 h2 => c k h1 (by omega)⟩

theorem trK_lt (x : ℕ) : trK x < 2 := by
  unfold trK
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem trK_cast (x : ℕ) : ((trK x : ℕ) : ZMod 2) = Matrix.trace (pkMat 6 x) := by
  have h1 : trK x = (x ^^^ (x >>> 7) ^^^ (x >>> 14) ^^^ (x >>> 21) ^^^ (x >>> 28) ^^^
      (x >>> 35)) % 2 := by
    unfold trK
    exact Nat.and_one_is_mod _
  have h2 : ∀ y : ℕ, y % 2 = if y.testBit 0 then 1 else 0 := by
    intro y
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one y with h | h <;> simp [h]
  have e : Matrix.trace (pkMat 6 x) = (if x.testBit 0 then 1 else 0) +
      (if x.testBit 7 then 1 else 0) + (if x.testBit 14 then 1 else 0) +
      (if x.testBit 21 then 1 else 0) + (if x.testBit 28 then 1 else 0) +
      (if x.testBit 35 then 1 else 0) := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_six, pkMat, Matrix.of_apply]
    rfl
  rw [h1, h2, e]
  simp only [Nat.testBit_xor, Nat.testBit_shiftRight, Nat.add_zero]
  generalize x.testBit 0 = b0
  generalize x.testBit 7 = b1
  generalize x.testBit 14 = b2
  generalize x.testBit 21 = b3
  generalize x.testBit 28 = b4
  generalize x.testBit 35 = b5
  revert b0 b1 b2 b3 b4 b5
  decide

theorem left_inv {G : ℕ} (hker : ∀ x < 64, 0 < x → MULF x G ≠ 0) :
    ∃ H, pkMat 6 H * pkMat 6 G = 1 ∧ pkMat 6 G * pkMat 6 H = 1 := by
  have hinj : Set.InjOn (fun x => MULF x G) (Finset.range 64 : Set ℕ) := by
    intro x hx y hy e
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    simp only at e
    by_contra hne
    have h0 : MULF (x ^^^ y) G = 0 := by rw [xor_mulF, e, Nat.xor_self]
    have hpos : 0 < x ^^^ y := by
      refine Nat.pos_of_ne_zero fun h => hne ?_
      have := congrArg (· ^^^ y) h
      simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at this
      exact this
    exact hker _ (xor_lt64 hx hy) hpos h0
  have himg : (Finset.range 64).image (fun x => MULF x G) = Finset.range 64 := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_image, Finset.mem_range] at hz ⊢
      obtain ⟨x, hx, rfl⟩ := hz
      exact vec_lt hx G
    · exact (Finset.card_image_of_injOn hinj).ge
  have hsurj : ∀ j < 6, ∃ y, y < 64 ∧ MULF y G = 2 ^ j := by
    intro j hj
    have : 2 ^ j ∈ (Finset.range 64).image (fun x => MULF x G) := by
      rw [himg, Finset.mem_range]
      exact pow_lt64 hj
    simpa only [Finset.mem_image, Finset.mem_range] using this
  choose! f hf1 hf2 using hsurj
  have hrows : ∀ r ∈ [f 0, f 1, f 2, f 3, f 4, f 5], r < 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact hf1 _ (by norm_num)
  have hHG : MULF (packL [f 0, f 1, f 2, f 3, f 4, f 5]) G = ONE := by
    refine rows_ext (MULF_lt _ _) ONE_lt fun j hj => ?_
    rw [← mulF_assoc, row_packL hrows hj, mulF_one (lt36 (pow_lt64 hj))]
    interval_cases j <;> exact hf2 _ (by norm_num)
  have h1 : pkMat 6 (packL [f 0, f 1, f 2, f 3, f 4, f 5]) * pkMat 6 G = 1 := by
    rw [← pkMat_MULF, hHG, pkMat_ONE]
  exact ⟨_, h1, mul_eq_one_comm.1 h1⟩

theorem trK_conj {M G X : ℕ} (hker : ∀ x < 64, 0 < x → MULF x G ≠ 0)
    (h : MULF M G = MULF G X) : trK X = trK M := by
  obtain ⟨H, h1, h2⟩ := left_inv hker
  have e : pkMat 6 X = pkMat 6 H * pkMat 6 M * pkMat 6 G := by
    have := congrArg (pkMat 6 H * ·) (congrArg (pkMat 6) h)
    simp only [pkMat_MULF] at this
    rw [mul_assoc, this, ← mul_assoc, h1, one_mul]
  have et : ((trK X : ℕ) : ZMod 2) = ((trK M : ℕ) : ZMod 2) := by
    rw [trK_cast, trK_cast, e, Matrix.trace_mul_cycle, h2, one_mul]
  have := congrArg ZMod.val et
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (trK_lt X),
    Nat.mod_eq_of_lt (trK_lt M)] at this

theorem mulF_nxor (N a b : ℕ) : MULF N (Nat.xor a b) = Nat.xor (MULF N a) (MULF N b) :=
  mulF_xor N a b

theorem nxor_mulF (a b N : ℕ) : MULF (Nat.xor a b) N = Nat.xor (MULF a N) (MULF b N) :=
  xor_mulF a b N

theorem nxor_zero (a : ℕ) : Nat.xor a 0 = a := Nat.xor_zero a

theorem boolN_eq (y : ℕ) (k : ℕ → Bool) : boolN y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def sOf (A B : ℕ) (j : ℕ) : ℕ :=
  [Nat.xor ONE (Nat.xor (MULF B B) (MULF B (MULF A (MULF B B)))),
    Nat.xor ONE (Nat.xor B (MULF B A)), ONE,
    Nat.xor B (Nat.xor (MULF B B) (MULF B (MULF A B))), B, MULF B B].getD j 0

@[expose] noncomputable def gOf (c A B : ℕ) : ℕ :=
  gmat6 c (sOf A B 0) (sOf A B 1) (sOf A B 2) (sOf A B 3) (sOf A B 4) (sOf A B 5)

@[expose] noncomputable def lamOf (A B : ℕ) (m : ℕ) : ℕ :=
  [ONE, A, B, MULF B A, MULF A B, MULF B B, 0, 0, MULF B (MULF A B), MULF A (MULF B B), 0, 0, 0, 0,
    MULF B (MULF A (MULF B B))].getD m 0

theorem gOf_lt {c : ℕ} (hc : c < 64) (A B : ℕ) : gOf c A B < 2 ^ 36 := gmat6_lt hc _ _ _ _ _ _

theorem row_gOf {c : ℕ} (hc : c < 64) (A B : ℕ) {j : ℕ} (hj : j < 6) :
    MULF (2 ^ j) (gOf c A B) = MULF c (sOf A B j) :=
  row_gmat6 hc (sOf A B) hj

theorem gOf_conj {c Sm Si A B : ℕ} (hc : c < 64) (hr : MULF c Sm < 64)
    (hSS : pkMat 6 Sm * pkMat 6 Si = 1) :
    MULF (gOf c A B) Sm =
      gOf (MULF c Sm) (MULF (MULF Si A) Sm) (MULF (MULF Si B) Sm) := by
  have kmul : ∀ X Y : ℕ, MULF (MULF (MULF Si X) Sm) (MULF (MULF Si Y) Sm) =
      MULF (MULF Si (MULF X Y)) Sm := by
    intro X Y
    refine pkMat_inj (MULF_lt _ _) (MULF_lt _ _) ?_
    simp only [pkMat_MULF, mul_assoc]
    rw [← mul_assoc (pkMat 6 Sm) (pkMat 6 Si), hSS, one_mul]
  have kone : MULF Sm (MULF (MULF Si ONE) Sm) = MULF ONE Sm := by
    refine pkMat_inj (MULF_lt _ _) (MULF_lt _ _) ?_
    simp only [pkMat_MULF, pkMat_ONE, mul_one, one_mul]
    rw [← mul_assoc, hSS, one_mul]
  have kS : ∀ X : ℕ, MULF Sm (MULF (MULF Si X) Sm) = MULF X Sm := by
    intro X
    refine pkMat_inj (MULF_lt _ _) (MULF_lt _ _) ?_
    simp only [pkMat_MULF]
    rw [← mul_assoc, ← mul_assoc, hSS, one_mul]
  have hSm1 : MULF Sm ONE = MULF ONE Sm := by
    refine pkMat_inj (MULF_lt _ _) (MULF_lt _ _) ?_
    simp only [pkMat_MULF, pkMat_ONE, mul_one, one_mul]
  refine rows_ext (MULF_lt _ _) (gOf_lt hr _ _) fun j hj => ?_
  rw [← mulF_assoc, row_gOf hc _ _ hj, row_gOf hr _ _ hj, mulF_assoc, mulF_assoc]
  congr 1
  interval_cases j
  · change MULF (Nat.xor ONE (Nat.xor (MULF B B) (MULF B (MULF A (MULF B B))))) Sm =
      MULF Sm (Nat.xor ONE (Nat.xor (MULF (MULF (MULF Si B) Sm) (MULF (MULF Si B) Sm))
        (MULF (MULF (MULF Si B) Sm) (MULF (MULF (MULF Si A) Sm)
          (MULF (MULF (MULF Si B) Sm) (MULF (MULF Si B) Sm))))))
    simp only [kmul]
    rw [mulF_nxor, mulF_nxor, kS, kS]
    rw [nxor_mulF, nxor_mulF, hSm1]
  · change MULF (Nat.xor ONE (Nat.xor B (MULF B A))) Sm =
      MULF Sm (Nat.xor ONE (Nat.xor (MULF (MULF Si B) Sm)
        (MULF (MULF (MULF Si B) Sm) (MULF (MULF Si A) Sm))))
    simp only [kmul]
    rw [mulF_nxor, mulF_nxor, kS, kS]
    rw [nxor_mulF, nxor_mulF, hSm1]
  · change MULF ONE Sm = MULF Sm ONE
    exact hSm1.symm
  · change MULF (Nat.xor B (Nat.xor (MULF B B) (MULF B (MULF A B)))) Sm =
      MULF Sm (Nat.xor (MULF (MULF Si B) Sm) (Nat.xor
        (MULF (MULF (MULF Si B) Sm) (MULF (MULF Si B) Sm))
        (MULF (MULF (MULF Si B) Sm) (MULF (MULF (MULF Si A) Sm) (MULF (MULF Si B) Sm)))))
    simp only [kmul]
    rw [mulF_nxor, mulF_nxor, kS, kS, kS]
    rw [nxor_mulF, nxor_mulF]
  · change MULF B Sm = MULF Sm (MULF (MULF Si B) Sm)
    rw [kS]
  · change MULF (MULF B B) Sm = MULF Sm (MULF (MULF (MULF Si B) Sm) (MULF (MULF Si B) Sm))
    rw [kmul, kS]

end CFSG.KC.YamakiLbar

end
