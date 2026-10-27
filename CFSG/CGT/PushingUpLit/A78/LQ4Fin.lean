module

public section

namespace CFSG.CGT.PushingUpLit.A78.LQ4Fin

@[expose] def mulVec : List Nat → Nat → Nat
  | [], _ => 0
  | a :: as, v => (if v % 2 = 1 then a else 0) ^^^ mulVec as (v / 2)

@[expose] def mul (A B : List Nat) : List Nat := B.map (mulVec A)

@[expose] def idM : List Nat := [1, 2, 4, 8]

@[expose] def A0 : List (List Nat) :=
  [[1, 2, 4, 8], [1, 2, 8, 12], [1, 2, 12, 4], [1, 3, 4, 12], [1, 3, 8, 4], [1, 3, 12, 8], [2, 1, 4,
   12], [2, 1, 8, 4], [2, 1, 12, 8], [2, 3, 4, 8], [2, 3, 8, 12], [2, 3, 12, 4], [3, 1, 4, 8], [3,
   1, 8, 12], [3, 1, 12, 4], [3, 2, 4, 12], [3, 2, 8, 4], [3, 2, 12, 8], [4, 8, 1, 2], [4, 8, 2, 3],
   [4, 8, 3, 1], [4, 12, 1, 3], [4, 12, 2, 1], [4, 12, 3, 2], [8, 4, 1, 3], [8, 4, 2, 1], [8, 4, 3,
   2], [8, 12, 1, 2], [8, 12, 2, 3], [8, 12, 3, 1], [12, 4, 1, 2], [12, 4, 2, 3], [12, 4, 3, 1],
   [12, 8, 1, 3], [12, 8, 2, 1], [12, 8, 3, 2]]

@[expose] def subs : List Nat :=
  [1, 3, 5, 9, 15, 17, 33, 51, 65, 85, 105, 129, 153, 165, 195, 255, 257, 513, 771, 1025, 1285,
   1545, 2049, 2313, 2565, 3075, 3855, 4097, 4369, 4641, 5185, 6273, 8193, 8481, 8721, 9345, 10305,
   12291, 13107, 15555, 16385, 16705, 17025, 17425, 18465, 20485, 21845, 23205, 24585, 26265, 26985,
   32769, 33153, 33345, 33825, 34833, 36873, 38505, 39321, 40965, 42405, 43605, 49155, 50115, 52275,
   61455, 65535]

@[expose] def mul4 (a c : Nat) : Nat :=
  let a1 := a &&& 1
  let a2 := (a >>> 1) &&& 1
  let c1 := c &&& 1
  let c2 := (c >>> 1) &&& 1
  ((a1 &&& c1) ^^^ (a2 &&& c2)) ||| ((((a1 &&& c2) ^^^ (a2 &&& c1)) ^^^ (a2 &&& c2)) <<< 1)

@[expose] def qv (v : Nat) : Nat := mul4 (v &&& 3) ((v >>> 2) &&& 3)

@[expose] def members (m : Nat) : List Nat := (List.range 16).filter fun v => m.testBit v

@[expose] def popc (m : Nat) : Nat := (members m).length

@[expose] def joinMask (m v : Nat) : Nat :=
  if m.testBit v then m else (members m).foldl (fun acc x => acc ||| (1 <<< (x ^^^ v))) m

@[expose] def spanMask (l : List Nat) : Nat := l.foldl joinMask 1

@[expose] def invariantB (A : List Nat) (m : Nat) : Bool :=
  (members m).all fun v => m.testBit (mulVec A v)

@[expose] def commList (A₁ A₂ : List Nat) (m : Nat) : List Nat :=
  (members m).flatMap fun v => [mulVec A₁ v ^^^ v, mulVec A₂ v ^^^ v]

@[expose] def qList (m : Nat) : List Nat := (members m).map qv

@[expose] def pOf (A₁ A₂ : List Nat) : Nat := ([idM, A₁, A₂, mul A₁ A₂].eraseDups).length

@[expose] def boundB (A₁ A₂ : List Nat) (m : Nat) : Bool :=
  pOf A₁ A₂ * popc m * 4 ≤ 16 * popc (spanMask (commList A₁ A₂ m)) * popc (spanMask (qList m))

@[expose] def invs : List (List Nat) := A0.filter fun A => mul A A == idM

@[expose] def zero0 : List Nat := [0, 1, 2, 3, 4, 8, 12]

@[expose] def gl2 : List (List Nat) := [[1, 2], [2, 1], [1, 3], [3, 1], [2, 3], [3, 2]]

@[expose] def okQ (A : List Nat) : Bool :=
  gl2.any fun g => (List.range 16).all fun v => qv (mulVec A v) == mulVec g (qv v)

@[expose] def okInj (A : List Nat) : Bool := (List.range 16).all fun v => v == 0 || mulVec A v != 0

@[expose] def iter6 (f : Nat → Nat) (v : Nat) : Nat := f (f (f (f (f (f v)))))

theorem mem_members {m v : Nat} : v ∈ members m ↔ v < 16 ∧ m.testBit v = true := by
  simp [members, List.mem_filter, List.mem_range]

theorem invariantB_iff {A : List Nat} {m : Nat} :
    invariantB A m = true ↔ ∀ v, v < 16 → m.testBit v = true → m.testBit (mulVec A v) = true := by
  simp [invariantB, List.all_eq_true, mem_members]

theorem mem_invs {A : List Nat} : A ∈ invs ↔ A ∈ A0 ∧ mul A A = idM := by
  simp [invs, List.mem_filter]

theorem zero0_of {v : Nat} (hv : v < 16) (h : qv v = 0) : v ∈ zero0 := by
  revert v; decide +kernel

set_option synthInstance.maxSize 1024 in
theorem gl2_of {a : Nat} (ha : a < 4) {b : Nat} (hb : b < 4) (h0 : a ≠ 0) (h0' : b ≠ 0)
    (h : a ≠ b) : [a, b] ∈ gl2 := by
  have key : ∀ a, a < 4 → ∀ b, b < 4 → a ≠ 0 → b ≠ 0 → a ≠ b → [a, b] ∈ gl2 := by decide +kernel
  exact key a ha b hb h0 h0' h

theorem qv_lt (v : Nat) (hv : v < 16) : qv v < 4 := by revert v; decide +kernel

theorem mulVec_lt {A : List Nat} (hA : A ∈ A0) (v : Nat) (hv : v < 16) : mulVec A v < 16 := by
  revert A v; decide +kernel

theorem A0_complete : ∀ c₀ ∈ zero0, ∀ c₁ ∈ zero0, (c₀ ^^^ c₁) ∈ zero0 → ∀ c₂ ∈ zero0, ∀ c₃ ∈ zero0,
    (c₂ ^^^ c₃) ∈ zero0 → okQ [c₀, c₁, c₂, c₃] = true → okInj [c₀, c₁, c₂, c₃] = true →
      [c₀, c₁, c₂, c₃] ∈ A0 := by
  decide +kernel

theorem A0_pow6 : ∀ A ∈ A0, ∀ v, v < 16 → iter6 (mulVec A) v = v := by decide +kernel

set_option synthInstance.maxSize 1024 in
theorem rank2 : ∀ A₁ ∈ invs, A₁ ≠ idM → ∀ A₂ ∈ invs, A₂ ≠ idM → A₂ ≠ A₁ →
    mul A₁ A₂ = mul A₂ A₁ → ∀ A₃ ∈ invs, mul A₁ A₃ = mul A₃ A₁ → mul A₂ A₃ = mul A₃ A₂ →
      A₃ = idM ∨ A₃ = A₁ ∨ A₃ = A₂ ∨ A₃ = mul A₁ A₂ := by
  decide +kernel

theorem one_mem_subs : 1 ∈ subs := by decide +kernel

theorem join_mem_subs : ∀ m ∈ subs, ∀ v, v < 16 → joinMask m v ∈ subs := by decide +kernel

theorem join_spec : ∀ m ∈ subs, ∀ v, v < 16 → ∀ w, w < 16 →
    (joinMask m v).testBit w = (m.testBit w || m.testBit (w ^^^ v)) := by
  decide +kernel

theorem subs_closed : ∀ m ∈ subs, m.testBit 0 = true ∧ ∀ v, v < 16 → ∀ w, w < 16 →
    m.testBit v = true → m.testBit w = true → m.testBit (v ^^^ w) = true := by
  decide +kernel

theorem main_bound : ∀ m ∈ subs, ∀ A₁ ∈ invs, invariantB A₁ m = true → ∀ A₂ ∈ invs,
    invariantB A₂ m = true → mul A₁ A₂ = mul A₂ A₁ → boundB A₁ A₂ m = true := by
  decide +kernel

end CFSG.CGT.PushingUpLit.A78.LQ4Fin
