
module

public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.HeldB.OuterArithCheckInputs
public import CFSG.Certificates.Kernel.Spor.PackWord
public import Certificates.Data.Kernel.BfsPin

public section

namespace CFSG.KC.PermTool

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore

@[expose] noncomputable def wordTabK (n w : Nat) (G : Nat → Nat) (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w) (fun j _ acc => pcomp n w (mask w) (G j) acc) wd

@[expose] noncomputable def powK (n w p e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn n w) (fun _ acc => pcomp n w (mask w) p acc) e

@[expose] noncomputable def restrictK (w w' : Nat) (L : List Nat) (p : Nat) : Nat :=
  packA w' (L.map fun x => L.idxOf (pg w (mask w) p x))

theorem comp_eq (n : Nat) (p q : Array Nat) : comp n p q = compA n p q := rfl

theorem idTab_eq (n : Nat) : idTab n = idA n := rfl

theorem canonK_wordTabK {n w : Nat} {G : Nat → Nat} (hid : canonK n w (mask w) (n * w) (pidn n w) = true) :
    ∀ wd : List Nat, (∀ j ∈ wd, canonK n w (mask w) (n * w) (G j) = true) →
      canonK n w (mask w) (n * w) (wordTabK n w G wd) = true
  | [], _ => hid
  | j :: wd, hG => canonK_pcomp (hG j List.mem_cons_self)
      (canonK_wordTabK hid wd fun i hi => hG i (List.mem_cons_of_mem j hi))

theorem wordTabS_unpack {n w : Nat} {gs : Array (Array Nat)} {G : Nat → Nat}
    (hid : canonK n w (mask w) (n * w) (pidn n w) = true) (hidA : idA n = unpack n w (pidn n w)) :
    ∀ wd : List Nat, (∀ j ∈ wd, canonK n w (mask w) (n * w) (G j) = true) →
      (∀ j ∈ wd, gs[j]! = unpack n w (G j)) → wordTabS n gs wd = unpack n w (wordTabK n w G wd)
  | [], _, _ => by
    unfold wordTabS
    rw [List.foldr_nil, idTab_eq, hidA]
    rfl
  | j :: wd, hG, h => by
    have hG' : ∀ i ∈ wd, canonK n w (mask w) (n * w) (G i) = true :=
      fun i hi => hG i (List.mem_cons_of_mem j hi)
    have ih := wordTabS_unpack hid hidA wd hG' fun i hi => h i (List.mem_cons_of_mem j hi)
    unfold wordTabS at ih ⊢
    rw [List.foldr_cons, ih, h j List.mem_cons_self, comp_eq,
      compA_unpack (hG j List.mem_cons_self) (canonK_wordTabK hid wd hG')]
    rfl

theorem canonK_powK {n w p : Nat} (hid : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hp : canonK n w (mask w) (n * w) p = true) :
    ∀ e, canonK n w (mask w) (n * w) (powK n w p e) = true
  | 0 => hid
  | e + 1 => canonK_pcomp hp (canonK_powK hid hp e)

theorem hePowA_unpack {p : Nat} {w : Nat}
    (hid : canonK 8330 w (mask w) (8330 * w) (pidn 8330 w) = true)
    (hidA : idA 8330 = unpack 8330 w (pidn 8330 w))
    (hp : canonK 8330 w (mask w) (8330 * w) p = true) :
    ∀ e, CFSG.Sporadic.HeldB.hePowA (unpack 8330 w p) e = unpack 8330 w (powK 8330 w p e)
  | 0 => by
    rw [CFSG.Sporadic.HeldB.hePowA, hidA]
    rfl
  | e + 1 => by
    rw [CFSG.Sporadic.HeldB.hePowA, hePowA_unpack hid hidA hp e,
      compA_unpack hp (canonK_powK hid hp e)]
    rfl

theorem wordK_cons {n w m idn : Nat} {S SI : Nat → Nat} (z : Int) (l : List Int) :
    wordK n w m idn S SI (z :: l) = strictN (wordK n w m idn S SI l) (fun T =>
      strictN (CFSG.KS.Mathieu.icode z) (fun c => pcomp n w m (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
        S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
        SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T)) := rfl

theorem wordK_append {n w m idn : Nat} {S SI : Nat → Nat} (w₁ w₂ : List Int) :
    wordK n w m idn S SI (w₁ ++ w₂) = wordK n w m (wordK n w m idn S SI w₂) S SI w₁ := by
  induction w₁ with
  | nil => rfl
  | cons z w₁ ih => rw [List.cons_append, wordK_cons, ih, wordK_cons]

theorem wordK_chain {n w m idn : Nat} {S SI R : Nat → Nat} {wd : List Int} {k N : Nat}
    (hN : wd.length ≤ k * N) (hR : R N = idn)
    (h : ∀ i < N, wordK n w m (R (i + 1)) S SI ((wd.drop (k * i)).take k) = R i) :
    wordK n w m idn S SI wd = R 0 := by
  have key : ∀ j ≤ N, wordK n w m idn S SI (wd.drop (k * (N - j))) = R (N - j) := by
    intro j hj
    induction j with
    | zero => rw [Nat.sub_zero, List.drop_eq_nil_of_le hN, hR]; rfl
    | succ j ih =>
      have e : N - (j + 1) + 1 = N - j := by omega
      have e2 : k * (N - (j + 1)) + k = k * (N - j) := by rw [← e, Nat.mul_succ]
      rw [← List.take_append_drop k (wd.drop (k * (N - (j + 1)))), wordK_append, List.drop_drop,
        e2, ih (by omega), ← e, h _ (by omega)]
  simpa using key N le_rfl

theorem pg_mask_eq (w p i : Nat) : pg w (mask w) p i = p / 2 ^ (w * i) % 2 ^ w := by
  have hm : mask w = 2 ^ w - 1 := by
    change 1 <<< w - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  change (p >>> (w * i)) &&& mask w = _
  rw [hm, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem packA_cons_eq {w x : Nat} (M : List Nat) (hx : x < 2 ^ w) :
    packA w (x :: M) = packA w M * 2 ^ w + x := by
  change x ||| (packA w M <<< w) = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]

theorem pg_packA {w : Nat} : ∀ {M : List Nat}, (∀ x ∈ M, x < 2 ^ w) →
    ∀ i (hi : i < M.length), pg w (mask w) (packA w M) i = M[i]
  | [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | x :: M, h, i, hi => by
    have hx := h x List.mem_cons_self
    rw [pg_mask_eq, packA_cons_eq M hx]
    rcases i with _ | i
    · rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_comm, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hx, List.getElem_cons_zero]
    · have e : 2 ^ (w * (i + 1)) = 2 ^ w * 2 ^ (w * i) := by
        rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
      rw [e, ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos w),
        Nat.div_eq_of_lt hx, Nat.zero_add, ← pg_mask_eq, List.getElem_cons_succ]
      exact pg_packA (fun y hy => h y (List.mem_cons_of_mem x hy)) i (Nat.lt_of_succ_lt_succ hi)

theorem restrictArr_unpack {n w w' : Nat} {L : List Nat} {p : Nat}
    (_hp : canonK n w (mask w) (n * w) p = true) (hL : ∀ x ∈ L, x < n)
    (hw : L.length + 1 < 2 ^ w') :
    restrictArr L (unpack n w p) = unpack L.length w' (restrictK w w' L p) := by
  have hlt : ∀ y ∈ L.map (fun x => L.idxOf (pg w (mask w) p x)), y < 2 ^ w' := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
    have := List.idxOf_le_length (a := pg w (mask w) p x) (l := L)
    omega
  apply Array.ext
  · simp [restrictArr, unpack]
  · intro i h1 h2
    have hi : i < L.length := by simpa [restrictArr] using h1
    have hx := hL L[i] (List.getElem_mem hi)
    have hu : (unpack n w p)[L[i]]! = pg w (mask w) p L[i] := by
      rw [getElem!_pos (unpack n w p) L[i] (by simpa [unpack] using hx)]
      simp [unpack]
    simp only [restrictArr, List.getElem_toArray, List.getElem_map, hu]
    have hv : (unpack L.length w' (restrictK w w' L p))[i] =
        pg w' (mask w') (restrictK w w' L p) i := by
      simp [unpack]
    rw [hv, restrictK, pg_packA hlt i (by simpa using hi), List.getElem_map]

end CFSG.KC.PermTool

end
