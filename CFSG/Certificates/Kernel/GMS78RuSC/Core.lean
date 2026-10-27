module

public import CFSG.Certificates.Kernel.GMS78RuSC.Basic
public import CFSG.Certificates.Kernel.GMS78RuSC.Idx
public import CFSG.Certificates.Kernel.GMS78RuSC.Zx
import CFSG.Certificates.Kernel.GMS78RuP.Basic

public section

namespace CFSG.KC.GMS.SC

open CFSG.KLie.CT CFSG.KC.Loop

theorem getD_map_lt {F : Nat → Nat} {C : List Nat} {j : Nat} (hj : j < C.length) (d d' : Nat) :
    (C.map F).getD j d = F (C.getD j d') := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hj]
  rfl

theorem beq_pred {A B : Nat} (hA : 1 ≤ A) (hB : 1 ≤ B) : Nat.beq (A - 1) (B - 1) = Nat.beq A B := by
  rw [Bool.eq_iff_iff]
  simp only [Nat.beq_eq]
  omega

theorem sCols_eq (R : List Nat) :
    sCols R = (List.range' 0 256).map (fun i => pk 9 (R.map (fun r => fget r i 9))) := by
  unfold sCols
  generalize List.range' 0 256 = L
  induction L with
  | nil => rfl
  | cons i L ih =>
    dsimp only
    rw [ih, listRec_map (fun r => fget r i 9) R, czPack9_eq, List.map_cons]

theorem rowsR_eq (m : Nat → Nat → Nat) (IDX : Nat) (C : List Nat) :
    rowsR m IDX C = C.map (fun p => pk 8 (C.map (fun q => fget IDX (m p q) 9 - 1))) := by
  have e1 : ∀ p, List.rec (motive := fun _ => List Nat) []
      (fun q _ ih2 => List.cons (Nat.sub (fget IDX (m p q) 9) 1) ih2) C =
        C.map (fun q => fget IDX (m p q) 9 - 1) :=
    fun p => listRec_map (fun q => fget IDX (m p q) 9 - 1) C
  have key : ∀ L : List Nat, List.rec (motive := fun _ => List Nat) []
      (fun p _ ih => List.cons (czPack8 (List.rec (motive := fun _ => List Nat) []
        (fun q _ ih2 => List.cons (Nat.sub (fget IDX (m p q) 9) 1) ih2) C)) ih) L =
      L.map (fun p => pk 8 (C.map (fun q => fget IDX (m p q) 9 - 1))) := by
    intro L
    induction L with
    | nil => rfl
    | cons p L ih =>
      dsimp only
      rw [ih, e1, czPack8_eq, List.map_cons]
  exact key C

theorem allN_congr {f g : Nat → Bool} : ∀ n : Nat, (∀ j, j < n → f j = g j) → allN n f = allN n g
  | 0, _ => rfl
  | n + 1, h => by
    change andB (f n) (allN n f) = andB (g n) (allN n g)
    rw [h n (Nat.lt_succ_self n), allN_congr n (fun j hj => h j (Nat.lt_succ_of_lt hj))]

theorem sum_shl (L : List Nat) (f g : Nat → Nat) :
    (L.map (fun i => f i + g i <<< 9)).sum = (L.map f).sum + (L.map g).sum <<< 9 := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.map_cons, List.sum_cons,
      List.sum_cons, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    omega

@[expose] noncomputable def rowF (m : Nat → Nat → Nat) (IDX : Nat) (C : List Nat) (p : Nat) : Nat :=
  pk 9 (C.map (fun q => fget IDX (m p q) 9))

theorem zx_core (m : Nat → Nat → Nat) (C : List Nat) (hnd : C.Nodup) (hlen : C.length = 256)
    (u z : Nat)
    (h : andB (neAllL (fun r => allN (nat_lit 256) fun j => notB (Nat.beq (fget r j 9) 0))
        (C.map (rowF m (sIdx C) C)))
      (Nat.beq (Nat.add (sZxT (C.map (rowF m (sIdx C) C)) (sCols (C.map (rowF m (sIdx C) C)))
          (neGet 0 (C.map (rowF m (sIdx C) C)) (Nat.sub (fget (sIdx C) u 9) 1)))
        (Nat.shiftLeft (sZxT (C.map (rowF m (sIdx C) C)) (sCols (C.map (rowF m (sIdx C) C)))
          (neGet 0 (C.map (rowF m (sIdx C) C)) (Nat.sub (fget (sIdx C) 256 9) 1))) 9)) z) = true) :
    sClosed m C = true ∧ sZx m C u = z := by
  have hle : ∀ x, fget (sIdx C) x 9 ≤ 256 := sIdx_le hnd hlen
  obtain ⟨IDX, hIDX⟩ : ∃ IDX, IDX = sIdx C := ⟨_, rfl⟩
  rw [← hIDX] at h hle
  have hmem : ∀ i, i < 256 → C.getD i 0 ∈ C := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  have hRlen : (C.map (rowF m IDX C)).length = 256 := by simpa using hlen
  rw [P117.andB_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hRget : ∀ i, i < 256 → (C.map (rowF m IDX C)).getD i 0 =
      pk 9 (C.map (fun q => fget IDX (m (C.getD i 0) q) 9)) := fun i hi =>
    getD_map_lt (by omega) 0 0
  have hent9 : ∀ p : Nat, ∀ x ∈ C.map (fun q => fget IDX (m p q) 9), x < 2 ^ 9 := by
    intro p x hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.1 hx
    have := hle (m p q)
    omega
  have hRfield : ∀ i j, i < 256 → j < 256 → fget ((C.map (rowF m IDX C)).getD i 0) j 9 =
      fget IDX (m (C.getD i 0) (C.getD j 0)) 9 := by
    intro i j hi hj
    rw [hRget i hi, pk_fget (hent9 _) j, getD_map_lt (by omega) 0 0]
  have nz : ∀ i j, i < 256 → j < 256 → fget IDX (m (C.getD i 0) (C.getD j 0)) 9 ≠ 0 := by
    intro i j hi hj
    rw [P117.neAllL_eq, List.all_eq_true] at h1
    have hmemR : (C.map (rowF m IDX C)).getD i 0 ∈ C.map (rowF m IDX C) := by
      rw [getD_map_lt (by omega) 0 0]
      exact List.mem_map.2 ⟨_, hmem i hi, rfl⟩
    have := (allN_iff _ 256).1 (h1 _ hmemR) j hj
    rw [P117.notB_eq, hRfield i j hi hj] at this
    intro hz
    rw [hz] at this
    simp at this
  have nz' : ∀ p ∈ C, ∀ q ∈ C, fget IDX (m p q) 9 ≠ 0 := by
    intro p hp q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
    have := nz i j (by omega) (by omega)
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj] at this
  have hclosed : sClosed m C = true := by
    unfold sClosed
    rw [neStrictB_eq, ← hIDX]
    beta_reduce
    rw [P117.neAllL_eq, List.all_eq_true]
    intro p hp
    rw [P117.neAllL_eq, List.all_eq_true]
    intro q hq
    rw [P117.notB_eq]
    have := nz' p hp q hq
    cases hb : Nat.beq (fget IDX (m p q) 9) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) this
  refine ⟨hclosed, ?_⟩
  have hrows : rowsR m IDX C =
      C.map (fun p => pk 8 (C.map (fun q => fget IDX (m p q) 9 - 1))) := rowsR_eq m IDX C
  have hrowsget : ∀ i, i < 256 → (rowsR m IDX C).getD i 0 =
      pk 8 (C.map (fun q => fget IDX (m (C.getD i 0) q) 9 - 1)) := by
    intro i hi
    rw [hrows]
    exact getD_map_lt (by omega) 0 0
  have hent8 : ∀ p : Nat, ∀ x ∈ C.map (fun q => fget IDX (m p q) 9 - 1), x < 2 ^ 8 := by
    intro p x hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.1 hx
    have := hle (m p q)
    omega
  have hrowsfield : ∀ i j, i < 256 → j < 256 → fget ((rowsR m IDX C).getD i 0) j 8 =
      fget IDX (m (C.getD i 0) (C.getD j 0)) 9 - 1 := by
    intro i j hi hj
    rw [hrowsget i hi, pk_fget (hent8 _) j, getD_map_lt (by omega) 0 0]
  have hrg : ∀ i, i < 256 → (List.range' 0 256).getD i 0 = i := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_range' hi]
    simp
  have hTget : ∀ i, i < 256 → (sCols (C.map (rowF m IDX C))).getD i 0 =
      pk 9 ((C.map (rowF m IDX C)).map (fun r => fget r i 9)) := by
    intro i hi
    rw [sCols_eq, getD_map_lt (by simp; omega) 0 0, hrg i hi]
  have hTfield : ∀ i j, i < 256 → j < 256 → fget ((sCols (C.map (rowF m IDX C))).getD i 0) j 9 =
      fget IDX (m (C.getD j 0) (C.getD i 0)) 9 := by
    intro i j hi hj
    have hent : ∀ x ∈ (C.map (rowF m IDX C)).map (fun r => fget r i 9), x < 2 ^ 9 := by
      intro x hx
      obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx
      exact fget_lt r i 9
    rw [hTget i hi, pk_fget hent j, getD_map_lt (by omega) 0 0, hRfield j i hj hi]
  have hterm : ∀ ι i, ι < 256 → i < 256 → cnt8 (rowsR m IDX C) i ι =
      cntT (C.map (rowF m IDX C)) (sCols (C.map (rowF m IDX C)))
        (neGet 0 (C.map (rowF m IDX C)) ι) i := by
    intro ι i hι hi
    unfold cnt8 cntT
    refine congrArg (Bool.rec (motive := fun _ => Nat) 0 1) (allN_congr 256 ?_)
    intro j hj
    beta_reduce
    simp only [neGet_eq, Nat.sub_eq]
    have hA := nz i j hi hj
    have hB := nz j i hj hi
    have hBle := hle (m (C.getD j 0) (C.getD i 0))
    have hX := nz ι (fget IDX (m (C.getD j 0) (C.getD i 0)) 9 - 1) hι (by omega)
    rw [hrowsfield i j hi hj, hrowsfield j i hj hi, hRfield i j hi hj, hTfield i j hi hj,
      hrowsfield ι _ hι (by omega), hRfield ι _ hι (by omega),
      beq_pred (Nat.one_le_iff_ne_zero.2 hA) (Nat.one_le_iff_ne_zero.2 hB),
      beq_pred (Nat.one_le_iff_ne_zero.2 hA) (Nat.one_le_iff_ne_zero.2 hX)]
  have hι1 : Nat.sub (fget IDX u 9) 1 < 256 := by
    have := hle u
    simp only [Nat.sub_eq]
    omega
  have hι2 : Nat.sub (fget IDX 256 9) 1 < 256 := by
    have := hle 256
    simp only [Nat.sub_eq]
    omega
  have h2' := Nat.eq_of_beq_eq_true h2
  rw [sZxT_eq, sZxT_eq] at h2'
  rw [sZx_def, ← hIDX, zxLoop_eq, ← h2']
  have e1 : ∀ ι, ι < 256 → ((List.range 256).map (fun i => cnt8 (rowsR m IDX C) i ι)).sum =
      ((List.range 256).map (cntT (C.map (rowF m IDX C)) (sCols (C.map (rowF m IDX C)))
        (neGet 0 (C.map (rowF m IDX C)) ι))).sum := by
    intro ι hι
    exact congrArg List.sum
      (List.map_congr_left (fun i hi => hterm ι i hι (List.mem_range.1 hi)))
  rw [sum_shl (List.range 256) (fun i => cnt8 (rowsR m IDX C) i (Nat.sub (fget IDX u 9) 1))
    (fun i => cnt8 (rowsR m IDX C) i (Nat.sub (fget IDX 256 9) 1)), e1 _ hι1, e1 _ hι2]
  rfl

end CFSG.KC.GMS.SC

end
