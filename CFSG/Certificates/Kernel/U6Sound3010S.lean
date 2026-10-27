
module

public import Certificates.Data.Kernel.U6.Cent
public import Certificates.Data.Kernel.U6.Trans
public import Certificates.Data.Kernel.U6.Tables
public import CFSG.Certificates.Kernel.U6Sound3142
import all CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Certificates.Kernel.U6Gen

namespace CFSG.KC.U6.Pk

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.U6.Snd CFSG.Sporadic.Schreier
open CFSG.KS (mask)
open CFSG.KC.Enum (pg pcomp)

set_option exponentiation.threshold 70000

def Rep (P : ℕ) (g : Equiv.Perm (Fin 693)) : Prop :=
  P >>> 6930 = 0 ∧ ∀ p : Fin 693, ap10 P p = (g p : ℕ)

theorem fget_pg (X i w : ℕ) : fget X i w = pg w (mask w) X i := by
  rw [fget_eq]
  change _ = (X >>> (w * i)) &&& mask w
  rw [CFSG.KS.PF.mask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.mul_comm]

theorem shr_of_lt {P : ℕ} (h : P < 2 ^ 6930) : P >>> 6930 = 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt h

theorem lt_of_shr {P : ℕ} (h : P >>> 6930 = 0) : P < 2 ^ 6930 := by
  rw [Nat.shiftRight_eq_div_pow] at h
  by_contra hc
  have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos 6930)
  omega

theorem pc_eq (P Q : ℕ) : pc P Q = pcomp 693 10 (mask 10) P Q := by
  unfold pc
  rw [strictN_eq, strictN_eq]
  rfl

theorem ap10_pc (P Q : ℕ) {p : ℕ} (hp : p < 693) : ap10 (pc P Q) p = ap10 P (ap10 Q p) := by
  simp only [ap10, fget_pg, pc_eq]
  exact CFSG.KS.PF.pg_pcomp (by norm_num) hp

theorem rep_pc {P Q : ℕ} {g h : Equiv.Perm (Fin 693)} (hP : Rep P g) (hQ : Rep Q h) :
    Rep (pc P Q) (g * h) := by
  refine ⟨?_, fun p => ?_⟩
  · rw [pc_eq]
    exact CFSG.KS.PF.pcomp_shr P Q (by norm_num) (by norm_num)
  · rw [ap10_pc _ _ p.isLt, hQ.2 p, hP.2 (h p)]
    rfl

theorem rep_ext {P Q : ℕ} {g h : Equiv.Perm (Fin 693)} (hP : Rep P g) (hQ : Rep Q h) :
    P = Q ↔ g = h := by
  constructor
  · rintro rfl
    apply Equiv.ext
    intro p
    apply Fin.ext
    rw [← hP.2 p, ← hQ.2 p]
  · rintro rfl
    apply CFSG.KS.PF.eq_of_fields (n := 693) (w := 10) (by norm_num) hP.1 hQ.1
    intro i hi
    rw [← fget_pg, ← fget_pg]
    exact (hP.2 ⟨i, hi⟩).trans (hQ.2 ⟨i, hi⟩).symm

theorem sumBelow_693 (f : ℕ → ℕ) : sumBelow 693 11 f = ∑ i ∈ Finset.range 693, f i := by
  have rec_sum : ∀ (G : ℕ → ℕ) (k : ℕ),
      Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (G l) ih2) k =
        ∑ l ∈ Finset.range k, G l := by
    intro G k
    induction k with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  have sel : ∀ (b : Bool) (x : ℕ), Bool.rec (motive := fun _ => ℕ) 0 x b = if b = true then x else 0 := by
    intro b x
    cases b <;> rfl
  have hgen : ∀ hi, sumBelow 693 hi f =
      ∑ i ∈ Finset.range (64 * hi), if i < 693 then f i else 0 := by
    intro hi
    induction hi with
    | zero =>
      rw [Nat.mul_zero, Finset.sum_range_zero]
      rfl
    | succ h ih =>
      change Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i 693))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + sumBelow 693 h f = _
      rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
        Nat.add_comm (Finset.sum (Finset.range 64) _)]
      refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
      have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
        change h <<< 6 + l = 64 * h + l
        rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
        omega
      simp only [e, sel, blt_iff]
  rw [hgen 11, show 64 * 11 = 693 + 11 from rfl, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range 11) (fun i _ => ite_eq_right (by omega)), Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.1 hi)

theorem sum_ofFnW (c : ℕ → ℕ) (hc : ∀ j, c j < 2 ^ 10) : ∀ n,
    ∑ j ∈ Finset.range n, c j * 2 ^ (10 * j) = CFSG.KC.LQT.PW.ofFnW n 10 c ∧
      ∑ j ∈ Finset.range n, c j * 2 ^ (10 * j) < 2 ^ (10 * n)
  | 0 => ⟨rfl, by simp⟩
  | n + 1 => by
    obtain ⟨e, b⟩ := sum_ofFnW c hc n
    rw [Finset.sum_range_succ]
    refine ⟨?_, ?_⟩
    · change _ = CFSG.KC.LQT.PW.ofFnW n 10 c ||| c n <<< (10 * n)
      rw [← e, Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt b, Nat.shiftLeft_eq]
      exact Nat.add_comm _ _
    · have h1 : c n * 2 ^ (10 * n) ≤ 1023 * 2 ^ (10 * n) :=
        Nat.mul_le_mul_right _ (by have := hc n; omega)
      have h2 : (2 : ℕ) ^ (10 * (n + 1)) = 1024 * 2 ^ (10 * n) := by
        rw [Nat.mul_succ, Nat.pow_add]
        norm_num
        ring
      rw [h2]
      omega

theorem rep_sum (σ : Equiv.Perm (Fin 693)) (s : ℕ → ℕ) (hs : ∀ i : Fin 693, s i = σ i) :
    Rep (sumBelow 693 11 fun i => Nat.shiftLeft i (Nat.mul 10 (s i))) σ⁻¹ := by
  let c : ℕ → ℕ := fun j => if h : j < 693 then (σ.symm ⟨j, h⟩ : ℕ) else 0
  have hc : ∀ j, c j < 2 ^ 10 := by
    intro j
    simp only [c]
    split
    · exact Nat.lt_trans (σ.symm _).isLt (by norm_num)
    · norm_num
  let f : Fin 693 → ℕ := fun i => (i : ℕ) * 2 ^ (10 * (σ i : ℕ))
  have e1 : sumBelow 693 11 (fun i => Nat.shiftLeft i (Nat.mul 10 (s i))) =
      ∑ j ∈ Finset.range 693, c j * 2 ^ (10 * j) := by
    rw [sumBelow_693, ← Fin.sum_univ_eq_sum_range (fun i => Nat.shiftLeft i (Nat.mul 10 (s i))),
      ← Fin.sum_univ_eq_sum_range (fun j => c j * 2 ^ (10 * j))]
    calc ∑ i : Fin 693, Nat.shiftLeft i (Nat.mul 10 (s i)) = ∑ i : Fin 693, f i :=
          Finset.sum_congr rfl fun i _ => by
            change (i : ℕ) <<< (10 * s i) = _
            rw [Nat.shiftLeft_eq, hs]
      _ = ∑ j : Fin 693, f (σ.symm j) := (Equiv.sum_comp σ.symm f).symm
      _ = ∑ j : Fin 693, c j * 2 ^ (10 * (j : ℕ)) := Finset.sum_congr rfl fun j _ => by
          simp only [f, c, j.isLt, dite_eq_left, Equiv.apply_symm_apply]
  obtain ⟨e2, -⟩ := sum_ofFnW c hc 693
  have hF := CFSG.KS.PF.fld_ofFnW 10 c hc 693
  rw [e1, e2]
  refine ⟨CFSG.KS.PF.shr_zero_of_fld (n := 693) (by norm_num) hF fun i hi => ite_eq_right (by omega),
    fun p => ?_⟩
  rw [ap10, fget_pg, CFSG.KS.PF.pg_of_fld hF (by rw [ite_eq_left p.isLt]; exact hc p), ite_eq_left p.isLt]
  simp only [c, p.isLt, dite_eq_left, Equiv.Perm.inv_def]

theorem rep_ID : Rep ID693 1 := by
  have h := rep_sum 1 (fun i => i) (fun _ => rfl)
  rw [inv_one] at h
  exact h

theorem rep_invP {P : ℕ} {g : Equiv.Perm (Fin 693)} (hP : Rep P g) : Rep (invP P) g⁻¹ := by
  have e : invP P = sumBelow 693 11 fun i => Nat.shiftLeft i (Nat.mul 10 (ap10 P i)) :=
    strictN_eq _ _
  rw [e]
  exact rep_sum g (fun i => ap10 P i) fun i => hP.2 i

theorem rep_letter {L : List (Equiv.Perm (Fin 693))} {LT : ℕ} (hL : LetsBind L LT) {k : ℕ}
    (hk : k < 46) : Rep (elt LT k) (L.getD k 1) :=
  ⟨shr_of_lt (fget_lt _ _ _), fun p => (hL.2 k hk p).symm⟩

theorem decZ_factor (gs : List (Equiv.Perm (Fin 693))) (c : ℕ) :
    (if 0 < decZ c then gs.getD ((decZ c).toNat - 1) 1 else (gs.getD ((-decZ c).toNat - 1) 1)⁻¹) =
      if c % 2 = 0 then gs.getD (c / 2) 1 else (gs.getD (c / 2) 1)⁻¹ := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · have hz : decZ c = ((c / 2 + 1 : ℕ) : ℤ) := by rw [decZ, ite_eq_left h]; rfl
    have hpos : 0 < decZ c := by rw [hz]; omega
    have ht : (decZ c).toNat - 1 = c / 2 := by rw [hz]; omega
    rw [ite_eq_left hpos, ht, ite_eq_left h]
  · have hz : decZ c = -((c / 2 : ℕ) : ℤ) - 1 := by
      rw [decZ, ite_eq_right (by omega), Int.negSucc_eq]
      omega
    have hneg : ¬ 0 < decZ c := by rw [hz]; omega
    have ht : (-decZ c).toNat - 1 = c / 2 := by rw [hz]; omega
    rw [ite_eq_right hneg, ht, ite_eq_right (by omega)]

theorem rep_evW {S : ℕ} {gs : List (Equiv.Perm (Fin 693))}
    (hS : ∀ j < gs.length, Rep (elt S j) (gs.getD j 1)) :
    ∀ w : List ℕ, (∀ c ∈ w, c < 2 * gs.length) → Rep (evW S w) (evalCodes gs (w.map decZ))
  | [], _ => rep_ID
  | c :: w, hw => by
    have ih := rep_evW hS w fun d hd => hw d (List.mem_cons_of_mem _ hd)
    have hj : c / 2 < gs.length := by have := hw c List.mem_cons_self; omega
    rw [List.map_cons, evalCodes, decZ_factor]
    refine rep_pc ?_ ih
    have hsh : Nat.shiftRight c 1 = c / 2 := by
      rw [show Nat.shiftRight c 1 = c >>> 1 from rfl, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have hand : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
    change Rep (Bool.rec (motive := fun _ => ℕ) (invP (elt S (Nat.shiftRight c 1)))
      (elt S (Nat.shiftRight c 1)) (Nat.beq (Nat.land c 1) 0)) _
    rw [hsh, hand]
    rcases Nat.mod_two_eq_zero_or_one c with h | h
    · rw [h, ite_eq_left rfl]
      exact hS _ hj
    · rw [h, ite_eq_right (by omega)]
      exact rep_invP (hS _ hj)

theorem evalCodes_mem (gs : List (Equiv.Perm (Fin 693))) :
    ∀ w : List ℤ, evalCodes gs w ∈ Subgroup.closure {g | g ∈ gs}
  | [] => Subgroup.one_mem _
  | z :: w => by
    have hget : ∀ j, gs.getD j 1 ∈ Subgroup.closure {g | g ∈ gs} := by
      intro j
      rw [List.getD_eq_getElem?_getD]
      cases h : gs[j]? with
      | none => exact Subgroup.one_mem _
      | some x => exact Subgroup.subset_closure (List.mem_of_getElem? h)
    rw [evalCodes]
    refine Subgroup.mul_mem _ ?_ (evalCodes_mem gs w)
    split
    · exact hget _
    · exact Subgroup.inv_mem _ (hget _)

theorem fld_evList (S : ℕ) (ws : List (List ℕ)) (hlt : ∀ w ∈ ws, evW S w < 2 ^ 6930) : ∀ i,
    CFSG.KS.PF.Fld 6930 (List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
        (fun w _ ih i => strictN (evW S w) fun P =>
          Nat.lor (Nat.shiftLeft P (Nat.mul 6930 i)) (ih (Nat.succ i))) ws i)
      (fun j => if i ≤ j then (ws.map (evW S)).getD (j - i) 0 else 0) := by
  induction ws with
  | nil =>
    intro i
    refine CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_zero 6930) fun j => ?_
    split <;> simp
  | cons w ws ih =>
    intro i
    have hw := hlt w List.mem_cons_self
    have ih' := ih (fun v hv => hlt v (List.mem_cons_of_mem _ hv)) (i + 1)
    change CFSG.KS.PF.Fld 6930 (strictN (evW S w) fun P =>
      Nat.lor (Nat.shiftLeft P (Nat.mul 6930 i)) _) _
    rw [strictN_eq]
    refine CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_or (CFSG.KS.PF.fld_shl i
      (CFSG.KS.PF.fld_one hw)) ih') fun j => ?_
    rcases Nat.lt_trichotomy j i with hj | hj | hj
    · have h1 : ¬ i ≤ j := by omega
      have h2 : ¬ i + 1 ≤ j := by omega
      simp only [h1, h2, ite_false, Nat.or_zero]
    · subst hj
      simp
    · have h1 : i ≤ j := by omega
      have h2 : i + 1 ≤ j := by omega
      have h3 : j - i ≠ 0 := by omega
      have e : j - i = (j - (i + 1)) + 1 := by omega
      simp only [h1, h2, h3, ite_true, ite_false, Nat.zero_or, List.map_cons]
      rw [e, List.getD_cons_succ]

theorem elt_evList (S : ℕ) (ws : List (List ℕ)) (hlt : ∀ w ∈ ws, evW S w < 2 ^ 6930) (j : ℕ) :
    elt (evList S ws) j = (ws.map (evW S)).getD j 0 := by
  have hF := fld_evList S ws hlt 0
  have hb : (ws.map (evW S)).getD j 0 < 2 ^ 6930 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : (ws.map (evW S))[j]? with
    | none => exact Nat.two_pow_pos _
    | some x =>
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? h)
      exact hlt w hw
  rw [elt, fget_pg]
  have := CFSG.KS.PF.pg_of_fld (i := j) hF
    (by rw [ite_eq_left (Nat.zero_le j), Nat.sub_zero]; exact hb)
  rw [ite_eq_left (Nat.zero_le j), Nat.sub_zero] at this
  exact this

theorem wordsK_spec {S P : ℕ} : ∀ (W : List (List ℕ)) (i : ℕ),
    List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun w _ ih i => CFSG.KLie.CT.andB (Nat.beq (elt P i) (evW S w)) (ih (Nat.succ i))) W i = true →
    ∀ j (hj : j < W.length), elt P (i + j) = evW S W[j]
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | w :: W, i, h, j, hj => by
    change CFSG.KLie.CT.andB (Nat.beq (elt P i) (evW S w)) _ = true at h
    rw [andB_iff, beq_iff] at h
    rcases j with _ | j
    · exact h.1
    · have := wordsK_spec W (i + 1) h.2 j (by simpa using hj)
      rw [show i + (j + 1) = i + 1 + j by omega]
      exact this

theorem subP_mem {A m : ℕ} {G : Subgroup (Equiv.Perm (Fin 693))} {as : ℕ → Equiv.Perm (Fin 693)}
    (hA : ∀ i < 9, Rep (elt A i) (as i)) (hG : ∀ i < 9, as i ∈ G) :
    ∃ g ∈ G, Rep (subP A m) g := by
  have : ∀ n ≤ 9, ∃ g ∈ G, Rep (Nat.rec (motive := fun _ => ℕ) ID693
      (fun i acc => strictN acc fun acc => Bool.rec (motive := fun _ => ℕ) acc (pc (elt A i) acc)
        (Nat.beq (fget m i 1) 1)) n) g := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨1, G.one_mem, rep_ID⟩
    | succ n ih =>
      intro hn
      obtain ⟨g, hg, hr⟩ := ih (by omega)
      change ∃ g ∈ G, Rep (strictN _ fun acc => Bool.rec (motive := fun _ => ℕ) acc
        (pc (elt A n) acc) (Nat.beq (fget m n 1) 1)) g
      rw [strictN_eq]
      cases Nat.beq (fget m n 1) 1
      · exact ⟨g, hg, hr⟩
      · exact ⟨as n * g, G.mul_mem (hG n (by omega)) hg, rep_pc (hA n (by omega)) hr⟩
  exact this 9 le_rfl

theorem rep_list {S : ℕ} {gs : List (Equiv.Perm (Fin 693))}
    (hS : ∀ j < gs.length, Rep (elt S j) (gs.getD j 1)) (ws : List (List ℕ))
    (hc : ∀ w ∈ ws, ∀ c ∈ w, c < 2 * gs.length) :
    ∀ j < ws.length, Rep (elt (evList S ws) j)
      (((ws.map (List.map decZ)).map (evalCodes gs)).getD j 1) := by
  intro j hj
  have hlt : ∀ w ∈ ws, evW S w < 2 ^ 6930 := fun w hw => lt_of_shr (rep_evW hS w (hc w hw)).1
  rw [elt_evList S ws hlt, List.getD_eq_getElem _ _ (by simpa using hj),
    List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map]
  exact rep_evW hS _ (hc _ (List.getElem_mem hj))

theorem getD_mem_closure (gs : List (Equiv.Perm (Fin 693))) (j : ℕ) :
    gs.getD j 1 ∈ Subgroup.closure {g | g ∈ gs} := by
  rw [List.getD_eq_getElem?_getD]
  cases h : gs[j]? with
  | none => exact Subgroup.one_mem _
  | some x => exact Subgroup.subset_closure (List.mem_of_getElem? h)

theorem mem_getD {gs : List (Equiv.Perm (Fin 693))} {x : Equiv.Perm (Fin 693)} (hx : x ∈ gs) :
    ∃ j < gs.length, x = gs.getD j 1 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  exact ⟨j, hj, (List.getD_eq_getElem _ _ hj).symm⟩

theorem rep_unique {P : ℕ} {g h : Equiv.Perm (Fin 693)} (hg : Rep P g) (hh : Rep P h) : g = h :=
  (rep_ext hg hh).1 rfl

theorem ap10_eq {P x : ℕ} {g : Equiv.Perm (Fin 693)} (h : Rep P g) (hx : x < 693) :
    ap10 P x = (g ⟨x, hx⟩ : ℕ) := h.2 ⟨x, hx⟩

theorem orB_iff {a b : Bool} : CFSG.KLie.CT.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [CFSG.KLie.CT.orB]

theorem rep_co2 {P : ℕ} {g : Equiv.Perm (Fin 693)} (h : Rep P g) :
    CFSG.Monster.B.Co2.Rep 693 (CFSG.KS.Raw.unpack 693 10 P) g := fun x => by
  rw [CFSG.KS.Raw.Orb.unpack_get x.2, ← fget_pg, ← h.2 x]
  rfl

theorem fld_self (w X : ℕ) : CFSG.KS.PF.Fld w X (fun i => pg w (mask w) X i) := fun i k hk => by
  rw [CFSG.KS.PF.testBit_pgM]
  simp [hk]

theorem elt_cat {A K : ℕ} (hA : A < 2 ^ 62370) (j : ℕ) :
    elt (Nat.lor A (Nat.shiftLeft K 62370)) j = if j < 9 then elt A j else elt K (j - 9) := by
  have hF := CFSG.KS.PF.fld_or (fld_self 6930 A) (CFSG.KS.PF.fld_shl 9 (fld_self 6930 K))
  have hz : ∀ i, 9 ≤ i → pg 6930 (mask 6930) A i = 0 := by
    intro i hi
    apply Nat.eq_of_testBit_eq
    intro k
    rw [CFSG.KS.PF.testBit_pgM, Nat.zero_testBit,
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Bool.and_false]
  have e : Nat.lor A (Nat.shiftLeft K 62370) = A ||| K <<< (6930 * 9) := rfl
  have hb : (pg 6930 (mask 6930) A j ||| if 9 ≤ j then pg 6930 (mask 6930) K (j - 9) else 0) <
      2 ^ 6930 := by
    refine Nat.or_lt_two_pow (CFSG.KS.PF.pg_lt _ _ _) ?_
    split
    · exact CFSG.KS.PF.pg_lt _ _ _
    · exact Nat.two_pow_pos _
  simp only [elt, fget_pg]
  rw [e, CFSG.KS.PF.pg_of_fld hF hb]
  by_cases hj : j < 9
  · rw [ite_eq_right (by omega), ite_eq_left hj, Nat.or_zero]
  · rw [ite_eq_left (by omega), ite_eq_right hj, hz j (by omega), Nat.zero_or]

theorem evList_lt {S : ℕ} {ws : List (List ℕ)} (hlt : ∀ w ∈ ws, evW S w < 2 ^ 6930) :
    evList S ws < 2 ^ (ws.length * 6930) := by
  have hF := fld_evList S ws hlt 0
  have h := CFSG.KS.PF.shr_zero_of_fld (n := ws.length) (by norm_num) hF fun i hi => by
    rw [ite_eq_left (Nat.zero_le i), Nat.sub_zero,
      List.getD_eq_default _ _ (by simpa using hi)]
  rw [Nat.shiftRight_eq_div_pow] at h
  by_contra hc
  have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos (ws.length * 6930))
  change evList S ws / _ = 0 at h
  omega

theorem rep_gens {LT : ℕ} {L : List (Equiv.Perm (Fin 693))} (hL : LetsBind L LT)
    (ws : List (List ℕ)) (hc : ∀ w ∈ ws, ∀ c ∈ w, c < 92) :
    ∀ j < ws.length,
      Rep (elt (evList LT ws) j) (((ws.map (List.map decZ)).map (u62WG L)).getD j 1) := by
  have hLet : ∀ j < L.length, Rep (elt LT j) (L.getD j 1) := fun j hj => rep_letter hL (hL.1 ▸ hj)
  have e : (ws.map (List.map decZ)).map (u62WG L) = (ws.map (List.map decZ)).map (evalCodes L) :=
    List.map_congr_left fun w _ => tab_eq _
  rw [e]
  exact rep_list hLet ws fun w hw c hc' => by rw [hL.1]; exact hc w hw c hc'

theorem evList_lt_gens {LT : ℕ} {L : List (Equiv.Perm (Fin 693))} (hL : LetsBind L LT)
    {ws : List (List ℕ)} (hc : ∀ w ∈ ws, ∀ c ∈ w, c < 92) :
    evList LT ws < 2 ^ (ws.length * 6930) := by
  have hLet : ∀ j < L.length, Rep (elt LT j) (L.getD j 1) := fun j hj => rep_letter hL (hL.1 ▸ hj)
  exact evList_lt fun w hw => lt_of_shr (rep_evW hLet w fun c hc' => by
    rw [hL.1]; exact hc w hw c hc').1

theorem rep_A {LT : ℕ} {L : List (Equiv.Perm (Fin 693))} {aw : List (List ℤ)} {aW : List (List ℕ)}
    (hL : LetsBind L LT) (haw : aw = aW.map (List.map decZ)) (h9 : aW.length = 9)
    (hc : ∀ w ∈ aW, ∀ c ∈ w, c < 92) :
    (aGensG L aw).length = 9 ∧
      (∀ i < 9, Rep (elt (evList LT aW) i) ((aGensG L aw).getD i 1)) ∧
      Rep (elt (evList LT aW) 0) (j1G L aw) ∧ Rep (evW (evList LT aW) [2, 8]) (j2G L aw) ∧
      Rep (evW (evList LT aW) [0, 2, 8]) (j3G L aw) := by
  have hlen : (aGensG L aw).length = 9 := by rw [aGensG, haw, List.length_map, List.length_map, h9]
  have hA : ∀ i < 9, Rep (elt (evList LT aW) i) ((aGensG L aw).getD i 1) := by
    intro i hi
    have := rep_gens hL aW hc i (h9 ▸ hi)
    rwa [← haw] at this
  have hS : ∀ j < (aGensG L aw).length, Rep (elt (evList LT aW) j) ((aGensG L aw).getD j 1) :=
    fun j hj => hA j (hlen ▸ hj)
  have hw : ∀ w : List ℕ, (∀ c ∈ w, c < 18) → ∀ c ∈ w, c < 2 * (aGensG L aw).length :=
    fun w h c hc => by rw [hlen]; exact h c hc
  have r1 := rep_evW hS [0] (hw _ (by decide))
  have r2 := rep_evW hS [2, 8] (hw _ (by decide))
  have r3 := rep_evW hS [0, 2, 8] (hw _ (by decide))
  have d1 : ([0] : List ℕ).map decZ = [1] := rfl
  have d2 : ([2, 8] : List ℕ).map decZ = [2, 5] := rfl
  have d3 : ([0, 2, 8] : List ℕ).map decZ = [1, 2, 5] := rfl
  rw [d1] at r1
  rw [d2] at r2
  rw [d3] at r3
  refine ⟨hlen, hA, ?_, r2, r3⟩
  have e := rep_unique r1 (rep_pc (hA 0 (by norm_num)) rep_ID)
  rw [j1G, e, mul_one]
  exact hA 0 (by norm_num)

theorem cat_rep {LT : ℕ} {L : List (Equiv.Perm (Fin 693))} {aw kw : List (List ℤ)}
    {aW kW : List (List ℕ)} (hL : LetsBind L LT) (haw : aw = aW.map (List.map decZ))
    (hkw : kw = kW.map (List.map decZ)) (h9 : aW.length = 9)
    (hc : ∀ w ∈ aW ++ kW, ∀ c ∈ w, c < 92) :
    ∀ j < (aGensG L aw ++ kGensG L kw).length,
      Rep (elt (Nat.lor (evList LT aW) (Nat.shiftLeft (evList LT kW) 62370)) j)
        ((aGensG L aw ++ kGensG L kw).getD j 1) := by
  have hcA : ∀ w ∈ aW, ∀ c ∈ w, c < 92 := fun w hw => hc w (List.mem_append_left _ hw)
  have hcK : ∀ w ∈ kW, ∀ c ∈ w, c < 92 := fun w hw => hc w (List.mem_append_right _ hw)
  obtain ⟨hlen, hA, -⟩ := rep_A hL haw h9 hcA
  have hK := rep_gens hL kW hcK
  rw [← hkw] at hK
  have hlt : evList LT aW < 2 ^ 62370 := by
    have := evList_lt_gens hL hcA
    rwa [h9] at this
  have hklen : (kGensG L kw).length = kW.length := by
    rw [kGensG, hkw, List.length_map, List.length_map]
  intro j hj
  rw [elt_cat hlt]
  rw [List.length_append, hlen, hklen] at hj
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact h)]
    exact hA j h
  · rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
    exact hK (j - 9) (by omega)

theorem bindA_spec {P w : ℕ} : ∀ (l : List ℕ) (k : ℕ) {n : ℕ},
    List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k n)
      (fun x _ ih k => CFSG.KLie.CT.andB (Nat.blt x (pw2 w)) (CFSG.KLie.CT.andB (Nat.beq x (fget P k w)) (ih (Nat.succ k))))
      l k = true → k + l.length = n ∧ ∀ i (hi : i < l.length), l[i] = fget P (k + i) w
  | [], k, n, h => ⟨by simpa using (beq_iff.1 h), fun i hi => absurd hi (by simp)⟩
  | x :: l, k, n, h => by
    change CFSG.KLie.CT.andB _ (CFSG.KLie.CT.andB _ _) = true at h
    rw [andB_iff, andB_iff, beq_iff] at h
    obtain ⟨e, hl⟩ := bindA_spec l (k + 1) h.2.2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    rcases i with _ | i
    · simpa using h.2.1
    · have := hl i (by simpa using hi)
      rw [show k + (i + 1) = k + 1 + i by omega]
      simpa using this

theorem bindA_get {P w n : ℕ} {A : Array ℕ} (h : CFSG.KC.S23.bindA P w n A = true) :
    A.size = n ∧ ∀ i < n, A[i]! = fget P i w := by
  obtain ⟨e, hl⟩ := bindA_spec A.toList 0 h
  simp only [Nat.zero_add, Array.length_toList] at e hl
  refine ⟨e, fun i hi => ?_⟩
  rw [getElem!_pos A i (by omega), ← Array.getElem_toList]
  exact hl i (by simpa using (by omega : i < A.size))

theorem list3 {α : Type} (d : α) :
    ∀ l : List α, l.length = 3 → l = [l.getD 0 d, l.getD 1 d, l.getD 2 d]
  | [_, _, _], _ => rfl

def bits (m : ℕ) : Set (Fin 693) := {p | m.testBit p}

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun e => h (beq_iff.1 e)

theorem fget_one (m p : ℕ) : fget m p 1 = if m.testBit p then 1 else 0 := by
  rw [fget_eq, Nat.mul_one, Nat.pow_one, Nat.shiftRight_eq_div_pow,
    Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ p) with h | h <;> simp [h]

theorem fget_one_eq_one {m p : ℕ} : fget m p 1 = 1 ↔ m.testBit p := by
  rw [fget_one]
  split <;> simp_all

theorem fget_one_eq_zero {m p : ℕ} : fget m p 1 = 0 ↔ m.testBit p = false := by
  rw [fget_one]
  split <;> simp_all

theorem pw2_eq (x : ℕ) : pw2 x = 2 ^ x := by
  change 1 <<< x = _
  rw [Nat.one_shiftLeft]

theorem testBit_maskL (l : List ℕ) (p : ℕ) : (maskL l).testBit p = decide (p ∈ l) := by
  induction l with
  | nil => simp [maskL]
  | cons x l ih =>
    change ((pw2 x) ||| (maskL l)).testBit p = _
    rw [Nat.testBit_or, ih, pw2_eq, Nat.testBit_two_pow]
    by_cases h : x = p
    · simp [h]
    · have h' : p ≠ x := fun e => h e.symm
      simp [h, h']

theorem maskL_lt {l : List ℕ} (hl : ∀ x ∈ l, x < 693) : maskL l < 2 ^ 693 := by
  refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
  rw [testBit_maskL]
  simp only [decide_eq_false_iff_not]
  intro h
  have := hl i h
  omega

theorem bits_maskL (l : List ℕ) : bits (maskL l) = CFSG.Certificates.finSet 693 l := by
  ext p
  simp [bits, CFSG.Certificates.finSet, testBit_maskL]

theorem bits_inj {a b : ℕ} (ha : a < 2 ^ 693) (hb : b < 2 ^ 693) (h : bits a = bits b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 693
  · have := congrArg (fun s => (⟨i, hi⟩ : Fin 693) ∈ s) h
    simp only [bits, Set.mem_ofPred_eq, eq_iff_iff] at this
    cases h1 : a.testBit i <;> cases h2 : b.testBit i <;> simp_all
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem imgSet_rec (P m : ℕ) : ∀ k q, (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p acc => strictN acc fun acc =>
      nIf(Nat.beq (fget m p (nat_lit 1)) (nat_lit 1), Nat.lor acc (pw2 (ap10 P p)), acc)) k).testBit
      q = true ↔ ∃ p < k, m.testBit p = true ∧ ap10 P p = q
  | 0, q => by simp
  | k + 1, q => by
    change (strictN _ fun acc => nIf(Nat.beq (fget m k 1) 1, Nat.lor acc (pw2 (ap10 P k)),
      acc)).testBit q = true ↔ _
    rw [strictN_eq]
    have ih := imgSet_rec P m k q
    cases hb : Nat.beq (fget m k 1) 1
    · have hk : m.testBit k = false := by
        rw [← fget_one_eq_zero]
        have := Nat.ne_of_beq_eq_false hb
        have := CFSG.KS.PF.pg_lt 1 m k
        rw [← fget_pg] at this
        omega
      change (Nat.rec (motive := fun _ => Nat) _ _ k).testBit q = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨p, hp, h⟩
        exact ⟨p, by omega, h⟩
      · rintro ⟨p, hp, h1, h2⟩
        refine ⟨p, ?_, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
        · exact hp
        · rw [hk] at h1
          exact absurd h1 (by simp)
    · have hk : m.testBit k = true := fget_one_eq_one.1 (beq_iff.1 hb)
      change ((Nat.rec (motive := fun _ => Nat) _ _ k) ||| (pw2 (ap10 P k))).testBit q = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, ih, pw2_eq, Nat.testBit_two_pow, decide_eq_true_iff]
      constructor
      · rintro (⟨p, hp, h⟩ | h)
        · exact ⟨p, by omega, h⟩
        · exact ⟨k, by omega, hk, h⟩
      · rintro ⟨p, hp, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
        · exact Or.inl ⟨p, hp, h1, h2⟩
        · exact Or.inr h2

open scoped Pointwise in
theorem imgSet_spec {P m : ℕ} {g : Equiv.Perm (Fin 693)} (hP : Rep P g) :
    imgSet P m < 2 ^ 693 ∧ bits (imgSet P m) = g • bits m := by
  have key := imgSet_rec P m (nat_lit 693)
  refine ⟨Nat.lt_pow_two_of_testBit _ fun i hi => ?_, ?_⟩
  · cases h : (imgSet P m).testBit i
    · rfl
    · obtain ⟨p, hp, -, hq⟩ := (key i).1 h
      rw [ap10_eq hP hp] at hq
      have := (g ⟨p, hp⟩).isLt
      omega
  · ext q
    simp only [bits, Set.mem_ofPred_eq, Set.mem_smul_set]
    refine (key q).trans ?_
    constructor
    · rintro ⟨p, hp, h1, h2⟩
      refine ⟨⟨p, hp⟩, h1, Fin.ext ?_⟩
      rw [← h2, ap10_eq hP hp]
      rfl
    · rintro ⟨p, h1, rfl⟩
      exact ⟨p, p.isLt, h1, ap10_eq hP p.isLt⟩

open scoped Pointwise in
theorem recSets_spec {LT FA RP n : ℕ} {L : List (Equiv.Perm (Fin 693))} (hL : LetsBind L LT)
    (hFA : FA < 2 ^ 693) (hpar : ∀ j < n, j = 0 ∨ (recPar RP j < j ∧ recLet RP j < 46)) :
    ∀ k ≤ n, ∃ F : ℕ → ℕ, CFSG.KS.PF.Fld 693 (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => strictN acc fun acc =>
        Nat.lor acc (Nat.shiftLeft
          (nIf(Nat.beq j (nat_lit 0), FA,
            imgSet (letK LT (recLet RP j)) (fget acc (recPar RP j) (nat_lit 693))))
          (Nat.mul (nat_lit 693) j))) k) F ∧ (∀ i, k ≤ i → F i = 0) ∧
      ∀ i < k, F i < 2 ^ 693 ∧ ∃ g ∈ Subgroup.closure {g | g ∈ L}, bits (F i) = g • bits FA
  | 0, _ => ⟨fun _ => 0, CFSG.KS.PF.fld_zero 693, fun _ _ => rfl, fun i hi => absurd hi (by omega)⟩
  | k + 1, hk => by
    obtain ⟨F, hF, hz, hs⟩ := recSets_spec hL hFA hpar k (by omega)
    set V := nIf(Nat.beq k (nat_lit 0), FA, imgSet (letK LT (recLet RP k))
      (fget (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => strictN acc fun acc =>
        Nat.lor acc (Nat.shiftLeft
          (nIf(Nat.beq j (nat_lit 0), FA,
            imgSet (letK LT (recLet RP j)) (fget acc (recPar RP j) (nat_lit 693))))
          (Nat.mul (nat_lit 693) j))) k) (recPar RP k) 693)) with hV
    have hVs : V < 2 ^ 693 ∧ ∃ g ∈ Subgroup.closure {g | g ∈ L}, bits V = g • bits FA := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨hFA, 1, Subgroup.one_mem _, by rw [one_smul]; rfl⟩
      · obtain ⟨hp, hl⟩ := (hpar k (by omega)).resolve_left (by omega)
        have hb : Nat.beq k 0 = false := beq_false (by omega)
        have e : V = imgSet (letK LT (recLet RP k)) (F (recPar RP k)) := by
          rw [hV, hb]
          change imgSet _ (fget _ _ 693) = _
          rw [fget_pg, CFSG.KS.PF.pg_of_fld hF (hs _ hp).1]
        obtain ⟨-, g, hg, hbits⟩ := hs _ hp
        have hr : Rep (letK LT (recLet RP k)) (L.getD (recLet RP k) 1) := rep_letter hL hl
        obtain ⟨h1, h2⟩ := imgSet_spec (m := F (recPar RP k)) hr
        refine ⟨e ▸ h1, L.getD (recLet RP k) 1 * g, Subgroup.mul_mem _ (getD_mem_closure L _) hg,
          ?_⟩
        rw [e, h2, hbits, mul_smul]
    refine ⟨fun i => F i ||| (if k ≤ i then (if i - k = 0 then V else 0) else 0), ?_, ?_, ?_⟩
    · change CFSG.KS.PF.Fld 693 (strictN _ fun acc => Nat.lor acc (Nat.shiftLeft _ (Nat.mul 693 k)))
        _
      rw [strictN_eq]
      exact CFSG.KS.PF.fld_or hF (CFSG.KS.PF.fld_shl k (CFSG.KS.PF.fld_one hVs.1))
    · intro i hi
      dsimp only
      rw [hz i (by omega), ite_eq_left (by omega), ite_eq_right (by omega), Nat.zero_or]
    · intro i hi
      dsimp only
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [ite_eq_right (by omega), Nat.or_zero]
        exact hs i hi
      · rw [hz i le_rfl, ite_eq_left le_rfl, Nat.sub_self, ite_eq_left rfl, Nat.zero_or]
        exact hVs

def subG (a : ℕ → Equiv.Perm (Fin 693)) (m : ℕ) : ℕ → Equiv.Perm (Fin 693)
  | 0 => 1
  | n + 1 => if m.testBit n then a n * subG a m n else subG a m n

theorem beq_fget1 (m i : ℕ) : Nat.beq (fget m i 1) 1 = m.testBit i := by
  rw [fget_one]
  cases m.testBit i <;> rfl

theorem beq_fget1' (m i : ℕ) : Nat.beq (fget m i (nat_lit 1)) (nat_lit 1) = m.testBit i :=
  beq_fget1 m i

theorem rec_succN (z : ℕ) (F : ℕ → ℕ → ℕ) (j : ℕ) :
    Nat.rec (motive := fun _ => ℕ) z F (j + 1) = F j (Nat.rec (motive := fun _ => ℕ) z F j) := rfl

theorem rep_subP {A : ℕ} {a : ℕ → Equiv.Perm (Fin 693)} (hA : ∀ i < 9, Rep (elt A i) (a i))
    (m : ℕ) : Rep (subP A m) (subG a m 9) := by
  have : ∀ n ≤ 9, Rep (Nat.rec (motive := fun _ => ℕ) ID693
      (fun i acc => strictN acc fun acc => Bool.rec (motive := fun _ => ℕ) acc (pc (elt A i) acc)
        (Nat.beq (fget m i 1) 1)) n) (subG a m n) := by
    intro n
    induction n with
    | zero => exact fun _ => rep_ID
    | succ n ih =>
      intro hn
      change Rep (strictN _ fun acc => Bool.rec (motive := fun _ => ℕ) acc
        (pc (elt A n) acc) (Nat.beq (fget m n 1) 1)) _
      rw [strictN_eq, beq_fget1, subG]
      cases m.testBit n
      · exact ih (by omega)
      · exact rep_pc (hA n (by omega)) (ih (by omega))
  exact this 9 le_rfl

theorem subImg_eq {A : ℕ} {a : ℕ → Equiv.Perm (Fin 693)} (hA : ∀ i < 9, Rep (elt A i) (a i))
    (m x : ℕ) (hx : x < 693) : subImg A m x = (subG a m 9 ⟨x, hx⟩ : ℕ) := by
  have : ∀ n ≤ 9, Nat.rec (motive := fun _ => ℕ) x
      (fun i y => strictN y fun y => Bool.rec (motive := fun _ => ℕ) y (ap10 (elt A i) y)
        (Nat.beq (fget m i 1) 1)) n = (subG a m n ⟨x, hx⟩ : ℕ) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      change strictN _ (fun y => Bool.rec (motive := fun _ => ℕ) y (ap10 (elt A n) y)
        (Nat.beq (fget m n 1) 1)) = _
      rw [strictN_eq, beq_fget1, subG, ih (by omega)]
      cases m.testBit n
      · rfl
      · change ap10 (elt A n) _ = _
        rw [ap10_eq (hA n (by omega)) (Fin.isLt _)]
        rfl
  exact this 9 le_rfl

theorem subG_zero_mask (a : ℕ → Equiv.Perm (Fin 693)) : ∀ n, subG a 0 n = 1
  | 0 => rfl
  | n + 1 => by rw [subG, Nat.zero_testBit, subG_zero_mask a n]; rfl

theorem subG_conj (a : ℕ → Equiv.Perm (Fin 693)) (g : Equiv.Perm (Fin 693)) (m : ℕ) :
    ∀ n, g * subG a m n * g⁻¹ = subG (fun i => g * a i * g⁻¹) m n
  | 0 => by simp [subG]
  | n + 1 => by
    rw [subG, subG, ← subG_conj a g m n]
    split
    · group
    · rfl

theorem subG_congr {a b : ℕ → Equiv.Perm (Fin 693)} (m : ℕ) :
    ∀ n, (∀ i < n, a i = b i) → subG a m n = subG b m n
  | 0, _ => rfl
  | n + 1, h => by rw [subG, subG, h n (by omega), subG_congr m n fun i hi => h i (by omega)]

theorem subG_two_pow (a : ℕ → Equiv.Perm (Fin 693)) (i : ℕ) :
    ∀ n, subG a (2 ^ i) n = if i < n then a i else 1
  | 0 => by simp [subG]
  | n + 1 => by
    rw [subG, Nat.testBit_two_pow, subG_two_pow a i n]
    rcases lt_trichotomy i n with h | rfl | h
    · simp [h, h.ne, Nat.lt_succ_of_lt h]
    · simp
    · simp [h.ne', show ¬ i < n by omega, show ¬ i < n + 1 by omega]

theorem subG_mem {H : Subgroup (Equiv.Perm (Fin 693))} {a : ℕ → Equiv.Perm (Fin 693)} (m : ℕ) :
    ∀ n, (∀ i < n, a i ∈ H) → subG a m n ∈ H
  | 0, _ => H.one_mem
  | n + 1, h => by
    rw [subG]
    split
    · exact H.mul_mem (h n (by omega)) (subG_mem m n fun i hi => h i (by omega))
    · exact subG_mem m n fun i hi => h i (by omega)

theorem mapM_lt (M k v : ℕ) : mapM M k v < 512 := by
  have : ∀ n, Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => strictN acc fun acc =>
        Bool.rec (motive := fun _ => ℕ) acc (Nat.xor acc (fget M (Nat.add (Nat.mul 9 k) i) 9))
          (Nat.beq (fget v i 1) 1)) n < 2 ^ 9 := by
    intro n
    induction n with
    | zero => exact Nat.two_pow_pos 9
    | succ n ih =>
      change strictN _ (fun acc => Bool.rec (motive := fun _ => ℕ) acc
        (Nat.xor acc (fget M (Nat.add (Nat.mul 9 k) n) 9)) (Nat.beq (fget v n 1) 1)) < _
      rw [strictN_eq]
      cases Nat.beq (fget v n 1) 1
      · exact ih
      · exact Nat.xor_lt_two_pow ih (fget_lt _ _ _)
  exact this 9

section Alg

variable {a : ℕ → Equiv.Perm (Fin 693)} (hI : ∀ i < 9, a i * a i = 1)
  (hC : ∀ i < 9, ∀ j < 9, a i * a j = a j * a i)

include hC in
theorem comm_subG {j : ℕ} (hj : j < 9) (m : ℕ) :
    ∀ n ≤ 9, a j * subG a m n = subG a m n * a j := by
  intro n
  induction n with
  | zero => intro _; simp [subG]
  | succ n ih =>
    intro hn
    rw [subG]
    split
    · rw [← mul_assoc, hC j hj n (by omega), mul_assoc, ih (by omega), mul_assoc]
    · exact ih (by omega)

include hI hC in
theorem subG_mul (x y : ℕ) : ∀ n ≤ 9, subG a x n * subG a y n = subG a (x ^^^ y) n := by
  intro n
  induction n with
  | zero => intro _; simp [subG]
  | succ n ih =>
    intro hn
    have ih := ih (by omega)
    simp only [subG, Nat.testBit_xor]
    cases hx : x.testBit n <;> cases hy : y.testBit n <;>
      simp only [Bool.false_xor, Bool.xor_false, Bool.true_xor, Bool.not_true, Bool.false_eq_true,
        ite_false, ite_true]
    · exact ih
    · rw [← mul_assoc, ← comm_subG hC (by omega) x n (by omega), mul_assoc, ih]
    · rw [mul_assoc, ih]
    · rw [mul_assoc, ← mul_assoc (subG a x n), ← comm_subG hC (by omega) x n (by omega),
        ← mul_assoc, ← mul_assoc, hI n (by omega), one_mul, ih]

include hI hC in
theorem subG_sq (x : ℕ) : subG a x 9 * subG a x 9 = 1 := by
  rw [subG_mul hI hC x x 9 le_rfl, Nat.xor_self, subG_zero_mask]

include hI hC in
theorem mapM_conj {g : Equiv.Perm (Fin 693)} {M k : ℕ}
    (hg : ∀ i < 9, g * a i * g⁻¹ = subG a (fget M (9 * k + i) 9) 9) (v : ℕ) :
    g * subG a v 9 * g⁻¹ = subG a (mapM M k v) 9 := by
  rw [subG_conj, subG_congr v 9 hg]
  have : ∀ n ≤ 9, subG (fun i => subG a (fget M (9 * k + i) 9) 9) v n =
      subG a (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => strictN acc fun acc =>
        Bool.rec (motive := fun _ => ℕ) acc (Nat.xor acc (fget M (Nat.add (Nat.mul 9 k) i) 9))
          (Nat.beq (fget v i 1) 1)) n) 9 := by
    intro n
    induction n with
    | zero => intro _; exact (subG_zero_mask a 9).symm
    | succ n ih =>
      intro hn
      change _ = subG a (strictN _ fun acc => Bool.rec (motive := fun _ => ℕ) acc
        (Nat.xor acc (fget M (Nat.add (Nat.mul 9 k) n) 9)) (Nat.beq (fget v n 1) 1)) 9
      rw [strictN_eq, beq_fget1, subG, ih (by omega)]
      cases v.testBit n
      · rfl
      · change subG a (fget M (9 * k + n) 9) 9 * _ = subG a (_ ^^^ fget M (9 * k + n) 9) 9
        rw [subG_mul hI hC _ _ 9 le_rfl, Nat.xor_comm]
  exact this 9 le_rfl

include hI hC in
theorem mem_closure_sub {gs : List (Equiv.Perm (Fin 693))} (hlen : gs.length = 9)
    (ha : ∀ i, a i = gs.getD i 1) {x : Equiv.Perm (Fin 693)} :
    x ∈ Subgroup.closure {g | g ∈ gs} ↔ ∃ m < 512, x = subG a m 9 := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, hi, rfl⟩ := mem_getD hg
      rw [hlen] at hi
      refine ⟨2 ^ i, Nat.pow_lt_pow_right (by norm_num) hi, ?_⟩
      rw [subG_two_pow, ite_eq_left hi, ha]
    | one => exact ⟨0, by norm_num, (subG_zero_mask a 9).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      exact ⟨u ^^^ v, Nat.xor_lt_two_pow (n := 9) hu hv, subG_mul hI hC u v 9 le_rfl⟩
    | inv x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact ⟨u, hu, inv_eq_of_mul_eq_one_right (subG_sq hI hC u)⟩
  · rintro ⟨m, -, rfl⟩
    exact subG_mem m 9 fun i _ => ha i ▸ getD_mem_closure gs i

include hI hC in
theorem subG_inj (h0 : ∀ m < 512, subG a m 9 = 1 → m = 0) {x y : ℕ} (hx : x < 512)
    (hy : y < 512) (h : subG a x 9 = subG a y 9) : x = y := by
  have e : subG a (x ^^^ y) 9 = 1 := by
    rw [← subG_mul hI hC x y 9 le_rfl, h, subG_sq hI hC]
  have := h0 _ (Nat.xor_lt_two_pow (n := 9) hx hy) e
  exact Nat.eq_of_testBit_eq fun i => by
    have := congrArg (fun z => Nat.testBit z i) this
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    cases h1 : x.testBit i <;> cases h2 : y.testBit i <;> simp_all

end Alg

theorem testBit_lor_pw2 (acc y z : ℕ) :
    (Nat.lor acc (pw2 y)).testBit z = (acc.testBit z || decide (y = z)) := by
  change (acc ||| pw2 y).testBit z = _
  rw [Nat.testBit_or, pw2_eq, Nat.testBit_two_pow]

theorem stepS_spec {M n : ℕ} {P : ℕ → Prop} (hP : ∀ y, P y → ∀ k < n, P (mapM M k y)) {S : ℕ}
    (hS : ∀ y, S.testBit y → y < 512 ∧ P y) :
    (∀ y, (stepS M n S).testBit y → y < 512 ∧ P y) ∧
      ∀ y, S.testBit y → (stepS M n S).testBit y := by
  have inner : ∀ x, x < 512 → P x → ∀ acc : ℕ, (∀ y, acc.testBit y → y < 512 ∧ P y) →
      ∀ F : ℕ → ℕ → ℕ, (∀ k b, F k b = Nat.lor b (pw2 (mapM M k x))) → ∀ j ≤ n,
      (∀ y, (Nat.rec (motive := fun _ => ℕ) acc F j).testBit y → y < 512 ∧ P y) ∧
        ∀ y, acc.testBit y → (Nat.rec (motive := fun _ => ℕ) acc F j).testBit y := by
    intro x hx hPx acc hacc F hF j
    induction j with
    | zero => exact fun _ => ⟨hacc, fun y hy => hy⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [rec_succN, hF]
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · rw [testBit_lor_pw2, Bool.or_eq_true, decide_eq_true_iff] at hy
        rcases hy with hy | rfl
        · exact h1 y hy
        · exact ⟨mapM_lt _ _ _, hP x hPx j (by omega)⟩
      · rw [testBit_lor_pw2, h2 y hy, Bool.true_or]
  have outer : ∀ F : ℕ → ℕ → ℕ, (∀ x b, F x b = Bool.rec (motive := fun _ => ℕ) b
      (Nat.rec (motive := fun _ => ℕ) b
        (fun k acc' => strictN acc' fun acc' => Nat.lor acc' (pw2 (mapM M k x))) n)
      (S.testBit x)) → ∀ i,
      (∀ y, (Nat.rec (motive := fun _ => ℕ) S F i).testBit y → y < 512 ∧ P y) ∧
      ∀ y, S.testBit y → (Nat.rec (motive := fun _ => ℕ) S F i).testBit y := by
    intro F hF i
    induction i with
    | zero => exact ⟨hS, fun y hy => hy⟩
    | succ i ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [rec_succN, hF]
      cases hb : S.testBit i
      · exact ⟨h1, h2⟩
      · obtain ⟨hx, hPx⟩ := hS i hb
        obtain ⟨h3, h4⟩ := inner i hx hPx _ h1
          (fun k acc' => strictN acc' fun acc' => Nat.lor acc' (pw2 (mapM M k i)))
          (fun k b => strictN_eq _ _) n le_rfl
        exact ⟨h3, fun y hy => h4 y (h2 y hy)⟩
  have := outer (fun x acc => strictN acc fun acc =>
      nIf(Nat.beq (fget S x (nat_lit 1)) (nat_lit 1),
        Nat.rec (motive := fun _ => Nat) acc
          (fun k acc' => strictN acc' fun acc' => Nat.lor acc' (pw2 (mapM M k x))) n,
        acc)) (fun x b => by rw [strictN_eq, beq_fget1']) (nat_lit 512)
  unfold stepS
  exact this

theorem closeS_spec {M n : ℕ} {P : ℕ → Prop} (hP : ∀ y, P y → ∀ k < n, P (mapM M k y)) {S : ℕ}
    (hS : ∀ y, S.testBit y → y < 512 ∧ P y) : ∀ r,
    (∀ y, (closeS M n S r).testBit y → y < 512 ∧ P y) ∧
      ∀ y, S.testBit y → (closeS M n S r).testBit y
  | 0 => ⟨hS, fun _ h => h⟩
  | r + 1 => by
    obtain ⟨h1, h2⟩ := closeS_spec hP hS r
    obtain ⟨h3, h4⟩ := stepS_spec hP h1
    have e : closeS M n S (r + 1) = stepS M n (closeS M n S r) := strictN_eq _ _
    rw [e]
    exact ⟨h3, fun y hy => h4 y (h2 y hy)⟩

theorem closedK_spec {M n S : ℕ} (h : closedK M n S = true) :
    ∀ x < 512, S.testBit x → ∀ k < n, S.testBit (mapM M k x) := by
  intro x hx hb k hk
  have := allBelow_spec h (by norm_num) x hx
  rw [orB_iff, beq_iff, fget_one_eq_zero, allN_iff] at this
  rcases this with h1 | h1
  · rw [h1] at hb
    exact absurd hb (by simp)
  · exact fget_one_eq_one.1 (beq_iff.1 (h1 k hk))

theorem sumBelow_eq (m hi : ℕ) (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  have rec_sum : ∀ (G : ℕ → ℕ) (k : ℕ),
      Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (G l) ih2) k =
        ∑ l ∈ Finset.range k, G l := by
    intro G k
    induction k with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  have sel : ∀ (b : Bool) (x : ℕ), Bool.rec (motive := fun _ => ℕ) 0 x b =
      if b = true then x else 0 := by
    intro b x
    cases b <;> rfl
  have hgen : ∀ h, sumBelow m h f =
      ∑ i ∈ Finset.range (64 * h), if i < m then f i else 0 := by
    intro h
    induction h with
    | zero =>
      rw [Nat.mul_zero, Finset.sum_range_zero]
      rfl
    | succ h ih =>
      change Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + sumBelow m h f = _
      rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
        Nat.add_comm (Finset.sum (Finset.range 64) _)]
      refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
      have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
        change h <<< 6 + l = 64 * h + l
        rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
        omega
      simp only [e, sel, blt_iff]
  rw [hgen hi, show 64 * hi = m + (64 * hi - m) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range (64 * hi - m)) (fun i _ => ite_eq_right (by omega)),
    Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.1 hi)

theorem popK_eq (S : ℕ) : popK S = ((Finset.range 512).filter fun x => S.testBit x).card := by
  rw [popK, sumBelow_eq 512 8 _ (by norm_num), Finset.card_filter]
  exact Finset.sum_congr rfl fun x _ => fget_one S x

theorem class_eq {a : ℕ → Equiv.Perm (Fin 693)} {ks : List (Equiv.Perm (Fin 693))} {M x0 : ℕ}
    (hx0 : x0 < 512)
    (hk : ∀ k < ks.length, ∀ v, ks.getD k 1 * subG a v 9 * (ks.getD k 1)⁻¹ = subG a (mapM M k v) 9)
    (hcl : closedK M ks.length (closeS M ks.length (pw2 x0) 12) = true) :
    conjClass (Subgroup.closure {g | g ∈ ks}) (subG a x0 9) =
      (fun x => subG a x 9) '' {x | x < 512 ∧ (closeS M ks.length (pw2 x0) 12).testBit x} := by
  set S := closeS M ks.length (pw2 x0) 12 with hS
  have hP : ∀ y, (∃ c ∈ Subgroup.closure {g | g ∈ ks}, subG a y 9 = c * subG a x0 9 * c⁻¹) →
      ∀ k < ks.length, ∃ c ∈ Subgroup.closure {g | g ∈ ks},
        subG a (mapM M k y) 9 = c * subG a x0 9 * c⁻¹ := by
    rintro y ⟨c, hc, e⟩ k hk'
    refine ⟨ks.getD k 1 * c, Subgroup.mul_mem _ (getD_mem_closure ks k) hc, ?_⟩
    rw [← hk k hk' y, e]
    group
  have h0 : ∀ y, (pw2 x0).testBit y → y < 512 ∧
      ∃ c ∈ Subgroup.closure {g | g ∈ ks}, subG a y 9 = c * subG a x0 9 * c⁻¹ := by
    intro y hy
    rw [pw2_eq, Nat.testBit_two_pow, decide_eq_true_iff] at hy
    subst hy
    exact ⟨hx0, 1, Subgroup.one_mem _, by group⟩
  obtain ⟨hfw, hmono⟩ := closeS_spec hP h0 12
  have hx0S : S.testBit x0 := hmono x0 (by rw [pw2_eq, Nat.testBit_two_pow_self])
  have hcl' := closedK_spec hcl
  ext z
  constructor
  · rintro ⟨c, hc, rfl⟩
    let Q : Equiv.Perm (Fin 693) → Prop := fun c => ∀ x, x < 512 → S.testBit x →
      ∃ y, (y < 512 ∧ S.testBit y) ∧ c * subG a x 9 * c⁻¹ = subG a y 9
    have Qmul : ∀ c d, Q c → Q d → Q (c * d) := by
      intro c d hc hd x hx hxS
      obtain ⟨y, ⟨hy, hyS⟩, e⟩ := hd x hx hxS
      obtain ⟨z, hz, e'⟩ := hc y hy hyS
      refine ⟨z, hz, ?_⟩
      rw [← e', ← e]
      group
    have Qgen : ∀ k < ks.length, Q (ks.getD k 1) := by
      intro k hk' x hx hxS
      exact ⟨mapM M k x, ⟨mapM_lt _ _ _, hcl' x hx hxS k hk'⟩, hk k hk' x⟩
    have Q1 : Q 1 := fun x hx hxS => ⟨x, ⟨hx, hxS⟩, by group⟩
    have Qpow : ∀ g, Q g → ∀ j : ℕ, Q (g ^ j) := by
      intro g hg j
      induction j with
      | zero => rw [pow_zero]; exact Q1
      | succ j ih => rw [pow_succ]; exact Qmul _ _ ih hg
    have Qinv : ∀ g, Q g → Q g⁻¹ := by
      intro g hg
      have e : g⁻¹ = g ^ (orderOf g - 1) := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
      rw [e]
      exact Qpow g hg _
    have hQ : Q c := by
      induction hc using Subgroup.closure_induction_left with
      | one => exact Q1
      | mul_left x hx y _ ih =>
        obtain ⟨k, hk', rfl⟩ := mem_getD hx
        exact Qmul _ _ (Qgen k hk') ih
      | inv_mul_cancel x hx y _ ih =>
        obtain ⟨k, hk', rfl⟩ := mem_getD hx
        exact Qmul _ _ (Qinv _ (Qgen k hk')) ih
    obtain ⟨y, hy, e⟩ := hQ x0 hx0 hx0S
    exact ⟨y, hy, e.symm⟩
  · rintro ⟨y, ⟨hy, hyS⟩, rfl⟩
    obtain ⟨-, c, hc, e⟩ := hfw y hyS
    exact ⟨c, hc, e⟩

def aG (L : List (Equiv.Perm (Fin 693))) (aw : List (List ℤ)) (i : ℕ) : Equiv.Perm (Fin 693) :=
  (aGensG L aw).getD i 1

theorem fixK_eq {P : ℕ} {g : Equiv.Perm (Fin 693)} (h : Rep P g) :
    fixK P = {p : Fin 693 | g p = p}.ncard := by
  have e : {p : Fin 693 | g p = p} = ↑(Finset.univ.filter fun p : Fin 693 => g p = p) := by
    ext p
    simp
  rw [e, Set.ncard_coe_finset, Finset.card_filter, fixK, strictN_eq, sumBelow_693,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [h.2 p]
  by_cases hp : g p = p
  · rw [ite_eq_left hp, hp, Nat.beq_refl]
  · rw [ite_eq_right hp, beq_false fun e => hp (Fin.ext e)]

theorem sumN_fld (w : ℕ) (f : ℕ → ℕ) : ∀ n, (∀ i < n, f i < 2 ^ w) →
    CFSG.KS.PF.Fld w (sumN n fun i => Nat.shiftLeft (f i) (Nat.mul w i))
      (fun i => if i < n then f i else 0) ∧
      sumN n (fun i => Nat.shiftLeft (f i) (Nat.mul w i)) < 2 ^ (w * n)
  | 0, _ => ⟨CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_zero w) fun i => by simp, by
      change 0 < _
      exact Nat.two_pow_pos _⟩
  | n + 1, hf => by
    obtain ⟨hF, hb⟩ := sumN_fld w f n fun i hi => hf i (by omega)
    have e : sumN (n + 1) (fun i => Nat.shiftLeft (f i) (Nat.mul w i)) =
        f n <<< (w * n) ||| sumN n (fun i => Nat.shiftLeft (f i) (Nat.mul w i)) := by
      change Nat.add (f n <<< (w * n)) _ = _
      exact Nat.shiftLeft_add_eq_or_of_lt hb _
    rw [e]
    refine ⟨CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_or (CFSG.KS.PF.fld_shl n
      (CFSG.KS.PF.fld_one (hf n (by omega)))) hF) fun i => ?_, ?_⟩
    · rcases Nat.lt_trichotomy i n with h | rfl | h
      · simp [show ¬ n ≤ i by omega, h, show i < n + 1 by omega]
      · simp
      · simp [show n ≤ i by omega, show i - n ≠ 0 by omega, show ¬ i < n by omega,
          show ¬ i < n + 1 by omega]
    · rw [← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]
      have h1 : f n * 2 ^ (w * n) ≤ (2 ^ w - 1) * 2 ^ (w * n) :=
        Nat.mul_le_mul_right _ (by have := hf n (by omega); omega)
      have h2 : (2 : ℕ) ^ (w * (n + 1)) = 2 ^ w * 2 ^ (w * n) := by
        rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
      rw [h2, Nat.sub_mul, Nat.one_mul] at *
      have : 2 ^ (w * n) ≤ 2 ^ w * 2 ^ (w * n) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos w)
      omega

theorem sumN_get {w : ℕ} {f : ℕ → ℕ} {n i : ℕ} (hf : ∀ i < n, f i < 2 ^ w) (hi : i < n) :
    fget (sumN n fun i => Nat.shiftLeft (f i) (Nat.mul w i)) i w = f i := by
  rw [fget_pg, CFSG.KS.PF.pg_of_fld (sumN_fld w f n hf).1 (by rw [ite_eq_left hi]; exact hf i hi),
    ite_eq_left hi]

theorem sum_ofFnW_w (w : ℕ) (c : ℕ → ℕ) (hc : ∀ j, c j < 2 ^ w) : ∀ n,
    ∑ j ∈ Finset.range n, c j * 2 ^ (w * j) = CFSG.KC.LQT.PW.ofFnW n w c ∧
      ∑ j ∈ Finset.range n, c j * 2 ^ (w * j) < 2 ^ (w * n)
  | 0 => ⟨rfl, by simp⟩
  | n + 1 => by
    obtain ⟨e, b⟩ := sum_ofFnW_w w c hc n
    rw [Finset.sum_range_succ]
    refine ⟨?_, ?_⟩
    · change _ = CFSG.KC.LQT.PW.ofFnW n w c ||| c n <<< (w * n)
      rw [← e, Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt b, Nat.shiftLeft_eq]
      exact Nat.add_comm _ _
    · have h1 : c n * 2 ^ (w * n) ≤ (2 ^ w - 1) * 2 ^ (w * n) :=
        Nat.mul_le_mul_right _ (by have := hc n; omega)
      have h2 : (2 : ℕ) ^ (w * (n + 1)) = 2 ^ w * 2 ^ (w * n) := by
        rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
      rw [h2]
      rw [Nat.sub_mul, Nat.one_mul] at h1
      have : 2 ^ (w * n) ≤ 2 ^ w * 2 ^ (w * n) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos w)
      omega

theorem keyA_lt {A : ℕ} {a : ℕ → Equiv.Perm (Fin 693)} (hA : ∀ i < 9, Rep (elt A i) (a i))
    (m : ℕ) : keyA A m < 2 ^ 30 := by
  have h1 := subImg_eq hA m 1 (by norm_num)
  have h3 := subImg_eq hA m 3 (by norm_num)
  have h45 := subImg_eq hA m 45 (by norm_num)
  have b1 := (subG a m 9 ⟨1, by norm_num⟩).isLt
  have b3 := (subG a m 9 ⟨3, by norm_num⟩).isLt
  have b45 := (subG a m 9 ⟨45, by norm_num⟩).isLt
  change (subImg A m 1 * 1024 + subImg A m 3) * 1024 + subImg A m 45 < 2 ^ 30
  rw [h1, h3, h45]
  norm_num
  omega

theorem AK_get {A : ℕ} {a : ℕ → Equiv.Perm (Fin 693)} (hA : ∀ i < 9, Rep (elt A i) (a i))
    {m : ℕ} (hm : m < 512) : fget (AK A) m 30 = keyA A m := by
  let c : ℕ → ℕ := fun j => if j < 512 then keyA A j else 0
  have hc : ∀ j, c j < 2 ^ 30 := fun j => by
    simp only [c]
    split
    · exact keyA_lt hA j
    · exact Nat.two_pow_pos _
  have e : AK A = CFSG.KC.LQT.PW.ofFnW 512 30 c := by
    rw [AK, sumBelow_eq 512 8 _ (by norm_num), ← (sum_ofFnW_w 30 c hc 512).1]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < 512 := Finset.mem_range.1 hj
    change keyA A j <<< (30 * j) = _
    rw [Nat.shiftLeft_eq]
    simp [c, hj']
  rw [e, fget_pg, CFSG.KS.PF.pg_of_fld (CFSG.KS.PF.fld_ofFnW 30 c hc 512)
    (by rw [ite_eq_left hm]; exact hc m), ite_eq_left hm]
  simp [c, hm]

theorem maskOf_eq {AKs k m0 : ℕ} (hm0 : m0 < 512) (hk : fget AKs m0 30 = k)
    (hu : ∀ m < 512, fget AKs m 30 = k → m = m0) : maskOf AKs k = m0 := by
  have : ∀ F : ℕ → ℕ → ℕ, (∀ i acc, F i acc =
      Bool.rec (motive := fun _ => ℕ) acc (511 - i) (Nat.beq (fget AKs (511 - i) 30) k)) →
      ∀ n ≤ 512, Nat.rec (motive := fun _ => ℕ) (nat_lit 512) F n =
        if 512 - n ≤ m0 then m0 else 512 := by
    intro F hF n
    induction n with
    | zero =>
      intro _
      rw [ite_eq_right (by omega)]
      rfl
    | succ n ih =>
      intro hn
      rw [rec_succN, hF, ih (by omega)]
      by_cases hb : fget AKs (511 - n) 30 = k
      · rw [beq_iff.2 hb]
        have := hu _ (by omega) hb
        change 511 - n = _
        rw [ite_eq_left (by omega)]
        exact this
      · rw [beq_false hb]
        change (if 512 - n ≤ m0 then m0 else 512) = _
        by_cases h1 : 512 - n ≤ m0
        · rw [ite_eq_left h1, ite_eq_left (by omega)]
        · have : m0 ≠ 511 - n := fun e => hb (e ▸ hk)
          rw [ite_eq_right h1, ite_eq_right (by omega)]
  have h := this (fun i acc => (fun m => nIf(Nat.beq (fget AKs m (nat_lit 30)) k, m, acc))
    (Nat.sub (nat_lit 511) i)) (fun i acc => rfl) (nat_lit 512) le_rfl
  have e : (if 512 - nat_lit 512 ≤ m0 then m0 else 512) = m0 :=
    ite_eq_left (by change 512 - 512 ≤ m0; omega)
  rw [e] at h
  unfold maskOf
  exact h

theorem shr_zero_of_lt' {X : ℕ} (h : X < 2 ^ 81) : X >>> (9 * 9) = 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt h

theorem eq_of_xor_eq_zero {x y : ℕ} (h : x ^^^ y = 0) : x = y := by
  calc x = x ^^^ (y ^^^ y) := by rw [Nat.xor_self, Nat.xor_zero]
    _ = (x ^^^ y) ^^^ y := (Nat.xor_assoc _ _ _).symm
    _ = y := by rw [h, Nat.zero_xor]

def keyF (x1 x3 x45 : ℕ) : ℕ :=
  Nat.add (Nat.mul (Nat.add (Nat.mul x1 (nat_lit 1024)) x3) (nat_lit 1024)) x45

theorem keyA_keyF (A m : ℕ) : keyA A m =
    keyF (subImg A m (nat_lit 1)) (subImg A m (nat_lit 3)) (subImg A m (nat_lit 45)) := rfl

theorem keyF_inj {x1 x3 x45 y1 y3 y45 : ℕ} (h1 : x3 < 1024) (h2 : x45 < 1024) (h3 : y3 < 1024)
    (h4 : y45 < 1024) (h : keyF x1 x3 x45 = keyF y1 y3 y45) : x1 = y1 ∧ x3 = y3 ∧ x45 = y45 := by
  simp only [keyF, Nat.add_eq, Nat.mul_eq] at h
  omega

def MatRep (a : ℕ → Equiv.Perm (Fin 693)) (X : ℕ) (g : Equiv.Perm (Fin 693)) : Prop :=
  X < 2 ^ 81 ∧ ∀ i < 9, fget X i 9 < 512 ∧ g * a i * g⁻¹ = subG a (fget X i 9) 9

theorem mapV_eq (X v : ℕ) : mapV X v = mapM X 0 v := rfl

theorem mapV_lt (X v : ℕ) : mapV X v < 512 := mapM_lt X 0 v

theorem mat_lt {f : ℕ → ℕ} (hf : ∀ i < 9, f i < 512) :
    sumN 9 (fun i => Nat.shiftLeft (f i) (Nat.mul 9 i)) < 2 ^ 81 :=
  (sumN_fld 9 f 9 hf).2

theorem mat_id {a : ℕ → Equiv.Perm (Fin 693)} : MatRep a mId 1 := by
  have hf : ∀ i < 9, pw2 i < 2 ^ 9 := fun i hi => by
    rw [pw2_eq]
    exact Nat.pow_lt_pow_right (by norm_num) hi
  refine ⟨mat_lt hf, fun i hi => ?_⟩
  have e : fget mId i 9 = pw2 i := sumN_get hf hi
  rw [e, pw2_eq, subG_two_pow, ite_eq_left hi, one_mul, inv_one, mul_one]
  exact ⟨Nat.pow_lt_pow_right (by norm_num) hi, rfl⟩

theorem mat_id_of_comm {a : ℕ → Equiv.Perm (Fin 693)} {g : Equiv.Perm (Fin 693)}
    (h : ∀ i < 9, g * a i = a i * g) : MatRep a mId g := by
  obtain ⟨hlt, hid⟩ := (mat_id : MatRep a mId 1)
  refine ⟨hlt, fun i hi => ⟨(hid i hi).1, ?_⟩⟩
  rw [← (hid i hi).2, h i hi]
  group

section Mat

variable {a : ℕ → Equiv.Perm (Fin 693)} (hI : ∀ i < 9, a i * a i = 1)
  (hC : ∀ i < 9, ∀ j < 9, a i * a j = a j * a i) (h0 : ∀ m < 512, subG a m 9 = 1 → m = 0)

include hI hC in
theorem mat_apply {X : ℕ} {g : Equiv.Perm (Fin 693)} (hX : MatRep a X g) (v : ℕ) :
    g * subG a v 9 * g⁻¹ = subG a (mapV X v) 9 := by
  rw [mapV_eq]
  exact mapM_conj hI hC (fun i hi => by rw [Nat.mul_zero, Nat.zero_add]; exact (hX.2 i hi).2) v

include hI hC in
theorem mat_mul {X Y : ℕ} {g h : Equiv.Perm (Fin 693)} (hX : MatRep a X g) (hY : MatRep a Y h) :
    MatRep a (mcomp X Y) (g * h) := by
  have hf : ∀ i < 9, mapV X (fget Y i 9) < 2 ^ 9 := fun i _ => mapV_lt _ _
  refine ⟨mat_lt hf, fun i hi => ?_⟩
  have e : fget (mcomp X Y) i 9 = mapV X (fget Y i 9) := sumN_get hf hi
  rw [e]
  refine ⟨mapV_lt _ _, ?_⟩
  have e2 : g * h * a i * (g * h)⁻¹ = g * (h * a i * h⁻¹) * g⁻¹ := by group
  rw [e2, (hY.2 i hi).2, mat_apply hI hC hX]

include hI hC h0 in
theorem mat_unique {X Y : ℕ} {g : Equiv.Perm (Fin 693)} (hX : MatRep a X g)
    (hY : MatRep a Y g) : X = Y := by
  apply CFSG.KS.PF.eq_of_fields (n := 9) (w := 9) (by norm_num)
    (shr_zero_of_lt' hX.1) (shr_zero_of_lt' hY.1)
  intro i hi
  rw [← fget_pg, ← fget_pg]
  exact subG_inj hI hC h0 (hX.2 i hi).1 (hY.2 i hi).1 ((hX.2 i hi).2.symm.trans (hY.2 i hi).2)

include hI hC in
theorem subG_comm (x y : ℕ) : subG a x 9 * subG a y 9 = subG a y 9 * subG a x 9 := by
  rw [subG_mul hI hC x y 9 le_rfl, subG_mul hI hC y x 9 le_rfl, Nat.xor_comm]

end Mat

theorem norm_closure {a : ℕ → Equiv.Perm (Fin 693)} {ks : List (Equiv.Perm (Fin 693))} {M : ℕ}
    (hk : ∀ k < ks.length, ∀ v, ks.getD k 1 * subG a v 9 * (ks.getD k 1)⁻¹ = subG a (mapM M k v) 9)
    {g : Equiv.Perm (Fin 693)} (hg : g ∈ Subgroup.closure {g | g ∈ ks}) :
    ∀ x < 512, ∃ y < 512, g * subG a x 9 * g⁻¹ = subG a y 9 := by
  let Q : Equiv.Perm (Fin 693) → Prop := fun c => ∀ x < 512, ∃ y < 512,
    c * subG a x 9 * c⁻¹ = subG a y 9
  have Qmul : ∀ c d, Q c → Q d → Q (c * d) := by
    intro c d hc hd x hx
    obtain ⟨y, hy, e⟩ := hd x hx
    obtain ⟨z, hz, e'⟩ := hc y hy
    refine ⟨z, hz, ?_⟩
    rw [← e', ← e]
    group
  have Qgen : ∀ k < ks.length, Q (ks.getD k 1) := fun k hk' x _ =>
    ⟨mapM M k x, mapM_lt _ _ _, hk k hk' x⟩
  have Q1 : Q 1 := fun x hx => ⟨x, hx, by group⟩
  have Qpow : ∀ g, Q g → ∀ j : ℕ, Q (g ^ j) := by
    intro g hg j
    induction j with
    | zero => rw [pow_zero]; exact Q1
    | succ j ih => rw [pow_succ]; exact Qmul _ _ ih hg
  have Qinv : ∀ g, Q g → Q g⁻¹ := by
    intro g hg
    have e : g⁻¹ = g ^ (orderOf g - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
    rw [e]
    exact Qpow g hg _
  induction hg using Subgroup.closure_induction_left with
  | one => exact Q1
  | mul_left x hx y _ ih =>
    obtain ⟨k, hk', rfl⟩ := mem_getD hx
    exact Qmul _ _ (Qgen k hk') ih
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨k, hk', rfl⟩ := mem_getD hx
    exact Qmul _ _ (Qinv _ (Qgen k hk')) ih

theorem matX_rep {A : ℕ} {a : ℕ → Equiv.Perm (Fin 693)} (hA : ∀ i < 9, Rep (elt A i) (a i))
    (hI : ∀ i < 9, a i * a i = 1) (hC : ∀ i < 9, ∀ j < 9, a i * a j = a j * a i)
    (hkey : ∀ m < 512, (subG a m 9 ⟨1, by norm_num⟩ : ℕ) = 1 →
      (subG a m 9 ⟨3, by norm_num⟩ : ℕ) = 3 → (subG a m 9 ⟨45, by norm_num⟩ : ℕ) = 45 → m = 0)
    {X XI : ℕ} {g : Equiv.Perm (Fin 693)} (hX : ∀ p : Fin 693, ap10 X p = g p)
    (hXI : ∀ p : Fin 693, ap10 XI p = g⁻¹ p)
    (hN : ∀ x < 512, ∃ y < 512, g * subG a x 9 * g⁻¹ = subG a y 9) :
    MatRep a (matX A (AK A) X XI) g := by
  let f : ℕ → ℕ := fun i => maskOf (AK A) (keyF (ap10 X (ap10 (elt A i) (ap10 XI (nat_lit 1))))
    (ap10 X (ap10 (elt A i) (ap10 XI (nat_lit 3))))
    (ap10 X (ap10 (elt A i) (ap10 XI (nat_lit 45)))))
  have e : matX A (AK A) X XI = sumN 9 fun i => Nat.shiftLeft (f i) (Nat.mul 9 i) := by
    unfold matX
    congr 1
    funext i
    exact strictN_eq _ _
  have hcol : ∀ i < 9, f i < 512 ∧ g * a i * g⁻¹ = subG a (f i) 9 := by
    intro i hi
    obtain ⟨y, hy, hgy⟩ := hN (2 ^ i)
      (show 2 ^ i < 2 ^ 9 from Nat.pow_lt_pow_right (by norm_num) hi)
    rw [subG_two_pow, ite_eq_left hi] at hgy
    have hpt : ∀ p : Fin 693, ap10 X (ap10 (elt A i) (ap10 XI p)) = (subG a y 9 p : ℕ) := by
      intro p
      rw [hXI, ap10_eq (hA i hi) (Fin.isLt _), Fin.eta, hX, ← hgy]
      rfl
    have h1 : ap10 X (ap10 (elt A i) (ap10 XI (nat_lit 1))) =
        (subG a y 9 ⟨1, by norm_num⟩ : ℕ) := hpt ⟨1, by norm_num⟩
    have h3 : ap10 X (ap10 (elt A i) (ap10 XI (nat_lit 3))) =
        (subG a y 9 ⟨3, by norm_num⟩ : ℕ) := hpt ⟨3, by norm_num⟩
    have h45 : ap10 X (ap10 (elt A i) (ap10 XI (nat_lit 45))) =
        (subG a y 9 ⟨45, by norm_num⟩ : ℕ) := hpt ⟨45, by norm_num⟩
    have hkA : ∀ m < 512, fget (AK A) m 30 = keyF (subG a m 9 ⟨1, by norm_num⟩ : ℕ)
        (subG a m 9 ⟨3, by norm_num⟩ : ℕ) (subG a m 9 ⟨45, by norm_num⟩ : ℕ) := by
      intro m hm
      rw [AK_get hA hm, keyA_keyF, subImg_eq hA m _ (by norm_num),
        subImg_eq hA m _ (by norm_num), subImg_eq hA m _ (by norm_num)]
    have hfi : f i = y := by
      refine maskOf_eq hy ?_ fun m hm hkm => ?_
      · rw [hkA y hy, h1, h3, h45]
      · rw [hkA m hm, h1, h3, h45] at hkm
        obtain ⟨k1, k3, k45⟩ := keyF_inj (Fin.isLt _ |>.trans (by norm_num))
          (Fin.isLt _ |>.trans (by norm_num)) (Fin.isLt _ |>.trans (by norm_num))
          (Fin.isLt _ |>.trans (by norm_num)) hkm
        have hxy := hkey (y ^^^ m) (Nat.xor_lt_two_pow (n := 9) hy hm)
        have hmul : ∀ p : Fin 693, (subG a m 9 p : ℕ) = subG a y 9 p →
            (subG a (y ^^^ m) 9 p : ℕ) = p := by
          intro p hp
          rw [← subG_mul hI hC y m 9 le_rfl, Equiv.Perm.mul_apply, Fin.ext hp,
            ← Equiv.Perm.mul_apply, subG_sq hI hC]
          rfl
        exact (eq_of_xor_eq_zero (hxy (hmul _ k1) (hmul _ k3) (hmul _ k45))).symm
    rw [hfi]
    exact ⟨hy, hgy⟩
  rw [e]
  have hf : ∀ i < 9, f i < 2 ^ 9 := fun i hi => (hcol i hi).1
  refine ⟨mat_lt hf, fun i hi => ?_⟩
  rw [sumN_get hf hi]
  exact hcol i hi

theorem ap10_of_co2 {P : ℕ} {g : Equiv.Perm (Fin 693)}
    (h : CFSG.Monster.B.Co2.Rep 693 (CFSG.KS.Raw.unpack 693 10 P) g) (p : Fin 693) :
    ap10 P p = g p := by
  rw [← h p, CFSG.KS.Raw.Orb.unpack_get p.2, ← fget_pg]
  rfl

def selF (c : ℕ → ℕ) (u : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if u.testBit n then c n ^^^ selF c u n else selF c u n

def Ech (B : ℕ) : Prop :=
  ∀ p < 9, fget B p 9 = 0 ∨ (fget B p 9 < 2 ^ (p + 1) ∧ (fget B p 9).testBit p)

theorem xor_lc (a b c : ℕ) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

theorem selF_add (c d : ℕ → ℕ) (u : ℕ) :
    ∀ n, selF (fun i => c i ^^^ d i) u n = selF c u n ^^^ selF d u n
  | 0 => (Nat.xor_self 0).symm
  | n + 1 => by
    simp only [selF, selF_add c d u n]
    split
    · rw [Nat.xor_assoc, Nat.xor_assoc, xor_lc (d n)]
    · rfl

theorem selF_xor (c : ℕ → ℕ) (m m' : ℕ) :
    ∀ n, selF c (m ^^^ m') n = selF c m n ^^^ selF c m' n
  | 0 => (Nat.xor_self 0).symm
  | n + 1 => by
    simp only [selF, Nat.testBit_xor, selF_xor c m m' n]
    cases m.testBit n <;> cases m'.testBit n <;>
      simp only [Bool.false_xor, Bool.xor_false, Bool.true_xor, Bool.not_true, Bool.false_eq_true,
        ite_false, ite_true]
    · exact xor_lc _ _ _
    · exact (Nat.xor_assoc _ _ _).symm
    · rw [Nat.xor_assoc, xor_lc (selF c m n), ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem selF_two_pow (c : ℕ → ℕ) (p : ℕ) : ∀ n, selF c (2 ^ p) n = if p < n then c p else 0
  | 0 => by simp [selF]
  | n + 1 => by
    rw [selF, Nat.testBit_two_pow, selF_two_pow c p n]
    rcases lt_trichotomy p n with h | rfl | h
    · simp [h, h.ne, Nat.lt_succ_of_lt h]
    · simp
    · simp [h.ne', show ¬ p < n by omega, show ¬ p < n + 1 by omega]

theorem selF_congr {c d : ℕ → ℕ} (u : ℕ) :
    ∀ n, (∀ q < n, u.testBit q → c q = d q) → selF c u n = selF d u n
  | 0, _ => rfl
  | n + 1, h => by
    rw [selF, selF, selF_congr u n fun q hq => h q (by omega)]
    split
    · rw [h n (by omega) (by assumption)]
    · rfl

theorem testBit_selF_pw2 (u : ℕ) :
    ∀ n j, (selF pw2 u n).testBit j = (decide (j < n) && u.testBit j)
  | 0, j => by simp [selF]
  | n + 1, j => by
    rw [selF]
    split
    · rename_i h
      rw [Nat.testBit_xor, testBit_selF_pw2 u n j, pw2_eq, Nat.testBit_two_pow]
      rcases lt_trichotomy j n with hj | rfl | hj
      · simp [hj, hj.ne', Nat.lt_succ_of_lt hj]
      · simp [h]
      · simp [hj.ne, show ¬ j < n by omega, show ¬ j < n + 1 by omega]
    · rename_i h
      rw [testBit_selF_pw2 u n j]
      rcases lt_trichotomy j n with hj | rfl | hj
      · simp [hj, Nat.lt_succ_of_lt hj]
      · simp [h]
      · simp [show ¬ j < n by omega, show ¬ j < n + 1 by omega]

theorem selF_pw2 {u : ℕ} (hu : u < 512) : selF pw2 u 9 = u := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_selF_pw2]
  by_cases hj : j < 9
  · simp [hj]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (n := 2) (by norm_num)
      (by omega : 9 ≤ j)))]
    simp [hj]

theorem mapV_selF (X u : ℕ) : mapV X u = selF (fun i => fget X i 9) u 9 := by
  have : ∀ F : ℕ → ℕ → ℕ, (∀ i acc, F i acc = if u.testBit i then fget X i 9 ^^^ acc else acc) →
      ∀ n, Nat.rec (motive := fun _ => ℕ) 0 F n = selF (fun i => fget X i 9) u n := by
    intro F hF n
    induction n with
    | zero => rfl
    | succ n ih => rw [rec_succN, hF, selF, ih]
  refine this (fun i acc => strictN acc fun acc => Bool.rec (motive := fun _ => ℕ) acc
    (Nat.xor acc (fget X i (nat_lit 9))) (Nat.beq (fget u i (nat_lit 1)) (nat_lit 1)))
    (fun i acc => ?_) (nat_lit 9)
  rw [strictN_eq, beq_fget1']
  cases u.testBit i
  · rfl
  · exact Nat.xor_comm _ _

theorem selF_lt {c : ℕ → ℕ} (hc : ∀ p < 9, c p < 2 ^ (p + 1)) (u : ℕ) :
    ∀ n ≤ 9, selF c u n < 2 ^ n
  | 0, _ => Nat.two_pow_pos 0
  | n + 1, hn => by
    have ih := selF_lt hc u n (by omega)
    rw [selF]
    split
    · exact Nat.xor_lt_two_pow (hc n (by omega))
        (Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by norm_num) (by omega)))
    · exact Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem ech_lt {B : ℕ} (hE : Ech B) : ∀ p < 9, fget B p 9 < 2 ^ (p + 1) := fun p hp => by
  rcases hE p hp with h | h
  · rw [h]
    exact Nat.two_pow_pos _
  · exact h.1

theorem selF_zero {B : ℕ} (hE : Ech B) (m : ℕ) : ∀ n ≤ 9,
    (∀ p < n, fget B p 9 ≠ 0 → (selF (fun p => fget B p 9) m n).testBit p = false) →
      selF (fun p => fget B p 9) m n = 0
  | 0, _, _ => rfl
  | n + 1, hn, h => by
    have hlt := selF_lt (ech_lt hE) m n (by omega)
    by_cases hb : m.testBit n
    · by_cases hs : fget B n 9 = 0
      · have e : selF (fun p => fget B p 9) m (n + 1) = selF (fun p => fget B p 9) m n := by
          rw [selF, ite_eq_left hb]
          rw [hs, Nat.zero_xor]
        rw [e]
        refine selF_zero hE m n (by omega) fun p hp hp0 => ?_
        rw [← e]
        exact h p (by omega) hp0
      · exfalso
        have := h n (by omega) hs
        rw [selF, ite_eq_left hb] at this
        change (fget B n 9 ^^^ _).testBit n = false at this
        rw [Nat.testBit_xor, Nat.testBit_lt_two_pow hlt] at this
        rcases hE n (by omega) with h0 | h0
        · exact hs h0
        · rw [h0.2] at this
          exact absurd this (by decide)
    · have e : selF (fun p => fget B p 9) m (n + 1) = selF (fun p => fget B p 9) m n := by
        rw [selF, ite_eq_right hb]
      rw [e]
      refine selF_zero hE m n (by omega) fun p hp hp0 => ?_
      rw [← e]
      exact h p (by omega) hp0

theorem red_spec {B x : ℕ} (hE : Ech B) (hx : x < 512) :
    redV B x < 512 ∧ (∃ m, redV B x = x ^^^ selF (fun p => fget B p 9) m 9) ∧
      ∀ p < 9, fget B p 9 ≠ 0 → (redV B x).testBit p = false := by
  have key : ∀ F : ℕ → ℕ → ℕ, (∀ i y, F i y = if y.testBit (8 - i) = true ∧
      fget B (8 - i) 9 ≠ 0 then y ^^^ fget B (8 - i) 9 else y) → ∀ j ≤ 9,
      Nat.rec (motive := fun _ => ℕ) x F j < 512 ∧
      (∃ m, Nat.rec (motive := fun _ => ℕ) x F j = x ^^^ selF (fun p => fget B p 9) m 9) ∧
      ∀ p < 9, 9 - j ≤ p → fget B p 9 ≠ 0 →
        (Nat.rec (motive := fun _ => ℕ) x F j).testBit p = false := by
    intro F hF j
    induction j with
    | zero =>
      intro _
      refine ⟨hx, ⟨0, ?_⟩, fun p hp hp' => absurd hp' (by omega)⟩
      rw [selF_congr 0 9 (d := fun _ => 0) (fun q _ h => by simp at h)]
      have : selF (fun _ => 0) 0 9 = 0 := by simp [selF]
      rw [this, Nat.xor_zero]
      rfl
    | succ j ih =>
      intro hj
      obtain ⟨hlt, ⟨m, hm⟩, hz⟩ := ih (by omega)
      rw [rec_succN, hF]
      set y := Nat.rec (motive := fun _ => ℕ) x F j
      have hs := ech_lt hE (8 - j) (by omega)
      split
      · rename_i h
        refine ⟨Nat.xor_lt_two_pow (n := 9) hlt (Nat.lt_of_lt_of_le hs
          (Nat.pow_le_pow_right (by norm_num) (by omega))), ⟨m ^^^ 2 ^ (8 - j), ?_⟩, ?_⟩
        · rw [hm, selF_xor, selF_two_pow, ite_eq_left (by omega), Nat.xor_assoc]
        · intro p hp hp' hp0
          rw [Nat.testBit_xor]
          rcases Nat.lt_or_eq_of_le (show 8 - j ≤ p by omega) with hpj | hpj
          · rw [hz p hp (by omega) hp0, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hs
              (Nat.pow_le_pow_right (by norm_num) (by omega)))]
            rfl
          · subst hpj
            rcases hE (8 - j) (by omega) with h0 | h0
            · exact absurd h0 h.2
            · rw [h.1, h0.2]
              rfl
      · rename_i h
        refine ⟨hlt, ⟨m, hm⟩, fun p hp hp' hp0 => ?_⟩
        rcases Nat.lt_or_eq_of_le (show 8 - j ≤ p by omega) with hpj | hpj
        · exact hz p hp (by omega) hp0
        · subst hpj
          by_contra hb
          exact h ⟨by simpa using hb, hp0⟩
  have := key (fun i y => strictN y fun y => (fun p =>
      nIf(CFSG.KLie.CT.andB (Nat.beq (fget y p (nat_lit 1)) (nat_lit 1))
          (CFSG.KLie.CT.notB (Nat.beq (fget B p (nat_lit 9)) (nat_lit 0))),
        Nat.xor y (fget B p (nat_lit 9)), y)) (Nat.sub (nat_lit 8) i)) (fun i y => by
      rw [strictN_eq]
      change Bool.rec (motive := fun _ => ℕ) y (y ^^^ fget B (8 - i) 9)
        (CFSG.KLie.CT.andB (Nat.beq (fget y (8 - i) 1) 1) (CFSG.KLie.CT.notB (Nat.beq (fget B (8 - i) 9) 0))) = _
      rw [beq_fget1]
      by_cases h1 : y.testBit (8 - i) = true
      · by_cases h2 : fget B (8 - i) 9 = 0
        · rw [h1, h2, ite_eq_right (by simp)]
          rfl
        · rw [h1, beq_false h2, ite_eq_left ⟨rfl, h2⟩]
          rfl
      · rw [Bool.not_eq_true] at h1
        rw [h1, ite_eq_right (by simp)]
        rfl) (nat_lit 9) le_rfl
  unfold redV
  exact ⟨this.1, this.2.1, fun p hp hp0 => this.2.2 p hp (Nat.zero_le p) hp0⟩

theorem red_zero {B x m0 : ℕ} (hE : Ech B) (hx : x < 512)
    (hm0 : x = selF (fun p => fget B p 9) m0 9) : redV B x = 0 := by
  obtain ⟨-, ⟨m, hm⟩, hz⟩ := red_spec hE hx
  rw [hm, hm0, ← selF_xor] at hz ⊢
  exact selF_zero hE _ 9 le_rfl fun p hp hp0 => hz p hp hp0

theorem leadV_spec {x : ℕ} (h0 : x ≠ 0) (hx : x < 512) :
    leadV x < 9 ∧ x.testBit (leadV x) ∧ x < 2 ^ (leadV x + 1) := by
  have key : ∀ F : ℕ → ℕ → ℕ, (∀ i acc, F i acc = if x.testBit i then i else acc) → ∀ n,
      (∃ i < n, x.testBit i) → Nat.rec (motive := fun _ => ℕ) 0 F n < n ∧
      x.testBit (Nat.rec (motive := fun _ => ℕ) 0 F n) ∧
      ∀ j, Nat.rec (motive := fun _ => ℕ) 0 F n < j → j < n → x.testBit j = false := by
    intro F hF n
    induction n with
    | zero => rintro ⟨i, hi, -⟩; omega
    | succ n ih =>
      intro hex
      rw [rec_succN, hF]
      cases hb : x.testBit n
      · rw [ite_eq_right (by simp)]
        obtain ⟨i, hi, hbi⟩ := hex
        have hi' : i < n := by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
          · exact h
          · rw [hb] at hbi
            exact absurd hbi (by simp)
        obtain ⟨h1, h2, h3⟩ := ih ⟨i, hi', hbi⟩
        refine ⟨by omega, h2, fun j hj hjn => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hjn with h | rfl
        · exact h3 j hj h
        · exact hb
      · rw [ite_eq_left rfl]
        exact ⟨by omega, hb, fun j hj hjn => absurd hjn (by omega)⟩
  have hex : ∃ i < 9, x.testBit i := by
    by_contra hc
    push Not at hc
    apply h0
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.zero_testBit]
    by_cases hj : j < 9
    · simpa using hc j hj
    · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (n := 2)
        (by norm_num) (by omega : 9 ≤ j)))
  obtain ⟨h1, h2, h3⟩ := key (fun i acc => nIf(Nat.beq (fget x i (nat_lit 1)) (nat_lit 1), i, acc))
    (fun i acc => by rw [beq_fget1']; cases x.testBit i <;> rfl) 9 hex
  have hl : leadV x = Nat.rec (motive := fun _ => ℕ) 0
      (fun i acc => nIf(Nat.beq (fget x i (nat_lit 1)) (nat_lit 1), i, acc)) 9 := rfl
  rw [hl]
  refine ⟨h1, h2, Nat.lt_pow_two_of_testBit _ fun j hj => ?_⟩
  by_cases hj9 : j < 9
  · exact h3 j (by omega) hj9
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (n := 2)
      (by norm_num) (by omega : 9 ≤ j)))

theorem ins_spec {B x : ℕ} (hE : Ech B) (hx : x < 512) :
    Ech (insV B x) ∧ (∀ m, ∃ m', selF (fun p => fget B p 9) m 9 =
      selF (fun p => fget (insV B x) p 9) m' 9) ∧
      ∃ m', x = selF (fun p => fget (insV B x) p 9) m' 9 := by
  obtain ⟨hlt, ⟨m, hm⟩, hz⟩ := red_spec hE hx
  have hxm : x = redV B x ^^^ selF (fun p => fget B p 9) m 9 := by
    rw [hm, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  unfold insV
  rw [strictN_eq]
  by_cases h0 : redV B x = 0
  · rw [h0]
    have e : (Bool.rec (motive := fun _ => ℕ) (Nat.lor B (Nat.shiftLeft 0 (Nat.mul 9 (leadV 0))))
        B (Nat.beq 0 0)) = B := rfl
    rw [e]
    refine ⟨hE, fun m => ⟨m, rfl⟩, m, ?_⟩
    rw [hxm, h0, Nat.zero_xor]
  · rw [beq_false h0]
    set r := redV B x with hr
    obtain ⟨hp9, hrp, hrlt⟩ := leadV_spec h0 hlt
    set p := leadV r
    have hBp : fget B p 9 = 0 := by
      by_contra hne
      rw [hz p hp9 hne] at hrp
      exact absurd hrp (by simp)
    change Ech (Nat.lor B (Nat.shiftLeft r (Nat.mul 9 p))) ∧ _
    have hF := CFSG.KS.PF.fld_or (fld_self 9 B) (CFSG.KS.PF.fld_shl p
      (CFSG.KS.PF.fld_one (w := 9) hlt))
    have hfld : ∀ q, fget (Nat.lor B (Nat.shiftLeft r (Nat.mul 9 p))) q 9 =
        if q = p then r else fget B q 9 := by
      intro q
      have e : Nat.lor B (Nat.shiftLeft r (Nat.mul 9 p)) = B ||| r <<< (9 * p) := rfl
      have hb : (pg 9 (mask 9) B q ||| if p ≤ q then (if q - p = 0 then r else 0) else 0) <
          2 ^ 9 := by
        refine Nat.or_lt_two_pow (CFSG.KS.PF.pg_lt _ _ _) ?_
        split
        · split
          · exact hlt
          · exact Nat.two_pow_pos _
        · exact Nat.two_pow_pos _
      rw [e, fget_pg, CFSG.KS.PF.pg_of_fld hF hb, ← fget_pg]
      by_cases hq : q = p
      · subst hq
        rw [hBp, ite_eq_left le_rfl, ite_eq_left (Nat.sub_self _), ite_eq_left rfl, Nat.zero_or]
      · rw [ite_eq_right hq]
        rcases Nat.lt_or_gt_of_ne hq with h | h
        · rw [ite_eq_right (by omega), Nat.or_zero]
        · rw [ite_eq_left (by omega), ite_eq_right (by omega), Nat.or_zero]
    have hsame : ∀ m', (m'.testBit p = false) →
        selF (fun q => fget B q 9) m' 9 =
          selF (fun q => fget (Nat.lor B (Nat.shiftLeft r (Nat.mul 9 p))) q 9) m' 9 := by
      intro m' hm'
      refine selF_congr m' 9 fun q _ hq => ?_
      rw [hfld, ite_eq_right]
      rintro rfl
      rw [hm'] at hq
      exact absurd hq (by simp)
    have hclear : ∀ m', selF (fun q => fget B q 9) m' 9 =
        selF (fun q => fget B q 9) (m' ^^^ (m' &&& 2 ^ p)) 9 := by
      intro m'
      have e : m' = (m' ^^^ (m' &&& 2 ^ p)) ^^^ (m' &&& 2 ^ p) := by
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      conv_lhs => rw [e]
      rw [selF_xor]
      have : selF (fun q => fget B q 9) (m' &&& 2 ^ p) 9 = 0 := by
        by_cases hb : m'.testBit p
        · have e2 : m' &&& 2 ^ p = 2 ^ p := by
            apply Nat.eq_of_testBit_eq
            intro j
            rw [Nat.testBit_and, Nat.testBit_two_pow]
            by_cases hj : p = j
            · subst hj
              simp [hb]
            · simp [hj]
          rw [e2, selF_two_pow, ite_eq_left hp9, hBp]
        · have e2 : m' &&& 2 ^ p = 0 := by
            apply Nat.eq_of_testBit_eq
            intro j
            rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
            by_cases hj : p = j
            · subst hj
              simp [hb]
            · simp [hj]
          rw [e2]
          exact selF_zero hE 0 9 le_rfl fun q _ _ => by
            rw [show (0 : ℕ) = 0 ^^^ 0 from rfl, selF_xor, Nat.xor_self, Nat.zero_testBit]
      rw [this, Nat.xor_zero]
    have hclr : ∀ m', (m' ^^^ (m' &&& 2 ^ p)).testBit p = false := by
      intro m'
      rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow]
      cases m'.testBit p <;> simp
    refine ⟨fun q hq => ?_, fun m' => ⟨m' ^^^ (m' &&& 2 ^ p), ?_⟩,
      ⟨2 ^ p ^^^ (m ^^^ (m &&& 2 ^ p)), ?_⟩⟩
    · rw [hfld]
      by_cases hqp : q = p
      · subst hqp
        rw [ite_eq_left rfl]
        exact Or.inr ⟨hrlt, hrp⟩
      · rw [ite_eq_right hqp]
        exact hE q hq
    · rw [hclear, hsame _ (hclr m')]
    · rw [selF_xor, selF_two_pow, ite_eq_left hp9, hfld, ite_eq_left rfl, ← hsame _ (hclr m),
        ← hclear, ← hxm]

theorem inImg_complete {X u : ℕ} (hu : u < 512) : inImg X (u ^^^ mapV X u) = true := by
  have hc : ∀ i < 9, fget X i 9 ^^^ pw2 i < 512 := fun i hi =>
    Nat.xor_lt_two_pow (n := 9) (fget_lt _ _ _)
      (by rw [pw2_eq]; exact Nat.pow_lt_pow_right (by norm_num) hi)
  have key : ∀ F : ℕ → ℕ → ℕ, (∀ i B, F i B = insV B (fget X i 9 ^^^ pw2 i)) → ∀ j ≤ 9,
      Ech (Nat.rec (motive := fun _ => ℕ) 0 F j) ∧ ∀ i < j, ∃ m, fget X i 9 ^^^ pw2 i =
        selF (fun p => fget (Nat.rec (motive := fun _ => ℕ) 0 F j) p 9) m 9 := by
    intro F hF j
    induction j with
    | zero =>
      intro _
      refine ⟨fun p _ => Or.inl ?_, fun i hi => absurd hi (by omega)⟩
      change fget 0 p 9 = 0
      rw [fget_pg]
      exact CFSG.KS.PF.pg_of_fld (CFSG.KS.PF.fld_zero 9) (Nat.two_pow_pos _)
    | succ j ih =>
      intro hj
      obtain ⟨hE, hs⟩ := ih (by omega)
      rw [rec_succN, hF]
      obtain ⟨hE', hold, hnew⟩ := ins_spec hE (hc j (by omega))
      refine ⟨hE', fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · obtain ⟨m, hm⟩ := hs i h
        obtain ⟨m', hm'⟩ := hold m
        exact ⟨m', hm.trans hm'⟩
      · exact hnew
  obtain ⟨hE, hs⟩ := key (fun i B => strictN B fun B => insV B (Nat.xor (fget X i 9) (pw2 i)))
    (fun i B => strictN_eq _ _) 9 le_rfl
  set B := Nat.rec (motive := fun _ => ℕ) 0
    (fun i B => strictN B fun B => insV B (Nat.xor (fget X i 9) (pw2 i))) 9
  have hspan : ∀ n ≤ 9, ∃ m, selF (fun i => fget X i 9 ^^^ pw2 i) u n =
      selF (fun p => fget B p 9) m 9 := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨0, by
        rw [show (0 : ℕ) = 0 ^^^ 0 from rfl, selF_xor, Nat.xor_self]
        exact (Nat.xor_self 0).symm⟩
    | succ n ih =>
      intro hn
      obtain ⟨m, hm⟩ := ih (by omega)
      rw [selF]
      split
      · obtain ⟨m', hm'⟩ := hs n (by omega)
        exact ⟨m' ^^^ m, by rw [hm, hm', selF_xor]⟩
      · exact ⟨m, hm⟩
  obtain ⟨m, hm⟩ := hspan 9 le_rfl
  have hv : u ^^^ mapV X u = selF (fun i => fget X i 9 ^^^ pw2 i) u 9 := by
    rw [selF_add, mapV_selF, selF_pw2 hu, Nat.xor_comm]
  unfold inImg
  rw [strictB_eq]
  exact beq_iff.2 (red_zero hE (Nat.xor_lt_two_pow (n := 9) hu (mapV_lt _ _)) (hv.trans hm))

theorem ble_iff {a b : ℕ} : Nat.ble a b = true ↔ a ≤ b := by rw [Nat.ble_eq]

theorem fget_fget81 (X k i : ℕ) (hi : i < 9) : fget (fget X k 81) i 9 = fget X (9 * k + i) 9 := by
  rw [fget_eq, fget_eq, fget_eq]
  apply Nat.eq_of_testBit_eq
  intro n
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hn : n < 9
  · have h1 : i * 9 + n < 81 := by omega
    have e : k * 81 + (i * 9 + n) = (9 * k + i) * 9 + n := by ring
    simp only [hn, h1, decide_true, Bool.true_and, e]
  · simp [hn]

theorem sumBelow_get {m hi w : ℕ} {f : ℕ → ℕ} (hm : m ≤ 64 * hi) (hf : ∀ k < m, f k < 2 ^ w)
    {i : ℕ} (hi' : i < m) :
    fget (sumBelow m hi fun k => Nat.shiftLeft (f k) (Nat.mul w k)) i w = f i := by
  let c : ℕ → ℕ := fun j => if j < m then f j else 0
  have hc : ∀ j, c j < 2 ^ w := fun j => by
    simp only [c]
    split_ifs with h
    · exact hf j h
    · exact Nat.two_pow_pos _
  have e : (sumBelow m hi fun k => Nat.shiftLeft (f k) (Nat.mul w k)) =
      CFSG.KC.LQT.PW.ofFnW m w c := by
    rw [sumBelow_eq m hi _ hm, ← (sum_ofFnW_w w c hc m).1]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < m := Finset.mem_range.1 hj
    change f j <<< (w * j) = _
    rw [Nat.shiftLeft_eq]
    simp [c, hj']
  rw [e, fget_pg, CFSG.KS.PF.pg_of_fld (CFSG.KS.PF.fld_ofFnW w c hc m)
    (by rw [ite_eq_left hi']; exact hc i), ite_eq_left hi']
  simp [c, hi']

theorem idxK_le (KY k : ℕ) : idxK KY k ≤ 64 := by
  have : ∀ n, Nat.rec (motive := fun _ => ℕ) (nat_lit 64)
      (fun i acc => (fun j => nIf(Nat.beq (fget KY j (nat_lit 20)) k, j, acc))
        (Nat.sub (nat_lit 63) i)) n ≤ 64 := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      change Bool.rec (motive := fun _ => ℕ) _ (Nat.sub 63 n)
        (Nat.beq (fget KY (Nat.sub 63 n) 20) k) ≤ 64
      cases Nat.beq (fget KY (Nat.sub 63 n) 20) k
      · exact ih
      · change 63 - n ≤ 64
        omega
  exact this 64

theorem idxK_eq {KY k j0 : ℕ} (hj0 : j0 < 64) (hk : fget KY j0 20 = k)
    (hu : ∀ j < 64, fget KY j 20 = k → j = j0) : idxK KY k = j0 := by
  have : ∀ F : ℕ → ℕ → ℕ, (∀ i acc, F i acc =
      Bool.rec (motive := fun _ => ℕ) acc (63 - i) (Nat.beq (fget KY (63 - i) 20) k)) →
      ∀ n ≤ 64, Nat.rec (motive := fun _ => ℕ) (nat_lit 64) F n =
        if 64 - n ≤ j0 then j0 else 64 := by
    intro F hF n
    induction n with
    | zero =>
      intro _
      rw [ite_eq_right (by omega)]
      rfl
    | succ n ih =>
      intro hn
      rw [rec_succN, hF, ih (by omega)]
      by_cases hb : fget KY (63 - n) 20 = k
      · rw [beq_iff.2 hb]
        have := hu _ (by omega) hb
        change 63 - n = _
        rw [ite_eq_left (by omega)]
        exact this
      · rw [beq_false hb]
        change (if 64 - n ≤ j0 then j0 else 64) = _
        by_cases h1 : 64 - n ≤ j0
        · rw [ite_eq_left h1, ite_eq_left (by omega)]
        · have : j0 ≠ 63 - n := fun e => hb (e ▸ hk)
          rw [ite_eq_right h1, ite_eq_right (by omega)]
  have h := this (fun i acc => (fun j => nIf(Nat.beq (fget KY j (nat_lit 20)) k, j, acc))
    (Nat.sub (nat_lit 63) i)) (fun i acc => rfl) (nat_lit 64) le_rfl
  have e : (if 64 - nat_lit 64 ≤ j0 then j0 else 64) = j0 :=
    ite_eq_left (by change 64 - 64 ≤ j0; omega)
  rw [e] at h
  unfold idxK
  exact h

theorem fld_mtList (M : ℕ) (ws : List (List ℕ)) (hlt : ∀ w ∈ ws, matW M w < 2 ^ 81) : ∀ i,
    CFSG.KS.PF.Fld 81 (List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
        (fun w _ ih i => strictN (matW M w) fun X =>
          Nat.lor (Nat.shiftLeft X (Nat.mul 81 i)) (ih (Nat.succ i))) ws i)
      (fun j => if i ≤ j then (ws.map (matW M)).getD (j - i) 0 else 0) := by
  induction ws with
  | nil =>
    intro i
    refine CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_zero 81) fun j => ?_
    split <;> simp
  | cons w ws ih =>
    intro i
    have hw := hlt w List.mem_cons_self
    have ih' := ih (fun v hv => hlt v (List.mem_cons_of_mem _ hv)) (i + 1)
    change CFSG.KS.PF.Fld 81 (strictN (matW M w) fun X =>
      Nat.lor (Nat.shiftLeft X (Nat.mul 81 i)) _) _
    rw [strictN_eq]
    refine CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_or (CFSG.KS.PF.fld_shl i
      (CFSG.KS.PF.fld_one hw)) ih') fun j => ?_
    rcases Nat.lt_trichotomy j i with hj | hj | hj
    · have h1 : ¬ i ≤ j := by omega
      have h2 : ¬ i + 1 ≤ j := by omega
      simp only [h1, h2, ite_false, Nat.or_zero]
    · subst hj
      simp
    · have h1 : i ≤ j := by omega
      have h2 : i + 1 ≤ j := by omega
      have h3 : j - i ≠ 0 := by omega
      have e : j - i = (j - (i + 1)) + 1 := by omega
      simp only [h1, h2, h3, ite_true, ite_false, Nat.zero_or, List.map_cons]
      rw [e, List.getD_cons_succ]

theorem mt_mtList (M : ℕ) (ws : List (List ℕ)) (hlt : ∀ w ∈ ws, matW M w < 2 ^ 81) {t : ℕ}
    (ht : t < ws.length) : mt (mtList M ws) t = matW M ws[t] := by
  have hF := fld_mtList M ws hlt 0
  have hb : (ws.map (matW M)).getD t 0 < 2 ^ 81 := by
    rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map]
    exact hlt _ (List.getElem_mem ht)
  rw [mt, fget_pg]
  have := CFSG.KS.PF.pg_of_fld (i := t) hF
    (by rw [ite_eq_left (Nat.zero_le t), Nat.sub_zero]; exact hb)
  rw [ite_eq_left (Nat.zero_le t), Nat.sub_zero, List.getD_eq_getElem _ _ (by simpa using ht),
    List.getElem_map] at this
  exact this

theorem sumN_sum (f : ℕ → ℕ) : ∀ n, sumN n f = ∑ i ∈ Finset.range n, f i
  | 0 => by
    rw [Finset.sum_range_zero]
    rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← sumN_sum f n]
    exact Nat.add_comm _ _

theorem nIf_one (b : Bool) : nIf(b, 1, 0) = if b = true then 1 else 0 := by cases b <;> rfl

theorem sumN_count (c : ℕ → Bool) (n : ℕ) :
    sumN n (fun x => nIf(c x, 1, 0)) = ((Finset.range n).filter fun x => c x = true).card := by
  rw [sumN_sum, Finset.card_filter]
  exact Finset.sum_congr rfl fun x _ => nIf_one (c x)

theorem sumBelow_count (c : ℕ → Bool) {m hi : ℕ} (hm : m ≤ 64 * hi) :
    sumBelow m hi (fun x => nIf(c x, 1, 0)) =
      ((Finset.range m).filter fun x => c x = true).card := by
  rw [sumBelow_eq m hi _ hm, Finset.card_filter]
  exact Finset.sum_congr rfl fun x _ => nIf_one (c x)

theorem card_le_enum {H : Subgroup (Equiv.Perm (Fin 693))} {P : Equiv.Perm (Fin 693) → Prop}
    {f : ℕ → Equiv.Perm (Fin 693)} {n : ℕ} (hf : ∀ x ∈ H, ∃ i < n, x = f i) {Q : ℕ → Bool}
    (hQ : ∀ i < n, f i ∈ H → P (f i) → Q i = true) :
    Nat.card {y : H // P y} ≤ ((Finset.range n).filter fun i => Q i = true).card := by
  have hsel : ∀ y : {y : H // P y}, ∃ i, i ∈ (Finset.range n).filter (fun i => Q i = true) ∧
      (y : Equiv.Perm (Fin 693)) = f i := by
    intro y
    obtain ⟨i, hi, e⟩ := hf y.1 y.1.2
    have h1 : f i ∈ H := by
      rw [← e]
      exact y.1.2
    have h2 : P (f i) := by
      rw [← e]
      exact y.2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hQ i hi h1 h2⟩, e⟩
  choose g hg using hsel
  let g' : {y : H // P y} → ((Finset.range n).filter fun i => Q i = true) :=
    fun y => ⟨g y, (hg y).1⟩
  have hinj : Function.Injective g' := by
    intro y z h
    have e : g y = g z := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    rw [(hg y).2, (hg z).2, e]
  calc Nat.card {y : H // P y} ≤ Nat.card ((Finset.range n).filter fun i => Q i = true) :=
        Nat.card_le_card_of_injective g' hinj
    _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]

theorem card_le_sumN {H : Subgroup (Equiv.Perm (Fin 693))} {P : Equiv.Perm (Fin 693) → Prop}
    {f : ℕ → Equiv.Perm (Fin 693)} {n : ℕ} (hf : ∀ x ∈ H, ∃ i < n, x = f i) {Q : ℕ → Bool}
    (hQ : ∀ i < n, f i ∈ H → P (f i) → Q i = true) :
    Nat.card {y : H // P y} ≤ sumN n (fun i => nIf(Q i, 1, 0)) := by
  rw [sumN_count]
  exact card_le_enum hf hQ

theorem card_le_sumBelow {H : Subgroup (Equiv.Perm (Fin 693))} {P : Equiv.Perm (Fin 693) → Prop}
    {f : ℕ → Equiv.Perm (Fin 693)} {n hi : ℕ} (hn : n ≤ 64 * hi) (hf : ∀ x ∈ H, ∃ i < n, x = f i)
    {Q : ℕ → Bool} (hQ : ∀ i < n, f i ∈ H → P (f i) → Q i = true) :
    Nat.card {y : H // P y} ≤ sumBelow n hi (fun i => nIf(Q i, 1, 0)) := by
  rw [sumBelow_count Q hn]
  exact card_le_enum hf hQ

theorem allBelow_of {m hi : ℕ} {f : ℕ → Bool} (h : ∀ i < m, f i = true) :
    allBelow m hi f = true := by
  refine (recAnd_iff (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      CFSG.KLie.CT.andB ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
        (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64) hi).2 fun h' _ => ?_
  refine (recAnd_iff (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
    (Nat.blt i m)) (Nat.add (Nat.shiftLeft h' 6) l)) 64).2 fun l _ => ?_
  dsimp only
  cases hb : Nat.blt (Nat.add (Nat.shiftLeft h' 6) l) m
  · rfl
  · exact h _ (blt_iff.1 hb)

theorem matW_rep {a : ℕ → Equiv.Perm (Fin 693)} (hI : ∀ i < 9, a i * a i = 1)
    (hC : ∀ i < 9, ∀ j < 9, a i * a j = a j * a i) {M : ℕ} {gs : List (Equiv.Perm (Fin 693))}
    (hM : ∀ j < gs.length, MatRep a (fget M (Nat.add 3 j) 81) (gs.getD j 1)) :
    ∀ w : List ℕ, (∀ c ∈ w, c < 2 * gs.length ∧ c % 2 = 0) →
      MatRep a (matW M w) (evalCodes gs (w.map decZ))
  | [], _ => mat_id
  | c :: w, hw => by
    have ih := matW_rep hI hC hM w fun d hd => hw d (List.mem_cons_of_mem _ hd)
    obtain ⟨hc, h0⟩ := hw c List.mem_cons_self
    rw [List.map_cons, evalCodes, decZ_factor, ite_eq_left h0]
    change MatRep a (strictN (matW M w) fun ih =>
      mcomp (fget M (Nat.add 3 (Nat.shiftRight c 1)) 81) ih) _
    rw [strictN_eq]
    have hsh : Nat.shiftRight c 1 = c / 2 := by
      change c >>> 1 = c / 2
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
    rw [hsh]
    exact mat_mul hI hC (hM _ (by omega)) ih

theorem strictS_eq (y : ℕ) (k : ℕ → BState) : strictS y k = k y := by cases y <;> rfl

def BInv (P : ℕ → Prop) (st : BState) : Prop :=
  (∀ x, st.1.testBit x = true → x < 32768 ∧ P x) ∧ (∀ x ∈ st.2.1, st.1.testBit x = true) ∧
    st.2.2 = ((Finset.range 32768).filter fun x => st.1.testBit x = true).card

theorem binv_add {P : ℕ → Prop} {R n : ℕ} {q : List ℕ} (h : BInv P (R, q, n)) {x : ℕ}
    (hx : x < 32768) (hP : P x) (hb : R.testBit x = false) :
    BInv P (Nat.lor R (pw2 x), x :: q, Nat.succ n) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun y hy => ?_, fun y hy => ?_, ?_⟩
  · change (Nat.lor R (pw2 x)).testBit y = true at hy
    rw [testBit_lor_pw2, Bool.or_eq_true, decide_eq_true_iff] at hy
    rcases hy with hy | rfl
    · exact h1 y hy
    · exact ⟨hx, hP⟩
  · change y ∈ x :: q at hy
    change (Nat.lor R (pw2 x)).testBit y = true
    rw [testBit_lor_pw2]
    rcases List.mem_cons.1 hy with rfl | hy
    · simp
    · rw [h2 y hy, Bool.true_or]
  · change Nat.succ n =
      ((Finset.range 32768).filter fun y => (Nat.lor R (pw2 x)).testBit y = true).card
    have e : ((Finset.range 32768).filter fun y => (Nat.lor R (pw2 x)).testBit y = true) =
        insert x ((Finset.range 32768).filter fun y => R.testBit y = true) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_range, testBit_lor_pw2,
        Bool.or_eq_true, decide_eq_true_iff]
      constructor
      · rintro ⟨hy, h | rfl⟩
        · exact Or.inr ⟨hy, h⟩
        · exact Or.inl rfl
      · rintro (rfl | ⟨hy, h⟩)
        · exact ⟨hx, Or.inr rfl⟩
        · exact ⟨hy, Or.inl h⟩
    have hn : x ∉ (Finset.range 32768).filter fun y => R.testBit y = true := by
      simp [hb]
    rw [e, Finset.card_insert_of_notMem hn, ← h3]

noncomputable def innerF (MU MT TG e k : ℕ) (acc : BState) : BState :=
  strictS (imgE MU MT TG k e) fun x =>
    Bool.rec (motive := fun _ => BState) (Nat.lor acc.1 (pw2 x), x :: acc.2.1, Nat.succ acc.2.2)
      acc (Nat.beq (fget acc.1 x (nat_lit 1)) (nat_lit 1))

theorem innerF_eq (MU MT TG e k : ℕ) (acc : BState) : innerF MU MT TG e k acc =
    if acc.1.testBit (imgE MU MT TG k e) = true then acc
    else (Nat.lor acc.1 (pw2 (imgE MU MT TG k e)), imgE MU MT TG k e :: acc.2.1,
      Nat.succ acc.2.2) := by
  unfold innerF
  rw [strictS_eq]
  dsimp only
  rw [beq_fget1']
  cases acc.1.testBit (imgE MU MT TG k e) <;> rfl

theorem bfsStep_cons (MU MT TG R n e : ℕ) (q : List ℕ) :
    bfsStep MU MT TG (R, e :: q, n) =
      Nat.rec (motive := fun _ => BState) (R, q, n) (innerF MU MT TG e) 13 := rfl

theorem binv_inner {MU MT TG : ℕ} {P : ℕ → Prop}
    (hstep : ∀ k < 13, ∀ e, e < 32768 → P e → imgE MU MT TG k e < 32768 ∧ P (imgE MU MT TG k e))
    {e : ℕ} {st : BState} (h : BInv P st) (he : st.1.testBit e = true) :
    ∀ j ≤ 13, BInv P (Nat.rec (motive := fun _ => BState) st (innerF MU MT TG e) j) ∧
      (Nat.rec (motive := fun _ => BState) st (innerF MU MT TG e) j).1.testBit e = true := by
  intro j
  induction j with
  | zero => exact fun _ => ⟨h, he⟩
  | succ j ih =>
    intro hj
    obtain ⟨hI, hE⟩ := ih (by omega)
    change BInv P (innerF MU MT TG e j (Nat.rec (motive := fun _ => BState) st (innerF MU MT TG e) j)) ∧
      (innerF MU MT TG e j (Nat.rec (motive := fun _ => BState) st (innerF MU MT TG e) j)).1.testBit e
        = true
    generalize Nat.rec (motive := fun _ => BState) st (innerF MU MT TG e) j = acc at hI hE ⊢
    obtain ⟨R, q, n⟩ := acc
    change R.testBit e = true at hE
    obtain ⟨hx, hP⟩ := hstep j (by omega) e (hI.1 e hE).1 (hI.1 e hE).2
    rw [innerF_eq]
    dsimp only
    split_ifs with hb
    · exact ⟨hI, hE⟩
    · refine ⟨binv_add hI hx hP (Bool.eq_false_iff.2 hb), ?_⟩
      change (Nat.lor R (pw2 _)).testBit e = true
      rw [testBit_lor_pw2, hE, Bool.true_or]

theorem binv_classE {MU MT TG : ℕ} {P : ℕ → Prop}
    (hstep : ∀ k < 13, ∀ e, e < 32768 → P e → imgE MU MT TG k e < 32768 ∧ P (imgE MU MT TG k e))
    {e0 : ℕ} (he0 : e0 < 32768) (hP0 : P e0) : BInv P (classE MU MT TG e0) := by
  have hbfs : ∀ st, BInv P st → BInv P (bfsStep MU MT TG st) := by
    rintro ⟨R, q, n⟩ h
    cases q with
    | nil => exact h
    | cons e q =>
      rw [bfsStep_cons]
      have he : R.testBit e = true := h.2.1 e List.mem_cons_self
      have h' : BInv P (R, q, n) := ⟨h.1, fun x hx => h.2.1 x (List.mem_cons_of_mem _ hx), h.2.2⟩
      exact (binv_inner hstep h' he 13 le_rfl).1
  have h0 : BInv P (pw2 e0, [e0], 1) := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩
    · change (pw2 e0).testBit x = true at hx
      rw [pw2_eq, Nat.testBit_two_pow, decide_eq_true_iff] at hx
      subst hx
      exact ⟨he0, hP0⟩
    · change x ∈ [e0] at hx
      rw [List.mem_singleton.1 hx]
      change (pw2 e0).testBit e0 = true
      rw [pw2_eq, Nat.testBit_two_pow_self]
    · change 1 = ((Finset.range 32768).filter fun x => (pw2 e0).testBit x = true).card
      have e : ((Finset.range 32768).filter fun x => (pw2 e0).testBit x = true) = {e0} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, pw2_eq,
          Nat.testBit_two_pow, decide_eq_true_iff]
        constructor
        · rintro ⟨-, rfl⟩
          rfl
        · rintro rfl
          exact ⟨he0, rfl⟩
      rw [e, Finset.card_singleton]
  have : ∀ n, BInv P (Nat.rec (motive := fun _ => BState) (pw2 e0, [e0], nat_lit 1)
      (fun _ st => strictS st.1 fun _ => bfsStep MU MT TG st) n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      change BInv P (strictS (Nat.rec (motive := fun _ => BState) (pw2 e0, [e0], nat_lit 1)
        (fun _ st => strictS st.1 fun _ => bfsStep MU MT TG st) n).1 fun _ =>
          bfsStep MU MT TG (Nat.rec (motive := fun _ => BState) (pw2 e0, [e0], nat_lit 1)
            (fun _ st => strictS st.1 fun _ => bfsStep MU MT TG st) n))
      rw [strictS_eq]
      exact hbfs _ ih
  exact this 65

theorem testBit_doneSet {st : BState} {e : ℕ} (h : (doneSet st).testBit e = true) :
    st.1.testBit e = true := by
  obtain ⟨R, q, n⟩ := st
  cases q with
  | nil => exact h
  | cons x q =>
    change Nat.testBit 0 e = true at h
    simp at h

theorem testBit_union (G : ℕ → ℕ) {e : ℕ} : ∀ n,
    (Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun r acc => strictN acc fun acc => Nat.lor acc (G r)) n).testBit e = true →
      ∃ r < n, (G r).testBit e = true
  | 0, h => by
    change Nat.testBit 0 e = true at h
    simp at h
  | n + 1, h => by
    change (strictN (Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun r acc => strictN acc fun acc => Nat.lor acc (G r)) n) fun acc =>
        Nat.lor acc (G n)).testBit e = true at h
    rw [strictN_eq] at h
    change (_ ||| G n).testBit e = true at h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨r, hr, h⟩ := testBit_union G n h
      exact ⟨r, by omega, h⟩
    · exact ⟨n, by omega, h⟩

theorem testBit_invSet {MU MT e : ℕ} (he : e < 32768) (h : isInvE MU MT e = true) :
    (invSet MU MT).testBit e = true := by
  have hf : (fun e => nIf(isInvE MU MT e, pw2 e, nat_lit 0)) =
      fun e => Nat.shiftLeft (nIf(isInvE MU MT e, 1, 0)) (Nat.mul 1 e) := by
    funext x
    cases isInvE MU MT x
    · change 0 = 0 <<< (1 * x)
      rw [Nat.zero_shiftLeft]
    · change 1 <<< x = 1 <<< (1 * x)
      rw [Nat.one_mul]
  have e1 : invSet MU MT =
      sumBelow 32768 512 fun e => Nat.shiftLeft (nIf(isInvE MU MT e, 1, 0)) (Nat.mul 1 e) := by
    unfold invSet
    exact congrArg (sumBelow 32768 512) hf
  have hlt : ∀ k < 32768, nIf(isInvE MU MT k, 1, 0) < 2 ^ 1 := fun k _ => by
    cases isInvE MU MT k <;> decide
  rw [← fget_one_eq_one, e1, sumBelow_get (hi := 512) (by norm_num) hlt he, h]

theorem le_ncard_class {H : Subgroup (Equiv.Perm (Fin 693))} {u : Equiv.Perm (Fin 693)}
    {el : ℕ → Equiv.Perm (Fin 693)} (hel : ∀ x < 32768, ∀ y < 32768, el x = el y → x = y)
    {st : BState} (h : BInv (fun x => ∃ c ∈ H, el x = c * u * c⁻¹) st) :
    st.2.2 ≤ (conjClass H u).ncard := by
  rw [h.2.2]
  have hinj : Set.InjOn el ↑((Finset.range 32768).filter fun x => st.1.testBit x = true) :=
    fun x hx y hy hxy => hel x (Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).1)
      y (Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).1) hxy
  have hsub : el '' ↑((Finset.range 32768).filter fun x => st.1.testBit x = true) ⊆
      conjClass H u := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc, e⟩ := (h.1 x (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2).2
    exact ⟨c, hc, e⟩
  rw [← Set.ncard_coe_finset, ← hinj.ncard_image]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

end CFSG.KC.U6.Pk

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.Sporadic.Schreier

set_option exponentiation.threshold 70000

@[expose] def tGensG (L : List (Equiv.Perm (Fin 693))) (tw : List (List ℤ)) :
    List (Equiv.Perm (Fin 693)) := tw.map (u62WG L)

@[expose] noncomputable def codesK (m : Nat) (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => CFSG.KLie.CT.andB (List.rec (motive := fun _ => Bool)
    true (fun c _ ih2 => CFSG.KLie.CT.andB (Nat.blt c m) ih2) w) ih) W

theorem codesK_iff {m : Nat} {W : List (List Nat)} :
    codesK m W = true ↔ ∀ w ∈ W, ∀ c ∈ w, c < m := by
  have inner : ∀ w : List Nat, List.rec (motive := fun _ => Bool) true
      (fun c _ ih2 => CFSG.KLie.CT.andB (Nat.blt c m) ih2) w = true ↔ ∀ c ∈ w, c < m := by
    intro w
    induction w with
    | nil => simp
    | cons c w ih =>
      change CFSG.KLie.CT.andB (Nat.blt c m) _ = true ↔ _
      rw [Snd.andB_iff, ih, Snd.blt_iff, List.forall_mem_cons]
  induction W with
  | nil => simp [codesK]
  | cons w W ihW =>
    change CFSG.KLie.CT.andB _ (codesK m W) = true ↔ _
    rw [Snd.andB_iff, List.forall_mem_cons]
    exact and_congr (inner w) ihW

@[expose] noncomputable def check3010S (LT : Nat) (aW kW tW : List (List Nat)) (M : Nat)
    (TW : List (List Nat)) : Bool :=
  strictB (evList LT aW) fun A => strictB (evList LT kW) fun K =>
    CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (List.length aW) (nat_lit 9))
          (Nat.beq (List.length TW) (List.length tW)))
        (CFSG.KLie.CT.andB (codesK (nat_lit 92) (aW ++ kW ++ tW))
          (codesK (Nat.mul (nat_lit 2) (List.length kW)) TW)))
      (CFSG.KLie.CT.andB (abarK A) (CFSG.KLie.CT.andB (conjK A (evList LT (kW ++ tW)) M (List.length (kW ++ tW)))
        (wordsK K (evList LT tW) TW)))

theorem sound3010S {LT M : Nat} {L : List (Equiv.Perm (Fin 693))} {aw kw tw : List (List ℤ)}
    {aW kW tW TW : List (List Nat)} (hL : LetsBind L LT) (haw : aw = aW.map (List.map decZ))
    (hkw : kw = kW.map (List.map decZ)) (htw : tw = tW.map (List.map decZ))
    (hk : check3010S LT aW kW tW M TW = true) :
    (∀ x ∈ aGensG L aw, orderOf x = 2 ∧ ∀ y ∈ aGensG L aw, x * y = y * x) ∧
      (∀ k ∈ kGensG L kw ++ tGensG L tw, ∀ a ∈ aGensG L aw,
        k * a * k⁻¹ ∈ Subgroup.closure {g | g ∈ aGensG L aw}) ∧
      ∀ g ∈ tGensG L tw, g ∈ Subgroup.closure {g | g ∈ kGensG L kw} := by
  open Pk Snd in
  unfold check3010S at hk
  rw [strictB_eq, strictB_eq, andB_iff, andB_iff, andB_iff, andB_iff, beq_iff, beq_iff,
    codesK_iff, codesK_iff, andB_iff, andB_iff] at hk
  obtain ⟨⟨⟨h9, hTW⟩, hc, hcT⟩, hab, hconj, hwords⟩ := hk
  have hLet : ∀ j < L.length, Rep (elt LT j) (L.getD j 1) :=
    fun j hj => rep_letter hL (hL.1 ▸ hj)
  have h92 : 2 * L.length = 92 := by rw [hL.1]
  have hcA : ∀ w ∈ aW, ∀ c ∈ w, c < 2 * L.length := fun w hw c hc' =>
    h92 ▸ hc w (List.mem_append_left _ (List.mem_append_left _ hw)) c hc'
  have hcK : ∀ w ∈ kW, ∀ c ∈ w, c < 2 * L.length := fun w hw c hc' =>
    h92 ▸ hc w (List.mem_append_left _ (List.mem_append_right _ hw)) c hc'
  have hcT' : ∀ w ∈ tW, ∀ c ∈ w, c < 2 * L.length := fun w hw c hc' =>
    h92 ▸ hc w (List.mem_append_right _ hw) c hc'
  have hcKT : ∀ w ∈ kW ++ tW, ∀ c ∈ w, c < 2 * L.length := by
    intro w hw
    rcases List.mem_append.1 hw with h | h
    · exact hcK w h
    · exact hcT' w h
  have eG : ∀ ws : List (List ℤ), ws.map (u62WG L) = ws.map (evalCodes L) := fun ws =>
    List.map_congr_left fun w _ => tab_eq _
  have hAG : aGensG L aw = (aW.map (List.map decZ)).map (evalCodes L) := by
    rw [aGensG, eG, haw]
  have hKG : kGensG L kw = (kW.map (List.map decZ)).map (evalCodes L) := by
    rw [kGensG, eG, hkw]
  have hTG : tGensG L tw = (tW.map (List.map decZ)).map (evalCodes L) := by
    rw [tGensG, eG, htw]
  have hKTG : kGensG L kw ++ tGensG L tw = ((kW ++ tW).map (List.map decZ)).map (evalCodes L) := by
    rw [hKG, hTG, List.map_append, List.map_append]
  have hA := rep_list hLet aW hcA
  have hKT := rep_list hLet (kW ++ tW) hcKT
  have hK := rep_list hLet kW hcK
  have hT := rep_list hLet tW hcT'
  have hAlen : (aGensG L aw).length = 9 := by rw [hAG, List.length_map, List.length_map, h9]
  rw [← hAG] at hA
  rw [← hKTG] at hKT
  rw [← hKG] at hK
  rw [← hTG] at hT
  unfold abarK at hab
  rw [andB_iff, andB_iff, allN_iff, allN_iff] at hab
  obtain ⟨hinv, hcomm, -⟩ := hab
  have hA9 : ∀ i < 9, Rep (elt (evList LT aW) i) ((aGensG L aw).getD i 1) :=
    fun i hi => hA i (h9 ▸ hi)
  refine ⟨fun x hx => ?_, fun k hk a ha => ?_, fun g hg => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := mem_getD hx
    rw [hAlen] at hi
    have h1 := hinv i hi
    rw [strictB_eq, andB_iff, notB_iff, beq_iff, Bool.eq_false_iff, Ne, beq_iff,
      rep_ext (rep_pc (hA9 i hi) (hA9 i hi)) rep_ID, rep_ext (hA9 i hi) rep_ID] at h1
    refine ⟨orderOf_eq_prime (by rw [pow_two]; exact h1.2) h1.1, fun y hy => ?_⟩
    obtain ⟨j, hj, rfl⟩ := mem_getD hy
    rw [hAlen] at hj
    have h2 := allN_iff.1 (hcomm i hi) j hj
    rwa [beq_iff, rep_ext (rep_pc (hA9 i hi) (hA9 j hj)) (rep_pc (hA9 j hj) (hA9 i hi))] at h2
  · obtain ⟨i, hi, rfl⟩ := mem_getD ha
    rw [hAlen] at hi
    obtain ⟨k', hk', rfl⟩ := mem_getD hk
    have hlen' : (kGensG L kw ++ tGensG L tw).length = (kW ++ tW).length := by
      rw [hKTG, List.length_map, List.length_map]
    rw [hlen'] at hk'
    unfold conjK at hconj
    rw [allN_iff] at hconj
    have h1 := hconj k' hk'
    rw [strictB_eq, strictB_eq, allN_iff] at h1
    have h2 := h1 i hi
    rw [beq_iff] at h2
    obtain ⟨g, hgm, hgr⟩ := subP_mem (m := fget M (Nat.add (Nat.mul 9 k') i) 9) hA9
      (fun i _ => getD_mem_closure _ i)
    have hr := rep_pc (rep_pc (hKT k' hk') (hA9 i hi)) (rep_invP (hKT k' hk'))
    rw [rep_ext hr hgr] at h2
    rw [h2]
    exact hgm
  · obtain ⟨j, hj, rfl⟩ := mem_getD hg
    have hjt : j < tW.length := by rwa [hTG, List.length_map, List.length_map] at hj
    have hkl : (kGensG L kw).length = kW.length := by rw [hKG, List.length_map, List.length_map]
    have hS : ∀ j < (kGensG L kw).length,
        Rep (elt (evList LT kW) j) ((kGensG L kw).getD j 1) := fun j hj => hK j (hkl ▸ hj)
    have hjT : j < TW.length := by rw [hTW]; exact hjt
    have hw := wordsK_spec TW 0 hwords j hjT
    rw [Nat.zero_add] at hw
    have hcw : ∀ c ∈ TW[j], c < 2 * (kGensG L kw).length := fun c hc' => by
      rw [hkl]
      exact hcT TW[j] (List.getElem_mem hjT) c hc'
    have hr := rep_evW hS TW[j] hcw
    rw [(rep_ext (hT j hjt) hr).1 hw]
    exact evalCodes_mem _ _

open Pk Snd in
private theorem facts3010S {LT M : ℕ} {L : List (Equiv.Perm (Fin 693))}
    {aw kw tw : List (List ℤ)} {aW kW tW TW : List (List ℕ)} (hL : LetsBind L LT)
    (haw : aw = aW.map (List.map decZ)) (hkw : kw = kW.map (List.map decZ))
    (htw : tw = tW.map (List.map decZ)) (hs : check3010S LT aW kW tW M TW = true) :
    aW.length = 9 ∧ (∀ w ∈ aW ++ kW ++ tW, ∀ c ∈ w, c < 92) ∧
      (∀ i < 9, Rep (elt (evList LT aW) i) (aG L aw i)) ∧
      (∀ i < 9, aG L aw i * aG L aw i = 1) ∧
      (∀ i < 9, ∀ j < 9, aG L aw i * aG L aw j = aG L aw j * aG L aw i) ∧
      (∀ m < 512, subG (aG L aw) m 9 = 1 → m = 0) ∧
      (∀ k < (kW ++ tW).length, ∀ v,
        (kGensG L kw ++ tGensG L tw).getD k 1 * subG (aG L aw) v 9 *
          ((kGensG L kw ++ tGensG L tw).getD k 1)⁻¹ = subG (aG L aw) (mapM M k v) 9) ∧
      (∀ m < 512, (subG (aG L aw) m 9 ⟨1, by norm_num⟩ : ℕ) = 1 →
        (subG (aG L aw) m 9 ⟨3, by norm_num⟩ : ℕ) = 3 →
        (subG (aG L aw) m 9 ⟨45, by norm_num⟩ : ℕ) = 45 → m = 0) ∧
      ∀ k < (kW ++ tW).length, ∀ i < 9,
        (kGensG L kw ++ tGensG L tw).getD k 1 * aG L aw i *
          ((kGensG L kw ++ tGensG L tw).getD k 1)⁻¹ = subG (aG L aw) (fget M (9 * k + i) 9) 9 := by
  unfold check3010S at hs
  rw [strictB_eq, strictB_eq, andB_iff, andB_iff, andB_iff, andB_iff, beq_iff, beq_iff,
    codesK_iff, codesK_iff, andB_iff, andB_iff] at hs
  obtain ⟨⟨⟨h9, -⟩, hc, -⟩, hab, hconj, -⟩ := hs
  have hcA : ∀ w ∈ aW, ∀ c ∈ w, c < 92 := fun w hw =>
    hc w (List.mem_append_left _ (List.mem_append_left _ hw))
  have hcKT : ∀ w ∈ kW ++ tW, ∀ c ∈ w, c < 92 := by
    intro w hw
    rcases List.mem_append.1 hw with h | h
    · exact hc w (List.mem_append_left _ (List.mem_append_right _ h))
    · exact hc w (List.mem_append_right _ h)
  obtain ⟨-, hA', -⟩ := rep_A hL haw h9 hcA
  have hA : ∀ i < 9, Rep (elt (evList LT aW) i) (aG L aw i) := hA'
  have hKT := rep_gens hL (kW ++ tW) hcKT
  have hKTG : ((kW ++ tW).map (List.map decZ)).map (u62WG L) = kGensG L kw ++ tGensG L tw := by
    rw [kGensG, tGensG, hkw, htw, List.map_append, List.map_append]
  rw [hKTG] at hKT
  unfold abarK at hab
  rw [andB_iff, andB_iff, allN_iff, allN_iff, allN_iff] at hab
  obtain ⟨hinv, hcomm, hdist⟩ := hab
  have hI : ∀ i < 9, aG L aw i * aG L aw i = 1 := by
    intro i hi
    have h1 := hinv i hi
    rw [strictB_eq, andB_iff, beq_iff] at h1
    exact (rep_ext (rep_pc (hA i hi) (hA i hi)) rep_ID).1 h1.2
  have hC : ∀ i < 9, ∀ j < 9, aG L aw i * aG L aw j = aG L aw j * aG L aw i := by
    intro i hi j hj
    have h2 := allN_iff.1 (hcomm i hi) j hj
    rw [beq_iff] at h2
    exact (rep_ext (rep_pc (hA i hi) (hA j hj)) (rep_pc (hA j hj) (hA i hi))).1 h2
  have hkey : ∀ m < 512, (subG (aG L aw) m 9 ⟨1, by norm_num⟩ : ℕ) = 1 →
      (subG (aG L aw) m 9 ⟨3, by norm_num⟩ : ℕ) = 3 →
      (subG (aG L aw) m 9 ⟨45, by norm_num⟩ : ℕ) = 45 → m = 0 := by
    intro m hm e1 e3 e45
    by_contra h0
    have := hdist (m - 1) (by change m - 1 < 511; omega)
    rw [show Nat.succ (m - 1) = m by omega, subImg_eq hA m 1 (by norm_num),
      subImg_eq hA m 3 (by norm_num), subImg_eq hA m 45 (by norm_num), e1, e3, e45] at this
    exact absurd this (by decide)
  have hgen : ∀ k < (kW ++ tW).length, ∀ i < 9,
      (kGensG L kw ++ tGensG L tw).getD k 1 * aG L aw i *
        ((kGensG L kw ++ tGensG L tw).getD k 1)⁻¹ = subG (aG L aw) (fget M (9 * k + i) 9) 9 := by
    intro k hk i hi
    unfold conjK at hconj
    rw [allN_iff] at hconj
    have h1 := hconj k hk
    rw [strictB_eq, strictB_eq, allN_iff] at h1
    have h2 := h1 i hi
    rw [beq_iff] at h2
    exact (rep_ext (rep_pc (rep_pc (hKT k hk) (hA i hi)) (rep_invP (hKT k hk)))
      (rep_subP hA _)).1 h2
  exact ⟨h9, hc, hA, hI, hC, fun m hm h1 => hkey m hm (by rw [h1]; rfl) (by rw [h1]; rfl)
    (by rw [h1]; rfl), fun k hk v => mapM_conj hI hC (hgen k hk) v, hkey, hgen⟩

@[expose] noncomputable def check3010O (LT : Nat) (aW kW : List (List Nat)) (M : Nat) : Bool :=
  strictB (evList LT aW) fun A =>
    CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (List.length kW) (nat_lit 3)) (orbK M (nat_lit 3)))
      (CFSG.KLie.CT.andB (Nat.beq (fixK (evW A [nat_lit 0])) (nat_lit 181))
        (CFSG.KLie.CT.andB (Nat.beq (fixK (evW A [nat_lit 2, nat_lit 8])) (nat_lit 53))
          (Nat.beq (fixK (evW A [nat_lit 0, nat_lit 2, nat_lit 8])) (nat_lit 21))))

theorem sound3010O {LT M : Nat} {L : List (Equiv.Perm (Fin 693))} {aw kw tw : List (List ℤ)}
    {aW kW tW TW : List (List Nat)} (hL : LetsBind L LT) (haw : aw = aW.map (List.map decZ))
    (hkw : kw = kW.map (List.map decZ)) (htw : tw = tW.map (List.map decZ))
    (hs : check3010S LT aW kW tW M TW = true) (ho : check3010O LT aW kW M = true) :
    (∀ a ∈ Subgroup.closure {g | g ∈ aGensG L aw}, a ≠ 1 →
        a ∈ conjClass (Subgroup.closure {g | g ∈ kGensG L kw}) (j1G L aw) ∨
        a ∈ conjClass (Subgroup.closure {g | g ∈ kGensG L kw}) (j2G L aw) ∨
        a ∈ conjClass (Subgroup.closure {g | g ∈ kGensG L kw}) (j3G L aw)) ∧
      (conjClass (Subgroup.closure {g | g ∈ kGensG L kw}) (j1G L aw)).ncard = 21 ∧
      (conjClass (Subgroup.closure {g | g ∈ kGensG L kw}) (j2G L aw)).ncard = 210 ∧
      (conjClass (Subgroup.closure {g | g ∈ kGensG L kw}) (j3G L aw)).ncard = 280 ∧
      orderOf (j1G L aw) = 2 ∧ orderOf (j2G L aw) = 2 ∧ orderOf (j3G L aw) = 2 ∧
      {p : Fin 693 | j1G L aw p = p}.ncard = 181 ∧ {p : Fin 693 | j2G L aw p = p}.ncard = 53 ∧
      {p : Fin 693 | j3G L aw p = p}.ncard = 21 := by
  open Pk Snd in
  obtain ⟨h9, hc, hA, hI, hC, hinj, hconjP, -⟩ := facts3010S hL haw hkw htw hs
  unfold check3010O at ho
  rw [strictB_eq, andB_iff, andB_iff, andB_iff, andB_iff, beq_iff, beq_iff, beq_iff,
    beq_iff] at ho
  obtain ⟨⟨hk3', horb⟩, hf1, hf2, hf3⟩ := ho
  have hk3 : kW.length = 3 := hk3'
  have hcA : ∀ w ∈ aW, ∀ c ∈ w, c < 92 := fun w hw =>
    hc w (List.mem_append_left _ (List.mem_append_left _ hw))
  obtain ⟨hlen, -, hj1, hj2, hj3⟩ := rep_A hL haw h9 hcA
  have hklen : (kGensG L kw).length = 3 := by
    rw [kGensG, hkw, List.length_map, List.length_map, hk3]
  have hk : ∀ k < (kGensG L kw).length, ∀ v, (kGensG L kw).getD k 1 * subG (aG L aw) v 9 *
      ((kGensG L kw).getD k 1)⁻¹ = subG (aG L aw) (mapM M k v) 9 := by
    intro k hk' v
    have := hconjP k (by rw [List.length_append]; rw [hklen] at hk'; omega) v
    rwa [List.getD_append _ _ _ _ hk'] at this
  have e1 : j1G L aw = subG (aG L aw) 1 9 := by
    rw [show (1 : ℕ) = 2 ^ 0 from rfl, subG_two_pow, ite_eq_left (by norm_num)]
    exact rep_unique hj1 (hA 0 (by norm_num))
  have e18 : subG (aG L aw) 18 9 = aG L aw 1 * (aG L aw 4 * 1) := by
    rw [show (18 : ℕ) = 2 ^ 1 ^^^ 2 ^ 4 from rfl, ← subG_mul hI hC _ _ 9 le_rfl, subG_two_pow,
      subG_two_pow, ite_eq_left (by norm_num), ite_eq_left (by norm_num), mul_one]
  have e2 : j2G L aw = subG (aG L aw) 18 9 := by
    rw [e18]
    exact rep_unique hj2 (rep_pc (hA 1 (by norm_num)) (rep_pc (hA 4 (by norm_num)) rep_ID))
  have e3 : j3G L aw = subG (aG L aw) 19 9 := by
    rw [show (19 : ℕ) = 2 ^ 0 ^^^ 18 from rfl, ← subG_mul hI hC _ _ 9 le_rfl, e18, subG_two_pow,
      ite_eq_left (by norm_num)]
    exact rep_unique hj3 (rep_pc (hA 0 (by norm_num))
      (rep_pc (hA 1 (by norm_num)) (rep_pc (hA 4 (by norm_num)) rep_ID)))
  unfold orbK at horb
  simp only [strictB_eq, andB_iff, beq_iff] at horb
  obtain ⟨⟨hcl1, hcl2, hcl3⟩, ⟨hp1, hp2, hp3⟩, hcov⟩ := horb
  have c1 := class_eq (x0 := 1) (by norm_num) hk (by rw [hklen]; exact hcl1)
  have c2 := class_eq (x0 := 18) (by norm_num) hk (by rw [hklen]; exact hcl2)
  have c3 := class_eq (x0 := 19) (by norm_num) hk (by rw [hklen]; exact hcl3)
  rw [hklen] at c1 c2 c3
  rw [← e1] at c1
  rw [← e2] at c2
  rw [← e3] at c3
  have hcard : ∀ S : ℕ, ((fun x => subG (aG L aw) x 9) '' {x | x < 512 ∧ S.testBit x}).ncard =
      popK S := by
    intro S
    have hset : {x | x < 512 ∧ S.testBit x} =
        ↑((Finset.range 512).filter fun x => S.testBit x) := by
      ext x
      rw [Finset.coe_filter]
      exact ⟨fun h => ⟨Finset.mem_range.2 h.1, h.2⟩, fun h => ⟨Finset.mem_range.1 h.1, h.2⟩⟩
    have hinj' : Set.InjOn (fun x => subG (aG L aw) x 9) {x | x < 512 ∧ S.testBit x} :=
      fun x hx y hy h => subG_inj hI hC hinj hx.1 hy.1 h
    rw [hinj'.ncard_image, hset, Set.ncard_coe_finset, popK_eq]
  have hne : ∀ m < 512, m ≠ 0 → subG (aG L aw) m 9 ≠ 1 := fun m hm h0 h1 => h0 (hinj m hm h1)
  have hord : ∀ m < 512, m ≠ 0 → orderOf (subG (aG L aw) m 9) = 2 := fun m hm h0 =>
    orderOf_eq_prime (by rw [pow_two]; exact subG_sq hI hC m) (hne m hm h0)
  refine ⟨fun a ha ha1 => ?_, by rw [c1, hcard, hp1], by rw [c2, hcard, hp2],
    by rw [c3, hcard, hp3], by rw [e1]; exact hord 1 (by norm_num) (by norm_num),
    by rw [e2]; exact hord 18 (by norm_num) (by norm_num),
    by rw [e3]; exact hord 19 (by norm_num) (by norm_num), ?_, ?_, ?_⟩
  · obtain ⟨m, hm, rfl⟩ := (mem_closure_sub hI hC hlen (fun _ => rfl)).1 ha
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact ha1 (subG_zero_mask _ 9)
    have hb : (Nat.lor (closeS M 3 (pw2 1) 12) (Nat.lor (closeS M 3 (pw2 18) 12)
        (closeS M 3 (pw2 19) 12))).testBit m = true := by
      rw [hcov]
      obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
      have e : (pw2 512).sub 2 = 2 * (2 ^ 511 - 1) := by rw [pw2_eq]; rfl
      rw [e, Nat.testBit_succ, Nat.mul_div_cancel_left _ (by norm_num),
        Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
      omega
    change ((closeS M 3 (pw2 1) 12) ||| ((closeS M 3 (pw2 18) 12) |||
      (closeS M 3 (pw2 19) 12))).testBit m = true at hb
    rw [Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true] at hb
    rcases hb with hb | hb | hb
    · left
      rw [c1]
      exact ⟨m, ⟨hm, hb⟩, rfl⟩
    · right
      left
      rw [c2]
      exact ⟨m, ⟨hm, hb⟩, rfl⟩
    · right
      right
      rw [c3]
      exact ⟨m, ⟨hm, hb⟩, rfl⟩
  · have := fixK_eq (rep_pc hj1 rep_ID)
    rw [mul_one] at this
    rw [← this]
    exact hf1
  · rw [← fixK_eq hj2]
    exact hf2
  · rw [← fixK_eq hj3]
    exact hf3

@[expose] noncomputable def check3010F (LT : Nat) (aW : List (List Nat)) (FA RP SO n : Nat) :
    Bool :=
  strictB (evList LT aW) fun A => CFSG.KLie.CT.andB (fixAK3 A FA) (transK LT FA RP SO n)

open scoped Pointwise in
theorem sound3010F {LT RP SO n : Nat} {L : List (Equiv.Perm (Fin 693))} {aw : List (List ℤ)}
    {aW : List (List Nat)} {fa : List ℕ} (hL : LetsBind L LT)
    (haw : aw = aW.map (List.map decZ)) (hfa : ∀ x ∈ fa, x < 693)
    (hlen : aW.length = 9) (hc : ∀ w ∈ aW, ∀ c ∈ w, c < 92)
    (hk : check3010F LT aW (maskL fa) RP SO n = true) :
    {p : Fin 693 | j3G L aw p = p} = CFSG.Certificates.finSet 693 fa ∧
      (∀ a ∈ aGensG L aw, ∀ p ∈ CFSG.Certificates.finSet 693 fa, a p = p) ∧
      n ≤ (Set.range fun g : Subgroup.closure {g | g ∈ L} =>
        g • CFSG.Certificates.finSet 693 fa).ncard := by
  open Pk Snd in
  unfold check3010F at hk
  rw [strictB_eq, andB_iff] at hk
  obtain ⟨hfix, htr⟩ := hk
  obtain ⟨hlen9, hA, -, -, hj3⟩ := rep_A hL haw hlen hc
  unfold fixAK3 at hfix
  rw [strictB_eq, andB_iff, allN_iff] at hfix
  obtain ⟨hf3, hfA⟩ := hfix
  have hf3' := allBelow_spec hf3 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · ext p
    rw [← bits_maskL]
    simp only [Set.mem_ofPred_eq, bits]
    have h := hf3' p p.isLt
    rw [ap10_eq hj3 p.isLt] at h
    by_cases hp : j3G L aw p = p
    · have hb : Nat.beq ((j3G L aw) ⟨p, p.isLt⟩ : ℕ) p = true := beq_iff.2 (by rw [hp])
      rw [hb] at h
      exact ⟨fun _ => fget_one_eq_one.1 (beq_iff.1 h), fun _ => hp⟩
    · have hb : Nat.beq ((j3G L aw) ⟨p, p.isLt⟩ : ℕ) p = false :=
        beq_false fun e => hp (Fin.ext e)
      rw [hb] at h
      have := fget_one_eq_zero.1 (beq_iff.1 h)
      simp only [hp, false_iff, this]
      simp
  · intro a ha p hp
    obtain ⟨i, hi, rfl⟩ := mem_getD ha
    rw [hlen9] at hi
    have h := hfA i hi
    rw [strictB_eq] at h
    have h' := allBelow_spec h (by norm_num) p p.isLt
    rw [orB_iff, beq_iff, beq_iff, fget_one_eq_zero, ap10_eq (hA i hi) p.isLt] at h'
    rw [← bits_maskL] at hp
    rcases h' with h' | h'
    · exact absurd hp (by simp [bits, h'])
    · exact Fin.ext h'
  · unfold transK at htr
    rw [strictB_eq, andB_iff, andB_iff, allN_iff, allN_iff, allN_iff] at htr
    obtain ⟨hpar, hso, hinc⟩ := htr
    have hpar' : ∀ j < n, j = 0 ∨ (recPar RP j < j ∧ recLet RP j < 46) := by
      intro j hj
      have := hpar j hj
      rw [orB_iff, beq_iff, andB_iff, blt_iff, blt_iff] at this
      exact this
    obtain ⟨F, hF, hz, hs⟩ := recSets_spec hL (maskL_lt hfa) hpar' n le_rfl
    have hX : ∀ i, fget (recSets LT (maskL fa) RP n) i 693 = F i := by
      intro i
      rw [fget_pg]
      refine CFSG.KS.PF.pg_of_fld hF ?_
      by_cases hi : i < n
      · exact (hs i hi).1
      · rw [hz i (by omega)]
        exact Nat.two_pow_pos _
    have hso' : ∀ i < n, fget SO i 10 < n := fun i hi => blt_iff.1 (hso i hi)
    have hinc' : ∀ i, i + 1 < n → F (fget SO i 10) < F (fget SO (i + 1) 10) := by
      intro i hi
      have := hinc i (by change i < n - 1; omega)
      rw [blt_iff, hX, hX] at this
      exact this
    have hmono : ∀ i j, i < j → j < n → F (fget SO i 10) < F (fget SO j 10) := by
      intro i j hij hj
      induction j with
      | zero => omega
      | succ j ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
        · exact Nat.lt_trans (ih h (by omega)) (hinc' j hj)
        · exact hinc' i hj
    let f : Fin n → Set (Fin 693) := fun i => bits (F (fget SO i 10))
    have hf : Function.Injective f := by
      intro i j hij
      have e := bits_inj (hs _ (hso' i i.isLt)).1 (hs _ (hso' j j.isLt)).1 hij
      by_contra hne
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · exact absurd e (Nat.ne_of_lt (hmono i j h j.isLt))
      · exact absurd e (Nat.ne_of_gt (hmono j i h i.isLt))
    have hsub : Set.range f ⊆ Set.range fun g : Subgroup.closure {g | g ∈ L} =>
        g • CFSG.Certificates.finSet 693 fa := by
      rintro _ ⟨i, rfl⟩
      obtain ⟨-, g, hg, hb⟩ := hs _ (hso' i i.isLt)
      refine ⟨⟨g, hg⟩, ?_⟩
      change g • CFSG.Certificates.finSet 693 fa = f i
      rw [← bits_maskL]
      exact hb.symm
    calc n = Nat.card (Fin n) := (Nat.card_fin n).symm
      _ = (Set.range f).ncard := (Set.ncard_range_of_injective hf).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

@[expose] noncomputable def withSbar (LT : Nat) (aW tW TEW sRW sCW : List (List Nat)) (M : Nat)
    (k : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool) : Bool :=
  strictB (evList LT aW) fun A => strictB (evList LT tW) fun Tg =>
  strictB (evList Tg TEW) fun TE => strictB (keysK TE) fun KY =>
  strictB (mulTab TE KY) fun MU => strictB (mtList M TEW) fun MT =>
  strictB (sumN (nat_lit 4) fun g =>
    Nat.shiftLeft (idxK KY (keyP (elt Tg g))) (Nat.mul (nat_lit 7) g)) fun TG =>
  strictB (Nat.lor A (Nat.shiftLeft Tg (nat_lit 62370))) fun S =>
  strictB (evList S sRW) fun R => strictB (evList LT sCW) fun Cj =>
    k A Tg TE MU MT TG S R Cj

theorem withSbar_spec {LT M : Nat} {aW tW TEW sRW sCW : List (List Nat)}
    {k : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool}
    (h : withSbar LT aW tW TEW sRW sCW M k = true) :
    ∃ MU MT TG, MU = mulTab (evList (evList LT tW) TEW) (keysK (evList (evList LT tW) TEW)) ∧
      MT = mtList M TEW ∧
      TG = sumN 4 (fun g => Nat.shiftLeft (idxK (keysK (evList (evList LT tW) TEW))
        (keyP (elt (evList LT tW) g))) (Nat.mul 7 g)) ∧
      k (evList LT aW) (evList LT tW) (evList (evList LT tW) TEW) MU MT TG
        (Nat.lor (evList LT aW) (Nat.shiftLeft (evList LT tW) 62370))
        (evList (Nat.lor (evList LT aW) (Nat.shiftLeft (evList LT tW) 62370)) sRW)
        (evList LT sCW) = true := by
  unfold withSbar at h
  simp only [Snd.strictB_eq] at h
  exact ⟨_, _, _, rfl, rfl, rfl, h⟩

@[expose] noncomputable def check3010Y (LT : Nat) (aW tW TEW sRW sCW : List (List Nat))
    (M FA RD CM : Nat) : Bool :=
  CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (List.length aW) (nat_lit 9)) (CFSG.KLie.CT.andB (Nat.beq (List.length tW) (nat_lit 4))
      (CFSG.KLie.CT.andB (Nat.beq (List.length TEW) (nat_lit 64))
        (CFSG.KLie.CT.andB (Nat.beq (List.length sCW) (List.length sRW)) (CFSG.KLie.CT.andB (evenW TEW)
          (CFSG.KLie.CT.andB (codesK (nat_lit 8) TEW)
            (CFSG.KLie.CT.andB (codesK (nat_lit 26) sRW) (codesK (nat_lit 92) sCW))))))))
    (withSbar LT aW tW TEW sRW sCW M fun A Tg TE MU MT TG S R Cj =>
      CFSG.KLie.CT.andB (check3010T A Tg TE FA)
        (CFSG.KLie.CT.andB (allN (List.length sRW) fun r => strictB (elt R r) fun x =>
            strictB (fget RD r (nat_lit 15)) fun e =>
              CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (pc x x) ID693) (CFSG.KLie.CT.notB (Nat.beq x ID693)))
                (CFSG.KLie.CT.andB (Nat.beq x (pc (subP A (Nat.land e (nat_lit 511)))
                    (elt TE (Nat.shiftRight e (nat_lit 9)))))
                  (Nat.beq (conjP (elt Cj r) x) (subP A (fget CM r (nat_lit 9))))))
          (CFSG.KLie.CT.andB (allN (nat_lit 13) fun k => strictB (elt S k) fun s =>
              Nat.beq (pc (elt A (nat_lit 0)) s) (pc s (elt A (nat_lit 0))))
            (CFSG.KLie.CT.andB (sbarK MU MT TG RD (sumN (List.length sRW) fun r =>
                Nat.shiftLeft (fixK (elt R r)) (Nat.mul (nat_lit 10) r)) (List.length sRW))
              (thomK MU MT TG)))))

private def teG (L : List (Equiv.Perm (Fin 693))) (tw : List (List ℤ)) (TEW : List (List ℕ))
    (t : ℕ) : Equiv.Perm (Fin 693) :=
  ((TEW.map (List.map decZ)).map (evalCodes (tGensG L tw))).getD t 1

private def elG (a te : ℕ → Equiv.Perm (Fin 693)) (e : ℕ) : Equiv.Perm (Fin 693) :=
  Pk.subG a (e % 512) 9 * te (e / 512)

theorem evenW_iff {W : List (List ℕ)} : evenW W = true ↔ ∀ w ∈ W, ∀ c ∈ w, c % 2 = 0 := by
  open Snd in
  have inner : ∀ w : List ℕ, List.rec (motive := fun _ => Bool) true
      (fun c _ ih' => CFSG.KLie.CT.andB (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0)) ih') w = true ↔
        ∀ c ∈ w, c % 2 = 0 := by
    intro w
    induction w with
    | nil => simp
    | cons c w ih =>
      change CFSG.KLie.CT.andB (Nat.beq (Nat.land c 1) 0) _ = true ↔ _
      have hand : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
      rw [andB_iff, ih, beq_iff, List.forall_mem_cons, hand]
  induction W with
  | nil => simp [evenW]
  | cons w W ihW =>
    change CFSG.KLie.CT.andB _ (evenW W) = true ↔ _
    rw [Snd.andB_iff, List.forall_mem_cons]
    exact and_congr (inner w) ihW

open Pk Snd in
private theorem factsT0 {LT M FA MU MT TG : ℕ} {L : List (Equiv.Perm (Fin 693))}
    {aw kw tw : List (List ℤ)} {aW kW tW TW TEW : List (List ℕ)} (hL : LetsBind L LT)
    (haw : aw = aW.map (List.map decZ)) (hkw : kw = kW.map (List.map decZ))
    (htw : tw = tW.map (List.map decZ)) (hs : check3010S LT aW kW tW M TW = true)
    (hkl : kW.length = 3) (h4 : tW.length = 4) (h64 : TEW.length = 64) (hev : evenW TEW = true)
    (hc8 : codesK 8 TEW = true)
    (hT : check3010T (evList LT aW) (evList LT tW) (evList (evList LT tW) TEW) FA = true)
    (hMU : MU = mulTab (evList (evList LT tW) TEW) (keysK (evList (evList LT tW) TEW)))
    (hMT : MT = mtList M TEW)
    (hTG : TG = sumN 4 (fun g => Nat.shiftLeft (idxK (keysK (evList (evList LT tW) TEW))
        (keyP (elt (evList LT tW) g))) (Nat.mul 7 g))) :
    (tGensG L tw).length = 4 ∧
      (∀ j < 4, Rep (elt (evList LT tW) j) ((tGensG L tw).getD j 1)) ∧
      (∀ t < 64, Rep (elt (evList (evList LT tW) TEW) t) (teG L tw TEW t)) ∧
      (∀ t, teG L tw TEW t ∈ Subgroup.closure {g | g ∈ tGensG L tw}) ∧
      (∀ x ∈ Subgroup.closure {g | g ∈ tGensG L tw}, ∃ t < 64, x = teG L tw TEW t) ∧
      (∀ s < 64, ∀ t < 64, teG L tw TEW s = teG L tw TEW t → s = t) ∧
      teG L tw TEW 0 = 1 ∧
      (∀ i < 64, ∀ j < 64, mu MU i j < 64 ∧
        teG L tw TEW (mu MU i j) = teG L tw TEW i * teG L tw TEW j) ∧
      (∀ t < 64, MatRep (aG L aw) (mt MT t) (teG L tw TEW t)) ∧
      (∀ g < 4, fget TG g (nat_lit 7) < 64 ∧
        teG L tw TEW (fget TG g (nat_lit 7)) = (tGensG L tw).getD g 1) ∧
      (∀ g < 4, (tGensG L tw).getD g 1 * (tGensG L tw).getD g 1 = 1) ∧
      ∀ t < 64, t ≠ 0 → ∀ v < 512, subG (aG L aw) v 9 ≠ teG L tw TEW t := by
  obtain ⟨h9, hc, hA, hI, hC, hinj, -, -, hgen⟩ := facts3010S hL haw hkw htw hs
  have hcT : ∀ w ∈ tW, ∀ c ∈ w, c < 92 := fun w hw => hc w (List.mem_append_right _ hw)
  have hTGl : tGensG L tw = (tW.map (List.map decZ)).map (u62WG L) := by rw [tGensG, htw]
  have htlen : (tGensG L tw).length = 4 := by rw [hTGl, List.length_map, List.length_map, h4]
  have hTg : ∀ j < 4, Rep (elt (evList LT tW) j) ((tGensG L tw).getD j 1) := by
    intro j hj
    rw [hTGl]
    exact rep_gens hL tW hcT j (by rw [h4]; exact hj)
  have hTg' : ∀ j < (tGensG L tw).length, Rep (elt (evList LT tW) j) ((tGensG L tw).getD j 1) :=
    fun j hj => hTg j (htlen ▸ hj)
  rw [codesK_iff] at hc8
  rw [evenW_iff] at hev
  have hcE : ∀ w ∈ TEW, ∀ c ∈ w, c < 2 * (tGensG L tw).length := fun w hw c hc' => by
    rw [htlen]
    exact hc8 w hw c hc'
  have hTE : ∀ t < 64, Rep (elt (evList (evList LT tW) TEW) t) (teG L tw TEW t) := fun t ht =>
    rep_list hTg' TEW hcE t (by rw [h64]; exact ht)
  have hmemT : ∀ t, teG L tw TEW t ∈ Subgroup.closure {g | g ∈ tGensG L tw} := by
    intro t
    unfold teG
    rw [List.getD_eq_getElem?_getD]
    cases h : ((TEW.map (List.map decZ)).map (evalCodes (tGensG L tw)))[t]? with
    | none => exact Subgroup.one_mem _
    | some x =>
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? h)
      exact evalCodes_mem _ _
  unfold check3010T at hT
  simp only [strictB_eq, andB_iff, orB_iff, notB_iff, beq_iff, blt_iff, allN_iff,
    Bool.eq_false_iff, Ne] at hT
  obtain ⟨h0, hdist, hcl, hinvT, hmove, hfix⟩ := hT
  set Tg := evList LT tW with hTgdef
  set TE := evList Tg TEW with hTEdef
  have hkeyP : ∀ x, keyP x < 2 ^ 20 := by
    intro x
    have h1 := fget_lt x 1 10
    have h3 := fget_lt x 3 10
    change fget x 1 10 * 1024 + fget x 3 10 < 2 ^ 20
    have e10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
    have e20 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
    rw [e10] at h1 h3
    rw [e20]
    omega
  have hKY : ∀ j < 64, fget (keysK TE) j 20 = keyP (elt TE j) := fun j hj =>
    sumN_get (f := fun j => keyP (elt TE j)) (w := 20) (n := 64) (fun i _ => hkeyP _) hj
  have hlook : ∀ x j0, j0 < 64 → elt TE j0 = x → idxK (keysK TE) (keyP x) = j0 := by
    intro x j0 hj0 hx
    refine idxK_eq hj0 (by rw [hKY j0 hj0, hx]) fun j hj hk => ?_
    rcases hdist j hj j0 hj0 with h | h
    · exact h
    · exact (h (by rw [hk, hKY j0 hj0, hx])).elim
  have hinjT : ∀ s < 64, ∀ t < 64, teG L tw TEW s = teG L tw TEW t → s = t := by
    intro s hs t ht he
    have e : elt TE s = elt TE t := (rep_ext (hTE s hs) (hTE t ht)).2 he
    rcases hdist s hs t ht with h | h
    · exact h
    · exact (h (by rw [hKY s hs, hKY t ht, e])).elim
  have hte0 : teG L tw TEW 0 = 1 := rep_unique (hTE 0 (by norm_num)) (by rw [h0]; exact rep_ID)
  have hgmul : ∀ g < 4, ∀ i < 64, ∃ j < 64,
      teG L tw TEW j = (tGensG L tw).getD g 1 * teG L tw TEW i := by
    intro g hg i hi
    obtain ⟨hj, hjx⟩ := hcl i hi g hg
    have := hTE _ hj
    rw [hjx] at this
    exact ⟨_, hj, rep_unique this (rep_pc (hTg g hg) (hTE i hi))⟩
  have hinv : ∀ g < 4, (tGensG L tw).getD g 1 * (tGensG L tw).getD g 1 = 1 := fun g hg =>
    (rep_ext (rep_pc (hTg g hg) (hTg g hg)) rep_ID).1 (hinvT g hg)
  have henum : ∀ x ∈ Subgroup.closure {g | g ∈ tGensG L tw}, ∃ t < 64, x = teG L tw TEW t := by
    intro x hx
    induction hx using Subgroup.closure_induction_left with
    | one => exact ⟨0, by norm_num, hte0.symm⟩
    | mul_left x hx y _ ih =>
      obtain ⟨t, ht, rfl⟩ := ih
      obtain ⟨g, hg, rfl⟩ := mem_getD hx
      rw [htlen] at hg
      obtain ⟨j, hj, e⟩ := hgmul g hg t ht
      exact ⟨j, hj, e.symm⟩
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨t, ht, rfl⟩ := ih
      obtain ⟨g, hg, rfl⟩ := mem_getD hx
      rw [htlen] at hg
      obtain ⟨j, hj, e⟩ := hgmul g hg t ht
      rw [inv_eq_of_mul_eq_one_right (hinv g hg)]
      exact ⟨j, hj, e.symm⟩
  have hmulK : ∀ i < 64, ∀ j < 64, mulK TE (keysK TE) i j < 64 ∧
      teG L tw TEW (mulK TE (keysK TE) i j) = teG L tw TEW i * teG L tw TEW j := by
    intro i hi j hj
    obtain ⟨k, hk, e⟩ := henum _ (Subgroup.mul_mem _ (hmemT i) (hmemT j))
    have ek : elt TE k = pc (elt TE i) (elt TE j) :=
      (rep_ext (hTE k hk) (rep_pc (hTE i hi) (hTE j hj))).2 e.symm
    have hkey : keyP (pc (elt TE i) (elt TE j)) = Nat.add (Nat.mul (ap10 (elt TE i)
        (ap10 (elt TE j) 1)) 1024) (ap10 (elt TE i) (ap10 (elt TE j) 3)) := by
      unfold keyP
      rw [ap10_pc (p := 1) _ _ (by norm_num), ap10_pc (p := 3) _ _ (by norm_num)]
    have hk' : mulK TE (keysK TE) i j = k := by
      unfold mulK
      rw [strictN_eq, strictN_eq]
      exact (congrArg (idxK (keysK TE)) hkey).symm.trans (hlook _ k hk ek)
    rw [hk']
    exact ⟨hk, e.symm⟩
  have hmuK : ∀ i < 64, ∀ j < 64, mu (mulTab TE (keysK TE)) i j = mulK TE (keysK TE) i j := by
    intro i hi j hj
    have hf : ∀ k < 4096, mulK TE (keysK TE) (Nat.shiftRight k 6) (Nat.land k 63) < 2 ^ 7 := by
      intro k _
      have : mulK TE (keysK TE) (Nat.shiftRight k 6) (Nat.land k 63) ≤ 64 := by
        unfold mulK
        rw [strictN_eq, strictN_eq]
        exact idxK_le _ _
      exact Nat.lt_of_le_of_lt this (by norm_num)
    have := sumBelow_get (m := 4096) (hi := 64) (w := 7)
      (f := fun k => mulK TE (keysK TE) (Nat.shiftRight k 6) (Nat.land k 63)) (by norm_num) hf
      (i := 64 * i + j) (by omega)
    have e1 : Nat.shiftRight (64 * i + j) 6 = i := by
      change (64 * i + j) >>> 6 = i
      rw [Nat.shiftRight_eq_div_pow]
      omega
    have e2 : Nat.land (64 * i + j) 63 = j := by
      have : Nat.land (64 * i + j) 63 = (64 * i + j) % 64 := Nat.and_two_pow_sub_one_eq_mod _ 6
      rw [this]
      omega
    rw [e1, e2] at this
    exact this
  have hmu : ∀ i < 64, ∀ j < 64, mu (mulTab TE (keysK TE)) i j < 64 ∧
      teG L tw TEW (mu (mulTab TE (keysK TE)) i j) = teG L tw TEW i * teG L tw TEW j := by
    intro i hi j hj
    rw [hmuK i hi j hj]
    exact hmulK i hi j hj
  have hkg : (kGensG L kw).length = 3 := by rw [kGensG, hkw, List.length_map, List.length_map, hkl]
  have hblk : ∀ j < (tGensG L tw).length,
      MatRep (aG L aw) (fget M (Nat.add 3 j) 81) ((tGensG L tw).getD j 1) := by
    intro j hj
    rw [htlen] at hj
    refine ⟨fget_lt _ _ _, fun i hi => ⟨fget_lt _ _ _, ?_⟩⟩
    rw [fget_fget81 _ _ _ hi]
    have hk : Nat.add 3 j < (kW ++ tW).length := by
      rw [List.length_append, hkl, h4]
      change 3 + j < 3 + 4
      omega
    have := hgen _ hk i hi
    rw [List.getD_append_right _ _ _ _ (by rw [hkg]; change 3 ≤ 3 + j; omega), hkg] at this
    have e : Nat.add 3 j - 3 = j := by
      change 3 + j - 3 = j
      omega
    rw [e] at this
    exact this
  have hMat : ∀ t < 64, MatRep (aG L aw) (mt (mtList M TEW) t) (teG L tw TEW t) := by
    have hw : ∀ w ∈ TEW, ∀ c ∈ w, c < 2 * (tGensG L tw).length ∧ c % 2 = 0 :=
      fun w hw c hc' => ⟨hcE w hw c hc', hev w hw c hc'⟩
    have hmw : ∀ w ∈ TEW, MatRep (aG L aw) (matW M w) (evalCodes (tGensG L tw) (w.map decZ)) :=
      fun w hw' => matW_rep hI hC hblk w (hw w hw')
    intro t ht
    have ht' : t < TEW.length := by rw [h64]; exact ht
    rw [mt_mtList M TEW (fun w hw' => (hmw w hw').1) ht']
    have e : teG L tw TEW t = evalCodes (tGensG L tw) (TEW[t].map decZ) := by
      unfold teG
      rw [List.getD_eq_getElem _ _ (by simpa using ht'), List.getElem_map, List.getElem_map]
    rw [e]
    exact hmw _ (List.getElem_mem ht')
  have hTGf : ∀ g < 4, fget (sumN 4 fun g => Nat.shiftLeft (idxK (keysK TE) (keyP (elt Tg g)))
      (Nat.mul 7 g)) g (nat_lit 7) < 64 ∧ teG L tw TEW (fget (sumN 4 fun g =>
        Nat.shiftLeft (idxK (keysK TE) (keyP (elt Tg g))) (Nat.mul 7 g)) g (nat_lit 7)) =
        (tGensG L tw).getD g 1 := by
    intro g hg
    have hf : ∀ g < 4, idxK (keysK TE) (keyP (elt Tg g)) < 2 ^ 7 := fun g _ => by
      exact Nat.lt_of_le_of_lt (idxK_le (keysK TE) (keyP (elt Tg g))) (by norm_num)
    have e1 := sumN_get (f := fun g => idxK (keysK TE) (keyP (elt Tg g))) (w := 7) (n := 4) hf hg
    rw [e1]
    obtain ⟨hj, hjx⟩ := hcl 0 (by norm_num) g hg
    have e : pc (elt Tg g) (elt TE 0) = elt Tg g := by
      rw [h0]
      exact (rep_ext (rep_pc (hTg g hg) rep_ID) (hTg g hg)).2 (mul_one _)
    rw [e] at hj hjx
    refine ⟨hj, ?_⟩
    have := hTE _ hj
    rw [hjx] at this
    exact rep_unique this (hTg g hg)
  have hfixA : ∀ v, ∀ p : Fin 693, FA.testBit p = true → subG (aG L aw) v 9 p = p := by
    intro v p hp
    have ha : ∀ i < 9, aG L aw i p = p := by
      intro i hi
      have h := allBelow_spec (hfix i hi) (by norm_num) p p.isLt
      rw [orB_iff, beq_iff, beq_iff, fget_one_eq_zero, ap10_eq (hA i hi) p.isLt] at h
      rcases h with h | h
      · rw [hp] at h
        exact absurd h (by simp)
      · exact Fin.ext h
    have : ∀ n ≤ 9, subG (aG L aw) v n p = p := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        rw [subG]
        split
        · rw [Equiv.Perm.mul_apply, ih (by omega), ha n (by omega)]
        · exact ih (by omega)
    exact this 9 le_rfl
  have hcap : ∀ t < 64, t ≠ 0 → ∀ v < 512, subG (aG L aw) v 9 ≠ teG L tw TEW t := by
    intro t ht ht0 v _ he
    obtain ⟨j, rfl⟩ : ∃ j, t = j + 1 := ⟨t - 1, by omega⟩
    apply hmove j (by omega)
    refine allBelow_of fun p hp => ?_
    rw [orB_iff, beq_iff, beq_iff]
    by_cases hb : fget FA p 1 = 0
    · exact Or.inl hb
    · right
      have hbit : FA.testBit p = true := by
        have := CFSG.KS.PF.pg_lt 1 FA p
        rw [← fget_pg] at this
        exact fget_one_eq_one.1 (by omega)
      have := hfixA v ⟨p, hp⟩ hbit
      rw [he] at this
      rw [ap10_eq (hTE _ ht) hp, this]
  rw [hMU, hMT, hTG]
  exact ⟨htlen, hTg, hTE, hmemT, henum, hinjT, hte0, hmu, hMat, hTGf, hinv, hcap⟩

theorem sound3010Y {LT M FA RD CM : Nat} {L : List (Equiv.Perm (Fin 693))}
    {aw kw tw srw scw : List (List ℤ)} {aW kW tW TW TEW sRW sCW : List (List Nat)}
    (hL : LetsBind L LT) (haw : aw = aW.map (List.map decZ)) (hkw : kw = kW.map (List.map decZ))
    (htw : tw = tW.map (List.map decZ)) (hsr : srw = sRW.map (List.map decZ))
    (hsc : scw = sCW.map (List.map decZ)) (hs : check3010S LT aW kW tW M TW = true)
    (hkl : kW.length = 3) (hy : check3010Y LT aW tW TEW sRW sCW M FA RD CM = true) :
    (∀ u ∈ Subgroup.closure {g | g ∈ aGensG L aw ++ tGensG L tw}, orderOf u = 2 →
        ∃ r ∈ srw.map (evalCodes (aGensG L aw ++ tGensG L tw)),
          ∃ c ∈ Subgroup.closure {g | g ∈ aGensG L aw ++ tGensG L tw}, u = c * r * c⁻¹) ∧
      (∀ r ∈ srw.map (evalCodes (aGensG L aw ++ tGensG L tw)), orderOf r = 2) ∧
      (∀ p ∈ List.zip (scw.map (u62WG L)) (srw.map (evalCodes (aGensG L aw ++ tGensG L tw))),
        p.1 * p.2 * p.1⁻¹ ∈ Subgroup.closure {g | g ∈ aGensG L aw}) ∧
      (∀ g ∈ aGensG L aw ++ tGensG L tw, j1G L aw * g = g * j1G L aw) ∧
      (∀ x ∈ Subgroup.closure {g | g ∈ aGensG L aw ++ tGensG L tw},
        (∀ g ∈ aGensG L aw ++ tGensG L tw, x * g = g * x) → x = 1 ∨ x = j1G L aw) ∧
      ∀ r ∈ srw.map (evalCodes (aGensG L aw ++ tGensG L tw)),
        ({p : Fin 693 | r p = p}.ncard = 53 →
          2 ≤ (conjClass (Subgroup.closure {g | g ∈ aGensG L aw ++ tGensG L tw}) r).ncard) ∧
        ({p : Fin 693 | r p = p}.ncard = 21 →
          8 ≤ (conjClass (Subgroup.closure {g | g ∈ aGensG L aw ++ tGensG L tw}) r).ncard) := by
  open Pk Snd in
  subst hsr hsc
  obtain ⟨h9, hc, hA, hI, hC, hinj, -, -, -⟩ := facts3010S hL haw hkw htw hs
  have hcA : ∀ w ∈ aW, ∀ c ∈ w, c < 92 := fun w hw =>
    hc w (List.mem_append_left _ (List.mem_append_left _ hw))
  obtain ⟨hlenA, -, hj1, -, -⟩ := rep_A hL haw h9 hcA
  unfold check3010Y at hy
  rw [andB_iff] at hy
  obtain ⟨hl, hw⟩ := hy
  simp only [andB_iff, beq_iff] at hl
  obtain ⟨-, h4, h64, -, hev, hc8, hc26, hc92⟩ := hl
  rw [codesK_iff] at hc26 hc92
  obtain ⟨MU, MT, TG, hMU, hMT, hTG, hw⟩ := withSbar_spec hw
  rw [andB_iff, andB_iff, andB_iff, andB_iff] at hw
  obtain ⟨hT, hrep, hcom, hsb, -⟩ := hw
  obtain ⟨htlen, -, hTE, hmemT, henum, hinjT, hte0, hmu, hmt, hTGf, hinvT, hcap⟩ :=
    factsT0 hL haw hkw htw hs hkl h4 h64 hev hc8 hT hMU hMT hTG
  have hgsl : (aGensG L aw ++ tGensG L tw).length = 13 := by
    rw [List.length_append, hlenA, htlen]
  have hgsA : ∀ j < 9, (aGensG L aw ++ tGensG L tw).getD j 1 = aG L aw j := fun j hj => by
    rw [List.getD_append _ _ _ _ (by rw [hlenA]; exact hj)]
    rfl
  have hgsT : ∀ j < 4, (aGensG L aw ++ tGensG L tw).getD (j + 9) 1 = (tGensG L tw).getD j 1 :=
    fun j hj => by
      rw [List.getD_append_right _ _ _ _ (by rw [hlenA]; omega), hlenA, Nat.add_sub_cancel]
  have hgmem : ∀ k, (aGensG L aw ++ tGensG L tw).getD k 1 ∈
      Subgroup.closure {g | g ∈ aGensG L aw ++ tGensG L tw} := getD_mem_closure _
  have hgin : ∀ k < 13, (aGensG L aw ++ tGensG L tw).getD k 1 ∈ aGensG L aw ++ tGensG L tw :=
    fun k hk => by
      rw [List.getD_eq_getElem _ _ (by rw [hgsl]; exact hk)]
      exact List.getElem_mem _
  have hcAT : ∀ w ∈ aW ++ tW, ∀ c ∈ w, c < 92 := by
    intro w hw
    rcases List.mem_append.1 hw with h | h
    · exact hcA w h
    · exact hc w (List.mem_append_right _ h)
  have hS : ∀ j < (aGensG L aw ++ tGensG L tw).length,
      Rep (elt (Nat.lor (evList LT aW) (Nat.shiftLeft (evList LT tW) 62370)) j)
        ((aGensG L aw ++ tGensG L tw).getD j 1) :=
    cat_rep (kw := tw) hL haw htw h9 hcAT
  have hmulP : ∀ v w, ∀ t < 64, ∀ s < 64,
      subG (aG L aw) v 9 * teG L tw TEW t * (subG (aG L aw) w 9 * teG L tw TEW s) =
        subG (aG L aw) (v ^^^ mapV (mt MT t) w) 9 * teG L tw TEW (mu MU t s) := by
    intro v w t ht s hs
    rw [← subG_mul hI hC _ _ 9 le_rfl, ← mat_apply hI hC (hmt t ht) w, (hmu t ht s hs).2]
    group
  have hinjP : ∀ v < 512, ∀ v' < 512, ∀ t < 64, ∀ t' < 64,
      subG (aG L aw) v 9 * teG L tw TEW t = subG (aG L aw) v' 9 * teG L tw TEW t' →
        v = v' ∧ t = t' := by
    intro v hv v' hv' t ht t' ht' h
    obtain ⟨u, hu, eu⟩ := henum (teG L tw TEW t' * (teG L tw TEW t)⁻¹)
      (Subgroup.mul_mem _ (hmemT t') (Subgroup.inv_mem _ (hmemT t)))
    have e1 : subG (aG L aw) (v' ^^^ v) 9 = teG L tw TEW t' * (teG L tw TEW t)⁻¹ := by
      calc subG (aG L aw) (v' ^^^ v) 9 = subG (aG L aw) v' 9 * subG (aG L aw) v 9 :=
            (subG_mul hI hC _ _ 9 le_rfl).symm
        _ = subG (aG L aw) v' 9 * (subG (aG L aw) v 9 * teG L tw TEW t) * (teG L tw TEW t)⁻¹ := by
            group
        _ = subG (aG L aw) v' 9 * (subG (aG L aw) v' 9 * teG L tw TEW t') *
            (teG L tw TEW t)⁻¹ := by rw [h]
        _ = teG L tw TEW t' * (teG L tw TEW t)⁻¹ := by
            rw [← mul_assoc (subG (aG L aw) v' 9), subG_sq hI hC, one_mul]
    have hxv : v' ^^^ v < 512 := Nat.xor_lt_two_pow (n := 9) hv' hv
    have hu0 : u = 0 := by
      by_contra hne
      exact hcap u hu hne _ hxv (e1.trans eu)
    rw [hu0, hte0] at eu
    have hvv := eq_of_xor_eq_zero (hinj _ hxv (e1.trans eu))
    subst hvv
    exact ⟨rfl, hinjT t ht t' ht' (mul_left_cancel h)⟩
  have hcode : ∀ t < 64, ∀ w < 512, Nat.add (Nat.mul t 512) w < 32768 ∧
      elG (aG L aw) (teG L tw TEW) (Nat.add (Nat.mul t 512) w) =
        subG (aG L aw) w 9 * teG L tw TEW t := by
    intro t ht w hw
    change t * 512 + w < 32768 ∧ elG (aG L aw) (teG L tw TEW) (t * 512 + w) = _
    refine ⟨by omega, ?_⟩
    unfold elG
    have e1 : (t * 512 + w) % 512 = w := by omega
    have e2 : (t * 512 + w) / 512 = t := by omega
    rw [e1, e2]
  have helinj : ∀ e < 32768, ∀ f < 32768,
      elG (aG L aw) (teG L tw TEW) e = elG (aG L aw) (teG L tw TEW) f → e = f := by
    intro e he f hf h
    obtain ⟨h1, h2⟩ := hinjP _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) _
      (by omega) _ (by omega) h
    omega
  have hel0 : elG (aG L aw) (teG L tw TEW) 0 = 1 := by
    unfold elG
    rw [Nat.zero_mod, Nat.zero_div, subG_zero_mask, hte0, one_mul]
  have hmt0 : ∀ v < 512, mapV (mt MT 0) v = v := fun v hv =>
    subG_inj hI hC hinj (mapV_lt _ _) hv (by
      rw [← mat_apply hI hC (hmt 0 (by norm_num)) v, hte0, one_mul, inv_one, mul_one])
  have hmapV0 : ∀ t < 64, mapV (mt MT t) 0 = 0 := fun t ht =>
    hinj _ (mapV_lt _ _) (by rw [← mat_apply hI hC (hmt t ht) 0, subG_zero_mask, mul_one,
      mul_inv_cancel])
  have hmu0 : ∀ t < 64, mu MU 0 t = t ∧ mu MU t 0 = t := fun t ht =>
    ⟨hinjT _ (hmu 0 (by norm_num) t ht).1 t ht (by rw [(hmu 0 (by norm_num) t ht).2, hte0,
      one_mul]),
    hinjT _ (hmu t ht 0 (by norm_num)).1 t ht (by rw [(hmu t ht 0 (by norm_num)).2, hte0,
      mul_one])⟩
  have keyA : ∀ k < 9, ∀ v < 512, ∀ t < 64,
      aG L aw k * (subG (aG L aw) v 9 * teG L tw TEW t) * (aG L aw k)⁻¹ =
        subG (aG L aw) (v ^^^ (pw2 k ^^^ mapV (mt MT t) (pw2 k))) 9 * teG L tw TEW t := by
    intro k hk v hv t ht
    have hak : aG L aw k = subG (aG L aw) (pw2 k) 9 * teG L tw TEW 0 := by
      rw [pw2_eq, subG_two_pow, ite_eq_left hk, hte0, mul_one]
    rw [inv_eq_of_mul_eq_one_right (hI k hk), hak, hmulP _ _ 0 (by norm_num) t ht,
      (hmu0 t ht).1, hmt0 v hv, hmulP _ _ t ht 0 (by norm_num), (hmu0 t ht).2,
      Nat.xor_comm (pw2 k) v, Nat.xor_assoc]
  have keyT : ∀ g < 64, teG L tw TEW g * teG L tw TEW g = 1 → ∀ v, ∀ t < 64,
      teG L tw TEW g * (subG (aG L aw) v 9 * teG L tw TEW t) * (teG L tw TEW g)⁻¹ =
        subG (aG L aw) (mapV (mt MT g) v) 9 * teG L tw TEW (mu MU (mu MU g t) g) := by
    intro g hg hgg v t ht
    have hg1 : teG L tw TEW g = subG (aG L aw) 0 9 * teG L tw TEW g := by
      rw [subG_zero_mask, one_mul]
    have hmg := (hmu g hg t ht).1
    rw [inv_eq_of_mul_eq_one_right hgg, hg1, hmulP _ _ g hg t ht, hmulP _ _ _ hmg g hg,
      hmapV0 _ hmg, Nat.zero_xor, Nat.xor_zero]
  have hland : ∀ e, Nat.land e (nat_lit 511) = e % 512 := fun e =>
    Nat.and_two_pow_sub_one_eq_mod e 9
  have hsh : ∀ e, Nat.shiftRight e (nat_lit 9) = e / 512 := fun e => Nat.shiftRight_eq_div_pow e 9
  have himg9 : ∀ k < 9, ∀ e, imgE MU MT TG k e = Nat.add (Nat.mul (e / 512) 512)
      (Nat.xor (e % 512) (Nat.xor (pw2 k) (mapV (mt MT (e / 512)) (pw2 k)))) := by
    intro k hk e
    have hb : Nat.blt k (nat_lit 9) = true := blt_iff.2 hk
    unfold imgE
    simp only [strictN_eq]
    rw [hsh, hland, hb]
  have himgT : ∀ k, 9 ≤ k → ∀ e, imgE MU MT TG k e = Nat.add (Nat.mul
      (mu MU (mu MU (fget TG (k - 9) (nat_lit 7)) (e / 512)) (fget TG (k - 9) (nat_lit 7))) 512)
      (mapV (mt MT (fget TG (k - 9) (nat_lit 7))) (e % 512)) := by
    intro k hk e
    have hb : Nat.blt k (nat_lit 9) = false := Bool.eq_false_iff.2 fun h => by
      have : k < 9 := blt_iff.1 h
      omega
    unfold imgE
    simp only [strictN_eq]
    rw [hsh, hland, hb]
    rfl
  have hact : ∀ k < 13, ∀ e < 32768, imgE MU MT TG k e < 32768 ∧
      (aGensG L aw ++ tGensG L tw).getD k 1 * elG (aG L aw) (teG L tw TEW) e *
        ((aGensG L aw ++ tGensG L tw).getD k 1)⁻¹ = elG (aG L aw) (teG L tw TEW) (imgE MU MT TG k e) := by
    intro k hk e he
    have hv : e % 512 < 512 := Nat.mod_lt _ (by norm_num)
    have ht : e / 512 < 64 := by omega
    by_cases hk9 : k < 9
    · have hw : Nat.xor (e % 512) (Nat.xor (pw2 k) (mapV (mt MT (e / 512)) (pw2 k))) < 512 := by
        refine Nat.xor_lt_two_pow (n := 9) hv (Nat.xor_lt_two_pow ?_ (mapV_lt _ _))
        rw [pw2_eq]
        exact Nat.pow_lt_pow_right (by norm_num) hk9
      obtain ⟨hlt, hel⟩ := hcode (e / 512) ht _ hw
      rw [himg9 k hk9 e, hel, hgsA k hk9]
      refine ⟨hlt, ?_⟩
      unfold elG
      exact keyA k hk9 _ hv _ ht
    · have hj : k - 9 < 4 := by omega
      obtain ⟨hg64, hgte⟩ := hTGf (k - 9) hj
      have hmg := (hmu _ hg64 (e / 512) ht).1
      have hmgg := (hmu _ hmg _ hg64).1
      obtain ⟨hlt, hel⟩ := hcode _ hmgg _ (mapV_lt (mt MT (fget TG (k - 9) (nat_lit 7))) (e % 512))
      have hgk : (aGensG L aw ++ tGensG L tw).getD k 1 = teG L tw TEW (fget TG (k - 9) (nat_lit 7)) := by
        have := hgsT (k - 9) hj
        rw [Nat.sub_add_cancel (by omega)] at this
        rw [this, hgte]
      have hgg : teG L tw TEW (fget TG (k - 9) (nat_lit 7)) *
          teG L tw TEW (fget TG (k - 9) (nat_lit 7)) = 1 := by
        rw [hgte]
        exact hinvT (k - 9) hj
      rw [himgT k (by omega) e, hel, hgk]
      refine ⟨hlt, ?_⟩
      unfold elG
      exact keyT _ hg64 hgg _ _ ht
  have hgsq : ∀ k < 13, (aGensG L aw ++ tGensG L tw).getD k 1 *
      (aGensG L aw ++ tGensG L tw).getD k 1 = 1 := by
    intro k hk
    by_cases hk9 : k < 9
    · rw [hgsA k hk9]
      exact hI k hk9
    · have := hgsT (k - 9) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at this
      rw [this]
      exact hinvT (k - 9) (by omega)
  have helmul : ∀ e < 32768, ∀ f < 32768, ∃ d < 32768,
      elG (aG L aw) (teG L tw TEW) e * elG (aG L aw) (teG L tw TEW) f =
        elG (aG L aw) (teG L tw TEW) d := by
    intro e he f hf
    have ht : e / 512 < 64 := by omega
    have hs' : f / 512 < 64 := by omega
    obtain ⟨hlt, hel⟩ := hcode _ (hmu _ ht _ hs').1 _ (Nat.xor_lt_two_pow (n := 9)
      (Nat.mod_lt e (by norm_num)) (mapV_lt (mt MT (e / 512)) (f % 512)))
    refine ⟨_, hlt, ?_⟩
    rw [hel]
    unfold elG
    exact hmulP _ _ _ ht _ hs'
  have hgenEl : ∀ k < 13, ∃ d < 32768,
      (aGensG L aw ++ tGensG L tw).getD k 1 = elG (aG L aw) (teG L tw TEW) d := by
    intro k hk
    by_cases hk9 : k < 9
    · have hp : 2 ^ k < 512 := Nat.pow_lt_pow_right (by norm_num) hk9
      obtain ⟨hlt, hel⟩ := hcode 0 (by norm_num) _ hp
      refine ⟨_, hlt, ?_⟩
      rw [hel, hgsA k hk9, hte0, mul_one, subG_two_pow, ite_eq_left hk9]
    · have hj : k - 9 < 4 := by omega
      obtain ⟨hg64, hgte⟩ := hTGf (k - 9) hj
      obtain ⟨hlt, hel⟩ := hcode _ hg64 0 (by norm_num)
      refine ⟨_, hlt, ?_⟩
      have := hgsT (k - 9) hj
      rw [Nat.sub_add_cancel (by omega)] at this
      rw [hel, this, subG_zero_mask, one_mul, hgte]
  have hdecomp : ∀ x ∈ Subgroup.closure {g | g ∈ aGensG L aw ++ tGensG L tw},
      ∃ e < 32768, x = elG (aG L aw) (teG L tw TEW) e := by
    intro x hx
    induction hx using Subgroup.closure_induction_left with
    | one => exact ⟨0, by norm_num, hel0.symm⟩
    | mul_left x hx y _ ih =>
      obtain ⟨e, he, rfl⟩ := ih
      obtain ⟨k, hk, rfl⟩ := mem_getD hx
      rw [hgsl] at hk
      obtain ⟨d, hd, ed⟩ := hgenEl k hk
      obtain ⟨d', hd', ed'⟩ := helmul d hd e he
      exact ⟨d', hd', by rw [ed, ed']⟩
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨e, he, rfl⟩ := ih
      obtain ⟨k, hk, rfl⟩ := mem_getD hx
      rw [hgsl] at hk
      obtain ⟨d, hd, ed⟩ := hgenEl k hk
      obtain ⟨d', hd', ed'⟩ := helmul d hd e he
      rw [inv_eq_of_mul_eq_one_right (hgsq k hk)]
      exact ⟨d', hd', by rw [ed, ed']⟩
  have hinvE : ∀ e < 32768, elG (aG L aw) (teG L tw TEW) e * elG (aG L aw) (teG L tw TEW) e = 1 →
      elG (aG L aw) (teG L tw TEW) e ≠ 1 → isInvE MU MT e = true := by
    intro e he h2 h1
    have hv : e % 512 < 512 := Nat.mod_lt _ (by norm_num)
    have ht : e / 512 < 64 := by omega
    have hsq : elG (aG L aw) (teG L tw TEW) e * elG (aG L aw) (teG L tw TEW) e =
        subG (aG L aw) (e % 512 ^^^ mapV (mt MT (e / 512)) (e % 512)) 9 *
          teG L tw TEW (mu MU (e / 512) (e / 512)) := by
      unfold elG
      exact hmulP _ _ _ ht _ ht
    rw [hsq] at h2
    obtain ⟨hx0, hm0⟩ := hinjP _ (Nat.xor_lt_two_pow (n := 9) hv (mapV_lt _ _)) 0 (by norm_num)
      _ (hmu _ ht _ ht).1 0 (by norm_num) (by rw [h2, subG_zero_mask, hte0, one_mul])
    have he0 : e ≠ 0 := by
      rintro rfl
      exact h1 hel0
    unfold isInvE
    simp only [strictB_eq, andB_iff, notB_iff, beq_iff]
    rw [hsh, hland]
    exact ⟨beq_false he0, hm0, (eq_of_xor_eq_zero hx0).symm⟩
  have hc26' : ∀ w ∈ sRW, ∀ c ∈ w, c < 2 * (aGensG L aw ++ tGensG L tw).length :=
    fun w hw c hc' => by
      rw [hgsl]
      exact hc26 w hw c hc'
  have hR := rep_list hS sRW hc26'
  simp only [allN_iff, strictB_eq, andB_iff, notB_iff, beq_iff, Bool.eq_false_iff, Ne] at hrep
  have hrr : ∀ r < sRW.length,
      ((sRW.map (List.map decZ)).map (evalCodes (aGensG L aw ++ tGensG L tw))).getD r 1 =
        elG (aG L aw) (teG L tw TEW) (fget RD r (nat_lit 15)) := by
    intro r hr
    obtain ⟨-, hdec, -⟩ := hrep r hr
    have ht : fget RD r 15 / 512 < 64 := by
      have := fget_lt RD r 15
      omega
    refine rep_unique (hR r hr) ?_
    rw [hdec, hland, hsh]
    exact rep_pc (rep_subP hA _) (hTE _ ht)
  have hstep : ∀ e0, ∀ k < 13, ∀ e, e < 32768 →
      (∃ c ∈ Subgroup.closure {g | g ∈ aGensG L aw ++ tGensG L tw},
        elG (aG L aw) (teG L tw TEW) e = c * elG (aG L aw) (teG L tw TEW) e0 * c⁻¹) →
      imgE MU MT TG k e < 32768 ∧
        ∃ c ∈ Subgroup.closure {g | g ∈ aGensG L aw ++ tGensG L tw},
          elG (aG L aw) (teG L tw TEW) (imgE MU MT TG k e) =
            c * elG (aG L aw) (teG L tw TEW) e0 * c⁻¹ := by
    intro e0 k hk e he hP
    obtain ⟨hlt, hg⟩ := hact k hk e he
    obtain ⟨c, hc, hce⟩ := hP
    refine ⟨hlt, (aGensG L aw ++ tGensG L tw).getD k 1 * c, Subgroup.mul_mem _ (hgmem k) hc, ?_⟩
    rw [← hg, hce]
    group
  have hB : ∀ r, BInv (fun x => ∃ c ∈ Subgroup.closure {g | g ∈ aGensG L aw ++ tGensG L tw},
      elG (aG L aw) (teG L tw TEW) x = c * elG (aG L aw) (teG L tw TEW) (fget RD r (nat_lit 15)) *
        c⁻¹) (classE MU MT TG (fget RD r (nat_lit 15))) := fun r =>
    binv_classE (hstep _) (fget_lt _ _ _) ⟨1, Subgroup.one_mem _, by group⟩
  unfold sbarK at hsb
  rw [strictB_eq, andB_iff, andB_iff, beq_iff, allN_iff] at hsb
  obtain ⟨hIeq, hcnt, hcen⟩ := hsb
  refine ⟨fun u hu ho => ?_, fun r hr => ?_, fun p hp => ?_, fun g hg => ?_,
    fun x hx hcomm => ?_, fun r hr => ?_⟩
  ·
    obtain ⟨e, he, rfl⟩ := hdecomp u hu
    have h2 : elG (aG L aw) (teG L tw TEW) e * elG (aG L aw) (teG L tw TEW) e = 1 := by
      rw [← pow_two, ← ho, pow_orderOf_eq_one]
    have h1 : elG (aG L aw) (teG L tw TEW) e ≠ 1 := fun h => by
      rw [h, orderOf_one] at ho
      exact absurd ho (by norm_num)
    have hbit := testBit_invSet he (hinvE e he h2 h1)
    rw [hIeq] at hbit
    obtain ⟨r, hr, hb⟩ := testBit_union
      (fun r => doneSet (classE MU MT TG (fget RD r (nat_lit 15)))) _ hbit
    obtain ⟨-, c, hc, hce⟩ := (hB r).1 e (testBit_doneSet hb)
    refine ⟨((sRW.map (List.map decZ)).map (evalCodes (aGensG L aw ++ tGensG L tw))).getD r 1,
      ?_, c, hc, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by simpa using hr)]
      exact List.getElem_mem _
    · rw [hrr r hr]
      exact hce
  ·
    obtain ⟨i, hi, rfl⟩ := mem_getD hr
    rw [List.length_map, List.length_map] at hi
    obtain ⟨⟨hsq, hne⟩, -, -⟩ := hrep i hi
    have h2 := (rep_ext (rep_pc (hR i hi) (hR i hi)) rep_ID).1 hsq
    have h1 : ((sRW.map (List.map decZ)).map (evalCodes (aGensG L aw ++ tGensG L tw))).getD i 1 ≠
        1 := fun h => hne ((rep_ext (hR i hi) rep_ID).2 h)
    exact orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  ·
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    rw [List.length_zip] at hi
    have hiC : i < sCW.length := by
      have := lt_min_iff.1 hi
      simpa using this.1
    have hiR : i < sRW.length := by
      have := lt_min_iff.1 hi
      simpa using this.2
    rw [List.getElem_zip]
    obtain ⟨-, -, hcj⟩ := hrep i hiR
    have hCj := rep_gens hL sCW hc92 i hiC
    have hc1 : ((sCW.map (List.map decZ)).map (u62WG L))[i]'(by simpa using hiC) =
        ((sCW.map (List.map decZ)).map (u62WG L)).getD i 1 :=
      (List.getD_eq_getElem _ _ _).symm
    have hc2 : ((sRW.map (List.map decZ)).map (evalCodes (aGensG L aw ++ tGensG L tw)))[i]'(by
        simpa using hiR) =
        ((sRW.map (List.map decZ)).map (evalCodes (aGensG L aw ++ tGensG L tw))).getD i 1 :=
      (List.getD_eq_getElem _ _ _).symm
    dsimp only
    rw [hc1, hc2]
    unfold conjP at hcj
    rw [(rep_ext (rep_pc (rep_pc hCj (hR i hiR)) (rep_invP hCj)) (rep_subP hA _)).1 hcj]
    exact subG_mem _ 9 fun j _ => getD_mem_closure _ j
  ·
    obtain ⟨k, hk, rfl⟩ := mem_getD hg
    rw [hgsl] at hk
    have h := allN_iff.1 hcom k hk
    rw [strictB_eq, beq_iff] at h
    exact (rep_ext (rep_pc hj1 (hS k (by rw [hgsl]; exact hk)))
      (rep_pc (hS k (by rw [hgsl]; exact hk)) hj1)).1 h
  ·
    obtain ⟨e, he, rfl⟩ := hdecomp x hx
    have h := allBelow_spec hcen (by norm_num) e he
    rw [orB_iff, ble_iff, notB_iff] at h
    rcases h with h | h
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with rfl | rfl
      · exact Or.inl hel0
      · right
        have hsub1 : subG (aG L aw) 1 9 = aG L aw 0 := by
          have := subG_two_pow (aG L aw) 0 9
          rwa [pow_zero, ite_eq_left (by norm_num)] at this
        unfold elG
        rw [Nat.one_mod_eq_one.2 (by norm_num), Nat.div_eq_of_lt (by norm_num), hte0, mul_one,
          hsub1]
        exact (rep_unique hj1 (hA 0 (by norm_num))).symm
    · rw [Bool.eq_false_iff] at h
      refine (h (allN_iff.2 fun k hk => beq_iff.2 ?_)).elim
      obtain ⟨hlt, hg⟩ := hact k hk e he
      refine helinj _ hlt _ he ?_
      rw [← hg, ← hcomm _ (hgin k hk), mul_inv_cancel_right]
  ·
    obtain ⟨i, hi, rfl⟩ := mem_getD hr
    rw [List.length_map, List.length_map] at hi
    have hle := le_ncard_class helinj (hB i)
    rw [← hrr i hi] at hle
    have hfx : ∀ r < sRW.length, fixK (elt (evList (Nat.lor (evList LT aW)
        (Nat.shiftLeft (evList LT tW) 62370)) sRW) r) < 2 ^ 10 := by
      intro r hr
      rw [fixK_eq (hR r hr)]
      have h693 : {p : Fin 693 | ((sRW.map (List.map decZ)).map
          (evalCodes (aGensG L aw ++ tGensG L tw))).getD r 1 p = p}.ncard ≤ 693 :=
        calc _ ≤ (Set.univ : Set (Fin 693)).ncard :=
              Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
          _ = 693 := by rw [Set.ncard_univ, Nat.card_fin]
      exact Nat.lt_of_le_of_lt h693 (by norm_num)
    have hFX := sumN_get (w := 10) (f := fun r => fixK (elt (evList (Nat.lor (evList LT aW)
        (Nat.shiftLeft (evList LT tW) 62370)) sRW) r)) hfx hi
    rw [fixK_eq (hR i hi)] at hFX
    have h := hcnt i hi
    rw [strictB_eq, andB_iff, orB_iff, orB_iff, notB_iff, notB_iff, ble_iff, ble_iff] at h
    obtain ⟨h53, h21⟩ := h
    refine ⟨fun e53 => ?_, fun e21 => ?_⟩
    · rcases h53 with h | h
      · exact absurd (h.symm.trans (beq_iff.2 (hFX.trans e53))) Bool.false_ne_true
      · exact h.trans hle
    · rcases h21 with h | h
      · exact absurd (h.symm.trans (beq_iff.2 (hFX.trans e21))) Bool.false_ne_true
      · exact h.trans hle

theorem sound3010H {LT M FA RD CM : Nat} {L : List (Equiv.Perm (Fin 693))}
    {aw kw tw : List (List ℤ)} {aW kW tW TW TEW sRW sCW : List (List Nat)}
    (hL : LetsBind L LT) (haw : aw = aW.map (List.map decZ)) (hkw : kw = kW.map (List.map decZ))
    (htw : tw = tW.map (List.map decZ)) (hs : check3010S LT aW kW tW M TW = true)
    (hkl : kW.length = 3) (hy : check3010Y LT aW tW TEW sRW sCW M FA RD CM = true) :
    (∀ x ∈ Subgroup.closure {g | g ∈ tGensG L tw}, (∀ g ∈ tGensG L tw, x * g = g * x) ∨
        Nat.card {y : Subgroup.closure {g | g ∈ tGensG L tw} //
          (y : Equiv.Perm (Fin 693)) * x = x * y} ≤ 16) ∧
      Nat.card {x : Subgroup.closure {g | g ∈ tGensG L tw} //
        ∀ g ∈ tGensG L tw, (x : Equiv.Perm (Fin 693)) * g = g * x} ≤ 16 ∧
      (∀ x ∈ Subgroup.closure {g | g ∈ tGensG L tw}, x ≠ 1 →
        Nat.card {a : Subgroup.closure {g | g ∈ aGensG L aw} //
          (a : Equiv.Perm (Fin 693)) * x = x * a} ≤ 32) ∧
      (∀ x ∈ Subgroup.closure {g | g ∈ tGensG L tw}, x * x ≠ 1 →
        Nat.card {a : Subgroup.closure {g | g ∈ aGensG L aw} //
          (a : Equiv.Perm (Fin 693)) * x = x * a} ≤ 16) ∧
      ∀ b ∈ Subgroup.closure {g | g ∈ tGensG L tw}, ∀ c ∈ Subgroup.closure {g | g ∈ tGensG L tw},
        b ≠ c → b ≠ 1 → c ≠ 1 → b * b = 1 → c * c = 1 → b * c = c * b →
        Nat.card {a : Subgroup.closure {g | g ∈ aGensG L aw} //
          (a : Equiv.Perm (Fin 693)) * b = b * a ∧ (a : Equiv.Perm (Fin 693)) * c = c * a} ≤
          16 := by
  open Pk Snd in
  obtain ⟨h9, hc, hA, hI, hC, hinj, -, -, -⟩ := facts3010S hL haw hkw htw hs
  have hcA : ∀ w ∈ aW, ∀ c ∈ w, c < 92 := fun w hw =>
    hc w (List.mem_append_left _ (List.mem_append_left _ hw))
  obtain ⟨hlenA, -⟩ := rep_A hL haw h9 hcA
  unfold check3010Y at hy
  rw [andB_iff] at hy
  obtain ⟨hl, hw⟩ := hy
  simp only [andB_iff, beq_iff] at hl
  obtain ⟨-, h4, h64, -, hev, hc8, -, -⟩ := hl
  obtain ⟨MU, MT, TG, hMU, hMT, hTG, hw⟩ := withSbar_spec hw
  rw [andB_iff, andB_iff, andB_iff, andB_iff] at hw
  obtain ⟨hT, -, -, -, hth⟩ := hw
  obtain ⟨htlen, -, -, -, henum, hinjT, hte0, hmu, hmt, hTGf, -, -⟩ :=
    factsT0 hL haw hkw htw hs hkl h4 h64 hev hc8 hT hMU hMT hTG
  unfold thomK at hth
  rw [andB_iff, andB_iff, andB_iff, andB_iff, allN_iff, ble_iff, allN_iff, allN_iff, allN_iff] at hth
  obtain ⟨p1, p2, p3, p4, p5⟩ := hth
  have hgm : ∀ g < 4, (tGensG L tw).getD g 1 ∈ tGensG L tw := fun g hg => by
    rw [List.getD_eq_getElem _ _ (by rw [htlen]; exact hg)]
    exact List.getElem_mem _
  have hAenum : ∀ x ∈ Subgroup.closure {g | g ∈ aGensG L aw}, ∃ v < 512, x = subG (aG L aw) v 9 :=
    fun x hx => (mem_closure_sub hI hC hlenA (fun _ => rfl)).1 hx
  have hcommT : ∀ s < 64, (∀ g < 4, mu MU s (fget TG g (nat_lit 7)) =
      mu MU (fget TG g (nat_lit 7)) s) → ∀ g ∈ tGensG L tw, teG L tw TEW s * g = g * teG L tw TEW s := by
    intro s hs h g hg
    obtain ⟨j, hj, rfl⟩ := mem_getD hg
    rw [htlen] at hj
    obtain ⟨hj64, hjte⟩ := hTGf j hj
    have e := congrArg (teG L tw TEW) (h j hj)
    rw [(hmu s hs _ hj64).2, (hmu _ hj64 s hs).2, hjte] at e
    exact e
  have hcommI : ∀ s < 64, ∀ t < 64, teG L tw TEW s * teG L tw TEW t =
      teG L tw TEW t * teG L tw TEW s → mu MU s t = mu MU t s := fun s hs t ht h =>
    hinjT _ (hmu s hs t ht).1 _ (hmu t ht s hs).1 (by rw [(hmu s hs t ht).2, (hmu t ht s hs).2, h])
  have hfixq : ∀ s < 64, ∀ v < 512, subG (aG L aw) v 9 * teG L tw TEW s =
      teG L tw TEW s * subG (aG L aw) v 9 → mapV (mt MT s) v = v := fun s hs v hv h =>
    subG_inj hI hC hinj (mapV_lt _ _) hv (by
      rw [← mat_apply hI hC (hmt s hs) v, ← h, mul_inv_cancel_right])
  have hsq0 : ∀ s < 64, teG L tw TEW s * teG L tw TEW s = 1 → mu MU s s = 0 := fun s hs h =>
    hinjT _ (hmu s hs s hs).1 0 (by norm_num) (by rw [(hmu s hs s hs).2, h, hte0])
  refine ⟨fun x hx => ?_, ?_, fun x hx hx1 => ?_, fun x hx hx2 => ?_,
    fun b hb c hc' hbc hb1 hc1 hbb hcc hcomm => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := henum x hx
    have h := p1 s hs
    rw [orB_iff, ble_iff] at h
    rcases h with h | h
    · left
      unfold commGens at h
      rw [allN_iff] at h
      refine hcommT s hs fun g hg => ?_
      have := h g hg
      rw [strictB_eq, beq_iff] at this
      exact this
    · right
      refine le_trans (card_le_sumN (P := fun g => g * teG L tw TEW s = teG L tw TEW s * g)
        (Q := fun y => Nat.beq (mu MU y s) (mu MU s y)) henum ?_) h
      intro y hy _ hP
      exact beq_iff.2 (hcommI y hy s hs hP)
  · refine le_trans (card_le_sumN (P := fun x => ∀ g ∈ tGensG L tw, x * g = g * x)
      (Q := fun x => commGens MU TG x) henum ?_) p2
    intro x hx _ hP
    unfold commGens
    refine allN_iff.2 fun g hg => ?_
    rw [strictB_eq, beq_iff]
    obtain ⟨hg64, hgte⟩ := hTGf g hg
    refine hcommI x hx _ hg64 ?_
    rw [hgte]
    exact hP _ (hgm g hg)
  · obtain ⟨s, hs, rfl⟩ := henum x hx
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hx1 hte0
    have h := p3 s hs
    rw [orB_iff, beq_iff, ble_iff] at h
    rcases h with h | h
    · exact absurd h hs0
    · unfold fixV at h
      refine le_trans (card_le_sumBelow (hi := 8)
        (P := fun a => a * teG L tw TEW s = teG L tw TEW s * a)
        (Q := fun v => Nat.beq (mapV (mt MT s) v) v) (by norm_num) hAenum ?_) h
      intro v hv _ hP
      exact beq_iff.2 (hfixq s hs v hv hP)
  · obtain ⟨s, hs, rfl⟩ := henum x hx
    have hs0 : mu MU s s ≠ 0 := fun h0 => hx2 (by rw [← (hmu s hs s hs).2, h0, hte0])
    have h := p4 s hs
    rw [orB_iff, beq_iff, ble_iff] at h
    rcases h with h | h
    · exact absurd h hs0
    · unfold fixV at h
      refine le_trans (card_le_sumBelow (hi := 8)
        (P := fun a => a * teG L tw TEW s = teG L tw TEW s * a)
        (Q := fun v => Nat.beq (mapV (mt MT s) v) v) (by norm_num) hAenum ?_) h
      intro v hv _ hP
      exact beq_iff.2 (hfixq s hs v hv hP)
  · obtain ⟨sb, hsb, rfl⟩ := henum b hb
    obtain ⟨sc, hsc, rfl⟩ := henum c hc'
    have h := allN_iff.1 (p5 sb hsb) sc hsc
    simp only [orB_iff, notB_iff, beq_iff, ble_iff, Bool.eq_false_iff, Ne] at h
    rcases h with h | h | h | h | h | h | h
    · exact absurd (congrArg (teG L tw TEW) h) hbc
    · exact (hb1 (by rw [h, hte0])).elim
    · exact (hc1 (by rw [h, hte0])).elim
    · exact absurd (hsq0 sb hsb hbb) h
    · exact absurd (hsq0 sc hsc hcc) h
    · exact absurd (hcommI sb hsb sc hsc hcomm) h
    · unfold fixV2 at h
      refine le_trans (card_le_sumBelow (hi := 8)
        (P := fun a => a * teG L tw TEW sb = teG L tw TEW sb * a ∧
          a * teG L tw TEW sc = teG L tw TEW sc * a)
        (Q := fun v => CFSG.KLie.CT.andB (Nat.beq (mapV (mt MT sb) v) v) (Nat.beq (mapV (mt MT sc) v) v))
        (by norm_num) hAenum ?_) h
      intro v hv _ hP
      exact andB_iff.2 ⟨beq_iff.2 (hfixq sb hsb v hv hP.1), beq_iff.2 (hfixq sc hsc v hv hP.2)⟩

@[expose] noncomputable def check3010B (LT : Nat) (kW : List (List Nat)) (BT G1 G2 G3 : Nat) :
    Bool :=
  strictB (evList LT kW) fun K =>
    CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (List.length kW) (nat_lit 3))
        (allN (nat_lit 42) fun i => Nat.blt (fget BT i (nat_lit 10)) (nat_lit 693)))
      (CFSG.KLie.CT.andB (allN (nat_lit 42) fun i => allN (nat_lit 42) fun j =>
          CFSG.KLie.CT.orB (Nat.beq i j) (CFSG.KLie.CT.notB (Nat.beq (fget BT i (nat_lit 10)) (fget BT j (nat_lit 10)))))
        (allN (nat_lit 3) fun m => strictB (elt K m) fun k =>
          strictB (nIf(Nat.beq m (nat_lit 0), G1, nIf(Nat.beq m (nat_lit 1), G2, G3))) fun G =>
            allN (nat_lit 42) fun i => strictB (fget G i (nat_lit 6)) fun g =>
              CFSG.KLie.CT.andB (Nat.blt g (nat_lit 42))
                (Nat.beq (ap10 k (fget BT i (nat_lit 10))) (fget BT g (nat_lit 10)))))

section

open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

@[expose] def betaCheckG (L : List (Equiv.Perm (Fin 693))) (kw : List (List ℤ))
    (bt : Array ℕ) (g1 g2 g3 : Array ℕ) : Bool :=
  bt.size == 42 && allIn 0 42 (fun i => decide (bt[i]! < 693)) &&
    decide bt.toList.Nodup &&
    (List.zip ((kGensG L kw).map toTable) [g1, g2, g3]).all fun p =>
      allIn 0 42 fun i => ap p.1 bt[i]! == bt[p.2[i]!]!

end

@[expose] noncomputable def check3010Q (LT : Nat) (aW kW : List (List Nat)) (o1W o2W yW : List Nat) :
    Bool :=
  strictB (evList LT aW) fun A => strictB (evList LT kW) fun K =>
  strictB (evW LT o1W) fun o1 => strictB (evW LT o2W) fun o2 =>
  strictB (elt A (nat_lit 0)) fun j1 => strictB (evW A [nat_lit 2, nat_lit 8]) fun j2 =>
  strictB (evW (Nat.lor A (Nat.shiftLeft K (nat_lit 62370))) yW) fun y =>
    CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (List.length aW) (nat_lit 9))
          (CFSG.KLie.CT.andB (codesK (nat_lit 92) (aW ++ kW ++ [o1W, o2W]))
            (codesK (Nat.mul (nat_lit 2) (Nat.add (nat_lit 9) (List.length kW))) [yW])))
        (CFSG.KLie.CT.andB (Nat.beq (pc o1 (pc o1 o1)) ID693) (CFSG.KLie.CT.notB (Nat.beq o1 ID693))))
      (CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (pc o2 (pc o2 o2)) ID693) (CFSG.KLie.CT.notB (Nat.beq o2 ID693)))
        (CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (pc o1 j1) (pc j1 o1)) (Nat.beq (pc o2 j1) (pc j1 o2)))
          (CFSG.KLie.CT.andB (strictB (pc o1 o2) fun p => Nat.beq (pc p p) j1) (Nat.beq (pc y y) j2))))

theorem sound3010Q {LT : Nat} {L : List (Equiv.Perm (Fin 693))} {aw kw : List (List ℤ)}
    {o1w o2w yw : List ℤ} {aW kW : List (List Nat)} {o1W o2W yW : List Nat} (hL : LetsBind L LT)
    (haw : aw = aW.map (List.map decZ)) (hkw : kw = kW.map (List.map decZ))
    (ho1 : o1w = o1W.map decZ) (ho2 : o2w = o2W.map decZ) (hy : yw = yW.map decZ)
    (hk : check3010Q LT aW kW o1W o2W yW = true) :
    orderOf (u62WG L o1w) = 3 ∧ orderOf (u62WG L o2w) = 3 ∧
      u62WG L o1w * j1G L aw = j1G L aw * u62WG L o1w ∧
      u62WG L o2w * j1G L aw = j1G L aw * u62WG L o2w ∧
      (u62WG L o1w * u62WG L o2w) ^ 2 = j1G L aw ∧
      evalCodes (aGensG L aw ++ kGensG L kw) yw ^ 2 = j2G L aw := by
  open Pk Snd in
  unfold check3010Q at hk
  simp only [strictB_eq, andB_iff, beq_iff, codesK_iff, notB_iff, Bool.eq_false_iff, Ne] at hk
  obtain ⟨⟨⟨h9, hc, hcy⟩, ho1e, ho1n⟩, ⟨ho2e, ho2n⟩, ⟨hc1, hc2⟩, hp, hy2⟩ := hk
  have hcA : ∀ w ∈ aW, ∀ c ∈ w, c < 92 := fun w hw =>
    hc w (List.mem_append_left _ (List.mem_append_left _ hw))
  have hcAK : ∀ w ∈ aW ++ kW, ∀ c ∈ w, c < 92 := fun w hw => hc w (List.mem_append_left _ hw)
  obtain ⟨hlen, hA, hj1, hj2, -⟩ := rep_A hL haw h9 hcA
  have hLet : ∀ j < L.length, Rep (elt LT j) (L.getD j 1) := fun j hj => rep_letter hL (hL.1 ▸ hj)
  have hro : ∀ (ow : List ℤ) (oW : List ℕ), ow = oW.map decZ → oW ∈ aW ++ kW ++ [o1W, o2W] →
      Rep (evW LT oW) (u62WG L ow) := by
    intro ow oW he hm
    rw [he, u62WG, tab_eq]
    exact rep_evW hLet oW fun c hc' => by rw [hL.1]; exact hc oW hm c hc'
  have r1 := hro o1w o1W ho1 (by simp)
  have r2 := hro o2w o2W ho2 (by simp)
  have hS := cat_rep hL haw hkw h9 hcAK
  have hlenK : (aGensG L aw ++ kGensG L kw).length = 9 + kW.length := by
    rw [List.length_append, hlen, kGensG, hkw, List.length_map, List.length_map]
  have ry := rep_evW hS yW fun c hc' => by
    rw [hlenK]
    exact hcy yW (List.mem_singleton_self _) c hc'
  rw [← hy] at ry
  have h3 : ∀ {P : ℕ} {g : Equiv.Perm (Fin 693)}, Rep P g → pc P (pc P P) = ID693 →
      ¬ P = ID693 → orderOf g = 3 := by
    intro P g hg he hn
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_succ', pow_two]
      exact rep_unique (rep_pc hg (rep_pc hg hg)) (he ▸ rep_ID)
    · intro h1
      exact hn ((rep_ext hg rep_ID).2 h1)
  refine ⟨h3 r1 ho1e ho1n, h3 r2 ho2e ho2n, ?_, ?_, ?_, ?_⟩
  · exact (rep_ext (rep_pc r1 hj1) (rep_pc hj1 r1)).1 hc1
  · exact (rep_ext (rep_pc r2 hj1) (rep_pc hj1 r2)).1 hc2
  · rw [pow_two]
    exact (rep_ext (rep_pc (rep_pc r1 r2) (rep_pc r1 r2)) hj1).1 hp
  · rw [pow_two]
    exact (rep_ext (rep_pc ry ry) hj2).1 hy2

@[expose] noncomputable def bindsK (LT : Nat) (wN : List (List Nat)) (P : Nat → Nat) : Bool :=
  strictB (evList LT wN) fun E => allN (List.length wN) fun j => Nat.beq (P j) (elt E j)

theorem soundBinds {LT : Nat} {L : List (Equiv.Perm (Fin 693))} {ws : List (List ℤ)}
    {wN : List (List Nat)} {P : Nat → Nat} (hL : LetsBind L LT)
    (hws : ws = wN.map (List.map decZ)) (hc : ∀ w ∈ wN, ∀ c ∈ w, c < 92)
    (hk : bindsK LT wN P = true) :
    ∀ j < ws.length, CFSG.Monster.B.Co2.Rep 693 (CFSG.KS.Raw.unpack 693 10 (P j))
      ((ws.map (u62WG L)).getD j 1) := by
  open Pk Snd in
  intro j hj
  unfold bindsK at hk
  rw [strictB_eq, allN_iff] at hk
  have hLet : ∀ j < L.length, Rep (elt LT j) (L.getD j 1) :=
    fun j hj => rep_letter hL (hL.1 ▸ hj)
  have h92 : 2 * L.length = 92 := by rw [hL.1]
  have hjw : j < wN.length := by rw [hws, List.length_map] at hj; exact hj
  have hr := rep_list hLet wN (fun w hw c hc' => h92 ▸ hc w hw c hc') j hjw
  have e : ws.map (u62WG L) = (wN.map (List.map decZ)).map (evalCodes L) := by
    rw [hws]
    exact List.map_congr_left fun w _ => tab_eq _
  rw [e, beq_iff.1 (hk j hjw)]
  exact rep_co2 hr

theorem trK_sound {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} (hb : CFSG.KS.Raw.Binds n w PS kS nb BP S base)
    (hp : CFSG.KC.Enum.allN kS (fun j => CFSG.KC.Enum.permOK n w (CFSG.KS.mask w) (n * w) (PS j) (PSI j)) =
      true)
    (hl : CFSG.KS.Raw.LevelsOK n w PS PSI LR TR TRI kS nb BP) :
    ∀ i < nb, ∀ k < CFSG.KS.Raw.rcnt (LR i),
      CFSG.Monster.B.Co2.Rep n
          (CFSG.KS.Raw.unpack n w (TR (Nat.add (CFSG.KS.Raw.roff n (n * w) (LR i)) k)))
          (CFSG.Certificates.ChainArrays.levT n S base i k) ∧
        CFSG.Monster.B.Co2.Rep n
          (CFSG.KS.Raw.unpack n w (TRI (Nat.add (CFSG.KS.Raw.roff n (n * w) (LR i)) k)))
          (CFSG.Certificates.ChainArrays.levT n S base i k)⁻¹ := by
  intro i hi k hk
  have hbl := CFSG.KS.Raw.Orb.base_lt_of_levels hb hl
  obtain ⟨A, P⟩ := CFSG.KS.Raw.Orb.agree_levelK hb hp hbl (TR := TR) (TRI := TRI) hi (hl i hi)
  have hk' : k < (CFSG.Certificates.ChainArrays.lev n S base i).pts.size := by
    rw [← A.cnt]
    exact hk
  have hR := (A.tr k hk').1
  have e : CFSG.Certificates.ChainArrays.levT n S base i k =
      CFSG.Monster.B.Co2.permOfArr n
        (CFSG.KS.Raw.unpack n w (TR (CFSG.KS.Raw.roff n (n * w) (LR i) + k))) := by
    have hc : (∀ j < n, ((CFSG.Certificates.ChainArrays.lev n S base i).tr[k]!)[j]! < n) ∧
        ∀ j < n, ∀ l < n, ((CFSG.Certificates.ChainArrays.lev n S base i).tr[k]!)[j]! =
          ((CFSG.Certificates.ChainArrays.lev n S base i).tr[k]!)[l]! → j = l :=
      ⟨fun j hj => hR.lt hj, fun j hj l hl' hjl => by
        rw [hR.apply hj, hR.apply hl'] at hjl
        have := (CFSG.Monster.B.Co2.permOfArr n
          (CFSG.KS.Raw.unpack n w (TR (CFSG.KS.Raw.roff n (n * w) (LR i) + k)))).injective
          (Fin.ext hjl)
        simpa using this⟩
    ext x
    rw [CFSG.Certificates.ChainArrays.levT, CFSG.Monster.B.Co2.permOfArr, dite_eq_left hc]
    change ((CFSG.Certificates.ChainArrays.lev n S base i).tr[k]!)[(x : ℕ)]! = _
    exact hR x
  rw [e]
  exact ⟨CFSG.KS.Raw.Orb.rep_unpack (P k hk).1, CFSG.KS.Raw.Orb.rep_unpack (P k hk).2⟩

theorem sound3010C {LT M o0 o1 o2 : Nat} {L : List (Equiv.Perm (Fin 693))}
    {aw kw tw : List (List ℤ)} {aW kW tW TW : List (List Nat)} {TR TRI : Nat → Nat}
    {X : ℕ → ℕ → Equiv.Perm (Fin 693)} (hL : LetsBind L LT) (haw : aw = aW.map (List.map decZ))
    (hkw : kw = kW.map (List.map decZ)) (htw : tw = tW.map (List.map decZ))
    (hs : check3010S LT aW kW tW M TW = true)
    (hX : ∀ i < 3, ∀ k < [21, 16, 60].getD i 0,
      CFSG.Monster.B.Co2.Rep 693 (CFSG.KS.Raw.unpack 693 10 (TR (Nat.add ([o0, o1, o2].getD i 0) k)))
          (X i k) ∧
        CFSG.Monster.B.Co2.Rep 693
          (CFSG.KS.Raw.unpack 693 10 (TRI (Nat.add ([o0, o1, o2].getD i 0) k))) (X i k)⁻¹)
    (hmem : ∀ i < 3, ∀ k < [21, 16, 60].getD i 0, X i k ∈ Subgroup.closure {g | g ∈ kGensG L kw})
    (henum : ∀ g ∈ Subgroup.closure {g | g ∈ kGensG L kw},
      ∃ a < 21, ∃ b < 16, ∃ c < 60, X 0 a * X 1 b * X 2 c = g)
    (hid : X 0 0 = 1 ∧ X 1 0 = 1 ∧ X 2 0 = 1)
    (hk : centK (evList LT aW) TR TRI o0 o1 o2 = true) :
    (∀ k ∈ Subgroup.closure {g | g ∈ kGensG L kw}, (∀ a ∈ aGensG L aw, k * a = a * k) → k = 1) ∧
      ∀ k ∈ Subgroup.closure {g | g ∈ kGensG L kw}, k * j3G L aw = j3G L aw * k →
        ∀ a ∈ Subgroup.closure {g | g ∈ aGensG L aw}, (a * k) ^ 2 ≠ j3G L aw := by
  open Pk Snd in
  obtain ⟨h9, hc, hA, hI, hC, hinj, hconjP, hkey, -⟩ := facts3010S hL haw hkw htw hs
  have hcA : ∀ w ∈ aW, ∀ c ∈ w, c < 92 := fun w hw =>
    hc w (List.mem_append_left _ (List.mem_append_left _ hw))
  obtain ⟨hlen, -, -, -, hj3⟩ := rep_A hL haw h9 hcA
  have hklen : (kGensG L kw).length = kW.length := by
    rw [kGensG, hkw, List.length_map, List.length_map]
  have hkc : ∀ k < (kGensG L kw).length, ∀ v, (kGensG L kw).getD k 1 * subG (aG L aw) v 9 *
      ((kGensG L kw).getD k 1)⁻¹ = subG (aG L aw) (mapM M k v) 9 := by
    intro k hk' v
    have := hconjP k (by rw [List.length_append]; rw [hklen] at hk'; omega) v
    rwa [List.getD_append _ _ _ _ hk'] at this
  have hN : ∀ g ∈ Subgroup.closure {g | g ∈ kGensG L kw}, ∀ x < 512, ∃ y < 512,
      g * subG (aG L aw) x 9 * g⁻¹ = subG (aG L aw) y 9 := fun g hg => norm_closure hkc hg
  have e18 : subG (aG L aw) 18 9 = aG L aw 1 * (aG L aw 4 * 1) := by
    rw [show (18 : ℕ) = 2 ^ 1 ^^^ 2 ^ 4 from rfl, ← subG_mul hI hC _ _ 9 le_rfl, subG_two_pow,
      subG_two_pow, ite_eq_left (by norm_num), ite_eq_left (by norm_num), mul_one]
  have e3 : j3G L aw = subG (aG L aw) 19 9 := by
    rw [show (19 : ℕ) = 2 ^ 0 ^^^ 18 from rfl, ← subG_mul hI hC _ _ 9 le_rfl, e18, subG_two_pow,
      ite_eq_left (by norm_num)]
    exact rep_unique hj3 (rep_pc (hA 0 (by norm_num))
      (rep_pc (hA 1 (by norm_num)) (rep_pc (hA 4 (by norm_num)) rep_ID)))
  have hM0 : ∀ i < 3, ∀ k < [21, 16, 60].getD i 0, MatRep (aG L aw)
      (matX (evList LT aW) (AK (evList LT aW)) (TR (Nat.add ([o0, o1, o2].getD i 0) k))
        (TRI (Nat.add ([o0, o1, o2].getD i 0) k))) (X i k) := fun i hi k hk =>
    matX_rep hA hI hC hkey (ap10_of_co2 (hX i hi k hk).1) (ap10_of_co2 (hX i hi k hk).2)
      (hN _ (hmem i hi k hk))
  have hmt : ∀ i < 3, ∀ x < [21, 16, 60].getD i 0, MatRep (aG L aw)
      (mt (matsT (evList LT aW) (AK (evList LT aW)) TR TRI ([o0, o1, o2].getD i 0)
        ([21, 16, 60].getD i 0)) x) (X i x) := by
    intro i hi x hx
    have hf : ∀ k < [21, 16, 60].getD i 0,
        matT (evList LT aW) (AK (evList LT aW)) TR TRI ([o0, o1, o2].getD i 0) k < 2 ^ 81 :=
      fun k hk => (hM0 i hi k hk).1
    unfold mt matsT
    rw [sumN_get hf hx]
    exact hM0 i hi x hx
  have hA0 := hmt 0 (by norm_num)
  have hA1 := hmt 1 (by norm_num)
  have hA2 := hmt 2 (by norm_num)
  change ∀ x < 21, MatRep (aG L aw)
    (mt (matsT (evList LT aW) (AK (evList LT aW)) TR TRI o0 21) x) (X 0 x) at hA0
  change ∀ x < 16, MatRep (aG L aw)
    (mt (matsT (evList LT aW) (AK (evList LT aW)) TR TRI o1 16) x) (X 1 x) at hA1
  change ∀ x < 60, MatRep (aG L aw)
    (mt (matsT (evList LT aW) (AK (evList LT aW)) TR TRI o2 60) x) (X 2 x) at hA2
  unfold centK at hk
  simp only [strictB_eq, andB_iff, orB_iff, notB_iff, beq_iff, allN_iff, Bool.eq_false_iff,
    Ne] at hk
  have hM : ∀ x < 21, ∀ y < 16, ∀ z < 60, MatRep (aG L aw)
      (mcomp (mcomp (mt (matsT (evList LT aW) (AK (evList LT aW)) TR TRI o0 21) x)
        (mt (matsT (evList LT aW) (AK (evList LT aW)) TR TRI o1 16) y))
        (mt (matsT (evList LT aW) (AK (evList LT aW)) TR TRI o2 60) z))
      (X 0 x * X 1 y * X 2 z) :=
    fun x hx y hy z hz => mat_mul hI hC (mat_mul hI hC (hA0 x hx) (hA1 y hy)) (hA2 z hz)
  have hcen : ∀ k ∈ Subgroup.closure {g | g ∈ kGensG L kw},
      (∀ i < 9, k * aG L aw i = aG L aw i * k) → k = 1 := by
    intro k hkK hcomm
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := henum k hkK
    have e := mat_unique hI hC hinj (hM x hx y hy z hz) (mat_id_of_comm hcomm)
    obtain ⟨h1, -⟩ := hk x hx y hy z hz
    rcases h1 with h1 | ⟨rfl, rfl, rfl⟩
    · exact absurd e h1
    · rw [hid.1, hid.2.1, hid.2.2, one_mul, one_mul]
  refine ⟨fun k hkK hcomm => hcen k hkK fun i hi => ?_, fun k hkK hkj a ha hsq => ?_⟩
  · refine hcomm _ ?_
    have : i < (aGensG L aw).length := by rw [hlen]; exact hi
    change (aGensG L aw).getD i 1 ∈ aGensG L aw
    rw [List.getD_eq_getElem _ _ this]
    exact List.getElem_mem this
  · obtain ⟨u, hu, rfl⟩ := (mem_closure_sub hI hC hlen (fun _ => rfl)).1 ha
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := henum k hkK
    set k := X 0 x * X 1 y * X 2 z with hkdef
    have hMk := hM x hx y hy z hz
    set Mk := mcomp (mcomp (mt (matsT (evList LT aW) (AK (evList LT aW)) TR TRI o0 21) x)
        (mt (matsT (evList LT aW) (AK (evList LT aW)) TR TRI o1 16) y))
        (mt (matsT (evList LT aW) (AK (evList LT aW)) TR TRI o2 60) z)
    have hka := mat_apply hI hC hMk u
    have hkk : k * k =
        subG (aG L aw) (mapV Mk u) 9 * subG (aG L aw) u 9 * subG (aG L aw) 19 9 := by
      have e1 : k * k = (k * subG (aG L aw) u 9 * k⁻¹)⁻¹ * (subG (aG L aw) u 9)⁻¹ *
          (subG (aG L aw) u 9 * k) ^ 2 := by
        rw [pow_two]
        group
      rw [e1, hsq, e3, hka, inv_eq_of_mul_eq_one_right (subG_sq hI hC _),
        inv_eq_of_mul_eq_one_right (subG_sq hI hC u)]
    have hk1 : k * k = 1 := by
      refine hcen _ (Subgroup.mul_mem _ hkK hkK) fun i hi => ?_
      have ha : aG L aw i = subG (aG L aw) (2 ^ i) 9 := by
        rw [subG_two_pow, ite_eq_left hi]
      rw [hkk, ha, subG_mul hI hC _ _ 9 le_rfl, subG_mul hI hC _ _ 9 le_rfl, subG_comm hI hC]
    have hMM : mcomp Mk Mk = mId := by
      have h := mat_mul hI hC hMk hMk
      rw [hk1] at h
      exact mat_unique hI hC hinj h mat_id
    have hM19 : mapV Mk 19 = 19 := by
      refine subG_inj hI hC hinj (mapV_lt _ _) (by norm_num) ?_
      rw [← mat_apply hI hC hMk, ← e3, hkj, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨-, h2⟩ := hk x hx y hy z hz
    rcases h2 with h2 | h2 | h2
    · exact h2 hM19
    · exact h2 hMM
    · apply h2
      have e : u ^^^ mapV Mk u = 19 := by
        refine subG_inj hI hC hinj (Nat.xor_lt_two_pow (n := 9) hu (mapV_lt _ _)) (by norm_num) ?_
        rw [← subG_mul hI hC _ _ 9 le_rfl, ← hka, ← e3, ← hsq]
        have e2 : (subG (aG L aw) u 9 * k) ^ 2 =
            subG (aG L aw) u 9 * (k * subG (aG L aw) u 9 * k⁻¹) * (k * k) := by
          rw [pow_two]
          group
        rw [e2, hk1, mul_one]
      rw [← e]
      exact inImg_complete hu

theorem sound3010B {LT BT G1 G2 G3 : Nat} {L : List (Equiv.Perm (Fin 693))} {kw : List (List ℤ)}
    {kW : List (List Nat)} {bt g1 g2 g3 : Array ℕ} (hL : LetsBind L LT)
    (hkw : kw = kW.map (List.map decZ)) (hb : CFSG.KC.S23.bindA BT 10 42 bt = true)
    (h1 : CFSG.KC.S23.bindA G1 6 42 g1 = true) (h2 : CFSG.KC.S23.bindA G2 6 42 g2 = true)
    (h3 : CFSG.KC.S23.bindA G3 6 42 g3 = true)
    (hc : ∀ w ∈ kW, ∀ c ∈ w, c < 92) (hk : check3010B LT kW BT G1 G2 G3 = true) :
    betaCheckG L kw bt g1 g2 g3 = true := by
  open Pk Snd in
  unfold check3010B at hk
  rw [strictB_eq, andB_iff, andB_iff, andB_iff, beq_iff, allN_iff, allN_iff, allN_iff] at hk
  obtain ⟨⟨hl3, hlt⟩, hdist, hact⟩ := hk
  have hLet : ∀ j < L.length, Rep (elt LT j) (L.getD j 1) :=
    fun j hj => rep_letter hL (hL.1 ▸ hj)
  have h92 : 2 * L.length = 92 := by rw [hL.1]
  have hK := rep_list hLet kW (fun w hw c hc' => h92 ▸ hc w hw c hc')
  have hKG : kGensG L kw = (kW.map (List.map decZ)).map (evalCodes L) := by
    rw [kGensG, hkw]
    exact List.map_congr_left fun w _ => tab_eq _
  rw [← hKG] at hK
  have hlen : (kGensG L kw).length = 3 := by rw [hKG, List.length_map, List.length_map, hl3]
  obtain ⟨hbs, hbt⟩ := bindA_get hb
  have hgen : ∀ m < 3, ∀ (G : ℕ) (g : Array ℕ), CFSG.KC.S23.bindA G 6 42 g = true →
      (∀ i < 42, fget G i 6 < 42 ∧ ap10 (elt (evList LT kW) m) (fget BT i 10) =
        fget BT (fget G i 6) 10) →
      CFSG.Sporadic.Th.Native.allIn 0 42 (fun i =>
        CFSG.Sporadic.Th.Native.ap (toTable ((kGensG L kw).getD m 1)) bt[i]! == bt[g[i]!]!) =
        true := by
    intro m hm G g hg hG
    obtain ⟨-, hgg⟩ := bindA_get hg
    refine allIn_iff.2 fun i hi => ?_
    obtain ⟨hGi, hap⟩ := hG i hi
    have hr := hK m (by rw [hl3]; exact hm)
    have hx : fget BT i 10 < 693 := blt_iff.1 (hlt i hi)
    rw [beq_iff_eq, hbt i hi, hgg i hi, hbt _ hGi, ← hap, CFSG.Sporadic.Th.Native.ap, toTable,
      getElem!_pos _ _ (by simpa using hx), Array.getElem_ofFn,
      UInt32.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans (Fin.isLt _) (by norm_num)),
      ap10_eq hr hx]
  have hA : ∀ m < 3, ∀ i < 42, fget ([G1, G2, G3].getD m 0) i 6 < 42 ∧
      ap10 (elt (evList LT kW) m) (fget BT i 10) =
        fget BT (fget ([G1, G2, G3].getD m 0) i 6) 10 := by
    intro m hm i hi
    have h := hact m hm
    rw [strictB_eq, strictB_eq, allN_iff] at h
    have h' := h i hi
    rw [strictB_eq, andB_iff, blt_iff, beq_iff] at h'
    have e : nIf(Nat.beq m 0, G1, nIf(Nat.beq m 1, G2, G3)) = [G1, G2, G3].getD m 0 := by
      rcases m with _ | _ | _ | m
      · rfl
      · rfl
      · rfl
      · omega
    rw [e] at h'
    exact h'
  unfold betaCheckG
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨hbs, allIn_iff.2 fun i hi => ?_⟩, ?_⟩, ?_⟩
  · rw [hbt i hi]
    exact decide_eq_true (blt_iff.1 (hlt i hi))
  · rw [List.nodup_iff_injective_get]
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Array.length_toList, hbs] at hi hj
    simp only [List.get_eq_getElem, Array.getElem_toList] at hij
    rw [← getElem!_pos bt i (by omega), ← getElem!_pos bt j (by omega), hbt i hi, hbt j hj] at hij
    have := allN_iff.1 (hdist i hi) j hj
    rw [orB_iff, beq_iff, notB_iff, Bool.eq_false_iff, Ne, beq_iff] at this
    rcases this with h | h
    · exact Fin.ext h
    · exact absurd hij h
  · rw [list3 1 _ hlen]
    simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨hgen 0 (by norm_num) G1 g1 h1 (hA 0 (by norm_num)),
      hgen 1 (by norm_num) G2 g2 h2 (hA 1 (by norm_num)),
      hgen 2 (by norm_num) G3 g3 h3 (hA 2 (by norm_num))⟩

end CFSG.KC.U6

end
