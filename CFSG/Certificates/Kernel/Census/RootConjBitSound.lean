module

public import Certificates.Data.Kernel.Census.PackedRootBit
public import CFSG.Certificates.Kernel.Census.RootConjSound
import CFSG.Certificates.Kernel.Census.SoundProof
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Pair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Roots
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjW

public section

namespace CFSG.KC.Census

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

variable {n w : Nat}

private noncomputable def toP (n w : Nat) (p : Nat) : Equiv.Perm (Fin n) :=
  permOfArr n (unpackP n w p)

private theorem ppcA_cons (x : Nat) (l : List Nat) (m : Nat) :
    ppcA n w (x :: l) m =
      if m % 2 = 1 then pc n w x (ppcA n w l (m / 2)) else ppcA n w l (m / 2) := by
  simp only [ppcA]
  cases hb : Nat.beq (m % 2) 1
  · have hm0 : m % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · exact h
      · rw [h] at hb; cases hb
    rw [hm0]; rfl
  · have hm1 : m % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · rw [h] at hb; cases hb
      · exact h
    rw [hm1]; rfl

private theorem ppcOK_cons {x : Nat} {l : List Nat} {r : Nat} {rs : List Nat} {c : List Nat}
    {cs : List (List Nat)} {b : Nat × Nat} {bs : List (Nat × Nat)}
    (h : ppcOK n w (x :: l) (r :: rs) (c :: cs) (b :: bs) = true) :
    pvalid n w x = true ∧ Nat.beq (pc n w x x) (ppcA n w l r) = true ∧
      Nat.beq c.length l.length = true ∧
      (l.zip c).all (fun yc => Nat.beq (pc n w yc.1 x) (pc n w x (ppcA n w l yc.2))) =
        true ∧
      Nat.blt b.2 n = true ∧ b.1.testBit b.2 = true ∧
      (!(b.1.testBit (at' w x b.2))) = true ∧
      (l.all (fun y => (List.range n).all fun p =>
        !(b.1.testBit p) || b.1.testBit (at' w y p))) = true ∧
      ppcOK n w l rs cs bs = true := by
  simp only [ppcOK, Bool.and_eq_true] at h
  exact ⟨by tauto, by tauto, by tauto, by tauto, by tauto, by tauto, by tauto, by tauto,
    by tauto⟩

private theorem pvalid_pid_of_ppcOK {xs : List Nat} {rs : List Nat} {cjs : List (List Nat)}
    {bs : List (Nat × Nat)} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hcan : xs.all (canon1 n w) = true) (h : ppcOK n w xs rs cjs bs = true)
    (hne : xs ≠ []) : pvalid n w (pid n w) = true := by
  induction xs generalizing rs cjs bs with
  | nil => exact absurd rfl hne
  | cons x l ih =>
    rw [List.all_cons, Bool.and_eq_true] at hcan
    obtain ⟨hcx, hcl⟩ := hcan
    cases rs with
    | nil => simp [ppcOK] at h
    | cons r rs' =>
      cases cjs with
      | nil => simp [ppcOK] at h
      | cons c cs' =>
        cases bs with
        | nil => simp [ppcOK] at h
        | cons b bs' =>
          obtain ⟨hpv, hsq, -, -, -, -, -, -, hrest⟩ := ppcOK_cons h
          cases l with
          | nil =>
            have hpc : pc n w x x = pid n w := by
              simpa [ppcA] using Nat.eq_of_beq_eq_true hsq
            rw [← hpc]
            exact pvalid_pc hn hw hcx hpv hcx hpv
          | cons y l' => exact ih hcl hrest (by simp)

private theorem unpackP_pid_of_ppcOK {xs : List Nat} {rs : List Nat} {cjs : List (List Nat)}
    {bs : List (Nat × Nat)} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hcan : xs.all (canon1 n w) = true) (h : ppcOK n w xs rs cjs bs = true)
    (hne : xs ≠ []) : unpackP n w (pid n w) = idA n :=
  (SP.pid_good hw (pvalid_pid_of_ppcOK hn hw hcan h hne)).1

private theorem unpackP_ppcA {l : List Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hcan : l.all (canon1 n w) = true) (hpid : unpackP n w (pid n w) = idA n) (m : Nat) :
    unpackP n w (ppcA n w l m) = pcA n (l.map (unpackP n w)) m := by
  induction l generalizing m with
  | nil => simpa [ppcA, pcA] using hpid
  | cons x l ih =>
    rw [List.all_cons, Bool.and_eq_true] at hcan
    obtain ⟨hcx, hcl⟩ := hcan
    rw [ppcA_cons, List.map_cons]
    simp only [pcA]
    by_cases hm : m % 2 = 1 <;> simp only [hm, if_true, if_false]
    · rw [unpackP_pc hn hw hcx, ih hcl (m / 2)]
    · exact ih hcl (m / 2)

private theorem toP_pc {p q : Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hcp : canon1 n w p = true) (hcq : canon1 n w q = true)
    (hpv : pvalid n w p = true) (hqv : pvalid n w q = true) :
    toP n w (pc n w p q) = toP n w p * toP n w q := by
  have hpv' : validA n (unpackP n w p) = true := by rwa [SP.validA_unpack hw hcp]
  have hqv' : validA n (unpackP n w q) = true := by rwa [SP.validA_unpack hw hcq]
  have hpq : validA n (unpackP n w (pc n w p q)) = true := by
    rw [SP.validA_unpack hw (SP.canon_pc hn hw)]
    exact pvalid_pc hn hw hcp hpv hcq hqv
  refine Rep.unique (t := unpackP n w (pc n w p q)) ?_ ?_
  · exact (rep_permOfArr (n := n) (by simpa [CFSG.RankThree.Native.validA] using hpq)).1
  · rw [unpackP_pc hn hw hcp]
    exact rep_compA
      (rep_permOfArr (n := n) (by simpa [CFSG.RankThree.Native.validA] using hpv')).1
      (rep_permOfArr (n := n) (by simpa [CFSG.RankThree.Native.validA] using hqv')).1

private theorem pcOK_of_ppcOK {xs : List Nat} {rs : List Nat} {cjs : List (List Nat)}
    {bs : List (Nat × Nat)} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hcan : xs.all (canon1 n w) = true)
    (hpv : ∀ x ∈ xs, pvalid n w x = true)
    (hpid : unpackP n w (pid n w) = idA n)
    (h : ppcOK n w xs rs cjs bs = true) :
    pcOK n (xs.map (unpackP n w)) rs cjs bs = true := by
  induction xs generalizing rs cjs bs with
  | nil => cases rs <;> cases cjs <;> cases bs <;> rfl
  | cons x l ih =>
    rw [List.all_cons, Bool.and_eq_true] at hcan
    obtain ⟨hcx, hcl⟩ := hcan
    cases rs with
    | nil => simp [ppcOK] at h
    | cons r rs' =>
      cases cjs with
      | nil => simp [ppcOK] at h
      | cons c cs' =>
        cases bs with
        | nil => simp [ppcOK] at h
        | cons b bs' =>
          obtain ⟨hpvx, hsq, hlen0, hzip0, hlt0, hb20, hbx0, hlall0, hrest⟩ := ppcOK_cons h
          have hrec := ih hcl (fun y hy => hpv y (List.mem_cons_of_mem x hy)) hrest
          have hpc_eq : pc n w x x = ppcA n w l r := Nat.eq_of_beq_eq_true hsq
          have hv : validA n (unpackP n w x) = true := by
            rw [SP.validA_unpack hw hcx]; exact hpvx
          have h2 : eqA n (compA n (unpackP n w x) (unpackP n w x))
              (pcA n (l.map (unpackP n w)) r) = true := by
            have hcp : canon1 n w (pc n w x x) = true := SP.canon_pc hn hw
            have hcpp : canon1 n w (ppcA n w l r) = true := by
              rw [← hpc_eq]; exact hcp
            have heq : eqA n (unpackP n w (pc n w x x))
                (unpackP n w (ppcA n w l r)) = true := by
              rw [SP.eqA_unpack hcp hcpp, hsq]
            rw [unpackP_pc hn hw hcx, unpackP_ppcA hn hw hcl hpid r] at heq
            exact heq
          have hlen : (c.length == (l.map (unpackP n w)).length) = true := by
            rw [List.length_map]; simpa using hlen0
          have hzip : ((l.map (unpackP n w)).zip c).all (fun yc =>
              eqA n (compA n yc.1 (unpackP n w x))
                (compA n (unpackP n w x) (pcA n (l.map (unpackP n w)) yc.2))) = true := by
            rw [List.all_eq_true]
            intro yc hyc
            rw [List.mem_iff_getElem] at hyc
            obtain ⟨i, hi, hget⟩ := hyc
            rw [List.length_zip, List.length_map] at hi
            have hi1 : i < l.length := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
            have hi2 : i < c.length := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
            have hq := List.all_eq_true.1 hzip0
              (l.get ⟨i, hi1⟩, c.get ⟨i, hi2⟩) (mem_zip_of_lt hi1 hi2)
            rw [← hget, List.getElem_zip, List.getElem_map]
            have hli : l.get ⟨i, hi1⟩ ∈ l := List.get_mem l ⟨i, hi1⟩
            have hcy : canon1 n w (l.get ⟨i, hi1⟩) = true := List.all_eq_true.1 hcl _ hli
            have heq : eqA n (unpackP n w (pc n w (l.get ⟨i, hi1⟩) x))
                (unpackP n w (pc n w x (ppcA n w l (c.get ⟨i, hi2⟩)))) = true := by
              rw [SP.eqA_unpack (SP.canon_pc hn hw) (SP.canon_pc hn hw), hq]
            rw [unpackP_pc hn hw hcy, unpackP_pc hn hw hcx,
              unpackP_ppcA hn hw hcl hpid (c.get ⟨i, hi2⟩)] at heq
            exact heq
          have hlt : decide (b.2 < n) = true := by
            rw [decide_eq_true_eq]; exact Nat.blt_eq.mp hlt0
          have hbx : (!(b.1.testBit (unpackP n w x)[b.2]!)) = true := by
            rw [SP.unpackP_get_canon hcx b.2]; exact hbx0
          have hlall : ((l.map (unpackP n w)).all fun y => (List.range n).all fun p =>
              !(b.1.testBit p) || b.1.testBit y[p]!) = true := by
            rw [List.all_eq_true]
            intro y' hy'
            obtain ⟨y, hyl, rfl⟩ := List.mem_map.1 hy'
            have hy := List.all_eq_true.1 hlall0 y hyl
            rw [List.all_eq_true]
            intro pp hp
            have hp' := List.all_eq_true.1 hy pp hp
            rw [SP.unpackP_get_canon (List.all_eq_true.1 hcl y hyl) pp]
            exact hp'
          simp only [List.map_cons, pcOK, hv, h2, hlen, hzip, hlt, hb20, hbx, hlall, hrec,
            Bool.and_true, Bool.true_and]

private theorem pvalid_of_ppcOK {xs : List Nat} {rs : List Nat} {cjs : List (List Nat)}
    {bs : List (Nat × Nat)} (h : ppcOK n w xs rs cjs bs = true) :
    ∀ x ∈ xs, pvalid n w x = true := by
  induction xs generalizing rs cjs bs with
  | nil => simp
  | cons x l ih =>
    intro y hy
    cases rs with
    | nil => simp [ppcOK] at h
    | cons r rs' =>
      cases cjs with
      | nil => simp [ppcOK] at h
      | cons c cs' =>
        cases bs with
        | nil => simp [ppcOK] at h
        | cons b bs' =>
          obtain ⟨hpvx, -, -, -, -, -, -, -, hrest⟩ := ppcOK_cons h
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hpvx
          · exact ih hrest y hy

private theorem permOfArr_idA : permOfArr n (idA n) = 1 := by
  unfold permOfArr
  rw [dif_pos ⟨fun i hi => by rw [idA_get hi]; exact hi, fun i hi j hj hij => by
    rw [idA_get hi, idA_get hj] at hij; exact hij⟩]
  apply Equiv.ext
  intro i
  apply Fin.ext
  simp only [Equiv.ofBijective_apply, Equiv.refl_apply]
  rw [idA_get i.2]
  rfl

private theorem toP_pid_of_unpack (hpid : unpackP n w (pid n w) = idA n) :
    toP n w (pid n w) = 1 := by
  unfold toP
  rw [hpid, permOfArr_idA]

private theorem toP_sq_one {p : Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hcp : canon1 n w p = true) (hpv : pvalid n w p = true)
    (hpc : pc n w p p = pid n w) (hpid : unpackP n w (pid n w) = idA n) :
    toP n w p ^ 2 = 1 := by
  rw [pow_two, ← toP_pc hn hw hcp hcp hpv hpv, hpc, toP_pid_of_unpack hpid]

private theorem toP_ne_one {p : Nat} (hw : n ≤ 2 ^ w)
    (hcp : canon1 n w p = true) (hpv : pvalid n w p = true)
    (hpid : unpackP n w (pid n w) = idA n) (hcpid : canon1 n w (pid n w) = true)
    (hvalp : pvalid n w (pid n w) = true) (hne : p ≠ pid n w) : toP n w p ≠ 1 := by
  intro h1
  have h1' : toP n w p = toP n w (pid n w) := by rw [h1, toP_pid_of_unpack hpid]
  have hvalx : validA n (unpackP n w p) = true := by rwa [SP.validA_unpack hw hcp]
  have hvalp' : validA n (unpackP n w (pid n w)) = true := by rwa [SP.validA_unpack hw hcpid]
  have hrep_x : Rep n (unpackP n w p) (toP n w p) :=
    (rep_permOfArr (n := n) (by simpa [CFSG.RankThree.Native.validA] using hvalx)).1
  have hrep_p : Rep n (unpackP n w (pid n w)) (toP n w (pid n w)) :=
    (rep_permOfArr (n := n) (by simpa [CFSG.RankThree.Native.validA] using hvalp')).1
  have harray : unpackP n w p = unpackP n w (pid n w) := by
    apply Array.ext
    · rw [SP.unpackP_size, SP.unpackP_size]
    · intro i hi _
      have hi' : i < n := by simpa [SP.unpackP_size] using hi
      have hcong := congrArg (fun g : Equiv.Perm (Fin n) => ((g ⟨i, hi'⟩ : Fin n) : Nat)) h1'
      rw [← hrep_x ⟨i, hi'⟩, ← hrep_p ⟨i, hi'⟩] at hcong
      rw [getElem!_pos (unpackP n w p) i (by rwa [SP.unpackP_size]),
        getElem!_pos (unpackP n w (pid n w)) i (by rwa [SP.unpackP_size])] at hcong
      exact hcong
  exact hne (SP.unpackP_inj hcp hcpid harray)

private theorem toP_fixP {p : Nat} (hw : n ≤ 2 ^ w)
    (hcp : canon1 n w p = true) (hpv : pvalid n w p = true) :
    fixP (toP n w p) = pfix n w p := by
  have hvalx : validA n (unpackP n w p) = true := by rwa [SP.validA_unpack hw hcp]
  have hrep : Rep n (unpackP n w p) (toP n w p) :=
    (rep_permOfArr (n := n) (by simpa [CFSG.RankThree.Native.validA] using hvalx)).1
  rw [← fixA_eq hrep]
  simp only [fixA, pfix, List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro a _
  rw [SP.unpackP_get_canon hcp a]
  rfl

private theorem rep_toP {p : Nat} (hw : n ≤ 2 ^ w) (hcp : canon1 n w p = true)
    (hpv : pvalid n w p = true) : Rep n (unpackP n w p) (toP n w p) := by
  have hvalx : validA n (unpackP n w p) = true := by rwa [SP.validA_unpack hw hcp]
  exact rep_of_validA hvalx

private theorem at'_eq_toP {x p : Nat} (hw : n ≤ 2 ^ w) (hcx : canon1 n w x = true)
    (hvx : pvalid n w x = true) (hp : p < n) : at' w x p = (toP n w x ⟨p, hp⟩ : Nat) := by
  rw [← SP.unpackP_get_canon hcx p]
  exact (rep_toP hw hcx hvx).apply hp

private theorem at'_eq_toP_inv {q x p : Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hcq : canon1 n w q = true) (hcx : canon1 n w x = true) (hvx : pvalid n w x = true)
    (hpid : unpackP n w (pid n w) = idA n) (hqx : pc n w q x = pid n w) (hp : p < n) :
    at' w q p = ((toP n w x)⁻¹ ⟨p, hp⟩ : Nat) := by
  let i : Fin n := (toP n w x)⁻¹ ⟨p, hp⟩
  have hxi : toP n w x i = ⟨p, hp⟩ := by simp [i]
  have hi : (i : Nat) < n := i.2
  have h1 : at' w (pc n w q x) (i : Nat) = at' w q p := by
    rw [← SP.unpackP_get_canon (SP.canon_pc (n := n) (w := w) hn hw) (i : Nat),
      unpackP_pc (n := n) (w := w) hn hw hcq, compA_get (n := n) hi,
      SP.unpackP_get_canon hcx (i : Nat)]
    have hxi' : at' w x (i : Nat) = p := by
      rw [at'_eq_toP hw hcx hvx hi]
      exact congrArg Fin.val hxi
    rw [hxi', SP.unpackP_get_canon hcq p]
  have h2 : at' w (pc n w q x) (i : Nat) = (i : Nat) := by
    have e1 : at' w (pc n w q x) (i : Nat) = (unpackP n w (pc n w q x))[(i : Nat)]! :=
      ((SP.unpackP_get (pc n w q x) (i : Nat)).trans (if_pos hi)).symm
    rw [e1, hqx, hpid, idA_get hi]
  exact h1.symm.trans h2

private theorem toP_inj {p q : Nat} (hw : n ≤ 2 ^ w) (hcp : canon1 n w p = true)
    (hvp : pvalid n w p = true) (hcq : canon1 n w q = true) (hvq : pvalid n w q = true)
    (h : toP n w p = toP n w q) : p = q := by
  have hrep_p : Rep n (unpackP n w p) (toP n w p) := rep_toP hw hcp hvp
  have hrep_q : Rep n (unpackP n w q) (toP n w q) := rep_toP hw hcq hvq
  have harray : unpackP n w p = unpackP n w q := by
    apply Array.ext
    · rw [SP.unpackP_size, SP.unpackP_size]
    · intro i hi _
      have hi' : i < n := by simpa [SP.unpackP_size] using hi
      have hcong := congrArg (fun g : Equiv.Perm (Fin n) => ((g ⟨i, hi'⟩ : Fin n) : Nat)) h
      rw [← hrep_p ⟨i, hi'⟩, ← hrep_q ⟨i, hi'⟩] at hcong
      rw [getElem!_pos (unpackP n w p) i (by rwa [SP.unpackP_size]),
        getElem!_pos (unpackP n w q) i (by rwa [SP.unpackP_size])] at hcong
      exact hcong
  exact SP.unpackP_inj hcp hcq harray

private theorem rep_pc {p q : Nat} {g h : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (hw : n ≤ 2 ^ w) (hcp : canon1 n w p = true) (hp : Rep n (unpackP n w p) g)
    (hq : Rep n (unpackP n w q) h) : Rep n (unpackP n w (pc n w p q)) (g * h) := by
  rw [unpackP_pc (n := n) (w := w) hn hw hcp]
  exact rep_compA hp hq

private theorem rep_ppow {p : Nat} {g : Equiv.Perm (Fin n)} (G : SP.Good n w)
    (hcp : canon1 n w p = true) (hp : Rep n (unpackP n w p) g) (m : Nat) :
    Rep n (unpackP n w (ppow n w p m)) (g ^ m) := by
  rw [(SP.ppow_eq G hcp m).1]
  exact rep_powA hp m

private theorem ppcAt_cons (x : Nat) (l : List Nat) (m p : Nat) :
    ppcAt w (x :: l) m p =
      if m % 2 = 1 then at' w x (ppcAt w l (m / 2) p) else ppcAt w l (m / 2) p := by
  simp only [ppcAt]
  cases hb : Nat.beq (m % 2) 1
  · have hm0 : m % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · exact h
      · rw [h] at hb; cases hb
    rw [hm0]; rfl
  · have hm1 : m % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · rw [h] at hb; cases hb
      · exact h
    rw [hm1]; rfl

private theorem canon1_ppcA {l : List Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hcpid : canon1 n w (pid n w) = true) (m : Nat) : canon1 n w (ppcA n w l m) = true := by
  induction l generalizing m with
  | nil => simpa [ppcA] using hcpid
  | cons x l ih =>
    rw [ppcA_cons]
    by_cases hm : m % 2 = 1 <;> simp only [hm, if_true, if_false]
    · exact SP.canon_pc hn hw
    · exact ih (m / 2)

private theorem pvalid_ppcA {l : List Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hcl : l.all (canon1 n w) = true) (hpv : ∀ x ∈ l, pvalid n w x = true)
    (hcpid : canon1 n w (pid n w) = true) (hvpid : pvalid n w (pid n w) = true) (m : Nat) :
    pvalid n w (ppcA n w l m) = true := by
  induction l generalizing m with
  | nil => simpa [ppcA] using hvpid
  | cons x l ih =>
    rw [List.all_cons, Bool.and_eq_true] at hcl
    obtain ⟨hcx, hcl⟩ := hcl
    rw [ppcA_cons]
    by_cases hm : m % 2 = 1 <;> simp only [hm, if_true, if_false]
    · exact pvalid_pc hn hw hcx (hpv x List.mem_cons_self)
        (canon1_ppcA hn hw hcpid (m / 2))
        (ih hcl (fun y hy => hpv y (List.mem_cons_of_mem x hy)) (m / 2))
    · exact ih hcl (fun y hy => hpv y (List.mem_cons_of_mem x hy)) (m / 2)

private theorem toP_ppcA {l : List Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hcl : l.all (canon1 n w) = true) (hpv : ∀ x ∈ l, pvalid n w x = true)
    (hpid : unpackP n w (pid n w) = idA n) (hcpid : canon1 n w (pid n w) = true)
    (hvpid : pvalid n w (pid n w) = true) (m : Nat) :
    toP n w (ppcA n w l m) = pcG (l.map (toP n w)) m := by
  induction l generalizing m with
  | nil =>
    have h : ppcA n w [] m = pid n w := rfl
    rw [h, toP_pid_of_unpack hpid]
    rfl
  | cons x l ih =>
    rw [List.all_cons, Bool.and_eq_true] at hcl
    obtain ⟨hcx, hcl⟩ := hcl
    rw [ppcA_cons, List.map_cons, pcG]
    by_cases hm : m % 2 = 1 <;> simp only [hm, if_true, if_false, one_mul]
    · rw [toP_pc hn hw hcx (canon1_ppcA hn hw hcpid (m / 2))
        (hpv x List.mem_cons_self)
        (pvalid_ppcA hn hw hcl (fun y hy => hpv y (List.mem_cons_of_mem x hy)) hcpid hvpid
          (m / 2))]
      rw [ih hcl (fun y hy => hpv y (List.mem_cons_of_mem x hy)) (m / 2)]
    · exact ih hcl (fun y hy => hpv y (List.mem_cons_of_mem x hy)) (m / 2)

private theorem ppcAt_eq {l : List Nat} (hw : n ≤ 2 ^ w) (hcl : l.all (canon1 n w) = true)
    (hpv : ∀ x ∈ l, pvalid n w x = true) (m : Nat) {p : Nat} (hp : p < n) :
    ppcAt w l m p = (pcG (l.map (toP n w)) m ⟨p, hp⟩ : Nat) := by
  induction l generalizing m with
  | nil =>
    rw [List.map_nil, pcG]
    rfl
  | cons x l ih =>
    rw [List.all_cons, Bool.and_eq_true] at hcl
    obtain ⟨hcx, hcl⟩ := hcl
    rw [ppcAt_cons, List.map_cons, pcG]
    by_cases hm : m % 2 = 1 <;> simp only [hm, if_true, if_false, one_mul]
    · rw [ih hcl (fun y hy => hpv y (List.mem_cons_of_mem x hy)) (m / 2),
        Equiv.Perm.mul_apply]
      exact at'_eq_toP hw hcx (hpv x List.mem_cons_self) _
    · exact ih hcl (fun y hy => hpv y (List.mem_cons_of_mem x hy)) (m / 2)

private theorem good_of_check {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonR n w r = true)
    (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true) :
    SP.Good n w ∧ pvalid n w (pid n w) = true := by
  have hcanR := hc
  simp only [canonR, Bool.and_eq_true] at hcanR
  have hcanxs : r.xs.all (canon1 n w) = true := by tauto
  have h' := h
  simp only [prootConjOKB, Bool.and_eq_true] at h'
  have hppcOK : ppcOK n w r.xs r.rs r.cjs r.bs = true := by tauto
  have hblt : Nat.blt k r.xs.length = true := by tauto
  have hk : k < r.xs.length := Nat.blt_eq.mp hblt
  have hne : r.xs ≠ [] := by
    intro hnil; rw [hnil] at hk; simp at hk
  have hpvpid : pvalid n w (pid n w) = true := pvalid_pid_of_ppcOK hn hw hcanxs hppcOK hne
  have hpid := unpackP_pid_of_ppcOK hn hw hcanxs hppcOK hne
  have hcpid : canon1 n w (pid n w) = true := (SP.pid_good hw hpvpid).2
  exact ⟨⟨hn, hw, hpid, hcpid⟩, hpvpid⟩

private theorem x_facts {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonR n w r = true)
    (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true) :
    canon1 n w r.x = true ∧ pvalid n w r.x = true ∧ toP n w r.x ^ 2 = 1 ∧ toP n w r.x ≠ 1 := by
  have hcanR := hc
  simp only [canonR, Bool.and_eq_true] at hcanR
  have hcx : canon1 n w r.x = true := by tauto
  have hcanxs : r.xs.all (canon1 n w) = true := by tauto
  have h' := h
  simp only [prootConjOKB, Bool.and_eq_true] at h'
  have hpvx : pvalid n w r.x = true := by tauto
  have hinvol : pinvol n w r.x = true := by tauto
  have hppcOK : ppcOK n w r.xs r.rs r.cjs r.bs = true := by tauto
  have hblt : Nat.blt k r.xs.length = true := by tauto
  have hk : k < r.xs.length := Nat.blt_eq.mp hblt
  have hne : r.xs ≠ [] := by
    intro hnil; rw [hnil] at hk; simp at hk
  have hpid := unpackP_pid_of_ppcOK hn hw hcanxs hppcOK hne
  have hpvpid : pvalid n w (pid n w) = true := pvalid_pid_of_ppcOK hn hw hcanxs hppcOK hne
  have hcpid : canon1 n w (pid n w) = true := (SP.pid_good hw hpvpid).2
  have hinvol' := hinvol
  simp only [pinvol, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at hinvol'
  have hpc_xx : pc n w r.x r.x = pid n w := hinvol'.1
  have hne_pid : r.x ≠ pid n w := beq_eq_false_iff_ne.mp hinvol'.2
  exact ⟨hcx, hpvx, toP_sq_one hn hw hcx hpvx hpc_xx hpid,
    toP_ne_one hw hcx hpvx hpid hcpid hpvpid hne_pid⟩

private theorem walk_mem_of_headD_beq {l : List Nat} {d m : Nat}
    (h : Nat.beq (l.headD d) m = true) (hm : m < d) : m ∈ l := by
  cases l with
  | nil => rw [List.headD_nil, Nat.beq_eq] at h; omega
  | cons a l => rw [List.headD_cons, Nat.beq_eq] at h; rw [← h]; exact List.mem_cons_self

private theorem pinvRest_spec {xs : List Nat} : ∀ {m : Nat} {im wt r : List Nat},
    pinvRest n w xs m im wt = some r → ∀ i < wt.length, m + i < 2 ^ xs.length →
      m + i ∈ im ∨ m + i = 0 ∨
        (wt[i]! < n ∧ ppcAt w xs (m + i) (ppcAt w xs (m + i) wt[i]!) ≠ wt[i]!) := by
  intro m im wt
  induction wt generalizing m im with
  | nil =>
    intro r h i hi hm
    exact absurd hi (by simp)
  | cons x wt ih =>
    intro r h i hi hm
    simp only [pinvRest, Bool.cond_eq_ite] at h
    split_ifs at h with h1 h2
    · rcases i with _ | i
      · left
        rw [Nat.add_zero]
        exact walk_mem_of_headD_beq h1 (by simpa using hm)
      · have hrec := ih h i (by simpa using hi) (by omega)
        rw [show m + 1 + i = m + (i + 1) by omega] at hrec
        rcases hrec with h3 | h3
        · exact Or.inl (List.mem_of_mem_tail h3)
        · exact Or.inr h3
    · have h2' : m = 0 ∨ (x < n ∧ Nat.beq (ppcAt w xs m (ppcAt w xs m x)) x = false) := by
        simpa using h2
      rcases i with _ | i
      · rcases h2' with h2' | h2'
        · exact Or.inr (Or.inl (by omega))
        · obtain ⟨hlt, hbeq⟩ := h2'
          refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · simpa using hlt
          · simp only [List.getElem!_cons_zero, Nat.add_zero]
            intro heq
            rw [heq, Nat.beq_refl] at hbeq
            exact Bool.noConfusion hbeq
      · have hrec := ih h i (by simpa using hi) (by omega)
        rw [show m + 1 + i = m + (i + 1) by omega] at hrec
        simpa using hrec

private theorem exists_mask_of_invol {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonR n w r = true)
    (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true) :
    ∀ b ∈ (closure {a | a ∈ r.xs.map (fun x => toP n w x)} : Subgroup (Equiv.Perm (Fin n))),
      b ^ 2 = 1 → b ≠ 1 → ∃ m ∈ r.im, pcG (r.xs.map (fun x => toP n w x)) m = b := by
  have hcanR := hc
  simp only [canonR, Bool.and_eq_true] at hcanR
  have hcanxs : r.xs.all (canon1 n w) = true := by tauto
  have h' := h
  simp only [prootConjOKB, Bool.and_eq_true] at h'
  have hppcOK : ppcOK n w r.xs r.rs r.cjs r.bs = true := by tauto
  have hblt : Nat.blt k r.xs.length = true := by tauto
  have hlenwt : Nat.beq r.wt.flatten.length (2 ^ r.xs.length) = true := by tauto
  have hpinvres : (pinvRest n w r.xs 0 r.im r.wt.flatten == some ([] : List Nat)) = true := by
    tauto
  have hpv_all := pvalid_of_ppcOK hppcOK
  have hk : k < r.xs.length := Nat.blt_eq.mp hblt
  have hne : r.xs ≠ [] := by intro hnil; rw [hnil] at hk; simp at hk
  have hpid := unpackP_pid_of_ppcOK hn hw hcanxs hppcOK hne
  have hpcOK := pcOK_of_ppcOK hn hw hcanxs hpv_all hpid hppcOK
  obtain ⟨-, hrel, hsep⟩ := pc_of_pcOK hpcOK
  have hmap : (r.xs.map (unpackP n w)).map (permOfArr n) = r.xs.map (fun x => toP n w x) := by
    rw [List.map_map]; rfl
  have hrel' : PcRel (r.xs.map (fun x => toP n w x)) := by rwa [hmap] at hrel
  intro b hb hb2 hb1
  obtain ⟨m, hm_lt, hm_eq⟩ := exists_pcG_of_pcRel hrel' b hb
  rw [List.length_map] at hm_lt
  have hlenwt' : r.wt.flatten.length = 2 ^ r.xs.length := by
    simpa only [Nat.beq_eq] using hlenwt
  have hmlen : m < r.wt.flatten.length := by rw [hlenwt']; exact hm_lt
  have hpinv : pinvRest n w r.xs 0 r.im r.wt.flatten = some ([] : List Nat) :=
    beq_iff_eq.mp hpinvres
  have hspec := pinvRest_spec (m := 0) (im := r.im) (wt := r.wt.flatten) (r := [])
    hpinv m hmlen (by omega)
  refine ⟨m, ?_, hm_eq⟩
  rcases hspec with him | hzero | hcase
  · simpa using him
  · exfalso
    have hm0 : m = 0 := by omega
    exact hb1 (by rw [← hm_eq, hm0, pcG_zero])
  · exfalso
    obtain ⟨hq_lt, hq_ne⟩ := hcase
    have hq_ne' :
        ppcAt w r.xs m (ppcAt w r.xs m (r.wt.flatten[m]!)) ≠ r.wt.flatten[m]! := by
      simpa using hq_ne
    have hpat : ppcAt w r.xs m (ppcAt w r.xs m (r.wt.flatten[m]!)) =
        (b (b ⟨r.wt.flatten[m]!, hq_lt⟩) : Nat) := by
      rw [ppcAt_eq hw hcanxs hpv_all m hq_lt]
      rw [hm_eq]
      rw [ppcAt_eq hw hcanxs hpv_all m (b ⟨r.wt.flatten[m]!, hq_lt⟩).2]
      rw [hm_eq]
    have hbb : b (b ⟨r.wt.flatten[m]!, hq_lt⟩) = ⟨r.wt.flatten[m]!, hq_lt⟩ := by
      have h1 := congrArg (fun g : Equiv.Perm (Fin n) => g ⟨r.wt.flatten[m]!, hq_lt⟩) hb2
      rw [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h1
      exact h1
    exact hq_ne' (hpat.trans (congrArg Fin.val hbb))

private noncomputable def uPermF (n w : Nat) (r : RootConjP) : Nat → Nat → Equiv.Perm (Fin n)
  | 0, _ => 1
  | f + 1, j =>
    if (r.e j).1 = 0 then toP n w (ppcA n w r.xs (r.e j).2.1)
    else toP n w r.xs[(r.e j).2.2.1]! * uPermF n w r f (r.e j).2.1 *
      (toP n w r.xs[(r.e j).2.2.1]!)⁻¹

private noncomputable def uPerm (n w : Nat) (r : RootConjP) (j : Nat) : Equiv.Perm (Fin n) :=
  uPermF n w r ((r.e j).2.2.2 + 1) j

private theorem uPerm_of_rep {r : RootConjP} {j : Nat} (h0 : (r.e j).1 = 0) :
    uPerm n w r j = toP n w (ppcA n w r.xs (r.e j).2.1) := by
  unfold uPerm
  rw [uPermF]
  rw [if_pos h0]

private theorem uPerm_of_conj {r : RootConjP} {j : Nat} (h0 : (r.e j).1 ≠ 0)
    (hd : (r.e j).2.2.2 = (r.e (r.e j).2.1).2.2.2 + 1) :
    uPerm n w r j = toP n w r.xs[(r.e j).2.2.1]! * uPerm n w r (r.e j).2.1 *
      (toP n w r.xs[(r.e j).2.2.1]!)⁻¹ := by
  unfold uPerm
  rw [hd, uPermF]
  rw [if_neg h0]

private theorem puAt_of_rep {r : RootConjP} {j p : Nat} (h0 : (r.e j).1 = 0) :
    puAt w r j p = ppcAt w r.xs (r.e j).2.1 p := by
  simp only [puAt, puAtF, Nat.rec_add_one, h0, Nat.beq_refl, cond_true]

private theorem puAt_of_conj {r : RootConjP} {j p : Nat} (h0 : (r.e j).1 ≠ 0)
    (hd : (r.e j).2.2.2 = (r.e (r.e j).2.1).2.2.2 + 1) :
    puAt w r j p = at' w r.xs[(r.e j).2.2.1]!
      (puAt w r (r.e j).2.1 (at' w r.xi[(r.e j).2.2.1]! p)) := by
  simp only [puAt, puAtF, hd, Nat.rec_add_one]
  have hb : Nat.beq (r.e j).1 0 = false := by
    rw [Bool.eq_false_iff]
    exact fun hh => h0 (Nat.eq_of_beq_eq_true hh)
  rw [hb, cond_false]

private theorem pentryOKB_spec {inXP : Nat → Bool} {bmode : Nat} {skip : List Nat}
    {pG : Array (Array Nat)} {k : Nat} {r : RootConjP} {j : Nat}
    (h : pentryOKB n w inXP bmode skip pG k r j = true) :
    ((r.e j).1 = 0 ∧ (r.e j).2.2.2 = 0 ∧ pinvol n w (ppcA n w r.xs (r.e j).2.1) = true ∧
        (r.e j).2.2.1 < r.cands.size ∧
        pleafOKB n w inXP bmode skip r.x r.ga r.gi pG (Nat.land (Nat.shiftRight (r.e j).2.1 k) 1)
          (ppcA n w r.xs (r.e j).2.1) r.cands[(r.e j).2.2.1]! = true) ∨
      ((r.e j).1 ≠ 0 ∧ (r.e j).2.1 < usize r.ukc ∧
        (r.e j).2.2.2 = (r.e (r.e j).2.1).2.2.2 + 1 ∧ (r.e j).2.2.1 < r.xs.length) := by
  simp only [pentryOKB] at h
  by_cases hk : (r.e j).1 = 0
  · have hb : Nat.beq (r.e j).1 0 = true := by rw [hk]; exact Nat.beq_refl 0
    rw [hb, cond_true] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact Or.inl ⟨hk, Nat.eq_of_beq_eq_true h1, h2, Nat.blt_eq.mp h3, h4⟩
  · have hb : Nat.beq (r.e j).1 0 = false := by
      rw [Bool.eq_false_iff]
      exact fun hh => hk (Nat.eq_of_beq_eq_true hh)
    rw [hb, cond_false] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact Or.inr ⟨hk, Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, Nat.blt_eq.mp h3⟩

private theorem uPerm_spec {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonR n w r = true)
    (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true) :
    ∀ j < usize r.ukc,
      uPerm n w r j ∈ (closure {a | a ∈ r.xs.map (fun x => toP n w x)} :
        Subgroup (Equiv.Perm (Fin n))) ∧
      uPerm n w r j ^ 2 = 1 ∧ uPerm n w r j ≠ 1 ∧
      ∀ p (hp : p < n), puAt w r j p = (uPerm n w r j ⟨p, hp⟩ : Nat) := by
  have hcan := hc
  simp only [canonR, Bool.and_eq_true] at hcan
  have hcanxs : r.xs.all (canon1 n w) = true := by tauto
  have hcanxi : r.xi.all (canon1 n w) = true := by tauto
  have h' := h
  simp only [prootConjOKB, Bool.and_eq_true] at h'
  have hlen_xi : Nat.beq r.xi.length r.xs.length = true := by tauto
  have hzip : (r.xs.zip r.xi).all (fun gi => Nat.beq (pc n w gi.2 gi.1) (pid n w)) = true := by
    tauto
  have hppcOK : ppcOK n w r.xs r.rs r.cjs r.bs = true := by tauto
  have hentries : (List.range (usize r.ukc)).all
      (pentryOKB n w inXP bmode skip (r.perfs.map (pperfGens n w r.ga)) k r) = true := by
    tauto
  obtain ⟨-, hpvpid⟩ := good_of_check hn hw hc h
  have hpid : unpackP n w (pid n w) = idA n := (SP.pid_good hw hpvpid).1
  have hcpid : canon1 n w (pid n w) = true := (SP.pid_good hw hpvpid).2
  have hpv_all : ∀ x ∈ r.xs, pvalid n w x = true := pvalid_of_ppcOK hppcOK
  let T : Subgroup (Equiv.Perm (Fin n)) := closure {a | a ∈ r.xs.map (fun x => toP n w x)}
  have hTdef : T = closure {a | a ∈ r.xs.map (fun x => toP n w x)} := rfl
  have key : ∀ d, ∀ j, j < usize r.ukc → (r.e j).2.2.2 = d →
      uPerm n w r j ∈ T ∧ uPerm n w r j ^ 2 = 1 ∧ uPerm n w r j ≠ 1 ∧
        ∀ p (hp : p < n), puAt w r j p = (uPerm n w r j ⟨p, hp⟩ : Nat) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro j hj hdj
      have hent := List.all_eq_true.1 hentries j (List.mem_range.mpr hj)
      rcases pentryOKB_spec hent with
        ⟨h0, -, hpinv, hcands, hleaf⟩ | ⟨h0, ha, hd, hb⟩
      ·
        have hca : canon1 n w (ppcA n w r.xs (r.e j).2.1) = true :=
          canon1_ppcA hn hw hcpid _
        have hpva : pvalid n w (ppcA n w r.xs (r.e j).2.1) = true :=
          pvalid_ppcA hn hw hcanxs hpv_all hcpid hpvpid _
        have hpinv' := hpinv
        simp only [pinvol, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at hpinv'
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [uPerm_of_rep h0,
            toP_ppcA hn hw hcanxs hpv_all hpid hcpid hpvpid (r.e j).2.1]
          exact pcG_mem _ _
        · rw [uPerm_of_rep h0]
          exact toP_sq_one hn hw hca hpva hpinv'.1 hpid
        · rw [uPerm_of_rep h0]
          exact toP_ne_one hw hca hpva hpid hcpid hpvpid
            (beq_eq_false_iff_ne.mp hpinv'.2)
        · intro p hp
          rw [uPerm_of_rep h0,
            toP_ppcA hn hw hcanxs hpv_all hpid hcpid hpvpid (r.e j).2.1,
            puAt_of_rep h0]
          exact ppcAt_eq hw hcanxs hpv_all _ hp
      ·
        have hb_xi : (r.e j).2.2.1 < r.xi.length := by
          rw [Nat.eq_of_beq_eq_true hlen_xi]; exact hb
        have hb_mem_xs : r.xs[(r.e j).2.2.1]! ∈ r.xs := by
          rw [getElem!_pos r.xs _ hb]; exact List.getElem_mem hb
        have hb_mem_xi : r.xi[(r.e j).2.2.1]! ∈ r.xi := by
          rw [getElem!_pos r.xi _ hb_xi]; exact List.getElem_mem hb_xi
        have hcxb : canon1 n w r.xs[(r.e j).2.2.1]! = true :=
          List.all_eq_true.1 hcanxs _ hb_mem_xs
        have hpvb : pvalid n w r.xs[(r.e j).2.2.1]! = true := hpv_all _ hb_mem_xs
        have hcxib : canon1 n w r.xi[(r.e j).2.2.1]! = true :=
          List.all_eq_true.1 hcanxi _ hb_mem_xi
        have hmem_zip : (r.xs[(r.e j).2.2.1], r.xi[(r.e j).2.2.1]) ∈ r.xs.zip r.xi :=
          mem_zip_of_lt hb hb_xi
        have hqx : pc n w (r.xi[(r.e j).2.2.1]!) (r.xs[(r.e j).2.2.1]!) = pid n w := by
          have hq0 := List.all_eq_true.1 hzip _ hmem_zip
          rw [getElem!_pos r.xs _ hb, getElem!_pos r.xi _ hb_xi]
          exact Nat.eq_of_beq_eq_true hq0
        obtain ⟨iha_mem, iha_sq, iha_ne, iha_pts⟩ :=
          ih ((r.e (r.e j).2.1).2.2.2) (by omega) (r.e j).2.1 ha rfl
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [uPerm_of_conj h0 hd]
          have ht : toP n w r.xs[(r.e j).2.2.1]! ∈ T := by
            rw [hTdef]
            exact subset_closure (by
              rw [Set.mem_setOf_eq, List.mem_map]
              exact ⟨_, hb_mem_xs, rfl⟩)
          exact mul_mem (mul_mem ht iha_mem) (inv_mem ht)
        · rw [uPerm_of_conj h0 hd]
          have hs2 : (toP n w r.xs[(r.e j).2.2.1]! * uPerm n w r (r.e j).2.1 *
              (toP n w r.xs[(r.e j).2.2.1]!)⁻¹) ^ 2 = 1 := by
            rw [conj_pow, iha_sq]; simp
          exact hs2
        · rw [uPerm_of_conj h0 hd]
          intro hh
          exact iha_ne (conj_eq_one_iff.mp hh)
        · intro p hp
          rw [uPerm_of_conj h0 hd, puAt_of_conj h0 hd]
          have hxi_inv : at' w r.xi[(r.e j).2.2.1]! p =
              ((toP n w r.xs[(r.e j).2.2.1]!)⁻¹ ⟨p, hp⟩ : Nat) :=
            at'_eq_toP_inv hn hw hcxib hcxb hpvb hpid hqx hp
          have hxi_lt : at' w r.xi[(r.e j).2.2.1]! p < n := by
            rw [hxi_inv]; exact ((toP n w r.xs[(r.e j).2.2.1]!)⁻¹ ⟨p, hp⟩).2
          have hpt_a := iha_pts (at' w r.xi[(r.e j).2.2.1]! p) hxi_lt
          have hxi_fin : (⟨at' w r.xi[(r.e j).2.2.1]! p, hxi_lt⟩ : Fin n) =
              (toP n w r.xs[(r.e j).2.2.1]!)⁻¹ ⟨p, hp⟩ := Fin.ext hxi_inv
          have hpt_a' : puAt w r (r.e j).2.1 (at' w r.xi[(r.e j).2.2.1]! p) =
              (uPerm n w r (r.e j).2.1
                ((toP n w r.xs[(r.e j).2.2.1]!)⁻¹ ⟨p, hp⟩) : Nat) := by
            rw [hpt_a]
            exact congrArg (fun z : Fin n => (uPerm n w r (r.e j).2.1 z : Nat)) hxi_fin
          rw [hpt_a']
          have hpu_lt : (uPerm n w r (r.e j).2.1
              ((toP n w r.xs[(r.e j).2.2.1]!)⁻¹ ⟨p, hp⟩) : Nat) < n :=
            (uPerm n w r (r.e j).2.1 _).2
          rw [at'_eq_toP hw hcxb hpvb hpu_lt]
          have hfin : (⟨(uPerm n w r (r.e j).2.1
                ((toP n w r.xs[(r.e j).2.2.1]!)⁻¹ ⟨p, hp⟩) : Nat), hpu_lt⟩ : Fin n) =
              uPerm n w r (r.e j).2.1 ((toP n w r.xs[(r.e j).2.2.1]!)⁻¹ ⟨p, hp⟩) :=
            Fin.ext rfl
          rw [hfin, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  intro j hj
  exact key (r.e j).2.2.2 j hj rfl

private theorem lt_of_chain {f : Nat → Nat} {N : Nat}
    (h : ((List.range (N - 1)).all fun i => Nat.blt (f i) (f (i + 1))) = true) :
    ∀ i j, i < j → j < N → f i < f j := by
  intro i j hij hjN
  have hchain : ∀ k, k < N - 1 → f k < f (k + 1) := fun k hk =>
    Nat.blt_eq.mp (List.all_eq_true.1 h k (List.mem_range.mpr hk))
  have hij' : i + 1 ≤ j := by omega
  induction j, hij' using Nat.le_induction with
  | base => exact hchain i (by omega)
  | succ j hij ih => exact lt_trans (ih (by omega) (by omega)) (hchain j (by omega))

private theorem uPerm_injOn {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hkb : ∀ p ∈ r.kb, p < n) (hc : canonR n w r = true)
    (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true) :
    ∀ i < usize r.ukc, ∀ j < usize r.ukc, uPerm n w r i = uPerm n w r j → i = j := by
  have h' := h
  simp only [prootConjOKB, Bool.and_eq_true] at h'
  have hpord : pordOK n w r = true := by tauto
  have keyeq : ∀ {i j : Nat}, i < usize r.ukc → j < usize r.ukc →
      uPerm n w r i = uPerm n w r j → pkeyU n w r i = pkeyU n w r j := by
    intro i j hi hj he
    obtain ⟨-, -, -, hai⟩ := uPerm_spec hn hw hc h i hi
    obtain ⟨-, -, -, haj⟩ := uPerm_spec hn hw hc h j hj
    have hmap : r.kb.map (puAt w r i) = r.kb.map (puAt w r j) := by
      apply List.map_congr_left
      intro p hp
      have hp' : p < n := hkb p hp
      rw [hai p hp', haj p hp', he]
    unfold pkeyU
    rw [hmap]
  intro i hi j hj hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hkey := keyeq hi hj hij
    have hlt' := lt_of_chain (f := pkeyU n w r) hpord i j hlt hj
    rw [hkey] at hlt'
    exact lt_irrefl _ hlt'
  · have hkey := keyeq hj hi hij.symm
    have hlt' := lt_of_chain (f := pkeyU n w r) hpord j i hlt hi
    rw [hkey] at hlt'
    exact lt_irrefl _ hlt'

private theorem exists_uPerm_eq {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hkb : ∀ p ∈ r.kb, p < n) (hc : canonR n w r = true)
    (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true) :
    ∀ b ∈ (closure {a | a ∈ r.xs.map (fun x => toP n w x)} : Subgroup (Equiv.Perm (Fin n))),
      b ^ 2 = 1 → b ≠ 1 → ∃ j < usize r.ukc, uPerm n w r j = b := by
  classical
  have h' := h
  simp only [prootConjOKB, Bool.and_eq_true] at h'
  have hbeq : Nat.beq (usize r.ukc) r.im.length = true := by tauto
  set S : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter fun g => g ∈ (closure {a | a ∈ r.xs.map (fun x => toP n w x)} :
      Subgroup (Equiv.Perm (Fin n))) ∧ g ^ 2 = 1 ∧ g ≠ 1 with hSdef
  set A : Finset (Equiv.Perm (Fin n)) :=
    (Finset.range (usize r.ukc)).image (uPerm n w r) with hAdef
  have hAcard : A.card = usize r.ukc := by
    rw [hAdef]
    have hcard : ((Finset.range (usize r.ukc)).image (uPerm n w r)).card =
        (Finset.range (usize r.ukc)).card := by
      apply Finset.card_image_of_injOn
      intro i hi j hj hij
      exact uPerm_injOn hn hw hkb hc h i (by simpa using hi) j (by simpa using hj) hij
    rw [hcard, Finset.card_range]
  have hAS : A ⊆ S := by
    intro g hg
    rw [hAdef, Finset.mem_image] at hg
    obtain ⟨j, hjr, rfl⟩ := hg
    rw [Finset.mem_range] at hjr
    obtain ⟨hmem, hsq, hne, -⟩ := uPerm_spec hn hw hc h j hjr
    rw [hSdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hmem, hsq, hne⟩
  have hSsub : S ⊆ (r.im.toFinset).image (pcG (r.xs.map fun x => toP n w x)) := by
    intro b hb
    rw [hSdef, Finset.mem_filter] at hb
    obtain ⟨-, hbT, hb2, hb1⟩ := hb
    obtain ⟨m, hm, hmb⟩ := exists_mask_of_invol hn hw hc h b hbT hb2 hb1
    rw [Finset.mem_image]
    exact ⟨m, by simpa using hm, hmb⟩
  have hScard : S.card ≤ usize r.ukc := by
    have h1 : S.card ≤ ((r.im.toFinset).image (pcG (r.xs.map fun x => toP n w x))).card :=
      Finset.card_le_card hSsub
    have h2 : ((r.im.toFinset).image (pcG (r.xs.map fun x => toP n w x))).card ≤
        r.im.toFinset.card := Finset.card_image_le
    have h3 : r.im.toFinset.card ≤ r.im.length := List.toFinset_card_le r.im
    have hN : r.im.length = usize r.ukc := (Nat.eq_of_beq_eq_true hbeq).symm
    omega
  have hAeq : A = S := Finset.eq_of_subset_of_card_le hAS (by rw [hAcard]; exact hScard)
  intro b hbT hb2 hb1
  have hbS : b ∈ S := by
    rw [hSdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hbT, hb2, hb1⟩
  have hbA : b ∈ A := by rw [hAeq]; exact hbS
  rw [hAdef, Finset.mem_image] at hbA
  obtain ⟨j, hj, hjb⟩ := hbA
  rw [Finset.mem_range] at hj
  exact ⟨j, hj, hjb⟩

private def LeafConcl (X : Subgroup (Equiv.Perm (Fin n))) (pw : Bool) (bmode : Nat)
    (skip : List Nat) (x b : Equiv.Perm (Fin n)) : Prop :=
  b ^ 2 = 1 → b ≠ 1 → b ≠ x → (bmode = 1 → b ∈ X) → (bmode = 2 → b ∉ X) →
    MonoW X pw (closure {x, b}) ∨ fixP b ∈ skip ∨ fixP (x * b) ∈ skip

private theorem pcG_mem_iff_bit {G : Type*} [Group G] {X : Subgroup G} :
    ∀ {l : List G} {k : Nat} (hk : k < l.length),
      (∀ i (hi : i < l.length), i ≠ k → l[i] ∈ X) → l[k] ∉ X →
      ∀ m, pcG l m ∈ X ↔ Nat.land (Nat.shiftRight m k) 1 = 0 := by
  intro l
  induction l with
  | nil => intro k hk; exact absurd hk (by simp)
  | cons x l ih =>
    intro k hk hmem hnot m
    cases k with
    | zero =>
      have hHle : closure ({a : G | a ∈ l} : Set G) ≤ X := by
        rw [Subgroup.closure_le]
        rintro y hy
        obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hy
        rw [← he]
        have h := hmem (i + 1) (by rw [List.length_cons]; exact Nat.add_lt_add_right hi 1)
          (by omega)
        simpa only [List.getElem_cons_succ, SetLike.mem_coe] using h
      have hpl : pcG l (m / 2) ∈ X := hHle (pcG_mem l (m / 2))
      have hx : x ∉ X := by simpa only [List.getElem_cons_zero] using hnot
      rw [pcG]
      by_cases hm : m % 2 = 1
      · rw [if_pos hm]
        refine ⟨fun h => absurd ((X.mul_mem_cancel_right hpl).mp h) hx, fun h => ?_⟩
        simp only [Nat.shiftRight_eq', Nat.shiftRight_zero, Nat.land_eq, Nat.and_one_is_mod] at h
        omega
      · rw [if_neg hm, one_mul]
        refine ⟨fun _ => ?_, fun _ => hpl⟩
        rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
        · simpa only [Nat.shiftRight_eq', Nat.shiftRight_zero, Nat.land_eq, Nat.and_one_is_mod]
            using h0
        · exact absurd h1 hm
    | succ k' =>
      have hk' : k' < l.length := by
        rw [List.length_cons] at hk
        omega
      have hxX : x ∈ X := by
        have h := hmem 0 (by simp) (by omega)
        simpa only [List.getElem_cons_zero] using h
      have hhead : (if m % 2 = 1 then x else 1) ∈ X := by
        by_cases hm : m % 2 = 1
        · rwa [if_pos hm]
        · rw [if_neg hm]; exact one_mem X
      have hmem' : ∀ i (hi : i < l.length), i ≠ k' → l[i] ∈ X := by
        intro i hi hne
        have h := hmem (i + 1) (by rw [List.length_cons]; exact Nat.add_lt_add_right hi 1)
          (by omega)
        simpa only [List.getElem_cons_succ] using h
      have hnot' : l[k'] ∉ X := by
        simpa only [List.getElem_cons_succ] using hnot
      have hshift : Nat.shiftRight (m / 2) k' = Nat.shiftRight m (k' + 1) := by
        simp only [Nat.shiftRight_eq']
        rw [Nat.shiftRight_eq_div_pow (m / 2) k', Nat.shiftRight_eq_div_pow m (k' + 1),
          Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
      rw [pcG, X.mul_mem_cancel_left hhead, ih (k := k') hk' hmem' hnot' (m / 2), hshift]

private theorem map_conj_eq_of_normal {G : Type*} [Group G] {X W : Subgroup G} {t : G}
    (ht : t ∈ W) (hXW : X ≤ W) (hXN : (X.subgroupOf W).Normal) :
    X.map (MulAut.conj t).toMonoidHom = X := by
  have hmem : ∀ {k : G}, k ∈ W → ∀ x ∈ X, k * x * k⁻¹ ∈ X := fun {k} hk x hx => by
    have := hXN.conj_mem ⟨x, hXW hx⟩ (mem_subgroupOf.2 hx) ⟨k, hk⟩
    rwa [mem_subgroupOf] at this
  refine le_antisymm ?_ fun x hx => ⟨t⁻¹ * x * t, by simpa using hmem (inv_mem ht) x hx, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hmem ht x hx
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private theorem leafConcl_conj {X : Subgroup (Equiv.Perm (Fin n))} {pw : Bool} {bmode : Nat}
    {skip : List Nat} {x u t : Equiv.Perm (Fin n)}
    (hXt : X.map (MulAut.conj t).toMonoidHom = X) (htx : t * x * t⁻¹ = x)
    (h : LeafConcl X pw bmode skip x u) : LeafConcl X pw bmode skip x (t * u * t⁻¹) := by
  unfold LeafConcl at h ⊢
  intro hb2 hb1 hbx hbm1 hbm2
  have hmem : u ∈ X ↔ t * u * t⁻¹ ∈ X := by
    have h1 : (MulAut.conj t) u ∈ X.map (MulAut.conj t).toMonoidHom ↔ u ∈ X :=
      Subgroup.mem_map_iff_mem (MulAut.conj t).injective
    rw [hXt] at h1
    simpa only [MulAut.conj_apply] using h1.symm
  have hu2 : u ^ 2 = 1 := by
    apply (MulAut.conj t).injective
    rw [map_pow, map_one]
    simpa only [MulAut.conj_apply] using hb2
  have hu1 : u ≠ 1 := by
    intro hu
    exact hb1 (by rw [hu, mul_one, mul_inv_cancel])
  have hux : u ≠ x := by
    intro hux
    exact hbx (by rw [hux, htx])
  have hum1 : bmode = 1 → u ∈ X := fun hb => hmem.mpr (hbm1 hb)
  have hum2 : bmode = 2 → u ∉ X := fun hb hu => hbm2 hb (hmem.mp hu)
  rcases h hu2 hu1 hux hum1 hum2 with hMono | hfix | hfix2
  · left
    have hclos : closure ({x, t * u * t⁻¹} : Set (Equiv.Perm (Fin n))) =
        (closure ({x, u} : Set (Equiv.Perm (Fin n)))).map (MulAut.conj t).toMonoidHom := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro (hy | hy)
        · rw [hy]
          exact ⟨x, Or.inl rfl, htx⟩
        · rw [hy]
          exact ⟨u, Or.inr rfl, rfl⟩
      · rintro ⟨z, hz, hzy⟩
        rw [← hzy]
        rcases hz with hz | hz
        · left; rw [hz, htx]
        · right; rw [hz]
    have hmw := (monoW_map_iff (MulAut.conj t).toMonoidHom (MulAut.conj t).injective X
      (closure ({x, u} : Set (Equiv.Perm (Fin n)))) pw).mpr hMono
    rw [hXt, ← hclos] at hmw
    exact hmw
  · right; left
    rwa [fixP_conj u t]
  · right; right
    have hxcu : x * (t * u * t⁻¹) = t * (x * u) * t⁻¹ := by
      calc x * (t * u * t⁻¹) = (t * x * t⁻¹) * (t * u * t⁻¹) := by rw [htx]
        _ = t * (x * u) * t⁻¹ := by group
    rw [hxcu, fixP_conj]
    exact hfix2

private theorem orderOf_of_pord4 {y : Nat} {g : Equiv.Perm (Fin n)} (G : SP.Good n w)
    (hcy : canon1 n w y = true) (hy : Rep n (unpackP n w y) g) (h : pord4 n w y = true) :
    orderOf g = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [pord4, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hne, h4⟩ := h
  have hne' : pc n w y y ≠ pid n w := beq_eq_false_iff_ne.mp hne
  have h4' : ppow n w y 4 = pid n w := Nat.eq_of_beq_eq_true h4
  have hg2 : ¬ g ^ 2 = 1 := by
    intro hg2
    have hgg : g * g = 1 := by rw [← pow_two]; exact hg2
    have hrep_pc : Rep n (unpackP n w (pc n w y y)) (g * g) := rep_pc G.hn G.hw hcy hy hy
    have hid : Rep n (unpackP n w (pid n w)) 1 := by rw [G.pid_eq]; exact rep_idA
    have heqA : eqA n (unpackP n w (pc n w y y)) (unpackP n w (pid n w)) = true :=
      (eqA_iff hrep_pc hid).mpr hgg
    have hbeq : Nat.beq (pc n w y y) (pid n w) = true := by
      rw [← SP.eqA_unpack (SP.canon_pc G.hn G.hw) G.pid_canon]
      exact heqA
    exact hne' (Nat.eq_of_beq_eq_true hbeq)
  have hg4 : g ^ 4 = 1 := by
    have hr : Rep n (unpackP n w (ppow n w y 4)) (g ^ 4) := rep_ppow G hcy hy 4
    rw [h4'] at hr
    refine Rep.unique hr ?_
    rw [G.pid_eq]; exact rep_idA
  have h2' : ¬ g ^ 2 ^ 1 = 1 := by
    show ¬ g ^ 2 = 1
    exact hg2
  have h4'' : g ^ 2 ^ (1 + 1) = 1 := by
    show g ^ 4 = 1
    exact hg4
  calc orderOf g = 2 ^ (1 + 1) := orderOf_eq_prime_pow h2' h4''
    _ = 4 := by norm_num

private theorem gam_specP {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonR n w r = true)
    (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true)
    (X : Subgroup (Equiv.Perm (Fin n)))
    (hsX : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
      permOfArr n (unpackP n w P) ∈ X) {l : Nat} (hl : l < r.gams.size) :
    ∃ Γ ∈ centDer X (toP n w r.x), Rep n (unpackP n w r.ga[l]!) Γ ∧
      Rep n (unpackP n w r.gi[l]!) Γ⁻¹ := by
  obtain ⟨G, -⟩ := good_of_check hn hw hc h
  have hcanR := hc
  simp only [canonR, Bool.and_eq_true] at hcanR
  have hcx : canon1 n w r.x = true := by tauto
  have hcs_can : r.cs.toList.all (canon1 n w) = true := by tauto
  have h' := h
  simp only [prootConjOKB, Bool.and_eq_true] at h'
  have hpvx : pvalid n w r.x = true := by tauto
  have hcs_all : r.cs.toList.all (fun c => pvalid n w c && inXP c && pcommA n w c r.x) = true := by
    tauto
  have hgams_all : (List.range r.gams.size).all (fun l =>
      Nat.blt r.gams[l]!.1 r.cs.size && Nat.blt r.gams[l]!.2 r.cs.size &&
      Nat.beq r.ga[l]! (pcomm n w r.cs[r.gams[l]!.1]! r.cs[r.gams[l]!.2]!) &&
      Nat.beq r.gi[l]! (pcomm n w r.cs[r.gams[l]!.2]! r.cs[r.gams[l]!.1]!)) = true := by
    tauto
  have hg := List.all_eq_true.1 hgams_all l (List.mem_range.mpr hl)
  have hg' : ((r.gams[l]!.1 < r.cs.size ∧ r.gams[l]!.2 < r.cs.size) ∧
      r.ga[l]! = pcomm n w r.cs[r.gams[l]!.1]! r.cs[r.gams[l]!.2]!) ∧
      r.gi[l]! = pcomm n w r.cs[r.gams[l]!.2]! r.cs[r.gams[l]!.1]! := by
    simpa only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] using hg
  obtain ⟨⟨⟨hi, hj⟩, hgai⟩, hgii⟩ := hg'
  have hmem_i : r.cs[r.gams[l]!.1]! ∈ r.cs.toList := by
    rw [getElem!_pos r.cs _ hi]
    exact Array.getElem_mem_toList hi
  have hmem_j : r.cs[r.gams[l]!.2]! ∈ r.cs.toList := by
    rw [getElem!_pos r.cs _ hj]
    exact Array.getElem_mem_toList hj
  have hci := List.all_eq_true.1 hcs_all _ hmem_i
  have hcj := List.all_eq_true.1 hcs_all _ hmem_j
  simp only [Bool.and_eq_true] at hci hcj
  obtain ⟨⟨hvi, hXi⟩, hcommi⟩ := hci
  obtain ⟨⟨hvj, hXj⟩, hcommj⟩ := hcj
  have hcan_i : canon1 n w (r.cs[r.gams[l]!.1]!) = true := List.all_eq_true.1 hcs_can _ hmem_i
  have hcan_j : canon1 n w (r.cs[r.gams[l]!.2]!) = true := List.all_eq_true.1 hcs_can _ hmem_j
  have hpc_i : pc n w (r.cs[r.gams[l]!.1]!) r.x = pc n w r.x (r.cs[r.gams[l]!.1]!) :=
    Nat.eq_of_beq_eq_true (by simpa only [pcommA] using hcommi)
  have hpc_j : pc n w (r.cs[r.gams[l]!.2]!) r.x = pc n w r.x (r.cs[r.gams[l]!.2]!) :=
    Nat.eq_of_beq_eq_true (by simpa only [pcommA] using hcommj)
  have hmem_i' : toP n w (r.cs[r.gams[l]!.1]!) ∈
      (X ⊓ centralizer ({toP n w r.x} : Set (Equiv.Perm (Fin n))) :
        Subgroup (Equiv.Perm (Fin n))) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa only [toP] using hsX _ hcan_i hvi hXi
    · rw [mem_centralizer_singleton_iff]
      show toP n w (r.cs[r.gams[l]!.1]!) * toP n w r.x =
        toP n w r.x * toP n w (r.cs[r.gams[l]!.1]!)
      rw [← toP_pc hn hw hcan_i hcx hvi hpvx, hpc_i,
        toP_pc hn hw hcx hcan_i hpvx hvi]
  have hmem_j' : toP n w (r.cs[r.gams[l]!.2]!) ∈
      (X ⊓ centralizer ({toP n w r.x} : Set (Equiv.Perm (Fin n))) :
        Subgroup (Equiv.Perm (Fin n))) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa only [toP] using hsX _ hcan_j hvj hXj
    · rw [mem_centralizer_singleton_iff]
      show toP n w (r.cs[r.gams[l]!.2]!) * toP n w r.x =
        toP n w r.x * toP n w (r.cs[r.gams[l]!.2]!)
      rw [← toP_pc hn hw hcan_j hcx hvj hpvx, hpc_j,
        toP_pc hn hw hcx hcan_j hpvx hvj]
  have hvalid_i : validA n (unpackP n w (r.cs[r.gams[l]!.1]!)) = true := by
    rw [SP.validA_unpack hw hcan_i]; exact hvi
  have hvalid_j : validA n (unpackP n w (r.cs[r.gams[l]!.2]!)) = true := by
    rw [SP.validA_unpack hw hcan_j]; exact hvj
  have hga' : unpackP n w (r.ga[l]!) =
      commutatorA n (unpackP n w (r.cs[r.gams[l]!.1]!))
        (unpackP n w (r.cs[r.gams[l]!.2]!)) := by
    rw [hgai, SP.pcomm_eq G hcan_i hcan_j]
  have hgi' : unpackP n w (r.gi[l]!) =
      commutatorA n (unpackP n w (r.cs[r.gams[l]!.2]!))
        (unpackP n w (r.cs[r.gams[l]!.1]!)) := by
    rw [hgii, SP.pcomm_eq G hcan_j hcan_i]
  refine ⟨_, commutator_mem_commutator hmem_i' hmem_j', ?_⟩
  refine ⟨?_, ?_⟩
  · rw [hga']; exact rep_commutatorA hvalid_i hvalid_j
  · rw [commutatorElement_inv, hgi']; exact rep_commutatorA hvalid_j hvalid_i

private theorem cand_ord4_spec {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonR n w r = true)
    (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true)
    (X : Subgroup (Equiv.Perm (Fin n))) (hps : ∀ p ∈ ps, p < n)
    (hsX : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
      permOfArr n (unpackP n w P) ∈ X)
    {b : Nat} (hcb : canon1 n w b = true) (hvb : pvalid n w b = true)
    (hb2 : toP n w b ^ 2 = 1) (hb1 : toP n w b ≠ 1) (hbx : toP n w b ≠ toP n w r.x)
    {l m : Nat} (hin : RootWitP.inRange r (.ord4 l m) = true)
    (hcand : pcandOK n w inXP r.x r.ga r.gi (r.perfs.map (pperfGens n w r.ga)) b
      (.ord4 l m) = true) :
    MonoW X pw (closure {toP n w r.x, toP n w b}) := by
  letI : Bracket (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) := commutatorElement
  obtain ⟨G, -⟩ := good_of_check hn hw hc h
  obtain ⟨hcx, hpvx, hx2, hx1⟩ := x_facts hn hw hc h
  have hl : l < r.gams.size := Nat.blt_eq.mp (by simpa [RootWitP.inRange] using hin)
  obtain ⟨Γ, hΓ, hΓr, hΓi⟩ := gam_specP hn hw hc h X hsX hl
  set V : Subgroup (Equiv.Perm (Fin n)) := closure {toP n w r.x, toP n w b} with hV
  have hxV : toP n w r.x ∈ V := subset_closure (Set.mem_insert _ _)
  have hbV : toP n w b ∈ V := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hΓV : centDer X (toP n w r.x) ≤ gammaE X V :=
    le_iSup₂_of_le (toP n w r.x) hxV (le_iSup_of_le hx1 le_rfl)
  have hbinv : (toP n w b)⁻¹ = toP n w b :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb2)
  have hyb : Rep n (unpackP n w b) (toP n w b) := rep_toP hw hcb hvb
  have hrep1 : Rep n (unpackP n w (pc n w b r.ga[l]!)) (toP n w b * Γ) :=
    rep_pc hn hw hcb hyb hΓr
  have hrep2 : Rep n (unpackP n w (pc n w b r.gi[l]!)) (toP n w b * Γ⁻¹) :=
    rep_pc hn hw hcb hyb hΓi
  have hwrep : Rep n (unpackP n w (pc n w (pc n w b r.ga[l]!) (pc n w b r.gi[l]!)))
      ⁅toP n w b, Γ⁆ := by
    rw [commutatorElement_def, hbinv, mul_assoc]
    exact rep_pc hn hw (SP.canon_pc hn hw) hrep1 hrep2
  have hwN : ⁅toP n w b, Γ⁆ ∈ nE X V := commutator_mem_commutator hbV (hΓV hΓ)
  have hcand' := hcand
  simp only [pcandOK] at hcand'
  have hpord : pord4 n w (ppow n w (pc n w (pc n w b r.ga[l]!) (pc n w b r.gi[l]!)) m) = true := by
    simpa using hcand'
  have hcany : canon1 n w (pc n w (pc n w b r.ga[l]!) (pc n w b r.gi[l]!)) = true :=
    SP.canon_pc hn hw
  have hy := rep_ppow G hcany hwrep m
  have hord := orderOf_of_pord4 G (SP.ppow_eq G hcany m).2 hy hpord
  refine Or.inl ⟨⁅toP n w b, Γ⁆ ^ m, pow_mem hwN m, ?_⟩
  rw [hord]

private theorem cand_ord4p_spec {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonR n w r = true)
    (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true)
    (X : Subgroup (Equiv.Perm (Fin n))) (hps : ∀ p ∈ ps, p < n)
    (hsX : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
      permOfArr n (unpackP n w P) ∈ X)
    {b : Nat} (hcb : canon1 n w b = true) (hvb : pvalid n w b = true)
    (hb2 : toP n w b ^ 2 = 1) (hb1 : toP n w b ≠ 1) (hbx : toP n w b ≠ toP n w r.x)
    {ls : List Nat} {m : Nat} (hin : RootWitP.inRange r (.ord4p ls m) = true)
    (hcand : pcandOK n w inXP r.x r.ga r.gi (r.perfs.map (pperfGens n w r.ga)) b
      (.ord4p ls m) = true) :
    MonoW X pw (closure {toP n w r.x, toP n w b}) := by
  letI : Bracket (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) := commutatorElement
  obtain ⟨G, -⟩ := good_of_check hn hw hc h
  obtain ⟨hcx, hpvx, hx2, hx1⟩ := x_facts hn hw hc h
  have hls : ls.all (fun l => Nat.blt l r.gams.size) = true := by
    simpa [RootWitP.inRange] using hin
  set V : Subgroup (Equiv.Perm (Fin n)) := closure {toP n w r.x, toP n w b} with hV
  have hxV : toP n w r.x ∈ V := subset_closure (Set.mem_insert _ _)
  have hbV : toP n w b ∈ V := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hΓV : centDer X (toP n w r.x) ≤ gammaE X V :=
    le_iSup₂_of_le (toP n w r.x) hxV (le_iSup_of_le hx1 le_rfl)
  have hbinv : (toP n w b)⁻¹ = toP n w b :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb2)
  have hyb : Rep n (unpackP n w b) (toP n w b) := rep_toP hw hcb hvb
  set lpacked : List Nat := ls.map (fun l => pc n w (pc n w b r.ga[l]!) (pc n w b r.gi[l]!))
    with hlpacked
  have hcan_lpacked : ∀ x ∈ lpacked, canon1 n w x = true := by
    intro x hx
    rw [hlpacked, List.mem_map] at hx
    obtain ⟨l, -, rfl⟩ := hx
    exact SP.canon_pc hn hw
  have hcand' : pord4 n w (ppow n w (pprod n w lpacked) m) = true := by
    simpa only [hlpacked, pcandOK] using hcand
  have hprod : ∃ g ∈ nE X V, Rep n (unpackP n w (pprod n w lpacked)) g := by
    have hrep : ∃ g ∈ nE X V, Rep n (prodA n (lpacked.map (unpackP n w))) g := by
      apply rep_prodA
      intro a ha
      rw [List.mem_map] at ha
      obtain ⟨y, hy, rfl⟩ := ha
      rw [hlpacked, List.mem_map] at hy
      obtain ⟨l, hl, rfl⟩ := hy
      have hlg : l < r.gams.size := Nat.blt_eq.mp (List.all_eq_true.1 hls l hl)
      obtain ⟨Γ, hΓ, hΓr, hΓi⟩ := gam_specP hn hw hc h X hsX hlg
      have hrep1 : Rep n (unpackP n w (pc n w b r.ga[l]!)) (toP n w b * Γ) :=
        rep_pc hn hw hcb hyb hΓr
      have hrep2 : Rep n (unpackP n w (pc n w b r.gi[l]!)) (toP n w b * Γ⁻¹) :=
        rep_pc hn hw hcb hyb hΓi
      refine ⟨⁅toP n w b, Γ⁆, commutator_mem_commutator hbV (hΓV hΓ), ?_⟩
      rw [commutatorElement_def, hbinv, mul_assoc]
      exact rep_pc hn hw (SP.canon_pc hn hw) hrep1 hrep2
    obtain ⟨g, hg, hgrep⟩ := hrep
    refine ⟨g, hg, ?_⟩
    rw [(SP.pprod_eq G hcan_lpacked).1]
    exact hgrep
  obtain ⟨g, hg, hgrep⟩ := hprod
  have hcany : canon1 n w (pprod n w lpacked) = true := (SP.pprod_eq G hcan_lpacked).2
  have hy := rep_ppow G hcany hgrep m
  have hord := orderOf_of_pord4 G (SP.ppow_eq G hcany m).2 hy hcand'
  refine Or.inl ⟨g ^ m, pow_mem hg m, ?_⟩
  rw [hord]

private theorem cand_ord4c_spec {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonR n w r = true)
    (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true)
    (X : Subgroup (Equiv.Perm (Fin n))) (hps : ∀ p ∈ ps, p < n)
    (hsX : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
      permOfArr n (unpackP n w P) ∈ X)
    {b : Nat} (hcb : canon1 n w b = true) (hvb : pvalid n w b = true)
    (hb2 : toP n w b ^ 2 = 1) (hb1 : toP n w b ≠ 1) (hbx : toP n w b ≠ toP n w r.x)
    {e c₁ c₂ m : Nat} (hcw : canonWitP n w (.ord4c e c₁ c₂ m) = true)
    (hcand : pcandOK n w inXP r.x r.ga r.gi (r.perfs.map (pperfGens n w r.ga)) b
      (.ord4c e c₁ c₂ m) = true) :
    MonoW X pw (closure {toP n w r.x, toP n w b}) := by
  letI : Bracket (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) := commutatorElement
  obtain ⟨G, -⟩ := good_of_check hn hw hc h
  obtain ⟨hcx, hpvx, hx2, hx1⟩ := x_facts hn hw hc h
  have hxinv : (toP n w r.x)⁻¹ = toP n w r.x :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx2)
  have hcw' := hcw
  simp only [canonWitP, Bool.and_eq_true] at hcw'
  obtain ⟨hcw1, hcw2⟩ := hcw'
  set e' : Nat := bif Nat.beq e 0 then b else pc n w r.x b with he'_def
  have hcand' : pvalid n w c₁ && pvalid n w c₂ && inXP c₁ && inXP c₂ &&
      pcommA n w c₁ e' && pcommA n w c₂ e' &&
      pord4 n w (ppow n w (pc n w (pc n w r.x (pcomm n w c₁ c₂))
        (pc n w r.x (pcomm n w c₂ c₁))) m) = true := by
    have h := hcand
    simp only [pcandOK] at h
    rw [← he'_def] at h
    exact h
  obtain ⟨⟨⟨⟨⟨⟨hv1, hv2⟩, hX1⟩, hX2⟩, hcomm1⟩, hcomm2⟩, hpord⟩ := by
    simpa only [Bool.and_eq_true] using hcand'
  have hcan_e' : canon1 n w e' = true := by
    rw [he'_def]
    by_cases he : e = 0
    · have hbq : Nat.beq e 0 = true := by rw [Nat.beq_eq]; exact he
      rw [hbq, Bool.cond_true]
      exact hcb
    · have hbq : Nat.beq e 0 = false := beq_eq_false_iff_ne.mpr he
      rw [hbq, Bool.cond_false]
      exact SP.canon_pc hn hw
  have hpv_e' : pvalid n w e' = true := by
    rw [he'_def]
    by_cases he : e = 0
    · have hbq : Nat.beq e 0 = true := by rw [Nat.beq_eq]; exact he
      rw [hbq, Bool.cond_true]
      exact hvb
    · have hbq : Nat.beq e 0 = false := beq_eq_false_iff_ne.mpr he
      rw [hbq, Bool.cond_false]
      exact pvalid_pc hn hw hcx hpvx hcb hvb
  set V : Subgroup (Equiv.Perm (Fin n)) := closure {toP n w r.x, toP n w b} with hV
  have hxV : toP n w r.x ∈ V := subset_closure (Set.mem_insert _ _)
  have hbV : toP n w b ∈ V := subset_closure (Set.mem_insert_of_mem _ rfl)
  have he'V : toP n w e' ∈ V := by
    rw [he'_def]
    by_cases he : e = 0
    · have hbq : Nat.beq e 0 = true := by rw [Nat.beq_eq]; exact he
      rw [hbq, Bool.cond_true]
      exact hbV
    · have hbq : Nat.beq e 0 = false := beq_eq_false_iff_ne.mpr he
      rw [hbq, Bool.cond_false, toP_pc hn hw hcx hcb hpvx hvb]
      exact V.mul_mem hxV hbV
  have he'1 : toP n w e' ≠ 1 := by
    rw [he'_def]
    by_cases he : e = 0
    · have hbq : Nat.beq e 0 = true := by rw [Nat.beq_eq]; exact he
      rw [hbq, Bool.cond_true]
      exact hb1
    · have hbq : Nat.beq e 0 = false := beq_eq_false_iff_ne.mpr he
      rw [hbq, Bool.cond_false, toP_pc hn hw hcx hcb hpvx hvb]
      intro h1
      apply hbx
      rw [← hxinv]
      exact eq_inv_of_mul_eq_one_right h1
  have hpc1 : pc n w c₁ e' = pc n w e' c₁ :=
    Nat.eq_of_beq_eq_true (by simpa only [pcommA] using hcomm1)
  have hpc2 : pc n w c₂ e' = pc n w e' c₂ :=
    Nat.eq_of_beq_eq_true (by simpa only [pcommA] using hcomm2)
  have hmem1 : toP n w c₁ ∈
      (X ⊓ centralizer ({toP n w e'} : Set (Equiv.Perm (Fin n))) :
        Subgroup (Equiv.Perm (Fin n))) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa only [toP] using hsX c₁ hcw1 hv1 hX1
    · rw [mem_centralizer_singleton_iff]
      show toP n w c₁ * toP n w e' = toP n w e' * toP n w c₁
      rw [← toP_pc hn hw hcw1 hcan_e' hv1 hpv_e', hpc1,
        toP_pc hn hw hcan_e' hcw1 hpv_e' hv1]
  have hmem2 : toP n w c₂ ∈
      (X ⊓ centralizer ({toP n w e'} : Set (Equiv.Perm (Fin n))) :
        Subgroup (Equiv.Perm (Fin n))) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa only [toP] using hsX c₂ hcw2 hv2 hX2
    · rw [mem_centralizer_singleton_iff]
      show toP n w c₂ * toP n w e' = toP n w e' * toP n w c₂
      rw [← toP_pc hn hw hcw2 hcan_e' hv2 hpv_e', hpc2,
        toP_pc hn hw hcan_e' hcw2 hpv_e' hv2]
  have hγmem : ⁅toP n w c₁, toP n w c₂⁆ ∈ centDer X (toP n w e') :=
    commutator_mem_commutator hmem1 hmem2
  have hγVle : centDer X (toP n w e') ≤ gammaE X V :=
    le_iSup₂_of_le (toP n w e') he'V (le_iSup_of_le he'1 le_rfl)
  have hγV : ⁅toP n w c₁, toP n w c₂⁆ ∈ gammaE X V := hγVle hγmem
  have hxrep : Rep n (unpackP n w r.x) (toP n w r.x) := rep_toP hw hcx hpvx
  have hγrep : Rep n (unpackP n w (pcomm n w c₁ c₂)) ⁅toP n w c₁, toP n w c₂⁆ := by
    rw [SP.pcomm_eq G hcw1 hcw2]
    exact rep_commutatorA (by rw [SP.validA_unpack hw hcw1]; exact hv1)
      (by rw [SP.validA_unpack hw hcw2]; exact hv2)
  have hγirep : Rep n (unpackP n w (pcomm n w c₂ c₁))
      (⁅toP n w c₁, toP n w c₂⁆)⁻¹ := by
    rw [commutatorElement_inv, SP.pcomm_eq G hcw2 hcw1]
    exact rep_commutatorA (by rw [SP.validA_unpack hw hcw2]; exact hv2)
      (by rw [SP.validA_unpack hw hcw1]; exact hv1)
  have hrep1 : Rep n (unpackP n w (pc n w r.x (pcomm n w c₁ c₂)))
      (toP n w r.x * ⁅toP n w c₁, toP n w c₂⁆) := rep_pc hn hw hcx hxrep hγrep
  have hrep2 : Rep n (unpackP n w (pc n w r.x (pcomm n w c₂ c₁)))
      (toP n w r.x * (⁅toP n w c₁, toP n w c₂⁆)⁻¹) := rep_pc hn hw hcx hxrep hγirep
  have hwrep : Rep n (unpackP n w (pc n w (pc n w r.x (pcomm n w c₁ c₂))
        (pc n w r.x (pcomm n w c₂ c₁)))) ⁅toP n w r.x, ⁅toP n w c₁, toP n w c₂⁆⁆ := by
    rw [commutatorElement_def, hxinv, mul_assoc]
    exact rep_pc hn hw (SP.canon_pc hn hw) hrep1 hrep2
  have hwN : ⁅toP n w r.x, ⁅toP n w c₁, toP n w c₂⁆⁆ ∈ nE X V :=
    commutator_mem_commutator hxV hγV
  have hcany : canon1 n w (pc n w (pc n w r.x (pcomm n w c₁ c₂))
      (pc n w r.x (pcomm n w c₂ c₁))) = true := SP.canon_pc hn hw
  have hy := rep_ppow G hcany hwrep m
  have hord := orderOf_of_pord4 G (SP.ppow_eq G hcany m).2 hy hpord
  refine Or.inl ⟨⁅toP n w r.x, ⁅toP n w c₁, toP n w c₂⁆⁆ ^ m, pow_mem hwN m, ?_⟩
  rw [hord]

private noncomputable def perfSubP (n w : Nat) (ga : Array Nat) (P : PerfCertP) :
    Subgroup (Equiv.Perm (Fin n)) :=
  closure {g | ∃ q ∈ (pperfGens n w ga P).toList, toP n w q = g}

private theorem perf_mem_toList_get {α : Type*} [Inhabited α] {a : Array α} {x : α}
    (hx : x ∈ a.toList) : ∃ k, ∃ _hk : k < a.size, a[k]! = x := by
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
  refine ⟨k, by simpa using hk, ?_⟩
  rw [getElem!_pos a k (by simpa using hk)]
  simpa using hkx

private theorem perfSubP_eq {ga : Array Nat} {P : PerfCertP} :
    perfSubP n w ga P = closure (permsA n ((pperfGens n w ga P).map (unpackP n w))) := by
  unfold perfSubP toP
  congr 1
  ext g
  constructor
  · rintro ⟨q, hq, hqg⟩
    obtain ⟨k, hk, rfl⟩ := perf_mem_toList_get hq
    refine ⟨k, by simpa using hk, ?_⟩
    show permOfArr n ((pperfGens n w ga P).map (unpackP n w))[k]! = g
    rw [SP.map_get (unpackP n w) (pperfGens n w ga P) hk]
    exact hqg
  · rintro ⟨k, hk, hkg⟩
    refine ⟨(pperfGens n w ga P)[k]!, ?_, ?_⟩
    · rw [getElem!_pos (pperfGens n w ga P) k (by simpa using hk)]
      exact Array.getElem_mem_toList (by simpa using hk)
    · have hkg' : permOfArr n ((pperfGens n w ga P).map (unpackP n w))[k]! = g := hkg
      rw [SP.map_get (unpackP n w) (pperfGens n w ga P) (by simpa using hk)] at hkg'
      exact hkg'

private theorem perf_gens_canon {ga : Array Nat} {P : PerfCertP} (G : SP.Good n w)
    (hga : ∀ l < ga.size, canon1 n w ga[l]! = true)
    (hgl : P.gens.all (fun gl => gl.1.all fun l => Nat.blt l ga.size) = true) :
    ∀ x ∈ (pperfGens n w ga P).toList, canon1 n w x = true := by
  intro x hx
  simp only [pperfGens, Array.mem_toList_iff, List.mem_toArray, List.mem_map] at hx
  obtain ⟨gl, hglmem, rfl⟩ := hx
  have hglall := List.all_eq_true.1 hgl gl hglmem
  have hcan_map : ∀ y ∈ gl.1.map (fun l => ga[l]!), canon1 n w y = true := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨l, hl, rfl⟩ := hy
    exact hga l (Nat.blt_eq.mp (List.all_eq_true.1 hglall l hl))
  exact (SP.ppow_eq G (SP.pprod_eq G hcan_map).2 gl.2).2

private theorem perf_canon_pcomm (G : SP.Good n w) (p q : Nat) :
    canon1 n w (pcomm n w p q) = true := by
  unfold pcomm
  exact SP.canon_pc G.hn G.hw

private theorem perf_canon_pconj (G : SP.Good n w) (p q : Nat) :
    canon1 n w (pconj n w p q) = true := by
  unfold pconj
  exact SP.canon_pc G.hn G.hw

private theorem perf_gs_map {ga : Array Nat} {P : PerfCertP} :
    (pperfGens n w ga P).map (unpackP n w) =
      (P.gens.map fun gl =>
        unpackP n w (ppow n w (pprod n w (gl.1.map fun l => ga[l]!)) gl.2)).toArray := by
  unfold pperfGens
  rw [List.map_toArray, List.map_map]
  rfl

private theorem pperfOK_spec {ps : List Nat} {ga : Array Nat} {P : PerfCertP}
    {X : Subgroup (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)} (G : SP.Good n w)
    (hps : ∀ p ∈ ps, p < n)
    (hga : ∀ l < ga.size, canon1 n w ga[l]! = true ∧
      ∃ Γ ∈ centDer X x, Rep n (unpackP n w ga[l]!) Γ)
    (hcP : ∀ q ∈ P.cP.pts.toList, canon1 n w q = true)
    (hcQ : ∀ q ∈ P.cQ.pts.toList, canon1 n w q = true)
    (hcR : ∀ q ∈ P.cR.pts.toList, canon1 n w q = true)
    (h : pperfOK n w ps ga P = true) :
    perfSubP n w ga P ≤ centDer X x ∧
      ⁅perfSubP n w ga P, perfSubP n w ga P⁆ = perfSubP n w ga P ∧
      (∀ q ∈ (pperfGens n w ga P).toList, canon1 n w q = true ∧ pvalid n w q = true) ∧
      ∃ y ∈ perfSubP n w ga P, IsPGroup 2 (zpowers y) ∧
        perfSubP n w ga P ≤ closure {z | ∃ p ∈ perfSubP n w ga P, z = p * y ^ 2 * p⁻¹} := by
  have hn := G.hn
  have hw := G.hw
  simp only [pperfOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hgl, hP⟩, hcomms⟩, hQ⟩, hQsize⟩, hx⟩, hxpow⟩, hconjs⟩, hR⟩, hRsize⟩ := h
  set gs := pperfGens n w ga P with hgsdef
  set xa := P.cP.pts[P.x]! with hxadef
  set rs := (P.conjs.map fun p => pconj n w P.cP.pts[p]! (pc n w xa xa)).toArray with hrsdef
  have hgscan : ∀ q ∈ gs.toList, canon1 n w q = true :=
    perf_gens_canon G (fun l hl => (hga l hl).1) hgl
  have hP' : enumOK n (gs.map (unpackP n w)) ps (ArrCertP.toMain n w P.cP) = true :=
    enumOK_of_enumOKK (SP.enumOKK_of_penumOK G hgscan hcP hP)
  have hqscan : ∀ q ∈ ((P.comms.map fun ij =>
      pcomm n w P.cP.pts[ij.1]! P.cP.pts[ij.2]!).toArray).toList, canon1 n w q = true := by
    intro y hy
    simp only [Array.mem_toList_iff, List.mem_toArray, List.mem_map] at hy
    obtain ⟨ij, -, rfl⟩ := hy
    exact perf_canon_pcomm G _ _
  have hQ' : enumOK n (((P.comms.map fun ij =>
      pcomm n w P.cP.pts[ij.1]! P.cP.pts[ij.2]!).toArray).map (unpackP n w))
      ps (ArrCertP.toMain n w P.cQ) = true :=
    enumOK_of_enumOKK (SP.enumOKK_of_penumOK G hqscan hcQ hQ)
  have hrscan : ∀ q ∈ rs.toList, canon1 n w q = true := by
    intro y hy
    rw [hrsdef] at hy
    simp only [Array.mem_toList_iff, List.mem_toArray, List.mem_map] at hy
    obtain ⟨p, -, rfl⟩ := hy
    exact perf_canon_pconj G _ _
  have hR' : enumOK n (rs.map (unpackP n w)) ps (ArrCertP.toMain n w P.cR) = true :=
    enumOK_of_enumOKK (SP.enumOKK_of_penumOK G hrscan hcR hR)
  have hcomm_arr :
      ((P.comms.map fun ij => pcomm n w P.cP.pts[ij.1]! P.cP.pts[ij.2]!).toArray).map
          (unpackP n w) =
        (P.comms.map fun ij => commutatorA n (ArrCertP.toMain n w P.cP).pts[ij.1]!
          (ArrCertP.toMain n w P.cP).pts[ij.2]!).toArray := by
    rw [List.map_toArray, List.map_map]
    congr 1
    refine List.map_congr_left fun ij hij => ?_
    have hij' := List.all_eq_true.1 hcomms ij hij
    simp only [Bool.and_eq_true] at hij'
    have h1 := Nat.blt_eq.mp hij'.1
    have h2 := Nat.blt_eq.mp hij'.2
    have hc1 : canon1 n w P.cP.pts[ij.1]! = true := hcP _ (by
      rw [getElem!_pos P.cP.pts ij.1 h1]; exact Array.getElem_mem_toList h1)
    have hc2 : canon1 n w P.cP.pts[ij.2]! = true := hcP _ (by
      rw [getElem!_pos P.cP.pts ij.2 h2]; exact Array.getElem_mem_toList h2)
    change unpackP n w (pcomm n w P.cP.pts[ij.1]! P.cP.pts[ij.2]!) =
      commutatorA n (ArrCertP.toMain n w P.cP).pts[ij.1]! (ArrCertP.toMain n w P.cP).pts[ij.2]!
    rw [SP.pcomm_eq G hc1 hc2, ← SP.getPts (c := P.cP) h1, ← SP.getPts (c := P.cP) h2]
  obtain ⟨hPmem, hPcard, hPval⟩ := enumOK_spec (c := ArrCertP.toMain n w P.cP) hps hP'
  obtain ⟨-, hRcard, -⟩ := enumOK_spec (c := ArrCertP.toMain n w P.cR) hps hR'
  have hperf_eq : perfSubP n w ga P = closure (permsA n (gs.map (unpackP n w))) := by
    rw [perfSubP_eq, ← hgsdef]
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [hperf_eq]
    have hgsmap : gs.map (unpackP n w) =
        (P.gens.map fun gl => unpackP n w
          (ppow n w (pprod n w (gl.1.map fun l => ga[l]!)) gl.2)).toArray := by
      rw [hgsdef]; exact perf_gs_map
    rw [hgsmap]
    refine closure_le_of_rep (l := P.gens) (f := fun gl => unpackP n w
      (ppow n w (pprod n w (gl.1.map fun l => ga[l]!)) gl.2)) ?_
    intro gl hglmem
    have hglall : gl.1.all (fun l => Nat.blt l ga.size) = true :=
      List.all_eq_true.1 hgl gl hglmem
    have hcan_map : ∀ y ∈ gl.1.map (fun l => ga[l]!), canon1 n w y = true := by
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨l, hl, rfl⟩ := hy
      exact (hga l (Nat.blt_eq.mp (List.all_eq_true.1 hglall l hl))).1
    have hprod : ∃ g ∈ centDer X x, Rep n (prodA n (gl.1.map fun l => unpackP n w ga[l]!)) g := by
      apply rep_prodA
      intro a ha
      rw [List.mem_map] at ha
      obtain ⟨l, hl, rfl⟩ := ha
      exact (hga l (Nat.blt_eq.mp (List.all_eq_true.1 hglall l hl))).2
    obtain ⟨g, hg, hrep⟩ := hprod
    refine ⟨g ^ gl.2, pow_mem hg _, ?_⟩
    have hprod_eq : unpackP n w (pprod n w (gl.1.map fun l => ga[l]!)) =
        prodA n (gl.1.map fun l => unpackP n w ga[l]!) := by
      rw [(SP.pprod_eq G hcan_map).1, List.map_map]
      rfl
    rw [(SP.ppow_eq G (SP.pprod_eq G hcan_map).2 gl.2).1, hprod_eq]
    exact rep_powA hrep gl.2
  ·
    rw [hperf_eq]
    exact commutator_eq_self_of_check hps hP'
      (fun ij hij => by
        have h0 := List.all_eq_true.1 hcomms ij hij
        simp only [Bool.and_eq_true] at h0
        exact ⟨by simpa only [ArrCertP.toMain, Array.size_map] using Nat.blt_eq.mp h0.1,
          by simpa only [ArrCertP.toMain, Array.size_map] using Nat.blt_eq.mp h0.2⟩)
      (by rw [← hcomm_arr]; exact hQ')
      (by simpa only [ArrCertP.toMain, Array.size_map] using Nat.eq_of_beq_eq_true hQsize)
  ·
    intro q hq
    have hq' : q ∈ gs.toList := by rw [hgsdef]; exact hq
    have hPgs : penumOK n w gs ps P.cP = true := by rw [hgsdef]; exact hP
    constructor
    · exact hgscan q hq'
    · obtain ⟨k, hk, rfl⟩ := perf_mem_toList_get hq'
      exact pvalid_of_penumOK hPgs hk
  ·
    have hxle : P.x < P.cP.pts.size := Nat.blt_eq.mp hx
    have hxa_canon : canon1 n w xa = true := by
      rw [hxadef]
      exact hcP _ (by rw [getElem!_pos P.cP.pts P.x hxle]; exact Array.getElem_mem_toList hxle)
    have hxa_val : validA n (unpackP n w xa) = true := by
      have h0 := hPval P.x (by simpa [ArrCertP.toMain] using hxle)
      rw [SP.getPts (c := P.cP) hxle, ← hxadef] at h0
      exact h0
    have hxr : Rep n (unpackP n w xa) (toP n w xa) := rep_of_validA hxa_val
    have hxaI : (ArrCertP.toMain n w P.cP).pts[P.x]! = unpackP n w xa := by
      rw [hxadef]
      exact SP.getPts (c := P.cP) hxle
    have hxa_mem : toP n w xa ∈ closure (permsA n (gs.map (unpackP n w))) :=
      (hPmem (toP n w xa)).2 ⟨P.x, by simpa [ArrCertP.toMain] using hxle, by rw [hxaI]; rfl⟩
    have hpow : toP n w xa ^ 2 ^ P.k = 1 := by
      have h1 : unpackP n w (ppow n w xa (2 ^ P.k)) = idA n := by
        rw [Nat.eq_of_beq_eq_true hxpow, G.pid_eq]
      have h2 : powA n (unpackP n w xa) (2 ^ P.k) = idA n := by
        rwa [(SP.ppow_eq G hxa_canon (2 ^ P.k)).1] at h1
      have h3 : permOfArr n (powA n (unpackP n w xa) (2 ^ P.k)) = 1 := by
        rw [h2, permOfArr_idA]
      rwa [permOfArr_eq_of_rep (rep_powA hxr (2 ^ P.k))] at h3
    obtain ⟨b, -, hb'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
    have hy2 : IsPGroup 2 (zpowers (toP n w xa)) :=
      IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb'])
    have hmap : (P.conjs.map fun p => unpackP n w
        (pconj n w P.cP.pts[p]! (pc n w xa xa))).toArray = rs.map (unpackP n w) := by
      rw [hrsdef, List.map_toArray, List.map_map]
      rfl
    have hRle : closure (permsA n (rs.map (unpackP n w))) ≤
        closure {z | ∃ p ∈ closure (permsA n (gs.map (unpackP n w))),
          z = p * toP n w xa ^ 2 * p⁻¹} := by
      rw [← hmap]
      refine closure_le_of_rep (l := P.conjs) (f := fun p => unpackP n w
        (pconj n w P.cP.pts[p]! (pc n w xa xa))) ?_
      intro p hp
      show ∃ g ∈ closure {z | ∃ p ∈ closure (permsA n (gs.map (unpackP n w))),
          z = p * toP n w xa ^ 2 * p⁻¹},
        Rep n (unpackP n w (pconj n w P.cP.pts[p]! (pc n w xa xa))) g
      have hp' : p < P.cP.pts.size := Nat.blt_eq.mp (List.all_eq_true.1 hconjs p hp)
      have hcp : canon1 n w P.cP.pts[p]! = true := hcP _ (by
        rw [getElem!_pos P.cP.pts p hp']; exact Array.getElem_mem_toList hp')
      have hvalp : validA n (unpackP n w P.cP.pts[p]!) = true := by
        have h0 := hPval p (by simpa [ArrCertP.toMain] using hp')
        rwa [SP.getPts (c := P.cP) hp'] at h0
      have hf : unpackP n w (pconj n w P.cP.pts[p]! (pc n w xa xa)) =
          conjA n (unpackP n w P.cP.pts[p]!)
            (compA n (unpackP n w xa) (unpackP n w xa)) := by
        rw [SP.pconj_eq G hcp (SP.canon_pc G.hn G.hw), SP.pc_eq G hxa_canon]
      rw [hf]
      refine ⟨toP n w P.cP.pts[p]! * toP n w xa ^ 2 * (toP n w P.cP.pts[p]!)⁻¹,
        subset_closure ⟨toP n w P.cP.pts[p]!, (hPmem _).2
          ⟨p, by simpa [ArrCertP.toMain] using hp',
            by rw [SP.getPts (c := P.cP) hp']; rfl⟩, rfl⟩, ?_⟩
      rw [sq]
      exact rep_conjA hvalp (rep_compA hxr hxr)
    have hRP : closure (permsA n (rs.map (unpackP n w))) ≤
        closure (permsA n (gs.map (unpackP n w))) := by
      rw [← hmap]
      refine closure_le_of_rep (l := P.conjs) (f := fun p => unpackP n w
        (pconj n w P.cP.pts[p]! (pc n w xa xa))) ?_
      intro p hp
      show ∃ g ∈ closure (permsA n (gs.map (unpackP n w))),
        Rep n (unpackP n w (pconj n w P.cP.pts[p]! (pc n w xa xa))) g
      have hp' : p < P.cP.pts.size := Nat.blt_eq.mp (List.all_eq_true.1 hconjs p hp)
      have hcp : canon1 n w P.cP.pts[p]! = true := hcP _ (by
        rw [getElem!_pos P.cP.pts p hp']; exact Array.getElem_mem_toList hp')
      have hvalp : validA n (unpackP n w P.cP.pts[p]!) = true := by
        have h0 := hPval p (by simpa [ArrCertP.toMain] using hp')
        rwa [SP.getPts (c := P.cP) hp'] at h0
      have hpmem : toP n w P.cP.pts[p]! ∈ closure (permsA n (gs.map (unpackP n w))) :=
        (hPmem _).2 ⟨p, by simpa [ArrCertP.toMain] using hp',
          by rw [SP.getPts (c := P.cP) hp']; rfl⟩
      have hf : unpackP n w (pconj n w P.cP.pts[p]! (pc n w xa xa)) =
          conjA n (unpackP n w P.cP.pts[p]!)
            (compA n (unpackP n w xa) (unpackP n w xa)) := by
        rw [SP.pconj_eq G hcp (SP.canon_pc G.hn G.hw), SP.pc_eq G hxa_canon]
      rw [hf]
      exact ⟨toP n w P.cP.pts[p]! * (toP n w xa * toP n w xa) * (toP n w P.cP.pts[p]!)⁻¹,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hpmem (Subgroup.mul_mem _ hxa_mem hxa_mem))
          (Subgroup.inv_mem _ hpmem),
        rep_conjA hvalp (rep_compA hxr hxr)⟩
    have hRe : closure (permsA n (rs.map (unpackP n w))) =
        closure (permsA n (gs.map (unpackP n w))) := by
      refine eq_of_le_of_card_ge hRP ?_
      rw [hPcard, hRcard]
      simp only [ArrCertP.toMain, Array.size_map]
      exact Nat.le_of_eq (Nat.eq_of_beq_eq_true hRsize).symm
    refine ⟨toP n w xa, ?_, hy2, ?_⟩
    · rw [hperf_eq]; exact hxa_mem
    · rw [hperf_eq]
      rw [hRe] at hRle
      exact hRle

private theorem cand_perf_spec {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonR n w r = true)
    (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true)
    (X : Subgroup (Equiv.Perm (Fin n))) (hps : ∀ p ∈ ps, p < n)
    (hsX : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
      permOfArr n (unpackP n w P) ∈ X)
    {b : Nat} (hcb : canon1 n w b = true) (hvb : pvalid n w b = true)
    (hb2 : toP n w b ^ 2 = 1) (hb1 : toP n w b ≠ 1) (hbx : toP n w b ≠ toP n w r.x)
    {l : Nat} (hin : RootWitP.inRange r (.perf l) = true)
    (hcand : pcandOK n w inXP r.x r.ga r.gi (r.perfs.map (pperfGens n w r.ga)) b
      (.perf l) = true) :
    MonoW X pw (closure {toP n w r.x, toP n w b}) := by
  have hin' : l < r.perfs.size := by
    have h0 := hin
    simp only [RootWitP.inRange, Nat.blt_eq] at h0
    exact h0
  have hpw0 : (pw || Nat.beq r.perfs.size 0) = true := by
    have h' := h; simp only [prootConjOKB, Bool.and_eq_true] at h'; tauto
  have hperfs : r.perfs.toList.all (pperfOK n w ps r.ga) = true := by
    have h' := h; simp only [prootConjOKB, Bool.and_eq_true] at h'; tauto
  have hgas : Nat.beq r.ga.size r.gams.size = true := by
    have h' := h; simp only [prootConjOKB, Bool.and_eq_true] at h'; tauto
  have hpw : pw = true := by
    rw [Bool.or_eq_true] at hpw0
    rcases hpw0 with h0 | h0
    · exact h0
    · have : r.perfs.size = 0 := Nat.eq_of_beq_eq_true h0
      omega
  have hga_canon : ∀ j < r.ga.size, canon1 n w r.ga[j]! = true := by
    intro j hj
    have h0 : r.ga.toList.all (canon1 n w) = true := by
      have hc' := hc
      simp only [canonR, Bool.and_eq_true] at hc'
      tauto
    have hmem : r.ga[j]! ∈ r.ga.toList := by
      rw [getElem!_pos r.ga j hj]; exact Array.getElem_mem_toList hj
    exact List.all_eq_true.1 h0 _ hmem
  have hPl_mem : r.perfs[l]! ∈ r.perfs.toList := by
    rw [getElem!_pos r.perfs l hin']; exact Array.getElem_mem_toList hin'
  have hcan_perfs : r.perfs.toList.all (fun P =>
      P.cP.pts.toList.all (canon1 n w) && P.cQ.pts.toList.all (canon1 n w) &&
        P.cR.pts.toList.all (canon1 n w)) = true := by
    have hc' := hc
    simp only [canonR, Bool.and_eq_true] at hc'
    tauto
  have hPcan := List.all_eq_true.1 hcan_perfs (r.perfs[l]!) hPl_mem
  have hcP : ∀ q ∈ (r.perfs[l]!).cP.pts.toList, canon1 n w q = true :=
    List.all_eq_true.1 (by simp only [Bool.and_eq_true] at hPcan; tauto)
  have hcQ : ∀ q ∈ (r.perfs[l]!).cQ.pts.toList, canon1 n w q = true :=
    List.all_eq_true.1 (by simp only [Bool.and_eq_true] at hPcan; tauto)
  have hcR : ∀ q ∈ (r.perfs[l]!).cR.pts.toList, canon1 n w q = true :=
    List.all_eq_true.1 (by simp only [Bool.and_eq_true] at hPcan; tauto)
  have hga : ∀ j < r.ga.size, canon1 n w r.ga[j]! = true ∧
      ∃ Γ ∈ centDer X (toP n w r.x), Rep n (unpackP n w r.ga[j]!) Γ := by
    intro j hj
    refine ⟨hga_canon j hj, ?_⟩
    have hj' : j < r.gams.size := by
      have h0 : r.ga.size = r.gams.size := Nat.eq_of_beq_eq_true hgas
      omega
    obtain ⟨Γ, hΓ, hrep, -⟩ := gam_specP hn hw hc h X hsX hj'
    exact ⟨Γ, hΓ, hrep⟩
  have G : SP.Good n w := (good_of_check hn hw hc h).1
  have hPl : pperfOK n w ps r.ga r.perfs[l]! = true :=
    List.all_eq_true.1 hperfs (r.perfs[l]!) hPl_mem
  obtain ⟨hPΓ, hperf, hgens, y, hyP, hy2, hgen⟩ :=
    pperfOK_spec G hps hga hcP hcQ hcR hPl
  have hcand' := hcand
  simp only [pcandOK] at hcand'
  rw [SP.map_get (pperfGens n w r.ga) r.perfs hin'] at hcand'
  rw [List.any_eq_true] at hcand'
  obtain ⟨g, hg, hgc⟩ := hcand'
  have hgcf : pcommA n w b g = false := by simpa only [Bool.not_eq_true'] using hgc
  have hgcan : canon1 n w g = true := (hgens g hg).1
  have hgpv : pvalid n w g = true := (hgens g hg).2
  have hgmem : toP n w g ∈ perfSubP n w r.ga (r.perfs[l]!) :=
    subset_closure ⟨g, hg, rfl⟩
  have hx1 : toP n w r.x ≠ 1 := (x_facts hn hw hc h).2.2.2
  have hnotle : ¬ closure {toP n w r.x, toP n w b} ≤
      centralizer (perfSubP n w r.ga (r.perfs[l]!) : Set (Equiv.Perm (Fin n))) := by
    intro hVC
    have hbV : toP n w b ∈ closure {toP n w r.x, toP n w b} := subset_closure (by simp)
    have hcomm := mem_centralizer_iff.mp (hVC hbV) (toP n w g) hgmem
    have hpcbq : toP n w (pc n w b g) = toP n w b * toP n w g :=
      toP_pc hn hw hcb hgcan hvb hgpv
    have hpcqb : toP n w (pc n w g b) = toP n w g * toP n w b :=
      toP_pc hn hw hgcan hcb hgpv hvb
    have hcpcbq : canon1 n w (pc n w b g) = true := SP.canon_pc hn hw
    have hcpcqb : canon1 n w (pc n w g b) = true := SP.canon_pc hn hw
    have hpv_pcbq : pvalid n w (pc n w b g) = true := pvalid_pc hn hw hcb hvb hgcan hgpv
    have hpv_pcqb : pvalid n w (pc n w g b) = true := pvalid_pc hn hw hgcan hgpv hcb hvb
    have heq : toP n w (pc n w b g) = toP n w (pc n w g b) := by
      rw [hpcbq, hpcqb]; exact hcomm.symm
    have hpc_eq : pc n w b g = pc n w g b :=
      toP_inj hw hcpcbq hpv_pcbq hcpcqb hpv_pcqb heq
    have htrue : pcommA n w b g = true := by simp only [pcommA, hpc_eq, Nat.beq_refl]
    rw [hgcf] at htrue
    exact Bool.noConfusion htrue
  refine Or.inr ⟨hpw, perfSubP n w r.ga (r.perfs[l]!), ?_, hperf, hnotle, y, hyP, hy2, hgen⟩
  exact hPΓ.trans (le_iSup₂_of_le (toP n w r.x) (subset_closure (by simp))
    (le_iSup_of_le hx1 le_rfl))

private theorem kb_lt_of_canonR {r : RootConjP} (hc : canonR n w r = true) :
    ∀ p ∈ r.kb, p < n := by
  intro p hp
  have hcanR := hc
  simp only [canonR, Bool.and_eq_true] at hcanR
  have hkb : r.kb.all (fun q => Nat.blt q n) = true := by tauto
  exact Nat.blt_eq.mp (List.all_eq_true.mp hkb p hp)

private theorem pcandOK_spec {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonR n w r = true)
    (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true)
    (X : Subgroup (Equiv.Perm (Fin n))) (hps : ∀ p ∈ ps, p < n)
    (hsX : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
      permOfArr n (unpackP n w P) ∈ X)
    {b : Nat} (hcb : canon1 n w b = true) (hvb : pvalid n w b = true)
    (hb2 : toP n w b ^ 2 = 1) (hb1 : toP n w b ≠ 1) (hbx : toP n w b ≠ toP n w r.x)
    {c : Nat} (hcl : c < r.cands.size)
    (hcand : pcandOK n w inXP r.x r.ga r.gi (r.perfs.map (pperfGens n w r.ga)) b
      r.cands[c]! = true) :
    MonoW X pw (closure {toP n w r.x, toP n w b}) := by
  have h' := h
  simp only [prootConjOKB, Bool.and_eq_true] at h'
  have hc' := hc
  simp only [canonR, Bool.and_eq_true] at hc'
  have hmem : r.cands[c]! ∈ r.cands.toList := by
    rw [getElem!_pos r.cands c hcl]
    exact Array.getElem_mem_toList hcl
  have hinAll : r.cands.toList.all (RootWitP.inRange r) = true := by tauto
  have hcanAll : r.cands.toList.all (canonWitP n w) = true := by tauto
  have hin : RootWitP.inRange r r.cands[c]! = true := List.all_eq_true.1 hinAll _ hmem
  have hcan : canonWitP n w r.cands[c]! = true := List.all_eq_true.1 hcanAll _ hmem
  cases hcc : r.cands[c]! with
  | perf l =>
      rw [hcc] at hin hcan hcand
      exact cand_perf_spec hn hw hc h X hps hsX hcb hvb hb2 hb1 hbx hin hcand
  | ord4 l m =>
      rw [hcc] at hin hcan hcand
      exact cand_ord4_spec hn hw hc h X hps hsX hcb hvb hb2 hb1 hbx hin hcand
  | ord4p ls m =>
      rw [hcc] at hin hcan hcand
      exact cand_ord4p_spec hn hw hc h X hps hsX hcb hvb hb2 hb1 hbx hin hcand
  | ord4c e c₁ c₂ m =>
      rw [hcc] at hin hcan hcand
      exact cand_ord4c_spec hn hw hc h X hps hsX hcb hvb hb2 hb1 hbx hcan hcand

private theorem leaf_spec {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonR n w r = true)
    (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true)
    (X : Subgroup (Equiv.Perm (Fin n))) (hps : ∀ p ∈ ps, p < n)
    (hsX : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
      permOfArr n (unpackP n w P) ∈ X)
    (hgk : toP n w r.xs[k]! ∉ X) {j : Nat} (hj : j < usize r.ukc) (h0 : (r.e j).1 = 0) :
    LeafConcl X pw bmode skip (toP n w r.x) (uPerm n w r j) := by
  have h' := h
  simp only [prootConjOKB, Bool.and_eq_true] at h'
  have hc' := hc
  simp only [canonR, Bool.and_eq_true] at hc'
  have hcx : canon1 n w r.x = true := by tauto
  have hcanxs : r.xs.all (canon1 n w) = true := by tauto
  have hpvx : pvalid n w r.x = true := by tauto
  have hppcOK : ppcOK n w r.xs r.rs r.cjs r.bs = true := by tauto
  have hblt : Nat.blt k r.xs.length = true := by tauto
  have hinXi : ((List.range r.xs.length).all fun i => Nat.beq i k || inXP r.xs[i]!) = true := by
    tauto
  have hentries : (List.range (usize r.ukc)).all
      (pentryOKB n w inXP bmode skip (r.perfs.map (pperfGens n w r.ga)) k r) = true := by tauto
  have hk : k < r.xs.length := Nat.blt_eq.mp hblt
  have hpv_all := pvalid_of_ppcOK hppcOK
  have hne : r.xs ≠ [] := by intro hnil; rw [hnil] at hk; simp at hk
  have hpid := unpackP_pid_of_ppcOK hn hw hcanxs hppcOK hne
  have hpvpid : pvalid n w (pid n w) = true := pvalid_pid_of_ppcOK hn hw hcanxs hppcOK hne
  have hcpid : canon1 n w (pid n w) = true := (SP.pid_good hw hpvpid).2
  have hentry := List.all_eq_true.1 hentries j (List.mem_range.mpr hj)
  rcases pentryOKB_spec hentry with ⟨-, -, hpinvol, hcl, hleaf⟩ | ⟨hne0, -⟩
  · let a := (r.e j).2.1
    let b := ppcA n w r.xs a
    let o := Nat.land (Nat.shiftRight a k) 1
    have hcb : canon1 n w b = true := canon1_ppcA hn hw hcpid a
    have hvb : pvalid n w b = true := pvalid_ppcA hn hw hcanxs hpv_all hcpid hpvpid a
    have htoPb : toP n w b = pcG (r.xs.map (fun x => toP n w x)) a :=
      toP_ppcA hn hw hcanxs hpv_all hpid hcpid hpvpid a
    have hlt : ∀ i (hi : i < (r.xs.map (fun x => toP n w x)).length), i ≠ k →
        (r.xs.map (fun x => toP n w x))[i] ∈ X := by
      intro i hi hik
      have hi' : i < r.xs.length := by simpa using hi
      have hxcan : canon1 n w r.xs[i] = true :=
        List.all_eq_true.1 hcanxs _ (List.getElem_mem hi')
      have hxpv : pvalid n w r.xs[i] = true := hpv_all _ (List.getElem_mem hi')
      have hxinx : inXP r.xs[i] = true := by
        have hc0 := List.all_eq_true.1 hinXi i (List.mem_range.mpr hi')
        simp only [Bool.or_eq_true, Nat.beq_eq] at hc0
        rcases hc0 with hik' | hinx
        · exact absurd hik' hik
        · rwa [getElem!_pos r.xs i hi'] at hinx
      have hmemX := hsX r.xs[i] hxcan hxpv hxinx
      rw [List.getElem_map]
      exact hmemX
    have hklen : k < (r.xs.map (fun x => toP n w x)).length := by simpa using hk
    have hknot : (r.xs.map (fun x => toP n w x))[k]'hklen ∉ X := by
      intro hmem
      apply hgk
      rw [List.getElem_map] at hmem
      rwa [getElem!_pos r.xs k hk]
    have hmem_iff : toP n w b ∈ X ↔ o = 0 := by
      rw [htoPb]
      exact pcG_mem_iff_bit (l := r.xs.map (fun x => toP n w x)) (k := k)
        hklen hlt hknot a
    rw [uPerm_of_rep h0]
    simp only [LeafConcl]
    intro hb2 hb1 hbx hbm1 hbm2
    have hleaf' := hleaf
    simp only [pleafOKB, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_true_eq, or_assoc] at hleaf'
    rcases hleaf' with ⟨hbm1', ho1⟩ | ⟨hbm2', ho0⟩ | hnot | hbeq | hfix | hfix2 | hcand
    · have hbX : toP n w b ∈ X := hbm1 hbm1'
      have ho0 : o = 0 := hmem_iff.mp hbX
      have ho0' : ((r.e j).2.1.shiftRight k).land 1 = 0 := ho0
      rw [ho1] at ho0'
      exact absurd ho0' (by decide)
    · have hbX : toP n w b ∈ X := hmem_iff.mpr ho0
      exact absurd hbX (hbm2 hbm2')
    · rw [hnot] at hpinvol
      exact absurd hpinvol (by decide)
    · exact absurd (congrArg (toP n w) hbeq) hbx
    · exact Or.inr (Or.inl (by rwa [toP_fixP hw hcb hvb]))
    · have hcan_pc : canon1 n w (pc n w r.x b) = true := SP.canon_pc hn hw
      have hpv_pc : pvalid n w (pc n w r.x b) = true := pvalid_pc hn hw hcx hpvx hcb hvb
      have htoP_pc : toP n w (pc n w r.x b) = toP n w r.x * toP n w b :=
        toP_pc hn hw hcx hcb hpvx hvb
      exact Or.inr (Or.inr (by rw [← htoP_pc, toP_fixP hw hcan_pc hpv_pc]; exact hfix2))
    · exact Or.inl (pcandOK_spec hn hw hc h X hps hsX hcb hvb hb2 hb1 hbx hcl hcand)
  · exact absurd h0 hne0

private theorem uPerm_leaf {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {W : Subgroup (Equiv.Perm (Fin n))} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hsW : ∀ P, canon1 n w P = true → pvalid n w P = true → inWP P = true →
      permOfArr n (unpackP n w P) ∈ W)
    (hc : canonR n w r = true) (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true)
    (X : Subgroup (Equiv.Perm (Fin n))) (hXW : X ≤ W) (hXN : (X.subgroupOf W).Normal)
    (hps : ∀ p ∈ ps, p < n)
    (hsX : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
      permOfArr n (unpackP n w P) ∈ X)
    (hgk : toP n w r.xs[k]! ∉ X) :
    ∀ j < usize r.ukc, LeafConcl X pw bmode skip (toP n w r.x) (uPerm n w r j) := by
  have h' := h
  simp only [prootConjOKB, Bool.and_eq_true] at h'
  have hc' := hc
  simp only [canonR, Bool.and_eq_true] at hc'
  have hcanxs : r.xs.all (canon1 n w) = true := by tauto
  have hppcOK : ppcOK n w r.xs r.rs r.cjs r.bs = true := by tauto
  have hcomm : (r.xs.all fun g => pcommA n w g r.x && inWP g) = true := by tauto
  have hentries : (List.range (usize r.ukc)).all
      (pentryOKB n w inXP bmode skip (r.perfs.map (pperfGens n w r.ga)) k r) = true := by tauto
  have hpv_all := pvalid_of_ppcOK hppcOK
  have key : ∀ d, ∀ j < usize r.ukc, (r.e j).2.2.2 = d →
      LeafConcl X pw bmode skip (toP n w r.x) (uPerm n w r j) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro j hj hd
      have hentry := List.all_eq_true.1 hentries j (List.mem_range.mpr hj)
      rcases pentryOKB_spec hentry with ⟨h0, -, -, -, -⟩ | ⟨hne0, ha_lt, hda, hb_lt⟩
      · exact leaf_spec hn hw hc h X hps hsX hgk hj h0
      · let a := (r.e j).2.1
        let b' := (r.e j).2.2.1
        let t := toP n w r.xs[b']!
        have hlt_d : (r.e a).2.2.2 < d := by
          rw [← hd, hda]
          exact Nat.lt_succ_self _
        have ih_a : LeafConcl X pw bmode skip (toP n w r.x) (uPerm n w r a) :=
          ih ((r.e a).2.2.2) hlt_d a ha_lt rfl
        have hmem_b' : r.xs[b']! ∈ r.xs := by
          rw [getElem!_pos r.xs b' hb_lt]
          exact List.getElem_mem hb_lt
        have hcan_t : canon1 n w r.xs[b']! = true := by
          rw [getElem!_pos r.xs b' hb_lt]
          exact List.all_eq_true.1 hcanxs _ (List.getElem_mem hb_lt)
        have hpv_t : pvalid n w r.xs[b']! = true := by
          rw [getElem!_pos r.xs b' hb_lt]
          exact hpv_all _ (List.getElem_mem hb_lt)
        have hc0 := List.all_eq_true.1 hcomm _ hmem_b'
        simp only [Bool.and_eq_true] at hc0
        have hcommx : pcommA n w r.xs[b']! r.x = true := hc0.1
        have hinWP_t : inWP r.xs[b']! = true := hc0.2
        have htW : t ∈ W := hsW (r.xs[b']!) hcan_t hpv_t hinWP_t
        have hXt : X.map (MulAut.conj t).toMonoidHom = X :=
          map_conj_eq_of_normal htW hXW hXN
        have hcx : canon1 n w r.x = true := by tauto
        have hpvx : pvalid n w r.x = true := by tauto
        have htx : t * toP n w r.x * t⁻¹ = toP n w r.x := by
          have hpc_eq : pc n w (r.xs[b']!) r.x = pc n w r.x (r.xs[b']!) :=
            Nat.eq_of_beq_eq_true hcommx
          rw [show t = toP n w r.xs[b']! from rfl]
          rw [← toP_pc hn hw hcan_t hcx hpv_t hpvx, hpc_eq,
            toP_pc hn hw hcx hcan_t hpvx hpv_t, mul_assoc, mul_inv_cancel, mul_one]
        rw [uPerm_of_conj (r := r) (j := j) hne0 hda]
        exact leafConcl_conj hXt htx ih_a
  intro j hj
  exact key ((r.e j).2.2.2) j hj rfl

private theorem rootConjB_facts_gap_mono {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {W : Subgroup (Equiv.Perm (Fin n))} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hkb : ∀ p ∈ r.kb, p < n)
    (hsW : ∀ P, canon1 n w P = true → pvalid n w P = true → inWP P = true →
      permOfArr n (unpackP n w P) ∈ W)
    (hc : canonR n w r = true) (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true)
    (X : Subgroup (Equiv.Perm (Fin n))) (hXW : X ≤ W) (hXN : (X.subgroupOf W).Normal)
    (hps : ∀ p ∈ ps, p < n)
    (hsX : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
      permOfArr n (unpackP n w P) ∈ X)
    (hgk : toP n w r.xs[k]! ∉ X) :
    ∀ b ∈ (closure {a | a ∈ r.xs.map (fun x => toP n w x)} :
        Subgroup (Equiv.Perm (Fin n))),
      b ^ 2 = 1 → b ≠ 1 → b ≠ toP n w r.x →
        (bmode = 1 → b ∈ X) → (bmode = 2 → b ∉ X) →
        MonoW X pw (closure {toP n w r.x, b}) ∨ fixP b ∈ skip ∨
          fixP (toP n w r.x * b) ∈ skip := by
  intro b hbT hb2 hb1 hbx hbm1 hbm2
  obtain ⟨j, hj, hu⟩ := exists_uPerm_eq hn hw hkb hc h b hbT hb2 hb1
  subst b
  exact uPerm_leaf hn hw hsW hc h X hXW hXN hps hsX hgk j hj hb2 hb1 hbx hbm1 hbm2

private theorem rootConjB_facts_gap {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool}
    {bmode : Nat} {skip : List Nat} {k : Nat} {W : Subgroup (Equiv.Perm (Fin n))} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hsW : ∀ P, canon1 n w P = true → pvalid n w P = true → inWP P = true →
      permOfArr n (unpackP n w P) ∈ W)
    (hc : canonR n w r = true) (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true) :
    permOfArr n (unpackP n w r.x) ^ 2 = 1 ∧
      permOfArr n (unpackP n w r.x) ≠ 1 ∧
      fixP (permOfArr n (unpackP n w r.x)) = pfix n w r.x ∧
      ∃ T : Subgroup (Equiv.Perm (Fin n)), T ≤ W ⊓ centralizer {permOfArr n (unpackP n w r.x)} ∧
        Nat.card T = 2 ^ r.xs.length ∧ permOfArr n (unpackP n w r.xs[k]!) ∈ T ∧
        ∀ X : Subgroup (Equiv.Perm (Fin n)), X ≤ W → (X.subgroupOf W).Normal →
          (∀ p ∈ ps, p < n) →
          (∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
            permOfArr n (unpackP n w P) ∈ X) →
          (permOfArr n (unpackP n w r.xs[k]!) ∈ X → T ≤ X) ∧
          (permOfArr n (unpackP n w r.xs[k]!) ∉ X →
            ∀ b ∈ T, b ^ 2 = 1 → b ≠ 1 → b ≠ permOfArr n (unpackP n w r.x) →
              (bmode = 1 → b ∈ X) → (bmode = 2 → b ∉ X) →
              MonoW X pw (closure {permOfArr n (unpackP n w r.x), b}) ∨ fixP b ∈ skip ∨
                fixP (permOfArr n (unpackP n w r.x) * b) ∈ skip) := by
  have hcanR := hc
  simp only [canonR, Bool.and_eq_true] at hcanR
  have hcx : canon1 n w r.x = true := by tauto
  have hcanxs : r.xs.all (canon1 n w) = true := by tauto
  have h' := h
  simp only [prootConjOKB, Bool.and_eq_true] at h'
  have hpvx : pvalid n w r.x = true := by tauto
  have hinvol : pinvol n w r.x = true := by tauto
  have hppcOK : ppcOK n w r.xs r.rs r.cjs r.bs = true := by tauto
  have hblt : Nat.blt k r.xs.length = true := by tauto
  have hcomm : (r.xs.all fun g => pcommA n w g r.x && inWP g) = true := by tauto
  have hinXi : ((List.range r.xs.length).all fun i => Nat.beq i k || inXP r.xs[i]!) = true := by
    tauto
  have hpv_all := pvalid_of_ppcOK hppcOK
  have hk : k < r.xs.length := Nat.blt_eq.mp hblt
  have hne : r.xs ≠ [] := by
    intro hnil; rw [hnil] at hk; simp at hk
  have hpid := unpackP_pid_of_ppcOK hn hw hcanxs hppcOK hne
  have hpcOK := pcOK_of_ppcOK hn hw hcanxs hpv_all hpid hppcOK
  obtain ⟨-, hrel, hsep⟩ := pc_of_pcOK hpcOK
  have hmap : (r.xs.map (unpackP n w)).map (permOfArr n) = r.xs.map (fun x => toP n w x) := by
    rw [List.map_map]; rfl
  have hrel' : PcRel (r.xs.map (fun x => toP n w x)) := by rwa [hmap] at hrel
  have hsep' : PcSep (r.xs.map (fun x => toP n w x)) := by rwa [hmap] at hsep
  let T : Subgroup (Equiv.Perm (Fin n)) := closure {a | a ∈ r.xs.map (fun x => toP n w x)}
  have hTdef : T = closure {a | a ∈ r.xs.map (fun x => toP n w x)} := rfl
  have hcardT : Nat.card T = 2 ^ r.xs.length := by
    have hlen : (r.xs.map (fun x => toP n w x)).length = r.xs.length := by simp
    rw [hTdef, ← hlen]
    exact card_closure_of_pc hrel' hsep'
  have hTW : T ≤ W := by
    rw [hTdef, closure_le]
    intro g hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
    have hxcan : canon1 n w x = true := List.all_eq_true.1 hcanxs x hx
    have hxpv : pvalid n w x = true := hpv_all x hx
    have hxinW : inWP x = true := by
      have hc0 := List.all_eq_true.1 hcomm x hx
      simp only [Bool.and_eq_true] at hc0
      exact hc0.2
    exact hsW x hxcan hxpv hxinW
  have hTc : T ≤ centralizer ({toP n w r.x} : Set (Equiv.Perm (Fin n))) := by
    rw [hTdef, closure_le]
    intro g hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have hxcan : canon1 n w x = true := List.all_eq_true.1 hcanxs x hx
    have hxpv : pvalid n w x = true := hpv_all x hx
    have hxpc : pcommA n w x r.x = true := by
      have hc0 := List.all_eq_true.1 hcomm x hx
      simp only [Bool.and_eq_true] at hc0
      exact hc0.1
    have hpc_eq : pc n w x r.x = pc n w r.x x := Nat.eq_of_beq_eq_true hxpc
    rw [← toP_pc hn hw hxcan hcx hxpv hpvx, hpc_eq, toP_pc hn hw hcx hxcan hpvx hxpv]
  have hxsk_mem : toP n w (r.xs[k]!) ∈ T := by
    rw [hTdef]
    refine subset_closure ?_
    rw [Set.mem_setOf_eq, List.mem_map]
    have hmem : r.xs[k]! ∈ r.xs := by
      rw [getElem!_pos r.xs k hk]; exact List.getElem_mem hk
    exact ⟨r.xs[k]!, hmem, rfl⟩
  have hinvol' := hinvol
  simp only [pinvol, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at hinvol'
  have hpc_xx : pc n w r.x r.x = pid n w := hinvol'.1
  have hne_pid : r.x ≠ pid n w := beq_eq_false_iff_ne.mp hinvol'.2
  have hpvpid : pvalid n w (pid n w) = true := pvalid_pid_of_ppcOK hn hw hcanxs hppcOK hne
  have hcpid : canon1 n w (pid n w) = true := (SP.pid_good hw hpvpid).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact toP_sq_one hn hw hcx hpvx hpc_xx hpid
  · exact toP_ne_one hw hcx hpvx hpid hcpid hpvpid hne_pid
  · exact toP_fixP hw hcx hpvx
  · refine ⟨T, ?_, ?_, ?_, ?_⟩
    · exact le_inf hTW hTc
    · exact hcardT
    · exact hxsk_mem
    · intro X hXW hXN hps hsX
      refine ⟨?_, ?_⟩
      · intro hgk
        rw [hTdef, closure_le]
        intro g hg
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
        have hxcan : canon1 n w x = true := List.all_eq_true.1 hcanxs x hx
        have hxpv : pvalid n w x = true := hpv_all x hx
        by_cases hxeq : x = r.xs[k]!
        · rw [hxeq]; exact hgk
        · have hinx : inXP x = true := by
            obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
            have hc0 := List.all_eq_true.1 hinXi i (List.mem_range.mpr hi)
            simp only [Bool.or_eq_true, Nat.beq_eq] at hc0
            rcases hc0 with hik | hinx
            · exfalso; apply hxeq
              have hix! : r.xs[i]! = x := by rw [getElem!_pos r.xs i hi]; exact hix
              rw [← hix!, hik]
            · rwa [getElem!_pos r.xs i hi, hix] at hinx
          exact hsX x hxcan hxpv hinx
      · intro hgk b hbT hb2 hb1 hbx hbm1 hbm2
        exact rootConjB_facts_gap_mono hn hw (kb_lt_of_canonR hc) hsW hc h X hXW hXN hps hsX hgk
          b hbT hb2 hb1 hbx hbm1 hbm2

theorem rootConjB_facts {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool} {bmode : Nat}
    {skip : List Nat} {k : Nat} {W : Subgroup (Equiv.Perm (Fin n))} {r : RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hsW : ∀ P, canon1 n w P = true → pvalid n w P = true → inWP P = true →
      permOfArr n (unpackP n w P) ∈ W)
    (hc : canonR n w r = true) (h : prootConjOKB n w ps inXP inWP pw bmode skip k r = true) :
    permOfArr n (unpackP n w r.x) ∈ W ∧ permOfArr n (unpackP n w r.x) ^ 2 = 1 ∧
      permOfArr n (unpackP n w r.x) ≠ 1 ∧
      fixP (permOfArr n (unpackP n w r.x)) = pfix n w r.x ∧
      ∃ T : Subgroup (Equiv.Perm (Fin n)), T ≤ W ⊓ centralizer {permOfArr n (unpackP n w r.x)} ∧
        Nat.card T = 2 ^ r.xs.length ∧ permOfArr n (unpackP n w r.xs[k]!) ∈ T ∧
        ∀ X : Subgroup (Equiv.Perm (Fin n)), X ≤ W → (X.subgroupOf W).Normal →
          (∀ p ∈ ps, p < n) →
          (∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
            permOfArr n (unpackP n w P) ∈ X) →
          (permOfArr n (unpackP n w r.xs[k]!) ∈ X → T ≤ X) ∧
          (permOfArr n (unpackP n w r.xs[k]!) ∉ X →
            ∀ b ∈ T, b ^ 2 = 1 → b ≠ 1 → b ≠ permOfArr n (unpackP n w r.x) →
              (bmode = 1 → b ∈ X) → (bmode = 2 → b ∉ X) →
              MonoW X pw (closure {permOfArr n (unpackP n w r.x), b}) ∨ fixP b ∈ skip ∨
                fixP (permOfArr n (unpackP n w r.x) * b) ∈ skip) := by
  have hxW : permOfArr n (unpackP n w r.x) ∈ W := by
    have hc' := hc
    have h' := h
    simp only [canonR, Bool.and_eq_true] at hc'
    simp only [prootConjOKB, Bool.and_eq_true] at h'
    exact hsW r.x (by tauto) (by tauto) (by tauto)
  obtain ⟨h2, h3, h4, h5⟩ := rootConjB_facts_gap hn hw hsW hc h
  exact ⟨hxW, h2, h3, h4, h5⟩

theorem roots_in_W_conjB {ps : List Nat} {inXP inWP : Nat → Bool} {pw : Bool} {bmode : Nat}
    {X W : Subgroup (Equiv.Perm (Fin n))} {ks : List Nat} {rs : List RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hXW : X ≤ W) (hN : (X.subgroupOf W).Normal)
    (hps : ∀ p ∈ ps, p < n)
    (hsX : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
      permOfArr n (unpackP n w P) ∈ X)
    (hsW : ∀ P, canon1 n w P = true → pvalid n w P = true → inWP P = true →
      permOfArr n (unpackP n w P) ∈ W)
    (hc : rs.all (canonR n w) = true) (h : prootsConjOKB n w ps inXP inWP pw bmode ks rs = true)
    (hsyl : ∀ i < rs.length, rs[i]!.xs.length =
      (Nat.card ↥(W ⊓ centralizer {permOfArr n (unpackP n w rs[i]!.x)})).factorization 2)
    (hfix : ∀ g ∈ W, g ^ 2 = 1 → g ≠ 1 → ∀ j < rs.length,
      fixP g = fixP (permOfArr n (unpackP n w rs[j]!.x)) →
        ∃ v ∈ W, v * g * v⁻¹ = permOfArr n (unpackP n w rs[j]!.x))
    (hout : ∀ i < rs.length, permOfArr n (unpackP n w rs[i]!.xs[ks[i]!]!) ∉ X) :
    ∃ (x : ℕ → ↥W) (T : ℕ → Subgroup ↥W),
      (∀ i < rs.length, ((x i : ↥W) : Equiv.Perm (Fin n)) = permOfArr n (unpackP n w rs[i]!.x)) ∧
      (∀ i < rs.length, IsSylowOf 2 (T i) (centralizer {x i})) ∧
      ∀ i < rs.length, ∀ b ∈ T i, b ^ 2 = 1 → b ≠ 1 → b ≠ x i →
        (bmode = 1 → b ∈ X.subgroupOf W) → (bmode = 2 → b ∉ X.subgroupOf W) →
        MonoW (X.subgroupOf W) pw (closure {x i, b}) ∨
          ∃ j < i, IsConj b (x j) ∨ IsConj (x i * b) (x j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold prootsConjOKB at h
  rw [Bool.and_eq_true] at h
  have hspec : ∀ i < rs.length, _ := fun i hi => rootConjB_facts hn hw hsW
    (List.all_eq_true.mp hc _ (by rw [getElem!_pos rs i hi]; exact List.getElem_mem hi))
    (List.all_eq_true.mp h.2 i (List.mem_range.mpr hi))
  let x : ℕ → ↥W := fun i =>
    if hi : i < rs.length then ⟨permOfArr n (unpackP n w rs[i]!.x), (hspec i hi).1⟩ else 1
  have hx : ∀ i (hi : i < rs.length),
      ((x i : ↥W) : Equiv.Perm (Fin n)) = permOfArr n (unpackP n w rs[i]!.x) :=
    fun i hi => by simp only [x, hi, dite_true]
  let T₀ : ℕ → Subgroup (Equiv.Perm (Fin n)) := fun i =>
    if hi : i < rs.length then Classical.choose (hspec i hi).2.2.2.2 else ⊥
  have hT₀ : ∀ i (hi : i < rs.length), T₀ i = Classical.choose (hspec i hi).2.2.2.2 :=
    fun i hi => by simp only [T₀, hi, dite_true]
  refine ⟨x, fun i => (T₀ i).subgroupOf W, hx, fun i hi => ?_,
    fun i hi b hb hb2 hb1 hbx hbm1 hbm2 => ?_⟩
  · obtain ⟨hTle, hcard, -⟩ := Classical.choose_spec (hspec i hi).2.2.2.2
    rw [← hT₀ i hi] at hTle hcard
    have hTW : T₀ i ≤ W := hTle.trans inf_le_left
    refine isSylowOf_of_card ?_ ?_
    · intro b hb
      rw [mem_subgroupOf] at hb
      rw [mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.mp (hTle hb).2
      apply Subtype.ext
      simp only [coe_mul, hx i hi]
      exact this
    · rw [card_centralizer_subtype, hx i hi, ← hsyl i hi, ← hcard]
      exact Nat.card_congr (subgroupOfEquivOfLe hTW).toEquiv
  · obtain ⟨hTle, -, -, hw'⟩ := Classical.choose_spec (hspec i hi).2.2.2.2
    rw [← hT₀ i hi] at hTle hw'
    have hbT : (b : Equiv.Perm (Fin n)) ∈ T₀ i := by rwa [mem_subgroupOf] at hb
    have hbx' : (b : Equiv.Perm (Fin n)) ≠ permOfArr n (unpackP n w rs[i]!.x) := by
      rw [← hx i hi]
      exact fun h1 => hbx (Subtype.ext h1)
    have hb2' : (b : Equiv.Perm (Fin n)) ^ 2 = 1 := by rw [← coe_pow, hb2, coe_one]
    have hb1' : (b : Equiv.Perm (Fin n)) ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
    have hconj : ∀ g : ↥W, (g : Equiv.Perm (Fin n)) ^ 2 = 1 → (g : Equiv.Perm (Fin n)) ≠ 1 →
        fixP (g : Equiv.Perm (Fin n)) ∈ pskipFix n w rs i → ∃ j < i, IsConj g (x j) := by
      intro g hg2 hg1 hgs
      rw [pskipFix, List.mem_map] at hgs
      obtain ⟨r, hr, hre⟩ := hgs
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
      have hji : j < i := by simp at hj; omega
      have hjk : j < rs.length := by simp at hj; omega
      rw [List.getElem_take, ← getElem!_pos rs j hjk, ← (hspec j hjk).2.2.2.1] at hre
      obtain ⟨v, hvW, hv⟩ := hfix g g.2 hg2 hg1 j hjk hre.symm
      refine ⟨j, hji, isConj_iff.mpr ⟨⟨v, hvW⟩, Subtype.ext ?_⟩⟩
      simp only [coe_mul, coe_inv, hx j hjk]
      exact hv
    rcases (hw' X hXW hN hps hsX).2 (hout i hi) (b : Equiv.Perm (Fin n)) hbT hb2' hb1' hbx'
      (fun hm => by simpa [mem_subgroupOf] using hbm1 hm)
      (fun hm => by simpa [mem_subgroupOf] using hbm2 hm) with hM | hs | hs
    · left
      have hXmap : (X.subgroupOf W).map W.subtype = X := by
        rw [subgroupOf_map_subtype, inf_eq_left.mpr hXW]
      have hEmap : (closure ({x i, b} : Set ↥W)).map W.subtype =
          closure {permOfArr n (unpackP n w rs[i]!.x), (b : Equiv.Perm (Fin n))} := by
        rw [MonoidHom.map_closure, Set.image_pair]
        simp only [coe_subtype, hx i hi]
      rw [← monoW_map_iff W.subtype W.subtype_injective, hXmap, hEmap]
      exact hM
    · obtain ⟨j, hji, hj⟩ := hconj b hb2' hb1' hs
      exact Or.inr ⟨j, hji, Or.inl hj⟩
    ·
      have hcomm : permOfArr n (unpackP n w rs[i]!.x) * b =
          b * permOfArr n (unpackP n w rs[i]!.x) :=
        (mem_centralizer_singleton_iff.mp (hTle hbT).2).symm
      have hx2 := (hspec i hi).2.1
      have hxb2 : ((x i * b : ↥W) : Equiv.Perm (Fin n)) ^ 2 = 1 := by
        rw [coe_mul, hx i hi, sq, mul_assoc, ← mul_assoc (b : Equiv.Perm (Fin n)), ← hcomm,
          mul_assoc, ← mul_assoc, ← sq, hx2, ← sq, hb2', one_mul]
      have hxb1 : ((x i * b : ↥W) : Equiv.Perm (Fin n)) ≠ 1 := by
        rw [coe_mul, hx i hi]
        intro h1
        apply hbx'
        have hxinv :
            (permOfArr n (unpackP n w rs[i]!.x))⁻¹ = permOfArr n (unpackP n w rs[i]!.x) :=
          inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx2)
        rw [← hxinv]
        exact eq_inv_of_mul_eq_one_right h1
      obtain ⟨j, hji, hj⟩ := hconj (x i * b) hxb2 hxb1 (by rwa [coe_mul, hx i hi])
      exact Or.inr ⟨j, hji, Or.inr hj⟩

theorem isConj_of_roots {X W : Subgroup (Equiv.Perm (Fin n))} {m : ℕ} {x : ℕ → ↥W}
    {y : ℕ → Equiv.Perm (Fin n)} (hx : ∀ i < m, ((x i : ↥W) : Equiv.Perm (Fin n)) = y i)
    (hcls : ∀ a ∈ X, a ^ 2 = 1 → a ≠ 1 → ∃ i < m, ∃ g ∈ W, g * a * g⁻¹ = y i) :
    ∀ a ∈ X.subgroupOf W, a ^ 2 = 1 → a ≠ 1 → ∃ i < m, IsConj a (x i) := by
  intro a ha ha2 ha1
  rw [mem_subgroupOf] at ha
  obtain ⟨i, hi, g, hgW, hg⟩ := hcls a ha (by rw [← coe_pow, ha2, coe_one])
    (fun h1 => ha1 (Subtype.ext h1))
  refine ⟨i, hi, isConj_iff.mpr ⟨⟨g, hgW⟩, Subtype.ext ?_⟩⟩
  simp only [coe_mul, coe_inv, hx i hi]
  exact hg

theorem yCensusII_of_rootConjChecksB {ps : List Nat} {inXP inWP : Nat → Bool}
    {X W : Subgroup (Equiv.Perm (Fin n))} {ks : List Nat} {rs : List RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hXW : X ≤ W) (hN : (X.subgroupOf W).Normal)
    (hXi : (X.subgroupOf W).index ≤ 2) (hps : ∀ p ∈ ps, p < n)
    (hsX : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
      permOfArr n (unpackP n w P) ∈ X)
    (hsW : ∀ P, canon1 n w P = true → pvalid n w P = true → inWP P = true →
      permOfArr n (unpackP n w P) ∈ W)
    (hc : rs.all (canonR n w) = true) (h : prootsConjOKB n w ps inXP inWP false 2 ks rs = true)
    (hsyl : ∀ i < rs.length, rs[i]!.xs.length =
      (Nat.card ↥(W ⊓ centralizer {permOfArr n (unpackP n w rs[i]!.x)})).factorization 2)
    (hfix : ∀ g ∈ W, g ^ 2 = 1 → g ≠ 1 → ∀ j < rs.length,
      fixP g = fixP (permOfArr n (unpackP n w rs[j]!.x)) →
        ∃ v ∈ W, v * g * v⁻¹ = permOfArr n (unpackP n w rs[j]!.x))
    (hout : ∀ i < rs.length, permOfArr n (unpackP n w rs[i]!.xs[ks[i]!]!) ∉ X)
    (hin : ∀ i < rs.length, permOfArr n (unpackP n w rs[i]!.x) ∈ X)
    (hcls : ∀ a ∈ X, a ^ 2 = 1 → a ≠ 1 →
      ∃ i < rs.length, ∃ g ∈ W, g * a * g⁻¹ = permOfArr n (unpackP n w rs[i]!.x)) :
    YCensus (X.subgroupOf W) (· ≤ X.subgroupOf W) := by
  obtain ⟨x, T, hx, hT, hwit⟩ :=
    roots_in_W_conjB hn hw hXW hN hps hsX hsW hc h hsyl hfix hout
  have hxX : ∀ j < rs.length, x j ∈ X.subgroupOf W := fun j hj => by
    rw [mem_subgroupOf, hx j hj]
    exact hin j hj
  refine yCensusII_of_innerRoots hN hXi x T hT (isConj_of_roots hx hcls)
    (fun i hi b hb hb2 hbX => ?_)
  have hb1 : b ≠ 1 := fun h1 => hbX (h1 ▸ one_mem _)
  have hbx : b ≠ x i := fun h1 => hbX (h1 ▸ hxX i hi)
  rcases hwit i hi b hb hb2 hb1 hbx (by simp) (fun _ => hbX) with hM | ⟨j, hji, hj | hj⟩
  · exact hM
  ·
    exfalso
    obtain ⟨c, hc⟩ := isConj_iff.mp hj
    have hmem : b ∈ X.subgroupOf W := by
      have := hN.conj_mem _ (hxX j (hji.trans hi)) c⁻¹
      rw [← hc] at this
      simpa [mul_assoc] using this
    exact hbX hmem
  ·
    exfalso
    obtain ⟨c, hc⟩ := isConj_iff.mp hj
    have hmem : x i * b ∈ X.subgroupOf W := by
      have := hN.conj_mem _ (hxX j (hji.trans hi)) c⁻¹
      rw [← hc] at this
      simpa [mul_assoc] using this
    exact hbX (by simpa using (X.subgroupOf W).mul_mem ((X.subgroupOf W).inv_mem (hxX i hi)) hmem)

theorem yCensus17_of_rootConjChecksB {ps : List Nat} {inXP inWP : Nat → Bool}
    {X W : Subgroup (Equiv.Perm (Fin n))} {ks : List Nat} {rs : List RootConjP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hXW : X ≤ W) (hN : (X.subgroupOf W).Normal)
    (hXi : (X.subgroupOf W).index ≤ 2) (hps : ∀ p ∈ ps, p < n)
    (hsX : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = true →
      permOfArr n (unpackP n w P) ∈ X)
    (hsW : ∀ P, canon1 n w P = true → pvalid n w P = true → inWP P = true →
      permOfArr n (unpackP n w P) ∈ W)
    (hc : rs.all (canonR n w) = true) (h : prootsConjOKB n w ps inXP inWP true 1 ks rs = true)
    (hsyl : ∀ i < rs.length, rs[i]!.xs.length =
      (Nat.card ↥(W ⊓ centralizer {permOfArr n (unpackP n w rs[i]!.x)})).factorization 2)
    (hfix : ∀ g ∈ W, g ^ 2 = 1 → g ≠ 1 → ∀ j < rs.length,
      fixP g = fixP (permOfArr n (unpackP n w rs[j]!.x)) →
        ∃ v ∈ W, v * g * v⁻¹ = permOfArr n (unpackP n w rs[j]!.x))
    (hout : ∀ i < rs.length, permOfArr n (unpackP n w rs[i]!.xs[ks[i]!]!) ∉ X)
    (hII : YCensus (X.subgroupOf W) (· ≤ X.subgroupOf W))
    (hcls : ∀ a ∈ X, a ^ 2 = 1 → a ≠ 1 →
      ∃ i < rs.length, ∃ g ∈ W, g * a * g⁻¹ = permOfArr n (unpackP n w rs[i]!.x)) :
    YCensus17 (X.subgroupOf W) (fun _ => False) := by
  obtain ⟨x, T, hx, hT, hwit⟩ :=
    roots_in_W_conjB hn hw hXW hN hps hsX hsW hc h hsyl hfix hout
  exact yCensus17_of_innerRoots hN hXi x T hT hII (isConj_of_roots hx hcls)
    (fun i hi b hb hb2 hb1 hbx hbX => hwit i hi b hb hb2 hb1 hbx (fun _ => hbX) (by simp))

end CFSG.KC.Census
