module

public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.EBfs
public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.EK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Fix

public section

namespace CFSG.KC.LQT.Syl.CoreSnd

open Equiv CFSG.KC.LQT CFSG.QuasithinUnique.A5.Kc3Cert
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

variable {n : ℕ}

private noncomputable def kpw_F : List ℕ → List ℕ → List (ℕ × ℕ) :=
  List.rec (motive := fun _ => List ℕ → List (ℕ × ℕ)) (fun _ => [])
    (fun x _ ih pend => List.rec (motive := fun _ => List (ℕ × ℕ)) (ih [x])
      (fun p _ _ => List.cons (p, x) (ih [])) pend)

private theorem kpw_F_spec (rT : List ℕ) :
    kpw_F rT [] = pairUp rT ∧ ∀ p, kpw_F rT [p] = pairUp (p :: rT) := by
  induction rT with
  | nil => exact ⟨rfl, fun p => rfl⟩
  | cons x rest ih =>
    refine ⟨ih.2 x, fun p => ?_⟩
    show (p, x) :: kpw_F rest [] = pairUp (p :: x :: rest)
    exact congrArg (List.cons (p, x)) ih.1

theorem pairUpK_eq (rT : List ℕ) : Syl.pairUpK rT = pairUp rT :=
  (kpw_F_spec rT).1

private theorem kpw_getD_toList {R : Type} (a : Array R) (i : ℕ) (d : R) :
    a.getD i d = a.toList.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

private theorem kpw_foldl_toList {R : Type} [Mul R] [One R] (gens : List R)
    (ps : List (ℕ × ℕ)) : ∀ acc : Array R,
      (ps.foldl (fun acc ps => acc.push (gens.getD ps.2 1 * acc.getD ps.1 1)) acc).toList =
        ps.foldl (fun l pk => l ++ [gens.getD pk.2 1 * l.getD pk.1 1]) acc.toList := by
  induction ps with
  | nil => intro acc; rfl
  | cons pk ps ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih, Array.toList_push, kpw_getD_toList]

theorem treeReps_toList {R : Type} [Mul R] [One R] (gens : List R) (ps : List (ℕ × ℕ)) :
    (treeReps gens ps).toList = T2.bfsG (fun x g => g * x) 1 gens 1 ps :=
  kpw_foldl_toList gens ps #[1]

theorem repsK_eq (hn : n ≤ 32) (gs : List (Perm (Fin n))) (rT : List ℕ)
    (hm : T2.monoK (Syl.pairUpK rT) = true) :
    Syl.repsK n (gs.map P.code) rT =
      ((treeReps (gs.map RN.enc) (pairUp rT)).toList).map L.rnc := by
  unfold Syl.repsK
  rw [T2.bfsQ_eq _ _ _ _ _ hm, pairUpK_eq, treeReps_toList,
    T2.bfsG_map (L.rnc (n := n)) (fun x g => g * x) (fun x g => P.mul n g x)
      (fun x g => L.rnc_mul hn g x) 1 (gs.map RN.enc) 1, L.rnc_one, L.map_rnc_enc]

theorem lor_pow_sum (v : List ℕ) :
    v.foldr (fun a acc => 2 ^ a ||| acc) 0 = ∑ q ∈ v.toFinset, 2 ^ q := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_sum_pow]
  induction v with
  | nil => simp
  | cons a v ih =>
    simp only [List.foldr_cons, Nat.testBit_or, Nat.testBit_two_pow, ih]
    simp [List.toFinset_cons, Finset.mem_insert, eq_comm]

private theorem kpw_maskK_foldr (S : List ℕ) (m : ℕ) :
    Syl.maskK S m = (S.map fun p => P.img m p).foldr (fun a acc => 2 ^ a ||| acc) 0 := by
  induction S with
  | nil => rfl
  | cons p S ih =>
    rw [List.map_cons, List.foldr_cons, ← ih]
    rfl

private theorem kpw_sum_toFinset_map (w : List (Fin n)) :
    ∑ q ∈ (w.map Fin.val).toFinset, 2 ^ q = ∑ q ∈ w.toFinset, 2 ^ q.val := by
  have h : (w.map Fin.val).toFinset = w.toFinset.image Fin.val := by
    ext x
    simp [List.mem_map, Finset.mem_image]
  rw [h]
  exact Finset.sum_image (fun a _ b _ hab => Fin.val_injective hab)

theorem maskK_eq (hn : n ≤ 32) (T : List (Fin n)) (r : RN n) :
    Syl.maskK (T.map Fin.val) (L.rnc r) = imgMask T r := by
  have h2 : (T.map Fin.val).map (fun p => P.img (L.rnc r) p) =
      (T.map fun p => r.val[p]).map Fin.val := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro p _
    exact L.img_rnc hn r p
  rw [kpw_maskK_foldr, h2, lor_pow_sum, kpw_sum_toFinset_map]
  rfl

private theorem kpw_map_val_finRange (m : ℕ) : (List.finRange m).map Fin.val = List.range m := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem fixK_eq (hn : n ≤ 32) {B : List (Perm (Fin n))} (h : EFacts B) :
    Syl.fixK n ((lst B).map P.code) =
      (fixPts (bfsSet (B.map RN.enc) 16)).map Fin.val := by
  have key : ∀ p : Fin n, P.allL ((lst B).map P.code) (fun e => Nat.beq (P.img e p) p) =
      (bfsSet (B.map RN.enc) 16).toList.all (fun e => e.val[p] == p) := by
    intro p
    rw [Bool.eq_iff_iff, P.allL_map, List.all_eq_true]
    constructor
    · intro hA e he
      rw [Std.HashSet.mem_toList, es_mem h] at he
      obtain ⟨σ, hσ, rfl⟩ := he
      have hs : Nat.beq (P.img (P.code σ) p) p = true := hA σ hσ
      rw [P.beq_iff, P.img_code hn σ p] at hs
      rw [RN.enc_get, beq_iff_eq]
      exact Fin.ext hs
    · intro hB g hg
      have hmem : RN.enc g ∈ (bfsSet (B.map RN.enc) 16).toList := by
        rw [Std.HashSet.mem_toList, es_mem h]
        exact ⟨g, hg, rfl⟩
      have hs := hB _ hmem
      rw [RN.enc_get, beq_iff_eq] at hs
      show Nat.beq (P.img (P.code g) p) p = true
      rw [P.beq_iff, P.img_code hn g p, hs]
  unfold Syl.fixK fixPts
  rw [← kpw_map_val_finRange n, List.filter_map]
  exact congrArg (List.map Fin.val) (List.filter_congr fun p _ => key p)

theorem orbK_sound (hn : n ≤ 32) (gs : List (Perm (Fin n))) {B : List (Perm (Fin n))}
    (h : EFacts B) (rT : List ℕ) (nOrd kOrd : ℕ)
    (ho : Syl.orbK n (gs.map P.code) (B.map P.code) rT nOrd kOrd = true) :
    ((treeReps (gs.map RN.enc) (pairUp rT)).toList.map
        (imgMask (fixPts (bfsSet (B.map RN.enc) 16)))).Nodup ∧
      kOrd = (treeReps (gs.map RN.enc) (pairUp rT)).size * nOrd := by
  unfold Syl.orbK at ho
  simp only [S.allBs_cons, S.allBs_nil, P.andB_iff, and_true] at ho
  obtain ⟨hm, hd, hk⟩ := ho
  rw [lstK_code hn B, fixK_eq hn h, repsK_eq hn gs rT hm] at hd
  rw [repsK_eq hn gs rT hm, S.lenL_eq, List.length_map, Array.length_toList] at hk
  refine ⟨?_, P.beq_iff.1 hk⟩
  have := T2.nodup_of_distinctS hd
  rw [List.map_map] at this
  convert this using 2
  funext r
  exact (maskK_eq hn _ r).symm

end CFSG.KC.LQT.Syl.CoreSnd

end
