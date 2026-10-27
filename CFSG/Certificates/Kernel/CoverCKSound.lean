module

public import Certificates.Data.Kernel.CoverCK
public import Certificates.Data.CFSGNative.SectionRank.F2
public import Certificates.Data.CoverCenterThreeMcL
import all CFSG.Certificates.Kernel.OpsF2KSound
import CFSG.Certificates.Kernel.Co1F2Sound
import CFSG.Certificates.Kernel.OpsLayKSnd

public section

namespace CFSG.KC.CoverCK

open CFSG.KC.M1F2 CFSG.SectionRank.Native CFSG.KC.LQT

private theorem toArray_getElem! {α : Type} [Inhabited α] (l : List α) {i : Nat} (hi : i < l.length) :
    l.toArray[i]! = l[i] := by
  simp [hi]

private theorem getElem!_eq_getD {l : List Nat} {i : Nat} : l[i]! = l.getD i 0 := by
  rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

section F2

open CFSG.KC.OpsF2K
open CFSG.KC.Co1F2 (unpackR)

private theorem evalW2_unpack {m d : Nat} {G I : Array (Array Nat)} {GK IK : List Nat}
    (hG : ∀ i < m, G[i]! = unpackR d (GK.getD i 0))
    (hI : ∀ i < m, I[i]! = unpackR d (IK.getD i 0)) :
    ∀ w : List (Fin m × Bool), (ops2 d).evalWordN G I w = unpackR d (evalWK2 d GK IK w)
  | [] => (unpackR_idF_eq_one d).symm
  | ⟨i, b⟩ :: w => by
    simp only [Ops.evalWordN, evalWK2]
    rw [unpackR_mulF, evalW2_unpack hG hI w]
    cases b <;> simp [hG _ i.isLt, hI _ i.isLt]

theorem coverCheck_of_K2 {m d A B : Nat} {csA csB : List Char} {D : CoverData m}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (h : coverK2 d A B D = true) : (ops2 d).coverCheck D = true := by
  simp only [coverK2, dataOK2, seedsOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, -, hexp, hn, hprog, hgl, hil, hgr, hie, hfin, hrels⟩ := h
  have hreg : ∀ r < D.nregs, ((ops2 d).run D.prog ((ops2 d).initRegs ((ops2 d).decode D.seedA)
      ((ops2 d).decode D.seedB) D.nregs))[r]! =
        unpackR d (getR d (runK d A B D.nregs D.prog) r) :=
    fun r hr => regs_get hA hB hsA hsB hprog hexp hr
  have hgr' : ∀ r ∈ D.gens, r < D.nregs := fun r hr =>
    of_decide_eq_true (List.all_eq_true.1 hgr r hr)
  have hie' : ∀ e ∈ D.invExp, e < 65536 := fun e he =>
    of_decide_eq_true (List.all_eq_true.1 hie e he)
  have hG : ∀ i < m, ((ops2 d).coverGens D)[i]! =
      unpackR d ((D.gens.map (getR d (runK d A B D.nregs D.prog))).getD i 0) := by
    intro i hi
    have hi' : i < D.gens.length := by rw [hgl]; exact hi
    simp only [Ops.coverGens, Ops.regsOf]
    rw [toArray_getElem! _ (by simpa using hi'), List.getElem_map,
      List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map]
    exact hreg _ (hgr' _ (List.getElem_mem _))
  have hI : ∀ i < m, ((ops2 d).coverInvs D)[i]! =
      unpackR d (((D.gens.zip D.invExp).map fun p =>
        powK d (getR d (runK d A B D.nregs D.prog) p.1) (p.2 - 1)).getD i 0) := by
    intro i hi
    have hz : i < (D.gens.zip D.invExp).length := by simp [hgl, hil, hi]
    simp only [Ops.coverInvs, Ops.regsOf]
    rw [toArray_getElem! _ (by simpa using hz), List.getElem_map,
      List.getD_eq_getElem _ _ (by simpa using hz), List.getElem_map, List.getElem_zip]
    have hiI : i < D.invExp.length := by rw [hil]; exact hi
    have he : D.invExp[i] - 1 < 2 ^ 16 := by
      have := hie' _ (List.getElem_mem hiI)
      omega
    rw [unpackR_powK he, hreg _ (hgr' _ (List.getElem_mem _))]
  have hW := evalW2_unpack hG hI
  unfold Ops.coverCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]
  rw [List.all_eq_true] at hfin hrels
  refine ⟨hn, List.all_eq_true.1 hprog, hgl, hil, hgr', fun i _ => ?_, fun w hw => ?_⟩
  · have hfi := hfin i (List.mem_finRange i)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfi
    obtain ⟨⟨h0, hpow⟩, hif⟩ := hfi
    have hil' : i.val < D.invExp.length := by rw [hil]; exact i.isLt
    have hei : D.invExp.getD i.val 0 < 2 ^ 16 := by
      rw [List.getD_eq_getElem _ _ hil']
      exact hie' _ (List.getElem_mem _)
    rw [getElem!_eq_getD, hG i i.isLt]
    refine ⟨h0, ?_, ?_⟩
    · rw [← unpackR_powK hei, ← unpackR_idF_eq_one]
      exact eq_of_beq hpow
    · split_ifs at hif ⊢ with he
      · rw [hW]
        exact eq_of_beq hif
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hif
        rw [← unpackR_powK (by omega : D.e i < 2 ^ 16), ← unpackR_idF_eq_one]
        exact eq_of_beq hif.2
  · rw [hW, ← unpackR_idF_eq_one]
    exact eq_of_beq (hrels w hw)

end F2

private theorem bitsK_succ (m k g : Nat) :
    bitsK m (k + 1) g = if bitK m g = true then g :: bitsK m k (g + 1) else bitsK m k (g + 1) := by
  simp only [bitsK]
  cases bitK m g <;> rfl

private theorem mem_bitsK {m : Nat} : ∀ (k g x : Nat), x ∈ bitsK m k g → g ≤ x ∧ x < g + k
  | 0, g, x, h => by simp [bitsK] at h
  | k + 1, g, x, h => by
    have ih := mem_bitsK (m := m) k (g + 1) x
    rw [bitsK_succ] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := ih h
        omega
    · have := ih h
      omega

private theorem kidsK_cons (act : Nat → Nat → Nat) (v m G : Nat) (gs : List Nat) (g : Nat) :
    kidsK act v m (G :: gs) g =
      if bitK m g = true then act v G :: kidsK act v m gs (g + 1) else kidsK act v m gs (g + 1) := by
  simp only [kidsK]
  cases bitK m g <;> rfl

private theorem kidsK_eq (act : Nat → Nat → Nat) (v m : Nat) : ∀ (gs : List Nat) (g : Nat),
    kidsK act v m gs g = (bitsK m gs.length g).map fun x => act v (gs.getD (x - g) 0)
  | [], _ => rfl
  | G :: gs, g => by
    rw [kidsK_cons, List.length_cons, bitsK_succ, kidsK_eq act v m gs (g + 1)]
    have hc : ∀ x ∈ bitsK m gs.length (g + 1),
        act v (gs.getD (x - (g + 1)) 0) = act v ((G :: gs).getD (x - g) 0) := by
      intro x hx
      have := (mem_bitsK _ _ _ hx).1
      have e : x - g = x - (g + 1) + 1 := by omega
      rw [e, List.getD_cons_succ]
    split
    · rw [List.map_cons, Nat.sub_self, List.getD_cons_zero]
      exact congrArg _ (List.map_congr_left hc)
    · exact List.map_congr_left hc

def bfsQ (kids : Nat → Nat → List Nat) : List Nat → List Nat → List Nat → Option (List Nat)
  | [], [], out => some out.reverse
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none
  | m :: ms, v :: Q, out => bfsQ kids ms (Q ++ kids v m) (v :: out)

private theorem bfsQ_nil_cons (kids : Nat → Nat → List Nat) {Q : List Nat} (hQ : Q ≠ [])
    (out : List Nat) : bfsQ kids [] Q out = none := by
  obtain ⟨v, Q', rfl⟩ := List.exists_cons_of_ne_nil hQ
  rfl

private theorem bfsK_eq (act : Nat → Nat → Nat) (gens : List Nat) : ∀ (ms f b out : List Nat),
    bfsK act gens ms f b out = bfsQ (fun v m => kidsK act v m gens 0) ms (f ++ b.reverse) out
  | [], [], [], out => rfl
  | [], v :: f, b, out => by
    rw [bfsQ_nil_cons _ (by simp)]
    rfl
  | [], [], x :: b, out => by
    rw [bfsQ_nil_cons _ (by simp)]
    rfl
  | m :: ms, [], [], out => rfl
  | m :: ms, v :: f, b, out => by
    change bfsK act gens ms f (List.reverseAux (kidsK act v m gens 0) b) (v :: out) = _
    rw [bfsK_eq act gens ms, List.reverseAux_eq, List.reverse_append, List.reverse_reverse,
      List.cons_append]
    change _ = bfsQ _ ms ((f ++ b.reverse) ++ kidsK act v m gens 0) (v :: out)
    rw [List.append_assoc]
  | m :: ms, [], x :: b, out => by
    obtain ⟨y, f', hyf⟩ := List.exists_cons_of_ne_nil (by simp : (x :: b).reverse ≠ [])
    have e1 : bfsK act gens (m :: ms) [] (x :: b) out =
        bfsK act gens ms f' (List.reverseAux (kidsK act y m gens 0) []) (y :: out) := by
      simp only [bfsK, hyf]
    rw [e1, bfsK_eq act gens ms, List.nil_append, hyf, List.reverseAux_eq, List.append_nil,
      List.reverse_reverse]
    rfl

private theorem bfsQ_spec {kids : Nat → Nat → List Nat} {κ : Nat → Nat}
    (hk : ∀ v m, (kids v m).length = κ m) : ∀ (ms Q out L : List Nat), bfsQ kids ms Q out = some L →
      ∃ P, L = out.reverse ++ P ∧ P.length = ms.length ∧
        P = Q ++ (List.zipWith kids P ms).flatten ∧
        ∀ j < ms.length, j < Q.length + ((ms.take j).map κ).sum
  | [], [], out, L, h => by
    simp only [bfsQ, Option.some.injEq] at h
    exact ⟨[], by simp [h], rfl, by simp, fun j hj => absurd hj (by simp)⟩
  | [], _ :: _, _, _, h => by simp [bfsQ] at h
  | _ :: _, [], _, _, h => by simp [bfsQ] at h
  | m :: ms, v :: Q, out, L, h => by
    simp only [bfsQ] at h
    obtain ⟨P, hL, hlen, hP, hj⟩ := bfsQ_spec hk ms _ _ L h
    refine ⟨v :: P, by simp [hL], by simp [hlen], ?_, fun j hjl => ?_⟩
    · rw [List.zipWith_cons_cons, List.flatten_cons, List.cons_append]
      congr 1
      conv_lhs => rw [hP]
      rw [List.append_assoc]
    · cases j with
      | zero => simp
      | succ j =>
        have := hj j (by simp at hjl; omega)
        simp only [List.length_append, hk] at this
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.length_cons]
        omega

def treeE (ng : Nat) (masks : List Nat) (s : Nat) : List (Nat × Nat) :=
  (masks.zipIdx s).flatMap fun p => (bitsK p.1 ng 0).map fun g => (p.2, g)

private theorem treeE_cons (ng m : Nat) (ms : List Nat) (s : Nat) :
    treeE ng (m :: ms) s = (bitsK m ng 0).map (fun g => (s, g)) ++ treeE ng ms (s + 1) := by
  simp [treeE]

private theorem parOf_eq (ng : Nat) (masks : List Nat) :
    parOf ng masks = 0 :: (treeE ng masks 0).map Prod.fst := by
  simp only [parOf, treeE, List.map_flatMap, List.map_map]
  rfl

private theorem treeE_snd (ng : Nat) : ∀ (ms : List Nat) (s : Nat),
    (treeE ng ms s).map Prod.snd = ms.flatMap fun m => bitsK m ng 0
  | [], _ => rfl
  | m :: ms, s => by
    rw [treeE_cons, List.map_append, treeE_snd ng ms (s + 1), List.map_map, List.flatMap_cons]
    congr 1
    exact List.map_id' _

private theorem labOf_eq (ng : Nat) (masks : List Nat) :
    labOf ng masks = 0 :: (treeE ng masks 0).map Prod.snd := by
  rw [treeE_snd]
  rfl

private theorem treeE_get (ng : Nat) : ∀ (ms : List Nat) (s k : Nat)
    (hk : k < (treeE ng ms s).length),
    s ≤ (treeE ng ms s)[k].1 ∧ (treeE ng ms s)[k].1 - s < ms.length ∧
      ((ms.take ((treeE ng ms s)[k].1 - s)).map fun m => (bitsK m ng 0).length).sum ≤ k ∧
      (treeE ng ms s)[k].2 < ng
  | [], s, k, hk => by simp [treeE] at hk
  | m :: ms, s, k, hk => by
    simp only [treeE_cons] at hk ⊢
    by_cases hb : k < ((bitsK m ng 0).map fun g => (s, g)).length
    · rw [List.getElem_append_left hb, List.getElem_map]
      have := (mem_bitsK ng 0 _ (List.getElem_mem (by simpa using hb))).2
      simp only [Nat.sub_self, List.take_zero, List.map_nil, List.sum_nil, List.length_cons]
      omega
    · have hk' : k - ((bitsK m ng 0).map fun g => (s, g)).length < (treeE ng ms (s + 1)).length := by
        rw [List.length_append] at hk
        omega
      rw [List.getElem_append_right (by omega)]
      obtain ⟨h1, h2, h3, h4⟩ := treeE_get ng ms (s + 1) _ hk'
      refine ⟨by omega, by rw [List.length_cons]; omega, ?_, h4⟩
      have e : (treeE ng ms (s + 1))[k - ((bitsK m ng 0).map fun g => (s, g)).length].1 - s =
          ((treeE ng ms (s + 1))[k - ((bitsK m ng 0).map fun g => (s, g)).length].1 - (s + 1)) + 1 := by
        omega
      rw [e, List.take_succ_cons, List.map_cons, List.sum_cons]
      simp only [List.length_map] at h3 hb ⊢
      omega

private theorem flat_eq (act : Nat → Nat → Nat) (gens : List Nat) (P : List Nat) :
    ∀ (ms : List Nat) (s : Nat), s + ms.length ≤ P.length →
      (List.zipWith (fun v m => (bitsK m gens.length 0).map fun g => act v (gens.getD g 0))
        (P.drop s) ms).flatten =
        (treeE gens.length ms s).map fun e => act (P.getD e.1 0) (gens.getD e.2 0)
  | [], s, _ => by simp [treeE]
  | m :: ms, s, h => by
    have hs : s < P.length := by simp at h; omega
    rw [List.drop_eq_getElem_cons hs, List.zipWith_cons_cons, List.flatten_cons,
      flat_eq act gens P ms (s + 1) (by simp at h; omega), treeE_cons, List.map_append,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro g _
    simp [List.getElem?_eq_getElem hs]

private theorem orbit_run {act : Nat → Nat → Nat} {gens masks vs : List Nat} {u : Nat}
    (h : bfsK act gens masks [u] [] [] = some vs) :
    vs.length = masks.length ∧
      vs = u :: (treeE gens.length masks 0).map (fun e => act (vs.getD e.1 0) (gens.getD e.2 0)) ∧
      ∀ k (hk : k < (treeE gens.length masks 0).length),
        (treeE gens.length masks 0)[k].1 < k + 1 ∧ (treeE gens.length masks 0)[k].2 < gens.length := by
  rw [bfsK_eq] at h
  have hkids : ∀ v m, (kidsK act v m gens 0).length = (bitsK m gens.length 0).length := by
    intro v m
    rw [kidsK_eq, List.length_map]
  obtain ⟨P, hL, hlen, hP, hj⟩ := bfsQ_spec hkids masks _ [] vs h
  simp only [List.reverse_nil, List.nil_append, List.append_nil, List.singleton_append,
    List.length_singleton] at hL hP hj
  subst hL
  have hk : (fun v m => kidsK act v m gens 0) =
      fun v m => (bitsK m gens.length 0).map fun g => act v (gens.getD g 0) := by
    funext v m
    rw [kidsK_eq]
    simp
  have hf := flat_eq act gens vs masks 0 (by omega)
  rw [List.drop_zero] at hf
  rw [hk, hf] at hP
  refine ⟨hlen, hP, fun k hk' => ?_⟩
  obtain ⟨-, h2, h3, h4⟩ := treeE_get gens.length masks 0 k hk'
  have := hj _ (by simpa using h2)
  simp only [Nat.sub_zero, List.length_singleton] at this h3
  exact ⟨by omega, h4⟩

private theorem mergeK_perm : ∀ (n : Nat) (a b : List Nat), (mergeK n a b).Perm (a ++ b)
  | 0, a, b => List.Perm.refl _
  | _ + 1, [], b => List.Perm.refl _
  | _ + 1, x :: a, [] => by simp [mergeK]
  | n + 1, x :: a, y :: b => by
    simp only [mergeK]
    cases Nat.blt x y
    · exact ((mergeK_perm n (x :: a) b).cons y).trans List.perm_middle.symm
    · exact (mergeK_perm n a (y :: b)).cons x

private theorem pairK_perm (f : Nat) : ∀ l : List (List Nat), (pairK f l).flatten.Perm l.flatten
  | a :: b :: l => by
    simp only [pairK, List.flatten_cons]
    rw [← List.append_assoc]
    exact (mergeK_perm f a b).append (pairK_perm f l)
  | [] => List.Perm.refl _
  | [_] => List.Perm.refl _

private theorem passK_perm (f : Nat) : ∀ (n : Nat) (l : List (List Nat)),
    (passK f n l).flatten.Perm l.flatten
  | 0, _ => List.Perm.refl _
  | n + 1, l => (passK_perm f n (pairK f l)).trans (pairK_perm f l)

private theorem msortK_perm (ks : List Nat) : (msortK ks).Perm ks := by
  unfold msortK
  refine (passK_perm _ _ _).trans ?_
  have e : ∀ l : List Nat, (l.map fun k => [k]).flatten = l := by
    intro l
    induction l with
    | nil => rfl
    | cons k l ih =>
      rw [List.map_cons, List.flatten_cons, ih]
      rfl
  rw [e]

private theorem sortedK_pairwise : ∀ l : List Nat, sortedK l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [sortedK, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := sortedK_pairwise (b :: l) h.2
    refine List.Pairwise.cons ?_ ih
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

private theorem strictInc_of : ∀ l : List Nat, l.Pairwise (· < ·) → Ops.strictInc l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    simp only [Ops.strictInc, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, strictInc_of (b :: l) h.of_cons⟩

private theorem strictInc_mergeSort {l : List Nat} (h : l.Nodup) :
    Ops.strictInc (l.mergeSort fun a b => decide (a ≤ b)) = true := by
  apply strictInc_of
  have hs := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp at hab hbc ⊢; omega) (fun a b => by simp; omega) l
  have hn : (l.mergeSort fun a b => decide (a ≤ b)).Nodup := (List.mergeSort_perm l _).nodup_iff.mpr h
  exact (hs.and hn).imp fun ⟨h1, h2⟩ => by simp at h1; omega

private theorem orbitVecs_succ {M V : Type} [Inhabited M] [Inhabited V] (O : Ops M V) (gens : Array M)
    (t : Nat) (par lab : Array Nat) (n : Nat) :
    O.orbitVecs gens t par lab (n + 1) = (O.orbitVecs gens t par lab n).push
      (if n = 0 then O.unit t else O.vmul (O.orbitVecs gens t par lab n)[par[n]!]! gens[lab[n]!]!) := by
  unfold Ops.orbitVecs
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  split_ifs <;> rfl

private theorem orbitVecs_size {M V : Type} [Inhabited M] [Inhabited V] (O : Ops M V) (gens : Array M)
    (t : Nat) (par lab : Array Nat) : ∀ n, (O.orbitVecs gens t par lab n).size = n
  | 0 => rfl
  | n + 1 => by rw [orbitVecs_succ, Array.size_push, orbitVecs_size O gens t par lab n]

private theorem orbitVecs_get {M V : Type} [Inhabited M] [Inhabited V] (O : Ops M V) (gens : Array M)
    (t : Nat) (par lab : Array Nat) : ∀ n i, i < n →
      (O.orbitVecs gens t par lab n)[i]! = (O.orbitVecs gens t par lab (i + 1))[i]!
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    by_cases hi : i = n
    · rw [hi]
    · have hin : i < n := by omega
      rw [orbitVecs_succ, getElem!_pos _ i (by simp [orbitVecs_size]; omega), Array.getElem_push_lt
        (by rw [orbitVecs_size]; exact hin), ← getElem!_pos _ i (by rw [orbitVecs_size]; exact hin),
        orbitVecs_get O gens t par lab n i hin]

private theorem push_get! {α : Type} [Inhabited α] (A : Array α) (x : α) (i : Nat)
    (hi : i = A.size) : (A.push x)[i]! = x := by
  subst hi
  rw [getElem!_pos _ A.size (by simp), Array.getElem_push_eq]

private theorem orbitVecs_rel {M V : Type} [Inhabited M] [Inhabited V] (O : Ops M V)
    (gens : Array M) (t : Nat) {act : Nat → Nat → Nat} {gK masks vs : List Nat} {u : Nat}
    (R : V → Nat → Prop) (hu : R (O.unit t) u)
    (hstep : ∀ (w : V) (v : Nat) (g : Nat), g < gK.length → R w v →
      R (O.vmul w gens[g]!) (act v (gK.getD g 0)))
    (h : bfsK act gK masks [u] [] [] = some vs) :
    ∀ i < masks.length, R (O.orbitVecs gens t (parOf gK.length masks).toArray
      (labOf gK.length masks).toArray masks.length)[i]! (vs.getD i 0) := by
  obtain ⟨hlen, hvs, htr⟩ := orbit_run h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rw [orbitVecs_get O gens t _ _ _ i hi]
    cases i with
    | zero =>
      rw [orbitVecs_succ, if_pos rfl, push_get! _ _ _ (by rw [orbitVecs_size])]
      have e : vs.getD 0 0 = u := by rw [hvs]; rfl
      rw [e]
      exact hu
    | succ k =>
      have hk : k < (treeE gK.length masks 0).length := by
        have := congrArg List.length hvs
        simp only [List.length_cons, List.length_map] at this
        omega
      obtain ⟨hp, hg⟩ := htr k hk
      have hpar : (parOf gK.length masks).toArray[k + 1]! = (treeE gK.length masks 0)[k].1 := by
        rw [toArray_getElem! _ (by rw [parOf_eq]; simpa using hk)]
        simp only [parOf_eq, List.getElem_cons_succ, List.getElem_map]
      have hlab : (labOf gK.length masks).toArray[k + 1]! = (treeE gK.length masks 0)[k].2 := by
        rw [toArray_getElem! _ (by rw [labOf_eq]; simpa using hk)]
        simp only [labOf_eq, List.getElem_cons_succ, List.getElem_map]
      rw [orbitVecs_succ, if_neg (Nat.succ_ne_zero k), push_get! _ _ _ (by rw [orbitVecs_size]),
        hpar, hlab]
      have hv : vs.getD (k + 1) 0 = act (vs.getD (treeE gK.length masks 0)[k].1 0)
          (gK.getD (treeE gK.length masks 0)[k].2 0) := by
        have hk1 : k + 1 < vs.length := by omega
        rw [List.getD_eq_getElem _ _ hk1]
        have e := congrArg (fun l : List Nat => l[k + 1]?) hvs
        simp only [List.getElem?_cons_succ, List.getElem?_map, List.getElem?_eq_getElem hk1,
          List.getElem?_eq_getElem hk, Option.map_some, Option.some.injEq] at e
        exact e
      rw [hv]
      have hrec := ih _ (by omega) (by omega)
      rw [orbitVecs_get O gens t _ _ masks.length _ (by omega)] at hrec
      rw [← orbitVecs_get O gens t _ _ (k + 1) _ hp] at hrec
      exact hstep _ _ _ hg hrec

theorem orbitOK_of_K2 {m d A B : Nat} {csA csB : List Char} {D : CoverData m}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB) {ng t : Nat}
    {masks : List Nat} (h : coverOrbitK2 d A B D ng t masks = true) :
    (ops2 d).orbitOK (((ops2 d).coverGens D).extract 0 ng) t masks.length (· % 2 ^ d)
      (parOf ng masks).toArray (labOf ng masks).toArray = true := by
  simp only [coverOrbitK2, dataOK2, OpsF2K.seedsOK, orbitK, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨-, -, -, hexp, hn, hprog, hgl, hil, hgr, hie, hng, ht, hne, -, hrun⟩ := h
  have hgr' : ∀ r ∈ D.gens, r < D.nregs := fun r hr =>
    of_decide_eq_true (List.all_eq_true.1 hgr r hr)
  have hreg : ∀ r < D.nregs, ((ops2 d).run D.prog ((ops2 d).initRegs ((ops2 d).decode D.seedA)
      ((ops2 d).decode D.seedB) D.nregs))[r]! =
        CFSG.KC.Co1F2.unpackR d (OpsF2K.getR d (OpsF2K.runK d A B D.nregs D.prog) r) :=
    fun r hr => OpsF2K.regs_get hA hB hsA hsB hprog hexp hr
  set gK := (D.gens.take ng).map (OpsF2K.getR d (OpsF2K.runK d A B D.nregs D.prog)) with hgK
  have hgKl : gK.length = ng := by simp [hgK, hgl, hng]
  have hsize : ((ops2 d).coverGens D).size = m := by simp [Ops.coverGens, hgl]
  have hgen : ∀ g < gK.length, (((ops2 d).coverGens D).extract 0 ng)[g]! =
      CFSG.KC.Co1F2.unpackR d (gK.getD g 0) := by
    intro g hg
    rw [hgKl] at hg
    have hgm : g < D.gens.length := by omega
    rw [getElem!_pos _ g (by simp [hsize]; omega), Array.getElem_extract,
      ← getElem!_pos _ (0 + g) (by rw [hsize]; omega), Nat.zero_add]
    simp only [Ops.coverGens, Ops.regsOf]
    have e : gK.getD g 0 = OpsF2K.getR d (OpsF2K.runK d A B D.nregs D.prog) D.gens[g] := by
      rw [hgK, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_take]
    rw [toArray_getElem! _ (by simpa using hgm), List.getElem_map, e]
    exact hreg _ (hgr' _ (List.getElem_mem _))
  split at hrun
  next vs hb =>
    obtain ⟨hlen, hvs, htr⟩ := orbit_run hb
    have hR := orbitVecs_rel (ops2 d) (((ops2 d).coverGens D).extract 0 ng) t
      (fun w v => w = v ∧ v < 2 ^ d) ⟨OpsF2K.unit_eq d t, OpsF2K.pw2_lt ht⟩
      (fun w v g hg hwv => by
        rw [hgen g hg, OpsF2K.vmul_unpackR, hwv.1]
        exact ⟨rfl, CFSG.KC.F2W.vmF_lt d _ _⟩) hb
    rw [hgKl] at hvs htr hR
    have hEl : (treeE ng masks 0).length + 1 = masks.length := by
      have := congrArg List.length hvs
      simp only [List.length_cons, List.length_map] at this
      omega
    unfold Ops.orbitOK
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, and_assoc]
    refine ⟨by simp [parOf_eq, hEl], by simp [labOf_eq, hEl],
      List.length_pos_of_ne_nil (by simpa using hne), fun x hx => ?_, ?_⟩
    · cases x with
      | zero => exact Or.inl rfl
      | succ k =>
        right
        have hk : k < (treeE ng masks 0).length := by omega
        obtain ⟨hp, hg⟩ := htr k hk
        rw [toArray_getElem! _ (by rw [parOf_eq]; simpa using hk),
          toArray_getElem! _ (by rw [labOf_eq]; simpa using hk)]
        simp only [parOf_eq, labOf_eq, List.getElem_cons_succ, List.getElem_map, Array.size_extract,
          hsize]
        exact ⟨hp, by omega⟩
    · have hmap : ((ops2 d).orbitVecs (((ops2 d).coverGens D).extract 0 ng) t
          (parOf ng masks).toArray (labOf ng masks).toArray masks.length).toList.map
          (· % 2 ^ d) = vs := by
        apply List.ext_getElem (by simp [orbitVecs_size, hlen])
        intro i h1 h2
        have hi : i < masks.length := by simpa [orbitVecs_size] using h1
        obtain ⟨hw, hlt⟩ := hR i hi
        rw [List.getD_eq_getElem _ _ h2] at hw hlt
        rw [List.getElem_map, Array.getElem_toList, ← getElem!_pos _ i (by simp [orbitVecs_size, hi]),
          hw]
        exact Nat.mod_eq_of_lt hlt
      rw [hmap]
      have hnd : vs.Nodup := (msortK_perm vs).nodup_iff.mp
        ((sortedK_pairwise _ hrun).imp fun h => Nat.ne_of_lt h)
      exact strictInc_mergeSort hnd
  next => exact absurd hrun Bool.false_ne_true

private theorem f3get_lt (v : CFSG.F3.Native.V) (j : Nat) : v.get j < 3 := by
  unfold CFSG.F3.Native.V.get
  split_ifs <;> omega

private theorem f3Key_toVec {d : Nat} {v w : CFSG.F3.Native.V} (h : f3Key d v = f3Key d w) :
    (LocalComp.Ops3Snd.spec3b d).toVec v = (LocalComp.Ops3Snd.spec3b d).toVec w := by
  have key : ∀ l : List Nat, l.foldr (fun j acc => v.get j + 3 * acc) 0 =
      l.foldr (fun j acc => w.get j + 3 * acc) 0 → ∀ j ∈ l, v.get j = w.get j := by
    intro l
    induction l with
    | nil => intro _ j hj; simp at hj
    | cons a l ih =>
      intro hl j hj
      rw [List.foldr_cons, List.foldr_cons] at hl
      have ha := f3get_lt v a
      have hb := f3get_lt w a
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · exact ih (by omega) j hj
  funext j
  change (v.get j.val : ZMod 3) = (w.get j.val : ZMod 3)
  rw [key _ h j.val (List.mem_range.mpr j.isLt)]

theorem coverCheck_of_KL {m d A B : Nat} {c : Lay} {LA LB : List Char} {D : CoverData m}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (h : coverKL c A B D = true) : (ops3 d).coverCheck D = true := by
  subst hd
  simp only [coverKL, dataOKL, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hprog, hgl, hil, hgr, hie, hrun⟩ := h
  rw [OpsLayK.Snd.runC_eq] at hrun
  obtain ⟨h2, hlt⟩ := OpsLayK.Snd.progOK_spec hprog
  have hL := OpsLayK.Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := OpsLayK.Snd.runL_initR_length c D.prog A B D.nregs
  have hgr' : ∀ r ∈ D.gens, r < D.nregs := fun r hr =>
    of_decide_eq_true (List.all_eq_true.1 hgr r hr)
  have hie' : ∀ e ∈ D.invExp, e < 65536 := fun e he =>
    of_decide_eq_true (List.all_eq_true.1 hie e he)
  set RL := OpsLayK.Snd.runL c D.prog (OpsLayK.initR c A B D.nregs) with hRL
  have hG : ∀ i < m, OpsLayK.Snd.LRel c ((ops3 c.d).coverGens D)[i]!
      ((D.gens.map (OpsLayK.getR c RL)).getD i 0) := by
    intro i hi
    have hi' : i < D.gens.length := by rw [hgl]; exact hi
    simp only [Ops.coverGens, Ops.regsOf]
    rw [toArray_getElem! _ (by simpa using hi'), List.getElem_map,
      List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map]
    exact hL.2 _ (by rw [hlen]; exact hgr' _ (List.getElem_mem _))
  have hI : ∀ i < m, OpsLayK.Snd.LRel c ((ops3 c.d).coverInvs D)[i]!
      (((D.gens.zip D.invExp).map fun p =>
        OpsLayK.powK c (OpsLayK.getR c RL p.1) (p.2 - 1)).getD i 0) := by
    intro i hi
    have hz : i < (D.gens.zip D.invExp).length := by simp [hgl, hil, hi]
    simp only [Ops.coverInvs, Ops.regsOf]
    rw [toArray_getElem! _ (by simpa using hz), List.getElem_map,
      List.getD_eq_getElem _ _ (by simpa using hz), List.getElem_map, List.getElem_zip]
    have hiI : i < D.invExp.length := by rw [hil]; exact hi
    have he : D.invExp[i] - 1 < 65536 := by
      have := hie' _ (List.getElem_mem hiI)
      omega
    exact OpsLayK.Snd.rel_pow hc hp (hL.2 _ (by rw [hlen]; exact hgr' _ (List.getElem_mem _))) he
  have hW : ∀ w : List (Fin m × Bool), OpsLayK.Snd.LRel c
      ((ops3 c.d).evalWordN ((ops3 c.d).coverGens D) ((ops3 c.d).coverInvs D) w)
      (evalWKL c (D.gens.map (OpsLayK.getR c RL))
        ((D.gens.zip D.invExp).map fun p => OpsLayK.powK c (OpsLayK.getR c RL p.1) (p.2 - 1)) w) := by
    intro w
    induction w with
    | nil => exact OpsLayK.Snd.rel_one hc hp
    | cons x w ih =>
      obtain ⟨i, b⟩ := x
      simp only [Ops.evalWordN, evalWKL]
      cases b
      · exact OpsLayK.Snd.rel_mul hc hp (hI i i.isLt) ih
      · exact OpsLayK.Snd.rel_mul hc hp (hG i i.isLt) ih
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hrun
  obtain ⟨hfin, hrels⟩ := hrun
  unfold Ops.coverCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]
  refine ⟨h2, List.all_eq_true.1 hlt, hgl, hil, hgr', fun i _ => ?_, fun w hw => ?_⟩
  · obtain ⟨⟨h0, hpow⟩, hif⟩ := hfin i (List.mem_finRange i)
    have hil' : i.val < D.invExp.length := by rw [hil]; exact i.isLt
    have hei : D.invExp.getD i.val 0 < 65536 := by
      rw [List.getD_eq_getElem _ _ hil']
      exact hie' _ (List.getElem_mem _)
    rw [getElem!_eq_getD]
    refine ⟨h0, OpsLayK.Snd.eq_pow_one hc hp (hG i i.isLt) hei hpow, ?_⟩
    split_ifs at hif ⊢ with he
    · exact OpsLayK.Snd.eq_of_rel (hG i i.isLt) (hW _) hif
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hif
      exact OpsLayK.Snd.eq_pow_one hc hp (hG i i.isLt) hif.1 hif.2
  · exact OpsLayK.Snd.eq_of_rel (hW w) (OpsLayK.Snd.rel_one hc hp) (hrels w hw)

theorem orbitOK_of_KL {m d A B : Nat} {c : Lay} {LA LB : List Char} {D : CoverData m}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB) {ng t : Nat}
    {masks : List Nat} (h : coverOrbitKL c A B D ng t masks = true) :
    (ops3 d).orbitOK (((ops3 d).coverGens D).extract 0 ng) t masks.length (f3Key d)
      (parOf ng masks).toArray (labOf ng masks).toArray = true := by
  subst hd
  simp only [coverOrbitKL, dataOKL, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hprog, hgl, hil, hgr, hie, hng, ht, hrun⟩ := h
  rw [OpsLayK.Snd.runC_eq] at hrun
  simp only [orbitK, Bool.and_eq_true] at hrun
  obtain ⟨⟨hne, -⟩, hrun⟩ := hrun
  have hL := OpsLayK.Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := OpsLayK.Snd.runL_initR_length c D.prog A B D.nregs
  have hgr' : ∀ r ∈ D.gens, r < D.nregs := fun r hr =>
    of_decide_eq_true (List.all_eq_true.1 hgr r hr)
  set RL := OpsLayK.Snd.runL c D.prog (OpsLayK.initR c A B D.nregs) with hRL
  set gK := (D.gens.take ng).map (OpsLayK.getR c RL) with hgK
  have hgKl : gK.length = ng := by simp [hgK, hgl, hng]
  have hsize : ((ops3 c.d).coverGens D).size = m := by simp [Ops.coverGens, hgl]
  have hgen : ∀ g < gK.length, OpsLayK.Snd.LRel c (((ops3 c.d).coverGens D).extract 0 ng)[g]!
      (gK.getD g 0) := by
    intro g hg
    rw [hgKl] at hg
    have hgm : g < D.gens.length := by omega
    rw [getElem!_pos _ g (by simp [hsize]; omega), Array.getElem_extract,
      ← getElem!_pos _ (0 + g) (by rw [hsize]; omega), Nat.zero_add]
    simp only [Ops.coverGens, Ops.regsOf]
    have e : gK.getD g 0 = OpsLayK.getR c RL D.gens[g] := by
      rw [hgK, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_take]
    rw [toArray_getElem! _ (by simpa using hgm), List.getElem_map, e]
    exact hL.2 _ (by rw [hlen]; exact hgr' _ (List.getElem_mem _))
  split at hrun
  next vs hb =>
    obtain ⟨hlenv, hvs, htr⟩ := orbit_run hb
    have hR := orbitVecs_rel (ops3 c.d) (((ops3 c.d).coverGens D).extract 0 ng) t
      (OpsLayK.Snd.LVRel c) (OpsLayK.Snd.vrel_unit hc hp ht)
      (fun w v g hg hwv => OpsLayK.Snd.vrel_vmul hc hp hwv (hgen g hg)) hb
    rw [hgKl] at hvs htr hR
    have hEl : (treeE ng masks 0).length + 1 = masks.length := by
      have := congrArg List.length hvs
      simp only [List.length_cons, List.length_map] at this
      omega
    unfold Ops.orbitOK
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, and_assoc]
    refine ⟨by simp [parOf_eq, hEl], by simp [labOf_eq, hEl],
      List.length_pos_of_ne_nil (by simpa using hne), fun x hx => ?_, ?_⟩
    · cases x with
      | zero => exact Or.inl rfl
      | succ k =>
        right
        have hk : k < (treeE ng masks 0).length := by omega
        obtain ⟨hp', hg⟩ := htr k hk
        rw [toArray_getElem! _ (by rw [parOf_eq]; simpa using hk),
          toArray_getElem! _ (by rw [labOf_eq]; simpa using hk)]
        simp only [parOf_eq, labOf_eq, List.getElem_cons_succ, List.getElem_map, Array.size_extract,
          hsize]
        exact ⟨hp', by omega⟩
    · apply strictInc_mergeSort
      have hnd : vs.Nodup := (msortK_perm vs).nodup_iff.mp
        ((sortedK_pairwise _ hrun).imp fun h => Nat.ne_of_lt h)
      rw [List.Nodup, List.pairwise_iff_getElem] at hnd ⊢
      intro i j hi hj hij heq
      simp only [List.length_map, Array.length_toList, orbitVecs_size] at hi hj
      simp only [List.getElem_map, Array.getElem_toList] at heq
      rw [← getElem!_pos _ i (by simp [orbitVecs_size, hi]),
        ← getElem!_pos _ j (by simp [orbitVecs_size, hj])] at heq
      obtain ⟨ci, wi, ti⟩ := hR i hi
      obtain ⟨cj, wj, tj⟩ := hR j hj
      have hv := f3Key_toVec heq
      rw [ti, tj] at hv
      have := LocalComp.Ops3Snd.vec3_inj c hc ci cj hp hv
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
      exact hnd i j (by omega) (by omega) hij this
  next => exact absurd hrun Bool.false_ne_true

end CFSG.KC.CoverCK

end
