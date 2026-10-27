module

public import Certificates.Data.Kernel.OpsF2KEnum
import all CFSG.Certificates.Kernel.LocalCompCubSound
import all CFSG.Certificates.Kernel.OpsF2KMcertSound

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.SectionRank.Native CFSG.KLie.CT
open CFSG.KC.Co1F2 (unpackR)

private theorem orN_lt' {n w : Nat} {f : Nat → Nat} (h : ∀ i < n, f i < 2 ^ w) :
    orN n f < 2 ^ w := by
  induction n with
  | zero => exact Nat.two_pow_pos w
  | succ n ih =>
    change f n ||| orN n f < 2 ^ w
    exact Nat.or_lt_two_pow (h n (Nat.lt_succ_self n)) (ih fun i hi => h i (Nat.lt_succ_of_lt hi))

private theorem shift_lt {d i x : Nat} (hi : i < d) (hx : x < 2 ^ d) :
    x <<< (d * i) < 2 ^ (d * d) := by
  rw [Nat.shiftLeft_eq]
  calc x * 2 ^ (d * i) < 2 ^ d * 2 ^ (d * i) := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
    _ = 2 ^ (d * (i + 1)) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (d * d) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left d hi)

private theorem mulF_lt (d X Y : Nat) : mulF d X Y < 2 ^ (d * d) := by
  rw [CFSG.KC.F2W.mulF_eq_orN]
  exact orN_lt' fun i hi => shift_lt hi (CFSG.KC.F2W.vmF_lt d Y _)

private theorem idF_lt (d : Nat) : idF d < 2 ^ (d * d) := by
  unfold idF
  refine orN_lt' fun i hi => ?_
  have h2 : pw2 i < 2 ^ d := by
    rw [show pw2 i = 2 ^ i from Nat.one_shiftLeft i]
    exact Nat.pow_lt_pow_right (by norm_num) hi
  exact shift_lt hi h2

private theorem unpackR_inj {d X Y : Nat} (hX : X < 2 ^ (d * d)) (hY : Y < 2 ^ (d * d))
    (h : unpackR d X = unpackR d Y) : X = Y := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < d * d
  · have hd : 0 < d := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hk
    have hi : k / d < d := (Nat.div_lt_iff_lt_mul hd).2 hk
    have hj : k % d < d := Nat.mod_lt _ hd
    have e := congrArg (fun A : Array Nat => A[k / d]!) h
    simp only [unpackR] at e
    rw [getElem!_pos _ _ (by simpa using hi), getElem!_pos _ _ (by simpa using hi),
      Array.getElem_ofFn, Array.getElem_ofFn] at e
    have e2 := congrArg (fun x => x.testBit (k % d)) e
    simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and,
      Nat.testBit_div_two_pow] at e2
    rwa [show k % d + d * (k / d) = k from Nat.mod_add_div k d] at e2
  · have hle : 2 ^ (d * d) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hX hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hY hle)]

private theorem eq_unpackR_iff {d X Y : Nat} (hX : X < 2 ^ (d * d)) (hY : Y < 2 ^ (d * d)) :
    (ops2 d).eq (unpackR d X) (unpackR d Y) = Nat.beq X Y := by
  change (unpackR d X == unpackR d Y) = Nat.beq X Y
  by_cases e : X = Y
  · subst e
    rw [Nat.beq_refl]
    exact beq_self_eq_true _
  · rw [CFSG.KC.LocalComp.Cub.nat_beq_false.mpr e]
    exact beq_eq_false_iff_ne.mpr fun h => e (unpackR_inj hX hY h)

private def gStep {M V : Type} (O : Ops M V) [Inhabited M] (gens : Array M) (h : Nat) (X : M)
    (s : Array M × Array Nat × Array Nat × Array Nat) (g : Nat) :
    Array M × Array Nat × Array Nat × Array Nat :=
  match s.1.findIdx? (fun Z => O.eq (O.mul X gens[g]!) Z) with
  | some j => (s.1, s.2.1, s.2.2.1, s.2.2.2.push j)
  | none => (s.1.push (O.mul X gens[g]!), s.2.1.push h, s.2.2.1.push g, s.2.2.2.push s.1.size)

private def hStep {M V : Type} (O : Ops M V) [Inhabited M] (gens : Array M)
    (s : Array M × Array Nat × Array Nat × Array (Array Nat)) (h : Nat) :
    Array M × Array Nat × Array Nat × Array (Array Nat) :=
  if h < s.1.size then
    let r := (List.range' 0 gens.size).foldl (gStep O gens h s.1[h]!) (s.1, s.2.1, s.2.2.1, #[])
    (r.1, r.2.1, r.2.2.1, s.2.2.2.push r.2.2.2)
  else s

private theorem forIn_eq_pure_foldl {β : Type} (l : List Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) (F : β → Nat → β)
    (hf : ∀ a b, f a b = pure (ForInStep.yield (F b a))) :
    forIn l init f = pure (l.foldl F init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, hf]
    exact ih (F init a)

private theorem range_size (n : Nat) : ([:n] : Std.Legacy.Range).size = n := by
  simp [Std.Legacy.Range.size]

private theorem enumBFS_eq_foldl {M V : Type} (O : Ops M V) [Inhabited M] (gens : Array M)
    (cap : Nat) :
    O.enumBFS gens cap = (List.range' 0 cap).foldl (hStep O gens) (#[O.one], #[0], #[0], #[]) := by
  unfold Ops.enumBFS
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', range_size]
  rw [forIn_eq_pure_foldl _ _ _ (hStep O gens) ?_]
  · rfl
  · intro h s
    unfold hStep
    split_ifs with hh
    · rw [forIn_eq_pure_foldl _ _ _ (gStep O gens h s.1[h]!) ?_]
      · rfl
      · intro g s1
        unfold gStep
        cases Array.findIdx? (fun Z => O.eq (O.mul s.1[h]! gens[g]!) Z) s1.1 <;> rfl
    · rfl

private abbrev upk (d : Nat) (E : List Nat) : Array (Array Nat) := (E.map (unpackR d)).toArray

private abbrev upk4 (d : Nat) (s : List Nat × List Nat × List Nat × List Nat) :
    Array (Array Nat) × Array Nat × Array Nat × Array Nat :=
  (upk d s.1, s.2.1.toArray, s.2.2.1.toArray, s.2.2.2.toArray)

private abbrev upkS (d : Nat) (s : EnSt) :
    Array (Array Nat) × Array Nat × Array Nat × Array (Array Nat) :=
  (upk d s.1, s.2.1.toArray, s.2.2.1.toArray, (s.2.2.2.map List.toArray).toArray)

private def Canon (d : Nat) (E : List Nat) : Prop := ∀ x ∈ E, x < 2 ^ (d * d)

private theorem findK_eq (y : Nat) :
    ∀ (L : List Nat) (i : Nat), findK y L i = (L.findIdx? (Nat.beq y)).map (· + i)
  | [], _ => rfl
  | z :: zs, i => by
    rw [findK, List.findIdx?_cons]
    cases hz : Nat.beq y z
    · simp only [Bool.false_eq_true, if_false, findK_eq y zs (i + 1), Option.map_map]
      congr 1
      funext k
      simp only [Function.comp_apply]
      omega
    · simp

private theorem findIdx?_map_upk {d Y : Nat} (hY : Y < 2 ^ (d * d)) :
    ∀ (E : List Nat), Canon d E →
      (E.map (unpackR d)).findIdx? (fun Z => (ops2 d).eq (unpackR d Y) Z) =
        E.findIdx? (Nat.beq Y)
  | [], _ => rfl
  | z :: zs, hE => by
    rw [List.map_cons, List.findIdx?_cons, List.findIdx?_cons,
      eq_unpackR_iff hY (hE z (by simp)),
      findIdx?_map_upk hY zs fun x hx => hE x (by simp [hx])]

private theorem findIdx?_upk {d Y : Nat} {E : List Nat} (hY : Y < 2 ^ (d * d)) (hE : Canon d E) :
    (upk d E).findIdx? (fun Z => (ops2 d).eq (unpackR d Y) Z) = findK Y E 0 := by
  rw [List.findIdx?_toArray, findIdx?_map_upk hY E hE, findK_eq]
  simp

private theorem enumGens_lockstep {d h X : Nat} {gensN : Array (Array Nat)} :
    ∀ (gs : List Nat) (g₀ : Nat) (s : List Nat × List Nat × List Nat × List Nat),
      Canon d s.1 → (∀ i < gs.length, gensN[g₀ + i]! = unpackR d (gs.getD i 0)) →
      (List.range' g₀ gs.length).foldl (gStep (ops2 d) gensN h (unpackR d X)) (upk4 d s) =
        upk4 d (enumGensK d h X gs g₀ s) ∧ Canon d (enumGensK d h X gs g₀ s).1
  | [], _, _, hs, _ => ⟨rfl, hs⟩
  | G :: gs, g₀, (E, par, lab, row), hs, hg => by
    have hG : gensN[g₀]! = unpackR d G := by simpa using hg 0 (by simp)
    have hg' : ∀ i < gs.length, gensN[g₀ + 1 + i]! = unpackR d (gs.getD i 0) := by
      intro i hi
      have := hg (i + 1) (by simp; omega)
      rwa [show g₀ + (i + 1) = g₀ + 1 + i by omega, List.getD_cons_succ] at this
    have hY : (ops2 d).mul (unpackR d X) gensN[g₀]! = unpackR d (mulF d X G) := by
      rw [hG, unpackR_mulF]
    have hfind := findIdx?_upk (mulF_lt d X G) hs
    rw [List.length_cons, List.range'_succ, List.foldl_cons]
    have hstep : gStep (ops2 d) gensN h (unpackR d X) (upk4 d (E, par, lab, row)) g₀ =
        match findK (mulF d X G) E 0 with
        | some j => upk4 d (E, par, lab, row ++ [j])
        | none => upk4 d (E ++ [mulF d X G], par ++ [h], lab ++ [g₀], row ++ [E.length]) := by
      unfold gStep
      rw [hY]
      simp only [upk4, upk] at hfind ⊢
      rw [hfind]
      cases findK (mulF d X G) E 0 <;> simp
    rw [hstep]
    show _ = upk4 d (match findK (mulF d X G) E 0 with
      | some j => enumGensK d h X gs (g₀ + 1) (E, par, lab, row ++ [j])
      | none => enumGensK d h X gs (g₀ + 1)
          (E ++ [mulF d X G], par ++ [h], lab ++ [g₀], row ++ [E.length])) ∧
      Canon d (match findK (mulF d X G) E 0 with
      | some j => enumGensK d h X gs (g₀ + 1) (E, par, lab, row ++ [j])
      | none => enumGensK d h X gs (g₀ + 1)
          (E ++ [mulF d X G], par ++ [h], lab ++ [g₀], row ++ [E.length])).1
    cases findK (mulF d X G) E 0 with
    | some j =>
      exact enumGens_lockstep (h := h) (X := X) gs (g₀ + 1) (E, par, lab, row ++ [j]) hs hg'
    | none =>
      have hs' : Canon d (E ++ [mulF d X G]) := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hs x hx
        · rw [List.mem_singleton.1 hx]
          exact mulF_lt d X G
      exact enumGens_lockstep (h := h) (X := X) gs (g₀ + 1)
        (E ++ [mulF d X G], par ++ [h], lab ++ [g₀], row ++ [E.length]) hs' hg'

private theorem getElem!_upk {d : Nat} {E : List Nat} {i : Nat} (hi : i < E.length) :
    (upk d E)[i]! = unpackR d (E.getD i 0) := by
  simp [upk, hi]

private theorem enumStep_lockstep {d : Nat} {gens : List Nat} (s : EnSt) (hs : Canon d s.1)
    (h : Nat) :
    hStep (ops2 d) (upk d gens) (upkS d s) h = upkS d (enumStepK d gens s h) ∧
      Canon d (enumStepK d gens s h).1 := by
  obtain ⟨E, par, lab, cl⟩ := s
  have hgens : ∀ i < gens.length, (upk d gens)[0 + i]! = unpackR d (gens.getD i 0) :=
    fun i hi => by rw [Nat.zero_add]; exact getElem!_upk hi
  by_cases hh : h < E.length
  · have hX : (upk d E)[h]! = unpackR d (E.getD h 0) := getElem!_upk hh
    obtain ⟨e, c⟩ := enumGens_lockstep (h := h) (X := E.getD h 0) gens 0 (E, par, lab, []) hs
      hgens
    have hsz : (upk d gens).size = gens.length := by simp [upk]
    unfold hStep enumStepK
    simp only [upkS, if_pos (show h < (upk d E).size by simpa [upk] using hh), if_pos hh]
    rw [hX, hsz]
    simp only [upk4] at e
    refine ⟨?_, c⟩
    simp only [upk] at e ⊢
    rw [e]
    simp
  · unfold hStep enumStepK
    simp only [upkS, if_neg (show ¬ h < (upk d E).size by simpa [upk] using hh), if_neg hh]
    exact ⟨by trivial, hs⟩

private theorem enumBFS_lockstep (d : Nat) (gens : List Nat) (cap : Nat) :
    (ops2 d).enumBFS (upk d gens) cap = upkS d (enumK d gens cap) ∧
      Canon d (enumK d gens cap).1 := by
  rw [enumBFS_eq_foldl]
  unfold enumK
  rw [List.range_eq_range']
  have hinit : ((#[(ops2 d).one], #[0], #[0], #[]) :
      Array (Array Nat) × Array Nat × Array Nat × Array (Array Nat)) =
      upkS d ([idF d], [0], [0], []) := by
    simp [upkS, upk, unpackR_idF_eq_one]
  rw [hinit]
  have key : ∀ (l : List Nat) (s : EnSt), Canon d s.1 →
      l.foldl (hStep (ops2 d) (upk d gens)) (upkS d s) = upkS d (l.foldl (enumStepK d gens) s) ∧
        Canon d (l.foldl (enumStepK d gens) s).1 := by
    intro l
    induction l with
    | nil => intro s hs; exact ⟨rfl, hs⟩
    | cons h l ih =>
      intro s hs
      obtain ⟨e, c⟩ := enumStep_lockstep s hs h
      rw [List.foldl_cons, List.foldl_cons, e]
      exact ih _ c
  exact key _ _ (by
    intro x hx
    rw [List.mem_singleton.1 hx]
    exact idF_lt d)

private theorem getElem!_toArray_nat {L : List Nat} {i : Nat} : L.toArray[i]! = L.getD i 0 := by
  by_cases hi : i < L.length
  · simp [hi]
  · simp [hi]

private theorem getElem!_cl {cl : List (List Nat)} {i g : Nat} :
    ((cl.map List.toArray).toArray[i]!)[g]! = (cl.getD i []).getD g 0 := by
  by_cases hi : i < cl.length
  · simp [hi]
  · have h1 : (cl.map List.toArray).toArray[i]! = #[] := by
      rw [getElem!_neg _ _ (by simpa using hi)]
      rfl
    rw [h1, List.getD_eq_default cl [] (show cl.length ≤ i by omega)]
    simp

private theorem distinctK_iff_nodup : ∀ L : List Nat, distinctK L = true ↔ L.Nodup
  | [] => by simp [distinctK]
  | x :: xs => by
    change (xs.all (fun y => !(Nat.beq x y)) && distinctK xs) = true ↔ _
    rw [Bool.and_eq_true, List.all_eq_true, distinctK_iff_nodup xs]
    constructor
    · rintro ⟨h1, h2⟩
      refine List.nodup_cons.2 ⟨fun hx => ?_, h2⟩
      have := h1 x hx
      rw [Bool.not_eq_true', CFSG.KC.LocalComp.Cub.nat_beq_false] at this
      exact this rfl
    · intro h
      obtain ⟨hx, h2⟩ := List.nodup_cons.1 h
      refine ⟨fun y hy => ?_, h2⟩
      rw [Bool.not_eq_true', CFSG.KC.LocalComp.Cub.nat_beq_false]
      exact fun e => hx (e ▸ hy)

private theorem distinctOK_of_distinctK {d : Nat} {L : List Nat} (hL : ∀ x ∈ L, x < 2 ^ d)
    (h : distinctK L = true) : (ops2 d).distinctOK L.toArray = true := by
  unfold Ops.distinctOK
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  have hiL : i < L.length := by simpa using hi
  have hjI : j < i := by simpa using hj
  have hnd := (distinctK_iff_nodup L).1 h
  rw [getElem!_toArray_nat, getElem!_toArray_nat, List.getD_eq_getElem _ _ hiL,
    List.getD_eq_getElem _ _ (by omega)]
  have hne : L[i] ≠ L[j] := fun e => by
    rw [List.Nodup.getElem_inj hnd] at e
    omega
  rw [CFSG.KC.LocalComp.Cub.vne_eq, Nat.mod_eq_of_lt (hL _ (List.getElem_mem _)),
    Nat.mod_eq_of_lt (hL _ (List.getElem_mem _)), CFSG.KC.LocalComp.Cub.nat_beq_false.mpr hne]
  rfl

private theorem vecs_upk {d t : Nat} (E : List Nat) :
    (upk d E).map (fun X => (ops2 d).vmul ((ops2 d).unit t) X) =
      (E.map fun X => vmF d X (pw2 t)).toArray := by
  simp only [upk, List.map_toArray, List.map_map]
  congr 1
  refine List.map_congr_left fun X _ => ?_
  simp only [Function.comp_apply]
  rw [unit_eq, vmul_unpackR]

private theorem enumOK_of_K {d n t : Nat} {gens : List Nat} {s : EnSt}
    (h : enumOKK d gens n t s = true) :
    (ops2 d).enumOK (upk d gens) n t (upkS d s).1 (upkS d s).2.1 (upkS d s).2.2.1
      (upkS d s).2.2.2 = true := by
  obtain ⟨E, par, lab, cl⟩ := s
  unfold enumOKK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hE, hpar⟩, hlab⟩, hcl⟩, hn⟩, h0⟩, htree⟩, hclose⟩, hdist⟩ := h
  unfold Ops.enumOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨by simp [upk, hE], by simp [hpar]⟩, by simp [hlab]⟩, by simp [hcl]⟩, hn⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have e0 : (upk d E)[0]! = unpackR d (E.getD 0 0) := getElem!_upk (by omega)
    rw [e0, ← unpackR_idF_eq_one]
    exact eq_of_beq h0
  · intro i hi
    rcases htree i hi with h | ⟨⟨hp, hl⟩, hb⟩
    · exact Or.inl h
    · have e1 : (upk d E)[i]! = unpackR d (E.getD i 0) := getElem!_upk (by omega)
      have e2 : (upk d E)[par.getD i 0]! = unpackR d (E.getD (par.getD i 0) 0) :=
        getElem!_upk (by omega)
      have e3 : (upk d gens)[lab.getD i 0]! = unpackR d (gens.getD (lab.getD i 0) 0) :=
        getElem!_upk hl
      refine Or.inr ⟨⟨?_, ?_⟩, ?_⟩
      · rw [getElem!_toArray_nat]
        exact hp
      · rw [getElem!_toArray_nat]
        simpa [upk] using hl
      · rw [getElem!_toArray_nat, getElem!_toArray_nat, e1, e2, e3, ← unpackR_mulF]
        exact eq_of_beq hb
  · intro i hi g hg
    have hg' : g < gens.length := by simpa [upk] using hg
    obtain ⟨hc, hb⟩ := hclose i hi g hg'
    have e1 : (upk d E)[i]! = unpackR d (E.getD i 0) := getElem!_upk (by omega)
    have e2 : (upk d gens)[g]! = unpackR d (gens.getD g 0) := getElem!_upk hg'
    have e3 : (upk d E)[(cl.getD i []).getD g 0]! =
        unpackR d (E.getD ((cl.getD i []).getD g 0) 0) :=
      getElem!_upk (by omega)
    refine ⟨?_, ?_⟩
    · rw [getElem!_cl]
      exact hc
    · rw [getElem!_cl, e1, e2, e3, ← unpackR_mulF]
      exact eq_of_beq hb
  · rw [vecs_upk]
    exact distinctOK_of_distinctK (fun x hx => by
      obtain ⟨X, -, rfl⟩ := List.mem_map.1 hx
      exact CFSG.KC.F2W.vmF_lt d X _) hdist

private theorem memOK_of_K {d X : Nat} {E : List Nat} (h : memK E X = true) :
    (ops2 d).memOK (upk d E) (unpackR d X) = true := by
  unfold memK at h
  obtain ⟨z, hz, hb⟩ := List.any_eq_true.1 h
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
  unfold Ops.memOK
  refine List.any_eq_true.2 ⟨j, List.mem_range.2 (by simpa [upk] using hj), ?_⟩
  rw [getElem!_upk hj, List.getD_eq_getElem _ _ hj]
  exact eq_of_beq hb

private theorem appK_eqF (d X : Nat) : ∀ (n v : Nat),
    (ops2 d).app (unpackR d X) n v = appK d X n v
  | 0, _ => rfl
  | n + 1, v => by
    change (ops2 d).app (unpackR d X) n (CFSG.Sporadic.SmallF2.Native.vecMulN d (unpackR d X) v) =
      appK d X n (vmF d X v)
    rw [CFSG.KC.F2W.vecMulN_unpackR]
    exact appK_eqF d X n (vmF d X v)

private theorem appBaseK_eqF (d b : Nat) :
    ∀ (xs : List Nat) (n v : Nat),
      (ops2 d).appBase b (xs.map (unpackR d)) n v = appBaseK d b xs n v
  | [], _, _ => rfl
  | X :: xs, n, v => by
    change (ops2 d).appBase b (xs.map (unpackR d)) (n / b)
      ((ops2 d).app (unpackR d X) (n % b) v) =
      appBaseK d b xs (n / b) (appK d X (n % b) v)
    rw [← appK_eqF]
    exact appBaseK_eqF d b xs (n / b) ((ops2 d).app (unpackR d X) (n % b) v)

private theorem appK_ltF (d X n v : Nat) (hv : v < 2 ^ d) : appK d X n v < 2 ^ d := by
  induction n generalizing v with
  | zero => exact hv
  | succ n ih => exact ih (v := vmF d X v) (CFSG.KC.F2W.vmF_lt d X v)

private theorem appBaseK_ltF (d b : Nat) :
    ∀ (xs : List Nat) (n v : Nat), v < 2 ^ d → appBaseK d b xs n v < 2 ^ d
  | [], _, _, hv => hv
  | X :: xs, n, v, hv => appBaseK_ltF d b xs (n / b) (appK d X (n % b) v) (appK_ltF d X _ v hv)

private theorem normalFormOK_of_K {d t X Y : Nat} (ht : t < d)
    (h : distinctK ((List.range (3 ^ 2)).map fun n => appBaseK d 3 [X, Y] n (pw2 t)) = true) :
    (ops2 d).normalFormOK 3 [unpackR d X, unpackR d Y] t = true := by
  unfold Ops.normalFormOK
  have hvs : (Array.ofFn (n := 3 ^ [unpackR d X, unpackR d Y].length) fun n =>
      (ops2 d).appBase 3 [unpackR d X, unpackR d Y] n.val ((ops2 d).unit t)) =
      ((List.range (3 ^ 2)).map fun n => appBaseK d 3 [X, Y] n (pw2 t)).toArray := by
    ext i hi1 hi2
    · simp
    · simp only [Array.getElem_ofFn, List.getElem_toArray, List.getElem_map, List.getElem_range]
      rw [show [unpackR d X, unpackR d Y] = [X, Y].map (unpackR d) from rfl, appBaseK_eqF]
      rfl
  rw [hvs]
  exact distinctOK_of_distinctK (fun x hx => by
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hx
    exact appBaseK_ltF d 3 [X, Y] n (pw2 t) (pw2_lt ht)) h

private theorem pow_one_of_K {d X e : Nat} (he : e < 2 ^ 16)
    (h : Nat.beq (powK d X e) (idF d) = true) :
    (ops2 d).eq ((ops2 d).pow (unpackR d X) e) (ops2 d).one = true := by
  rw [← unpackR_powK he, ← unpackR_idF_eq_one]
  exact eq_of_beq h

theorem sylowCentralCheck_of_K {d A B : Nat} {csA csB : List Char} {D : SylowCentralData}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (h : sylowCentralK d A B D = true) : (ops2 d).sylowCentralCheck D = true := by
  simp only [sylowCentralK, baseOK, genFactsK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, hexp, ht, hn, hprog, hregs, ho1, ho2, ho1', ho2', hK1, hK2, henum, hmX, hmY, hX3, hY3,
    hXY, hnf, hc1, hc2, hc3, hc4⟩ := h
  have hregs' := hregs
  simp only [SylowCentralData.regsLt, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hregs'
  obtain ⟨hr1, hr2, hrx, hry⟩ := hregs'
  have hreg : ∀ r < D.nregs, ((ops2 d).regsOf D.seedA D.seedB D.nregs D.prog)[r]! =
      unpackR d (getR d (runK d A B D.nregs D.prog) r) :=
    fun r hr => mRegs_get hA hB hsA hsB hprog hexp hr
  obtain ⟨hEn, -⟩ := enumBFS_lockstep d
    [getR d (runK d A B D.nregs D.prog) D.rk1, getR d (runK d A B D.nregs D.prog) D.rk2] D.nP
  unfold Ops.sylowCentralCheck Ops.sylowCentralFacts Ops.sylowGenFacts Ops.qFacts Ops.centralFacts
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  rw [hreg _ hr1, hreg _ hr2, hreg _ hrx, hreg _ hry]
  rw [show (#[unpackR d (getR d (runK d A B D.nregs D.prog) D.rk1),
      unpackR d (getR d (runK d A B D.nregs D.prog) D.rk2)] : Array (Array Nat)) =
      upk d [getR d (runK d A B D.nregs D.prog) D.rk1, getR d (runK d A B D.nregs D.prog) D.rk2]
      from rfl, hEn]
  exact ⟨hn, hprog, hregs, ho1, ho2, pow_one_of_K (by omega) hK1, pow_one_of_K (by omega) hK2,
    enumOK_of_K henum, memOK_of_K hmX, memOK_of_K hmY, pow_one_of_K (by norm_num) hX3,
    pow_one_of_K (by norm_num) hY3, commOK_of_commK hXY, normalFormOK_of_K ht hnf,
    commOK_of_commK hc1, commOK_of_commK hc2, commOK_of_commK hc3, commOK_of_commK hc4⟩

theorem commTripleCheck_of_K {d A B : Nat} {csA csB : List Char} {D : CommTripleData}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.base.seedA = String.ofList csA) (hsB : D.base.seedB = String.ofList csB)
    (h : commTripleK d A B D = true) : (ops2 d).commTripleCheck D = true := by
  simp only [commTripleK, baseOK, genFactsK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, hexp, ht, hn, hprog, hregs, ho1, ho2, ho1', ho2', hK1, hK2, henum, h9, htrip,
    hdist⟩ := h
  have hregs' := hregs
  simp only [SylowCentralData.regsLt, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hregs'
  obtain ⟨hr1, hr2, -, -⟩ := hregs'
  have hreg : ∀ r < D.base.nregs,
      ((ops2 d).regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog)[r]! =
        unpackR d (getR d (runK d A B D.base.nregs D.base.prog) r) :=
    fun r hr => mRegs_get hA hB hsA hsB hprog hexp hr
  obtain ⟨hEn, -⟩ := enumBFS_lockstep d
    [getR d (runK d A B D.base.nregs D.base.prog) D.base.rk1,
      getR d (runK d A B D.base.nregs D.base.prog) D.base.rk2] D.base.nP
  unfold Ops.commTripleCheck Ops.commTripleFacts Ops.sylowGenFacts
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  rw [hreg _ hr1, hreg _ hr2]
  rw [show (#[unpackR d (getR d (runK d A B D.base.nregs D.base.prog) D.base.rk1),
      unpackR d (getR d (runK d A B D.base.nregs D.base.prog) D.base.rk2)] : Array (Array Nat)) =
      upk d [getR d (runK d A B D.base.nregs D.base.prog) D.base.rk1,
        getR d (runK d A B D.base.nregs D.base.prog) D.base.rk2]
      from rfl, hEn]
  have hT : ∀ t ∈ D.trip, t.1 < D.base.nregs ∧ t.2.1 < D.base.nregs ∧ t.2.2 < D.base.nregs ∧
      (t.2.2 == D.base.rk1 || t.2.2 == D.base.rk2) = true ∧
      memK (enumK d [getR d (runK d A B D.base.nregs D.base.prog) D.base.rk1,
        getR d (runK d A B D.base.nregs D.base.prog) D.base.rk2] D.base.nP).1
        (getR d (runK d A B D.base.nregs D.base.prog) t.2.1) = true ∧
      Nat.beq (powK d (getR d (runK d A B D.base.nregs D.base.prog) t.1) 3) (idF d) = true ∧
      Nat.beq (mulF d (getR d (runK d A B D.base.nregs D.base.prog) t.1)
        (mulF d (getR d (runK d A B D.base.nregs D.base.prog) t.2.2)
          (getR d (runK d A B D.base.nregs D.base.prog) t.2.1)))
        (mulF d (getR d (runK d A B D.base.nregs D.base.prog) t.2.1)
          (getR d (runK d A B D.base.nregs D.base.prog) t.2.2)) = true := by
    intro t ht
    have := List.all_eq_true.1 htrip t ht
    simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using this
  refine ⟨hn, hprog, hregs, ho1, ho2, pow_one_of_K (by omega) hK1, pow_one_of_K (by omega) hK2,
    enumOK_of_K henum, h9, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro t ht
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hT t ht
    unfold Ops.commTripleOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    rw [hreg _ h1, hreg _ h2, hreg _ h3]
    refine ⟨h1, h2, h3, h4, memOK_of_K h5, pow_one_of_K (by norm_num) h6, ?_⟩
    rw [← unpackR_mulF, ← unpackR_mulF, ← unpackR_mulF]
    exact eq_of_beq h7
  · have hvec : (D.trip.toArray.map fun t => (ops2 d).vmul ((ops2 d).unit D.base.t)
        ((ops2 d).regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog)[t.1]!) =
        (D.trip.map fun t =>
          vmF d (getR d (runK d A B D.base.nregs D.base.prog) t.1) (pw2 D.base.t)).toArray := by
      rw [List.map_toArray]
      congr 1
      refine List.map_congr_left fun t ht => ?_
      rw [hreg _ (hT t ht).1, unit_eq, vmul_unpackR]
    rw [hvec]
    exact distinctOK_of_distinctK (fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
      exact CFSG.KC.F2W.vmF_lt d _ _) hdist

end CFSG.KC.OpsF2K

end
