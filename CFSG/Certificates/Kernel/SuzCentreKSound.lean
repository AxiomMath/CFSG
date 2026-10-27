module

public import Certificates.Data.Kernel.SuzCentreK
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18SuzCenterTests
public import CFSG.Certificates.Kernel.HexaKGlue
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.SuzCentreK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK
open CFSG.ComponentClassification.AS81.SuzCenter CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native
open CFSG.KLie.CT (andB orB notB)

theorem _root_.CFSG.KC.BfsPin.PP_of_permOK' {n w p q : Nat} (hsz : szOK n w = true)
    (h : permOK n w (mask w) (n * w) p q = true) : PP n w p := by
  obtain ⟨h1, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  have hc : canonK n w (mask w) (n * w) p = true := by
    unfold canonK
    simp only [bAnd_iff]
    exact ⟨hsz, Nat.beq_eq.mpr h1,
      CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (h3 i hi).1⟩
  refine ⟨hc, ⟨fun i hi => (h3 i hi).1, fun a ha b hb e => ?_⟩⟩
  rw [← (h3 a ha).2, ← (h3 b hb).2, e]

theorem comp_eq_compA (n : Nat) (p q : Array Nat) : comp n p q = compA n p q := rfl

theorem idTab_eq_idA (n : Nat) : idTab n = idA n := rfl

theorem wordC_unpack {g : Nat} {G : Nat → Nat} (hsz : szOK 1782 11 = true)
    (hG : ∀ k < g, PP 1782 11 (G k)) :
    ∀ w : List Nat, (∀ j ∈ w, j < g) →
      wordC (Array.ofFn (n := g) fun k => unpack 1782 11 (G k.val)) w =
        unpack 1782 11 (wordK G w) ∧ PP 1782 11 (wordK G w)
  | [], _ => ⟨by rw [wordC, List.foldr_nil, idTab_eq_idA, idA_eq hsz]; rfl, PP.id hsz⟩
  | j :: w, hw => by
    obtain ⟨ih1, ih2⟩ := wordC_unpack hsz hG w fun i hi => hw i (List.mem_cons_of_mem _ hi)
    have hj : j < g := hw j List.mem_cons_self
    have e1 : wordC (Array.ofFn (n := g) fun k => unpack 1782 11 (G k.val)) (j :: w) =
        comp 1782 (Array.ofFn (n := g) fun k => unpack 1782 11 (G k.val))[j]!
          (wordC (Array.ofFn (n := g) fun k => unpack 1782 11 (G k.val)) w) := by
      simp only [wordC, List.foldr_cons]
    have e2 : wordK G (j :: w) = mul 1782 11 (G j) (wordK G w) := strictN_eq' _ _
    rw [e1, e2, ih1, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, comp_eq_compA,
      compA_PP (hG j hj) ih2]
    exact ⟨rfl, (hG j hj).mul ih2⟩

theorem allL_eq (l : List Nat) (f : Nat → Bool) : allL l f = l.all f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change CFSG.KLie.CT.andB (f x) (allL l f) = _
    rw [ih, andB_eq, List.all_cons]

theorem anyL_eq (l : List Nat) (f : Nat → Bool) : anyL l f = l.any f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change CFSG.KLie.CT.orB (f x) (anyL l f) = _
    rw [ih, orB_eq, List.any_cons]

theorem cntL_eq (l : List Nat) (f : Nat → Bool) : cntL l f = (l.filter f).length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change strictN (cntL l f) (fun c => Bool.rec (motive := fun _ => Nat) c (Nat.succ c) (f x)) = _
    rw [strictN_eq', ih]
    cases hx : f x <;> simp [hx]

theorem lenL_eq (l : List Nat) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Nat.succ (lenL l) = _
    rw [ih, List.length_cons]

theorem getL_eq (l : List Nat) (i : Nat) : getL l i = l[i]! := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => exact List.getElem!_cons_zero.symm
    | succ i =>
      change getL l i = _
      rw [ih, List.getElem!_cons_succ]

theorem nodupL_rec (l : List Nat) : ∀ acc : Nat,
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun x _ ih acc => CFSG.KLie.CT.andB (Nat.beq (Nat.land (Nat.shiftRight acc x) 1) 0)
        (ih (Nat.lor acc (Nat.shiftLeft 1 x)))) l acc = true →
      l.Nodup ∧ ∀ x ∈ l, acc.testBit x = false := by
  induction l with
  | nil => exact fun _ _ => ⟨List.nodup_nil, by simp⟩
  | cons x l ih =>
    intro acc h
    change CFSG.KLie.CT.andB _ _ = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hn, hb⟩ := ih _ h2
    have hx : acc.testBit x = false := by
      have e : 1 &&& (acc >>> x) = 0 := by
        rw [Nat.and_comm]
        exact Nat.eq_of_beq_eq_true h1
      unfold Nat.testBit
      rw [e]
      rfl
    have hb' : ∀ y ∈ l, acc.testBit y = false ∧ y ≠ x := by
      intro y hy
      have e := hb y hy
      change (acc ||| 1 <<< x).testBit y = false at e
      rw [Nat.testBit_or,Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at e
      exact ⟨e.1, fun h' => e.2 h'.symm⟩
    refine ⟨List.nodup_cons.2 ⟨fun hm => (hb' x hm).2 rfl, hn⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact (hb' y hy).1

theorem nodupL_sound {l : List Nat} (h : nodupL l = true) : l.Nodup := (nodupL_rec l 0 h).1

theorem wordsK_eq (G : Nat → Nat) (ws : List (List Nat)) : wordsK G ws = ws.map (wordK G) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change wordK G w :: wordsK G ws = _
    rw [ih, List.map_cons]

theorem lettersK_spec {g : Nat} {ws : List (List Nat)} (h : lettersK g ws = true) :
    ∀ w ∈ ws, ∀ j ∈ w, j < g := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    change CFSG.KLie.CT.andB _ _ = true at h
    rw [andB_eq, Bool.and_eq_true, allL_eq, List.all_eq_true] at h
    intro v hv j hj
    rcases List.mem_cons.1 hv with rfl | hv
    · exact Nat.blt_eq.mp (h.1 j hj)
    · exact ih h.2 v hv j hj

theorem prodK_eq (Ls : List CentreLevel) : prodK Ls = (Ls.map (·.pts.length)).prod := by
  induction Ls with
  | nil => rfl
  | cons L Ls ih =>
    change Nat.mul (lenL L.pts) (prodK Ls) = _
    rw [ih, lenL_eq, List.map_cons, List.prod_cons]
    rfl

theorem basesK_spec {O : List Nat} {Ls : List CentreLevel} (h : basesK O Ls = true) :
    ∀ L ∈ Ls, L.b ∈ O := by
  induction Ls with
  | nil => simp
  | cons L Ls ih =>
    change CFSG.KLie.CT.andB _ _ = true at h
    rw [andB_eq, Bool.and_eq_true, anyL_eq, List.any_eq_true] at h
    intro L' hL
    rcases List.mem_cons.1 hL with rfl | hL
    · obtain ⟨x, hx, e⟩ := h.1
      rwa [← Nat.eq_of_beq_eq_true e]
    · exact ih h.2 L' hL

theorem fixAllK_eq (t : Nat) (ps : List Nat) : fixAllK t ps = fixesAll (unpack 1782 11 t) ps := by
  unfold fixAllK fixesAll
  rw [allL_eq]
  refine all_congr_mem fun p _ => ?_
  rw [pgC_eq, beq_nat]

theorem fixesAll_congr {t : Tab} {B B' : List Nat} (hB : ∀ x, x ∈ B ↔ x ∈ B')
    (h : fixesAll t B = true) : fixesAll t B' = true := by
  unfold fixesAll at *
  rw [List.all_eq_true] at *
  exact fun x hx => h x ((hB x).2 hx)

theorem getElem!_map_toArray {hs : List Nat} {f : Nat → Array Nat} {k : Nat}
    (hk : k < hs.length) : (hs.map f).toArray[k]! = f hs[k]! := by
  rw [getElem!_pos (hs.map f).toArray k (by simpa using hk), getElem!_pos hs k hk]
  simp

theorem treeK_sound {hs : List Nat} {L : CentreLevel} (h : treeK hs L = true) :
    treeOK (hs.map (unpack 1782 11)).toArray L = true := by
  unfold treeK at h
  simp only [strictB_eq', andB_eq, orB_eq, lenL_eq, getL_eq, pgC_eq, allL_eq, allN_eq',
    Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  unfold CFSG.ComponentClassification.AS81.SuzCenter.treeOK
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, List.size_toArray, List.length_map]
  refine ⟨⟨⟨⟨⟨h1, h2⟩, ?_⟩, nodupL_sound h5⟩, h6⟩, fun j hj => ?_⟩
  · obtain ⟨a, t, hp⟩ := List.exists_cons_of_length_pos h3
    rw [hp, List.getElem!_cons_zero] at h4
    rw [hp, List.head?_cons, h4]
  · rcases h7 j hj with e | ⟨e1, e2, e3⟩
    · exact Or.inl e
    · exact Or.inr ⟨⟨e1, e2⟩, by rw [getElem!_map_toArray e2]; exact e3⟩

section Levels

variable {g : Nat} {G : Nat → Nat}

theorem levelsK_sound (hsz : szOK 1782 11 = true) (hp : ∀ k < g, PP 1782 11 (G k)) :
    ∀ (Ls : List CentreLevel) (B B' : List Nat), (∀ x, x ∈ B ↔ x ∈ B') →
      levelsK g G Ls B = true →
      levelsOK (Array.ofFn (n := g) fun k => unpack 1782 11 (G k.val)) B' Ls = true
  | [], _, _, _, _ => by simp [levelsOK]
  | L :: Ls, B, B', hB, h => by
    change CFSG.KLie.CT.andB (lettersK g L.ws) (CFSG.KLie.CT.andB (allL (wordsK G L.ws) fun t => fixAllK t B)
      (CFSG.KLie.CT.andB (treeK (wordsK G L.ws) L) (levelsK g G Ls (L.b :: B)))) = true at h
    simp only [andB_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hl := lettersK_spec h1
    have hgens : levelGens (Array.ofFn (n := g) fun k => unpack 1782 11 (G k.val)) L =
        ((wordsK G L.ws).map (unpack 1782 11)).toArray := by
      have e : ∀ ws : List (List Nat), (∀ w ∈ ws, ∀ j ∈ w, j < g) →
          ws.map (wordC (Array.ofFn (n := g) fun k => unpack 1782 11 (G k.val))) =
            (ws.map (wordK G)).map (unpack 1782 11) := by
        intro ws hws
        induction ws with
        | nil => rfl
        | cons v ws ih =>
          rw [List.map_cons, List.map_cons, List.map_cons,
            (wordC_unpack hsz hp v (hws v List.mem_cons_self)).1,
            ih fun u hu => hws u (List.mem_cons_of_mem v hu)]
      unfold levelGens
      rw [wordsK_eq, e L.ws hl]
    rw [levelsOK, hgens]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, treeK_sound h3⟩,
      levelsK_sound hsz hp Ls _ _ (fun x => by simp [hB x, or_comm]) h4⟩
    · rw [List.all_eq_true]
      intro w hw
      rw [List.all_eq_true]
      intro j hj
      simpa using hl w hw j hj
    · rw [allL_eq, List.all_eq_true] at h2
      rw [List.all_toArray, List.all_eq_true]
      intro t ht
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
      exact fixesAll_congr hB (by rw [← fixAllK_eq]; exact h2 u hu)

end Levels

theorem centreK_sound {gs : Array Tab} {g : Nat} {G : Nat → Nat}
    (hg : gs = Array.ofFn (n := g) fun k => unpack 1782 11 (G k.val))
    (hp : ∀ k < g, PP 1782 11 (G k)) {zw : List Nat} {Ls : List CentreLevel} {N : Nat}
    (h : centreK g G zw Ls N = true) : centreOK gs zw Ls N = true := by
  subst hg
  have hsz : szOK 1782 11 = true := rfl
  have hgs : ∀ k < g, (Array.ofFn (n := g) fun k => unpack 1782 11 (G k.val))[k]! =
      unpack 1782 11 (G k) := fun k hk => by
    rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  rcases Ls with _ | ⟨L0, _ | ⟨L1, rest⟩⟩
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  change centreBody g G zw (L0 :: L1 :: rest) N L0 L1 = true at h
  unfold centreBody at h
  rw [strictB_eq'] at h
  simp only [andB_eq, notB_eq, Bool.and_eq_true] at h
  obtain ⟨hlev, hprod, horb, hbase, hcnt, hzw, hcomm, hmove⟩ := h
  rw [allL_eq, List.all_eq_true] at hzw
  have hzw' : ∀ j ∈ zw, j < g := fun j hj => Nat.blt_eq.mp (hzw j hj)
  obtain ⟨ez, pz⟩ := wordC_unpack hsz hp zw hzw'
  have hl1 := lettersK_spec (by
    change CFSG.KLie.CT.andB (lettersK g L0.ws) (CFSG.KLie.CT.andB _ (CFSG.KLie.CT.andB _ (CFSG.KLie.CT.andB (lettersK g L1.ws) _))) = true at hlev
    simp only [andB_eq, Bool.and_eq_true] at hlev
    exact hlev.2.2.2.1)
  simp only [centreOK, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨levelsK_sound hsz hp _ [] [] (fun _ => Iff.rfl) hlev, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩
  · rw [← prodK_eq, Nat.eq_of_beq_eq_true hprod]
    exact beq_self_eq_true N
  · rw [allL_eq, List.all_eq_true] at horb
    rw [List.all_eq_true]
    intro x hx
    have e := horb x hx
    rw [allN_eq', List.all_eq_true] at e
    unfold allBelow
    rw [List.all_eq_true, Array.size_ofFn]
    intro k hk
    have e2 := e k hk
    rw [anyL_eq, List.any_eq_true] at e2
    obtain ⟨y, hy, ey⟩ := e2
    rw [hgs k (List.mem_range.1 hk), ← pgC_eq, ← Nat.eq_of_beq_eq_true ey]
    exact List.contains_iff_mem.2 hy
  · rw [List.all_eq_true]
    intro L hL
    exact List.contains_iff_mem.2 (basesK_spec hbase L hL)
  · rw [cntL_eq, wordsK_eq] at hcnt
    rw [← Nat.eq_of_beq_eq_true hcnt]
    refine beq_iff_eq.2 (congrArg List.length (List.filter_congr fun x _ => ?_))
    unfold levelGens
    rw [List.all_toArray, List.all_map, allL_eq, List.all_map]
    refine all_congr_mem fun w hw => ?_
    simp only [Function.comp_apply]
    rw [(wordC_unpack hsz hp w (hl1 w hw)).1, pgC_eq, beq_nat]
  · rw [List.all_eq_true]
    intro j hj
    simpa using hzw' j hj
  · rw [ez]
    unfold commAll allBelow
    rw [List.all_eq_true, Array.size_ofFn]
    intro k hk
    have hk' := List.mem_range.1 hk
    rw [allN_eq', List.all_eq_true] at hcomm
    rw [hgs k hk', comp_eq_compA, comp_eq_compA, compA_PP pz (hp k hk'), compA_PP (hp k hk') pz]
    have e := Nat.eq_of_beq_eq_true (hcomm k hk)
    change (unpack 1782 11 (mul 1782 11 _ _) == unpack 1782 11 (mul 1782 11 _ _)) = true
    rw [e]
    exact beq_self_eq_true _
  · rw [ez, ← fixAllK_eq]
    exact hmove

end CFSG.KC.SuzCentreK

end
