module

public import Certificates.Data.Kernel.HeRK
public import Certificates.Data.HeRCentCheck
import CFSG.Certificates.Kernel.LocalQTCovTPrim
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

namespace CFSG.KC.HeRK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.AS81.HePres.Native

@[expose] def heWordArrG (g : Array (Array Nat)) (w : List Nat) : Array Nat :=
  wordArrW 8330 g (g.map (invCand 8330)) (ofCodes w)

@[expose] def heGenArrsOKG (g : Array (Array Nat)) : Bool :=
  (List.range 8).all fun i => isInvA 8330 (g.getD i #[]) ((g.map (invCand 8330)).getD i #[])

@[expose] def heRInvolOKG (g : Array (Array Nat)) : Bool :=
  let r₁ := heWordArrG g (heRWords.getD 0 [])
  let r₂ := heWordArrG g (heRWords.getD 1 [])
  let r₃ := compA 8330 r₁ r₂
  eqA 8330 (compA 8330 r₁ r₁) (idA 8330) && eqA 8330 (compA 8330 r₂ r₂) (idA 8330) &&
    commutesA 8330 r₁ r₂ && !eqA 8330 r₁ (idA 8330) && !eqA 8330 r₂ (idA 8330) &&
    !eqA 8330 r₃ (idA 8330) && fixCountA 8330 r₁ == 346 && fixCountA 8330 r₂ == 346 &&
    fixCountA 8330 r₃ == 346

@[expose] def heRWitOKG (g : Array (Array Nat)) : Bool :=
  let y := heWordArrG g heRWitWord
  commutesA 8330 y (heWordArrG g (heRWords.getD 0 [])) &&
    !commutesA 8330 y (heWordArrG g (heRWords.getD 1 []))

@[expose] def heRCentOKG (g : Array (Array Nat)) : Bool :=
  let r₁ := heWordArrG g (heRWords.getD 0 [])
  let r₂ := heWordArrG g (heRWords.getD 1 [])
  heRCentWords.length == 4 && heRCentWords.all fun w =>
    let u := heWordArrG g w
    isInvA 8330 u (invCand 8330 u) && commutesA 8330 u r₁ && commutesA 8330 u r₂

@[expose] def heRChainOrigG (g : Array (Array Nat)) : Array (Array Nat) :=
  #[commArr 8330 (heWordArrG g (heRCentWords.getD 0 [])) (heWordArrG g (heRCentWords.getD 1 [])),
    commArr 8330 (heWordArrG g (heRCentWords.getD 2 [])) (heWordArrG g (heRCentWords.getD 3 []))]

@[expose] def heRStrongG (g : Array (Array Nat)) : Array (Array Nat) :=
  buildStrong 8330 (heRChainOrigG g) heRChainWords


private theorem szOK_he : szOK 8330 14 = true := by decide

private theorem strictN_eq_he (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem strictB_eq_he (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem andB_eq_he (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by
  cases a <;> rfl

private theorem notB_eq_he (a : Bool) : CFSG.KLie.CT.notB a = !a := by
  cases a <;> rfl

private theorem canon_of_permOK {p q : Nat}
    (h : permOK 8330 14 (mask 14) (8330 * 14) p q = true) :
    canonK 8330 14 (mask 14) (8330 * 14) p = true := by
  obtain ⟨h1, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  unfold canonK
  simp only [bAnd_iff]
  exact ⟨szOK_he, Nat.beq_eq.mpr h1,
    CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (h3 i hi).1⟩

private theorem canon_inv_of_permOK {p q : Nat}
    (h : permOK 8330 14 (mask 14) (8330 * 14) p q = true) :
    canonK 8330 14 (mask 14) (8330 * 14) q = true := by
  obtain ⟨-, h2, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  obtain ⟨-, hs⟩ := CFSG.KC.LQT.Cov.T.perm_facts h
  unfold canonK
  simp only [bAnd_iff]
  refine ⟨szOK_he, Nat.beq_eq.mpr h2, CFSG.KS.Raw.Orb.allN_iff.2 fun j hj => Nat.blt_eq.mpr ?_⟩
  obtain ⟨i, hi, e⟩ := hs j hj
  rw [← e, (h3 i hi).2]
  exact hi

private theorem canon_pidn : canonK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) = true := by
  unfold canonK
  simp only [bAnd_iff]
  refine ⟨szOK_he, Nat.beq_eq.mpr (CFSG.KS.PF.pidn_shr (by norm_num) (by norm_num)),
    CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr ?_⟩
  rw [CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hi]
  exact hi

private theorem idA_he : idA 8330 = unpack 8330 14 (pidn 8330 14) :=
  (CFSG.KC.LQT.Cov.T.unpack_pidn (by norm_num) (by norm_num)).symm

private theorem canon_mul {p q : Nat} (hp : canonK 8330 14 (mask 14) (8330 * 14) p = true)
    (hq : canonK 8330 14 (mask 14) (8330 * 14) q = true) :
    canonK 8330 14 (mask 14) (8330 * 14) (CFSG.KC.HexaK.mul 8330 14 p q) = true :=
  CFSG.KC.BfsPin.canonK_pcomp hp hq

private theorem compA_mul {p q : Nat} (hp : canonK 8330 14 (mask 14) (8330 * 14) p = true)
    (hq : canonK 8330 14 (mask 14) (8330 * 14) q = true) :
    compA 8330 (unpack 8330 14 p) (unpack 8330 14 q) =
      unpack 8330 14 (CFSG.KC.HexaK.mul 8330 14 p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

private theorem eqA_beq {p q : Nat} (hp : canonK 8330 14 (mask 14) (8330 * 14) p = true)
    (hq : canonK 8330 14 (mask 14) (8330 * 14) q = true) :
    eqA 8330 (unpack 8330 14 p) (unpack 8330 14 q) = Nat.beq p q :=
  CFSG.KC.BfsPin.eqA_unpack hp hq

private theorem fixR_eq (p : Nat) : ∀ k, k ≤ 8330 →
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun i s => nIf(Nat.beq (pg 14 (mask 14) p i) i, Nat.succ s, s)) k =
      (List.range k).countP (fun i => (unpack 8330 14 p)[i]! == i)
  | 0, _ => rfl
  | k + 1, hk => by
    rw [List.range_succ, List.countP_append, ← fixR_eq p k (by omega)]
    simp only [List.countP_singleton, CFSG.KS.Raw.Orb.unpack_get (by omega : k < 8330)]
    show nIf(Nat.beq (pg 14 (mask 14) p k) k, Nat.succ _, _) = _
    cases h : Nat.beq (pg 14 (mask 14) p k) k
    · have h' := Nat.ne_of_beq_eq_false h
      simp [h']
    · have h' := Nat.eq_of_beq_eq_true h
      simp [h']

private theorem fixK_eq (p : Nat) : fixK p = fixCountA 8330 (unpack 8330 14 p) := by
  unfold fixK fixCountA
  exact fixR_eq p 8330 le_rfl

private theorem getD_he {g : Array (Array Nat)} (hs : g.size = 8) {i : Nat} (hi : i < 8) :
    g.getD i #[] = g[i]! := by
  simp [Array.getD, hs, hi, getElem!_pos]

private theorem getD_map_he {g : Array (Array Nat)} (hs : g.size = 8) {i : Nat} (hi : i < 8) :
    (g.map (invCand 8330)).getD i #[] = invCand 8330 g[i]! := by
  simp [Array.getD, hs, hi, getElem!_pos]

private theorem letter_eq {g : Array (Array Nat)} {G GI : Nat → Nat}
    (hs : g.size = 8) (hg : ∀ i < 8, g[i]! = unpack 8330 14 (G i))
    (hp : ∀ i < 8, permOK 8330 14 (mask 14) (8330 * 14) (G i) (GI i) = true) (c : Nat) :
    letterArrW g (g.map (invCand 8330)) ((⟨c / 2 % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8),
        decide (c % 2 = 0)) = unpack 8330 14 (letC G GI c) ∧
      canonK 8330 14 (mask 14) (8330 * 14) (letC G GI c) = true := by
  have hi : c / 2 % 8 < 8 := Nat.mod_lt _ (by decide)
  show (if decide (c % 2 = 0) = true then g.getD (c / 2 % 8) #[]
      else (g.map (invCand 8330)).getD (c / 2 % 8) #[]) =
      unpack 8330 14 (Bool.rec (motive := fun _ => Nat) (GI (c / 2 % 8)) (G (c / 2 % 8))
        (Nat.beq (c % 2) 0)) ∧
    canonK 8330 14 (mask 14) (8330 * 14) (Bool.rec (motive := fun _ => Nat) (GI (c / 2 % 8))
        (G (c / 2 % 8)) (Nat.beq (c % 2) 0)) = true
  cases h : Nat.beq (c % 2) 0
  · have h' := Nat.ne_of_beq_eq_false h
    simp only [h', decide_false, Bool.false_eq_true, if_false]
    rw [getD_map_he hs hi, hg _ hi, CFSG.KC.LQT.Cov.T.invCand_unpack (hp _ hi)]
    exact ⟨rfl, canon_inv_of_permOK (hp _ hi)⟩
  · have h' := Nat.eq_of_beq_eq_true h
    simp only [h', decide_true, if_true]
    rw [getD_he hs hi, hg _ hi]
    exact ⟨rfl, canon_of_permOK (hp _ hi)⟩

private theorem wordArrW_nil {k : Nat} (n : Nat) (gens invs : Array (Array Nat)) :
    wordArrW (k := k) n gens invs [] = idA n := rfl

private theorem wordArrW_cons {k : Nat} (n : Nat) (gens invs : Array (Array Nat))
    (l : Fin k × Bool) (w : List (Fin k × Bool)) :
    wordArrW n gens invs (l :: w) = compA n (letterArrW gens invs l) (wordArrW n gens invs w) :=
  rfl

private theorem ofCodes_nil : ofCodes [] = [] := rfl

private theorem ofCodes_cons (c : Nat) (w : List Nat) :
    ofCodes (c :: w) = ((⟨c / 2 % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8), decide (c % 2 = 0)) ::
      ofCodes w := rfl

private theorem codeK_nil (G GI : Nat → Nat) : codeK G GI [] = pidn 8330 14 := rfl

private theorem codeK_cons (G GI : Nat → Nat) (c : Nat) (w : List Nat) :
    codeK G GI (c :: w) = CFSG.KC.HexaK.mul 8330 14 (letC G GI c) (codeK G GI w) :=
  strictN_eq_he _ _

private theorem pair_get0 {α : Type} [Inhabited α] (x y : α) : (#[x, y])[0]! = x := rfl

private theorem pair_get1 {α : Type} [Inhabited α] (x y : α) : (#[x, y])[1]! = y := rfl

private theorem pair_size {α : Type} (x y : α) : (#[x, y]).size = 2 := rfl

private theorem word_eq {g : Array (Array Nat)} {G GI : Nat → Nat}
    (hs : g.size = 8) (hg : ∀ i < 8, g[i]! = unpack 8330 14 (G i))
    (hp : ∀ i < 8, permOK 8330 14 (mask 14) (8330 * 14) (G i) (GI i) = true) :
    ∀ w : List Nat, heWordArrG g w = unpack 8330 14 (codeK G GI w) ∧
      canonK 8330 14 (mask 14) (8330 * 14) (codeK G GI w) = true := by
  intro w
  induction w with
  | nil =>
    rw [heWordArrG, ofCodes_nil, wordArrW_nil, codeK_nil]
    exact ⟨idA_he, canon_pidn⟩
  | cons c w ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨l1, l2⟩ := letter_eq hs hg hp c
    rw [heWordArrG, ofCodes_cons, wordArrW_cons, ← heWordArrG, codeK_cons, ih1, l1,
      compA_mul l2 ih2]
    exact ⟨rfl, canon_mul l2 ih2⟩

private theorem build_eq {O : Array (Array Nat)} {W : Array (List Int)} {PS PSI : Nat → Nat}
    (hO : ∀ j < O.size, O[j]! = unpack 8330 14 (PS j))
    (hp : ∀ j < W.size, permOK 8330 14 (mask 14) (8330 * 14) (PS j) (PSI j) = true)
    (hw : ∀ j < W.size, O.size ≤ j →
      wordEqK 8330 14 (mask 14) (pidn 8330 14) PS PSI j W[j]! (PS j) = true) :
    ∀ k ≤ W.size,
      ((List.range k).foldl (fun S j => S.push (if j < O.size then O[j]! else
          wordA 8330 S (S.map (invCand 8330)) W[j]!)) #[]).size = k ∧
      ∀ j < k, ((List.range k).foldl (fun S j => S.push (if j < O.size then O[j]! else
          wordA 8330 S (S.map (invCand 8330)) W[j]!)) #[])[j]! = unpack 8330 14 (PS j)
  | 0, _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    obtain ⟨hs, hv⟩ := build_eq hO hp hw k (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize ((List.range k).foldl (fun S j => S.push (if j < O.size then O[j]! else
          wordA 8330 S (S.map (invCand 8330)) W[j]!)) #[]) = S at hs hv ⊢
    have hval : (if k < O.size then O[k]! else wordA 8330 S (S.map (invCand 8330)) W[k]!) =
        unpack 8330 14 (PS k) := by
      by_cases hkO : k < O.size
      · rw [if_pos hkO]
        exact hO k hkO
      · rw [if_neg hkO]
        exact (wordEqK_sound ⟨hs, hv⟩
          (CFSG.KS.Raw.Orb.allN_iff.2 fun j hj => hp j (by omega))
          (hw k (by omega) (by omega))).1
    refine ⟨by rw [Array.size_push, hs], fun j hj => ?_⟩
    rw [getElem!_pos _ j (by rw [Array.size_push, hs]; exact hj)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · rw [Array.getElem_push_lt (by rw [hs]; exact h), ← getElem!_pos S j (by rw [hs]; exact h)]
      exact hv j h
    · subst h
      rw [Array.getElem_push, dif_neg (by omega)]
      exact hval

theorem heGenArrsOK_eq : heGenArrsOK = heGenArrsOKG heGenArrs8 := rfl
theorem heWordArr_eq : heWordArr = heWordArrG heGenArrs8 := rfl
theorem heRInvolOK_eq : heRInvolOK = heRInvolOKG heGenArrs8 := by
  rw [heRInvolOK, heRInvolOKG, heWordArr_eq]
theorem heRWitOK_eq : heRWitOK = heRWitOKG heGenArrs8 := by
  rw [heRWitOK, heRWitOKG, heWordArr_eq]
theorem heRCentOK_eq : heRCentOK = heRCentOKG heGenArrs8 := by
  rw [heRCentOK, heRCentOKG, heWordArr_eq]
theorem heRChainOrig_eq : heRChainOrig = heRChainOrigG heGenArrs8 := by
  rw [heRChainOrig, heRChainOrigG, heWordArr_eq]
theorem heRStrong_eq : heRStrong = heRStrongG heGenArrs8 := by
  rw [heRStrong, heRStrongG, heRChainOrig_eq]

theorem heRK_sound {g : Array (Array Nat)} {G GI PS PSI : Nat → Nat}
    (hs : g.size = 8) (hg : ∀ i < 8, g[i]! = unpack 8330 14 (G i))
    (hp : ∀ i < 8, permOK 8330 14 (mask 14) (8330 * 14) (G i) (GI i) = true)
    (hK1 : heRK1 G GI heRWords heRWitWord = true)
    (hK2 : ∀ k < 4, heRK2 G GI heRWords heRCentWords k = true)
    (hK3 : ∀ j < 2, heRK3 G GI PS heRCentWords j = true)
    (hK4 : heRK4 PS PSI (fun j => heRChainWords[j]!) = true) :
    heGenArrsOKG g = true ∧ heRInvolOKG g = true ∧ heRWitOKG g = true ∧ heRCentOKG g = true ∧
      (heRStrongG g).size = 9 ∧ (∀ j < 9, (heRStrongG g)[j]! = unpack 8330 14 (PS j)) ∧
      (eqA 8330 (heRStrongG g)[0]! (heRChainOrigG g)[0]! &&
        eqA 8330 (heRStrongG g)[1]! (heRChainOrigG g)[1]!) = true := by
  have W := word_eq hs hg hp
  have hW : ∀ w, heWordArrG g w = unpack 8330 14 (codeK G GI w) := fun w => (W w).1
  have hC : ∀ w, canonK 8330 14 (mask 14) (8330 * 14) (codeK G GI w) = true := fun w => (W w).2
  unfold heRK1 invol346 at hK1
  simp only [strictB_eq_he, andB_eq_he, notB_eq_he, Bool.and_eq_true, Bool.not_eq_true'] at hK1
  obtain ⟨⟨h11, h12, h13⟩, ⟨h21, h22, h23⟩, h4, ⟨h51, h52, h53⟩, h6, h7⟩ := hK1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    unfold heGenArrsOKG
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    rw [getD_he hs hi, getD_map_he hs hi, hg i hi, CFSG.KC.LQT.Cov.T.invCand_unpack (hp i hi)]
    exact CFSG.KS.Raw.Orb.isInvA_unpack (hp i hi)
  ·
    unfold heRInvolOKG
    simp only [hW, commutesA, compA_mul, eqA_beq, hC, canon_mul, idA_he, canon_pidn,
      ← fixK_eq, h11, h21, h4, h51, h12, h22, h52, Nat.eq_of_beq_eq_true h13,
      Nat.eq_of_beq_eq_true h23, Nat.eq_of_beq_eq_true h53]
    rfl
  ·
    unfold heRWitOKG
    simp only [hW, commutesA, compA_mul, eqA_beq, hC, canon_mul, h6, h7]
    all_goals decide
  ·
    unfold heRCentOKG
    have hl : heRCentWords.length = 4 := rfl
    simp only [hl, Bool.and_eq_true, List.all_eq_true]
    refine ⟨rfl, fun u hu => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
    have h := hK2 k (hl ▸ hk)
    unfold heRK2 at h
    simp only [strictB_eq_he, andB_eq_he, Bool.and_eq_true, List.getD_eq_getElem _ _ hk] at h
    obtain ⟨hpk, hc1, hc2⟩ := h
    simp only [hW, commutesA, compA_mul, eqA_beq, hC, CFSG.KC.LQT.Cov.T.invCand_unpack hpk,
      CFSG.KS.Raw.Orb.isInvA_unpack hpk, canon_mul, hc1, hc2]
    all_goals decide
  ·
    unfold heRK4 at hK4
    rw [andB_eq_he, Bool.and_eq_true] at hK4
    have hpS : ∀ j < 9, permOK 8330 14 (mask 14) (8330 * 14) (PS j) (PSI j) = true :=
      fun j hj => CFSG.KS.Raw.Orb.allN_iff.1 hK4.1 j hj
    have hwS : ∀ j < 7, wordEqK 8330 14 (mask 14) (pidn 8330 14) PS PSI (2 + j)
        heRChainWords[2 + j]! (PS (2 + j)) = true :=
      fun j hj => CFSG.KS.Raw.Orb.allN_iff.1 hK4.2 j hj
    have hpC : ∀ a < 4, permOK 8330 14 (mask 14) (8330 * 14)
        (codeK G GI (heRCentWords.getD a [])) (codeK G GI (codeInv (heRCentWords.getD a []))) =
          true := by
      intro a ha
      have h := hK2 a ha
      unfold heRK2 at h
      simp only [strictB_eq_he, andB_eq_he, Bool.and_eq_true] at h
      exact h.1
    have hcomm : ∀ a < 4, ∀ b < 4, commArr 8330 (heWordArrG g (heRCentWords.getD a []))
        (heWordArrG g (heRCentWords.getD b [])) = unpack 8330 14
          (commP (codeK G GI (heRCentWords.getD a [])) (codeK G GI (codeInv (heRCentWords.getD a [])))
            (codeK G GI (heRCentWords.getD b [])) (codeK G GI (codeInv (heRCentWords.getD b [])))) := by
      intro a ha b hb
      have ia := canon_inv_of_permOK (hpC a ha)
      have ib := canon_inv_of_permOK (hpC b hb)
      unfold commArr commP
      simp (config := { maxDischargeDepth := 6 }) only [hW,
        CFSG.KC.LQT.Cov.T.invCand_unpack (hpC a ha),
        CFSG.KC.LQT.Cov.T.invCand_unpack (hpC b hb), compA_mul, hC, ia, ib, canon_mul]
    have h30 : Nat.beq (PS 0) (commP (codeK G GI (heRCentWords.getD 0 []))
        (codeK G GI (codeInv (heRCentWords.getD 0 []))) (codeK G GI (heRCentWords.getD 1 []))
        (codeK G GI (codeInv (heRCentWords.getD 1 [])))) = true := hK3 0 (by decide)
    have h31 : Nat.beq (PS 1) (commP (codeK G GI (heRCentWords.getD 2 []))
        (codeK G GI (codeInv (heRCentWords.getD 2 []))) (codeK G GI (heRCentWords.getD 3 []))
        (codeK G GI (codeInv (heRCentWords.getD 3 [])))) = true := hK3 1 (by decide)
    have hO0 : (heRChainOrigG g)[0]! = unpack 8330 14 (PS 0) := by
      rw [heRChainOrigG, pair_get0, hcomm 0 (by decide) 1 (by decide),
        Nat.eq_of_beq_eq_true h30]
    have hO1 : (heRChainOrigG g)[1]! = unpack 8330 14 (PS 1) := by
      rw [heRChainOrigG, pair_get1, hcomm 2 (by decide) 3 (by decide),
        Nat.eq_of_beq_eq_true h31]
    have hOs : (heRChainOrigG g).size = 2 := by rw [heRChainOrigG, pair_size]
    have hWs : heRChainWords.size = 9 := rfl
    have hO : ∀ j < (heRChainOrigG g).size, (heRChainOrigG g)[j]! = unpack 8330 14 (PS j) := by
      intro j hj
      rw [hOs] at hj
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact hO0
      · exact hO1
    have hw : ∀ j < heRChainWords.size, (heRChainOrigG g).size ≤ j →
        wordEqK 8330 14 (mask 14) (pidn 8330 14) PS PSI j heRChainWords[j]! (PS j) = true := by
      intro j hj h2
      rw [hWs] at hj
      rw [hOs] at h2
      obtain ⟨i, rfl⟩ : ∃ i, j = 2 + i := ⟨j - 2, by omega⟩
      exact hwS i (by omega)
    obtain ⟨hsz, hval⟩ := build_eq hO (fun j hj => hpS j (hWs ▸ hj)) hw _ le_rfl
    have hS : heRStrongG g = (List.range heRChainWords.size).foldl (fun S j =>
        S.push (if j < (heRChainOrigG g).size then (heRChainOrigG g)[j]! else
          wordA 8330 S (S.map (invCand 8330)) heRChainWords[j]!)) #[] := rfl
    rw [hS]
    refine ⟨hsz, fun j hj => hval j (hWs ▸ hj), ?_⟩
    rw [hval 0 (by decide), hval 1 (by decide), hO0, hO1,
      eqA_beq (canon_of_permOK (hpS 0 (by decide))) (canon_of_permOK (hpS 0 (by decide))),
      eqA_beq (canon_of_permOK (hpS 1 (by decide))) (canon_of_permOK (hpS 1 (by decide))),
      Nat.beq_refl, Nat.beq_refl]
    rfl

end CFSG.KC.HeRK

end
