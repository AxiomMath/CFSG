module

public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.KS.Raw

variable {n : Nat}

@[expose] def PRep (n w P : Nat) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n, pg w (mask w) P x = g x

theorem unpack_get {w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_ofFn_nat _ hi]

theorem rep_unpack {w P : Nat} {g : Equiv.Perm (Fin n)} (h : PRep n w P g) :
    Rep n (unpack n w P) g := fun x => by rw [unpack_get x.2, h x]

theorem prep_of_rep {w P : Nat} {g : Equiv.Perm (Fin n)} (h : Rep n (unpack n w P) g) :
    PRep n w P g := fun x => by rw [← unpack_get x.2]; exact h x

theorem prep_pcomp {w P Q : Nat} {g h : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (hP : PRep n w P g) (hQ : PRep n w Q h) : PRep n w (pcomp n w (mask w) P Q) (g * h) :=
  fun x => by rw [PF.pg_pcomp hn x.2, hQ x, hP (h x), Equiv.Perm.mul_apply]

theorem prep_pidn {w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) : PRep n w (pidn n w) 1 :=
  fun x => PF.pg_pidn hn hw x.2

theorem permOK_facts {w P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    Nat.shiftRight P (n * w) = 0 ∧ Nat.shiftRight Q (n * w) = 0 ∧
      ∀ i < n, pg w (mask w) P i < n ∧ pg w (mask w) Q (pg w (mask w) P i) = i := by
  unfold permOK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, allN_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, fun i hi => ?_⟩
  have := h3 i hi
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at this
  exact ⟨this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem isInvA_unpack {w P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    isInvA n (unpack n w P) (unpack n w Q) = true := by
  obtain ⟨_, _, h3⟩ := permOK_facts h
  unfold isInvA
  rw [allLt_iff]
  intro i hi
  rw [unpack_get hi, unpack_get (h3 i hi).1, (h3 i hi).2]
  simp [(h3 i hi).1]

theorem prep_PS {w kS nb BP : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    {j : Nat} (hj : j < kS) :
    PRep n w (PS j) (permOfArr n S[j]!) ∧ PRep n w (PSI j) (permOfArr n S[j]!)⁻¹ := by
  have hr := rep_permOfArr (isInvA_unpack (allN_iff.1 hp j hj))
  rw [hb.2.2.2.2.1 j hj]
  exact ⟨prep_of_rep hr.1, prep_of_rep hr.2⟩

theorem shr_eq (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b

theorem blt_dec (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

theorem ble_dec (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_iff]

theorem beq_dec (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

theorem wordK_nil (n w m idn : Nat) (S SI : Nat → Nat) : wordK n w m idn S SI [] = idn := rfl

theorem wordK_cons (n w m idn : Nat) (S SI : Nat → Nat) (z : Int) (wd : List Int) :
    wordK n w m idn S SI (z :: wd) = pcomp n w m (nIf(Nat.beq (Nat.land (icode z) (nat_lit 1))
      (nat_lit 0), S (Nat.sub (Nat.shiftRight (icode z) (nat_lit 1)) (nat_lit 1)),
      SI (Nat.sub (Nat.shiftRight (icode z) (nat_lit 1)) (nat_lit 1))))
      (wordK n w m idn S SI wd) := by
  have e : wordK n w m idn S SI (z :: wd) = strictN (wordK n w m idn S SI wd) (fun T =>
      strictN (icode z) (fun c => pcomp n w m (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
        S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
        SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T)) := rfl
  rw [e, strictN_eq, strictN_eq]

theorem lettersK_cons (j : Nat) (z : Int) (wd : List Int) :
    lettersK j (z :: wd) = (decide (0 < icode z) && decide (icode z / 2 ≤ j) && lettersK j wd) := by
  have e : lettersK j (z :: wd) = strictB (icode z) (fun c =>
      bAnd(Nat.blt (nat_lit 0) c, bAnd(Nat.ble (Nat.shiftRight c (nat_lit 1)) j,
        lettersK j wd))) := rfl
  rw [e, strictB_eq, bAnd_eq, bAnd_eq, shr_eq, blt_dec, ble_dec, Bool.and_assoc, Nat.pow_one]

theorem prep_wordK {w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {PS PSI : Nat → Nat}
    {gs : Nat → Equiv.Perm (Fin n)} {j : Nat} (hS : ∀ h < j, PRep n w (PS h) (gs h))
    (hSI : ∀ h < j, PRep n w (PSI h) (gs h)⁻¹) : ∀ wd : List Int, lettersK j wd = true →
    PRep n w (wordK n w (mask w) (pidn n w) PS PSI wd)
      (Quiver.SchreierGraph.evalWord (fun h : Fin j => gs h) (toLetters j wd)) ∧
      lettersOK j wd = true
  | [], _ => by
    refine ⟨?_, rfl⟩
    rw [wordK_nil]
    simpa [toLetters] using prep_pidn hn hw
  | z :: wd, hl => by
    rw [lettersK_cons, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq] at hl
    obtain ⟨⟨hc0, hcj⟩, hl⟩ := hl
    obtain ⟨ih1, ih2⟩ := prep_wordK hn hw hS hSI wd hl
    have h32 : n < 2 ^ 32 := by omega
    rw [wordK_cons]
    cases z with
    | ofNat k =>
      have ec : icode (Int.ofNat k) = k + k := rfl
      rw [ec] at hc0 hcj ⊢
      have hk0 : k ≠ 0 := by omega
      have hkj : k ≤ j := by omega
      have e1 : Nat.land (k + k) 1 = 0 := by
        change (k + k) &&& 1 = 0
        rw [Nat.and_one_is_mod]
        omega
      have e2 : Nat.shiftRight (k + k) 1 = k := by
        rw [shr_eq]
        omega
      have hz0 : (Int.ofNat k : Int) ≠ 0 := by simpa using hk0
      have hcons : toLetters j (Int.ofNat k :: wd) = (⟨k - 1, by omega⟩, true) ::
          toLetters j wd := by
        simp only [toLetters, List.filterMap_cons]
        simp [hk0, hkj]
        omega
      rw [e1, e2, hcons, Quiver.SchreierGraph.evalWord_cons_true]
      refine ⟨prep_pcomp h32 (hS (k - 1) (by omega)) ih1, ?_⟩
      simp [lettersOK, List.all_cons, hk0, hkj]
      simpa [lettersOK] using ih2
    | negSucc k =>
      have ec : icode (Int.negSucc k) = (k + 1) + (k + 1) + 1 := rfl
      rw [ec] at hc0 hcj ⊢
      have hkj : k + 1 ≤ j := by omega
      have e1 : Nat.land ((k + 1) + (k + 1) + 1) 1 = 1 := by
        change ((k + 1) + (k + 1) + 1) &&& 1 = 1
        rw [Nat.and_one_is_mod]
        omega
      have e2 : Nat.shiftRight ((k + 1) + (k + 1) + 1) 1 = k + 1 := by
        rw [shr_eq]
        omega
      have hcons : toLetters j (Int.negSucc k :: wd) = (⟨k, by omega⟩, false) ::
          toLetters j wd := by
        simp only [toLetters, List.filterMap_cons]
        simp [hkj]
      rw [e1, e2, hcons, Quiver.SchreierGraph.evalWord_cons_false]
      refine ⟨prep_pcomp h32 (hSI k (by omega)) ih1, ?_⟩
      simp [lettersOK, List.all_cons, hkj]
      simpa [lettersOK] using ih2

theorem nthD_eq : ∀ (D : List (List Int)) (i : Nat),
    List.rec (motive := fun _ => Nat → List Int) (fun _ => [])
      (fun x _ ih i => Nat.rec (motive := fun _ => List Int) x (fun i' _ => ih i') i) D i =
      D.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: D, i + 1 => nthD_eq D i

theorem dword_eq {D : List (List Int)} {k j : Nat} (h : k ≤ j) :
    dword D k j = D.getD (j - k) [] := by
  have hb : Nat.blt j k = false := by
    rw [blt_dec, decide_eq_false_iff_not]
    omega
  unfold dword
  rw [hb]
  exact nthD_eq D (Nat.sub j k)

theorem wordsArr_get' {k s : Nat} {D : List (List Int)} {j : Nat} (hkj : k ≤ j) (hj : j < s) :
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr k s D)[j]! = D.getD (j - k) [] := by
  rw [CFSG.Sporadic.Schreier.Co3.Native.wordsArr, getElem!_pos _ j (by simpa using hj),
    Array.getElem_ofFn]
  have hjk : ¬ j < k := by omega
  simp only [hjk, ↓reduceIte]

theorem rawInvs_get {S : Array (Array Nat)} {j : Nat} (hj : j < S.size) :
    (rawInvs n S)[j]! = invCand n S[j]! := by
  rw [rawInvs, getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos S j hj]

theorem rawHeadOK_of {w kS kO nb BP : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {D : List (List Int)} (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    kO ≤ S.size ∧ rawHeadOK n (S.extract 0 kO) S base
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D) = true := by
  have hb0 := hb
  obtain ⟨_, hw, _, hS, hSj, hbs, hbt⟩ := hb
  unfold headK at hh
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨hsz, _, hkO, _, hperm, hder, hterm, hbase⟩ := hh
  unfold szOK at hsz
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hsz
  have hn24 : n < 16777216 := hsz.1
  have hk : kO ≤ S.size := by
    rw [hS]
    simpa [Nat.ble_eq] using hkO
  have hO : (S.extract 0 kO).size = kO := by simp [Array.size_extract]; omega
  have hPS := fun j (hj : j < kS) => prep_PS hb0 hperm hj
  have hrS : ∀ j < S.size, Rep n S[j]! (permOfArr n S[j]!) := fun j hj => by
    have e := hSj j (hS ▸ hj)
    have := rep_unpack (hPS j (hS ▸ hj)).1
    rwa [← e] at this
  have hrSi : ∀ j < S.size, Rep n (rawInvs n S)[j]! (permOfArr n S[j]!)⁻¹ := fun j hj => by
    rw [rawInvs_get hj]
    exact rep_invCand (hrS j hj)
  have hbl : ∀ t < nb, base[t]! < n := fun t ht => by
    have := allN_iff.1 hbase t ht
    rw [Nat.blt_eq] at this
    rw [hbt t ht]
    exact this
  refine ⟨hk, ?_⟩
  unfold rawHeadOK
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨⟨by omega, by simp [CFSG.Sporadic.Schreier.Co3.Native.wordsArr, hS]⟩,
    fun j hj => isInvA_of_rep (hrS j hj) (hrSi j hj)⟩, fun k hk' => ?_⟩, fun j hj => ?_⟩,
    fun j hj => ?_⟩, fun i hi => hbl i (hbs ▸ hi)⟩
  · rw [hO] at hk'
    rw [getElem!_pos (S.extract 0 kO) k (by omega), Array.getElem_extract,
      getElem!_pos S k (by omega)]
    simp only [Nat.zero_add]
    exact eqA_self _
  · rw [hO]
    by_cases hjk : j < kO
    · exact Or.inl hjk
    · right
      have := allN_iff.1 hder j (hS ▸ hj)
      rw [bIf_eq, ite_eq_right (by rw [blt_dec]; simpa using hjk), strictB_eq, Bool.and_eq_true,
        beq_dec, decide_eq_true_iff, dword_eq (by omega)] at this
      obtain ⟨hl, he⟩ := this
      obtain ⟨hP, hlo⟩ := prep_wordK (gs := fun h => permOfArr n S[h]!) (j := j) hn24 hw
        (fun h hh => (hPS h (by omega)).1) (fun h hh => (hPS h (by omega)).2) _ hl
      rw [wordsArr_get' (by omega) (hS ▸ hj)]
      refine ⟨hlo, ?_⟩
      have hr1 := rep_unpack hP
      rw [← he, ← hSj j (hS ▸ hj)] at hr1
      exact (eqA_iff hr1 (rep_wordA (fun h hh => hrS h (by omega))
        (fun h hh => hrSi h (by omega)) _ hlo)).2 rfl
  · by_cases hf : fixesFirst base S[j]! base.size = true
    · right
      have hfix : ∀ t < nb, (S[j]!)[base[t]!]! = base[t]! := fun t ht => by
        have := allLt_spec hf (hbs ▸ ht)
        rwa [beq_iff_eq] at this
      have := allN_iff.1 hterm j (hS ▸ hj)
      rw [bIf_eq, ite_eq_left (allN_iff.2 fun t ht => by
        rw [strictB_eq, beq_dec, decide_eq_true_iff]
        have e := hfix t ht
        rwa [hbt t ht, hSj j (hS ▸ hj), unpack_get (hbt t ht ▸ hbl t ht)] at e),
        beq_dec, decide_eq_true_iff] at this
      have hr1 : Rep n S[j]! 1 := by
        rw [hSj j (hS ▸ hj), this]
        exact rep_unpack (prep_pidn hn24 hw)
      exact (eqA_iff hr1 rep_idA).2 rfl
    · left
      simpa using hf

end CFSG.KS.Raw.Orb

end
