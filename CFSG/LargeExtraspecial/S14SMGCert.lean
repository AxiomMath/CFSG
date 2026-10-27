module

public import CFSG.LargeExtraspecial.S14SMGBits
public import Certificates.Certificate21105
public import Certificates.Certificate21106
public import Certificates.Certificate21107

public section

namespace CFSG.LargeExtraspecial.S14.SMG

open CFSG.SmithE CFSG.F4.Native

theorem smithEWtCheck_holds : chkW = true :=
  Certificates.certificate21104

theorem smithETvCheck_holds : chkT = true :=
  Certificates.certificate21105

theorem smithEPairCheck_holds : chkP = true :=
  Certificates.certificate21106

theorem smithESpanCheck_holds : chkSpan = true :=
  Certificates.certificate21107.1

theorem smithEIntCheck_holds : chkI = true :=
  Certificates.certificate21107.2

theorem wtArr_get {i : Nat} (hi : i < 891) : wtArr[i]! = wt i := by
  simp [wtArr, getElem!_pos, hi]

theorem maskArr_get {i : Nat} (hi : i < 891) : maskArr[i]! = wMask i := by
  simp [maskArr, getElem!_pos, hi]

theorem tvArr_get {k : Nat} (hk : k < 693) : tvArr[k]! = tvCols k := by
  simp [tvArr, getElem!_pos, hk]

theorem adjM_eq {i j : Nat} (hi : i < 891) (hj : j < 891) : adjM i j = adjW i j := by
  simp only [adjM, adjW, maskArr_get hi, maskArr_get hj]

theorem size_tvCols (k : Nat) : (tvCols k).size = 20 := by
  simp [tvCols]

theorem spanArr_get {k : Nat} (hk : k < 693) : spanArr[k]! = spanData (tvCols k) := by
  simp [spanArr, getElem!_pos, hk, tvArr]

theorem gensOf_get (T : Array Nat) {m : Nat} (hm : m < 20) :
    (gensOf T)[m]! = T[m]! ^^^ 2 ^ m := by
  simp [gensOf, getElem!_pos, hm]

theorem getElem!_map' (B : Array Nat) (f : Nat → Nat) {i : Nat} (hi : i < B.size) :
    (B.map f)[i]! = f B[i]! := by
  rw [getElem!_pos (B.map f) i (by simpa using hi), getElem!_pos B i hi, Array.getElem_map]

theorem chkW_parts :
    (∀ j < 891, wtIdx[wt j]! = j) ∧ (∀ i < 891, modelOK i = true) ∧
      ∀ i < 891, wt i ≠ 0 ∧ (∃ j < 891, adjW i j = true ∧ wt j ≠ wt i) ∧
        ∀ j < 891, adjW i j = false → isWt (wt i ^^^ wt j) = false := by
  have hW := smithEWtCheck_holds
  simp only [chkW, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true, Bool.not_eq_true'] at hW
  obtain ⟨⟨h1, h2⟩, h3⟩ := hW
  refine ⟨fun j hj => by simpa [wtArr_get hj] using h1 j hj, h2, fun i hi => ?_⟩
  obtain ⟨⟨h4, j, hj, h5, h6⟩, h7⟩ := h3 i hi
  refine ⟨by simpa [wtArr_get hi] using h4, ⟨j, hj, by rwa [adjM_eq hi hj] at h5,
    by simpa [wtArr_get hi, wtArr_get hj] using h6⟩, fun j hj hadj => ?_⟩
  rcases h7 j hj with h | h
  · rw [adjM_eq hi hj, hadj] at h
    exact absurd h (by decide)
  · simpa [wtArr_get hi, wtArr_get hj] using h

theorem isWt_iff (v : Nat) :
    isWt v = true ↔ ∃ j < 891, wt j = v := by
  constructor
  · intro h
    simp only [isWt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨_, h.1, by rw [← wtArr_get h.1]; exact h.2⟩
  · rintro ⟨j, hj, rfl⟩
    simp only [isWt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [chkW_parts.1 j hj, wtArr_get hj]
    exact ⟨hj, rfl⟩

theorem wt_ne_zero {i : Nat} (hi : i < 891) : wt i ≠ 0 :=
  (chkW_parts.2.2 i hi).1

theorem exists_adj {i : Nat} (hi : i < 891) :
    ∃ j < 891, adjW i j = true ∧ wt j ≠ wt i :=
  (chkW_parts.2.2 i hi).2.1

theorem wt_ne_xor {i j : Nat} (hi : i < 891) (hj : j < 891)
    (hadj : adjW i j = false) : ∀ k < 891, wt k ≠ wt i ^^^ wt j := by
  intro k hk hk'
  have h := (chkW_parts.2.2 i hi).2.2 j hj hadj
  have : isWt (wt i ^^^ wt j) = true := (isWt_iff _).mpr ⟨k, hk, hk'⟩
  rw [h] at this
  exact absurd this (by decide)

theorem tv_wt {k i : Nat} (hk : k < 693) (hi : i < 891) :
    ∃ j < 891, wt j = applyCols (tvCols k) (wt i) ∧ adjW i j = true := by
  have hT := smithETvCheck_holds
  simp only [chkT, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hT
  obtain ⟨⟨h1, h2⟩, h3⟩ := hT k hk i hi
  rw [tvArr_get hk, wtArr_get hi] at h1 h2 h3
  refine ⟨_, h1, ?_, ?_⟩
  · rw [← wtArr_get h1]
    exact h2
  · rw [← adjM_eq hi h1]
    exact h3

theorem commute_of_commuteB {A B : Array Nat} (hA : A.size = 20) (hB : B.size = 20)
    (h : commuteB A B = true) :
    ∀ c < 2 ^ 20, applyCols A (applyCols B c) = applyCols B (applyCols A c) := by
  simp only [commuteB, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine eq_of_xorLin (comp_xorLin (applyCols_xor A) (applyCols_xor B))
    (comp_xorLin (applyCols_xor B) (applyCols_xor A)) 20 fun m hm => ?_
  rw [applyCols_two_pow B (by omega), applyCols_two_pow A (by omega)]
  exact h m hm

theorem braid_of_braidB {A B : Array Nat} (hA : A.size = 20) (hB : B.size = 20)
    (h : braidB A B = true) : ∀ c < 2 ^ 20,
      applyCols A (applyCols B (applyCols A c)) = applyCols B (applyCols A (applyCols B c)) := by
  simp only [braidB, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine eq_of_xorLin (f := fun c => applyCols A (applyCols B (applyCols A c)))
    (g := fun c => applyCols B (applyCols A (applyCols B c)))
    (fun a b => by simp only [applyCols_xor]) (fun a b => by simp only [applyCols_xor]) 20
    fun m hm => ?_
  rw [applyCols_two_pow B (by omega), applyCols_two_pow A (by omega)]
  exact h m hm

theorem pair_rel {k l : Nat} (hkl : k < l) (hl : l < 693) :
    (hermC uPts[k]! uPts[l]! = 0 → ∀ c < 2 ^ 20,
      applyCols (tvCols k) (applyCols (tvCols l) c) =
        applyCols (tvCols l) (applyCols (tvCols k) c)) ∧
    (hermC uPts[k]! uPts[l]! ≠ 0 → ∀ c < 2 ^ 20,
      applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c)) =
        applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c))) := by
  have hP := smithEPairCheck_holds
  simp only [chkP, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hP
  rcases hP k (by omega) l hl with h | h
  · omega
  · rw [tvArr_get (by omega), tvArr_get hl] at h
    constructor
    · intro h0
      simp only [h0, beq_self_eq_true, ↓reduceIte] at h
      exact commute_of_commuteB (size_tvCols k) (size_tvCols l) h
    · intro h0
      simp only [beq_iff_eq, h0, ↓reduceIte] at h
      exact braid_of_braidB (size_tvCols k) (size_tvCols l) h

theorem comm_eq_basis' {T : Array Nat} (hT : T.size = 20) {D : SpanData}
    (hcoef : D.coef.size = 20)
    (h : ∀ m < 20, applyCols D.basis D.coef[m]! = T[m]! ^^^ 2 ^ m) {c : Nat} (hc : c < 2 ^ 20) :
    applyCols T c ^^^ c = applyCols D.basis (applyCols D.coef c) := by
  refine eq_of_xorLin (f := fun c => applyCols T c ^^^ c)
    (g := fun c => applyCols D.basis (applyCols D.coef c))
    (fun a b => ?_) (fun a b => by simp only [applyCols_xor]) 20 (fun m hm => ?_) c hc
  · simp only [applyCols_xor]
    ac_rfl
  · rw [applyCols_two_pow _ (by omega), applyCols_two_pow _ (by omega), h m hm]

theorem syn_comm' {T : Array Nat} (hT : T.size = 20) {D : SpanData}
    (h : ∀ m < 20, applyCols D.syn (T[m]! ^^^ 2 ^ m) = 0) {c : Nat} (hc : c < 2 ^ 20) :
    applyCols D.syn (applyCols T c ^^^ c) = 0 := by
  refine eq_of_xorLin (f := fun c => applyCols D.syn (applyCols T c ^^^ c))
    (g := fun _ => 0) (fun a b => ?_) (fun a b => by simp) 20 (fun m hm => ?_) c hc
  · rw [← applyCols_xor]
    congr 1
    rw [applyCols_xor]
    ac_rfl
  · rw [applyCols_two_pow _ (by omega)]
    exact h m hm

theorem syn_basis' {D E : SpanData} (hb : D.basis.size = 6) {d : Nat} (hd : d < 2 ^ 6) :
    applyCols (D.basis.map (applyCols E.syn)) d = applyCols E.syn (applyCols D.basis d) := by
  refine eq_of_xorLin (f := applyCols (D.basis.map (applyCols E.syn)))
    (g := fun d => applyCols E.syn (applyCols D.basis d)) (applyCols_xor _)
    (fun a b => by simp only [applyCols_xor]) 6 (fun i hi => ?_) d hd
  rw [applyCols_two_pow _ (by simpa [hb] using hi), applyCols_two_pow _ (by omega),
    getElem!_map' _ _ (by omega)]

theorem span_parts {k : Nat} (hk : k < 693) :
    (spanData (tvCols k)).basis.size = 6 ∧ (spanData (tvCols k)).coef.size = 20 ∧
    ∀ m < 20, (spanData (tvCols k)).coef[m]! < 64 ∧
      applyCols (spanData (tvCols k)).basis (spanData (tvCols k)).coef[m]! =
        (tvCols k)[m]! ^^^ 2 ^ m ∧
      applyCols (spanData (tvCols k)).syn ((tvCols k)[m]! ^^^ 2 ^ m) = 0 := by
  have hS := smithESpanCheck_holds
  simp only [chkSpan, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hS
  obtain ⟨⟨h1, h2⟩, h3⟩ := hS k hk
  rw [spanArr_get hk] at h1 h2 h3
  rw [tvArr_get hk] at h3
  refine ⟨h1, h2, fun m hm => ?_⟩
  obtain ⟨⟨h4, h5⟩, h6⟩ := h3 m hm
  rw [gensOf_get _ hm] at h5 h6
  exact ⟨h4, h5, h6⟩

theorem int_rel {k l : Nat}
    (hkl : k < l) (hl : l < 693) {c c' : Nat} (hc : c < 2 ^ 20) (hc' : c' < 2 ^ 20)
    (h : applyCols (tvCols k) c ^^^ c = applyCols (tvCols l) c' ^^^ c') :
    applyCols (tvCols k) c ^^^ c = 0 ∨ (hermC uPts[k]! uPts[l]! = 0 ∧
      ∃ j < 891, wt j = applyCols (tvCols k) c ^^^ c) := by
  have hk : k < 693 := by omega
  obtain ⟨hbk, hck, hk3⟩ := span_parts hk
  obtain ⟨-, -, hl3⟩ := span_parts hl
  set Dk := spanData (tvCols k)
  set Dl := spanData (tvCols l)
  set d := applyCols Dk.coef c
  have hd64 : d < 2 ^ 6 := applyCols_lt (fun m hm => (hk3 m (by omega)).1) c
  have hv : applyCols (tvCols k) c ^^^ c = applyCols Dk.basis d :=
    comm_eq_basis' (size_tvCols k) hck (fun m hm => (hk3 m hm).2.1) hc
  have hsyn : applyCols Dl.syn (applyCols Dk.basis d) = 0 := by
    rw [← hv, h]
    exact syn_comm' (size_tvCols l) (fun m hm => (hl3 m hm).2.2) hc'
  have hI := smithEIntCheck_holds
  simp only [chkI, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq, beq_iff_eq, Bool.and_eq_true] at hI
  rcases hI k hk l hl with h1 | h1
  · omega
  rw [spanArr_get hk, spanArr_get hl] at h1
  have hSd := syn_basis' (E := Dl) hbk hd64
  rcases h1 d hd64 with h2 | h2
  · exact absurd (hSd.trans hsyn) h2
  · rw [hv]
    rcases h2 with h3 | ⟨h3, h4⟩
    · exact Or.inl h3
    · exact Or.inr ⟨h3, (isWt_iff _).mp h4⟩

theorem pair_rel_sym {k l : Nat} (hk : k < 693) (hl : l < 693)
    (hkl : k ≠ l) :
    (∀ c < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) c) =
      applyCols (tvCols l) (applyCols (tvCols k) c)) ∨
    (∀ c < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c)) =
      applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c))) := by
  rcases Nat.lt_or_gt_of_ne hkl with h | h
  · by_cases h0 : hermC uPts[k]! uPts[l]! = 0
    · exact Or.inl ((pair_rel h hl).1 h0)
    · exact Or.inr ((pair_rel h hl).2 h0)
  · by_cases h0 : hermC uPts[l]! uPts[k]! = 0
    · exact Or.inl fun c hc => ((pair_rel h hk).1 h0 c hc).symm
    · exact Or.inr fun c hc => ((pair_rel h hk).2 h0 c hc).symm

theorem int_rel_sym
    {k l : Nat} (hk : k < 693) (hl : l < 693) (hkl : k ≠ l)
    {c c' : Nat} (hc : c < 2 ^ 20) (hc' : c' < 2 ^ 20)
    (h : applyCols (tvCols k) c ^^^ c = applyCols (tvCols l) c' ^^^ c') :
    applyCols (tvCols k) c ^^^ c = 0 ∨
      ((∀ e < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) e) =
        applyCols (tvCols l) (applyCols (tvCols k) e)) ∧
       ∃ j < 891, wt j = applyCols (tvCols k) c ^^^ c) := by
  rcases Nat.lt_or_gt_of_ne hkl with hlt | hlt
  · rcases int_rel hlt hl hc hc' h with h1 | ⟨h0, h1⟩
    · exact Or.inl h1
    · exact Or.inr ⟨(pair_rel hlt hl).1 h0, h1⟩
  · rcases int_rel hlt hk hc' hc h.symm with h1 | ⟨h0, h1⟩
    · exact Or.inl (h.trans h1)
    · refine Or.inr ⟨fun e he => ((pair_rel hlt hk).1 h0 e he).symm, ?_⟩
      rw [h]
      exact h1

end CFSG.LargeExtraspecial.S14.SMG
