module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Local

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight (genArrs)
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord wordPerm rep_posWord getElem!_map'
  letters_of_all mapWord_rep digitsOf)

structure TriData where
  qW : Array (List ℕ)
  qKeys : List ℕ
  qFuel : ℕ
  xW : List ℕ
  rKeys : List ℕ
  rFuel : ℕ
  hW : Array (List ℕ)
  yW : Array (List ℕ)
  zW : Array (List ℕ)

@[expose] def triQGens (X : TriData) : Array (Array ℕ) := X.qW.map (posWord 360 genArrs)

@[expose] def triRGens (X : TriData) : Array (Array ℕ) :=
  (triQGens X).push (posWord 360 genArrs X.xW)

@[expose] def triQCert (X : TriData) : ArrCert := enumBfs 360 (triQGens X) X.qKeys X.qFuel

@[expose] def triRCert (X : TriData) : ArrCert := enumBfs 360 (triRGens X) X.rKeys X.rFuel

@[expose] def triHArrs (X : TriData) : Array (Array ℕ) := X.hW.map (posWord 360 genArrs)

@[expose] def triYArrs (X : TriData) : Array (Array ℕ) := X.yW.map (posWord 360 (triQGens X))

@[expose] def triZArrs (X : TriData) : Array (Array ℕ) := X.zW.map (posWord 360 (triQGens X))

@[expose] def triEntryOK (g y z r : Array ℕ) : Bool :=
  eqA 360 (compA 360 (conjA 360 g r) y) (compA 360 y (conjA 360 g r)) &&
  eqA 360 (compA 360 (conjA 360 g r) z) (compA 360 z (conjA 360 g r))

@[expose] def triPointOK (cQ : ArrCert) (hs ys zs : Array (Array ℕ)) (r : Array ℕ) : Bool :=
  !(eqA 360 (compA 360 r (compA 360 r r)) (idA 360)) || cQ.pts.toList.any (eqA 360 r) ||
  (List.range hs.size).any fun e => triEntryOK hs[e]! ys[e]! zs[e]! r

@[expose] def triCheck' (X : TriData) (cQ cR : ArrCert) (hs ys zs : Array (Array ℕ)) : Bool :=
  decide (genArrs.size = 10) &&
  allLt genArrs.size (fun k => validA 360 genArrs[k]!) &&
  (X.qKeys ++ X.rKeys).all (fun p => decide (p < 360)) &&
  decide (X.qW.size = 3) &&
  X.qW.all (fun w => w.all fun l => decide (l < 8)) &&
  X.xW.all (fun l => decide (l < 10)) &&
  X.hW.all (fun w => w.all fun l => decide (l < 10)) &&
  X.yW.all (fun w => w.all fun l => decide (l < 3)) &&
  X.zW.all (fun w => w.all fun l => decide (l < 3)) &&
  decide (X.yW.size = X.hW.size) && decide (X.zW.size = X.hW.size) &&
  enumOK 360 (triQGens X) X.qKeys cQ && decide (cQ.pts.size = 243) &&
  enumOK 360 (triRGens X) X.rKeys cR && decide (cR.pts.size = 729) &&
  allLt hs.size (fun e => validA 360 hs[e]!) &&
  allLt hs.size (fun e =>
    !eqA 360 (compA 360 ys[e]! zs[e]!) (compA 360 zs[e]! ys[e]!)) &&
  allLt cR.pts.size (fun i => triPointOK cQ hs ys zs cR.pts[i]!)

@[expose] def triCheck (X : TriData) : Bool :=
  triCheck' X (triQCert X) (triRCert X) (triHArrs X) (triYArrs X) (triZArrs X)

@[expose] def triData : TriData where
  qW := (#["0102453202735104626732010245320273510462673010245672321",
         "2376232",
         "0136712325421076264015372023542010232"]).map digitsOf
  qKeys := [0, 1, 2]
  qFuel := 245
  xW := digitsOf "724302686203427"
  rKeys := [1, 2]
  rFuel := 731
  hW := (#["142573109", "", "125342056", "2626", "201453573889", "1425731088", "3205462046",
         "324620145315", "120420376889", "0205373156988", "062031326", "4735426249",
         "013768888", "4245316738888", "0123731353688", "147320762019", "235346246988",
         "012373135369", "0205373156", "124762453109", "020531562423", "067312042356",
         "0546735620149", "424531673889", "201253731369", "0201354237369", "14245310736",
         "20454203679", "676203153889", "2347312536788", "4673135369", ""]).map digitsOf
  yW := (#["112", "112", "112", "112", "112", "112", "112", "112", "112", "112", "112", "112",
         "112", "112", "112", "112", "112", "112", "112", "112", "112", "112", "112", "112",
         "112", "112", "112", "112", "112", "112", "112", "0010"]).map digitsOf
  zW := (#["011001", "011001", "011001", "011001", "011001", "011001", "011001", "011001",
         "011001", "011001", "011001", "011001", "011001", "011001", "011001", "011001",
         "011001", "011001", "011001", "011001", "011001", "011001", "011001", "011001",
         "011001", "011001", "011001", "011001", "011001", "011001", "011001", "1"]).map digitsOf

theorem triWordPerm_mem {S : Subgroup (Equiv.Perm (Fin 360))} {m : ℕ}
    (hS : ∀ l < m, permOfArr 360 genArrs[l]! ∈ S) {w : List ℕ} (hw : ∀ l ∈ w, l < m) :
    wordPerm 360 genArrs w ∈ S :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact hS l (hw l hl)

theorem triCheck_sound (X : TriData) (h : triCheck X = true)
    (Pω PA : Subgroup (Equiv.Perm (Fin 360)))
    (hω : ∀ l < 8, permOfArr 360 genArrs[l]! ∈ Pω)
    (hA : ∀ l < 10, permOfArr 360 genArrs[l]! ∈ PA) :
    ∃ Q R : Subgroup (Equiv.Perm (Fin 360)), Q ≤ Pω ∧ R ≤ PA ∧ Nat.card Q = 243 ∧
      Nat.card R = 729 ∧ ∀ r ∈ R, r ^ 3 = 1 → r ∈ Q ∨
        ∃ g y z : Equiv.Perm (Fin 360), g ∈ PA ∧ y ∈ Q ∧ z ∈ Q ∧ y * z ≠ z * y ∧
          g * r * g⁻¹ * y = y * (g * r * g⁻¹) ∧ g * r * g⁻¹ * z = z * (g * r * g⁻¹) := by
  unfold triCheck triCheck' at h
  simp only [Bool.and_eq_true, and_assoc, decide_eq_true_eq] at h
  obtain ⟨hsz, hgv, hkeys, hqsz, hqW, hxW, hhW, hyW, hzW, hys, hzs, hQenum, hQcard, hRenum,
    hRcard, hhv, hnc, hpts⟩ := h
  have hgv' : ∀ l < genArrs.size, validA 360 genArrs[l]! = true := fun l hl => allLt_spec hgv hl
  have hk3 : ∀ p ∈ X.qKeys ++ X.rKeys, p < 360 := fun p hp => by
    simpa using List.all_eq_true.1 hkeys p hp
  have hqk : ∀ p ∈ X.qKeys, p < 360 := fun p hp => hk3 p (by simp [hp])
  have hrk : ∀ p ∈ X.rKeys, p < 360 := fun p hp => hk3 p (by simp [hp])
  have hqWl := letters_of_all hqW
  have hhWl := letters_of_all hhW
  have hyWl := letters_of_all hyW
  have hzWl := letters_of_all hzW
  have hxWl : ∀ l ∈ X.xW, l < 10 := fun l hl => by simpa using List.all_eq_true.1 hxW l hl
  have hqsize : (triQGens X).size = 3 := by simp [triQGens, hqsz]
  have hqgv : ∀ l < (triQGens X).size, validA 360 (triQGens X)[l]! = true := fun l hl =>
    enumOK_gens_valid hQenum hl
  have hqgrep : ∀ k < (triQGens X).size,
      Rep 360 (triQGens X)[k]! (wordPerm 360 genArrs X.qW[k]!) := by
    intro k hk
    have hk' : k < X.qW.size := by simpa [triQGens] using hk
    exact mapWord_rep hgv' (fun k hk l hl => (hqWl k hk l hl).trans (by omega)) hk'
  have hqgmem : ∀ (S : Subgroup (Equiv.Perm (Fin 360))) (m : ℕ), m ≤ 10 →
      (∀ l < m, permOfArr 360 genArrs[l]! ∈ S) → 8 ≤ m →
      ∀ k < (triQGens X).size, permOfArr 360 (triQGens X)[k]! ∈ S := by
    intro S m hm hS h8 k hk
    have hk' : k < X.qW.size := by simpa [triQGens] using hk
    rw [permOfArr_eq_of_rep (hqgrep k hk)]
    exact triWordPerm_mem hS fun l hl => (hqWl k hk' l hl).trans_le h8
  set Q := Subgroup.closure (permsA 360 (triQGens X)) with hQdef
  set R := Subgroup.closure (permsA 360 (triRGens X)) with hRdef
  have hQP : ∀ (S : Subgroup (Equiv.Perm (Fin 360))) (m : ℕ), m ≤ 10 →
      (∀ l < m, permOfArr 360 genArrs[l]! ∈ S) → 8 ≤ m → Q ≤ S := by
    intro S m hm hS h8
    rw [hQdef, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hqgmem S m hm hS h8 k hk
  have hRsize : (triRGens X).size = (triQGens X).size + 1 := by simp [triRGens]
  have hRgv : ∀ l < (triRGens X).size, validA 360 (triRGens X)[l]! = true := fun l hl =>
    enumOK_gens_valid hRenum hl
  have hRgP : ∀ k < (triRGens X).size, permOfArr 360 (triRGens X)[k]! ∈ PA := by
    intro k hk
    by_cases hlt : k < (triQGens X).size
    · have : (triRGens X)[k]! = (triQGens X)[k]! := by
        rw [getElem!_pos _ k hk, getElem!_pos _ k hlt]
        simp [triRGens, Array.getElem_push_lt hlt]
      rw [this]
      exact hqgmem PA 10 le_rfl hA (by norm_num) k hlt
    · have hk' : k = (triQGens X).size := by omega
      have : (triRGens X)[k]! = posWord 360 genArrs X.xW := by
        rw [getElem!_pos _ k hk]
        subst hk'
        simp [triRGens]
      rw [this, permOfArr_eq_of_rep (rep_posWord hgv' X.xW fun l hl => by
        have := hxWl l hl; omega)]
      exact triWordPerm_mem hA hxWl
  have hRP : R ≤ PA := by
    rw [hRdef, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hRgP k hk
  have hQcard' : Nat.card Q = 243 := (enumOK_spec hqk hQenum).2.1.trans hQcard
  have hRcard' : Nat.card R = 729 := (enumOK_spec hrk hRenum).2.1.trans hRcard
  refine ⟨Q, R, hQP Pω 8 (by norm_num) hω le_rfl, hRP, hQcard', hRcard', ?_⟩
  intro r hr hr3
  obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep hrk hRenum hr
  have hpt := allLt_spec hpts hi
  unfold triPointOK at hpt
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, List.mem_range] at hpt
  rcases hpt with (hcube | hQany) | ⟨e, he, hent⟩
  · exfalso
    have h1 : r * (r * r) = 1 := by rw [← hr3]; simp [pow_succ, mul_assoc]
    have := (eqA_iff (rep_compA hrep (rep_compA hrep hrep)) rep_idA).2 h1
    rw [this] at hcube
    exact absurd hcube (by simp)
  · exact Or.inl (enumOK_mem_of_any hqk hQenum hrep (List.any_eq_true.2 hQany))
  · right
    have he' : e < X.hW.size := by simpa [triHArrs] using he
    have hye : e < X.yW.size := by omega
    have hze : e < X.zW.size := by omega
    have hhrep : Rep 360 (triHArrs X)[e]! (wordPerm 360 genArrs X.hW[e]!) :=
      mapWord_rep hgv' (fun k hk l hl => (hhWl k hk l hl).trans_le (by omega)) he'
    have hyrep : Rep 360 (triYArrs X)[e]! (wordPerm 360 (triQGens X) X.yW[e]!) :=
      mapWord_rep hqgv (fun k hk l hl => (hyWl k hk l hl).trans_le (by omega)) hye
    have hzrep : Rep 360 (triZArrs X)[e]! (wordPerm 360 (triQGens X) X.zW[e]!) :=
      mapWord_rep hqgv (fun k hk l hl => (hzWl k hk l hl).trans_le (by omega)) hze
    have hhv' : validA 360 (triHArrs X)[e]! = true := allLt_spec hhv (by simpa [triHArrs] using he')
    have hgeq : permOfArr 360 (triHArrs X)[e]! = wordPerm 360 genArrs X.hW[e]! :=
      permOfArr_eq_of_rep hhrep
    have hcrep := rep_conjA (Y := r) hhv' hrep
    rw [hgeq] at hcrep
    have hQmem : ∀ w : List ℕ, (∀ l ∈ w, l < 3) → wordPerm 360 (triQGens X) w ∈ Q := by
      intro w hw
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact Subgroup.subset_closure ⟨l, by rw [hqsize]; exact hw l hl, rfl⟩
    refine ⟨wordPerm 360 genArrs X.hW[e]!, wordPerm 360 (triQGens X) X.yW[e]!,
      wordPerm 360 (triQGens X) X.zW[e]!, ?_, hQmem _ (hyWl e hye), hQmem _ (hzWl e hze), ?_, ?_, ?_⟩
    · exact triWordPerm_mem hA fun l hl => hhWl e he' l hl
    · intro hcomm
      have hnce := allLt_spec hnc (by simpa [triHArrs] using he')
      simp only [Bool.not_eq_true'] at hnce
      have := (eqA_iff (rep_compA hyrep hzrep) (rep_compA hzrep hyrep)).2 hcomm
      rw [this] at hnce
      exact absurd hnce (by simp)
    · simp only [triEntryOK, Bool.and_eq_true] at hent
      exact (eqA_iff (rep_compA hcrep hyrep) (rep_compA hyrep hcrep)).1 hent.1
    · simp only [triEntryOK, Bool.and_eq_true] at hent
      exact (eqA_iff (rep_compA hcrep hzrep) (rep_compA hzrep hcrep)).1 hent.2

end CFSG.HardMathSupport.Curtis.Coordinator
