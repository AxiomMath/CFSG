module

public import CFSG.Monster.B.Co2.BFS
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Certificates.SchreierChainOrder
public import Certificates.Data.CFSGNative.Schreier.Check

public noncomputable section

namespace CFSG.Certificates

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native SchreierOrbitState

variable {n : ℕ}

structure ChainArrays (Q : RawSchreierDatum n) (O S : Array (Array ℕ)) (base : Array ℕ)
    (W : Array (List ℤ)) : Prop where
  orig_size : O.size = Q.originalCount
  strong_size : S.size = Q.strongCount
  base_size : base.size = Q.baseCount
  orig : ∀ k : Fin Q.originalCount, Rep n O[(k : ℕ)]! (Q.original.get k)
  strong : ∀ j : Fin Q.strongCount, Rep n S[(j : ℕ)]! (Q.strong.get j)
  base_val : ∀ i : Fin Q.baseCount, ((Q.base.get i : Fin n) : ℕ) = base[(i : ℕ)]!
  deriv : ∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
    Q.derivation j hj = toLetters j.val W[(j : ℕ)]!

structure ChainCheckFacts (n : ℕ) (O S : Array (Array ℕ)) (base : Array ℕ)
    (W : Array (List ℤ)) (chunks : ℕ) : Prop where
  orig_le : O.size ≤ S.size
  words_size : W.size = S.size
  strong_inv : ∀ j < S.size, isInvA n S[j]! (rawInvs n S)[j]! = true
  initial : ∀ k < O.size, eqA n S[k]! O[k]! = true
  words : ∀ j < S.size, O.size ≤ j → lettersOK j W[j]! = true ∧
    eqA n S[j]! (wordA n S (rawInvs n S) W[j]!) = true
  terminal : ∀ j < S.size, fixesFirst base S[j]! base.size = true → eqA n S[j]! (idA n) = true
  base_lt : ∀ i < base.size, base[i]! < n
  level : ∀ i < base.size,
    levelOK n base[i]! (rawSteps n S base i) (rawLevels n S base)[i]! = true
  schreier : ∀ i < base.size, schreierOK n (rawLevels n S base) base i (rawSteps n S base i)
    (rawLevels n S base)[i]! chunks = true

theorem chainCheckFacts {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
    {chunks : ℕ} (h : rawChainOK n O S base W chunks = true) :
    ChainCheckFacts n O S base W chunks := by
  simp only [rawChainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, fun j hj => allLt_spec h3 hj, fun k hk => allLt_spec h4 hk,
    fun j hj hj2 => ?_, fun j hj hf => ?_, fun i hi => of_decide_eq_true (allLt_spec h7 hi),
    fun i hi => allLt_spec h8 hi, fun i hi => allLt_spec h9 hi⟩
  · have := allLt_spec h5 hj
    simpa [show ¬ j < O.size by omega] using this
  · have := allLt_spec h6 hj
    simpa [hf] using this

namespace ChainArrays

variable {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
  {chunks : ℕ}

@[expose] def strongAt (Q : RawSchreierDatum n) (j : ℕ) : Equiv.Perm (Fin n) :=
  if h : j < Q.strongCount then Q.strong.get ⟨j, h⟩ else 1

theorem strongAt_of_lt (Q : RawSchreierDatum n) {j : ℕ} (hj : j < Q.strongCount) :
    strongAt Q j = Q.strong.get ⟨j, hj⟩ := by
  simp only [strongAt, hj, ↓reduceDIte]

theorem rep_strong (hA : ChainArrays Q O S base W) {j : ℕ} (hj : j < S.size) :
    Rep n S[j]! (strongAt Q j) := by
  have hj' : j < Q.strongCount := hA.strong_size ▸ hj
  rw [strongAt_of_lt Q hj']
  exact hA.strong ⟨j, hj'⟩

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
include hA hF

theorem rep_strongInv {j : ℕ} (hj : j < S.size) :
    Rep n (rawInvs n S)[j]! (strongAt Q j)⁻¹ :=
  rep_inv_of_isInvA (hA.rep_strong hj) (hF.strong_inv j hj)

end Facts

theorem strong_toList (Q : RawSchreierDatum n) :
    Q.strong.toList = (List.range Q.strongCount).map (strongAt Q) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.length_map, List.length_range] at h2
  rw [List.getElem_map, List.getElem_range, strongAt_of_lt Q h2, Vector.getElem_toList]
  rfl

@[expose] def toFin (Q : RawSchreierDatum n) (x : ℕ) : Fin n :=
  ⟨x % n, Nat.mod_lt _ (by have := Q.degree_pos; omega)⟩

theorem toFin_eq (Q : RawSchreierDatum n) {x : ℕ} (hx : x < n) : toFin Q x = ⟨x, hx⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hx)

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
include hA hF

theorem base_toList :
    Q.base.toList = (List.range Q.baseCount).map fun k => toFin Q base[k]! := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.length_map, List.length_range] at h2
  rw [List.getElem_map, List.getElem_range, Vector.getElem_toList]
  have hb := hF.base_lt k (hA.base_size ▸ h2)
  rw [toFin_eq Q hb]
  apply Fin.ext
  exact hA.base_val ⟨k, h2⟩

theorem fixes_iff {j : ℕ} (hj : j < S.size) {i : ℕ} (hi : i ≤ Q.baseCount) :
    ((Q.base.toList.take i).all fun b => decide (strongAt Q j b = b)) =
      fixesFirst base S[j]! i := by
  rw [hA.base_toList hF, List.map_take.symm, List.take_range, Nat.min_eq_left hi,
    Bool.eq_iff_iff, List.all_map, List.all_eq_true, fixesFirst, allLt_iff]
  simp only [List.mem_range, Function.comp_apply, decide_eq_true_eq, beq_iff_eq]
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  have hb := hF.base_lt k (by rw [hA.base_size]; omega)
  rw [toFin_eq Q hb, (hA.rep_strong hj).apply hb, Fin.ext_iff]

theorem levelGenerators_eq {i : ℕ} (hi : i ≤ Q.baseCount) :
    Q.levelGenerators i = (levelIdx S base i).map (strongAt Q) := by
  rw [RawSchreierDatum.levelGenerators, strong_toList, List.filter_map, levelIdx,
    hA.strong_size]
  congr 1
  apply List.filter_congr
  intro j hj
  exact hA.fixes_iff hF (hA.strong_size ▸ List.mem_range.1 hj) hi

end Facts

theorem levelIdx_lt {i j : ℕ} (hj : j ∈ levelIdx S base i) : j < S.size := by
  rw [levelIdx] at hj
  exact List.mem_range.1 (List.mem_filter.1 hj).1

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
include hA hF

theorem levelSteps_eq {i : ℕ} (hi : i ≤ Q.baseCount) :
    Q.levelSteps i = (levelIdx S base i).map (strongAt Q) ++
      (levelIdx S base i).map fun j => (strongAt Q j)⁻¹ := by
  rw [RawSchreierDatum.levelSteps, hA.levelGenerators_eq hF hi, List.map_map]
  rfl

theorem chainSteps_size {i : ℕ} (hi : i ≤ Q.baseCount) :
    (rawSteps n S base i).size = (Q.levelSteps i).length := by
  rw [hA.levelSteps_eq hF hi, rawSteps, levelSteps]
  simp

theorem rep_chainSteps {i : ℕ} (hi : i ≤ Q.baseCount) {j : ℕ}
    (hj : j < (Q.levelSteps i).length) :
    Rep n (rawSteps n S base i)[j]! ((Q.levelSteps i)[j]) := by
  have hj' := hj
  rw [hA.levelSteps_eq hF hi] at hj'
  set idx := levelIdx S base i with hidx
  have hsz : j < (rawSteps n S base i).size := by rw [hA.chainSteps_size hF hi]; exact hj
  rw [getElem!_pos (rawSteps n S base i) j hsz]
  simp only [List.length_append, List.length_map] at hj'
  have e1 : ∀ h : j < (Q.levelSteps i).length, (Q.levelSteps i)[j] =
      (idx.map (strongAt Q) ++ idx.map fun j => (strongAt Q j)⁻¹)[j]'(by
        simpa [hA.levelSteps_eq hF hi] using h) := by
    intro h
    simp only [hA.levelSteps_eq hF hi, idx]
  rw [e1 hj]
  by_cases hlt : j < idx.length
  · rw [List.getElem_append_left (by simpa using hlt)]
    simp only [List.getElem_map]
    have : (rawSteps n S base i)[j] = S[idx[j]]! := by
      simp only [rawSteps, levelSteps, ← hidx]
      rw [Array.getElem_append_left (by simpa using hlt)]
      simp
    rw [this]
    exact hA.rep_strong (levelIdx_lt (List.getElem_mem hlt))
  · have hle : idx.length ≤ j := by omega
    rw [List.getElem_append_right (by simpa using hle)]
    simp only [List.getElem_map, List.length_map]
    have hk : j - idx.length < idx.length := by omega
    have : (rawSteps n S base i)[j] = (rawInvs n S)[idx[j - idx.length]]! := by
      simp only [rawSteps, levelSteps, ← hidx]
      rw [Array.getElem_append_right (by simpa using hle)]
      simp
    rw [this]
    exact hA.rep_strongInv hF (levelIdx_lt (List.getElem_mem hk))

end Facts

@[expose] def lev (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (i : ℕ) : Level :=
  (rawLevels n S base)[i]!

@[expose] def levPts (Q : RawSchreierDatum n) (S : Array (Array ℕ)) (base : Array ℕ)
    (i k : ℕ) : Fin n :=
  toFin Q (lev n S base i).pts[k]!

@[expose] def levT (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (i k : ℕ) :
    Equiv.Perm (Fin n) :=
  permOfArr n (lev n S base i).tr[k]!

structure LevelFacts (n root : ℕ) (steps : Array (Array ℕ)) (L : Level) : Prop where
  pos : 0 < L.pts.size
  le : L.pts.size ≤ n
  root : L.pts[0]! = root
  pts_lt : ∀ k < L.pts.size, L.pts[k]! < n
  pos_pts : ∀ k < L.pts.size, L.pos[L.pts[k]!]! = k
  pts_pos : ∀ z < n, L.pos[z]! < L.pts.size → L.pts[L.pos[z]!]! = z
  par_lt : ∀ k < L.pts.size, 0 < k → L.par[k]! < k
  lab_lt : ∀ k < L.pts.size, 0 < k → L.lab[k]! < steps.size
  edge : ∀ k < L.pts.size, 0 < k → (steps[L.lab[k]!]!)[L.pts[L.par[k]!]!]! = L.pts[k]!
  mono : ∀ k < L.pts.size, 0 < k → k + 1 < L.pts.size →
    lexLt L.par[k]! L.lab[k]! L.par[k + 1]! L.lab[k + 1]! = true
  closed : ∀ h < L.pts.size, ∀ j < steps.size,
    L.pos[(steps[j]!)[L.pts[h]!]!]! < L.pts.size ∧
      (L.pos[(steps[j]!)[L.pts[h]!]!]! = 0 ∨
        lexLt h j L.par[L.pos[(steps[j]!)[L.pts[h]!]!]!]! L.lab[L.pos[(steps[j]!)[L.pts[h]!]!]!]! =
          false)
  tr_zero : eqA n L.tr[0]! (idA n) = true
  tr_step : ∀ k < L.pts.size, 0 < k →
    eqA n L.tr[k]! (compA n steps[L.lab[k]!]! L.tr[L.par[k]!]!) = true
  tr_inv : ∀ k < L.pts.size, isInvA n L.tr[k]! L.trInv[k]! = true

theorem levelFacts_of_levelOK {root : ℕ} {steps : Array (Array ℕ)} {L : Level}
    (h : levelOK n root steps L = true) : LevelFacts n root steps L := by
  simp only [levelOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, fun k hk => ?_, fun k hk => ?_, fun z hz hzm => ?_, fun k hk hk0 => ?_,
    fun k hk hk0 => ?_, fun k hk hk0 => ?_, fun k hk hk0 hk1 => ?_, fun h hh j hj => ?_, h9,
    fun k hk hk0 => ?_, fun k hk => allLt_spec h11 hk⟩
  · exact (by simpa [Bool.and_eq_true] using allLt_spec h4 hk : _ ∧ _).1
  · exact (by simpa [Bool.and_eq_true] using allLt_spec h4 hk : _ ∧ _).2
  · have := allLt_spec h5 hz
    simpa [hzm] using this
  · have := allLt_spec h6 hk
    simp only [show k ≠ 0 by omega, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq, false_or] at this
    exact this.1.1
  · have := allLt_spec h6 hk
    simp only [show k ≠ 0 by omega, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq, false_or] at this
    exact this.1.2
  · have := allLt_spec h6 hk
    simp only [show k ≠ 0 by omega, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq, false_or] at this
    exact this.2
  · have := allLt_spec h7 hk
    simpa [show k ≠ 0 by omega, hk1] using this
  · have := allLt_spec (allLt_spec h8 hh) hj
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
      Bool.not_eq_true'] at this
    exact this
  · have := allLt_spec h10 hk
    simpa [show k ≠ 0 by omega] using this

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
include hA hF

theorem levelFacts {i : ℕ} (hi : i < Q.baseCount) :
    LevelFacts n base[i]! (rawSteps n S base i) (lev n S base i) :=
  levelFacts_of_levelOK (hF.level i (hA.base_size ▸ hi))

theorem levPts_val {i k : ℕ} (hi : i < Q.baseCount) (hk : k < (lev n S base i).pts.size) :
    ((levPts Q S base i k : Fin n) : ℕ) = (lev n S base i).pts[k]! := by
  rw [levPts, toFin_eq Q ((hA.levelFacts hF hi).pts_lt k hk)]

theorem rep_levT {i k : ℕ} (hi : i < Q.baseCount) (hk : k < (lev n S base i).pts.size) :
    Rep n (lev n S base i).tr[k]! (levT n S base i k) :=
  (rep_permOfArr ((hA.levelFacts hF hi).tr_inv k hk)).1

theorem rep_levTInv {i k : ℕ} (hi : i < Q.baseCount) (hk : k < (lev n S base i).pts.size) :
    Rep n (lev n S base i).trInv[k]! (levT n S base i k)⁻¹ :=
  (rep_permOfArr ((hA.levelFacts hF hi).tr_inv k hk)).2

theorem bfsCert {i : ℕ} (hi : i < Q.baseCount) :
    BFSCert (Q.levelSteps i) (Q.base.get ⟨i, hi⟩) (lev n S base i).pts.size (levPts Q S base i)
      (fun k => (lev n S base i).par[k]!) (fun k => (lev n S base i).lab[k]!)
      (levT n S base i) := by
  have F := hA.levelFacts hF hi
  have hsz := hA.chainSteps_size hF (Nat.le_of_lt hi)
  have hlab : ∀ k, 0 < k → k < (lev n S base i).pts.size →
      (lev n S base i).lab[k]! < (Q.levelSteps i).length :=
    fun k hk0 hk => hsz ▸ F.lab_lt k hk hk0
  have hedge : ∀ k (hk0 : 0 < k) (hk : k < (lev n S base i).pts.size),
      ((Q.levelSteps i)[(lev n S base i).lab[k]!]'(hlab k hk0 hk))
        (levPts Q S base i ((lev n S base i).par[k]!)) = levPts Q S base i k := by
    intro k hk0 hk
    have hp := F.par_lt k hk hk0
    apply Fin.ext
    rw [hA.levPts_val hF hi hk, ← F.edge k hk hk0,
      (hA.rep_chainSteps hF (Nat.le_of_lt hi) (hlab k hk0 hk)).apply (F.pts_lt _ (by omega))]
    congr 2
    exact Fin.ext (hA.levPts_val hF hi (by omega))
  refine ⟨F.pos, ?_, ?_, ?_, fun k hk0 hk => F.par_lt k hk hk0, hlab, hedge, ?_, ?_, ?_⟩
  · apply Fin.ext
    rw [hA.levPts_val hF hi F.pos, F.root, hA.base_val ⟨i, hi⟩]
  · exact (eqA_iff (hA.rep_levT hF hi F.pos) rep_idA).1 F.tr_zero
  · intro a ha b hb hab
    have h1 := congrArg Fin.val hab
    rw [hA.levPts_val hF hi ha, hA.levPts_val hF hi hb] at h1
    rw [← F.pos_pts a ha, ← F.pos_pts b hb, h1]
  · intro k hk0 hk
    have hp := F.par_lt k hk hk0
    have hrep := rep_compA (hA.rep_chainSteps hF (Nat.le_of_lt hi) (hlab k hk0 hk))
      (hA.rep_levT hF hi (by omega : (lev n S base i).par[k]! < (lev n S base i).pts.size))
    exact (eqA_iff (hA.rep_levT hF hi hk) hrep).1 (F.tr_step k hk hk0)
  · intro k hk0 hk1
    have := F.mono k (by omega) hk0 hk1
    simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at this
    exact this
  · intro h hh j hj
    have hj' : j < (rawSteps n S base i).size := by rw [hsz]; exact hj
    obtain ⟨hk, hle⟩ := F.closed h hh j hj'
    set z := ((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]! with hz
    have hzn : z < n := by
      rw [hz, (hA.rep_chainSteps hF (Nat.le_of_lt hi) hj).apply (F.pts_lt h hh)]
      exact Fin.isLt _
    refine ⟨(lev n S base i).pos[z]!, hk, ?_, ?_⟩
    · apply Fin.ext
      rw [hA.levPts_val hF hi hk, F.pts_pos z hzn hk, hz,
        (hA.rep_chainSteps hF (Nat.le_of_lt hi) hj).apply (F.pts_lt h hh)]
      congr 2
      exact Fin.ext (hA.levPts_val hF hi hh).symm
    · rcases hle with h0 | hl
      · exact Or.inl h0
      · right
        intro hlex
        simp only [lexLt, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff,
          beq_eq_false_iff_ne, ne_eq] at hl
        unfold LexLt at hlex
        omega

theorem orbitSearch_eq {i : ℕ} (hi : i < Q.baseCount) :
    Q.orbitSearch ⟨i, hi⟩ =
      ⟨(List.range (lev n S base i).pts.size).map fun k =>
        (levPts Q S base i k, levT n S base i k), []⟩ :=
  (hA.bfsCert hF hi).run_initial_eq

theorem transversal_of_lt {i : ℕ} (hi : i < Q.baseCount) {k : ℕ}
    (hk : k < (lev n S base i).pts.size) :
    (Q.orbitSearch ⟨i, hi⟩).transversal? (levPts Q S base i k) = some (levT n S base i k) := by
  rw [hA.orbitSearch_eq hF hi]
  exact (hA.bfsCert hF hi).lookup_recs_of_lt le_rfl hk

theorem transversal_eq_none {i : ℕ} (hi : i < Q.baseCount) {z : Fin n}
    (hz : ¬ (lev n S base i).pos[(z : ℕ)]! < (lev n S base i).pts.size) :
    (Q.orbitSearch ⟨i, hi⟩).transversal? z = none := by
  rw [hA.orbitSearch_eq hF hi]
  change List.lookup z ((List.range (lev n S base i).pts.size).map fun k =>
    (levPts Q S base i k, levT n S base i k)) = none
  rw [List.lookup_eq_none_iff]
  intro p hp
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  rw [bne_iff_ne]
  intro he
  apply hz
  rw [he, hA.levPts_val hF hi hk, (hA.levelFacts hF hi).pos_pts k hk]
  exact hk

end Facts

theorem schreierSiftSucceeds_cons_some (b : Fin n) (q : SchreierOrbitState n)
    (levels : List (Fin n × SchreierOrbitState n)) (h t : Equiv.Perm (Fin n))
    (ht : q.transversal? (h b) = some t) :
    schreierSiftSucceeds ((b, q) :: levels) h = schreierSiftSucceeds levels (t⁻¹ * h) := by
  unfold schreierSiftSucceeds
  rw [schreierSiftResidual_available b q levels h t ht]

theorem schreierSiftSucceeds_cons_none (b : Fin n) (q : SchreierOrbitState n)
    (levels : List (Fin n × SchreierOrbitState n)) (h : Equiv.Perm (Fin n))
    (ht : q.transversal? (h b) = none) : schreierSiftSucceeds ((b, q) :: levels) h = false := by
  unfold schreierSiftSucceeds
  rw [schreierSiftResidual_unavailable b q levels h ht]

theorem chainLevels_size (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) :
    (rawLevels n S base).size = base.size := by
  simp [rawLevels]

theorem chainLevels_getElem {l : ℕ} (hl : l < (rawLevels n S base).size) :
    (rawLevels n S base)[l] = lev n S base l := by
  rw [lev, getElem!_pos (rawLevels n S base) l hl]

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
include hA hF

theorem siftA_eq : ∀ d l, l + d = Q.baseCount → ∀ (g : Array ℕ) (G : Equiv.Perm (Fin n)),
    Rep n g G → siftA n (rawLevels n S base) base l g =
      schreierSiftSucceeds (Q.siftLevels Q.orbitTables l) G := by
  intro d
  induction d with
  | zero =>
    intro l hl g G hG
    have hle : l = Q.baseCount := by omega
    subst hle
    rw [siftA, dite_eq_right (by rw [chainLevels_size, hA.base_size]; omega)]
    have hnil : Q.siftLevels Q.orbitTables Q.baseCount = [] := by
      simp [RawSchreierDatum.siftLevels]
    rw [hnil]
    rw [Bool.eq_iff_iff, eqA_iff hG rep_idA, schreierSiftSucceeds_nil]
  | succ d ih =>
    intro l hl g G hG
    have hlb : l < Q.baseCount := by omega
    have hls : l < (rawLevels n S base).size := by
      rw [chainLevels_size, hA.base_size]; exact hlb
    rw [siftA, dite_eq_left hls, chainLevels_getElem hls]
    have hcons := Q.siftLevels_cons Q.orbitTables ⟨l, hlb⟩
    simp only at hcons
    rw [hcons, RawSchreierDatum.orbitTables_get]
    set b := Q.base.get ⟨l, hlb⟩ with hb
    have hbv : (b : ℕ) = base[l]! := hA.base_val ⟨l, hlb⟩
    have hgb : g[base[l]!]! = (G b : ℕ) := by
      rw [← hbv]
      exact hG b
    rw [hgb]
    by_cases hk : (lev n S base l).pos[(G b : ℕ)]! < (lev n S base l).pts.size
    · have hpts : levPts Q S base l ((lev n S base l).pos[(G b : ℕ)]!) = G b := by
        apply Fin.ext
        rw [hA.levPts_val hF hlb hk, (hA.levelFacts hF hlb).pts_pos _ (G b).2 hk]
      have ht := hA.transversal_of_lt hF hlb hk
      rw [hpts] at ht
      rw [schreierSiftSucceeds_cons_some _ _ _ _ _ ht]
      simp only [hk, decide_true, Bool.true_and]
      exact ih (l + 1) (by omega) _ _ (rep_compA (hA.rep_levTInv hF hlb hk) hG)
    · rw [schreierSiftSucceeds_cons_none _ _ _ _ (hA.transversal_eq_none hF hlb hk)]
      simp [hk]

theorem initial : ∀ j : Fin Q.originalCount,
    Q.strong.get (Fin.castLE Q.originalCount_le j) = Q.original.get j := by
  intro j
  have hjO : (j : ℕ) < O.size := by rw [hA.orig_size]; exact j.2
  have hjS : (j : ℕ) < S.size := lt_of_lt_of_le hjO hF.orig_le
  have h1 := hA.rep_strong hjS
  rw [strongAt_of_lt Q (hA.strong_size ▸ hjS)] at h1
  exact eq_of_eqA h1 (hA.orig j) (hF.initial j hjO)

theorem words : ∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
    Q.strong.get j = Q.derivationValue j hj := by
  intro j hj
  have hjS : (j : ℕ) < S.size := by rw [hA.strong_size]; exact j.2
  have hjO : O.size ≤ (j : ℕ) := by rw [hA.orig_size]; exact hj
  obtain ⟨hl, he⟩ := hF.words j hjS hjO
  have hrep := rep_wordA (gs := strongAt Q) (j := j.val)
    (fun h hh => hA.rep_strong (by omega)) (fun h hh => hA.rep_strongInv hF (by omega)) _ hl
  have h1 := hA.rep_strong hjS
  rw [strongAt_of_lt Q j.2] at h1
  refine (eqA_iff h1 hrep).1 he |>.trans ?_
  unfold RawSchreierDatum.derivationValue schreierWordValue
  rw [hA.deriv j hj]
  congr 1
  funext h
  exact strongAt_of_lt Q (by omega)

theorem terminal : ∀ s ∈ Q.levelGenerators Q.baseCount, s = 1 := by
  intro s hs
  rw [hA.levelGenerators_eq hF le_rfl, List.mem_map] at hs
  obtain ⟨j, hj, rfl⟩ := hs
  have hjS := levelIdx_lt hj
  have hfix : fixesFirst base S[j]! base.size = true := by
    rw [levelIdx, List.mem_filter] at hj
    rw [hA.base_size]
    exact hj.2
  exact (eqA_iff (hA.rep_strong hjS) rep_idA).1 (hF.terminal j hjS hfix)

theorem schreier (hc : 0 < chunks) : ∀ (i : Fin Q.baseCount) (x : Fin n)
    (tx : Equiv.Perm (Fin n)), (Q.orbitSearch i).transversal? x = some tx →
    ∀ s ∈ Q.levelSteps i.val, ∃ ty : Equiv.Perm (Fin n),
      (Q.orbitSearch i).transversal? (s x) = some ty ∧
      schreierSiftSucceeds (Q.siftLevels Q.orbitTables (i.val + 1)) (ty⁻¹ * s * tx) = true := by
  rintro ⟨i, hi⟩ x tx htx s hs
  rw [hA.orbitSearch_eq hF hi] at htx
  change List.lookup x ((List.range (lev n S base i).pts.size).map fun k =>
    (levPts Q S base i k, levT n S base i k)) = some tx at htx
  obtain ⟨before, after, heq, -⟩ := List.lookup_eq_some_iff.1 htx
  have hmem : (x, tx) ∈ (List.range (lev n S base i).pts.size).map fun k =>
      (levPts Q S base i k, levT n S base i k) := by
    rw [heq]
    simp
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hmem
  obtain ⟨h, hh, rfl, rfl⟩ := hmem
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  have F := hA.levelFacts hF hi
  have hsz := hA.chainSteps_size hF (Nat.le_of_lt hi)
  have hj' : j < (rawSteps n S base i).size := by rw [hsz]; exact hj
  have hrs := hA.rep_chainSteps hF (Nat.le_of_lt hi) hj
  have htest : allLt (rawSteps n S base i).size (fun j =>
      decide ((lev n S base i).pos[((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]!]! <
        (lev n S base i).pts.size) &&
        siftA n (rawLevels n S base) base (i + 1)
          (compA n (lev n S base i).trInv[(lev n S base i).pos[((rawSteps n S base i)[j]!)[
            (lev n S base i).pts[h]!]!]!]!
            (compA n (rawSteps n S base i)[j]! (lev n S base i).tr[h]!))) = true :=
    parLt_spec hc (hF.schreier i (hA.base_size ▸ hi)) h hh
  have htest' := allLt_spec htest hj'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htest'
  obtain ⟨hk, hsift⟩ := htest'
  have hzv : ((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]! =
      ((Q.levelSteps i)[j] (levPts Q S base i h) : ℕ) := by
    rw [hrs.apply (F.pts_lt h hh)]
    congr 2
    exact Fin.ext (hA.levPts_val hF hi hh).symm
  have hpts : levPts Q S base i
      ((lev n S base i).pos[((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]!]!) =
      (Q.levelSteps i)[j] (levPts Q S base i h) := by
    apply Fin.ext
    rw [hA.levPts_val hF hi hk, F.pts_pos _ (by rw [hzv]; exact Fin.isLt _) hk, hzv]
  refine ⟨levT n S base i
    ((lev n S base i).pos[((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]!]!), ?_, ?_⟩
  · rw [← hpts]
    exact hA.transversal_of_lt hF hi hk
  · have hrep := rep_compA (hA.rep_levTInv hF hi hk) (rep_compA hrs (hA.rep_levT hF hi hh))
    rw [mul_assoc, ← hA.siftA_eq hF (Q.baseCount - (i + 1)) (i + 1) (by omega) _ _ hrep]
    exact hsift

theorem orbitSize_eq {i : ℕ} (hi : i < Q.baseCount) :
    Q.orbitSize ⟨i, hi⟩ = (lev n S base i).pts.size := by
  rw [RawSchreierDatum.orbitSize, hA.orbitSearch_eq hF hi]
  simp [SchreierOrbitState.keys]

end Facts

end ChainArrays

theorem validSchreier_of_chainOK {Q : RawSchreierDatum n} {O S : Array (Array ℕ)}
    {base : Array ℕ} {W : Array (List ℤ)} (hA : ChainArrays Q O S base W) {chunks : ℕ}
    (hc : 0 < chunks) (h : rawChainOK n O S base W chunks = true) :
    ValidSchreier Q ∧ ∀ i : Fin Q.baseCount,
      Q.orbitSize i = ((rawLevels n S base)[(i : ℕ)]!).pts.size := by
  have hF := chainCheckFacts h
  refine ⟨?_, fun i => hA.orbitSize_eq hF i.2⟩
  rw [validSchreier_iff]
  exact ⟨hA.initial hF, hA.words hF, hA.terminal hF, fun i x tx htx s hs => by
    rw [← RawSchreierDatum.orbitTables_get] at htx ⊢
    simp only [RawSchreierDatum.orbitTables_get] at htx ⊢
    exact hA.schreier hF hc i x tx htx s hs⟩

end CFSG.Certificates
