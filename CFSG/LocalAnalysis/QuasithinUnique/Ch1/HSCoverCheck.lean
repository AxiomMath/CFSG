module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverForms
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverWalk
public import CFSG.Sporadic.Schreier.PairHSOrder
public import CFSG.Sporadic.Schreier.TitsBasic

public section

namespace CFSG.QuasithinUnique.Ch1.HSCover

open CFSG.Monster.B CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 (rep_compA rep_idA eqA_iff eq_of_eqA allLt_iff rep_inv_of_isInvA)
open CFSG.Sporadic.Schreier (hsGen hsStrongArrs rep_hsGen hsGen_mem hsChain)
open CFSG.Sporadic.Schreier.Tits (getElem!_ofFn_of_lt)
open CFSG.QuasithinUnique.Ch1.TitsCover (evalForm evalForm_zero evalForm_xor evalForm_unit
  evalForm_formOf formOf reduceF gePivots eq_zero_of_reduce)
open CFSG.QuasithinUnique.Ch1.M22Cover

@[expose] def lc (l : ℕ) : ℕ := if l = 0 then 0 else 1

@[expose] noncomputable def gen (l : ℕ) : Equiv.Perm (Fin 3850) := hsGen (lc l)

@[expose] def genArr (l : ℕ) : Array ℕ := hsStrongArrs[lc l]!

theorem lc_lt (l : ℕ) : lc l < 2 := by
  unfold lc
  split_ifs <;> norm_num

theorem rep_genArr (l : ℕ) : Co2.Rep 3850 (genArr l) (gen l) :=
  rep_hsGen (by have := lc_lt l; omega)

theorem gen_mem (l : ℕ) : gen l ∈ CFSG.Sporadic.Schreier.hsChain.originalSubgroup :=
  hsGen_mem (lc l) (lc_lt l)

@[expose] noncomputable def wordP (w : List ℕ) : Equiv.Perm (Fin 3850) := (w.map gen).prod

@[expose] def wordArrP (w : List ℕ) : Array ℕ :=
  w.foldl (fun acc l => compA 3850 acc (genArr l)) (idA 3850)

theorem rep_wordArrP
    (w : List ℕ) : Co2.Rep 3850 (wordArrP w) (wordP w) := by
  unfold wordArrP wordP
  have key : ∀ (w : List ℕ) (acc : Array ℕ) (g : Equiv.Perm (Fin 3850)), Co2.Rep 3850 acc g →
      Co2.Rep 3850 (w.foldl (fun acc l => compA 3850 acc (genArr l)) acc)
        (g * (w.map gen).prod) := by
    intro w
    induction w with
    | nil => intro acc g hg; simpa using hg
    | cons l w ih =>
      intro acc g hg
      have h := ih (compA 3850 acc (genArr l)) (g * gen l)
        (rep_compA hg (rep_genArr l))
      simpa [mul_assoc] using h
  simpa using key w (idA 3850) 1 rep_idA

theorem wordP_mem (w : List ℕ) :
    wordP w ∈ CFSG.Sporadic.Schreier.hsChain.originalSubgroup :=
  Subgroup.list_prod_mem _ fun y hy => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hy
    exact gen_mem l

@[expose] def cWord : List ℕ := [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]

@[expose] noncomputable def cElt : Equiv.Perm (Fin 3850) := wordP cWord

theorem cElt_eq : cElt = (hsGen 0 * hsGen 1 * hsGen 1) ^ 5 := by
  have h0 : gen 0 = hsGen 0 := by simp [gen, lc]
  have h1 : gen 1 = hsGen 1 := by simp [gen, lc]
  simp [cElt, wordP, cWord, h0, h1, pow_succ, mul_assoc]

structure Rec where
  gw : List ℕ
  a : ℕ
  b : ℕ
deriving Inhabited

structure CovData where
  xw0 : List ℕ
  xw1 : List ℕ
  xw2 : List ℕ
  nV : ℕ
  words : Array (List ℕ)
  tgtA : Array ℕ
  backA : Array ℕ
  pairs : List Rec
  anchors : List Rec

@[expose] def covText : String := include_str "HSCoverData.txt"

@[expose] def parseNats (s : String) : List ℕ := (s.splitOn " ").filterMap String.toNat?

@[expose] def parseWord (s : String) : List ℕ :=
  s.toList.filterMap fun c =>
    if c = '0' then some 0 else if c = '1' then some 1 else if c = '2' then some 2 else none

@[expose] def parseData (txt : String) : CovData := Id.run do
  let L := (txt.splitOn "\n").toArray
  let nV := (L[3]!).toNat!
  let words := (Array.range nV).map fun v => parseWord L[4 + v]!
  let tgtA := (parseNats L[4 + nV]!).toArray
  let backA := (parseNats L[5 + nV]!).toArray
  let np := (L[6 + nV]!).toNat!
  let mut pairs : Array Rec := #[]
  let mut pos := 7 + nV
  for _ in [0:np] do
    let ab := parseNats L[pos + 1]!
    pairs := pairs.push { gw := parseNats L[pos]!, a := ab[0]!, b := ab[1]! }
    pos := pos + 2
  let na := (L[pos]!).toNat!
  pos := pos + 1
  let mut anchors : Array Rec := #[]
  for _ in [0:na] do
    anchors := anchors.push { gw := parseNats L[pos]!, a := 0, b := (L[pos + 1]!).toNat! }
    pos := pos + 2
  return { xw0 := parseNats L[0]!, xw1 := parseNats L[1]!, xw2 := parseNats L[2]!, nV := nV,
           words := words, tgtA := tgtA, backA := backA, pairs := pairs.toList,
           anchors := anchors.toList }

@[expose] def covData : CovData := parseData covText

namespace CovData

variable (d : CovData)

@[expose] def tab : CayTab where
  nV := d.nV
  word v := (d.words[v]!).map fo
  tgt v i := d.tgtA[3 * v + (i : ℕ)]!
  back v i := d.backA[3 * v + (i : ℕ)]!

@[expose] def xwOf (i : Fin 3) : List ℕ :=
  if i.val = 0 then d.xw0 else if i.val = 1 then d.xw1 else d.xw2

@[expose] noncomputable def x (i : Fin 3) : Equiv.Perm (Fin 3850) := wordP (d.xwOf i)

@[expose] def xa (i : Fin 3) : Array ℕ := wordArrP (d.xwOf i)

end CovData

@[expose] def elaOf (xa : Fin 3 → Array ℕ) (w : List ℕ) : Array ℕ :=
  w.foldl (fun acc l => compA 3850 acc (xa (fo l))) (idA 3850)

@[expose] def CovData.elaTab (d : CovData) : Array (Array ℕ) :=
  Array.ofFn (n := d.nV) fun v => elaOf d.xa (d.words[v]!)

theorem fo_val (i : Fin 3) : fo (i : ℕ) = i := by
  ext
  simp only [fo]
  exact Nat.mod_eq_of_lt i.2

theorem rep_elaOf {xa : Fin 3 → Array ℕ} {x : Fin 3 → Equiv.Perm (Fin 3850)}
    (hx : ∀ i, Co2.Rep 3850 (xa i) (x i)) (w : List ℕ) :
    Co2.Rep 3850 (elaOf xa w) ((w.map fun l => x (fo l)).prod) := by
  unfold elaOf
  have key : ∀ (w : List ℕ) (acc : Array ℕ) (g : Equiv.Perm (Fin 3850)), Co2.Rep 3850 acc g →
      Co2.Rep 3850 (w.foldl (fun acc l => compA 3850 acc (xa (fo l))) acc)
        (g * (w.map fun l => x (fo l)).prod) := by
    intro w
    induction w with
    | nil => intro acc g hg; simpa using hg
    | cons l w ih =>
      intro acc g hg
      have h := ih (compA 3850 acc (xa (fo l))) (g * x (fo l)) (rep_compA hg (hx _))
      simpa [mul_assoc] using h
  simpa using key w (idA 3850) 1 rep_idA

theorem CovData.xa_rep
    (d : CovData) (i : Fin 3) : Co2.Rep 3850 (d.xa i) (d.x i) :=
  rep_wordArrP _

theorem CovData.rep_el (d : CovData) (hx : ∀ i, Co2.Rep 3850 (d.xa i) (d.x i)) {v : ℕ}
    (hv : v < d.nV) : Co2.Rep 3850 (d.elaTab[v]!) (d.tab.el d.x v) := by
  have h1 : d.elaTab[v]! = elaOf d.xa (d.words[v]!) := by
    unfold CovData.elaTab
    exact getElem!_ofFn_of_lt _ hv
  rw [h1]
  have := rep_elaOf hx (d.words[v]!)
  simpa [CayTab.el, CovData.tab, List.map_map, Function.comp_def] using this

@[expose] def goodCheck (d : CovData) (tb : Array (Array ℕ)) : Bool :=
  decide (0 < d.nV) && (d.words[0]! == []) &&
  allLt d.nV (fun v => allLt 3 (fun i =>
    decide (d.tgtA[3 * v + i]! < d.nV) && decide (d.backA[3 * v + i]! < d.nV) &&
    eqA 3850 tb[d.tgtA[3 * v + i]!]! (compA 3850 tb[v]! (d.xa (fo i))) &&
    (d.tgtA[3 * d.backA[3 * v + i]! + i]! == v))) &&
  allLt d.nV (fun u => allLt d.nV (fun v => !decide (u < v) || !eqA 3850 tb[u]! tb[v]!))

theorem goodCheck_sound
    {d : CovData} (h : goodCheck d d.elaTab = true) :
    d.tab.Good d.x ∧ ∀ i, Co2.Rep 3850 (d.xa i) (d.x i) := by
  simp only [goodCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hnV, hw0⟩, hmain⟩, hinj⟩ := h
  have hx : ∀ i, Co2.Rep 3850 (d.xa i) (d.x i) := fun i => d.xa_rep i
  have hrep : ∀ {v : ℕ}, v < d.nV → Co2.Rep 3850 (d.elaTab[v]!) (d.tab.el d.x v) :=
    fun hv => d.rep_el hx hv
  have hmain' := fun v (hv : v < d.nV) (i : Fin 3) =>
    (allLt_iff.1 (allLt_iff.1 hmain v hv) i i.2)
  refine ⟨⟨?_, hnV, ?_, ?_, ?_, ?_, ?_⟩, hx⟩
  · simp [CovData.tab, hw0]
  · intro v hv i
    have := hmain' v hv i
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this.1.1.1
  · intro v hv i
    have := hmain' v hv i
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this.1.1.2
  · intro v hv i
    have := hmain' v hv i
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    have htg : d.tgtA[3 * v + (i : ℕ)]! < d.nV := this.1.1.1
    have e := eq_of_eqA (hrep htg) (rep_compA (hrep hv) (by rw [fo_val]; exact hx i)) this.1.2
    exact e
  · intro v hv i
    have := hmain' v hv i
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this.2
  · intro u hu v hv huv
    rcases lt_trichotomy u v with h | h | h
    · have := allLt_iff.1 (allLt_iff.1 hinj u hu) v hv
      simp only [h, decide_true, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at this
      have := (eqA_iff (hrep hu) (hrep hv)).2 huv
      simp_all
    · exact h
    · have := allLt_iff.1 (allLt_iff.1 hinj v hv) u hu
      simp only [h, decide_true, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at this
      have := (eqA_iff (hrep hv) (hrep hu)).2 huv.symm
      simp_all

@[expose] noncomputable def Rec.g (r : Rec) : Equiv.Perm (Fin 3850) := (wordP r.gw)⁻¹

theorem Rec.g_mem (r : Rec) : r.g ∈ CFSG.Sporadic.Schreier.hsChain.originalSubgroup :=
  Subgroup.inv_mem _ (wordP_mem r.gw)

@[expose] def pairCheck (d : CovData) (tb : Array (Array ℕ)) (r : Rec) : Bool :=
  let Ga := wordArrP r.gw
  let Gi := invCand 3850 Ga
  isInvA 3850 Ga Gi && decide (r.a < d.nV) && decide (r.b < d.nV) &&
    eqA 3850 (compA 3850 (compA 3850 Gi tb[r.a]!) Ga) tb[r.b]!

@[expose] def anchorCheck (d : CovData) (tb : Array (Array ℕ)) (r : Rec) : Bool :=
  let Ga := wordArrP r.gw
  let Gi := invCand 3850 Ga
  isInvA 3850 Ga Gi && decide (r.b < d.nV) &&
    eqA 3850 (compA 3850 (compA 3850 Gi (wordArrP cWord)) Ga) tb[r.b]!

theorem pairCheck_sound
    {d : CovData} (hx : ∀ i, Co2.Rep 3850 (d.xa i) (d.x i)) {r : Rec}
    (h : pairCheck d d.elaTab r = true) :
    r.a < d.nV ∧ r.b < d.nV ∧ r.g * d.tab.el d.x r.a * r.g⁻¹ = d.tab.el d.x r.b := by
  simp only [pairCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hinv, ha⟩, hb⟩, he⟩ := h
  have hGa : Co2.Rep 3850 (wordArrP r.gw) (wordP r.gw) := rep_wordArrP r.gw
  have hGi : Co2.Rep 3850 (invCand 3850 (wordArrP r.gw)) (wordP r.gw)⁻¹ :=
    rep_inv_of_isInvA hGa hinv
  refine ⟨ha, hb, ?_⟩
  have e := eq_of_eqA (rep_compA (rep_compA hGi (d.rep_el hx ha)) hGa) (d.rep_el hx hb) he
  show (wordP r.gw)⁻¹ * d.tab.el d.x r.a * ((wordP r.gw)⁻¹)⁻¹ = _
  rw [inv_inv]
  exact e

theorem anchorCheck_sound
    {d : CovData} (hx : ∀ i, Co2.Rep 3850 (d.xa i) (d.x i)) {r : Rec}
    (h : anchorCheck d d.elaTab r = true) :
    r.b < d.nV ∧ r.g * cElt * r.g⁻¹ = d.tab.el d.x r.b := by
  simp only [anchorCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hinv, hb⟩, he⟩ := h
  have hGa : Co2.Rep 3850 (wordArrP r.gw) (wordP r.gw) := rep_wordArrP r.gw
  have hGi : Co2.Rep 3850 (invCand 3850 (wordArrP r.gw)) (wordP r.gw)⁻¹ :=
    rep_inv_of_isInvA hGa hinv
  refine ⟨hb, ?_⟩
  have e := eq_of_eqA (rep_compA (rep_compA hGi (rep_wordArrP cWord)) hGa) (d.rep_el hx hb) he
  show (wordP r.gw)⁻¹ * cElt * ((wordP r.gw)⁻¹)⁻¹ = _
  rw [inv_inv]
  exact e

inductive Eqn where
  | tree (v : ℕ) (i : Fin 3)
  | trans (w : List Letter) (v₀ v₁ : ℕ)
  | eqv (a b : ℕ)
  | zero (b : ℕ)

@[expose] def sqEdgesOf (T : CayTab) (v : ℕ) : List ℕ := T.walkEdges v (posW (T.word v))

@[expose] def Eqn.form (d : CovData) : Eqn → ℕ
  | .tree v i => 2 ^ (3 * v + (i : ℕ))
  | .trans w v₀ v₁ => formOf (d.tab.walkEdges v₀ w) ^^^ formOf (d.tab.walkEdges v₁ w)
  | .eqv a b => formOf (sqEdgesOf d.tab a) ^^^ formOf (sqEdgesOf d.tab b)
  | .zero b => formOf (sqEdgesOf d.tab b)

@[expose] def Eqn.valid (d : CovData) : Eqn → Bool
  | .tree v i => decide (v < d.nV) && (d.tab.word (d.tab.tgt v i) == d.tab.word v ++ [i])
  | .trans w v₀ v₁ => decide (v₀ < d.nV) && decide (v₁ < d.nV) &&
      (d.tab.walkEnd v₀ w == v₀) && (d.tab.walkEnd v₁ w == v₁)
  | .eqv a b => decide (a < d.nV) && decide (b < d.nV) &&
      (d.tab.walkEnd a (posW (d.tab.word a)) == 0) &&
      (d.tab.walkEnd b (posW (d.tab.word b)) == 0) &&
      d.pairs.any (fun r => r.a == a && r.b == b)
  | .zero b => decide (b < d.nV) && (d.tab.walkEnd b (posW (d.tab.word b)) == 0) &&
      d.anchors.any (fun r => r.b == b)

@[expose] def CovData.eqns (d : CovData) : List Eqn :=
  let T := d.tab
  let edges : List (ℕ × Fin 3) :=
    (List.range d.nV).flatMap fun v => (List.finRange 3).map fun i => (v, i)
  let isTree : ℕ × Fin 3 → Bool := fun p => T.word (T.tgt p.1 p.2) == T.word p.1 ++ [p.2]
  (edges.filter isTree).map (fun p => Eqn.tree p.1 p.2) ++
    (edges.filter (fun p => !isTree p)).flatMap (fun p =>
      (List.finRange 3).map fun j => Eqn.trans
        (posW (T.word p.1) ++ [(p.2, true)] ++ invW (T.word (T.tgt p.1 p.2))) 0 (T.tgt 0 j)) ++
    d.pairs.map (fun r => Eqn.eqv r.a r.b) ++ d.anchors.map (fun r => Eqn.zero r.b)

@[expose] def CovData.M (d : CovData) : ℕ := 3 * d.nV

@[expose] def CovData.forms (d : CovData) : List ℕ := d.eqns.map (Eqn.form d)

@[expose] def geFinal (d : CovData) : Bool :=
  let piv := gePivots (d.M + 5) d.M d.forms
  allLt d.M fun e => reduceF piv (d.M + 5) (2 ^ e) == 0

@[expose] def covCheck (d : CovData) : Bool :=
  let tb := d.elaTab
  goodCheck d tb && d.pairs.all (pairCheck d tb) && d.anchors.all (anchorCheck d tb) &&
    d.eqns.all (Eqn.valid d) && geFinal d

section Squares

variable {E G : Type*} [Group E] [Group G] (X : CentralExt E G)

theorem sq_eq_one_of_conj {u gt s : E} (hu : u * u = 1) (h : X.φ (gt * u * gt⁻¹) = X.φ s) :
    s * s = 1 := by
  have h1 : X.φ (s⁻¹ * (gt * u * gt⁻¹)) = 1 := by rw [map_mul, map_inv, h]; group
  obtain ⟨z, hz⟩ := X.exists_toZ h1
  have h2 : gt * u * gt⁻¹ = s * X.toZ z := by
    calc gt * u * gt⁻¹ = s * (s⁻¹ * (gt * u * gt⁻¹)) := by group
      _ = s * X.toZ z := by rw [hz]
  have h3 : (gt * u * gt⁻¹) * (gt * u * gt⁻¹) = 1 := by
    calc (gt * u * gt⁻¹) * (gt * u * gt⁻¹) = gt * (u * u) * gt⁻¹ := by group
      _ = 1 := by rw [hu]; group
  rw [h2] at h3
  have hzz : X.toZ z * X.toZ z = 1 := by
    rw [← X.toZ_add, CharTwo.add_self_eq_zero, X.toZ_zero]
  calc s * s = s * (X.toZ z * X.toZ z) * s := by rw [hzz, mul_one]
    _ = (s * X.toZ z) * (s * X.toZ z) := by
        calc s * (X.toZ z * X.toZ z) * s = s * X.toZ z * (X.toZ z * s) := by group
          _ = s * X.toZ z * (s * X.toZ z) := by rw [X.toZ_central]
    _ = 1 := h3

theorem sq_eq_of_conj {gt s s' : E} {z : ZMod 2} (hs : X.φ (s * s) = 1)
    (h : gt * s * gt⁻¹ = s' * X.toZ z) : s * s = s' * s' := by
  obtain ⟨a, ha⟩ := X.exists_toZ hs
  have hc : gt * (s * s) * gt⁻¹ = s * s := by
    rw [ha]
    have := X.toZ_central a gt
    calc gt * X.toZ a * gt⁻¹ = X.toZ a * gt * gt⁻¹ := by rw [← this]
      _ = X.toZ a := by group
  have hzz : X.toZ z * X.toZ z = 1 := by
    rw [← X.toZ_add, CharTwo.add_self_eq_zero, X.toZ_zero]
  calc s * s = gt * (s * s) * gt⁻¹ := hc.symm
    _ = (gt * s * gt⁻¹) * (gt * s * gt⁻¹) := by group
    _ = (s' * X.toZ z) * (s' * X.toZ z) := by rw [h]
    _ = s' * s' * (X.toZ z * X.toZ z) := by
        calc (s' * X.toZ z) * (s' * X.toZ z) = s' * (X.toZ z * s') * X.toZ z := by group
          _ = s' * (s' * X.toZ z) * X.toZ z := by rw [X.toZ_central z s']
          _ = s' * s' * (X.toZ z * X.toZ z) := by group
    _ = s' * s' := by rw [hzz, mul_one]

theorem sq_sig {T : CayTab} {x : Fin 3 → G} (xt : Fin 3 → E) (hT : T.Good x)
    (hxt : ∀ i, X.φ (xt i) = x i) {v : ℕ} (hv : v < T.nV)
    (hend : T.walkEnd v (posW (T.word v)) = 0) :
    sig T xt v * sig T xt v = X.toZ (((sqEdgesOf T v).map (cE T xt)).sum) := by
  have h := telescope X xt hT hxt hv (posW (T.word v))
  rw [psi_posW, hend] at h
  have h0 : sig T xt 0 = 1 := by simp [sig, hT.word_zero]
  rw [h0, one_mul] at h
  exact h

theorem phi_sq_sig {T : CayTab} {x : Fin 3 → G} (xt : Fin 3 → E) (hT : T.Good x)
    (hxt : ∀ i, X.φ (xt i) = x i) {v : ℕ} (hv : v < T.nV)
    (hend : T.walkEnd v (posW (T.word v)) = 0) : X.φ (sig T xt v * sig T xt v) = 1 := by
  rw [sq_sig X xt hT hxt hv hend]
  rcases zmod_two_cases (((sqEdgesOf T v).map (cE T xt)).sum) with h | h <;> rw [h]
  · rw [X.toZ_zero, map_one]
  · rw [X.toZ_one]
    exact X.φ_ζ

end Squares

theorem eqn_sound {E : Type*} [Group E] (d : CovData)
    (X : CentralExt E (Equiv.Perm (Fin 3850))) (xt : Fin 3 → E)
    (hT : d.tab.Good d.x) (hxt : ∀ i, X.φ (xt i) = d.x i)
    (hpair : ∀ r ∈ d.pairs, sig d.tab xt r.a * sig d.tab xt r.a =
      sig d.tab xt r.b * sig d.tab xt r.b)
    (hanch : ∀ r ∈ d.anchors, sig d.tab xt r.b * sig d.tab xt r.b = 1)
    (eq : Eqn) (hv : eq.valid d = true) :
    evalForm d.M (cE d.tab xt) (eq.form d) = 0 := by
  have hnV : d.tab.nV = d.nV := rfl
  have hlt : ∀ (v : ℕ), v < d.nV → ∀ e ∈ sqEdgesOf d.tab v, e < d.M := by
    intro v hv e he
    have := hT.walkEdges_lt (v := v) hv (posW (d.tab.word v)) e he
    unfold CovData.M
    omega
  cases eq with
  | tree v i =>
    simp only [Eqn.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
    have hi := i.2
    have h2 : 3 * v + (i : ℕ) < d.M := by unfold CovData.M; omega
    rw [Eqn.form, evalForm_unit _ h2]
    exact tree_sound X xt hT hxt hv.1 i hv.2
  | trans w v₀ v₁ =>
    simp only [Eqn.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
    obtain ⟨⟨⟨h₀, h₁⟩, e₀⟩, e₁⟩ := hv
    have hlt₀ := hT.walkEdges_lt h₀ w
    have hlt₁ := hT.walkEdges_lt h₁ w
    rw [Eqn.form, evalForm_xor,
      evalForm_formOf _ _ (fun e he => by have := hlt₀ e he; unfold CovData.M; omega),
      evalForm_formOf _ _ (fun e he => by have := hlt₁ e he; unfold CovData.M; omega),
      trans_sound X xt hT hxt h₀ h₁ e₀ e₁]
    exact CharTwo.add_self_eq_zero _
  | eqv a b =>
    simp only [Eqn.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.any_eq_true] at hv
    obtain ⟨⟨⟨⟨ha, hb⟩, hea⟩, heb⟩, r, hr, rfl, rfl⟩ := hv
    have hsa := sq_sig X xt hT hxt ha hea
    have hsb := sq_sig X xt hT hxt hb heb
    have hsq := hpair r hr
    rw [hsa, hsb] at hsq
    have hsum := X.toZ_inj hsq
    rw [Eqn.form, evalForm_xor, evalForm_formOf _ _ (hlt _ ha), evalForm_formOf _ _ (hlt _ hb),
      hsum]
    exact CharTwo.add_self_eq_zero _
  | zero b =>
    simp only [Eqn.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.any_eq_true] at hv
    obtain ⟨⟨hb, heb⟩, r, hr, rfl⟩ := hv
    have hsb := sq_sig X xt hT hxt hb heb
    have hsq := hanch r hr
    rw [hsb, ← X.toZ_zero] at hsq
    rw [Eqn.form, evalForm_formOf _ _ (hlt _ hb)]
    exact X.toZ_inj hsq

theorem covCheck_good
    {d : CovData} (hd : covCheck d = true) : d.tab.Good d.x := by
  simp only [covCheck, Bool.and_eq_true] at hd
  exact (goodCheck_sound hd.1.1.1.1).1

theorem eqv_mem {d : CovData} {r : Rec} (hr : r ∈ d.pairs) : Eqn.eqv r.a r.b ∈ d.eqns := by
  unfold CovData.eqns
  simp only [List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨r, hr, rfl⟩)

theorem zero_mem {d : CovData} {r : Rec} (hr : r ∈ d.anchors) : Eqn.zero r.b ∈ d.eqns := by
  unfold CovData.eqns
  simp only [List.mem_append, List.mem_map]
  exact Or.inr ⟨r, hr, rfl⟩

theorem covCheck_vanish
    {E : Type*} [Group E] (d : CovData) (hd : covCheck d = true)
    (X : CentralExt E (Equiv.Perm (Fin 3850))) (xt : Fin 3 → E) (hxt : ∀ i, X.φ (xt i) = d.x i)
    (hlift : ∀ r ∈ d.pairs ++ d.anchors, ∃ gt : E, X.φ gt = r.g)
    (u : E) (hu : u * u = 1) (huc : X.φ u = cElt) :
    ∀ e < 3 * d.nV, cE d.tab xt e = 0 := by
  classical
  simp only [covCheck, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨hgood, hpairs⟩, hanchors⟩, hvalid⟩, hge⟩ := hd
  obtain ⟨hT, hx⟩ := goodCheck_sound hgood
  have hpairs' : ∀ r ∈ d.pairs, pairCheck d d.elaTab r = true := List.all_eq_true.1 hpairs
  have hanchors' : ∀ r ∈ d.anchors, anchorCheck d d.elaTab r = true :=
    List.all_eq_true.1 hanchors
  have hvalid' : ∀ eq ∈ d.eqns, eq.valid d = true := List.all_eq_true.1 hvalid
  have hpair : ∀ r ∈ d.pairs, sig d.tab xt r.a * sig d.tab xt r.a =
      sig d.tab xt r.b * sig d.tab xt r.b := by
    intro r hr
    have hv := hvalid' _ (eqv_mem hr)
    simp only [Eqn.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
    obtain ⟨⟨⟨⟨ha, -⟩, hea⟩, -⟩, -⟩ := hv
    obtain ⟨-, -, hrel⟩ := pairCheck_sound hx (hpairs' r hr)
    obtain ⟨gt, hgt⟩ := hlift r (List.mem_append_left _ hr)
    obtain ⟨γ, hγ⟩ := exists_gamma X xt hxt hgt (fun _ => r.a) (fun _ => r.b) 1
      (fun _ _ => hrel)
    exact sq_eq_of_conj X (phi_sq_sig X xt hT hxt ha hea) (hγ 0 (by norm_num))
  have hanch : ∀ r ∈ d.anchors, sig d.tab xt r.b * sig d.tab xt r.b = 1 := by
    intro r hr
    obtain ⟨-, hrel⟩ := anchorCheck_sound hx (hanchors' r hr)
    obtain ⟨gt, hgt⟩ := hlift r (List.mem_append_right _ hr)
    refine sq_eq_one_of_conj X (gt := gt) hu ?_
    rw [map_mul, map_mul, map_inv, hgt, huc, phi_sig X xt hxt]
    exact hrel
  have hform : ∀ f ∈ d.forms, evalForm d.M (cE d.tab xt) f = 0 := by
    intro f hf
    obtain ⟨eq, heq, rfl⟩ := List.mem_map.1 hf
    exact eqn_sound d X xt hT hxt hpair hanch eq (hvalid' eq heq)
  intro e he
  have he' : e < d.M := he
  have hred : reduceF (gePivots (d.M + 5) d.M d.forms) (d.M + 5) (2 ^ e) = 0 := by
    simp only [geFinal] at hge
    exact beq_iff_eq.1 (allLt_iff.1 hge e he')
  exact eq_zero_of_reduce (d.M + 5) hform he' hred

end CFSG.QuasithinUnique.Ch1.HSCover
