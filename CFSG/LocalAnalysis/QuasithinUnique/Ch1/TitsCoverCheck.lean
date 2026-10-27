module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverForms
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverWalk
public import CFSG.Sporadic.Schreier.TitsStab
public import CFSG.Sporadic.Schreier.TitsIso

public section

namespace CFSG.QuasithinUnique.Ch1.TitsCover

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

structure Blk where
  gw : List ℤ
  va : List ℕ
  vb : List ℕ
  rhos : List (List (ℕ × Bool))
deriving Inhabited

structure CovData where
  xw0 : List ℤ
  xw1 : List ℤ
  nV : ℕ
  words : Array (List ℕ)
  tgtA : Array ℕ
  backA : Array ℕ
  blocks : List Blk

@[expose] def covText : String := include_str "TitsCoverData.txt"

@[expose] def parseNats (s : String) : List ℕ := (s.splitOn " ").filterMap String.toNat?

@[expose] def parseInts (s : String) : List ℤ := (s.splitOn " ").filterMap String.toInt?

@[expose] def parseWord (s : String) : List ℕ :=
  s.toList.filterMap fun c => if c = '0' then some 0 else if c = '1' then some 1 else none

@[expose] def parseData (txt : String) : CovData := Id.run do
  let L := (txt.splitOn "\n").toArray
  let nV := (L[2]!).toNat!
  let words := (Array.range nV).map fun v => parseWord L[3 + v]!
  let tgtA := (parseNats L[3 + nV]!).toArray
  let backA := (parseNats L[4 + nV]!).toArray
  let nb := (L[5 + nV]!).toNat!
  let mut pos := 6 + nV
  let mut blocks : Array Blk := #[]
  for _ in [0:nb] do
    let gw := parseInts L[pos]!
    let va := parseNats L[pos + 1]!
    let vb := parseNats L[pos + 2]!
    let neq := (L[pos + 3]!).toNat!
    let mut rhos : Array (List (ℕ × Bool)) := #[]
    for k in [0:neq] do
      rhos := rhos.push ((parseNats L[pos + 4 + k]!).map fun m => (m / 2, m % 2 == 0))
    blocks := blocks.push { gw := gw, va := va, vb := vb, rhos := rhos.toList }
    pos := pos + 4 + neq
  return { xw0 := parseInts L[0]!, xw1 := parseInts L[1]!, nV := nV, words := words,
           tgtA := tgtA, backA := backA, blocks := blocks.toList }

@[expose] def covData : CovData := parseData covText


open CFSG.Sporadic.Schreier.Tits (titsT titsD titsDerivedArrs wordIn rep_wordArr_titsT
  wordIn_titsT_mem_titsD)

namespace CovData

variable (d : CovData)

@[expose] def tab : CayTab where
  nV := d.nV
  word v := (d.words[v]!).map fo
  tgt v i := d.tgtA[2 * v + (i : ℕ)]!
  back v i := d.backA[2 * v + (i : ℕ)]!

@[expose] def xwOf (i : Fin 2) : List ℤ := if i.val = 0 then d.xw0 else d.xw1

@[expose] noncomputable def x (i : Fin 2) : Equiv.Perm (Fin 1755) := wordIn 13 titsT (d.xwOf i)

@[expose] def xa (i : Fin 2) : Array ℕ :=
  CFSG.Sporadic.Schreier.Tits.wordArr 1755 titsDerivedArrs (d.xwOf i)

end CovData

@[expose] def elaOf (xa : Fin 2 → Array ℕ) (w : List ℕ) : Array ℕ :=
  w.foldl (fun acc l => compA 1755 acc (xa (fo l))) (idA 1755)

@[expose] def CovData.elaTab (d : CovData) : Array (Array ℕ) :=
  Array.ofFn (n := d.nV) fun v => elaOf d.xa (d.words[v]!)

theorem fo_val (i : Fin 2) : fo (i : ℕ) = i := by
  ext
  simp only [fo]
  exact Nat.mod_eq_of_lt i.2

theorem rep_elaOf {xa : Fin 2 → Array ℕ} {x : Fin 2 → Equiv.Perm (Fin 1755)}
    (hx : ∀ i, Rep 1755 (xa i) (x i)) (w : List ℕ) :
    Rep 1755 (elaOf xa w) ((w.map fun l => x (fo l)).prod) := by
  unfold elaOf
  have key : ∀ (w : List ℕ) (acc : Array ℕ) (g : Equiv.Perm (Fin 1755)), Rep 1755 acc g →
      Rep 1755 (w.foldl (fun acc l => compA 1755 acc (xa (fo l))) acc)
        (g * (w.map fun l => x (fo l)).prod) := by
    intro w
    induction w with
    | nil => intro acc g hg; simpa using hg
    | cons l w ih =>
      intro acc g hg
      have h := ih (compA 1755 acc (xa (fo l))) (g * x (fo l)) (rep_compA hg (hx _))
      simpa [mul_assoc] using h
  simpa using key w (idA 1755) 1 rep_idA

theorem CovData.xa_rep
    (d : CovData) (i : Fin 2) (h : lettersOK 13 (d.xwOf i) = true) :
    Rep 1755 (d.xa i) (d.x i) :=
  rep_wordArr_titsT h

theorem CovData.rep_el (d : CovData) (hx : ∀ i, Rep 1755 (d.xa i) (d.x i)) {v : ℕ}
    (hv : v < d.nV) : Rep 1755 (d.elaTab[v]!) (d.tab.el d.x v) := by
  have h1 : d.elaTab[v]! = elaOf d.xa (d.words[v]!) := by
    unfold CovData.elaTab
    exact CFSG.Sporadic.Schreier.Tits.getElem!_ofFn_of_lt _ hv
  rw [h1]
  have := rep_elaOf hx (d.words[v]!)
  simpa [CayTab.el, CovData.tab, List.map_map, Function.comp_def] using this


@[expose] def goodCheck (d : CovData) (tb : Array (Array ℕ)) : Bool :=
  lettersOK 13 d.xw0 && lettersOK 13 d.xw1 && decide (0 < d.nV) && (d.words[0]! == []) &&
  allLt d.nV (fun v => allLt 2 (fun i =>
    decide (d.tgtA[2 * v + i]! < d.nV) && decide (d.backA[2 * v + i]! < d.nV) &&
    eqA 1755 tb[d.tgtA[2 * v + i]!]! (compA 1755 tb[v]! (d.xa (fo i))) &&
    (d.tgtA[2 * d.backA[2 * v + i]! + i]! == v))) &&
  allLt d.nV (fun u => allLt d.nV (fun v => !decide (u < v) || !eqA 1755 tb[u]! tb[v]!))

theorem goodCheck_sound
    {d : CovData} (h : goodCheck d d.elaTab = true) :
    d.tab.Good d.x ∧ ∀ i, Rep 1755 (d.xa i) (d.x i) := by
  simp only [goodCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hl0, hl1⟩, hnV⟩, hw0⟩, hmain⟩, hinj⟩ := h
  have hx : ∀ i, Rep 1755 (d.xa i) (d.x i) := by
    intro i
    refine d.xa_rep i ?_
    fin_cases i
    · exact hl0
    · exact hl1
  have hrep : ∀ {v : ℕ}, v < d.nV → Rep 1755 (d.elaTab[v]!) (d.tab.el d.x v) :=
    fun hv => d.rep_el hx hv
  have hmain' := fun v (hv : v < d.nV) (i : Fin 2) => (allLt_iff.1 (allLt_iff.1 hmain v hv) i i.2)
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
    have htg : d.tgtA[2 * v + (i : ℕ)]! < d.nV := this.1.1.1
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


@[expose] def blkCheck (d : CovData) (tb : Array (Array ℕ)) (bl : Blk) : Bool :=
  let Ga := CFSG.Sporadic.Schreier.Tits.wordArr 1755 titsDerivedArrs bl.gw
  let Gi := invCand 1755 Ga
  lettersOK 13 bl.gw && isInvA 1755 Ga Gi && (bl.va.length == bl.vb.length) &&
  decide (bl.va.length ≤ 32) &&
  allLt bl.va.length (fun j => decide (bl.va[j]! < d.nV) && decide (bl.vb[j]! < d.nV) &&
    eqA 1755 (compA 1755 (compA 1755 Ga tb[bl.va[j]!]!) Gi) tb[bl.vb[j]!]!)

@[expose] noncomputable def Blk.g (bl : Blk) : Equiv.Perm (Fin 1755) := wordIn 13 titsT bl.gw

theorem Blk.g_mem
    (bl : Blk) : bl.g ∈ titsD := wordIn_titsT_mem_titsD bl.gw

theorem blkCheck_sound
    {d : CovData} (hx : ∀ i, Rep 1755 (d.xa i) (d.x i)) {bl : Blk}
    (h : blkCheck d d.elaTab bl = true) :
    bl.va.length = bl.vb.length ∧ bl.va.length ≤ 32 ∧
      ∀ j < bl.va.length, bl.va[j]! < d.nV ∧ bl.vb[j]! < d.nV ∧
        bl.g * d.tab.el d.x (bl.va[j]!) * bl.g⁻¹ = d.tab.el d.x (bl.vb[j]!) := by
  simp only [blkCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hl, hinv⟩, hlen⟩, h32⟩, hall⟩ := h
  have hGa : Rep 1755 (CFSG.Sporadic.Schreier.Tits.wordArr 1755 titsDerivedArrs bl.gw) bl.g :=
    rep_wordArr_titsT hl
  have hGi : Rep 1755 (invCand 1755 (CFSG.Sporadic.Schreier.Tits.wordArr 1755 titsDerivedArrs
      bl.gw)) bl.g⁻¹ := rep_inv_of_isInvA hGa hinv
  refine ⟨hlen, h32, fun j hj => ?_⟩
  have := allLt_iff.1 hall j hj
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨ha, hb⟩, he⟩ := this
  refine ⟨ha, hb, ?_⟩
  exact eq_of_eqA (rep_compA (rep_compA hGa (d.rep_el hx ha)) hGi) (d.rep_el hx hb) he

inductive Eqn where
  | tree (v : ℕ) (i : Fin 2)
  | trans (w : List Letter) (v₀ v₁ : ℕ)
  | fus (b : ℕ) (ρ : List (ℕ × Bool))

@[expose] def Eqn.form (d : CovData) : Eqn → ℕ
  | .tree v i => 2 ^ (2 * v + (i : ℕ))
  | .trans w v₀ v₁ => formOf (d.tab.walkEdges v₀ w) ^^^ formOf (d.tab.walkEdges v₁ w)
  | .fus b ρ =>
    formOf (d.tab.walkEdges 0 (substW d.tab (fun j => (d.blocks[b]!).va[j]!) ρ)) ^^^
      formOf (d.tab.walkEdges 0 (substW d.tab (fun j => (d.blocks[b]!).vb[j]!) ρ)) ^^^
        formOf (ρ.map fun p => 2 * d.nV + 32 * b + p.1)

@[expose] def Eqn.valid (d : CovData) : Eqn → Bool
  | .tree v i => decide (v < d.nV) && (d.tab.word (d.tab.tgt v i) == d.tab.word v ++ [i])
  | .trans w v₀ v₁ => decide (v₀ < d.nV) && decide (v₁ < d.nV) &&
      (d.tab.walkEnd v₀ w == v₀) && (d.tab.walkEnd v₁ w == v₁)
  | .fus b ρ =>
    decide (b < d.blocks.length) &&
      ρ.all (fun p => decide (p.1 < (d.blocks[b]!).va.length)) &&
      (d.tab.walkEnd 0 (substW d.tab (fun j => (d.blocks[b]!).va[j]!) ρ) == 0) &&
      (d.tab.walkEnd 0 (substW d.tab (fun j => (d.blocks[b]!).vb[j]!) ρ) == 0)

@[expose] def CovData.eqns (d : CovData) : List Eqn :=
  let T := d.tab
  let edges : List (ℕ × Fin 2) :=
    (List.range d.nV).flatMap fun v => (List.finRange 2).map fun i => (v, i)
  let isTree : ℕ × Fin 2 → Bool := fun p => T.word (T.tgt p.1 p.2) == T.word p.1 ++ [p.2]
  (edges.filter isTree).map (fun p => Eqn.tree p.1 p.2) ++
    (edges.filter (fun p => !isTree p)).flatMap (fun p =>
      (List.finRange 2).map fun j => Eqn.trans
        (posW (T.word p.1) ++ [(p.2, true)] ++ invW (T.word (T.tgt p.1 p.2))) 0 (T.tgt 0 j)) ++
    (List.range d.blocks.length).flatMap fun b =>
      ((d.blocks[b]!).rhos).map fun ρ => Eqn.fus b ρ

@[expose] def CovData.M (d : CovData) : ℕ := 2 * d.nV + 32 * d.blocks.length

@[expose] def CovData.forms (d : CovData) : List ℕ := d.eqns.map (Eqn.form d)

@[expose] def geFinal (d : CovData) : Bool :=
  let piv := gePivots (d.M + 5) d.M d.forms
  allLt (2 * d.nV) fun e => reduceF piv (d.M + 5) (2 ^ e) == 0

@[expose] def covCheck (d : CovData) : Bool :=
  let tb := d.elaTab
  goodCheck d tb && d.blocks.all (blkCheck d tb) && d.eqns.all (Eqn.valid d) && geFinal d


@[expose] noncomputable def valOf {E : Type*} [Group E] (d : CovData) (xt : Fin 2 → E)
    (γs : ℕ → ℕ → ZMod 2) (n : ℕ) : ZMod 2 :=
  if n < 2 * d.nV then cE d.tab xt n else
    γs ((n - 2 * d.nV) / 32) ((n - 2 * d.nV) % 32)

theorem valOf_edge {E : Type*} [Group E] (d : CovData) (xt : Fin 2 → E) (γs : ℕ → ℕ → ZMod 2)
    {e : ℕ} (he : e < 2 * d.nV) : valOf d xt γs e = cE d.tab xt e := by
  simp [valOf, he]

theorem valOf_gamma {E : Type*} [Group E] (d : CovData) (xt : Fin 2 → E) (γs : ℕ → ℕ → ZMod 2)
    (b : ℕ) {j : ℕ} (hj : j < 32) : valOf d xt γs (2 * d.nV + 32 * b + j) = γs b j := by
  have h1 : ¬ (2 * d.nV + 32 * b + j < 2 * d.nV) := by omega
  have h2 : (2 * d.nV + 32 * b + j - 2 * d.nV) / 32 = b := by omega
  have h3 : (2 * d.nV + 32 * b + j - 2 * d.nV) % 32 = j := by omega
  simp [valOf, h1, h2, h3]

theorem map_valOf_eq {E : Type*} [Group E] (d : CovData) (xt : Fin 2 → E) (γs : ℕ → ℕ → ZMod 2)
    {es : List ℕ} (hes : ∀ e ∈ es, e < 2 * d.nV) :
    (es.map (valOf d xt γs)).sum = (es.map (cE d.tab xt)).sum := by
  congr 1
  exact List.map_congr_left fun e he => valOf_edge d xt γs (hes e he)

theorem eqn_sound {E : Type*} [Group E] (d : CovData)
    (X : CentralExt E (Equiv.Perm (Fin 1755))) (xt : Fin 2 → E)
    (hT : d.tab.Good d.x) (hxt : ∀ i, X.φ (xt i) = d.x i) {gt : ℕ → E} {γs : ℕ → ℕ → ZMod 2}
    (hγ : ∀ b < d.blocks.length, ∀ j < (d.blocks[b]!).va.length,
      gt b * sig d.tab xt ((d.blocks[b]!).va[j]!) * (gt b)⁻¹ =
        sig d.tab xt ((d.blocks[b]!).vb[j]!) * X.toZ (γs b j))
    (hlen : ∀ b < d.blocks.length, (d.blocks[b]!).va.length ≤ 32)
    (eq : Eqn) (hv : eq.valid d = true) :
    evalForm d.M (valOf d xt γs) (eq.form d) = 0 := by
  have hM : 2 * d.nV ≤ d.M := by unfold CovData.M; omega
  have hnV : d.tab.nV = d.nV := rfl
  cases eq with
  | tree v i =>
    simp only [Eqn.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
    have hi := i.2
    have h2 : 2 * v + (i : ℕ) < 2 * d.nV := by omega
    rw [Eqn.form, evalForm_unit _ (by omega : 2 * v + (i : ℕ) < d.M), valOf_edge d xt γs h2]
    exact tree_sound X xt hT hxt hv.1 i hv.2
  | trans w v₀ v₁ =>
    simp only [Eqn.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
    obtain ⟨⟨⟨h₀, h₁⟩, e₀⟩, e₁⟩ := hv
    have hlt₀ := hT.walkEdges_lt h₀ w
    have hlt₁ := hT.walkEdges_lt h₁ w
    rw [Eqn.form, evalForm_xor, evalForm_formOf _ _ (fun e he => by have := hlt₀ e he; omega),
      evalForm_formOf _ _ (fun e he => by have := hlt₁ e he; omega),
      map_valOf_eq d xt γs hlt₀, map_valOf_eq d xt γs hlt₁,
      trans_sound X xt hT hxt h₀ h₁ e₀ e₁]
    exact CharTwo.add_self_eq_zero _
  | fus b ρ =>
    simp only [Eqn.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hv
    obtain ⟨⟨⟨hb, hρ⟩, hA⟩, hB⟩ := hv
    have hρ' : ∀ p ∈ ρ, p.1 < (d.blocks[b]!).va.length := hρ
    have h0 := hT.zero_lt
    have hltA := hT.walkEdges_lt h0 (substW d.tab (fun j => (d.blocks[b]!).va[j]!) ρ)
    have hltB := hT.walkEdges_lt h0 (substW d.tab (fun j => (d.blocks[b]!).vb[j]!) ρ)
    have hfus := fus_sound X xt hT hxt (hγ b hb) hρ' hA hB
    have hγvar : ∀ e ∈ ρ.map (fun p => 2 * d.nV + 32 * b + p.1), e < d.M := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      have := hρ' p hp
      have := hlen b hb
      unfold CovData.M
      omega
    rw [Eqn.form, evalForm_xor, evalForm_xor,
      evalForm_formOf _ _ (fun e he => by have := hltA e he; omega),
      evalForm_formOf _ _ (fun e he => by have := hltB e he; omega),
      evalForm_formOf _ _ hγvar, map_valOf_eq d xt γs hltA, map_valOf_eq d xt γs hltB, hfus]
    have hg : ((ρ.map fun p => 2 * d.nV + 32 * b + p.1).map (valOf d xt γs)).sum =
        (ρ.map fun p => γs b p.1).sum := by
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun p hp => ?_
      exact valOf_gamma d xt γs b (by have := hρ' p hp; have := hlen b hb; omega)
    rw [hg]
    generalize ((d.tab.walkEdges 0 (substW d.tab (fun j => (d.blocks[b]!).vb[j]!) ρ)).map
      (cE d.tab xt)).sum = sB
    generalize (ρ.map fun p => γs b p.1).sum = sγ
    calc sB + sγ + sB + sγ = (sB + sγ) + (sB + sγ) := by ring
      _ = 0 := CharTwo.add_self_eq_zero _


theorem covCheck_good
    {d : CovData} (hd : covCheck d = true) : d.tab.Good d.x := by
  simp only [covCheck, Bool.and_eq_true] at hd
  exact (goodCheck_sound hd.1.1.1).1

theorem covCheck_vanish
    {E : Type*} [Group E] (d : CovData) (hd : covCheck d = true)
    (X : CentralExt E (Equiv.Perm (Fin 1755))) (xt : Fin 2 → E) (hxt : ∀ i, X.φ (xt i) = d.x i)
    (hlift : ∀ bl ∈ d.blocks, ∃ gt : E, X.φ gt = bl.g) :
    ∀ e < 2 * d.nV, cE d.tab xt e = 0 := by
  classical
  simp only [covCheck, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨hgood, hblk⟩, hvalid⟩, hge⟩ := hd
  obtain ⟨hT, hx⟩ := goodCheck_sound hgood
  have hblk' : ∀ bl ∈ d.blocks, blkCheck d d.elaTab bl = true := List.all_eq_true.1 hblk
  have hvalid' : ∀ eq ∈ d.eqns, eq.valid d = true := List.all_eq_true.1 hvalid
  have hmem : ∀ b < d.blocks.length, d.blocks[b]! ∈ d.blocks := fun b hb => by
    rw [getElem!_pos d.blocks b hb]
    exact List.getElem_mem hb
  have hex : ∀ b : ℕ, ∃ (gt : E) (γ : ℕ → ZMod 2), b < d.blocks.length →
      ∀ j < (d.blocks[b]!).va.length,
        gt * sig d.tab xt ((d.blocks[b]!).va[j]!) * gt⁻¹ =
          sig d.tab xt ((d.blocks[b]!).vb[j]!) * X.toZ (γ j) := by
    intro b
    by_cases hb : b < d.blocks.length
    · obtain ⟨gt, hgt⟩ := hlift _ (hmem b hb)
      obtain ⟨-, -, hrel⟩ := blkCheck_sound hx (hblk' _ (hmem b hb))
      obtain ⟨γ, hγ⟩ := exists_gamma X xt hxt hgt (fun j => (d.blocks[b]!).va[j]!)
        (fun j => (d.blocks[b]!).vb[j]!) (d.blocks[b]!).va.length fun j hj => (hrel j hj).2.2
      exact ⟨gt, γ, fun _ => hγ⟩
    · exact ⟨1, 0, fun h => absurd h hb⟩
  choose gt γs hγ using hex
  have hlen : ∀ b < d.blocks.length, (d.blocks[b]!).va.length ≤ 32 := fun b hb =>
    (blkCheck_sound hx (hblk' _ (hmem b hb))).2.1
  have hform : ∀ f ∈ d.forms, evalForm d.M (valOf d xt γs) f = 0 := by
    intro f hf
    obtain ⟨eq, heq, rfl⟩ := List.mem_map.1 hf
    exact eqn_sound d X xt hT hxt hγ hlen eq (hvalid' eq heq)
  intro e he
  have hred : reduceF (gePivots (d.M + 5) d.M d.forms) (d.M + 5) (2 ^ e) = 0 := by
    simp only [geFinal] at hge
    exact beq_iff_eq.1 (allLt_iff.1 hge e he)
  have h := eq_zero_of_reduce (d.M + 5) hform (e := e) (by unfold CovData.M; omega) hred
  rwa [valOf_edge d xt γs he] at h

end CFSG.QuasithinUnique.Ch1.TitsCover
