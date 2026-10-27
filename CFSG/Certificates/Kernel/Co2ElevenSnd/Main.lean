module

public import CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenInputs
public import Certificates.Data.Kernel.Co2Eleven
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.Co2ElevenSnd.Pack
import CFSG.Certificates.Kernel.Co2ElevenSnd.Letters
import CFSG.Certificates.Kernel.Co2ElevenSnd.Level
import CFSG.Certificates.Kernel.Co2ElevenSnd.Sift
import CFSG.Certificates.Kernel.Spor.PK.NatChain
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.KC.Co2Eleven.Snd

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenNative
  CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenNative CFSG.KS.PK CFSG.KS.TW CFSG.KC.Co2Eleven

private theorem elevenK_facts {A B : Nat} {WV WVI R : Nat → Nat} {ws : List (List Int)}
    {is ih : Nat} {chain : List Nat} {m e bound : Nat} {szs : List Nat}
    (h : elevenK A B WV WVI R ws is ih chain m e bound szs = true) :
    lettersK A B WV WVI ws = true ∧ levelsK WV WVI R chain is ih m szs = true ∧
      countK WV WVI R chain is ih m bound szs = true ∧ miscK WV ws chain is ih m e szs = true := by
  unfold elevenK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

private theorem miscK_facts {WV : Nat → Nat} {ws : List (List Int)} {chain : List Nat}
    {is ih m e : Nat} {szs : List Nat} (h : miscK WV ws chain is ih m e szs = true) :
    is < ws.length ∧ ih < ws.length ∧ (∀ j ∈ chain, j < ws.length) ∧ 0 < m ∧
      CFSG.KS.ppow 2300 12 (CFSG.KS.mask 12) (CFSG.KC.Enum.pidn 2300 12) (WV is) e =
        CFSG.KC.Enum.pidn 2300 12 ∧
      WV is ≠ CFSG.KC.Enum.pidn 2300 12 ∧ szs.foldl (· * ·) 1 = 42305421312000 := by
  unfold miscK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h6, Nat.ne_of_beq_eq_false h7, h8⟩

private theorem levelsK_facts {WV WVI R : Nat → Nat} {chain : List Nat} {is ih m : Nat}
    {szs : List Nat} (h : levelsK WV WVI R chain is ih m szs = true) :
    szs.length = m ∧ ∀ i < m, levelK (chainLet WV WVI chain) (2 * chain.length)
      (baseK WV is ih m) R i (szs.getD i 0) = true := by
  unfold levelsK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact h

private theorem countK_le {WV WVI R : Nat → Nat} {chain : List Nat} {is ih m bound : Nat}
    {szs : List Nat} (h : countK WV WVI R chain is ih m bound szs = true) :
    ((List.range 2300).filter fun p => siftL (chainLet WV WVI chain) R (baseK WV is ih m) szs
      (List.range m) (tupK (WV is) m p)).length ≤ bound := by
  unfold countK at h
  exact of_decide_eq_true h

private theorem memK_iff (a : Nat) : ∀ l : List Nat, memK a l = true ↔ a ∈ l
  | [] => by simp [memK]
  | b :: l => by
    rw [memK, Bool.or_eq_true, Nat.beq_eq, memK_iff a l, List.mem_cons]

private theorem nodup_of_nodupK : ∀ {l : List Nat}, nodupK l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [nodupK, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_of_nodupK h.2⟩
    have h1 := (memK_iff a l).2 hm
    rw [h.1] at h1
    exact Bool.false_ne_true h1

private theorem centK_facts {WV : Nat → Nat} {ws : List (List Int)} {ids : List Nat}
    {is ih e : Nat} (h : centK WV ws ids is ih e = true) :
    (∀ j ∈ ids, j < ws.length ∧
      CFSG.KC.Enum.pcomp 2300 12 (CFSG.KS.mask 12) (WV j) (WV is) =
        CFSG.KC.Enum.pcomp 2300 12 (CFSG.KS.mask 12) (WV is) (WV j)) ∧
      (centPts WV ids is ih e).Nodup := by
  unfold centK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Nat.beq_eq] at h
  exact ⟨h.1, nodup_of_nodupK h.2⟩

private theorem arr_getD (a : Array Nat) (i : Nat) : a[i]! = a.toList.getD i 0 := by
  rw [← Array.getElem!_toList, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

private theorem getD_mem {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

private theorem foldl_mul_congr {f g : Nat → Nat} : ∀ (l : List Nat) (a : Nat),
    (∀ i ∈ l, f i = g i) →
      l.foldl (fun acc i => acc * f i) a = l.foldl (fun acc i => acc * g i) a
  | [], _, _ => rfl
  | x :: l, a, h => by
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self]
    exact foldl_mul_congr l _ fun i hi => h i (List.mem_cons_of_mem x hi)

private theorem foldl_range_getD (l : List Nat) :
    (List.range l.length).foldl (fun acc i => acc * l.getD i 0) 1 = l.foldl (· * ·) 1 := by
  have e : (List.range l.length).map (fun i => l.getD i 0) = l := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp [List.getD_eq_getElem?_getD, h2]
  have h := congrArg (fun l' => l'.foldl (· * ·) 1) e
  simp only [List.foldl_map] at h
  exact h

private theorem compT_TR' {P Q : Table} {f g : Nat → Nat} (hP : TR 2300 P f)
    (hQ : TR 2300 Q g) : TR 2300 (compT 2300 P Q) fun x => f (g x) := by
  refine ⟨by simp [compT], fun i hi => ?_⟩
  obtain ⟨hq1, hq2⟩ := hQ.2 i hi
  obtain ⟨hp1, hp2⟩ := hP.2 _ hq2
  refine ⟨?_, hp2⟩
  unfold ap compT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have e : (Q[i]!).toNat = g i := hq1
  rw [e]
  exact hp1

private theorem powT_TR' {P : Table} {f : Nat → Nat} (hP : TR 2300 P f) (e : Nat) :
    TR 2300 (powT 2300 e P) (itr f e) := by
  induction e with
  | zero => exact idT_TR (by decide)
  | succ e ih => exact compT_TR' (f := f) (g := itr f e) hP ih

private theorem itr_iterK (y : Nat) : ∀ k x, itr (ap12 y) k x = iterK y k x
  | 0, _ => rfl
  | k + 1, x => by
    show ap12 y (itr (ap12 y) k x) = ap12 y (iterK y k x)
    rw [itr_iterK y k x]

private theorem tup_eq {Y : Table} {y : Nat} (hY : TR 2300 Y (ap12 y)) (m : Nat) {p : Nat}
    (hp : p < 2300) :
    (tupleOf Y m p).toList = tupK y m p ∧ ∀ x ∈ (tupleOf Y m p).toList, x < 2300 := by
  have e : (tupleOf Y m p).toList = tupK y m p := by
    unfold tupleOf tupK
    rw [Array.toList_map, Array.toList_range]
    exact List.map_congr_left fun i _ => (iterAp_eq hY i hp).1
  refine ⟨e, ?_⟩
  rw [e]
  intro x hx
  unfold tupK at hx
  rw [List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact (iterAp_eq hY i hp).2

private theorem trees_get {LC : Array Table} {base : Array Nat} {i : Nat} (hi : i < base.size) :
    (chainTrees 2300 LC base)[i]! = treeBFS 2300 base[i]! LC (levelLetters LC base i) := by
  unfold chainTrees
  rw [getElem!_pos _ i (by simpa using hi)]
  simp only [Array.getElem_ofFn]

private theorem lev_eq {LC : Array Table} {LCf : Nat → Nat} {NL : Nat} {base : Array Nat}
    (hLs : LC.size = NL) (hTR : ∀ l < NL, TR 2300 LC[l]! (ap12 (LCf l)))
    (hb : ∀ b ∈ base.toList, b < 2300) (i : Nat) :
    levelLetters LC base i = (lvK LCf NL base.toList i).toArray := by
  apply Array.toList_inj.1
  rw [levelLetters_eq, hLs, lvAt_congr (F := tabF LC) (G := fun l x => ap12 (LCf l) x)
    (by decide) hb (fun l hl x hx => ((hTR l hl).2 x hx).1), ← lvK_eq LCf NL base.toList i,
    List.toList_toArray]

private theorem tree_eq {LC : Array Table} {LCf : Nat → Nat} {NL : Nat} {base : Array Nat}
    {i : Nat} (hLs : LC.size = NL) (hTR : ∀ l < NL, TR 2300 LC[l]! (ap12 (LCf l)))
    (hb : ∀ b ∈ base.toList, b < 2300) (hi : i < base.size) :
    (chainTrees 2300 LC base)[i]! =
      treeOf 2300 (BS.run (tabF LC) (lvK LCf NL base.toList i) 2300 (base.toList.getD i 0)) := by
  have hr : base.toList.getD i 0 < 2300 := hb _ (getD_mem (by simpa using hi))
  have hF : ∀ l ∈ (lvK LCf NL base.toList i).toArray.toList, ∀ x < 2300, tabF LC l x < 2300 := by
    intro l hl x hx
    have hl' : l ∈ lvK LCf NL base.toList i := by simpa using hl
    have h' := (hTR l (lvK_lt l hl')).2 x hx
    show ap LC[l]! x < 2300
    rw [h'.1]
    exact h'.2
  rw [trees_get hi, lev_eq hLs hTR hb i, arr_getD base i, treeBFS_eq (by decide) hr hF,
    List.toList_toArray]

private theorem basics {words : Array (List Int)} {is ih : Nat} {chain : List Nat}
    {m e bound A B : Nat} {WV WVI R : Nat → Nat} {szs : List Nat} {L : Array Table} {Y : Table}
    {ω : Nat} (eL : L = slpLetters 2300 (co2Gens (co2T 0) (co2T 1)) words) (eY : Y = L[2 * is]!)
    (eω : ω = ap L[2 * ih]! 0)
    (hA : co2T 0 = (CFSG.KS.Raw.unpack 2300 12 A).map UInt32.ofNat)
    (hB : co2T 1 = (CFSG.KS.Raw.unpack 2300 12 B).map UInt32.ofNat)
    (hs : slpOK words = true)
    (h : elevenK A B WV WVI R words.toList is ih chain m e bound szs = true) :
    L.size = 2 * words.size ∧ (∀ l < 2 * words.size, TR 2300 L[l]! (ap12 (wordLet WV WVI l))) ∧
      TR 2300 Y (ap12 (WV is)) ∧ ω = ap12 (WV ih) 0 ∧ ω < 2300 := by
  obtain ⟨hlet, -, -, hmisc⟩ := elevenK_facts h
  obtain ⟨pA, pB, -⟩ := lettersK_facts hlet
  obtain ⟨m1, m2, -⟩ := miscK_facts hmisc
  have h0 : TR 2300 (co2T 0) (ap12 A) := by
    rw [hA]
    exact tr_unpack fun x hx => ((perm12_facts pA).2.2 x hx).1
  have h1 : TR 2300 (co2T 1) (ap12 B) := by
    rw [hB]
    exact tr_unpack fun x hx => ((perm12_facts pB).2.2 x hx).1
  obtain ⟨hLs, hL⟩ := slpLetters_TR (WV := WV) (WVI := WVI) h0 h1 hs hlet
  rw [← eL] at hLs hL
  have hlen : words.toList.length = words.size := Array.length_toList
  have hY := hL (2 * is) (by omega)
  rw [wordLet_even, ← eY] at hY
  have hW := hL (2 * ih) (by omega)
  rw [wordLet_even] at hW
  have hω : ω = ap12 (WV ih) 0 := by
    rw [eω]
    exact (hW.2 0 (by decide)).1
  refine ⟨hLs, hL, hY, hω, ?_⟩
  rw [hω]
  exact (hW.2 0 (by decide)).2

private theorem common {words : Array (List Int)} {is ih : Nat} {chain : Array Nat}
    {m e bound A B : Nat} {WV WVI R : Nat → Nat} {szs : List Nat} {L : Array Table} {Y : Table}
    {ω : Nat} {base : Array Nat} {LC : Array Table} {trees : Array Tree}
    (eL : L = slpLetters 2300 (co2Gens (co2T 0) (co2T 1)) words) (eY : Y = L[2 * is]!)
    (eω : ω = ap L[2 * ih]! 0) (eb : base = (Array.range m).map fun i => iterAp Y i ω)
    (eLC : LC = subLetters L chain) (et : trees = chainTrees 2300 LC base)
    (hA : co2T 0 = (CFSG.KS.Raw.unpack 2300 12 A).map UInt32.ofNat)
    (hB : co2T 1 = (CFSG.KS.Raw.unpack 2300 12 B).map UInt32.ofNat)
    (hs : slpOK words = true)
    (h : elevenK A B WV WVI R words.toList is ih chain.toList m e bound szs = true) :
    invOK 2300 (co2T 0) (invT 2300 (co2T 0)) = true ∧
      invOK 2300 (co2T 1) (invT 2300 (co2T 1)) = true ∧ is < words.size ∧ ih < words.size ∧
      (List.range words.size).all (fun j => invOK 2300 L[2 * j]! L[2 * j + 1]!) = true ∧
      chain.all (fun j => decide (j < words.size)) = true ∧ ω < 2300 ∧ 0 < m ∧
      eqTab2 (powT 2300 e Y) (idT 2300) = true ∧ (!(eqTab2 Y (idT 2300))) = true ∧
      (List.range m).all (fun i => CFSG.Perm.Native.treeOK 2300 base[i]! trees[i]! LC
        (levelLetters LC base i)) = true ∧
      (List.range m).foldl (fun acc i => acc * trees[i]!.pts.size) 1 = cardCo2 () ∧
      Nat.count (fun p => sift trees LC (Array.range m) base 0 (tupleOf Y m p) = true) 2300 ≤
        bound := by
  obtain ⟨hlet, hlev, hcnt, hmisc⟩ := elevenK_facts h
  obtain ⟨pA, pB, pW⟩ := lettersK_facts hlet
  obtain ⟨m1, m2, m3, m4, m6, m7, m8⟩ := miscK_facts hmisc
  obtain ⟨hszl, hlv⟩ := levelsK_facts hlev
  obtain ⟨-, hL, hY, hω, hω'⟩ := basics eL eY eω hA hB hs h
  have hlen : words.toList.length = words.size := Array.length_toList
  have hcs : chain.toList.length = chain.size := Array.length_toList
  have h0 : TR 2300 (co2T 0) (ap12 A) := by
    rw [hA]
    exact tr_unpack fun x hx => ((perm12_facts pA).2.2 x hx).1
  have h1 : TR 2300 (co2T 1) (ap12 B) := by
    rw [hB]
    exact tr_unpack fun x hx => ((perm12_facts pB).2.2 x hx).1
  have hI : TR 2300 (idT 2300) fun i => i := idT_TR (by decide)
  have hcl : ∀ c ∈ chain.toList, c < words.size := fun c hc => by
    have := m3 c hc
    omega
  obtain ⟨hLCs, hLC⟩ := subLetters_TR (WV := WV) (WVI := WVI) hL hcl
  rw [← eLC] at hLCs hLC
  have hLCs' : LC.size = 2 * chain.toList.length := by rw [hLCs, hcs]
  have hLC' : ∀ l < 2 * chain.toList.length,
      TR 2300 LC[l]! (ap12 (chainLet WV WVI chain.toList l)) := fun l hl => hLC l (by omega)
  have hbt := tup_eq hY m hω'
  have hbase : base.toList = baseK WV is ih m := by
    have e1 : tupK (WV is) m (ap12 (WV ih) 0) = baseK WV is ih m := rfl
    rw [eb]
    show (tupleOf Y m ω).toList = _
    rw [hbt.1, hω, e1]
  have hb : ∀ b ∈ base.toList, b < 2300 := by
    rw [eb]
    exact hbt.2
  have hbs : base.size = m := by
    rw [eb]
    simp
  have hr : ∀ i < m, (baseK WV is ih m).getD i 0 < 2300 := by
    intro i hi
    rw [← hbase]
    exact hb _ (getD_mem (by simpa [hbs] using hi))
  have hts : trees.size = m := by
    rw [et]
    simp [chainTrees, hbs]
  have htree : ∀ i < m, trees[i]! = treeOf 2300 (BS.run (tabF LC)
      (lvK (chainLet WV WVI chain.toList) (2 * chain.toList.length) (baseK WV is ih m) i) 2300
      ((baseK WV is ih m).getD i 0)) := by
    intro i hi
    rw [et, tree_eq hLCs' hLC' hb (by omega), hbase]
  have hTR : ∀ i < m,
      TreeRec trees[i]! LC (chainLet WV WVI chain.toList) R i (szs.getD i 0) := by
    intro i hi
    rw [htree i hi]
    exact treeRec_of (by omega) hLC' (hr i hi) (hlv i hi)
  refine ⟨invOK_gen h0 pA, invOK_gen h1 pB, by omega, by omega, ?_, ?_, hω', m4, ?_, ?_, ?_, ?_,
    ?_⟩
  ·
    rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    have hT := hL (2 * j) (by omega)
    have hU := hL (2 * j + 1) (by omega)
    rw [wordLet_even] at hT
    rw [wordLet_odd] at hU
    exact invOK_of hT hU fun x hx => ((perm12_facts (pW j (by omega)).1).2.2 x hx).2
  ·
    rw [Array.all_eq_true']
    intro j hj
    rw [decide_eq_true_eq]
    exact hcl j (Array.mem_def.1 hj)
  ·
    have hP := powT_TR' hY e
    unfold eqTab2
    rw [List.all_eq_true]
    intro x hx
    have hx' := List.mem_range.1 hx
    have a1 : ap (powT 2300 e Y) x = itr (ap12 (WV is)) e x := (hP.2 x hx').1
    have a2 : ap (idT 2300) x = x := (hI.2 x hx').1
    rw [a1, a2, ← ap12_ppow _ e hx', m6, ap12_pidn hx', beq_self_eq_true]
  ·
    have hne : eqTab2 Y (idT 2300) ≠ true := by
      intro hE
      unfold eqTab2 at hE
      rw [List.all_eq_true] at hE
      apply m7
      refine eq_pidn_of_fix (perm12_facts (pW is m1).1).1 fun x hx => ?_
      have h' := hE x (List.mem_range.2 hx)
      have a1 : ap Y x = ap12 (WV is) x := (hY.2 x hx).1
      have a2 : ap (idT 2300) x = x := (hI.2 x hx).1
      rw [a1, a2, beq_iff_eq] at h'
      exact h'
    simpa using hne
  ·
    rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [htree i hi', lev_eq hLCs' hLC' hb i, arr_getD base i, hbase]
    exact treeOK_of_level hLC' (hr i hi') (hlv i hi')
  ·
    rw [foldl_mul_congr (f := fun i => trees[i]!.pts.size) (g := fun i => szs.getD i 0)
      (List.range m) 1 (fun i hi => (hTR i (List.mem_range.1 hi)).size), ← hszl,
      foldl_range_getD]
    exact m8
  ·
    have e1 : (List.range 2300).filter (fun p =>
        decide (sift trees LC (Array.range m) base 0 (tupleOf Y m p) = true)) =
        (List.range 2300).filter (fun p => siftL (chainLet WV WVI chain.toList) R
          (baseK WV is ih m) szs (List.range m) (tupK (WV is) m p)) := by
      apply List.filter_congr
      intro p hp
      obtain ⟨t1, t2⟩ := tup_eq hY m (List.mem_range.1 hp)
      rw [sift_eq hts hTR m 0 _ (by omega) t2, t1, hbase, ← List.range_eq_range',
        Bool.decide_eq_true]
    rw [Nat.count, List.countP_eq_length_filter]
    exact (congrArg List.length e1).trans_le (countK_le hcnt)

private theorem seven_extras {words : Array (List Int)} {is ih : Nat} {ids : Array Nat}
    {WV WVI : Nat → Nat} {L : Array Table} {Y : Table} {ω : Nat}
    (hL : ∀ l < 2 * words.size, TR 2300 L[l]! (ap12 (wordLet WV WVI l)))
    (hY : TR 2300 Y (ap12 (WV is))) (hω : ω = ap12 (WV ih) 0) (hω' : ω < 2300)
    (hid : ids.size = 8) (hc : centK WV words.toList ids.toList is ih 7 = true) :
    ids.all (fun j => decide (j < words.size)) = true ∧
      (ids.map fun j => L[2 * j]!).all
        (fun E => eqTab2 (compT 2300 E Y) (compT 2300 Y E)) = true ∧
      imagesDistinct (centTabs7 2300 Y (ids.map fun j => L[2 * j]!)) ω = true := by
  obtain ⟨cf1, cf2⟩ := centK_facts hc
  have hlen : words.toList.length = words.size := Array.length_toList
  have hl8 : ids.toList.length = 8 := by rw [Array.length_toList, hid]
  have hw : ∀ j ∈ ids.toList, TR 2300 L[2 * j]! (ap12 (WV j)) := by
    intro j hj
    have h' := hL (2 * j) (by have := (cf1 j hj).1; omega)
    rwa [wordLet_even] at h'
  refine ⟨?_, ?_, ?_⟩
  · rw [Array.all_eq_true']
    intro j hj
    rw [decide_eq_true_eq]
    have := (cf1 j (Array.mem_def.1 hj)).1
    omega
  · rw [Array.all_eq_true']
    intro E hE
    rw [Array.mem_map] at hE
    obtain ⟨j, hj, rfl⟩ := hE
    have hj' := Array.mem_def.1 hj
    have hEj := hw j hj'
    have h1 := compT_TR' hEj hY
    have h2 := compT_TR' hY hEj
    unfold eqTab2
    rw [List.all_eq_true]
    intro x hx
    have hx' := List.mem_range.1 hx
    have a1 : ap (compT 2300 L[2 * j]! Y) x = ap12 (WV j) (ap12 (WV is) x) := (h1.2 x hx').1
    have a2 : ap (compT 2300 Y L[2 * j]!) x = ap12 (WV is) (ap12 (WV j) x) := (h2.2 x hx').1
    rw [a1, a2, ← ap12_pcomp _ _ hx', ← ap12_pcomp _ _ hx', (cf1 j hj').2, beq_self_eq_true]
  · have hsz : (centTabs7 2300 Y (ids.map fun j => L[2 * j]!)).size = 56 := by
      simp [centTabs7]
    have hval : ∀ t < 56, ap (centTabs7 2300 Y (ids.map fun j => L[2 * j]!))[t]! ω =
        iterK (WV is) (t / 8) (ap12 (WV (ids.toList.getD (t % 8) 0)) (ap12 (WV ih) 0)) := by
      intro t ht
      have ht8 : t % 8 < ids.size := by
        rw [hid]
        omega
      have hg : (centTabs7 2300 Y (ids.map fun j => L[2 * j]!))[t]! =
          compT 2300 (powT 2300 (t / 8) Y) L[2 * ids.toList.getD (t % 8) 0]! := by
        unfold centTabs7
        rw [getElem!_pos _ t (by simpa using ht), Array.getElem_map, Array.getElem_range,
          getElem!_pos _ (t % 8) (by simpa using ht8), Array.getElem_map,
          ← getElem!_pos ids (t % 8) ht8, arr_getD ids (t % 8)]
      have hmem : ids.toList.getD (t % 8) 0 ∈ ids.toList := getD_mem (by rw [hl8]; omega)
      have hC := compT_TR' (powT_TR' hY (t / 8)) (hw _ hmem)
      have a1 : ap (compT 2300 (powT 2300 (t / 8) Y) L[2 * ids.toList.getD (t % 8) 0]!) ω =
          itr (ap12 (WV is)) (t / 8) (ap12 (WV (ids.toList.getD (t % 8) 0)) ω) :=
        (hC.2 ω hω').1
      rw [hg, a1, itr_iterK, hω]
    have hcpe : centPts WV ids.toList is ih 7 = (List.range (7 * 8)).map fun t =>
        iterK (WV is) (t / 8) (ap12 (WV (ids.toList.getD (t % 8) 0)) (ap12 (WV ih) 0)) := by
      unfold centPts
      rw [hl8]
    have hcl : (centPts WV ids.toList is ih 7).length = 56 := by
      simp [hcpe]
    have hcp : ∀ t (ht : t < (centPts WV ids.toList is ih 7).length),
        (centPts WV ids.toList is ih 7)[t] =
          iterK (WV is) (t / 8) (ap12 (WV (ids.toList.getD (t % 8) 0)) (ap12 (WV ih) 0)) := by
      intro t ht
      rw [List.getElem_of_eq hcpe, List.getElem_map, List.getElem_range]
    unfold imagesDistinct
    rw [hsz, List.all_eq_true]
    intro s hs
    rw [List.all_eq_true]
    intro t ht
    have hs' := List.mem_range.1 hs
    have ht' := List.mem_range.1 ht
    by_cases est : s = t
    · subst est
      simp
    · have hne : ap (centTabs7 2300 Y (ids.map fun j => L[2 * j]!))[s]! ω ≠
          ap (centTabs7 2300 Y (ids.map fun j => L[2 * j]!))[t]! ω := by
        rw [hval s hs', hval t ht']
        intro e
        apply est
        refine cf2.eq_of_getElem_eq (by omega) (by omega) ?_
        rw [hcp, hcp]
        exact e
      simp [est, hne]

theorem co2ElevenOK_of {D : Co2ElevenData} {m bound A B : Nat} {WV WVI R : Nat → Nat}
    {szs : List Nat}
    (hA : co2T 0 = (CFSG.KS.Raw.unpack 2300 12 A).map UInt32.ofNat)
    (hB : co2T 1 = (CFSG.KS.Raw.unpack 2300 12 B).map UInt32.ofNat)
    (hs : slpOK D.words = true)
    (h : elevenK A B WV WVI R D.words.toList D.is D.ih D.chain.toList m 11 bound szs = true) :
    co2ElevenOK D m bound = true := by
  obtain ⟨c1, c2, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ :=
    common (words := D.words) (is := D.is) (ih := D.ih) (chain := D.chain) rfl rfl rfl rfl rfl
      rfl hA hB hs h
  unfold co2ElevenOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, hs⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩

theorem co2SevenOK_of {D : Co2SevenData} {m bound A B : Nat} {WV WVI R : Nat → Nat}
    {szs : List Nat}
    (hA : co2T 0 = (CFSG.KS.Raw.unpack 2300 12 A).map UInt32.ofNat)
    (hB : co2T 1 = (CFSG.KS.Raw.unpack 2300 12 B).map UInt32.ofNat)
    (hs : slpOK D.words = true) (hid : D.id.size = 8)
    (h : elevenK A B WV WVI R D.words.toList D.is D.ih D.chain.toList m 7 bound szs = true)
    (hc : centK WV D.words.toList D.id.toList D.is D.ih 7 = true) :
    co2SevenOK D m bound = true := by
  obtain ⟨-, hL, hY, hω, hω'⟩ :=
    basics (words := D.words) (is := D.is) (ih := D.ih) rfl rfl rfl hA hB hs h
  obtain ⟨d1, d2, d3⟩ := seven_extras hL hY hω hω' hid hc
  obtain ⟨c1, c2, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ :=
    common (words := D.words) (is := D.is) (ih := D.ih) (chain := D.chain) rfl rfl rfl rfl rfl
      rfl hA hB hs h
  unfold co2SevenOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, hs⟩, c4⟩, c5⟩, hid⟩, d1⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩,
    d2⟩, c12⟩, c13⟩, c14⟩, d3⟩

end CFSG.KC.Co2Eleven.Snd

end
