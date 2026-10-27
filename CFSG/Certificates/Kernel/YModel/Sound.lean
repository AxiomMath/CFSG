module

public import Certificates.Data.Kernel.YModel.Model
public import CFSG.YGroups.Exact.Model
public import CFSG.Certificates.Kernel.YModel.TextSound
import CFSG.Certificates.Kernel.YModel.SchCard
import CFSG.Certificates.Kernel.YModel.ChainSem

public section

namespace CFSG.KC.YModel

open CFSG.YGroups.ModelNative CFSG.Monster.B.Co2.Native

@[expose] noncomputable def unpackA (n w F : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => fieldAt w F i.val

@[expose] def decodeInt (x : Nat) : Int := if x % 2 = 1 then -((x / 2 : Nat) : Int) else ((x / 2 : Nat) : Int)

@[expose] noncomputable def linesA (n : Nat → Nat) (w : Nat) (F : Nat → Nat) (lines : Nat) : Array (Array Nat) :=
  ((List.range lines).map fun L => unpackA (n L) w (F L)).toArray

@[expose] noncomputable def linesW (n : Nat → Nat) (w : Nat) (F : Nat → Nat) (lines : Nat) : Array (List Int) :=
  ((List.range (lines - 1)).map fun L =>
    (List.range (n (L + 1))).map fun i => decodeInt (fieldAt w (F (L + 1)) i)).toArray

theorem decBind_perms {bs : List Nat} {w lines : Nat} {C : Nat → List Nat} {E : Nat → Nat}
    (h : decBind bs w lines lines C E = true)
    (hnl : bs.getLast? = some 10 := by
      exact CFSG.KC.YModel.TextSem.getLast?_bytesOf (by decide +kernel)) :
    parsePerms (String.ofList (bs.map Char.ofNat)) = linesA E w (fun L => joinW w (C L)) lines :=
  TextSem.parsePerms_of_decBind h hnl

theorem decBind_chain {bs : List Nat} {w lines : Nat} {C : Nat → List Nat} {E : Nat → Nat}
    (hl : 0 < lines) (h : decBind bs w lines 1 C E = true)
    (hnl : bs.getLast? = some 10 := by
      exact CFSG.KC.YModel.TextSem.getLast?_bytesOf (by decide +kernel)) :
    chainBase (String.ofList (bs.map Char.ofNat)) = unpackA (E 0) w (joinW w (C 0)) ∧
      chainWords (String.ofList (bs.map Char.ofNat)) = linesW E w (fun L => joinW w (C L)) lines :=
  TextSem.chain_of_decBind h hnl hl

theorem size_linesA' {n : Nat → Nat} {w : Nat} {F : Nat → Nat} {m : Nat} :
    (linesA n w F m).size = m := by
  simp [linesA]

theorem getElem_linesA' {n w m c i : Nat} {F : Nat → Nat} (hc : c < m) (hi : i < n) :
    ((linesA (fun _ => n) w F m)[c]!)[i]! = fieldAt w (F c) i := by
  simp [linesA, unpackA, hc, hi]

theorem permsOK_of_letOK {k n m : Nat} {F Nf : Nat → Nat}
    (h : ∀ c < m, letOK k n (F c) (Nf c) = true) (hk : k ≤ 32 := by decide) :
    permsOK n (linesA (fun _ => n) 32 F m) = true := by
  unfold permsOK
  rw [CFSG.Monster.B.Co2.allLt_iff, size_linesA']
  intro c hc
  obtain ⟨hn, hv, hent, hfix⟩ := Sem.letOK_spec hk (h c hc)
  have hg : ∀ i < n, ((linesA (fun _ => n) 32 F m)[c]!)[i]! = Benes.benesPerm k (Nf c) i :=
    fun i hi => by rw [getElem_linesA' hc hi, hent i hi]
  apply Sem.isInvA_invCand
  · intro i hi
    rw [hg i hi]
    exact Sem.perm_lt hn hv hfix hi
  · intro i hi j hj e
    rw [hg i hi, hg j hj] at e
    have := congrArg (Benes.benesInv k (Nf c)) e
    rwa [Benes.benesInv_benesPerm hv, Benes.benesInv_benesPerm hv] at this

theorem relsOK_mem {k m : Nat} {Nf : Nat → Nat} : ∀ {rels : List (List Nat)},
    relsOK k m Nf rels = true → ∀ r ∈ rels, wordAp k m Nf r (MonsterConv.Perm.idP k) =
      MonsterConv.Perm.idP k
  | [], _, r, hr => absurd hr List.not_mem_nil
  | r' :: rs, h, r, hr => by
    change andB (Nat.beq (wordAp k m Nf r' (MonsterConv.Perm.idP k)) (MonsterConv.Perm.idP k))
      (relsOK k m Nf rs) = true at h
    obtain ⟨h1, h2⟩ := Sem.andB_eq h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Nat.eq_of_beq_eq_true h1
    · exact relsOK_mem h2 r hr

private theorem val_evalWord {k n m : Nat} {F Nf : Nat → Nat}
    (h : ∀ c < m, letOK k n (F c) (Nf c) = true) (hk : k ≤ 32) (r : List Nat) (i : Fin n) :
    ((CFSG.Certificates.CosetEnumeration.evalWord
      (CFSG.YGroups.arrGen n (linesA (fun _ => n) 32 F m)) r i : Fin n) : Nat) =
        Sem.wF k m Nf r i := by
  have hp := permsOK_of_letOK h hk
  set O := linesA (fun _ => n) 32 F m with hOd
  induction r generalizing i with
  | nil => rfl
  | cons c r ih =>
    have hj : Sem.wF k m Nf r i < n := by rw [← ih i]; exact Fin.isLt _
    rw [CFSG.Certificates.CosetEnumeration.evalWord_cons, Equiv.Perm.mul_apply,
      ← CFSG.YGroups.rep_letterOf hp c
        (CFSG.Certificates.CosetEnumeration.evalWord (CFSG.YGroups.arrGen n O) r i), ih i]
    change _ = if c < m then Benes.benesPerm k (Nf c) (Sem.wF k m Nf r i) else Sem.wF k m Nf r i
    unfold CFSG.YGroups.ModelNative.letterOf
    rw [size_linesA']
    by_cases hc : c < m
    · rw [if_pos hc, if_pos hc, getElem_linesA' hc hj, (Sem.letOK_spec hk (h c hc)).2.2.1 _ hj]
    · rw [if_neg hc, if_neg hc, CFSG.Monster.B.Co2.idA_get hj]

theorem relatorsOK_of_relsOK {k n m : Nat} {F Nf : Nat → Nat} {rels : List (List Nat)}
    (h : ∀ c < m, letOK k n (F c) (Nf c) = true) (hr : relsOK k m Nf rels = true)
    (hk : k ≤ 32 := by decide) :
    relatorsOK n (linesA (fun _ => n) 32 F m) rels = true := by
  have hp := permsOK_of_letOK h hk
  set O := linesA (fun _ => n) 32 F m with hOd
  have hval := val_evalWord h hk
  unfold relatorsOK
  rw [List.all_eq_true]
  intro r hrr
  rw [CFSG.Monster.B.Co2.eqA_iff (CFSG.YGroups.rep_evalW hp r) CFSG.Monster.B.Co2.rep_idA]
  ext i
  rw [hval r i, Equiv.Perm.coe_one, id]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact Sem.wF_zero r i
  · have hn : n ≤ 2 ^ k := (Sem.letOK_spec hk (h 0 hm)).1
    have hv : ∀ c < m, Benes.StagesValid k (Nf c) := fun c hc => (Sem.letOK_spec hk (h c hc)).2.1
    exact Sem.eq_of_idP (Sem.acts_wordAp hv r) (Sem.acts_id k k) (relsOK_mem hr r hrr) i
      (by have := i.2; omega)

theorem wordAp_zero {k : Nat} {Nf : Nat → Nat} : ∀ (w : List Nat) (X : Nat), wordAp k 0 Nf w X = X
  | [], _ => rfl
  | c :: w, X => by
    rw [Sem.wordAp_cons, if_neg (Nat.not_lt_zero c), wordAp_zero w X]

private theorem testBit_wordAp_high {k m : Nat} {Nf : Nat → Nat}
    (hv : ∀ c < m, Benes.StagesValid k (Nf c)) :
    ∀ (w : List Nat) (X q : Nat), 2 ^ k * k ≤ q → (wordAp k m Nf w X).testBit q = X.testBit q
  | [], _, _, _ => rfl
  | c :: w, X, q, hq => by
    rw [Sem.wordAp_cons, testBit_wordAp_high hv w _ q hq]
    split
    · unfold apK
      rw [Sem.wid_eq]
      exact (Benes.testBit_netApply (P := k) rfl (hv c ‹_›) X).2 q hq
    · rfl

private theorem wF_fix {k n m : Nat} {Nf : Nat → Nat}
    (hfix : ∀ c < m, ∀ i, n ≤ i → i < 2 ^ k → Benes.benesPerm k (Nf c) i = i) :
    ∀ (w : List Nat) (r : Nat), n ≤ r → r < 2 ^ k → Sem.wF k m Nf w r = r
  | [], _, _, _ => rfl
  | c :: w, r, h1, h2 => by
    change (if c < m then _ else Sem.wF k m Nf w r) = r
    rw [wF_fix hfix w r h1 h2]
    split
    · exact hfix c ‹_› r h1 h2
    · rfl

theorem eqA_of_weqK {k n m : Nat} {F Nf : Nat → Nat} (u v : List Nat)
    (h : ∀ c < m, letOK k n (F c) (Nf c) = true) (hk : k ≤ 32 := by decide) :
    eqA n (evalW n (linesA (fun _ => n) 32 F m) u) (evalW n (linesA (fun _ => n) 32 F m) v) =
      weqK k m Nf u v := by
  have hp := permsOK_of_letOK h hk
  have hval := val_evalWord h hk
  rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.eqA_iff (CFSG.YGroups.rep_evalW hp u)
    (CFSG.YGroups.rep_evalW hp v)]
  unfold weqK
  rw [Nat.beq_eq]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [wordAp_zero, wordAp_zero]
    refine iff_of_true ?_ rfl
    ext i
    rw [hval u i, hval v i, Sem.wF_zero, Sem.wF_zero]
  have hn : n ≤ 2 ^ k := (Sem.letOK_spec hk (h 0 hm)).1
  have hv : ∀ c < m, Benes.StagesValid k (Nf c) := fun c hc => (Sem.letOK_spec hk (h c hc)).2.1
  have hfix := fun c hc => (Sem.letOK_spec hk (h c hc)).2.2.2
  have hu := Sem.acts_wordAp hv u
  have hv' := Sem.acts_wordAp hv v
  constructor
  · intro he
    have hwf : ∀ r < 2 ^ k, Sem.wF k m Nf u r = Sem.wF k m Nf v r := by
      intro r hr
      by_cases hrn : r < n
      · have := congrArg (fun g : Equiv.Perm (Fin n) => ((g ⟨r, hrn⟩ : Fin n) : Nat)) he
        rwa [hval u, hval v] at this
      · have hr' : n ≤ r := by omega
        rw [wF_fix hfix u r hr' hr, wF_fix hfix v r hr' hr]
    apply Nat.eq_of_testBit_eq
    intro q
    by_cases hq : q < 2 ^ k * k
    · have hW : 0 < 2 ^ k := Nat.two_pow_pos k
      have e : q = 2 ^ k * (q / 2 ^ k) + q % 2 ^ k := (Nat.div_add_mod q (2 ^ k)).symm
      have hqu : q / 2 ^ k < k := (Nat.div_lt_iff_lt_mul hW).mpr (by rw [Nat.mul_comm]; exact hq)
      have hqr : q % 2 ^ k < 2 ^ k := Nat.mod_lt q hW
      rw [e, hu.2 _ _ hqu _ hqr, hv'.2 _ _ hqu _ hqr, hwf _ hqr]
    · rw [testBit_wordAp_high hv u _ q (by omega), testBit_wordAp_high hv v _ q (by omega)]
  · intro he
    have hwf := Sem.eq_of_idP hu hv' he
    ext i
    rw [hval u i, hval v i, hwf i (by have := i.2; omega)]

theorem chainOK_of_checks {k n m nw w nb : Nat} {F Nf T WP WL R M Z : Nat → Nat} {B : Nat}
    {W : Array (List Int)} {base : Array Nat}
    (h : ∀ c < m, letOK k n (F c) (Nf c) = true)
    (hW : W = linesW (fun L => WL (L - 1)) w (fun L => WP (L - 1)) (nw + 1))
    (hB : base = unpackA nb 32 B)
    (hT : ∀ c < m, T c = Nf c)
    (hw : ∀ i < nw, wordOK k w m T WP WL i = true)
    (hl : ∀ i < nb, levelOK k n (Nat.add m nw) T B R M Z i = true)
    (hk : k ≤ 32 := by decide) (hm : 0 < m := by decide) :
    chainOK n (linesA (fun _ => n) 32 F m) W base = true ∧
      chainSizes n (linesA (fun _ => n) 32 F m) W base = (List.range nb).map Z := by
  have hn : n ≤ 2 ^ k := (Sem.letOK_spec hk (h 0 hm)).1
  subst hW hB
  apply Chain.chain_spec hn (permsOK_of_letOK h hk) size_linesA' _ _ _ _ _ hw hl
  · intro c hc
    obtain ⟨hn', hv, hent, hfix⟩ := Sem.letOK_spec hk (h c hc)
    have hG : Sch.Good k n (Nf c) := ⟨hn', hv, hfix⟩
    rw [hT c hc]
    refine ⟨hG, fun x => ?_⟩
    rw [getElem_linesA' hc x.2, hent x x.2, Sch.netPerm_apply hG]
  · simp [linesW]
  · intro i hi
    rw [getElem!_pos _ i (by simp [linesW]; omega)]
    simp only [linesW, List.getElem_toArray, List.getElem_map, List.getElem_range,
      Nat.add_sub_cancel, Sch.codesL, List.map_map]
    rfl
  · simp [unpackA]
  · intro i hi
    simp [unpackA, hi]

theorem card_arrClosure_of_sch {k n m w t : Nat} {F Nf U WP WL : Nat → Nat}
    {off bp Z LP LL : Nat → Nat} {TT : Nat → Nat → Nat}
    (h : ∀ c < m, letOK k n (F c) (Nf c) = true) (hU : ∀ c < m, U c = Nf c)
    (hoff : off 0 = m) (hmono : ∀ i < t, off i ≤ off (i + 1))
    (hgen0 : ∀ j, off 0 ≤ j → j < off 1 → genOK k w U WP WL 0 m j 0 false = true)
    (hgen : ∀ i, 0 < i → i < t → ∀ j, off i ≤ j → j < off (i + 1) →
      genOK k w U WP WL (off (i - 1)) (off i) j (bp (i - 1)) true = true)
    (hbp : ∀ i < t, bp i < n) (hb0 : ∀ i < t, ptX (TT i 0) = bp i ∧ 0 < Z i)
    (hpts : ∀ i < t, pointsOK k (TT i) (Z i) = true)
    (htr : ∀ i < t, ∀ a < Z i, transOK k w U (TT i) (bp i) (off i) (off (i + 1)) a 1 = true)
    (hrec : ∀ i < t, ∀ a < Z i, ∀ j, off i ≤ j → j < off (i + 1) →
      ∃ rec, recOK k w U (TT i) (Z i) (off (i + 1)) (off t) a j rec = true)
    (hlet : ∀ c < m, sweqK k w U (2 * (c + 1)) 1 (LP c) (LL c) = true ∧
      codesIn w m (off t) (LP c) (LL c) = true)
    (hk : k ≤ 32 := by decide) (hw : 2 * m < 2 ^ w := by decide) (hm : 0 < m := by decide) :
    Nat.card (CFSG.YGroups.arrClosure n (linesA (fun _ => n) 32 F m)) =
      ∏ i ∈ Finset.range t, Z i :=
  Sch.card_sch hk hw hm size_linesA' (fun c hc i hi => getElem_linesA' hc hi) h hU hoff hmono hgen0
    hgen hbp hb0 hpts htr hrec hlet

end CFSG.KC.YModel

end
