module

public import CFSG.Sporadic.J4.QT2LocX0Native
public import CFSG.Certificates.Kernel.J4Q.VOrbBFS
public import CFSG.Certificates.Kernel.J4Q.BfsOrder

public section

namespace CFSG.KC.J4Q.MOrbBFS

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2 CFSG.KC.J4Q
  CFSG.KC.J4Q.VOrbStorage CFSG.KC.J4Q.VOrbBFS

section Probe

variable {bits : Nat}

def home (bits : Nat) (k : Array V2) : Nat := (rowsHash k).toNat % 2 ^ bits

structure HInv (bits : Nat) (pts : Array (Array V2)) (slots : ByteArray) : Prop where
  size : slots.size = 4 * 2 ^ bits
  range : ∀ s < 2 ^ bits, rdU32 slots s ≤ pts.size
  inj : ∀ s < 2 ^ bits, ∀ t < 2 ^ bits, rdU32 slots s = rdU32 slots t → rdU32 slots s ≠ 0 → s = t
  cover : ∀ i (hi : i < pts.size), ∃ d < 2 ^ bits,
    rdU32 slots (slotAt bits (home bits pts[i]) d) = i + 1 ∧
      ∀ d' < d, rdU32 slots (slotAt bits (home bits pts[i]) d') ≠ 0
  nodup : ∀ i j (hi : i < pts.size) (hj : j < pts.size), pts[i] = pts[j] → i = j

theorem exists_empty {pts : Array (Array V2)} {slots : ByteArray} (H : HInv bits pts slots)
    (hsz : pts.size < 2 ^ bits) (h : Nat) : ∃ d < 2 ^ bits, rdU32 slots (slotAt bits h d) = 0 := by
  by_contra hne'
  have hne : ∀ d < 2 ^ bits, rdU32 slots (slotAt bits h d) ≠ 0 :=
    fun d hd h0 => hne' ⟨d, hd, h0⟩
  have hall : ∀ s < 2 ^ bits, rdU32 slots s ≠ 0 := by
    intro s hs
    obtain ⟨d, hd, rfl⟩ := slotAt_surj (bits := bits) h hs
    exact hne d hd
  have hc := Finset.card_le_card_of_injOn (s := Finset.range (2 ^ bits))
    (t := Finset.Icc 1 pts.size) (fun s => rdU32 slots s)
    (by
      intro s hs
      have hs' : s < 2 ^ bits := Finset.mem_range.1 hs
      have h1 := hall s hs'
      have h2 := H.range s hs'
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega)
    (by
      intro s hs t ht hst
      exact H.inj s (Finset.mem_range.1 hs) t (Finset.mem_range.1 ht) hst
        (hall s (Finset.mem_range.1 hs)))
  simp only [Finset.card_range, Nat.card_Icc] at hc
  omega

theorem home_eq (k : Array V2) : (rowsHash k).toNat &&& 2 ^ bits - 1 = home bits k :=
  Nat.and_two_pow_sub_one_eq_mod _ _

theorem home_lt (k : Array V2) : home bits k < 2 ^ bits := Nat.mod_lt _ (Nat.two_pow_pos bits)

theorem mfind_spec {pts : Array (Array V2)} {slots : ByteArray} (H : HInv bits pts slots)
    (k : Array V2) :
    (mfind pts slots bits k ≠ 0 → ∃ h : mfind pts slots bits k - 1 < pts.size,
      pts[mfind pts slots bits k - 1] = k) ∧
    (k ∈ pts → mfind pts slots bits k ≠ 0) := by
  have hn := Nat.two_pow_pos bits
  let R : Nat → Prop := fun r =>
    (r ≠ 0 → ∃ h : r - 1 < pts.size, pts[r - 1] = k) ∧ (k ∈ pts → r ≠ 0)
  let I : Nat → Option Nat × Nat → Prop := fun j st =>
    st.1 = none ∧ st.2 = slotAt bits (home bits k) j ∧ ∀ d < j,
      rdU32 slots (slotAt bits (home bits k) d) ≠ 0 ∧
      eqRows (pts[rdU32 slots (slotAt bits (home bits k) d) - 1]?.getD #[]) k = false
  have hfound : ∀ i (hi : i < pts.size), pts[i] = k → ∃ d < 2 ^ bits,
      rdU32 slots (slotAt bits (home bits k) d) = i + 1 ∧
      ∀ d' < d, rdU32 slots (slotAt bits (home bits k) d') ≠ 0 := by
    intro i hi hik
    obtain ⟨d, hd, h1, h2⟩ := H.cover i hi
    rw [hik] at h1 h2
    exact ⟨d, hd, h1, h2⟩
  have hbeq : ∀ i (hi : i < pts.size), pts[i] = k →
      eqRows (pts[i + 1 - 1]?.getD #[]) k = true := by
    intro i hi hik
    rw [Nat.add_sub_cancel, Array.getElem?_eq_getElem hi, Option.getD_some, hik]
    exact eqRows_iff.2 rfl
  change R (mfind pts slots bits k)
  unfold mfind
  dsimp only
  refine BfsOrder.forIn_range_bind I R _ _ _ _ ?_ ?_ ?_
  · intro j st _ hI
    obtain ⟨h1, h2, h3⟩ := hI
    split
    · rename_i he
      have he' : rdU32 slots st.2 = 0 := by simpa using he
      refine ⟨fun h => (h rfl).elim, fun hk => ?_⟩
      obtain ⟨i, hi, hik⟩ := Array.mem_iff_getElem.1 hk
      obtain ⟨d, hd, hd1, hd2⟩ := hfound i hi hik
      rw [h2] at he'
      rcases Nat.lt_trichotomy j d with hjd | hjd | hjd
      · exact (hd2 j hjd he').elim
      · subst hjd
        omega
      · have := (h3 d hjd).2
        rw [hd1, hbeq i hi hik] at this
        exact absurd this (by decide)
    · rename_i he
      have he' : rdU32 slots st.2 ≠ 0 := by simpa using he
      split
      · rename_i hb
        refine ⟨fun _ => ?_, fun _ => he'⟩
        have hr := H.range st.2 (by rw [h2]; exact slotAt_lt _ _)
        have hlt : rdU32 slots st.2 - 1 < pts.size := by omega
        refine ⟨hlt, ?_⟩
        rw [Array.getElem?_eq_getElem hlt, Option.getD_some] at hb
        exact eqRows_iff.1 hb
      · rename_i hb
        refine ⟨rfl, ?_, ?_⟩
        · dsimp only
          rw [Nat.and_two_pow_sub_one_eq_mod, h2, slotAt_succ]
        · intro d hd
          rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | rfl
          · exact h3 d hd
          · rw [← h2]
            exact ⟨he', by simpa using hb⟩
  · rintro ⟨o, h⟩ ⟨h1, h2, h3⟩
    dsimp only at h1
    subst h1
    change R 0
    refine ⟨fun h => (h rfl).elim, fun hk => ?_⟩
    obtain ⟨i, hi, hik⟩ := Array.mem_iff_getElem.1 hk
    obtain ⟨d, hd, hd1, _⟩ := hfound i hi hik
    have := (h3 d hd).2
    rw [hd1, hbeq i hi hik] at this
    exact absurd this (by decide)
  · exact ⟨rfl, by rw [home_eq, slotAt_zero (home_lt k)], fun d hd => (Nat.not_lt_zero _ hd).elim⟩

theorem mslot_spec {pts : Array (Array V2)} {slots : ByteArray} (H : HInv bits pts slots)
    (hsz : pts.size < 2 ^ bits) (k : Array V2) :
    ∃ d < 2 ^ bits, mslot slots bits k = slotAt bits (home bits k) d ∧
      rdU32 slots (slotAt bits (home bits k) d) = 0 ∧
      ∀ d' < d, rdU32 slots (slotAt bits (home bits k) d') ≠ 0 := by
  let I : Nat → Option Nat × Nat → Prop := fun j st =>
    st.1 = none ∧ st.2 = slotAt bits (home bits k) j ∧ ∀ d < j,
      rdU32 slots (slotAt bits (home bits k) d) ≠ 0
  let R : Nat → Prop := fun r => ∃ d < 2 ^ bits, r = slotAt bits (home bits k) d ∧
      rdU32 slots (slotAt bits (home bits k) d) = 0 ∧
      ∀ d' < d, rdU32 slots (slotAt bits (home bits k) d') ≠ 0
  change R (mslot slots bits k)
  unfold mslot
  dsimp only
  refine BfsOrder.forIn_range_bind I R _ _ _ _ ?_ ?_ ?_
  · intro j st hj hI
    obtain ⟨h1, h2, h3⟩ := hI
    split
    · rename_i he
      have he' : rdU32 slots st.2 = 0 := by simpa using he
      exact ⟨j, hj, h2, by rw [← h2]; exact he', h3⟩
    · rename_i he
      have he' : rdU32 slots st.2 ≠ 0 := by simpa using he
      refine ⟨rfl, ?_, ?_⟩
      · dsimp only
        rw [Nat.and_two_pow_sub_one_eq_mod, h2, slotAt_succ]
      · intro d hd
        rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | rfl
        · exact h3 d hd
        · rw [← h2]
          exact he'
  · intro st hI
    obtain ⟨_, _, h3⟩ := hI
    obtain ⟨d, hd, h0⟩ := exists_empty H hsz (home bits k)
    exact (h3 d hd h0).elim
  · exact ⟨rfl, by rw [home_eq, slotAt_zero (home_lt k)], fun d hd => (Nat.not_lt_zero _ hd).elim⟩

theorem hinv_zeros (hb : 4 * 2 ^ bits < 2 ^ 32) : HInv bits #[] (zeros (4 * 2 ^ bits)) where
  size := size_zeros _
  range s hs := by rw [rdU32_zeros hb hs]; exact Nat.le_refl _
  inj s hs _ _ _ h0 := (h0 (rdU32_zeros hb hs)).elim
  cover i hi := (Nat.not_lt_zero _ hi).elim
  nodup i _ hi := (Nat.not_lt_zero _ hi).elim

theorem hinv_insert {pts : Array (Array V2)} {slots : ByteArray} (H : HInv bits pts slots)
    (hb : 4 * 2 ^ bits < 2 ^ 32) (hsz : pts.size < 2 ^ bits) {k : Array V2} (hk : k ∉ pts) :
    HInv bits (pts.push k) (minsert pts slots bits k) := by
  obtain ⟨d, hd, hs, h0, hpre⟩ := mslot_spec H hsz k
  have hsl : slots.size < 2 ^ 32 := by rw [H.size]; exact hb
  have hn := Nat.two_pow_pos bits
  set s := mslot slots bits k with hsdef
  have hslt : s < 2 ^ bits := by rw [hs]; exact slotAt_lt _ _
  have haddr : ∀ t < 2 ^ bits, 4 * t + 3 < slots.size := by
    intro t ht
    rw [H.size]
    omega
  have hrd : ∀ t < 2 ^ bits, rdU32 (minsert pts slots bits k) t =
      if t = s then pts.size + 1 else rdU32 slots t := by
    intro t ht
    unfold minsert
    rw [← hsdef]
    by_cases hts : t = s
    · subst hts
      rw [ite_eq_left rfl, rdU32_wrU32_self _ hsl (haddr _ ht) (by omega)]
    · rw [ite_eq_right hts, rdU32_wrU32_other _ hsl (haddr _ hslt) (haddr _ ht) (Ne.symm hts)]
  have hs0 : rdU32 slots s = 0 := by rw [hs]; exact h0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold minsert
    rw [size_wrU32, H.size]
  · intro t ht
    rw [hrd t ht, Array.size_push]
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (H.range t ht)
  · intro t ht u hu htu hne
    rw [hrd t ht, hrd u hu] at htu
    rw [hrd t ht] at hne
    have hrt := H.range t ht
    have hru := H.range u hu
    by_cases h1 : t = s <;> by_cases h2 : u = s <;> simp only [h1, h2, ite_true, ite_false] at htu hne
    · rw [h1, h2]
    · omega
    · omega
    · exact H.inj t ht u hu htu hne
  · intro i hi
    rw [Array.size_push] at hi
    by_cases hil : i < pts.size
    · obtain ⟨d1, hd1, he, hb1⟩ := H.cover i hil
      have hget : (pts.push k)[i] = pts[i] := Array.getElem_push_lt hil
      refine ⟨d1, hd1, ?_, ?_⟩
      · rw [hget, hrd _ (slotAt_lt _ _)]
        have hne : slotAt bits (home bits pts[i]) d1 ≠ s := by
          intro he'
          rw [he', hs0] at he
          omega
        rw [ite_eq_right hne, he]
      · intro d' hd'
        rw [hget, hrd _ (slotAt_lt _ _)]
        split
        · omega
        · exact hb1 d' hd'
    · have hi' : i = pts.size := by omega
      subst hi'
      have hget : (pts.push k)[pts.size] = k := Array.getElem_push_eq
      refine ⟨d, hd, ?_, ?_⟩
      · rw [hget, hrd _ (slotAt_lt _ _), ← hs, ite_eq_left rfl]
      · intro d' hd'
        rw [hget, hrd _ (slotAt_lt _ _)]
        have hne : slotAt bits (home bits k) d' ≠ s := by
          intro he'
          exact hpre d' hd' (by rw [he']; exact hs0)
        rw [ite_eq_right hne]
        exact hpre d' hd'
  · intro i j hi hj hij
    rw [Array.size_push] at hi hj
    by_cases h1 : i < pts.size <;> by_cases h2 : j < pts.size
    · rw [Array.getElem_push_lt h1, Array.getElem_push_lt h2] at hij
      exact H.nodup i j h1 h2 hij
    · have : j = pts.size := by omega
      subst this
      rw [Array.getElem_push_lt h1, Array.getElem_push_eq] at hij
      exact (hk (hij ▸ Array.getElem_mem h1)).elim
    · have : i = pts.size := by omega
      subst this
      rw [Array.getElem_push_lt h2, Array.getElem_push_eq] at hij
      exact (hk (hij.symm ▸ Array.getElem_mem h2)).elim
    · omega

end Probe

theorem encR_inj {X Y : Array V2} (hX : WfA X) (hY : WfA Y) (h : encR X = encR Y) : X = Y := by
  refine Array.ext (by rw [hX.1, hY.1]) fun i h1 h2 => ?_
  have hi : i < 112 := by rw [← hX.1]; exact h1
  have e := rows_of_encR_eq h hi
  rw [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.getD_some,
    Option.getD_some] at e
  exact v2N_inj e

section BFS

variable {step : Array V2 → Nat → Array V2} {nl : Nat} {stepK : Nat → Nat → Nat} {w : Array V2}
  {cap bits : Nat} {MS PAR LAB : Nat → Nat} {TT : Nat → Nat → Nat}

structure Base (cap bits : Nat) (MS PAR LAB : Nat → Nat)
    (st : Array (Array V2) × Array Nat × Array Nat × ByteArray) : Prop where
  hinv : HInv bits st.1 st.2.2.2
  szp : st.2.1.size = st.1.size
  szl : st.2.2.1.size = st.1.size
  enc : ∀ k (hk : k < st.1.size), WfA st.1[k] ∧ encR st.1[k] = MS k
  tree : ∀ k, k < st.1.size → 0 < k → st.2.1[k]! = PAR k ∧ st.2.2.1[k]! = LAB k

structure Hyp (step : Array V2 → Nat → Array V2) (nl : Nat) (stepK : Nat → Nat → Nat)
    (w : Array V2) (cap bits : Nat) (MS PAR LAB : Nat → Nat) (TT : Nat → Nat → Nat) : Prop where
  hstep : ∀ X g, WfA X → g < nl → WfA (step X g) ∧ encR (step X g) = stepK (encR X) g
  hw : WfA w
  hb : 4 * 2 ^ bits < 2 ^ 32
  hcap : cap < 2 ^ bits
  hpos : 0 < cap
  root : MS 0 = encR w
  inj : ∀ i < cap, ∀ j < cap, MS i = MS j → i = j
  tree : BfsOrder.Tree cap 1 nl PAR LAB TT
  edge : ∀ k, 0 < k → k < cap → MS k = stepK (MS (PAR k)) (LAB k)
  clos : ∀ k < cap, ∀ g < nl, stepK (MS k) g = MS (TT k g)

theorem mem_iff (Hy : Hyp step nl stepK w cap bits MS PAR LAB TT)
    {st : Array (Array V2) × Array Nat × Array Nat × ByteArray} (hB : Base cap bits MS PAR LAB st)
    (hle : st.1.size ≤ cap) {y : Array V2} (hy : WfA y) {j : Nat} (hj : j < cap)
    (he : encR y = MS j) : (y ∈ st.1 ↔ j < st.1.size) := by
  constructor
  · intro hm
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hm
    rw [(hB.enc i hi).2] at he
    rw [← Hy.inj i (by omega) j hj he]
    exact hi
  · intro hjs
    have e := hB.enc j hjs
    rw [encR_inj hy e.1 (he.trans e.2.symm)]
    exact Array.getElem_mem hjs

def Inner (cap bits nl : Nat) (MS PAR LAB : Nat → Nat) (q : Nat) (p : Array V2) (g : Nat)
    (st : Array (Array V2) × Array Nat × Array Nat × ByteArray) : Prop :=
  Base cap bits MS PAR LAB st ∧ BfsOrder.Inv cap 1 nl PAR LAB q g st.1.size ∧ q < st.1.size ∧
    st.1[q]! = p

theorem inner_step (Hy : Hyp step nl stepK w cap bits MS PAR LAB TT) {q g : Nat} {p : Array V2}
    (hg : g < nl) {pts : Array (Array V2)} {par lab : Array Nat} {slots : ByteArray}
    (hJ : Inner cap bits nl MS PAR LAB q p g (pts, par, lab, slots)) :
    Inner cap bits nl MS PAR LAB q p (g + 1)
      (if (mfind pts slots bits (step p g) == 0 && decide (pts.size < cap)) = true then
        (pts.push (step p g), par.push q, lab.push g, minsert pts slots bits (step p g))
      else (pts, par, lab, slots)) := by
  obtain ⟨hB, hI, hq, hp⟩ := hJ
  replace hI : BfsOrder.Inv cap 1 nl PAR LAB q g pts.size := hI
  replace hq : q < pts.size := hq
  replace hp : pts[q]! = p := hp
  have szp : par.size = pts.size := hB.szp
  have szl : lab.size = pts.size := hB.szl
  have hle : pts.size ≤ cap := hI.1
  have hqc : q < cap := by omega
  have hpq : pts[q]! = pts[q] := getElem!_pos pts q hq
  have hpe : p = pts[q] := hp.symm.trans hpq
  subst hpe
  obtain ⟨hwq, heq⟩ := hB.enc q hq
  obtain ⟨hwy, hey⟩ := Hy.hstep pts[q] g hwq hg
  have htt := Hy.tree.clos q hqc g hg
  have hey' : encR (step pts[q] g) = MS (TT q g) := by rw [hey, heq, Hy.clos q hqc g hg]
  have hmem := mem_iff Hy hB hle hwy htt hey'
  by_cases hin : TT q g < pts.size
  · have hf := (mfind_spec hB.hinv (step pts[q] g)).2 (hmem.2 hin)
    have hc : (mfind pts slots bits (step pts[q] g) == 0 && decide (pts.size < cap)) = false := by
      simp [hf]
    rw [hc]
    exact ⟨hB, BfsOrder.inv_old Hy.tree hI hqc hg hin, hq, hpq⟩
  · obtain ⟨hTm, hmn, -, hpar, hlab, hI'⟩ := BfsOrder.inv_new Hy.tree hI hqc hg hin
    have hnot : step pts[q] g ∉ pts := fun h => hin (hmem.1 h)
    have hf : mfind pts slots bits (step pts[q] g) = 0 := by
      by_contra hne
      obtain ⟨hlt, he⟩ := (mfind_spec hB.hinv _).1 hne
      exact hnot (he ▸ Array.getElem_mem hlt)
    have hc : (mfind pts slots bits (step pts[q] g) == 0 && decide (pts.size < cap)) = true := by
      simp [hf, hmn]
    rw [hc]
    simp only [↓reduceIte]
    have hinv : HInv bits pts slots := hB.hinv
    refine ⟨⟨hinv_insert hinv Hy.hb (Nat.lt_trans hmn Hy.hcap) hnot, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simp only [Array.size_push, szp]
    · simp only [Array.size_push, szl]
    · intro k hk
      dsimp only at hk ⊢
      rw [Array.size_push] at hk
      by_cases hkl : k < pts.size
      · rw [Array.getElem_push_lt hkl]
        exact hB.enc k hkl
      · have : k = pts.size := by omega
        subst this
        rw [Array.getElem_push_eq, hey', hTm]
        exact ⟨hwy, rfl⟩
    · intro k hk h0
      dsimp only at hk ⊢
      rw [Array.size_push] at hk
      by_cases hkl : k < pts.size
      · rw [get!_push_lt _ _ (by rw [szp]; exact hkl), get!_push_lt _ _ (by rw [szl]; exact hkl)]
        exact hB.tree k hkl h0
      · have hk' : k = pts.size := by omega
        have e1 : (par.push q)[par.size]! = q := get!_push_eq par q
        have e2 : (lab.push g)[lab.size]! = g := get!_push_eq lab g
        rw [szp] at e1
        rw [szl] at e2
        rw [hk', e1, e2]
        exact ⟨hpar.symm, hlab.symm⟩
    · simpa only [Array.size_push] using hI'
    · simp only [Array.size_push]
      omega
    · dsimp only
      rw [get!_push_lt _ _ hq, hpq]

theorem final (Hy : Hyp step nl stepK w cap bits MS PAR LAB TT)
    {st : Array (Array V2) × Array Nat × Array Nat × ByteArray} (hB : Base cap bits MS PAR LAB st)
    (hsz : st.1.size = cap) :
    oOrbOK step nl w ⟨st.1, st.2.1, st.2.2.1, st.2.2.2, bits⟩ cap = true := by
  have H := hB.hinv
  have hfind : ∀ i < st.1.size, mfind st.1 st.2.2.2 bits st.1[i]! = i + 1 := by
    intro i hi
    have hs := mfind_spec H st.1[i]!
    have hne := hs.2 (get!_mem' hi)
    obtain ⟨hlt, heq⟩ := hs.1 hne
    have := H.nodup _ i hlt hi (heq.trans (getElem!_pos st.1 i hi))
    omega
  have hget : ∀ {y : Array V2} {j : Nat}, WfA y → j < cap → encR y = MS j → st.1[j]! = y := by
    intro y j hy hj he
    have e := hB.enc j (by omega)
    rw [getElem!_pos st.1 j (by omega)]
    exact encR_inj e.1 hy (e.2.trans he.symm)
  have hpos := Hy.hpos
  unfold oOrbOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨hsz, by rw [hB.szp, hsz]⟩, by rw [hB.szl, hsz]⟩, hpos⟩, ?_⟩, fun q hq => ?_⟩
  · exact eqRows_iff.2 (hget Hy.hw hpos Hy.root.symm)
  have hq' : q < st.1.size := by omega
  obtain ⟨hwq, heq⟩ := hB.enc q hq'
  have hpq : st.1[q]! = st.1[q] := getElem!_pos st.1 q hq'
  unfold oOrbAt
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨?_, hfind q hq'⟩, fun g hg => ?_⟩, ?_⟩
  · rw [hpq]
    unfold wfRows
    rw [Bool.and_eq_true, beq_iff_eq]
    exact hwq
  · rw [hpq]
    obtain ⟨hwy, hey⟩ := Hy.hstep st.1[q] g hwq hg
    have htt := Hy.tree.clos q hq g hg
    have hey' : encR (step st.1[q] g) = MS (TT q g) := by rw [hey, heq, Hy.clos q hq g hg]
    have hy := hget hwy htt hey'
    have hm : step st.1[q] g ∈ st.1 := hy ▸ get!_mem' (by omega)
    have hs := mfind_spec H (step st.1[q] g)
    have hne := hs.2 hm
    obtain ⟨hlt, he⟩ := hs.1 hne
    refine ⟨⟨hne, by omega⟩, ?_⟩
    rw [getElem!_pos st.1 _ hlt, he]
    exact eqRows_iff.2 rfl
  · rcases Nat.eq_zero_or_pos q with h0 | h0
    · exact Or.inl h0
    · obtain ⟨hp, hl⟩ := hB.tree q hq' h0
      obtain ⟨hpq', hlq⟩ := Hy.tree.par q (by omega) hq
      refine Or.inr ⟨⟨by rw [hp]; exact hpq', by rw [hl]; exact hlq⟩, ?_⟩
      rw [hp, hl]
      obtain ⟨hwp, hep⟩ := hB.enc (PAR q) (by omega)
      rw [getElem!_pos st.1 (PAR q) (by omega)]
      obtain ⟨hwy, hey⟩ := Hy.hstep st.1[PAR q] (LAB q) hwp hlq
      apply eqRows_iff.2
      rw [hpq]
      exact encR_inj hwy hwq (by rw [hey, hep, ← Hy.edge q h0 hq, heq])
where
  get!_mem' {xs : Array (Array V2)} {i : Nat} (h : i < xs.size) : xs[i]! ∈ xs := by
    rw [getElem!_pos xs i h]
    exact Array.getElem_mem h

theorem obfs_order (Hy : Hyp step nl stepK w cap bits MS PAR LAB TT) :
    oOrbOK step nl w (obfs step nl w cap bits) cap = true ∧
      (∀ k (hk : k < (obfs step nl w cap bits).mats.size),
        WfA (obfs step nl w cap bits).mats[k] ∧ encR (obfs step nl w cap bits).mats[k] = MS k) ∧
      (obfs step nl w cap bits).mats.size = cap := by
  let P : MOrb → Prop := fun O => oOrbOK step nl w O cap = true ∧
    (∀ k (hk : k < O.mats.size), WfA O.mats[k] ∧ encR O.mats[k] = MS k) ∧ O.mats.size = cap
  let I : Nat → Array (Array V2) × Array Nat × Array Nat × ByteArray → Prop := fun q st =>
    Base cap bits MS PAR LAB st ∧ BfsOrder.Inv cap 1 nl PAR LAB q 0 st.1.size ∧ q ≤ st.1.size
  have hfin : ∀ st : Array (Array V2) × Array Nat × Array Nat × ByteArray,
      Base cap bits MS PAR LAB st → st.1.size = cap → P ⟨st.1, st.2.1, st.2.2.1, st.2.2.2, bits⟩ :=
    fun st hB hsz => ⟨final Hy hB hsz, hB.enc, hsz⟩
  change P (obfs step nl w cap bits)
  unfold obfs
  dsimp only
  refine BfsOrder.forIn_range_bind I P _ _ _ _ ?_ ?_ ?_
  · rintro q ⟨pts, par, lab, slots⟩ hq ⟨hB, hI, hle⟩
    dsimp only at hI hle
    dsimp only
    split
    · rename_i hqs
      refine BfsOrder.forIn_range_bind (Inner cap bits nl MS PAR LAB q pts[q]!) _ _ _ _ _ ?_ ?_ ?_
      · rintro g ⟨pts', par', lab', slots'⟩ hg hJ
        have hs := inner_step Hy hg hJ
        dsimp only
        split
        · rename_i hcond
          simp only [hcond, ↓reduceIte] at hs
          exact hs
        · rename_i hcond
          simp only [hcond] at hs
          exact hs
      · rintro ⟨pts', par', lab', slots'⟩ ⟨hB', hI', hq', -⟩
        replace hq' : q < pts'.size := hq'
        exact ⟨hB', BfsOrder.inv_next hI', Nat.succ_le_of_lt hq'⟩
      · exact ⟨hB, hI, hqs, rfl⟩
    · rename_i hqs
      replace hqs : ¬ q < pts.size := hqs
      replace hI : BfsOrder.Inv cap 1 nl PAR LAB q 0 pts.size := hI
      have hdone : pts.size = cap := BfsOrder.inv_done Hy.tree hI (by omega)
      exact hfin (pts, par, lab, slots) hB hdone
  · rintro ⟨pts, par, lab, slots⟩ ⟨hB, hI, hle⟩
    have h1 : pts.size ≤ cap := hI.1
    replace hle : cap ≤ pts.size := hle
    exact hfin (pts, par, lab, slots) hB (Nat.le_antisymm h1 hle)
  · have hw0 : #[w].size = 1 := rfl
    refine ⟨⟨hinv_insert (hinv_zeros Hy.hb) Hy.hb (by simp)
      (by simp), by simp, by simp, ?_, ?_⟩, ?_, by simp⟩
    · intro k hk
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      exact ⟨Hy.hw, Hy.root.symm⟩
    · intro k hk h0
      have : k = 0 := by simpa using hk
      omega
    · have := BfsOrder.inv_init Hy.tree
      simpa using this

end BFS

end CFSG.KC.J4Q.MOrbBFS

end
