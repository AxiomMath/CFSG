module

public import Certificates.Data.Kernel.LocalComp.Tits
public import CFSG.Certificates.Kernel.LocalCompTits.Defs
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.TBfsSound
import CFSG.Certificates.Kernel.Common.QSort
import CFSG.Certificates.Kernel.LocalCompTits.Bsearch

public section

namespace CFSG.KC.LocalComp.TitsSound

open CFSG.KC.Enum CFSG.KS CFSG.SectionRank.Native.Tits CFSG.Sporadic.Th.Native CFSG.KC.LocalComp.Tits

structure OrbHyp (gs : Array (List Nat)) (root cap N : Nat) (TP TG TR : Nat → Nat) : Prop where
  ncap : N ≤ cap
  npos : 0 < N
  lt : ∀ i < N, TP i < 2 ^ 52
  inc : ∀ i, i + 1 < N → TP i < TP (i + 1)
  mapto : ∀ s < gs.size, ∀ i < N,
    pg 11 (mask 11) (TG s) i < N ∧ TP (pg 11 (mask 11) (TG s) i) = mvK (colsK gs s) (TP i) 0
  root : TP (rf (TR 0) 0) = root
  row : ∀ j < N, rf (TR j) 0 < N ∧ (j = 0 ∨ (rf (TR j) 1 < j ∧ rf (TR j) 2 < gs.size ∧
    rf (TR j) 0 = pg 11 (mask 11) (TG (rf (TR j) 2)) (rf (TR (rf (TR j) 1)) 0)))
  cover : ∀ k < N, ∃ j < N, rf (TR j) 0 = k

private theorem testBit_foldr {a : Nat → Nat} (k : Nat) :
    ∀ l : List Nat, (l.foldr (fun j s => Nat.lor s (Nat.shiftLeft 1 (a j))) 0).testBit k = true ↔
      ∃ j ∈ l, a j = k
  | [] => by simp
  | j :: l => by
    rw [List.foldr_cons]
    show (_ ||| 1 <<< a j).testBit k = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_foldr k l, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.testBit_two_pow]
    simp only [List.mem_cons, decide_eq_true_eq]
    constructor
    · rintro (⟨x, hx, e⟩ | e)
      · exact ⟨x, Or.inr hx, e⟩
      · exact ⟨j, Or.inl rfl, e⟩
    · rintro ⟨x, hx | hx, e⟩
      · subst hx; exact Or.inr e
      · exact Or.inl ⟨x, hx, e⟩

theorem orbHyp_of_K {gs : Array (List Nat)} {root cap N : Nat} {TP TG TR : Nat → Nat}
    (h : orbitK gs root cap N TP TG TR = true) : OrbHyp gs root cap N TP TG TR := by
  unfold orbitK at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, fun i hi => ?_, fun i hi => ?_, fun s hs i hi => ?_, ?_, fun j hj => ?_, ?_⟩
  · have := CFSG.KS.allN_spec h3 i hi
    simpa [Nat.blt_eq, Nat.shiftLeft_eq] using this
  · have := CFSG.KS.allN_spec h4 i (by omega)
    simpa [Nat.blt_eq] using this
  · have := CFSG.KS.allN_spec h5 s hs
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at this
    have := CFSG.KS.allN_spec this.2 i hi
    simpa [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Nat.blt_eq, Nat.beq_eq] using this
  · simpa [Nat.beq_eq] using h6
  · have := CFSG.KS.allN_spec h7 j hj
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, CFSG.KS.Raw.Orb.bIf_eq, Nat.blt_eq,
      Nat.beq_eq] at this
    obtain ⟨a, b⟩ := this
    refine ⟨a, ?_⟩
    by_cases hj0 : j = 0
    · exact Or.inl hj0
    · right
      simpa [hj0] using b
  · intro k hk
    have e := Nat.eq_of_beq_eq_true h8
    rw [CFSG.KS.Raw.Orb.foldN_eq] at e
    have hb : ((List.range N).foldr (fun j s => Nat.lor s (Nat.shiftLeft 1 (rf (TR j) 0))) 0).testBit
        k = true := by
      rw [e]
      show (1 <<< N - 1).testBit k = true
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
      simpa using hk
    obtain ⟨j, hj, e'⟩ := (testBit_foldr (a := fun j => rf (TR j) 0) k _).1 hb
    exact ⟨j, List.mem_range.1 hj, e'⟩

private theorem bit_eq (v i : Nat) : (Nat.beq (Nat.land (Nat.shiftRight v i) 1) 1 = true) ↔ v.testBit i = true := by
  rw [Nat.beq_eq]
  show (v >>> i &&& 1 = 1) ↔ _
  rw [Nat.testBit]
  simp [Nat.and_comm]

private theorem mvK_cons (c : Nat) (cs : List Nat) (v i : Nat) : mvK (c :: cs) v i =
   (if v.testBit i then c else 0) ^^^ mvK cs v (i+1) := by
  show Nat.xor (nIf(_,_,_)) _ = _
  rw [CFSG.KS.Raw.Orb.nIf_eq]
  simp only [bit_eq]
  rfl

private def xs (f : Nat → Nat) (m : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | i, n + 1 => (if m.testBit i then f i else 0) ^^^ xs f m (i + 1) n

private theorem xs_congr {f g : Nat → Nat} (m : Nat) : ∀ n i, (∀ k, i ≤ k → k < i + n → f k = g k) →
    xs f m i n = xs g m i n
  | 0, i, _ => rfl
  | n + 1, i, h => by
    simp only [xs]
    rw [h i (Nat.le_refl _) (by omega), xs_congr m n (i + 1) (fun k hk hk' => h k (by omega) (by omega))]

private theorem xs_zero {f : Nat → Nat} (m : Nat) : ∀ n i, (∀ k, i ≤ k → k < i + n →
    m.testBit k = false ∨ f k = 0) → xs f m i n = 0
  | 0, i, _ => rfl
  | n + 1, i, h => by
    simp only [xs]
    rw [xs_zero m n (i + 1) (fun k hk hk' => h k (by omega) (by omega))]
    rcases h i (Nat.le_refl _) (by omega) with e | e <;> simp [e]

private theorem xs_add (f : Nat → Nat) (m : Nat) : ∀ a b i, xs f m i (a + b) = xs f m i a ^^^ xs f m (i + a) b
  | 0, b, i => by simp [xs]
  | a + 1, b, i => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [xs]
    rw [xs_add f m a b (i + 1), show i + 1 + a = i + (a + 1) by omega, Nat.xor_assoc]

private theorem xorSel_eq_xs (f : Nat → Nat) (m : Nat) : ∀ n i, xorSel f m (i + n) = xorSel f m i ^^^ xs f m i n
  | 0, i => by simp [xs]
  | n + 1, i => by
    rw [show i + (n + 1) = (i + 1) + n by omega, xorSel_eq_xs f m n (i + 1)]
    simp only [xs, xorSel]
    by_cases hb : m.testBit i = true <;> simp [hb, Nat.xor_assoc]

private theorem mvK_eq_xs (v : Nat) : ∀ (cs : List Nat) (i : Nat),
    mvK cs v i = xs (fun k => cs.getD (k - i) 0) v i cs.length
  | [], i => rfl
  | c :: cs, i => by
    rw [mvK_cons, mvK_eq_xs v cs (i + 1)]
    simp only [xs, List.length_cons]
    congr 1
    · simp
    · exact xs_congr v _ _ (fun k hk _ => by
        rw [show k - i = (k - (i + 1)) + 1 by omega]; rfl)

theorem mvK_eq_mv (cs : List Nat) {v : Nat} (hv : v < 2 ^ 52) : mvK cs v 0 = mv cs v := by
  rw [mvK_eq_xs]
  unfold mv
  have h52 := xorSel_eq_xs (fun c => cs.getD c 0) v 52 0
  rw [Nat.zero_add, show xorSel (fun c => cs.getD c 0) v 0 = 0 from rfl, Nat.zero_xor] at h52
  rw [h52]
  have hf : ∀ k ≥ 52, v.testBit k = false := fun k hk =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) hk))
  have e1 : xs (fun k => cs.getD (k - 0) 0) v 0 cs.length = xs (fun k => cs.getD k 0) v 0 cs.length :=
    xs_congr v _ _ (fun k _ _ => by simp)
  rw [e1]
  rcases Nat.le_total cs.length 52 with hl | hl
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hl
    have e2 : xs (fun c => cs.getD c 0) v 0 52 =
        xs (fun c => cs.getD c 0) v 0 cs.length ^^^ xs (fun c => cs.getD c 0) v (0 + cs.length) d := by
      rw [← xs_add, ← hd]
    have : xs (fun c => cs.getD c 0) v (0 + cs.length) d = 0 :=
      xs_zero v d _ (fun k hk _ => Or.inr (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl))
    rw [e2, this, Nat.xor_zero]
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hl
    have e2 : xs (fun c => cs.getD c 0) v 0 cs.length =
        xs (fun c => cs.getD c 0) v 0 52 ^^^ xs (fun c => cs.getD c 0) v (0 + 52) d := by
      rw [← xs_add, ← hd]
    have : xs (fun c => cs.getD c 0) v (0 + 52) d = 0 :=
      xs_zero v d _ (fun k hk _ => Or.inl (hf k (by omega)))
    rw [e2, this, Nat.xor_zero]

private def innerB (v : Nat) (g : List Nat) (pts : Array Nat) : Id (ForInStep (Array Nat)) :=
  if (!pts.contains (mv g v)) = true then pure (ForInStep.yield (pts.push (mv g v)))
  else pure (ForInStep.yield pts)

private def outerB (gs : Array (List Nat)) (h : Nat) (pts : Array Nat) : Id (ForInStep (Array Nat)) :=
  if h < pts.size then pure (ForInStep.yield (Id.run (forIn gs pts (innerB pts[h]!))))
  else pure (ForInStep.yield pts)

private theorem orbitBFS_eq (gs : Array (List Nat)) (root cap : Nat) :
    orbitBFS gs root cap = Id.run (forIn (List.range' 0 cap) #[root] (outerB gs)) := by
  unfold orbitBFS
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private def QI (S : Nat → Prop) (gs : Array (List Nat)) (v : Nat) (pts0 : Array Nat) (j : Nat)
    (pts : Array Nat) : Prop :=
  pts.toList.Nodup ∧ (∀ x ∈ pts.toList, S x) ∧ (∃ ext, pts.toList = pts0.toList ++ ext) ∧
    ∀ g ∈ gs.toList.take j, mv g v ∈ pts.toList


private theorem innerB_mem {v : Nat} {g : List Nat} {b : Array Nat} (hc : mv g v ∈ b.toList) :
    innerB v g b = pure (ForInStep.yield b) := by
  rw [← Array.mem_def] at hc
  simp [innerB, hc]

private theorem innerB_new {v : Nat} {g : List Nat} {b : Array Nat} (hc : mv g v ∉ b.toList) :
    innerB v g b = pure (ForInStep.yield (b.push (mv g v))) := by
  rw [← Array.mem_def] at hc
  simp [innerB, hc]

private theorem inner_loop' {S : Nat → Prop} {gs : Array (List Nat)} {v : Nat} {pts0 : Array Nat}
    (hv : S v) (hcl : ∀ w, S w → ∀ g ∈ gs.toList, S (mv g w))
    (h0 : pts0.toList.Nodup) (hS : ∀ x ∈ pts0.toList, S x) :
    QI S gs v pts0 gs.toList.length (Id.run (forIn gs.toList pts0 (innerB v))) := by
  refine CFSG.KS.TBfs.forIn_list_yield gs.toList pts0 (innerB v) (QI S gs v pts0) ?_ ⟨h0, hS, ⟨[], by simp⟩, by simp⟩
  intro j hj b ⟨hnd, hSb, ⟨ext, hext⟩, hcb⟩
  have hg : gs.toList[j] ∈ gs.toList := List.getElem_mem hj
  have hSw : S (mv gs.toList[j] v) := hcl v hv _ hg
  by_cases hc : mv gs.toList[j] v ∈ b.toList
  · refine ⟨b, ?_, hnd, hSb, ⟨ext, hext⟩, ?_⟩
    · exact innerB_mem hc
    · intro g hg'
      rw [List.take_succ, List.getElem?_eq_getElem hj] at hg'
      simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hg'
      rcases hg' with h | h
      · exact hcb g h
      · rw [h]; exact hc
  · refine ⟨b.push (mv gs.toList[j] v), ?_, ?_, ?_, ⟨ext ++ [mv gs.toList[j] v], by simp [hext]⟩, ?_⟩
    · exact innerB_new hc
    · rw [Array.toList_push]
      refine List.nodup_append.2 ⟨hnd, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, ?_⟩
      intro a ha c hc' e
      rw [List.mem_singleton] at hc'
      subst hc'
      exact hc (e ▸ ha)
    · intro x hx
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with h | h
      · exact hSb x h
      · rw [h]; exact hSw
    · intro g hg'
      rw [List.take_succ, List.getElem?_eq_getElem hj] at hg'
      simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hg'
      simp only [Array.toList_push, List.mem_append, List.mem_singleton]
      rcases hg' with h | h
      · exact Or.inl (hcb g h)
      · exact Or.inr (by rw [h])

private def QO (S : Nat → Prop) (gs : Array (List Nat)) (root : Nat) (h : Nat) (pts : Array Nat) :
    Prop :=
  pts.toList.Nodup ∧ (∀ x ∈ pts.toList, S x) ∧ root ∈ pts.toList ∧
    ∀ i (hi : i < pts.size), i < h → ∀ g ∈ gs.toList, mv g pts[i] ∈ pts.toList

theorem orbitBFS_spec {S : Nat → Prop} {gs : Array (List Nat)} {root cap : Nat}
    (hroot : S root) (hcl : ∀ w, S w → ∀ g ∈ gs.toList, S (mv g w))
    (hbound : ∀ l : List Nat, l.Nodup → (∀ x ∈ l, S x) → l.length ≤ cap) :
    (orbitBFS gs root cap).toList.Nodup ∧ (∀ x ∈ (orbitBFS gs root cap).toList, S x) ∧
      root ∈ (orbitBFS gs root cap).toList ∧
      ∀ x ∈ (orbitBFS gs root cap).toList, ∀ g ∈ gs.toList, mv g x ∈ (orbitBFS gs root cap).toList := by
  rw [orbitBFS_eq]
  have key : QO S gs root (List.range' 0 cap).length
      (Id.run (forIn (List.range' 0 cap) #[root] (outerB gs))) := by
    refine CFSG.KS.TBfs.forIn_list_yield (List.range' 0 cap) #[root] (outerB gs) (QO S gs root) ?_
      ⟨by simp, by simpa using hroot, by simp, by simp⟩
    intro j hj b ⟨hnd, hSb, hrb, hcb⟩
    have hjj : (List.range' 0 cap)[j] = j := by simp
    rw [hjj]
    by_cases hjb : j < b.size
    · have hvS : S b[j] := hSb _ (by simp)
      have hin := inner_loop' (gs := gs) (v := b[j]) (pts0 := b) hvS hcl hnd hSb
      have hv : b[j]! = b[j] := getElem!_pos b j hjb
      generalize hb' : Id.run (forIn gs.toList b (innerB b[j])) = b' at hin
      obtain ⟨hnd', hS', ⟨ext, hext⟩, hcl'⟩ := hin
      have hget : ∀ i (hi : i < b.size) (hi' : i < b'.size), b'[i] = b[i] := by
        intro i hi hi'
        rw [← Array.getElem_toList, ← Array.getElem_toList (xs := b)]
        simp only [hext]
        exact List.getElem_append_left (by simpa using hi)
      refine ⟨b', ?_, hnd', hS', ?_, ?_⟩
      · simp only [outerB, hjb, if_true, hv, ← Array.forIn_toList, hb']
      · rw [hext]; simp [hrb]
      · intro i hi hij g hg
        have hmem : ∀ y ∈ b.toList, y ∈ b'.toList := by
          intro y hy; rw [hext]; exact List.mem_append_left _ hy
        rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | heq
        · rw [hget i (by omega) hi]
          exact hmem _ (hcb i (by omega) hlt g hg)
        · subst heq
          rw [hget i hjb hi]
          exact hcl' g (by rw [List.take_of_length_le (Nat.le_refl _)]; exact hg)
    · refine ⟨b, ?_, hnd, hSb, hrb, ?_⟩
      · simp [outerB, hjb]
      · intro i hi hij g hg
        exact hcb i hi (by omega) g hg
  generalize Id.run (forIn (List.range' 0 cap) #[root] (outerB gs)) = r at key ⊢
  obtain ⟨hnd, hS, hr, hc⟩ := key
  have hsz : r.size ≤ cap := by
    have := hbound r.toList hnd hS
    simpa using this
  refine ⟨hnd, hS, hr, fun x hx g hg => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := hc i (by simpa using hi) (by simp at hi ⊢; omega) g hg
  simpa using this


section Main

variable {gs : Array (List Nat)} {root cap N : Nat} {TP TG TR : Nat → Nat}

private theorem strictMono_of_inc (hinc : ∀ i, i + 1 < N → TP i < TP (i + 1)) :
    ∀ j i, i < j → j < N → TP i < TP j
  | 0, i, hij, _ => absurd hij (Nat.not_lt_zero _)
  | j + 1, i, hij, hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · exact Nat.lt_trans (strictMono_of_inc hinc j i h (by omega)) (hinc j hj)
    · subst h; exact hinc i hj

private theorem mv_eq_of_mem (H : OrbHyp gs root cap N TP TG TR) {s : Nat} (hs : s < gs.size) {i : Nat}
    (hi : i < N) : mv gs[s] (TP i) = TP (pg 11 (mask 11) (TG s) i) := by
  rw [← mvK_eq_mv _ (H.lt i hi), (H.mapto s hs i hi).2]
  have : colsK gs s = gs[s] := by
    unfold colsK
    simp [hs]
  rw [this]

private theorem orbit_set (H : OrbHyp gs root cap N TP TG TR) :
    let r := orbitBFS gs root cap
    r.toList.Nodup ∧ (∀ x ∈ r.toList, ∃ i < N, TP i = x) ∧ ∀ k < N, TP k ∈ r.toList := by
  have hcl : ∀ w, (∃ i < N, TP i = w) → ∀ g ∈ gs.toList, ∃ i < N, TP i = mv g w := by
    rintro w ⟨i, hi, rfl⟩ g hg
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hg
    have hs' : s < gs.size := by simpa using hs
    refine ⟨_, (H.mapto s hs' i hi).1, ?_⟩
    rw [← mv_eq_of_mem H hs' hi]
    simp
  have hbound : ∀ l : List Nat, l.Nodup → (∀ x ∈ l, ∃ i < N, TP i = x) → l.length ≤ cap := by
    intro l hnd hl
    have hsub : l ⊆ (List.range N).map TP := fun x hx => by
      obtain ⟨i, hi, e⟩ := hl x hx
      exact List.mem_map.2 ⟨i, List.mem_range.2 hi, e⟩
    have := hnd.length_le_of_subset hsub
    simp at this
    have := H.ncap
    omega
  obtain ⟨hnd, hS, hr, hc⟩ := orbitBFS_spec (S := fun x => ∃ i < N, TP i = x) (gs := gs)
    (root := root) (cap := cap) ⟨_, (H.row 0 H.npos).1, H.root⟩ hcl hbound
  refine ⟨hnd, hS, ?_⟩
  have hrows : ∀ j, j < N → TP (rf (TR j) 0) ∈ (orbitBFS gs root cap).toList := by
    intro j
    induction j using Nat.strongRecOn with
    | _ j ih =>
      intro hj
      obtain ⟨hlt, hj0 | ⟨hp, hs, he⟩⟩ := H.row j hj
      · subst hj0; rw [H.root]; exact hr
      · have hpN : rf (TR (rf (TR j) 1)) 0 < N := (H.row _ (by omega)).1
        have hmem := hc _ (ih _ hp (by omega)) gs[rf (TR j) 2] (by simp)
        rw [mv_eq_of_mem H hs hpN, ← he] at hmem
        exact hmem
  intro k hk
  obtain ⟨j, hj, e⟩ := H.cover k hk
  rw [← e]
  exact hrows j hj

private theorem ofFn_toList_lt (hinc : ∀ i, i + 1 < N → TP i < TP (i + 1)) :
    (Array.ofFn (n := N) fun i => TP i.val).toList.Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [Array.getElem_toList, Array.getElem_ofFn]
  simp only [Array.length_toList, Array.size_ofFn] at hj
  exact strictMono_of_inc hinc j i hij hj

private theorem sorted_eq (H : OrbHyp gs root cap N TP TG TR) :
    (orbitBFS gs root cap).qsort (· < ·) = Array.ofFn (n := N) (fun i => TP i.val) := by
  obtain ⟨hnd, hS, hall⟩ := orbit_set H
  have hlt := ofFn_toList_lt H.inc
  apply Array.toList_inj.1
  refine List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2) ?_
    (hlt.imp Nat.le_of_lt) ?_
  · have := CFSG.KC.QSort.qsort_pairwise (orbitBFS gs root cap) (fun a b => decide (a < b))
      (fun a b c h1 h2 => by simp at *; omega) (fun a b h => by simp at *; omega)
    exact this.imp (fun {a b} h => by simpa using h)
  · refine (Array.perm_iff_toList_perm.1 (CFSG.KC.QSort.qsort_perm _ _)).trans ?_
    refine (List.perm_ext_iff_of_nodup hnd (hlt.imp Nat.ne_of_lt)).2 fun x => ?_
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := hS x hx
      simp only [Array.mem_toList_iff, Array.mem_ofFn]
      exact ⟨⟨i, hi⟩, rfl⟩
    · intro hx
      simp only [Array.mem_toList_iff, Array.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hall i.val i.isLt


private theorem field_lt (H : OrbHyp gs root cap N TP TG TR) {s : Nat} (hs : s < gs.size) {i : Nat}
    (hi : i < N) : pg 11 (mask 11) (TG s) i < N := (H.mapto s hs i hi).1

private theorem tabP_get {N P i : Nat} (hi : i < N) :
    (tabP N P)[i]! = UInt32.ofNat (pg 11 (mask 11) P i) := by
  unfold tabP
  exact CFSG.KS.TBfs.ofFn_get (f := fun k => UInt32.ofNat (pg 11 (mask 11) P k)) hi

private theorem toNat_tabP {N P i : Nat} (hi : i < N) :
    ap (tabP N P) i = pg 11 (mask 11) P i := by
  unfold ap
  rw [tabP_get hi, UInt32.toNat_ofNat_of_lt']
  exact Nat.lt_trans (CFSG.KS.PF.pg_lt 11 P i) (by decide)

theorem orbit_sound {gs : Array (List Nat)} {root cap N : Nat} {TP TG TR : Nat → Nat}
    (h : orbitK gs root cap N TP TG TR = true) :
    (orbitBFS gs root cap).qsort (· < ·) = Array.ofFn (n := N) (fun i => TP i.val) ∧
      gs.map (tableOf ((orbitBFS gs root cap).qsort (· < ·))) =
        Array.ofFn (n := gs.size) (fun s => tabP N (TG s.val)) ∧
      orbitOK N (Array.ofFn (n := N) fun i => TP i.val) gs
        (Array.ofFn (n := gs.size) fun s => tabP N (TG s.val)) = true := by
  have H := orbHyp_of_K h
  have hsorted := sorted_eq H
  have hbs := bsearch_ofFn H.lt H.inc
  have himg : ∀ s (hs : s < gs.size) i, i < N →
      bsearch (Array.ofFn (n := N) fun i => TP i.val) (mv gs[s] (TP i)) =
        pg 11 (mask 11) (TG s) i := by
    intro s hs i hi
    rw [hbs, mv_eq_of_mem H hs hi]
    exact idxK_of_eq H.inc (field_lt H hs hi)
  have hS2 : gs.map (tableOf (Array.ofFn (n := N) fun i => TP i.val)) =
      Array.ofFn (n := gs.size) (fun s => tabP N (TG s.val)) := by
    apply Array.ext
    · simp
    · intro s h1 h2
      simp only [Array.getElem_map, Array.getElem_ofFn]
      unfold tableOf tabP
      apply Array.ext
      · simp
      · intro i hi1 hi2
        simp only [Array.getElem_map, Array.getElem_ofFn]
        have hi : i < N := by simpa using hi2
        rw [himg s (by simpa using h2) i hi]
  refine ⟨hsorted, ?_, ?_⟩
  · rw [hsorted]; exact hS2
  · have hgs : ∀ s (hs : s < gs.size), gs[s]! = gs[s] := fun s hs => getElem!_pos gs s hs
    have g1 : ∀ i, i < N → (Array.ofFn (n := N) fun i => TP i.val)[i]! = TP i :=
      fun i hi => CFSG.KS.TBfs.ofFn_get (f := TP) hi
    have g2 : ∀ s, s < gs.size →
        (Array.ofFn (n := gs.size) fun s => tabP N (TG s.val))[s]! = tabP N (TG s) :=
      fun s hs => CFSG.KS.TBfs.ofFn_get (f := fun s => tabP N (TG s)) hs
    unfold CFSG.SectionRank.Native.Tits.orbitOK
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, CFSG.KS.TBfs.allIn_iff]
    refine ⟨⟨⟨⟨by simp, by simp⟩, fun i hi => ?_⟩, fun i hi => ?_⟩, fun s hs i hi => ?_⟩
    · rw [g1 i hi]; exact H.lt i hi
    · rw [g1 i (by omega), g1 (i + 1) (by omega)]
      exact H.inc i (by omega)
    · have hs' : s < gs.size := hs
      rw [g2 s hs', toNat_tabP hi]
      refine ⟨field_lt H hs' hi, ?_⟩
      rw [g1 _ (field_lt H hs' hi), g1 i hi, hgs s hs', mv_eq_of_mem H hs' hi]

end Main

end CFSG.KC.LocalComp.TitsSound

end
