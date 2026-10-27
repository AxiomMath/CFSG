module

public import Certificates.Data.Kernel.LocalQT.Base
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative

import CFSG.Certificates.Kernel.LocalQTBfsClosedProved
import CFSG.Certificates.Kernel.LocalQTLatKSound

namespace CFSG.KC.LQT.BC.Pf

open CFSG.KC.Ord Equiv
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  (RN bfsSet bfsSet_sound mem_closure_iff_H rawIsEnc)

variable {n : Nat}

theorem img_lt32 (s i : Nat) : P.img s i < 32 := by
  rw [P.img_eq]
  exact Nat.mod_lt _ (by omega)

theorem img_ofFn {g : Nat → Nat} (hg : ∀ j < n, g j < 32) {i : Nat} (hi : i < n) :
    P.img (P.ofFn n g) i = g i := by
  rw [P.img_eq, P.ofFn_eq, P.E_digit hg hi]

theorem img_mul {s t i : Nat} (hi : i < n) : P.img (P.mul n s t) i = P.img s (P.img t i) :=
  img_ofFn (fun _ _ => img_lt32 _ _) hi

theorem img_one (hn : n ≤ 32) {i : Nat} (hi : i < n) : P.img (P.one n) i = i :=
  img_ofFn (fun j hj => by omega) hi

def Can (n c : Nat) : Prop := (∀ i < n, P.img c i < n) ∧ c = P.E (fun i => P.img c i) n

theorem can_ofFn (hn : n ≤ 32) {g : Nat → Nat} (hg : ∀ j < n, g j < n) :
    Can n (P.ofFn n g) := by
  have hg' : ∀ j < n, g j < 32 := fun j hj => Nat.lt_of_lt_of_le (hg j hj) hn
  refine ⟨fun i hi => by rw [img_ofFn hg' hi]; exact hg i hi, ?_⟩
  conv_lhs => rw [P.ofFn_eq]
  exact P.E_congr fun i hi => (img_ofFn hg' hi).symm

theorem codeL_eq : ∀ l : List Nat, codeL l = P.E (fun i => l.getD i 0) l.length
  | [] => (P.E_zero _).symm
  | x :: l => by
    have e : codeL (x :: l) = x + 32 * codeL l := by
      change Nat.add x (Nat.shiftLeft (codeL l) 5) = _
      change x + (codeL l <<< 5) = _
      rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 5 = 32 from rfl, Nat.mul_comm]
    rw [e, codeL_eq l, List.length_cons, P.E_succ_left]
    simp only [List.getD_cons_zero, List.getD_cons_succ]

def NodeRep (n c : Nat) (t : Array Nat) : Prop :=
  t.size = n ∧ Can n c ∧ ∀ i < n, P.img c i = img t i

theorem nodeRep_codeL (hn : n ≤ 32) {l : List Nat} (hl : tabL n l = true) :
    NodeRep n (codeL l) l.toArray := by
  obtain ⟨h1, h2⟩ := BW.Pf.tabL_spec hl
  have hval : ∀ i < n, l.getD i 0 < n := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact h2 _ (List.getElem_mem _)
  have himg : ∀ i < n, P.img (codeL l) i = l.getD i 0 := fun i hi => by
    rw [P.img_eq, codeL_eq,
      P.E_digit (fun j hj => Nat.lt_of_lt_of_le (hval j (by omega)) hn) (by omega)]
  have hget : ∀ i < n, img l.toArray i = l.getD i 0 := fun i _ => by
    rw [img, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  refine ⟨by simpa using h1, ⟨fun i hi => by rw [himg i hi]; exact hval i hi, ?_⟩,
    fun i hi => by rw [himg i hi, hget i hi]⟩
  conv_lhs => rw [codeL_eq, h1]
  exact P.E_congr fun i hi => (himg i hi).symm

theorem nodeRep_lt {c : Nat} {t : Array Nat} (h : NodeRep n c t) : ∀ i < n, img t i < n :=
  fun i hi => by rw [← h.2.2 i hi]; exact h.2.1.1 i hi

theorem nodeRep_mul (hn : n ≤ 32) {c d : Nat} {s t : Array Nat} (hc : NodeRep n c s)
    (hd : NodeRep n d t) : NodeRep n (P.mul n c d) (compArr s t) := by
  have htl := nodeRep_lt hd
  obtain ⟨hs, ⟨hc1, -⟩, hc2⟩ := hc
  obtain ⟨ht, ⟨hd1, -⟩, hd2⟩ := hd
  refine ⟨by simp [compArr, ht], can_ofFn hn fun j hj => hc1 _ (hd1 j hj), fun i hi => ?_⟩
  rw [BW.Pf.img_compArr hs ht htl hi, img_mul hi, hd2 i hi, hc2 _ (htl i hi)]

noncomputable def slpGoK (n : Nat) : List (Nat × Nat) → List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun p _ ih acc => ih (List.cons (P.mul n (nodeK acc p.1) (nodeK acc p.2)) acc))

theorem slpK_eq (n a b : Nat) (prog : List (Nat × Nat)) :
    slpK n a b prog = slpGoK n prog [b, a] := rfl

theorem slpGoK_cons (p : Nat × Nat) (l : List (Nat × Nat)) (acc : List Nat) :
    slpGoK n (p :: l) acc = slpGoK n l (P.mul n (nodeK acc p.1) (nodeK acc p.2) :: acc) := rfl

theorem slpGoK_rep (hn : n ≤ 32) : ∀ (l : List (Nat × Nat)) (acc : List Nat)
    (arr : Array (Array Nat)), acc.length = arr.size →
    (∀ j < arr.size, NodeRep n (nodeK acc j) arr[j]!) → slpValidAux l arr.size = true →
    (slpGoK n l acc).length = (l.foldl slpStepA arr).size ∧
      ∀ j < (l.foldl slpStepA arr).size,
        NodeRep n (nodeK (slpGoK n l acc) j) (l.foldl slpStepA arr)[j]!
  | [], acc, arr, hl, ha, _ => ⟨hl, ha⟩
  | p :: l, acc, arr, hl, ha, hv => by
    rw [slpValidAux, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hp1, hp2⟩, hv⟩ := hv
    rw [slpGoK_cons, List.foldl_cons]
    have hs : (slpStepA arr p).size = arr.size + 1 := by simp [slpStepA]
    apply slpGoK_rep hn l
    · simp [hs, hl]
    · intro j hj
      rw [hs] at hj
      unfold slpStepA
      rcases Nat.lt_or_ge j arr.size with hjk | hjk
      · rw [BW.Pf.nodeK_cons_lt _ _ (by omega), getElem!_pos _ j (by simp; omega),
          Array.getElem_push_lt hjk, ← getElem!_pos arr j hjk]
        exact ha j hjk
      · have e : j = arr.size := by omega
        subst e
        rw [← hl, BW.Pf.nodeK_cons_len, hl, getElem!_pos _ arr.size (by simp),
          Array.getElem_push_eq]
        exact nodeRep_mul hn (ha _ hp1) (ha _ hp2)
    · rw [hs]
      exact hv

theorem slpK_rep (hn : n ≤ 32) {ta tb : List Nat} (ha : tabL n ta = true)
    (hb : tabL n tb = true) {prog : List (Nat × Nat)} (hv : slpOKK prog 2 = true) :
    L.lenA (slpK n (codeL ta) (codeL tb) prog) = (slpTabsA ta.toArray tb.toArray prog).size ∧
      ∀ j < (slpTabsA ta.toArray tb.toArray prog).size,
        NodeRep n (nodeK (slpK n (codeL ta) (codeL tb) prog) j)
          (slpTabsA ta.toArray tb.toArray prog)[j]! := by
  rw [BW.Pf.lenA_eq, slpK_eq, slpTabsA]
  apply slpGoK_rep hn prog [codeL tb, codeL ta] #[ta.toArray, tb.toArray] rfl
  · intro j hj
    rcases j with _ | _ | j
    · exact nodeRep_codeL hn ha
    · exact nodeRep_codeL hn hb
    · simp at hj
  · exact BW.Pf.slpOKK_spec' prog 2 hv

theorem inv_of_mul (hn : n ≤ 32) {c d : Nat} {s t : Array Nat} (hc : NodeRep n c s)
    (hd : NodeRep n d t) (h : P.mul n d c = P.one n) : ∀ q < n, img t (img s q) = q := by
  intro q hq
  have e : P.img (P.mul n d c) q = P.img (P.one n) q := by rw [h]
  rw [img_mul hq, img_one hn hq, hc.2.2 q hq, hd.2.2 _ (nodeRep_lt hc q hq)] at e
  exact e

theorem exists_perm (hn : n ≤ 32) {c d : Nat} {s : Array Nat} (hc : NodeRep n c s)
    (h : P.mul n d c = P.one n) : ∃ σ : Perm (Fin n), P.code σ = c := by
  have hinv : ∀ q < n, P.img d (P.img c q) = q := fun q hq => by
    have e : P.img (P.mul n d c) q = P.img (P.one n) q := by rw [h]
    rwa [img_mul hq, img_one hn hq] at e
  let f : Fin n → Fin n := fun i => ⟨P.img c i, hc.2.1.1 i i.isLt⟩
  have hf : Function.Injective f := by
    intro i j hij
    have e := congrArg (fun x : Fin n => P.img d x) hij
    simp only [f] at e
    rw [hinv i i.isLt, hinv j j.isLt] at e
    exact Fin.ext e
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩
  rw [P.code_eq]
  refine Eq.trans ?_ hc.2.1.2.symm
  refine P.E_congr fun i hi => ?_
  exact (P.vals_fin _ ⟨i, hi⟩).trans (congrArg Fin.val (Equiv.ofBijective_apply f _ ⟨i, hi⟩))

theorem exists_perms {f : Nat × Nat → Nat} : ∀ qp : List (Nat × Nat),
    (∀ p ∈ qp, ∃ σ : Perm (Fin n), P.code σ = f p) →
    ∃ Lg : List (Perm (Fin n)), Lg.map P.code = qp.map f
  | [], _ => ⟨[], rfl⟩
  | p :: qp, h => by
    obtain ⟨σ, hσ⟩ := h p (List.mem_cons_self ..)
    obtain ⟨Lg, hL⟩ := exists_perms qp fun p' hp' => h p' (List.mem_cons_of_mem _ hp')
    exact ⟨σ :: Lg, by rw [List.map_cons, List.map_cons, hσ, hL]⟩

theorem img_code (hn : n ≤ 32) (σ : Perm (Fin n)) {i : Nat} (hi : i < n) :
    P.img (P.code σ) i = (σ ⟨i, hi⟩ : Nat) :=
  (P.img_code' hn σ hi).trans (P.vals_fin σ ⟨i, hi⟩)

theorem img_code_lt (hn : n ≤ 32) (σ : Perm (Fin n)) {i : Nat} (hi : i < n) :
    P.img (P.code σ) i < n := by
  rw [img_code hn σ hi]
  exact (σ ⟨i, hi⟩).isLt

theorem perm_ext_code (hn : n ≤ 32) {σ τ : Perm (Fin n)}
    (h : ∀ i < n, P.img (P.code σ) i = P.img (P.code τ) i) : σ = τ := by
  refine Equiv.ext fun i => Fin.ext ?_
  have := h i i.isLt
  rwa [img_code hn σ i.isLt, img_code hn τ i.isLt] at this

theorem ptsOf_lt {G : List (Array Nat)} (hG : ∀ s ∈ G, ∀ q < n, img s q < n) :
    ∀ p ∈ ptsOf (List.range n) G, p < n := by
  intro x hx
  rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
  rcases hx with hx | ⟨s, hs, hx⟩
  · exact List.mem_range.1 hx
  · rw [List.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact hG s hs b (List.mem_range.1 hb)

theorem ptsOf_length (G : List (Array Nat)) :
    (ptsOf (List.range n) G).length = n + n * G.length := by
  induction G with
  | nil => simp [ptsOf]
  | cons s G ih =>
    simp only [ptsOf, List.length_append, List.length_range, List.flatMap_cons,
      List.length_map] at ih ⊢
    rw [List.length_cons, Nat.mul_succ]
    omega

theorem ptsOf_getD {G : List (Array Nat)} {q : Nat} (hq : q < n) :
    (ptsOf (List.range n) G).getD q 0 = q := by
  rw [ptsOf, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
    List.getElem?_range hq, Option.getD_some]

theorem flatMap_getD : ∀ (G : List (Array Nat)) {t j : Nat}, t < G.length → j < n →
    (G.flatMap fun s => (List.range n).map (img s)).getD (n * t + j) 0 = img (G.getD t #[]) j
  | [], t, j, ht, _ => by simp at ht
  | s :: G, t, j, ht, hj => by
    rw [List.flatMap_cons]
    cases t with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range hj]
      rfl
    | succ t =>
      have hlen : ((List.range n).map (img s)).length = n := by simp
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [hlen, Nat.mul_succ]; omega),
        hlen, show n * (t + 1) + j - n = n * t + j by rw [Nat.mul_succ]; omega,
        ← List.getD_eq_getElem?_getD, flatMap_getD G (by simp at ht; omega) hj, List.getD_cons_succ]

theorem ptsOf_getD_gen {G : List (Array Nat)} {t j : Nat} (ht : t < G.length) (hj : j < n) :
    (ptsOf (List.range n) G).getD (n * (1 + t) + j) 0 = img (G.getD t #[]) j := by
  have hlen : (List.range n).length = n := List.length_range
  rw [ptsOf, List.getD_eq_getElem?_getD, List.getElem?_append_right
    (by rw [hlen, Nat.mul_add, Nat.mul_one]; omega), hlen,
    show n * (1 + t) + j - n = n * t + j by rw [Nat.mul_add, Nat.mul_one]; omega,
    ← List.getD_eq_getElem?_getD, flatMap_getD G ht hj]

theorem getD_map_lt {f : Nat → Nat} {l : List Nat} {i : Nat} (hi : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

end CFSG.KC.LQT.BC.Pf

public section

namespace CFSG.KC.LQT.BC

open CFSG.KC.Ord Equiv CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.LQT.BC.Pf
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  (RN bfsSet bfsSet_sound mem_closure_iff_H rawIsEnc)

theorem base_sound_proved {n : Nat} (hn : n ≤ 24) (ta tb : List Nat) (prog : List (Nat × Nat))
    (qp : List (Nat × Nat)) (zn gn gin hn' hin k fuel d : Nat)
    (h : baseK n ta tb prog qp zn gn gin hn' hin k fuel d = true) :
    BaseCertS n (List.range n) (slpTabsA ta.toArray tb.toArray prog) qp zn gn gin hn' hin
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 k := by
  classical
  have h32 : n ≤ 32 := by omega
  rw [baseK, BW.Pf.andB_eq, BW.Pf.andB_eq, BW.Pf.andB_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨hta, htb, hso, hR⟩ := h
  obtain ⟨hlen, hrep⟩ := slpK_rep h32 hta htb hso
  generalize slpTabsA ta.toArray tb.toArray prog = T at hlen hrep ⊢
  generalize slpK n (codeL ta) (codeL tb) prog = R at hlen hrep hR
  rw [baseR, BW.Pf.andB_eq, BW.Pf.andB_eq, BW.Pf.andB_eq, BW.Pf.andB_eq, BW.Pf.andB_eq,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hR
  obtain ⟨hqp, hbd, hqi, hg, hh, hQ⟩ := hR
  rw [P.letB_eq, P.letB_eq, P.letB_eq, LK.recMap] at hQ
  rw [BW.Pf.allA_eq, List.all_eq_true] at hqp hqi
  simp only [BW.Pf.allBs_cons, BW.Pf.allBs_nil, Bool.and_true, Bool.and_eq_true, Nat.blt_eq,
    hlen] at hbd
  obtain ⟨hzn, hgn, hgin, hhn, hhin⟩ := hbd
  have hq1 : ∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size := by
    intro p hp
    have := hqp p hp
    rw [BW.Pf.andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, hlen] at this
    exact this
  have hqi' : ∀ p ∈ qp, P.mul n (nodeK R p.2) (nodeK R p.1) = P.one n := fun p hp =>
    P.beq_iff.1 (hqi p hp)
  obtain ⟨Lg, hL⟩ : ∃ Lg : List (Perm (Fin n)), Lg.map P.code = qp.map fun p => nodeK R p.1 :=
    exists_perms qp fun p hp => exists_perm h32 (hrep _ (hq1 p hp).1) (hqi' p hp)
  rw [← hL] at hQ
  rw [baseQ] at hQ
  simp only [BW.Pf.allBs_cons, BW.Pf.allBs_nil, Bool.and_true, Bool.and_eq_true] at hQ
  obtain ⟨hcl, hsz, hfu, hcen, hmg, hmh, hnc⟩ := hQ
  set H := Subgroup.closure {g | g ∈ Lg} with hHdef
  have hcl' : CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.closedH (Lg.map RN.enc)
      (bfsSet (Lg.map RN.enc) d) = true := by
    rw [LK.closedK_iff h32] at hcl
    exact hcl
  have hmemH : ∀ σ : Perm (Fin n), σ ∈ H ↔ RN.enc σ ∈ bfsSet (Lg.map RN.enc) d :=
    mem_closure_iff_H (rawIsEnc n) Lg d hcl'
  have hsoundE : ∀ r ∈ bfsSet (Lg.map RN.enc) d, ∃ σ ∈ H, RN.enc σ = r :=
    bfsSet_sound (rawIsEnc n) Lg d
  have hcard : (L.bfsK n (Lg.map P.code) d).size = (bfsSet (Lg.map RN.enc) d).size :=
    LK.sizeK_eq h32 Lg d
  have hK2 : ∀ σ ∈ H, (∀ τ ∈ Lg, σ * τ = τ * σ) →
      P.code σ = P.one n ∨ P.code σ = nodeK R zn := by
    intro σ hσ hc
    have := (LK.allK_iff h32 Lg d _).1 hcen (RN.enc σ) ((hmemH σ).1 hσ)
    rw [L.rnc_enc, P.impB_iff, P.orB_iff, P.beq_iff, P.beq_iff] at this
    apply this
    rw [P.allL_iff]
    intro g hg
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hg
    rw [P.beq_iff, P.code_mul h32, P.code_mul h32, hc τ hτ]
  have hK3 : ∀ x, L.memT (L.bfsK n (Lg.map P.code) d).t x = true → ∃ σ ∈ H, P.code σ = x := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := (L.rep_memT (L.rep_bfsK h32 Lg d) x).1 hx
    obtain ⟨σ, hσ, rfl⟩ := hsoundE r hr
    exact ⟨σ, hσ, (L.rnc_enc σ).symm⟩
  set G := qp.map fun p => T[p.1]! with hGdef
  set Gi := qp.map fun p => T[p.2]! with hGidef
  have hGl : G.length = qp.length := by rw [hGdef, List.length_map]
  have hGil : Gi.length = qp.length := by rw [hGidef, List.length_map]
  have hsG : ∀ s ∈ G, ∃ τ ∈ Lg, ∀ q < n, img s q = P.img (P.code τ) q := by
    intro s hs
    rw [hGdef, List.mem_map] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    have hmem : nodeK R p.1 ∈ Lg.map P.code := by
      rw [hL]
      exact List.mem_map_of_mem hp
    obtain ⟨τ, hτ, e⟩ := List.mem_map.1 hmem
    exact ⟨τ, hτ, fun q hq => by rw [e]; exact ((hrep _ (hq1 p hp).1).2.2 q hq).symm⟩
  have hGlt : ∀ s ∈ G, ∀ q < n, img s q < n := fun s hs q hq => by
    obtain ⟨τ, -, e⟩ := hsG s hs
    rw [e q hq]
    exact img_code_lt h32 τ hq
  have hGs : ∀ τ ∈ Lg, ∃ s ∈ G, ∀ q < n, img s q = P.img (P.code τ) q := by
    intro τ hτ
    have hmem : P.code τ ∈ qp.map fun p => nodeK R p.1 := by
      rw [← hL]
      exact List.mem_map_of_mem hτ
    obtain ⟨p, hp, e⟩ := List.mem_map.1 hmem
    refine ⟨T[p.1]!, ?_, fun q hq => ?_⟩
    · rw [hGdef]
      exact List.mem_map_of_mem hp
    · rw [← e]
      exact ((hrep _ (hq1 p hp).1).2.2 q hq).symm
  have hGj : ∀ j (hj : j < qp.length), G[j]! = T[qp[j].1]! := by
    intro j hj
    rw [getElem!_pos G j (by omega)]
    simp only [hGdef, List.getElem_map]
  have hGij : ∀ j (hj : j < qp.length), Gi[j]! = T[qp[j].2]! := by
    intro j hj
    rw [getElem!_pos Gi j (by omega)]
    simp only [hGidef, List.getElem_map]
  have hinvG : ∀ j < G.length, ∀ q < n, img Gi[j]! (img G[j]! q) = q := by
    intro j hj q hq
    have hjq : j < qp.length := by omega
    rw [hGj j hjq, hGij j hjq]
    have hp := List.getElem_mem hjq
    exact inv_of_mul h32 (hrep _ (hq1 _ hp).1) (hrep _ (hq1 _ hp).2) (hqi' _ hp) q hq
  have hpts : ∀ p ∈ ptsOf (List.range n) G, p < n := ptsOf_lt hGlt
  set rt : Perm (Fin n) → List Nat := fun σ => (ptsOf (List.range n) G).map (P.img (P.code σ))
    with hrt
  have hrt_val : ∀ σ, BW.Pf.Val n (ptsOf (List.range n) G).length (rt σ) := fun σ => by
    refine ⟨by simp only [hrt, List.length_map], fun x hx => ?_⟩
    simp only [hrt, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact img_code_lt h32 σ (hpts p hp)
  have hrt_getD : ∀ σ, ∀ q < n, (rt σ).getD q 0 = P.img (P.code σ) q := fun σ q hq => by
    simp only [hrt]
    rw [getD_map_lt (by rw [ptsOf_length]; omega), ptsOf_getD hq]
  have hrt_inj : ∀ σ τ, rt σ = rt τ → σ = τ := fun σ τ e =>
    perm_ext_code h32 fun i hi => by rw [← hrt_getD σ i hi, ← hrt_getD τ i hi, e]
  have hrt_one : rt 1 = ptsOf (List.range n) G := by
    simp only [hrt]
    conv_rhs => rw [← List.map_id (ptsOf (List.range n) G)]
    apply List.map_congr_left
    intro p hp
    rw [← P.code_one, img_one h32 (hpts p hp)]
    rfl
  have hrt_mul : ∀ (s : Array Nat) (τ σ : Perm (Fin n)),
      (∀ q < n, img s q = P.img (P.code τ) q) → applyTab s (rt σ) = rt (τ * σ) := by
    intro s τ σ hs
    simp only [hrt, applyTab, List.map_map]
    apply List.map_congr_left
    intro p hp
    rw [Function.comp_apply, hs _ (img_code_lt h32 σ (hpts p hp)), ← P.code_mul h32,
      img_mul (hpts p hp)]
  set E := bfsSet (Lg.map RN.enc) d with hEdef
  set Ul := E.toList.map fun r => (ptsOf (List.range n) G).map (P.img (L.rnc r)) with hUldef
  have hUl : ∀ T', T' ∈ Ul ↔ ∃ σ ∈ H, T' = rt σ := by
    intro T'
    rw [hUldef, List.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨σ, hσ, rfl⟩ := hsoundE r (Std.HashSet.mem_toList.1 hr)
      exact ⟨σ, hσ, by simp only [hrt, L.rnc_enc]⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨RN.enc σ, Std.HashSet.mem_toList.2 ((hmemH σ).1 hσ), by simp only [hrt, L.rnc_enc]⟩
  have hUlen : Ul.length = (L.bfsK n (Lg.map P.code) d).size := by
    rw [hUldef, List.length_map, Std.HashSet.length_toList, hcard]
  have hUnd : Ul.Nodup := by
    rw [hUldef]
    refine List.Nodup.map_on ?_ (L.toList_nodup E)
    intro r hr r' hr' e
    obtain ⟨σ, -, rfl⟩ := hsoundE r (Std.HashSet.mem_toList.1 hr)
    obtain ⟨σ', -, rfl⟩ := hsoundE r' (Std.HashSet.mem_toList.1 hr')
    have : rt σ = rt σ' := by
      simp only [hrt, ← L.rnc_enc]
      exact e
    rw [hrt_inj σ σ' this]
  have hclo : ∀ T' ∈ Ul, ∀ s ∈ G, applyTab s T' ∈ Ul := by
    intro T' hT' s hs
    obtain ⟨σ, hσ, rfl⟩ := (hUl T').1 hT'
    obtain ⟨τ, hτ, hsτ⟩ := hsG s hs
    rw [hrt_mul s τ σ hsτ]
    exact (hUl _).2 ⟨τ * σ, H.mul_mem (Subgroup.subset_closure hτ) hσ, rfl⟩
  have hkey : ∀ T' ∈ Ul, ∀ V ∈ Ul, keyNat n (List.range n).length T' =
      keyNat n (List.range n).length V → T' = V := by
    intro T' hT' V hV e
    obtain ⟨σ, -, rfl⟩ := (hUl T').1 hT'
    obtain ⟨τ, -, rfl⟩ := (hUl V).1 hV
    rw [BW.Pf.keyNat_eq_iff (hrt_val σ) (hrt_val τ), List.length_range] at e
    have hst : σ = τ := perm_ext_code h32 fun q hq => by
      have := congrArg (fun l => l.getD q 0) e
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hq] at this
      rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, hrt_getD σ q hq,
        hrt_getD τ q hq] at this
      exact this
    rw [hst]
  have hreach : ∀ A : List (List Nat), ptsOf (List.range n) G ∈ A →
      (∀ T' ∈ A, T' ∈ Ul → ∀ s ∈ G, applyTab s T' ∈ A) → ∀ T' ∈ Ul, T' ∈ A := by
    intro A hoA hA T' hT'
    obtain ⟨σ, hσ, rfl⟩ := (hUl T').1 hT'
    have hstep : ∀ x ∈ Lg, ∀ y ∈ H, rt y ∈ A → rt (x * y) ∈ A := by
      intro x hx y hy hyA
      obtain ⟨s, hs, hsx⟩ := hGs x hx
      rw [← hrt_mul s x y hsx]
      exact hA _ hyA ((hUl _).2 ⟨y, hy, rfl⟩) s hs
    have hpow : ∀ x ∈ Lg, ∀ m : Nat, ∀ y ∈ H, rt y ∈ A → rt (x ^ m * y) ∈ A := by
      intro x hx m
      induction m with
      | zero => intro y _ hyA; rwa [pow_zero, one_mul]
      | succ m ih =>
        intro y hy hyA
        rw [pow_succ, mul_assoc]
        exact ih _ (H.mul_mem (Subgroup.subset_closure hx) hy) (hstep x hx y hy hyA)
    refine Subgroup.closure_induction_left (p := fun σ _ => rt σ ∈ A) ?_ ?_ ?_ hσ
    · rw [hrt_one]
      exact hoA
    · intro x hx y hy hyA
      exact hstep x hx y hy hyA
    · intro x hx y hy hyA
      have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
        refine (eq_inv_of_mul_eq_one_left ?_).symm
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
      rw [hinv]
      exact hpow x hx _ y hy hyA
  have hfuel : Ul.length ≤ fuel := by
    rw [hUlen]
    exact Nat.le_of_ble_eq_true hfu
  obtain ⟨hEnum, hsize, hmemTs⟩ := BS.Cl.bfs_closed (n := n)
    (L := (ptsOf (List.range n) G).length) (B := List.range n) (G := G) (Gi := Gi) (Ul := Ul)
    fuel (by rw [hGl, hGil]) hinvG
    (fun T' hT' => by obtain ⟨σ, -, rfl⟩ := (hUl T').1 hT'; exact hrt_val σ)
    hclo hkey ((hUl _).2 ⟨1, H.one_mem, hrt_one.symm⟩) hUnd hreach hfuel
  have hconj : ∀ {zc gc gic : Nat} {zt gt git : Array Nat}, NodeRep n zc zt → NodeRep n gc gt →
      NodeRep n gic git → ∀ p < n,
        conjImg zt gt git p = P.img (P.mul n gic (P.mul n zc gc)) p := by
    intro zc gc gic zt gt git hz hg' hgi p hp
    rw [conjImg, img_mul hp, img_mul hp, hg'.2.2 p hp, hz.2.2 _ (nodeRep_lt hg' p hp),
      hgi.2.2 _ (nodeRep_lt hz _ (nodeRep_lt hg' p hp))]
  obtain ⟨σg, hσg, hcg⟩ := hK3 _ hmg
  obtain ⟨σh, hσh, hch⟩ := hK3 _ hmh
  have hcg' : ∀ p < n, conjImg T[zn]! T[gn]! T[gin]! p = P.img (P.code σg) p := fun p hp => by
    rw [hconj (hrep zn hzn) (hrep gn hgn) (hrep gin hgin) p hp, hcg]
  have hch' : ∀ p < n, conjImg T[zn]! T[hn']! T[hin]! p = P.img (P.code σh) p := fun p hp => by
    rw [hconj (hrep zn hzn) (hrep hn' hhn) (hrep hin hhin) p hp, hch]
  unfold BaseCertS
  refine ⟨hq1, hzn, hgn, hgin, hhn, hhin, ?_⟩
  have hm1 : (qp.map fun p => (T[p.1]!, T[p.2]!)).map Prod.fst = G := by
    rw [List.map_map, hGdef]
    rfl
  have hm2 : (qp.map fun p => (T[p.1]!, T[p.2]!)).map Prod.snd = Gi := by
    rw [List.map_map, hGidef]
    rfl
  unfold BaseCert
  rw [hm1, hm2]
  refine ⟨?_, inv_of_mul h32 (hrep gn hgn) (hrep gin hgin) (P.beq_iff.1 hg),
    inv_of_mul h32 (hrep hn' hhn) (hrep hin hhin) (P.beq_iff.1 hh), hEnum, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq
    rw [List.mem_map] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact inv_of_mul h32 (hrep _ (hq1 a ha).1) (hrep _ (hq1 a ha).2) (hqi' a ha) q hq
  · rw [hsize, hUlen]
    exact Nat.eq_of_beq_eq_true hsz
  · intro T' hT' hcond
    obtain ⟨σ, hσ, rfl⟩ := (hUl T').1 ((hmemTs T').1 hT')
    have hcomm : ∀ τ ∈ Lg, σ * τ = τ * σ := by
      intro τ hτ
      have hmem : P.code τ ∈ qp.map fun p => nodeK R p.1 := by
        rw [← hL]
        exact List.mem_map_of_mem hτ
      obtain ⟨p, hp, e⟩ := List.mem_map.1 hmem
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hp
      have hGt : G.getD t #[] = T[qp[t].1]! := by
        rw [hGdef, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht]
        rfl
      have himgt : ∀ q < n, img (G.getD t #[]) q = P.img (P.code τ) q := fun q hq => by
        rw [hGt, ← e]
        exact ((hrep _ (hq1 _ hp).1).2.2 q hq).symm
      refine perm_ext_code h32 fun q hq => ?_
      have hc := hcond t (by rw [hGl]; exact ht) q (by rw [List.length_range]; exact hq)
      have hbound : n * (1 + t) + q < (ptsOf (List.range n) G).length := by
        rw [ptsOf_length, hGl]
        have h1 : n * (1 + t) = n + n * t := by rw [Nat.mul_add, Nat.mul_one]
        have h2 : n * (t + 1) ≤ n * qp.length := Nat.mul_le_mul_left n (Nat.succ_le_of_lt ht)
        rw [Nat.mul_succ] at h2
        rw [h1]
        omega
      simp only [List.length_range] at hc
      have e1 : (rt σ).getD (n * (1 + t) + q) 0 = P.img (P.code σ) (P.img (P.code τ) q) := by
        simp only [hrt]
        rw [getD_map_lt hbound, ptsOf_getD_gen (by rw [hGl]; exact ht) hq, himgt q hq]
      rw [e1, hrt_getD σ q hq, himgt _ (img_code_lt h32 σ hq)] at hc
      rw [← P.code_mul h32, ← P.code_mul h32, img_mul hq, img_mul hq]
      exact hc
    rcases hK2 σ hσ hcomm with h1 | h1
    · left
      rw [P.code_one] at h1
      rw [P.code_inj h32 h1, hrt_one]
    · right
      simp only [hrt, applyTab]
      apply List.map_congr_left
      intro p hp
      rw [h1, (hrep zn hzn).2.2 p (hpts p hp)]
  · rw [hmemTs, hUl]
    refine ⟨σg, hσg, ?_⟩
    simp only [hrt]
    apply List.map_congr_left
    intro p hp
    exact hcg' p (hpts p hp)
  · rw [hmemTs, hUl]
    refine ⟨σh, hσh, ?_⟩
    simp only [hrt]
    apply List.map_congr_left
    intro p hp
    exact hch' p (hpts p hp)
  · rw [P.notB_iff, P.beq_iff] at hnc
    rw [← hcg, ← hch, P.code_mul h32, P.code_mul h32] at hnc
    have hne : σg * σh ≠ σh * σg := fun e => hnc (by rw [e])
    obtain ⟨q, hq⟩ : ∃ q : Fin n, (σg * σh) q ≠ (σh * σg) q := by
      by_contra hall
      push Not at hall
      exact hne (Equiv.ext hall)
    refine ⟨q, by rw [List.length_range]; exact q.isLt, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_range q.isLt, Option.getD_some]
    have hcg2 : ∀ x : Fin n, conjImg T[zn]! T[gn]! T[gin]! x = σg x := fun x => by
      rw [hcg' x x.isLt]
      exact img_code h32 σg x.isLt
    have hch2 : ∀ x : Fin n, conjImg T[zn]! T[hn']! T[hin]! x = σh x := fun x => by
      rw [hch' x x.isLt]
      exact img_code h32 σh x.isLt
    rw [hch2 q, hcg2 q, hcg2 (σh q), hch2 (σg q)]
    exact fun e => hq (Fin.ext e)

end CFSG.KC.LQT.BC

end
