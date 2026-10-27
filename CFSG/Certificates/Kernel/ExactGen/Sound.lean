module

public import Certificates.Data.Kernel.ExactGen.Defs
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.Fi22Rk.Side
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.ExactGen

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

variable {n w : ℕ} (hw : szOK n w = true)

def CB (n w : ℕ) (cd : ChainData) : Prop :=
  ∀ j < cd.S.size, cd.S[j]! = unpack n w (SC w cd j) ∧ permB n w (SC w cd j) = true

theorem cb_of {cd : ChainData} (h : chainBK n w cd = true) : CB n w cd := by
  intro j hj
  have h1 := List.all_eq_true.1 h j (List.mem_range.2 hj)
  unfold bndA at h1
  rw [Bool.and_eq_true] at h1
  exact ⟨arrBind_sound h1.1, h1.2⟩

include hw in
theorem cb_inv {cd : ChainData} (hc : CB n w cd) :
    ∀ j < cd.S.size, (rawInvs n cd.S)[j]! = unpack n w (SIC n w cd j) ∧
      permB n w (SIC n w cd j) = true := by
  intro j hj
  obtain ⟨e, hp⟩ := hc j hj
  refine ⟨?_, permB_pinvS hw hp⟩
  unfold rawInvs
  rw [getElem!_map_inv n cd.S hj, e]
  exact invCand_PP (pp_of_permB hw hp)

include hw in
theorem wordArr_eq {cd : ChainData} (hc : CB n w cd) {wd : List ℤ}
    (hl : lettersOK cd.S.size wd = true) : cd.wordArr n wd = unpack n w (wK n w cd wd) :=
  wordA_unpack hw (fun h hh => (hc h hh).1) (fun h hh => (cb_inv hw hc h hh).1)
    (fun h hh => (hc h hh).2) (fun h hh => (cb_inv hw hc h hh).2) hl

include hw in
theorem permB_wK {cd : ChainData} (hc : CB n w cd) {wd : List ℤ}
    (hl : lettersOK cd.S.size wd = true) : permB n w (wK n w cd wd) = true :=
  permB_wordK hw (fun h hh => (hc h hh).2) (fun h hh => (cb_inv hw hc h hh).2) hl

include hw in
theorem eqA_pk {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    eqA n (unpack n w p) (unpack n w q) = Nat.beq p q := eqA_unpack' hw hp hq

include hw in
theorem compA_pk {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    compA n (unpack n w p) (unpack n w q) = unpack n w (pc n w p q) := comp_unpack' hw hp hq

include hw in
theorem permB_pc {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    permB n w (pc n w p q) = true := permB_pcomp hw hp hq

include hw in
theorem idA_pk : idA n = unpack n w (pid n w) := idA_eq hw

include hw in
theorem permB_pid : permB n w (pid n w) = true := permB_of_pp (PP.id hw)

theorem get_pk {P i : ℕ} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i :=
  CFSG.KC.Fi22RkS.get_unpack hi

theorem eqA_of_beq {p q : ℕ} (h : Nat.beq p q = true) :
    eqA n (unpack n w p) (unpack n w q) = true := by
  rw [Nat.eq_of_beq_eq_true h]
  unfold eqA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem beq_of_nbeq {a b : ℕ} (h : Nat.beq a b = true) : (a == b) = true :=
  beq_iff_eq.2 (Nat.eq_of_beq_eq_true h)

include hw in
theorem origs_of {H amb : ChainData} {ws : List (List ℤ)} (hH : CB n w H) (hA : CB n w amb)
    (hk : H.k ≤ H.S.size) (h : origsK n w H amb ws = true) : ChainData.origsOK n H amb ws = true := by
  unfold origsK at h
  unfold ChainData.origsOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun i hi => ?_⟩
  obtain ⟨hl, he⟩ := h2 i hi
  obtain ⟨e, hp⟩ := hH i (lt_of_lt_of_le hi hk)
  refine ⟨hl, ?_⟩
  rw [e, wordArr_eq hw hA hl, eqA_pk hw hp (permB_wK hw hA hl)]
  exact he

include hw in
theorem ctx_of {c : Ctx} (hP : c.chP.check n = true) (hN : c.chN.check n = true)
    (hcP : CB n w c.chP) (hcN : CB n w c.chN) (h : ctxK n w c = true) : c.ok n = true := by
  have hkP := ChainData.k_le_size n hP
  have hkN := ChainData.k_le_size n hN
  unfold ctxK at h
  unfold Ctx.ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h3, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hP, hN⟩, h3⟩, h4⟩, fun i hi => ?_⟩, fun a ha p hp => ?_⟩, h7⟩, fun ω hω => ?_⟩,
    fun j hj => ?_⟩, fun ω hω => ?_⟩, h11⟩
  · obtain ⟨eN, -⟩ := hcN i (by omega)
    obtain ⟨eP, -⟩ := hcP i (by omega)
    rw [eN, eP, Nat.eq_of_beq_eq_true (h5 i hi)]
    exact beq_self_eq_true _
  · obtain ⟨hl, he⟩ := h6 a ha p hp
    refine ⟨hl, ?_⟩
    obtain ⟨eN, pN⟩ := hcN (c.chP.k + a) (by omega)
    obtain ⟨eNi, pNi⟩ := cb_inv hw hcN (c.chP.k + a) (by omega)
    obtain ⟨eP, pP⟩ := hcP p (by omega)
    unfold conjArr
    rw [eN, eNi, eP, compA_pk hw pN pP, compA_pk hw (permB_pc hw pN pP) pNi,
      wordArr_eq hw hcP hl, eqA_pk hw (permB_pc hw (permB_pc hw pN pP) pNi) (permB_wK hw hcP hl)]
    exact he
  · obtain ⟨hl, he⟩ := h8 ω hω
    refine ⟨hl, ?_⟩
    rw [wordArr_eq hw hcP hl, get_pk h11]
    exact beq_of_nbeq he
  · obtain ⟨⟨hj0, hjs⟩, he⟩ := h9 j hj
    refine ⟨⟨hj0, hjs⟩, ?_⟩
    rw [(hcP (j - 1) (by omega)).1, get_pk h11]
    exact beq_of_nbeq he
  · have h10' := h10 ω hω
    rw [Bool.or_eq_true] at h10' ⊢
    rcases h10' with e | e
    · exact Or.inl e
    · right
      obtain ⟨j, hj, hb⟩ := List.any_eq_true.1 e
      refine List.any_eq_true.2 ⟨j, hj, ?_⟩
      obtain ⟨⟨hj0, hjs⟩, -⟩ := h9 j hj
      rw [(hcP (j - 1) (by omega)).1, get_pk hω, bne_iff_ne]
      intro e'
      rw [e', Nat.beq_refl] at hb
      exact absurd hb (by decide)

theorem hash_pk (P : ℕ) : hashN n (unpack n w P) = hashK n w P := by
  unfold hashN hashK
  refine List.foldl_ext _ _ _ fun acc i hi => ?_
  rw [get_pk (List.mem_range.1 hi)]

theorem getElem!_mem {α : Type} [Inhabited α] {l : List α} {i : ℕ} (hi : i < l.length) :
    l[i]! ∈ l := by
  rw [getElem!_pos l i hi]
  exact List.getElem_mem hi

include hw in
theorem cover_of {T K : ChainData} {cc : CoverCert} {nrep : ℕ} {repA : ℕ → Array ℕ}
    {repK : ℕ → ℕ} {oT : ℕ} (hT : T.check n = true) (hK : K.check n = true) (hcT : CB n w T)
    (hcK : CB n w K) (hTo : T.order n = oT)
    (hrep : ∀ j, 1 ≤ j → j ≤ nrep → repA j = unpack n w (repK j))
    (h : coverK n w T K cc nrep repK oT = true) : cc.ok n T K nrep repA = true := by
  unfold coverK at h
  unfold CoverCert.ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨hl, hs⟩, hlen⟩, hcj⟩, hall⟩ := h
  have hm : (cc.ws.map fun wd => hashN n (T.wordArr n wd)) =
      cc.ws.map fun wd => hashK n w (wK n w T wd) :=
    List.map_congr_left fun wd hwd => by rw [wordArr_eq hw hcT (hl wd hwd), hash_pk]
  refine ⟨⟨⟨⟨⟨⟨hT, hK⟩, hl⟩, hm ▸ hs⟩, hTo ▸ Nat.eq_of_beq_eq_true hlen⟩,
    Nat.eq_of_beq_eq_true hcj⟩, fun i hi => ?_⟩
  have hwl := hl _ (getElem!_mem hi)
  have eV := wordArr_eq hw hcT hwl
  have pV := permB_wK hw hcT hwl
  have hi' := hall i hi
  rw [eV, compA_pk hw pV pV, idA_pk hw, eqA_pk hw (permB_pc hw pV pV) (permB_pid hw),
    eqA_pk hw pV (permB_pid hw)]
  rw [Bool.or_eq_true, Bool.or_eq_true] at hi' ⊢
  rcases hi' with (a | a) | a
  · exact Or.inl (Or.inl a)
  · exact Or.inl (Or.inr a)
  · right
    simp only [Bool.and_eq_true, decide_eq_true_eq] at a ⊢
    obtain ⟨⟨⟨hj, hlc⟩, hinv⟩, heq⟩ := a
    have eK := wordArr_eq hw hcK hlc
    have pK := permB_wK hw hcK hlc
    have eKi := wordArr_eq hw hcK (lettersOK_winv hlc)
    have pKi := permB_wK hw hcK (lettersOK_winv hlc)
    refine ⟨⟨⟨hj, hlc⟩, ?_⟩, ?_⟩
    · unfold invPair
      rw [eK, eKi, compA_pk hw pK pKi, idA_pk hw, eqA_pk hw (permB_pc hw pK pKi) (permB_pid hw)]
      exact hinv
    · unfold conjArr
      rw [hrep _ hj.1 hj.2, eK, eKi, compA_pk hw pK pV, compA_pk hw (permB_pc hw pK pV) pKi]
      exact eqA_of_beq heq

theorem lettersOK_single {j : ℕ} {l : ℤ} : lettersOK j [l] = true ↔ l ≠ 0 ∧ l.natAbs ≤ j := by
  simp [lettersOK]

include hw in
theorem letterA_pk {cd : ChainData} (hc : CB n w cd) {l : ℤ}
    (hl : lettersOK cd.S.size [l] = true) :
    letterA cd.S (rawInvs n cd.S) l = unpack n w (letK n w cd l) ∧
      permB n w (letK n w cd l) = true := by
  obtain ⟨h0, hle⟩ := lettersOK_single.1 hl
  unfold letterA letK
  by_cases hp : 0 < l
  · rw [if_pos hp, if_pos hp]
    exact hc _ (by omega)
  · rw [if_neg hp, if_neg hp]
    exact cb_inv hw hc _ (by omega)

include hw in
include hw in
theorem bfsAux_pk {cd : ChainData} (hc : CB n w cd) {BT : ℕ → ℕ} :
    ∀ (par : List (ℕ × ℤ)) (m : ℕ) (L : Array (Array ℕ)), L.size = m + 1 →
      (∀ i < m + 1, L[i]! = unpack n w (BT i) ∧ permB n w (BT i) = true) →
      bfsOK cd.S.size par L.size = true → parOK n w cd BT m par = true →
      (bfsAux n cd.S (rawInvs n cd.S) par L).size = m + 1 + par.length ∧
        ∀ i < m + 1 + par.length, (bfsAux n cd.S (rawInvs n cd.S) par L)[i]! = unpack n w (BT i)
  | [], m, L, hs, hL, _, _ => ⟨hs, fun i hi => (hL i hi).1⟩
  | (p, l) :: rest, m, L, hs, hL, hok, hpar => by
    simp only [bfsOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hpl, hl⟩, hrest⟩ := hok
    unfold parOK at hpar
    rw [Bool.and_eq_true] at hpar
    obtain ⟨hpar1, hpar2⟩ := hpar
    have hl' : lettersOK cd.S.size [-l] = true := by
      obtain ⟨a, b⟩ := lettersOK_single.1 hl
      exact lettersOK_single.2 ⟨by omega, by omega⟩
    obtain ⟨e1, p1⟩ := letterA_pk hw hc hl
    obtain ⟨e2, p2⟩ := letterA_pk hw hc hl'
    obtain ⟨eY, pY⟩ := hL p (by omega)
    have hstep : conjArr n (letterA cd.S (rawInvs n cd.S) l) (letterA cd.S (rawInvs n cd.S) (-l))
        L[p]! = unpack n w (BT (m + 1)) := by
      unfold conjArr
      rw [e1, e2, eY, compA_pk hw p1 pY, compA_pk hw (permB_pc hw p1 pY) p2,
        Nat.eq_of_beq_eq_true hpar1]
    have pN : permB n w (BT (m + 1)) = true := by
      rw [Nat.eq_of_beq_eq_true hpar1]
      exact permB_pc hw (permB_pc hw p1 pY) p2
    have hL' : ∀ i < m + 1 + 1, (L.push (conjArr n (letterA cd.S (rawInvs n cd.S) l)
        (letterA cd.S (rawInvs n cd.S) (-l)) L[p]!))[i]! = unpack n w (BT i) ∧
        permB n w (BT i) = true := by
      intro i hi
      by_cases h : i < m + 1
      · rw [getElem!_pos _ i (by simp; omega), Array.getElem_push_lt (by omega),
          ← getElem!_pos L i (by omega)]
        exact hL i h
      · have e : i = L.size := by omega
        subst e
        rw [getElem!_pos _ L.size (by simp), Array.getElem_push_eq, hstep, ← hs]
        exact ⟨rfl, hs ▸ pN⟩
    have ih := bfsAux_pk hc rest (m + 1) _ (by simp [hs]) hL' (by simpa [hs] using hrest) hpar2
    have e : m + 1 + 1 + rest.length = m + 1 + ((p, l) :: rest).length := by simp; omega
    rw [e] at ih
    exact ih

include hw in
theorem bfs_of {cd : ChainData} (hc : CB n w cd) {seed : ℕ} (hs : permB n w seed = true)
    {par : List (ℕ × ℤ)} {ord : List ℕ} {BT : ℕ → ℕ} (h : bfsK n w cd seed par ord BT = true) :
    bfsCheck n cd.S (unpack n w seed) par ord = true := by
  unfold bfsK at h
  unfold bfsCheck
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨hok, hord⟩, h0⟩, hpar⟩, hinc⟩ := h
  have hL : ∀ i < 0 + 1, (#[unpack n w seed] : Array (Array ℕ))[i]! = unpack n w (BT i) ∧
      permB n w (BT i) = true := by
    intro i hi
    have e : i = 0 := by omega
    subst e
    rw [Nat.eq_of_beq_eq_true h0]
    exact ⟨rfl, hs⟩
  obtain ⟨-, e⟩ := bfsAux_pk hw hc par 0 _ rfl hL hok hpar
  refine ⟨⟨hok, hord⟩, ?_⟩
  have hm : (ord.map fun m => hashN n (bfsAux n cd.S (rawInvs n cd.S) par #[unpack n w seed])[m]!) =
      ord.map fun m => hashK n w (BT m) :=
    List.map_congr_left fun m hm => by
      rw [e m (by have := hord m hm; omega), hash_pk]
  rw [hm]
  exact hinc

theorem powA_eq (t : Array ℕ) : ∀ k, powA n t k = CFSG.Monster.B.Mathieu.powArr n t k
  | 0 => rfl
  | k + 1 => by
    change compA n t (powA n t k) = compA n t (CFSG.Monster.B.Mathieu.powArr n t k)
    rw [powA_eq t k]

include hw in
theorem pow_pk {p : ℕ} (hp : permB n w p = true) (k : ℕ) :
    powA n (unpack n w p) k = unpack n w (ppw n w p k) :=
  (powA_eq _ k).trans (pow_unpack' hw hp k)

include hw in
theorem permB_ppw {p : ℕ} (hp : permB n w p = true) (k : ℕ) : permB n w (ppw n w p k) = true :=
  permB_ppow hw hp k

theorem toArray_map_get {l : List ℕ} {j : ℕ} (hj : j < l.length) :
    (l.map (unpack n w)).toArray[j]! = unpack n w l[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), List.getElem_toArray, List.getElem_map,
    getElem!_pos l j hj]

include hw in
theorem ab_eq {chP chC : ChainData} {g : GenCert} (hcP : CB n w chP) (hcC : CB n w chC)
    (hA : ∀ x ∈ g.Aw, lettersOK chC.S.size x = true) (hB : ∀ x ∈ g.Bw, lettersOK chP.S.size x = true) :
    g.AB n chP chC = ((abK n w chP chC g).map (unpack n w)).toArray ∧
      ∀ x ∈ abK n w chP chC g, permB n w x = true := by
  refine ⟨?_, fun x hx => ?_⟩
  · unfold GenCert.AB abK
    rw [List.map_append, List.map_map, List.map_map]
    congr 2
    · exact List.map_congr_left fun x hx => wordArr_eq hw hcC (hA x hx)
    · exact List.map_congr_left fun x hx => wordArr_eq hw hcP (hB x hx)
  · unfold abK at hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact permB_wK hw hcC (hA y hy)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact permB_wK hw hcP (hB y hy)

include hw in
theorem gen_of {chP chC : ChainData} {g : GenCert} {nu enu : ℕ} (hP : chP.check n = true)
    (hcP : CB n w chP) (hcC : CB n w chC) (hnu : permB n w nu = true) (henu : permB n w enu = true)
    (h : genK n w chP chC g nu enu = true) : g.ok n chP chC (unpack n w nu) (unpack n w enu) = true := by
  have hk := ChainData.k_le_size n hP
  unfold genK at h
  unfold GenCert.ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨hAl, hBl⟩, hka⟩, hkb⟩, hA⟩, hB⟩, hpwl⟩, hpw⟩ := h
  obtain ⟨eAB, pAB⟩ := ab_eq hw hcP hcC hAl hBl
  have hsz : (g.AB n chP chC).size = (abK n w chP chC g).length := by rw [eAB]; simp
  have hget : ∀ j < (g.AB n chP chC).size, (g.AB n chP chC)[j]! = unpack n w (abK n w chP chC g)[j]! ∧
      permB n w (abK n w chP chC g)[j]! = true := fun j hj => by
    rw [hsz] at hj
    exact ⟨by rw [eAB]; exact toArray_map_get hj, pAB _ (getElem!_mem hj)⟩
  have hgeti : ∀ j < (g.AB n chP chC).size, ((g.AB n chP chC).map (invCand n))[j]! =
      unpack n w (pinvS n w (mask w) (abK n w chP chC g)[j]!) ∧
      permB n w (pinvS n w (mask w) (abK n w chP chC g)[j]!) = true := fun j hj => by
    obtain ⟨e, p⟩ := hget j hj
    rw [getElem!_map_inv n _ hj, e]
    exact ⟨invCand_PP (pp_of_permB hw p), permB_pinvS hw p⟩
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hAl, hBl⟩, hka⟩, hkb⟩, fun i hi => ?_⟩, fun i hi => ?_⟩, hpwl⟩, fun j hj => ?_⟩,
    fun i hi => ?_⟩
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hA i hi
    have hl := hAl _ (getElem!_mem hi)
    have e := wordArr_eq hw hcC hl
    have p := permB_wK hw hcC hl
    rw [e, compA_pk hw hnu p, compA_pk hw p hnu, eqA_pk hw (permB_pc hw hnu p) (permB_pc hw p hnu),
      pow_pk hw p, idA_pk hw, eqA_pk hw (permB_ppw hw p _) (permB_pid hw)]
    exact ⟨⟨h1, h2⟩, h3⟩
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hB i hi
    have hl := hBl _ (getElem!_mem hi)
    have e := wordArr_eq hw hcP hl
    have p := permB_wK hw hcP hl
    rw [e, compA_pk hw henu p, compA_pk hw p henu,
      eqA_pk hw (permB_pc hw henu p) (permB_pc hw p henu), pow_pk hw p, idA_pk hw,
      eqA_pk hw (permB_ppw hw p _) (permB_pid hw)]
    exact ⟨⟨h1, h2⟩, h3⟩
  · rw [getElem!_map_inv n _ hj, (hget j hj).1]
    exact CFSG.KC.Fi22RkS.isInvA_PP (pp_of_permB hw (hget j hj).2)
  · obtain ⟨hl, he⟩ := hpw i hi
    rw [← hsz] at hl
    refine ⟨hl, ?_⟩
    rw [(hcP i (by omega)).1, wordA_unpack hw (fun h hh => (hget h hh).1) (fun h hh => (hgeti h hh).1)
      (fun h hh => (hget h hh).2) (fun h hh => (hgeti h hh).2) hl,
      eqA_pk hw (hcP i (by omega)).2 (permB_wordK hw (fun h hh => (hget h hh).2)
        (fun h hh => (hgeti h hh).2) hl)]
    exact he

include hw in
theorem rep_of {ctx : Ctx} {r : RepCert} {oP oC oX oT : ℕ} (hP : ctx.chP.check n = true)
    (hPo : ctx.chP.order n = oP) (hC : r.chC.check n = true) (hCo : r.chC.order n = oC)
    (hX : r.chX.check n = true) (hXo : r.chX.order n = oX) (hT : r.chT.check n = true)
    (hTo : r.chT.order n = oT) (hcP : CB n w ctx.chP) (hcN : CB n w ctx.chN)
    (hcC : CB n w r.chC) (hcX : CB n w r.chX) (hcT : CB n w r.chT)
    {BT : ℕ → ℕ} (h : repK n w ctx r BT oP oC oX oT = true) : r.ok n ctx = true := by
  have hkC := ChainData.k_le_size n hC
  have hkX := ChainData.k_le_size n hX
  have hkT := ChainData.k_le_size n hT
  unfold repK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩, h16⟩, h17⟩ := h
  have eNu : r.nuA n ctx = unpack n w (wK n w ctx.chN r.nuW) := wordArr_eq hw hcN h1
  have pNu := permB_wK hw hcN h1
  have hokC : r.okC n ctx = true := by
    unfold RepCert.okC
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
    rw [eNu, compA_pk hw pNu pNu, idA_pk hw, eqA_pk hw (permB_pc hw pNu pNu) (permB_pid hw)]
    refine ⟨⟨⟨⟨h1, h2⟩, hC⟩, origs_of hw hcC hcP hkC h3⟩, fun i hi => ?_⟩
    obtain ⟨e, p⟩ := hcC i (by omega)
    rw [e, compA_pk hw pNu p, compA_pk hw p pNu,
      eqA_pk hw (permB_pc hw pNu p) (permB_pc hw p pNu)]
    exact h4 i hi
  have hokE : r.okE n ctx = true := by
    unfold RepCert.okE
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [eNu, hPo, hCo]
    exact ⟨bfs_of hw hcP pNu h5, h6⟩
  have hokX : r.okX n = true := by
    unfold RepCert.okX
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨hX, origs_of hw hcX hcC hkX h7⟩, fun i hi j hj => ?_⟩, fun i hi i' hi' => ?_⟩
    · obtain ⟨hl, he⟩ := h8 i hi j hj
      refine ⟨hl, ?_⟩
      obtain ⟨eC, pC⟩ := hcC i (by omega)
      obtain ⟨eCi, pCi⟩ := cb_inv hw hcC i (by omega)
      obtain ⟨eX, pX⟩ := hcX j (by omega)
      unfold conjArr
      rw [eC, eCi, eX, compA_pk hw pC pX, compA_pk hw (permB_pc hw pC pX) pCi, wordArr_eq hw hcX hl,
        eqA_pk hw (permB_pc hw (permB_pc hw pC pX) pCi) (permB_wK hw hcX hl)]
      exact he
    · obtain ⟨hl, he⟩ := h9 i hi i' hi'
      refine ⟨hl, ?_⟩
      obtain ⟨eC, pC⟩ := hcC i (by omega)
      obtain ⟨eCi, pCi⟩ := cb_inv hw hcC i (by omega)
      obtain ⟨eC', pC'⟩ := hcC i' (by omega)
      obtain ⟨eCi', pCi'⟩ := cb_inv hw hcC i' (by omega)
      unfold commArr
      rw [eC, eCi, eC', eCi', compA_pk hw pC pC', compA_pk hw pCi pCi',
        compA_pk hw (permB_pc hw pC pC') (permB_pc hw pCi pCi'), wordArr_eq hw hcX hl,
        eqA_pk hw (permB_pc hw (permB_pc hw pC pC') (permB_pc hw pCi pCi')) (permB_wK hw hcX hl)]
      exact he
  have heps : ∀ k, 1 ≤ k → k ≤ r.epsW.length →
      r.epsA n k = unpack n w (wK n w r.chX (r.epsW[k - 1]!)) := fun k hk1 hk2 =>
    wordArr_eq hw hcX (h14 _ (getElem!_mem (by omega)))
  have hokT : r.okT n = true := by
    unfold RepCert.okT
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    rw [hTo, hXo]
    exact ⟨⟨⟨⟨⟨⟨hT, origs_of hw hcT hcX hkT h10⟩, Nat.eq_of_beq_eq_true h11⟩,
      Nat.eq_of_beq_eq_true h12⟩, h13⟩, h14⟩,
      cover_of hw hT hC hcT hcC hTo heps h15⟩
  have hokG : r.okG n ctx = true := by
    unfold RepCert.okG
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    refine ⟨h16, fun l hl => ?_⟩
    have hl' := h14 _ (getElem!_mem hl)
    have e := heps (l + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at e
    rw [e, eNu, compA_pk hw (permB_wK hw hcX hl') pNu]
    exact gen_of hw hP hcP hcC pNu (permB_pc hw (permB_wK hw hcX hl') pNu) (h17 l hl)
  unfold RepCert.ok
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨hokC, hokE⟩, hokX⟩, hokT⟩, hokG⟩

@[expose] def chainSmall (n : ℕ) (cd : ChainData) : Bool :=
  decide (1 ≤ n) && decide (cd.k ≤ cd.S.size) && decide cd.base.Nodup &&
    cd.base.all (fun b => decide (b < n)) && decide (0 < cd.chunks)

theorem chain_of {cd : ChainData} {kS nb BP NS CH : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {D : List (List ℤ)} (hb : Binds n w PS kS nb BP cd.S cd.base.toArray)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS cd.k D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hW : cd.W = CFSG.Sporadic.Schreier.Co3.Native.wordsArr cd.k kS D)
    (hsm : chainSmall n cd = true) : cd.check n = true := by
  unfold chainSmall at hsm
  unfold ChainData.check
  rw [hsm, hW, rawChainK_sound hb hh hl hNS hs]
  rfl

theorem chain_order {cd : ChainData} {kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    (hb : Binds n w PS kS nb BP cd.S cd.base.toArray)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) :
    cd.order n = ((List.range nb).map fun i => rcnt (LR i)).prod := by
  unfold ChainData.order
  rw [← rawOrbitSizesK_sound hb hp hl]
  rfl

theorem wordsArr_eq' {kO kS : Nat} {D : List (List Int)} {W : Array (List Int)}
    (hs : W.size = kS) (hk : kO ≤ kS) (hW : ∀ j < kO, W[j]! = [])
    (hD : W.extract kO W.size = D.toArray) :
    W = CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D := by
  apply Array.ext
  · simp [CFSG.Sporadic.Schreier.Co3.Native.wordsArr, hs]
  · intro j h1 h2
    simp only [CFSG.Sporadic.Schreier.Co3.Native.wordsArr, Array.getElem_ofFn]
    split_ifs with h
    · rw [← getElem!_pos W j h1]
      exact hW j h
    · have e := congrArg (fun A : Array (List Int) => A[j - kO]?) hD
      simp only [Array.getElem?_extract] at e
      rw [List.getD_eq_getElem?_getD, ← List.getElem?_toArray, ← e]
      simp [show kO + (j - kO) = j by omega, h1, show j - kO < W.size - kO by omega]

theorem chain_ok_of {cd : ChainData} {kS kO nb BP NS CH : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {D : List (List ℤ)} (hsz : 0 < n ∧ n + 1 < 2 ^ w ∧ n < 65536)
    (hc : chainBindK n w cd PS PSI kS nb BP D = true) (hk : cd.k = kO)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true) :
    cd.check n = true ∧ cd.order n = ((List.range nb).map fun i => rcnt (LR i)).prod := by
  rw [← hk] at hh
  unfold chainBindK at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := hc
  have hb : Binds n w PS kS nb BP cd.S cd.base.toArray :=
    ⟨hsz.1, hsz.2.1, hsz.2.2, Nat.eq_of_beq_eq_true h1, fun j hj => arrBind_sound (h2 j hj),
      by simpa using Nat.eq_of_beq_eq_true h3, fun t ht => Nat.eq_of_beq_eq_true (h4 t ht)⟩
  have hW := wordsArr_eq' (Nat.eq_of_beq_eq_true h5) h6
    (fun j hj => List.isEmpty_iff.1 (h7 j hj)) h8
  have hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true :=
    CFSG.KS.Raw.Orb.allN_iff.2 fun j hj => h9 j hj
  refine ⟨chain_of hb hh hl hNS hs hW ?_, chain_order hb hp hl⟩
  unfold chainSmall
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  have e1 := Nat.eq_of_beq_eq_true h1
  exact ⟨⟨⟨⟨h10, by omega⟩, h11⟩, h12⟩, h13⟩

theorem fcK_of {c : FCCert} {oP oN oTN : ℕ} {ro : List RepOrd} {bt : ℕ → ℕ → ℕ}
    (h1 : chainBK n w c.ctx.chP = true) (h2 : chainBK n w c.ctx.chN = true)
    (h3 : chainBK n w c.chTN = true)
    (h4 : ∀ r ∈ c.reps, (chainBK n w r.chC && chainBK n w r.chX && chainBK n w r.chT) = true)
    (h5 : ctxK n w c.ctx = true) (h6 : origsK n w c.chTN c.ctx.chN c.tnW = true)
    (h7 : Nat.beq oTN (2 ^ c.sylA) = true) (h8 : Nat.beq oN (2 ^ c.sylA * c.sylM) = true)
    (h9 : c.sylM % 2 = 1)
    (h10 : coverK n w c.chTN c.ctx.chN c.tel c.reps.length
      (fun j => wK n w c.ctx.chN (c.reps[j - 1]!).nuW) oTN = true)
    (h11 : ro.length = c.reps.length)
    (h12 : ∀ j < c.reps.length,
      repK n w c.ctx c.reps[j]! (bt j) oP (ro[j]!).1 (ro[j]!).2.1 (ro[j]!).2.2 = true) :
    fcK n w c oP oN oTN ro bt = true := by
  unfold fcK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, fun r hr => ?_⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, ?_⟩, h12⟩
  · have := h4 r hr
    simp only [Bool.and_eq_true] at this
    exact this
  · rw [h11]
    exact Nat.beq_refl _

abbrev RepChains (n : ℕ) (r : RepCert) (o : RepOrd) : Prop :=
  r.chC.check n = true ∧ r.chC.order n = o.1 ∧ r.chX.check n = true ∧ r.chX.order n = o.2.1 ∧
    r.chT.check n = true ∧ r.chT.order n = o.2.2

include hw in
theorem fc_ok_of {c : FCCert} {oP oN oTN : ℕ} {ro : List RepOrd}
    (hP : c.ctx.chP.check n = true) (hPo : c.ctx.chP.order n = oP)
    (hN : c.ctx.chN.check n = true) (hNo : c.ctx.chN.order n = oN)
    (hT : c.chTN.check n = true) (hTo : c.chTN.order n = oTN)
    (hR : ∀ j < c.reps.length, RepChains n c.reps[j]! ro[j]!)
    {bt : ℕ → ℕ → ℕ} (h : fcK n w c oP oN oTN ro bt = true) : c.ok n = true := by
  unfold fcK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨bP, bN⟩, bT⟩, bR⟩, hctx⟩, horig⟩, hTo'⟩, hNo'⟩, hodd⟩, hcov⟩, hlen⟩, hreps⟩ := h
  have cP := cb_of bP
  have cN := cb_of bN
  have cT := cb_of bT
  have cR : ∀ r ∈ c.reps, CB n w r.chC ∧ CB n w r.chX ∧ CB n w r.chT := fun r hr => by
    have := bR r hr
    exact ⟨cb_of this.1.1, cb_of this.1.2, cb_of this.2⟩
  have hrepA : ∀ j, 1 ≤ j → j ≤ c.reps.length →
      c.repA n j = unpack n w (wK n w c.ctx.chN (c.reps[j - 1]!).nuW) := by
    intro j hj1 hj2
    have hj := hreps (j - 1) (by omega)
    unfold repK at hj
    simp only [Bool.and_eq_true] at hj
    exact wordArr_eq hw cN hj.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  unfold FCCert.ok FCCert.okTN
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨ctx_of hw hP hN cP cN hctx, ⟨⟨⟨⟨⟨hT, origs_of hw cT cN (ChainData.k_le_size n hT) horig⟩,
    hTo ▸ Nat.eq_of_beq_eq_true hTo'⟩, hNo ▸ Nat.eq_of_beq_eq_true hNo'⟩, hodd⟩,
    cover_of hw hT hN cT cN hTo hrepA hcov⟩⟩, fun r hr => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  have hj' : c.reps[j]! = c.reps[j] := getElem!_pos c.reps j hj
  obtain ⟨hC, hCo, hX, hXo, hT', hTo''⟩ := hR j hj
  obtain ⟨cC, cX, cT'⟩ := cR _ hr
  rw [hj'] at hC hCo hX hXo hT' hTo''
  have := hreps j hj
  rw [hj'] at this
  exact rep_of hw hP hPo hC hCo hX hXo hT' hTo'' cP cN cC cX cT' this

end CFSG.KC.ExactGen

end
