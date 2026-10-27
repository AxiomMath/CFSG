module

public import Certificates.Data.Kernel.TwistDce3.ChainP
public import CFSG.Certificates.Kernel.TwistDce2.ChainB
public import CFSG.Certificates.Kernel.TwistDce3.CoverSound

public section

namespace CFSG.Certificates.TwDce3.ChainP

open CFSG.KC.TwDce3 CFSG.KC.LaneChain CFSG.KC.YModel CFSG.Certificates.CosetEnumeration
  CFSG.Certificates.TwDce CFSG.Certificates.TwDce.Words CFSG.KC.StabChain
open CFSG.Certificates.TwDce2.ChainB
open CFSG.KC.TwDce2 (wvld gRegs gWord isStabOf allRange getLL)
open CFSG.KC.TwDce (wLen wOK wCat wStr wAt)
open CFSG.KS.LaneChain (getR_mem getN_mem getN_eq_getElem lenL_eq allLt_spec memN_spec gensK_spec
  strictB_app strictN_app andT)

theorem wmulP_odd (PB : ℕ) (F : ℕ → ℕ) {g h : ℕ} (hh : h % 2 = 1) :
    wmulP PB F g h = 2 * wCat (h / 2) (g / 2) + 1 := by
  have hb : Nat.beq (Nat.land h 1) 1 = true := by rw [land1, hh]; rfl
  unfold wmulP
  rw [hb]
  change 2 * wCat (Nat.shiftRight h 1) (Nat.shiftRight g 1) + 1 = _
  rw [shr1, shr1]

theorem wmulP_even (PB : ℕ) (F : ℕ → ℕ) {g h : ℕ} (hh : h % 2 = 0) :
    wmulP PB F g h = 2 * CFSG.KC.TwDce3.evP PB F (g / 2) (h / 2) := by
  have hb : Nat.beq (Nat.land h 1) 1 = false := by rw [land1, hh]; rfl
  unfold wmulP
  rw [hb]
  change 2 * CFSG.KC.TwDce3.evP PB F (Nat.shiftRight g 1) (Nat.shiftRight h 1) = _
  rw [shr1, shr1]

theorem good_wmulP (PB : ℕ) (F : ℕ → ℕ) {G : Type*} [Group G] {K : Subgroup G} {x : ℕ → G}
    {g h : ℕ} (hg : GoodW K x g) (hh : GoodW K x h) (hl : wLen (h / 2) + wLen (g / 2) < 2 ^ 32) :
    GoodW K x (wmulP PB F g h) ∧ wLen (wmulP PB F g h / 2) = wLen (h / 2) + wLen (g / 2) := by
  obtain ⟨-, hg2, hg3, hg4⟩ := hg
  obtain ⟨hh1, hh2, hh3, hh4⟩ := hh
  obtain ⟨c1, c2, c3⟩ := wCat_spec hh2 hg2 hl
  rw [wmulP_odd PB F hh1]
  have e : (2 * wCat (h / 2) (g / 2) + 1) / 2 = wCat (h / 2) (g / 2) := by omega
  unfold GoodW
  rw [e]
  refine ⟨⟨by omega, c2, fun c hc => ?_, ?_⟩, c1⟩
  · rw [c3] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hh3 c hc
    · exact hg3 c hc
  · rw [wVal_lst, c3, evalWord_append']
    exact K.mul_mem hh4 hg4

theorem good_wfoldP (PB : ℕ) (F : ℕ → ℕ) {G : Type*} [Group G] {K : Subgroup G} {x : ℕ → G}
    {M : List ℕ} (hM : ∀ r ∈ M, GoodW K x r) :
    ∀ (rs : List ℕ) (acc : ℕ), (∀ r ∈ rs, r < M.length) → GoodW K x acc →
      wLen (acc / 2) + (rs.map fun r => wLen (getR M M.length r / 2)).sum < 2 ^ 32 →
      GoodW K x (wfold (wmulP PB F) M M.length rs acc) ∧
        wLen (wfold (wmulP PB F) M M.length rs acc / 2) =
          wLen (acc / 2) + (rs.map fun r => wLen (getR M M.length r / 2)).sum
  | [], acc, _, h, _ => ⟨h, by change wLen (acc / 2) = _; simp⟩
  | r :: rs, acc, hr, h, hl => by
    change GoodW K x (CFSG.KC.Loop.strictN (wmulP PB F acc (getR M M.length r))
        (wfold (wmulP PB F) M M.length rs)) ∧
      wLen (CFSG.KC.Loop.strictN (wmulP PB F acc (getR M M.length r))
        (wfold (wmulP PB F) M M.length rs) / 2) = _
    rw [strictN_app]
    have hgr := hM _ (getR_mem (hr r List.mem_cons_self))
    rw [List.map_cons, List.sum_cons] at hl ⊢
    obtain ⟨g1, g2⟩ := good_wmulP PB F h hgr (by omega)
    obtain ⟨k1, k2⟩ := good_wfoldP PB F hM rs _ (fun y hy => hr y (List.mem_cons_of_mem _ hy)) g1
      (by rw [g2]; omega)
    exact ⟨k1, by rw [k2, g2]; omega⟩

theorem regsBP_spec (PB : ℕ) (F : ℕ → ℕ) {G : Type*} [Group G] {K : Subgroup G} {x : ℕ → G}
    {k : List ℕ → ℕ → Bool} : ∀ (W : List (List ℕ)) (M : List ℕ),
    (∀ r ∈ M, GoodW K x r) → (∀ m ∈ chainLens (M.map fun r => wLen (r / 2)) W, m < 2 ^ 32) →
    regsK (wmulP PB F) k W M M.length = true →
      ∃ M', (∀ r ∈ M', GoodW K x r) ∧ k M' M'.length = true
  | [], M, hM, _, h => ⟨M, hM, h⟩
  | wd :: W, M, hM, hl, h => by
    obtain ⟨h1, h2⟩ := andT h
    obtain ⟨h1a, h1b⟩ := andT h1
    obtain ⟨r0, rs, rfl⟩ : ∃ r0 rs, wd = r0 :: rs := by
      cases wd with
      | nil => exact absurd h1a (by decide)
      | cons r0 rs => exact ⟨r0, rs, rfl⟩
    rw [strictB_app] at h2
    have hw := allLt_spec _ h1b
    have hget : ∀ r < M.length, (M.map fun r => wLen (r / 2)).getD
        ((M.map fun r => wLen (r / 2)).length - 1 - r) 0 = wLen (getR M M.length r / 2) := by
      intro r hr
      have e : getR M M.length r = M[M.length - 1 - r] :=
        getN_eq_getElem M _ (by change M.length - 1 - r < M.length; omega)
      rw [e, List.getD_eq_getElem _ _ (by rw [List.length_map]; omega)]
      simp
    have hsum : ((r0 :: rs).map fun r => (M.map fun r => wLen (r / 2)).getD
        ((M.map fun r => wLen (r / 2)).length - 1 - r) 0).sum =
        wLen (getR M M.length r0 / 2) + (rs.map fun r => wLen (getR M M.length r / 2)).sum := by
      rw [List.map_cons, List.sum_cons, hget r0 (hw r0 List.mem_cons_self)]
      congr 1
      congr 1
      exact List.map_congr_left fun r hr => hget r (hw r (List.mem_cons_of_mem _ hr))
    have hs := hl _ (mem_chainLens W _ _ List.mem_cons_self)
    rw [hsum] at hs
    obtain ⟨g1, g2⟩ := good_wfoldP PB F hM rs _ (fun r hr => hw r (List.mem_cons_of_mem _ hr))
      (hM _ (getR_mem (hw r0 List.mem_cons_self))) hs
    have h3 : regsK (wmulP PB F) k W (wprod (wmulP PB F) M M.length (r0 :: rs) :: M)
        (wprod (wmulP PB F) M M.length (r0 :: rs) :: M).length = true := h2
    refine regsBP_spec PB F W _ (fun r hr => ?_) (fun m hm => ?_) h3
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact g1
      · exact hM r hr
    · rw [List.map_cons] at hm
      have e : wLen (wprod (wmulP PB F) M M.length (r0 :: rs) / 2) =
          ((r0 :: rs).map fun r => (M.map fun r => wLen (r / 2)).getD
            ((M.map fun r => wLen (r / 2)).length - 1 - r) 0).sum := by
        rw [hsum]
        exact g2
      rw [e] at hm
      exact hl m hm

theorem treeBP_nil (PB : ℕ) (F : ℕ → ℕ) (M : List ℕ) (n : ℕ) (Gl : List ℕ) (k : ℕ → Bool)
    (pend mask cnt : ℕ) :
    treeBP PB F M n Gl k [] pend mask cnt = CFSG.KC.andB (Nat.beq pend 0) (k cnt) := rfl

theorem treeBP_zero (PB : ℕ) (F : ℕ → ℕ) (M : List ℕ) (n : ℕ) (Gl : List ℕ) (k : ℕ → Bool)
    (c : ℕ) (T : List ℕ) (mask cnt : ℕ) :
    treeBP PB F M n Gl k (c :: T) 0 mask cnt = CFSG.KC.andB
      (Nat.beq (CFSG.KC.TwDce.fld mask c 1) 1) (treeBP PB F M n Gl k T (c + 1) mask cnt) := rfl

theorem treeBP_succ (PB : ℕ) (F : ℕ → ℕ) (M : List ℕ) (n : ℕ) (Gl : List ℕ) (k : ℕ → Bool)
    (c : ℕ) (T : List ℕ) (q mask cnt : ℕ) :
    treeBP PB F M n Gl k (c :: T) (q + 1) mask cnt =
      CFSG.KC.andB (CFSG.KC.andB (memN c Gl) (Nat.blt c n))
        (CFSG.KC.TwDce.sB (Nat.shiftRight (wmulP PB F (getR M n c) (2 * q)) 1) (fun v =>
          CFSG.KC.andB (Nat.beq (CFSG.KC.TwDce.fld mask v 1) 0)
            (CFSG.KC.TwDce.sB (Nat.lor mask (Nat.shiftLeft 1 v)) (fun m =>
              treeBP PB F M n Gl k T 0 m (cnt + 1))))) := rfl

theorem levelsBP_nil (PB : ℕ) (F : ℕ → ℕ) (M : List ℕ) (n : ℕ) (Xs : List ℕ) (tot : ℕ)
    (Ts : List (List ℕ)) (k acc : ℕ) : levelsBP PB F M n Xs tot Ts [] k acc = Nat.beq acc tot :=
  rfl

theorem levelsBP_cons (PB : ℕ) (F : ℕ → ℕ) (M : List ℕ) (n : ℕ) (Xs : List ℕ) (tot : ℕ)
    (Ts : List (List ℕ)) (Gl : List ℕ) (Gs : List (List ℕ)) (k acc : ℕ) :
    levelsBP PB F M n Xs tot Ts (Gl :: Gs) k acc = CFSG.KC.andB
      (CFSG.KC.andB (Nat.blt k (CFSG.KC.Ord.lenL Xs)) (gensK (wmulP PB F) M Xs Gl n k))
      (treeBP PB F M n Gl (fun m => levelsBP PB F M n Xs tot Ts Gs (k + 1) (acc * m)) (getL Ts k)
        0 (Nat.shiftLeft 1 (Nat.shiftRight (getN Xs k) 1)) 1) := rfl

section Tree

variable {G : Type*} [Group G] {PB : ℕ} {F : ℕ → ℕ} {NP : ℕ} (x : ℕ → G) (pt : G → ℕ → ℕ)
  (K : Subgroup G) (hpt1 : ∀ p, pt 1 p = p) (hptm : ∀ a b p, pt (a * b) p = pt b (pt a p))
  (hF : ∀ c < 12, ∀ p < NP, fieldAt PB (F c) p < NP)
  (hx : ∀ c < 12, ∀ p < NP, fieldAt PB (F c) p = pt (x c) p)
include hpt1 hptm hF hx

theorem foldl_ptP : ∀ (cs : List ℕ) (p : ℕ), (∀ c ∈ cs, c < 12) → p < NP →
    cs.foldl (fun q c => fieldAt PB (F c) q) p = pt (evalWord x cs) p ∧
      pt (evalWord x cs) p < NP
  | [], p, _, hp => by
    rw [List.foldl_nil, evalWord_nil, hpt1]
    exact ⟨rfl, hp⟩
  | c :: cs, p, hc, hp => by
    have hc0 := hc c List.mem_cons_self
    obtain ⟨h1, h2⟩ := foldl_ptP cs (fieldAt PB (F c) p)
      (fun d hd => hc d (List.mem_cons_of_mem _ hd)) (hF c hc0 p hp)
    simp only [List.foldl_cons]
    rw [h1, evalWord_cons, hptm, ← hx c hc0 p hp]
    exact ⟨rfl, h2⟩

theorem wmulP_pt {g h : ℕ} (hg : GoodW K x g) (hh : h % 2 = 0) (hp : h / 2 < NP) :
    wmulP PB F g h = 2 * pt (wVal x (g / 2)) (h / 2) ∧ pt (wVal x (g / 2)) (h / 2) < NP := by
  obtain ⟨e1, e2⟩ := foldl_ptP x pt hpt1 hptm hF hx (lst (g / 2)) (h / 2) hg.2.2.1 hp
  rw [wmulP_even PB F hh, CFSG.Certificates.TwDce3.Words.evP_eq, e1]
  exact ⟨rfl, e2⟩

theorem treeBP_spec {M Gl Fx : List ℕ} {b : ℕ} (hM : ∀ r ∈ M, GoodW K x r)
    (hG : ∀ r ∈ Gl, r < M.length ∧ ∀ y ∈ Fx, pt (wVal x (getR M M.length r / 2)) y = y)
    {k : ℕ → Bool} : ∀ (T : List ℕ) (pend mask : ℕ) (V : List ℕ) (ts : List G),
      TreeI K pt NP Fx b V ts mask → (∀ q, pend = q + 1 → q ∈ V) →
      treeBP PB F M M.length Gl k T pend mask V.length = true →
      ∃ V' ts' mask', TreeI K pt NP Fx b V' ts' mask' ∧ k V'.length = true
  | [], pend, mask, V, ts, I, _, h => by
    rw [treeBP_nil, kandB_iff] at h
    exact ⟨V, ts, mask, I, h.2⟩
  | c :: T, 0, mask, V, ts, I, _, h => by
    rw [treeBP_zero, kandB_iff] at h
    have hc : c ∈ V := (I.bit c).1 (fld_one_eq_one.1 (Nat.eq_of_beq_eq_true h.1))
    exact treeBP_spec hM hG T (c + 1) mask V ts I (fun q e => by
      obtain rfl := Nat.succ.inj e
      exact hc) h.2
  | c :: T, q + 1, mask, V, ts, I, hp, h => by
    rw [treeBP_succ, kandB_iff, kandB_iff, sB_eq] at h
    obtain ⟨⟨hm, -⟩, h⟩ := h
    obtain ⟨hcM, hfix⟩ := hG c (memN_spec Gl hm)
    have hgood := hM _ (getR_mem hcM)
    have hqV := hp q rfl
    have hqN := I.lt q hqV
    obtain ⟨w1, w2⟩ := wmulP_pt x pt K hpt1 hptm hF hx hgood (h := 2 * q) (by omega)
      (by omega)
    have e2 : 2 * q / 2 = q := by omega
    rw [e2] at w1 w2
    have e3 : Nat.shiftRight (wmulP PB F (getR M M.length c) (2 * q)) 1 =
        pt (wVal x (getR M M.length c / 2)) q := by
      rw [w1, shr1]
      omega
    rw [e3, kandB_iff, sB_eq] at h
    obtain ⟨hv, h⟩ := h
    have hvV : pt (wVal x (getR M M.length c / 2)) q ∉ V := fun hmem =>
      absurd ((I.bit _).2 hmem) (by rw [fld_one_eq_zero.1 (Nat.eq_of_beq_eq_true hv)]; decide)
    have hqV' := hqV
    rw [I.img] at hqV'
    obtain ⟨tq, htq, htqb⟩ := List.mem_map.1 hqV'
    have hgK : wVal x (getR M M.length c / 2) ∈ K := hgood.2.2.2
    have I' : TreeI K pt NP Fx b (V ++ [pt (wVal x (getR M M.length c / 2)) q])
        (ts ++ [tq * wVal x (getR M M.length c / 2)])
        (Nat.lor mask (Nat.shiftLeft 1 (pt (wVal x (getR M M.length c / 2)) q))) := by
      refine ⟨?_, fun v hv' => ?_, ?_, fun q' => ?_, fun t ht => ?_, fun t ht y hy => ?_⟩
      · rw [List.map_append, ← I.img, List.map_singleton, hptm, htqb]
      · rcases List.mem_append.1 hv' with hv' | hv'
        · exact I.lt v hv'
        · rw [List.mem_singleton.1 hv']
          exact w2
      · refine List.nodup_append.2 ⟨I.nodup, List.nodup_singleton _, fun a ha b' hb' => ?_⟩
        rw [List.mem_singleton.1 hb']
        rintro rfl
        exact hvV ha
      · change (mask ||| Nat.shiftLeft 1 _).testBit q' = true ↔ _
        rw [Nat.testBit_or, testBit_shl_one, Bool.or_eq_true, I.bit, List.mem_append,
          List.mem_singleton, decide_eq_true_iff, eq_comm]
      · rcases List.mem_append.1 ht with ht | ht
        · exact I.mem t ht
        · rw [List.mem_singleton.1 ht]
          exact K.mul_mem (I.mem tq htq) hgK
      · rcases List.mem_append.1 ht with ht | ht
        · exact I.fix t ht y hy
        · rw [List.mem_singleton.1 ht, hptm, I.fix tq htq y hy, hfix y hy]
    have hlen : (V ++ [pt (wVal x (getR M M.length c / 2)) q]).length = V.length + 1 := by simp
    rw [← hlen] at h
    exact treeBP_spec hM hG T 0 _ _ _ I' (fun q' e => absurd e (by omega)) h

theorem levelsBP_spec {M Xs : List ℕ} (hM : ∀ r ∈ M, GoodW K x r)
    (hX : ∀ y ∈ Xs, y % 2 = 0 ∧ y / 2 < NP) {tot : ℕ} {Ts : List (List ℕ)} :
    ∀ (Gs : List (List ℕ)) (k acc : ℕ), levelsBP PB F M M.length Xs tot Ts Gs k acc = true →
      ∃ Lc : List (ℕ × List G), ChainOK pt K Lc ∧ acc * (Lc.map fun l => l.2.length).prod = tot ∧
        (∀ l ∈ Lc, ∀ t ∈ l.2, ∀ y ∈ fixP Xs k, pt t y = y) ∧ ∀ l ∈ Lc, l.1 ∈ Xs.map (· / 2)
  | [], k, acc, h => by
    rw [levelsBP_nil] at h
    exact ⟨[], trivial, by simpa using Nat.eq_of_beq_eq_true h, by simp, by simp⟩
  | Gl :: Gs, k, acc, h => by
    rw [levelsBP_cons, kandB_iff, kandB_iff, shr1] at h
    obtain ⟨⟨hk, hgen⟩, h⟩ := h
    have hk' : k < Xs.length := by
      rw [← lenL_eq]
      exact Nat.blt_eq.mp hk
    have hXk := hX _ (getN_mem Xs k hk')
    have hG : ∀ r ∈ Gl, r < M.length ∧
        ∀ y ∈ fixP Xs k, pt (wVal x (getR M M.length r / 2)) y = y := by
      intro r hr
      obtain ⟨hrn, hfx⟩ := gensK_spec Gl hgen r hr
      refine ⟨hrn, fun y hy => ?_⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
      have hj' := List.mem_range.1 hj
      obtain ⟨e0, e1⟩ := hX _ (getN_mem Xs j (by omega))
      obtain ⟨w1, -⟩ := wmulP_pt x pt K hpt1 hptm hF hx (hM _ (getR_mem hrn)) e0 e1
      have := hfx j hj'
      rw [w1] at this
      omega
    have I0 : TreeI K pt NP (fixP Xs k) (getN Xs k / 2) [getN Xs k / 2] [1]
        (Nat.shiftLeft 1 (getN Xs k / 2)) := by
      refine ⟨by simp [hpt1], fun v hv => ?_, List.nodup_singleton _, fun q => ?_,
        fun t ht => ?_, fun t ht y _ => ?_⟩
      · rw [List.mem_singleton.1 hv]
        exact hXk.2
      · rw [testBit_shl_one, decide_eq_true_iff, List.mem_singleton, eq_comm]
      · rw [List.mem_singleton.1 ht]
        exact K.one_mem
      · rw [List.mem_singleton.1 ht, hpt1]
    obtain ⟨V, ts, mask, I, hrest⟩ := treeBP_spec x pt K hpt1 hptm hF hx hM hG _ 0 _ _ _ I0
      (fun q e => absurd e (by omega)) h
    obtain ⟨Lc, hC, hprod, hfix, hbase⟩ := levelsBP_spec hM hX Gs (k + 1) _ hrest
    have hl : V.length = ts.length := by rw [I.img, List.length_map]
    refine ⟨(getN Xs k / 2, ts) :: Lc, ⟨I.mem, ?_, fun l hl t ht => hfix l hl t ht _ ?_, hC⟩,
      ?_, ?_, ?_⟩
    · rw [← I.img]
      exact I.nodup
    · exact List.mem_map.2 ⟨k, List.mem_range.2 (Nat.lt_succ_self k), rfl⟩
    · rw [List.map_cons, List.prod_cons, ← mul_assoc, ← hl]
      exact hprod
    · intro l hl t ht y hy
      rcases List.mem_cons.1 hl with rfl | hl
      · exact I.fix t ht y hy
      · refine hfix l hl t ht y ?_
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
        exact List.mem_map.2 ⟨j, List.mem_range.2 (by have := List.mem_range.1 hj; omega), rfl⟩
    · intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · exact List.mem_map.2 ⟨_, getN_mem Xs k hk', rfl⟩
      · exact hbase l hl

end Tree

theorem chainBP_sound {PB : ℕ} {F : ℕ → ℕ} {INVM NP : ℕ} {RW : ℕ → ℕ} {G : Type*} [Group G]
    (x : ℕ → G) (pt : G → ℕ → ℕ) (hpt1 : ∀ p, pt 1 p = p)
    (hptm : ∀ a b p, pt (a * b) p = pt b (pt a p))
    (hF : ∀ c < 12, ∀ p < NP, fieldAt PB (F c) p < NP)
    (hx : ∀ c < 12, ∀ p < NP, fieldAt PB (F c) p = pt (x c) p)
    (K : Subgroup G) [Finite K] {CG : List ℕ} {W Bs Gs Ts : List (List ℕ)} {tot : ℕ}
    (hCG : ∀ c ∈ CG, CFSG.KC.TwDce2.wBelow 12 (gWord INVM RW c) = true ∧
      wVal x (gWord INVM RW c) ∈ K)
    (hlen : ∀ m ∈ chainLens ((gRegs INVM RW CG).map fun r => CFSG.KC.TwDce.wLen (r / 2)) W,
      m < 2 ^ 32)
    (h : chainBP PB F NP W Bs Gs Ts (gRegs INVM RW CG) tot = true) :
    tot * Nat.card {g : G // g ∈ K ∧
      ∀ b ∈ Bs, pt g (CFSG.KC.LaneChain.colDat PB b / 2) = CFSG.KC.LaneChain.colDat PB b / 2} ≤
      Nat.card K := by
  classical
  have hM0 : ∀ r ∈ gRegs INVM RW CG, GoodW K x r := by
    rw [gRegs_eq]
    intro r hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
    obtain ⟨hb, hv⟩ := hCG c hc
    obtain ⟨h1, h2⟩ := CFSG.Certificates.TwDce2.Words.wBelow_spec hb
    have e : (2 * gWord INVM RW c + 1) / 2 = gWord INVM RW c := by omega
    exact ⟨by omega, by rw [e]; exact h1, by rw [e]; exact h2, by rw [e]; exact hv⟩
  unfold chainBP at h
  rw [lenL_eq] at h
  obtain ⟨M, hM, h1⟩ := regsBP_spec PB F W _ hM0 hlen h
  obtain ⟨Xs, hX, h2⟩ := basesK_spec2 (fun y => ∃ b ∈ Bs, y = colDat PB b) Bs []
    (fun _ hx => absurd hx List.not_mem_nil) (fun b hb => ⟨b, hb, rfl⟩) h1
  obtain ⟨Lc, hC, hprod, -, hbase⟩ := levelsBP_spec x pt K hpt1 hptm hF hx hM
    (fun y hy => wvld_spec (hX y hy).1) Gs 0 1 h2
  rw [one_mul] at hprod
  have hS : {g : G | g ∈ K ∧ ∀ b ∈ Bs, pt g (colDat PB b / 2) = colDat PB b / 2}.Finite :=
    (Set.toFinite (K : Set G)).subset fun g hg => hg.1
  have hAf : ∀ a ∈ hS.toFinset, ∀ l ∈ Lc, pt a l.1 = l.1 := by
    intro a ha l hl
    obtain ⟨y, hy, hyl⟩ := List.mem_map.1 (hbase l hl)
    obtain ⟨b, hb, rfl⟩ := (hX y hy).2
    rw [← hyl]
    exact ((Set.Finite.mem_toFinset hS).1 ha).2 b hb
  obtain ⟨s, hcard, hsK, -⟩ := exists_finset_right pt hptm K hS.toFinset
    (fun a ha => ((Set.Finite.mem_toFinset hS).1 ha).1) Lc hC hAf
  have hcS : Nat.card {g : G // g ∈ K ∧
      ∀ b ∈ Bs, pt g (colDat PB b / 2) = colDat PB b / 2} = hS.toFinset.card :=
    Nat.card_eq_card_finite_toFinset hS
  rw [hcS, ← hprod, mul_comm, ← hcard]
  have hinj : Function.Injective (fun g : s => (⟨g, hsK g g.2⟩ : K)) :=
    fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this

theorem stabRangeP_sound {PB : ℕ} {F : ℕ → ℕ} {INVM NP : ℕ} {RD RW : ℕ → ℕ} {n : ℕ}
    {DS : List ℕ} {CG : List (List ℕ)} {CW CB CS CT : List (List (List ℕ))} {CN : List ℕ}
    {a m : ℕ} (h : stabRangeP PB F INVM NP RD RW n DS CG CW CB CS CT CN a m = true) :
    ∀ j < m, stabOKP PB F INVM NP RD RW n (getN DS (a + j)) (getL CG (a + j))
      (getLL CW (a + j)) (getLL CB (a + j)) (getLL CS (a + j)) (getLL CT (a + j))
      (getN CN (a + j)) = true :=
  fun j hj => CFSG.Certificates.TwDce3.allRange_sound h j hj

end CFSG.Certificates.TwDce3.ChainP

end
