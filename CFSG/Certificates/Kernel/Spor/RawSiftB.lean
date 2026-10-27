module

public import CFSG.Certificates.Kernel.Spor.RawAgree
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw

@[expose] def BI (n w nb l X : Nat) (b : Nat → Fin n) (γ : Equiv.Perm (Fin n)) : Prop :=
  ∀ t, l ≤ t → t < nb → pg w (mask w) X t = (γ (b t) : Nat)

theorem pg_mapB {w nb l s G t : Nat} (ht : t < nb) :
    pg w (mask w) (mapB w (mask w) nb l s G) t =
      if l < t then pg w (mask w) s (pg w (mask w) G t) else 0 := by
  set v : Nat → Nat := fun t =>
    nIf(Nat.blt l t, pg w (mask w) s (pg w (mask w) G t), nat_lit 0) with hv
  have hvl : ∀ t, v t < 2 ^ w := fun t => by
    simp only [hv, nIf_eq]
    split
    · exact PF.pg_lt _ _ _
    · exact Nat.two_pow_pos w
  have key : ∀ k, PF.Fld w ((List.range k).foldl
      (fun acc t => Nat.lor acc (Nat.shiftLeft (v t) (Nat.mul w t))) 0)
      (fun i => if i < k then v i else 0) := by
    intro k
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil]
      exact PF.fld_congr (PF.fld_zero w) (fun i => by simp)
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine PF.fld_congr (PF.fld_or ih (PF.fld_shl k (PF.fld_one (hvl k)))) (fun i => ?_)
      by_cases h1 : i < k
      · simp [h1, show i < k + 1 by omega, show ¬ k ≤ i by omega]
      · by_cases h2 : i = k
        · subst h2
          simp
        · simp [h1, show ¬ i < k + 1 by omega, show k ≤ i by omega,
            show i - k ≠ 0 by omega]
  have e : mapB w (mask w) nb l s G = (List.range nb).foldl
      (fun acc t => Nat.lor acc (Nat.shiftLeft (v t) (Nat.mul w t))) 0 := by
    unfold mapB
    rw [strictN_eq, foldUp_eq]
  rw [e, PF.pg_of_fld (key nb) (by simp only [ht, ↓reduceIte]; exact hvl t)]
  simp only [ht, ↓reduceIte, hv, nIf_eq, blt_dec, decide_eq_true_eq]

theorem bi_mapB {n w nb l s G : Nat} {b : Nat → Fin n} {σ γ : Equiv.Perm (Fin n)}
    (hs : PRep n w s σ) (hG : BI n w nb (l + 1) G b γ) :
    BI n w nb (l + 1) (mapB w (mask w) nb l s G) b (σ * γ) := by
  intro t ht1 ht2
  have hlt : l < t := by omega
  simp only [pg_mapB ht2, hlt, ↓reduceIte]
  rw [hG t ht1 ht2, hs (γ (b t)), Equiv.Perm.mul_apply]

theorem bi_mono {n w nb l X : Nat} {b : Nat → Fin n} {γ : Equiv.Perm (Fin n)}
    (h : BI n w nb l X b γ) : BI n w nb (l + 1) X b γ :=
  fun t ht1 ht2 => h t (by omega) ht2

theorem beq_zero_true : Nat.beq 0 (nat_lit 0) = true := rfl

section Walks

variable {n w nb kS l c T R : Nat} {PS PSI : Nat → Nat} {b : Nat → Fin n}
  {σ : Nat → Equiv.Perm (Fin n)}
  (hpar : ∀ k < c, 0 < k → rpar w (mask w) (n * w) R k < k)

theorem walkT_succ_pos (f : Nat) {h : Nat} (hh : 0 < h) (G : Nat) :
    walkT n w (mask w) (n * w) nb PS PSI kS T R l (f + 1) h G =
      mapB w (mask w) nb l (letterK PS PSI kS (stAt T (rlab n (n * w) R h)))
        (walkT n w (mask w) (n * w) nb PS PSI kS T R l f (rpar w (mask w) (n * w) R h) G) := by
  have e : walkT n w (mask w) (n * w) nb PS PSI kS T R l (f + 1) h G =
      nIf(Nat.beq h (nat_lit 0), G, strictN (walkT n w (mask w) (n * w) nb PS PSI kS T R l f
        (rpar w (mask w) (n * w) R h) G) (fun G' => mapB w (mask w) nb l
          (letterK PS PSI kS (stAt T (rlab n (n * w) R h))) G')) := rfl
  rw [e, beq_zero_false hh]
  exact strictN_eq _ _

theorem walkIT_succ_pos (f : Nat) {k : Nat} (hk : 0 < k) (G : Nat) :
    walkIT n w (mask w) (n * w) nb PS PSI kS T R l (f + 1) k G =
      walkIT n w (mask w) (n * w) nb PS PSI kS T R l f (rpar w (mask w) (n * w) R k)
        (mapB w (mask w) nb l (invLetterK PS PSI kS (stAt T (rlab n (n * w) R k))) G) := by
  have e : walkIT n w (mask w) (n * w) nb PS PSI kS T R l (f + 1) k G =
      nIf(Nat.beq k (nat_lit 0), G, strictN (mapB w (mask w) nb l
        (invLetterK PS PSI kS (stAt T (rlab n (n * w) R k))) G)
        (walkIT n w (mask w) (n * w) nb PS PSI kS T R l f (rpar w (mask w) (n * w) R k))) := rfl
  rw [e, beq_zero_false hk]
  exact strictN_eq _ _

include hpar

theorem bi_walkT
    (hlet : ∀ k < c, 0 < k → PRep n w (letterK PS PSI kS (stAt T (rlab n (n * w) R k)))
      (σ (rlab n (n * w) R k))) :
    ∀ f h, h < c → ∀ G γ, BI n w nb (l + 1) G b γ →
      BI n w nb (l + 1) (walkT n w (mask w) (n * w) nb PS PSI kS T R l f h G) b
        (treeF σ (rpar w (mask w) (n * w) R) (rlab n (n * w) R) f h * γ) := by
  intro f
  induction f with
  | zero =>
    intro h _ G γ hG
    have e : walkT n w (mask w) (n * w) nb PS PSI kS T R l 0 h G = G := rfl
    rw [e, treeF, one_mul]
    exact hG
  | succ f ih =>
    intro h hh G γ hG
    rcases Nat.eq_zero_or_pos h with rfl | h0
    · have e : walkT n w (mask w) (n * w) nb PS PSI kS T R l (f + 1) 0 G = G := rfl
      rw [e, treeF_zero, one_mul]
      exact hG
    · have hp := hpar h hh h0
      rw [walkT_succ_pos f h0]
      simp only [treeF, show h ≠ 0 by omega, ↓reduceIte]
      rw [mul_assoc]
      exact bi_mapB (hlet h hh h0) (ih _ (by omega) G γ hG)

theorem bi_walkIT
    (hinv : ∀ k < c, 0 < k → PRep n w (invLetterK PS PSI kS (stAt T (rlab n (n * w) R k)))
      (σ (rlab n (n * w) R k))⁻¹) :
    ∀ f k, k < c → ∀ G γ, BI n w nb (l + 1) G b γ →
      BI n w nb (l + 1) (walkIT n w (mask w) (n * w) nb PS PSI kS T R l f k G) b
        ((treeF σ (rpar w (mask w) (n * w) R) (rlab n (n * w) R) f k)⁻¹ * γ) := by
  intro f
  induction f with
  | zero =>
    intro k _ G γ hG
    have e : walkIT n w (mask w) (n * w) nb PS PSI kS T R l 0 k G = G := rfl
    rw [e, treeF, inv_one, one_mul]
    exact hG
  | succ f ih =>
    intro k hk G γ hG
    rcases Nat.eq_zero_or_pos k with rfl | h0
    · have e : walkIT n w (mask w) (n * w) nb PS PSI kS T R l (f + 1) 0 G = G := rfl
      rw [e, treeF_zero, inv_one, one_mul]
      exact hG
    · have hp := hpar k hk h0
      rw [walkIT_succ_pos f h0]
      simp only [treeF, show k ≠ 0 by omega, ↓reduceIte]
      rw [mul_inv_rev, mul_assoc]
      exact ih _ (by omega) _ _ (bi_mapB (hinv k hk h0) hG)

end Walks

theorem siftBK_succ (n w m nw nb : Nat) (S SI LR ST : Nat → Nat) (kS d l G : Nat) :
    siftBK n w m nw nb S SI LR ST kS (d + 1) l G =
      strictB (LR l) (fun R => strictB (ST l) (fun T =>
        strictB (rpos w m nw R (pg w m G l)) (fun k =>
        bIf(Nat.blt k (rcnt R),
          strictB (walkIT n w m nw nb S SI kS T R l k k G)
            (siftBK n w m nw nb S SI LR ST kS d (Nat.succ l)), false)))) := rfl

theorem schreier_mem_fix {n kO : Nat} {S : Array (Array Nat)} {base : Array Nat}
    {W : Array (List Int)} (hd : Hd n S base kO W) {i h j : Nat} (hi : i < base.size)
    (hh : h < (lev n S base i).pts.size) (hj : j < (rawSteps n S base i).size)
    {σ : Equiv.Perm (Fin n)} (hσ : Rep n (rawSteps n S base i)[j]! σ)
    (hk : (lev n S base i).pos[((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]!]! <
      (lev n S base i).pts.size) :
    (trP n S base i
        ((lev n S base i).pos[((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]!]!))⁻¹ *
      (σ * trP n S base i h) ∈ Fix n S kO base (i + 1) := by
  have F := lev_facts hd hi
  obtain ⟨σ', hσ', hσm⟩ := step_rep hd hj
  have e := hσ.unique hσ'
  subst e
  set z := ((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]! with hz
  have hzn : z < n := steps_lt hd j hj _ (F.pts_lt h hh)
  have hT := tr_spec hd hi
  have hTi := Subgroup.inv_mem _ (hT _ hk).1
  refine ⟨Subgroup.mul_mem _ hTi.1 (Subgroup.mul_mem _ hσm (hT h hh).1).1, fun t ht hb => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, (hT h hh).1.2 t ht hb, hσm.2 t ht hb,
      hTi.2 t ht hb]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    apply Fin.ext
    rw [(hT _ hk).2, F.pts_pos z hzn hk, ← hσ', (hT h hh).2]

section SiftB

variable {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)} {base : Array Nat}
  {W : Array (List Int)}
  (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
  (hd : Hd n S base kO W)
include hb hp hd

@[expose] def TreeAgree (n w nb : Nat) (S : Array (Array Nat)) (base : Array Nat)
    (LR : Nat → Nat) : Prop :=
  ∀ l < nb, (∀ k < rcnt (LR l), 0 < k → rpar w (mask w) (n * w) (LR l) k < k ∧
      rlab n (n * w) (LR l) k < (rawSteps n S base l).size) ∧
    Agree n w (LR l) (lev n S base l) (fun k => treeF (stp n S base l)
      (rpar w (mask w) (n * w) (LR l)) (rlab n (n * w) (LR l)) k k)

omit hd in
theorem treeAgree_of (hbl : ∀ t < nb, base[t]! < n) {LR : Nat → Nat}
    (ht : TreeOK n w PS PSI LR kS nb BP) : TreeAgree n w nb S base LR :=
  fun l hl => agree_treeK hb hp hbl hl (ht l hl).1 (ht l hl).2

theorem siftA_of_siftBK (hn : 0 < n) (hk : kS < 128) (hbl : ∀ t < nb, base[t]! < n)
    (hsep : Sep n S base) {LR ST : Nat → Nat} (hst : StepsOK n w PS ST kS nb BP)
    (hag : TreeAgree n w nb S base LR) :
    ∀ d l, l + d = nb → ∀ (G : Nat) (g : Array Nat) (γ : Equiv.Perm (Fin n)),
      BI n w nb l G (fun t => toF hn base[t]!) γ → Rep n g γ → γ ∈ Fix n S kO base l →
      siftBK n w (mask w) (n * w) nb PS PSI LR ST kS d l G = true →
      siftA n (rawLevels n S base) base l g = true := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  intro d
  induction d with
  | zero =>
    intro l hl G g γ _ hg hm _
    have hl' : l = base.size := by omega
    have hsub : Set.range (fun j : Fin kO => permOfArr n S[j.val]!) ⊆
        {g : Equiv.Perm (Fin n) | ∃ j < S.size, permOfArr n S[j]! = g} := by
      rintro _ ⟨j, rfl⟩
      exact ⟨j.val, lt_of_lt_of_le j.2 hd.kO_le, rfl⟩
    have hγ : γ = 1 := hsep γ (Subgroup.closure_mono hsub hm.1)
      (fun t ht h => hm.2 t (by omega) h)
    rw [siftA, dite_eq_right (by rw [chainLevels_size]; omega)]
    rw [hγ] at hg
    exact (eqA_iff hg rep_idA).2 rfl
  | succ d ih =>
    intro l hl G g γ hG hg hm h
    have hlb : l < nb := by omega
    have hlb' : l < base.size := by omega
    have hls : l < (rawLevels n S base).size := by rw [chainLevels_size]; omega
    obtain ⟨hpar, A⟩ := hag l hlb
    obtain ⟨_, _, _, hinv⟩ := kernel_steps hb hp hk hbl hlb.le
    have F := lev_facts hd hlb'
    have hbl' := hbl l hlb
    rw [siftBK_succ, hst l hlb] at h
    simp only [strictB_eq, bIf_eq] at h
    have hGl := hG l le_rfl hlb
    simp only [toF_eq hn hbl'] at hGl
    have hz : g[base[l]!]! = pg w (mask w) G l := by
      rw [hg.apply hbl', hGl]
    have hzn : pg w (mask w) G l < n := by
      rw [← hz]
      exact hg.lt hbl'
    split at h
    · rename_i hk1
      have hk' := Nat.blt_eq.mp hk1
      have hK := (A.pos _ hzn).1 hk'
      have hKe := A.posE _ hzn hK
      set K := rpos w (mask w) (n * w) (LR l) (pg w (mask w) G l) with hKdef
      have hW := bi_walkIT (σ := stp n S base l) (b := fun t => toF hn base[t]!)
        (fun k hk hk0 => (hpar k hk hk0).1)
        (fun k hk hk0 => hinv _ (hpar k hk hk0).2) K K hk' G γ (bi_mono hG)
      rw [siftA, dite_eq_left hls, chainLevels_getElem hls, hz]
      simp only [hK, decide_true, Bool.true_and]
      rw [← hKe]
      have hKm : K < (lev n S base l).pts.size := by rw [hKe]; exact hK
      have eT : treeF (stp n S base l) (rpar w (mask w) (n * w) (LR l))
          (rlab n (n * w) (LR l)) K K = trP n S base l K :=
        Rep.unique (A.tr K hKm).1 (rep_tr hd hlb' hKm)
      rw [eT] at hW
      have hT := tr_spec hd hlb' K hKm
      have hTi := Subgroup.inv_mem _ hT.1
      refine ih (l + 1) (by omega) _ _ _ hW (rep_compA (rep_trInv hd hlb' hKm) hg)
        ⟨Subgroup.mul_mem _ hTi.1 hm.1, fun t ht hb' => ?_⟩ h
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · rw [Equiv.Perm.mul_apply, hm.2 t ht hb', hTi.2 t ht hb']
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
        apply Fin.ext
        rw [hT.2, hKe, F.pts_pos _ hzn hK, hGl]
    · exact absurd h Bool.false_ne_true

theorem schreierOK_of_schB (hn : 0 < n) (hk : kS < 128) (hbl : ∀ t < nb, base[t]! < n)
    (hsep : Sep n S base) {LR ST : Nat → Nat} (hst : StepsOK n w PS ST kS nb BP)
    (hag : TreeAgree n w nb S base LR) {i : Nat} (hi : i < nb)
    (hs : ∀ h < rcnt (LR i), schBPt n w (mask w) (n * w) nb PS PSI LR ST kS BP i h = true)
    (chunks : Nat) :
    CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i (rawSteps n S base i)
      (rawLevels n S base)[i]! chunks = true := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hi' : i < base.size := by omega
  change CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i (rawSteps n S base i)
    (lev n S base i) chunks = true
  unfold CFSG.Monster.B.Co2.Native.schreierOK
  apply parLt_of_forall
  intro h hh
  rw [allLt_iff]
  intro j hj
  dsimp only
  obtain ⟨hpar, A⟩ := hag i hi
  obtain ⟨hcnt, hpr, hlet, hinv⟩ := kernel_steps hb hp hk hbl hi.le
  have F := lev_facts hd hi'
  have hhc : h < rcnt (LR i) := by rw [A.cnt]; exact hh
  have key := hs h hhc
  unfold schBPt at key
  rw [hst i hi] at key
  simp only [strictB_eq] at key
  have hj' : j < stCnt (stepsAt n w PS kS BP i) := by rw [hcnt]; exact hj
  obtain ⟨hk1, hk2⟩ := (bAnd_iff _ _).1 (allN_spec key j hj')
  have hph : (lev n S base i).pts[h]! < n := F.pts_lt h hh
  have hzs : pg w (mask w) (letterK PS PSI kS (stAt (stepsAt n w PS kS BP i) j))
      (rpt w (mask w) (LR i) h) = ((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]! := by
    rw [A.pt h hh]
    exact (hpr j hj ⟨_, hph⟩).trans ((rep_stp hb hp hj).apply hph).symm
  rw [hzs] at hk1 hk2
  have hzn : ((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]! < n :=
    (rep_stp hb hp hj).lt hph
  have hKc := Nat.blt_eq.mp hk1
  have hK := (A.pos _ hzn).1 hKc
  have hKe := A.posE _ hzn hK
  simp only [hK, decide_true, Bool.true_and]
  set K := rpos w (mask w) (n * w) (LR i) ((rawSteps n S base i)[j]!)[(lev n S base i).pts[h]!]!
    with hKdef
  have hKm : K < (lev n S base i).pts.size := by rw [hKe]; exact hK
  have hBP : BI n w nb (i + 1) BP (fun t => toF hn base[t]!) 1 := fun t _ ht2 => by
    simp only [Equiv.Perm.one_apply, toF_eq hn (hbl t ht2)]
    exact (hb.2.2.2.2.2.2 t ht2).symm
  have hW1 := bi_walkT (σ := stp n S base i) (fun k hk hk0 => (hpar k hk hk0).1)
    (fun k hk hk0 => hlet _ (hpar k hk hk0).2) h h hhc BP 1 hBP
  have hW2 := bi_mapB (hlet j hj) hW1
  have hW3 := bi_walkIT (σ := stp n S base i) (fun k hk hk0 => (hpar k hk hk0).1)
    (fun k hk hk0 => hinv _ (hpar k hk hk0).2) K K hKc _ _ hW2
  have eh : treeF (stp n S base i) (rpar w (mask w) (n * w) (LR i)) (rlab n (n * w) (LR i)) h h =
      trP n S base i h := Rep.unique (A.tr h hh).1 (rep_tr hd hi' hh)
  have eK : treeF (stp n S base i) (rpar w (mask w) (n * w) (LR i)) (rlab n (n * w) (LR i)) K K =
      trP n S base i K := Rep.unique (A.tr K hKm).1 (rep_tr hd hi' hKm)
  rw [eh, eK, mul_one] at hW3
  have hfix := schreier_mem_fix hd hi' hh hj (rep_stp hb hp hj) hK
  rw [← hKe] at hfix ⊢
  exact siftA_of_siftBK hb hp hd hn hk hbl hsep hst hag (nb - (i + 1)) (i + 1) (by omega) _ _ _
    hW3 (rep_compA (rep_trInv hd hi' hKm) (rep_compA (rep_stp hb hp hj) (rep_tr hd hi' hh)))
    hfix hk2

end SiftB

end CFSG.KS.Raw.Orb

end
