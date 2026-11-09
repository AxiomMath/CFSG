module

public import CFSG.Certificates.Kernel.Q47KRunSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.HexaKGlue

public section

namespace CFSG.KC.Q47K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK

variable {n w ng : Nat} {G : Nat → Nat}

theorem mulK_assoc {p q r : Nat} (hp : PP n w p) (hr : PP n w r) :
    HexaK.mul n w (HexaK.mul n w p q) r = HexaK.mul n w p (HexaK.mul n w q r) := by
  obtain ⟨hn, hw, -, -⟩ := PF.canon_facts hp.1
  obtain ⟨-, -, -, hrr⟩ := PF.canon_facts hr.1
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  change pcomp n w (mask w) (pcomp n w (mask w) p q) r = pcomp n w (mask w) p (pcomp n w (mask w) q r)
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) (PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pcomp hn32 (hrr i hi), PF.pg_pcomp hn32 hi, PF.pg_pcomp hn32 hi]

theorem mulK_id {p : Nat} (hp : PP n w p) : HexaK.mul n w (pidn n w) p = p := by
  obtain ⟨hn, hw, hp0, hpr⟩ := PF.canon_facts hp.1
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  change pcomp n w (mask w) (pidn n w) p = p
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) hp0 fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw (hpr i hi)]

theorem runK_ind (P : Nat → Prop) (h0 : P (pidn n w))
    (hs : ∀ k < ng, ∀ y, P y → P (HexaK.mul n w (G k) y)) (fuel : Nat) :
    ∀ y ∈ runK n w ng G fuel, P y := by
  rw [runK_iter]
  induction fuel with
  | zero =>
    intro y hy
    rw [List.mem_singleton.1 hy]
    exact h0
  | succ f ih =>
    rw [Function.iterate_succ_apply']
    generalize (rkF n w ng G)^[f] ([pidn n w], 0) = st at ih ⊢
    obtain ⟨L, i⟩ := st
    unfold rkF
    dsimp only at ih ⊢
    split
    · next hlt =>
      rw [runStep_eq]
      intro y hy
      rcases (foldl_addN (fun k => HexaK.mul n w (G k) (L.getD i 0)) (List.range ng) L).2.2.2.2 y hy
        with hy | ⟨k, hk, rfl⟩
      · exact ih y hy
      · exact hs k (List.mem_range.1 hk) _ (ih _ (getD_mem hlt))
    · exact ih

theorem pidn_mem_runK (fuel : Nat) : pidn n w ∈ runK n w ng G fuel := by
  rw [runK_iter]
  induction fuel with
  | zero => exact List.mem_singleton_self _
  | succ f ih =>
    rw [Function.iterate_succ_apply']
    generalize (rkF n w ng G)^[f] ([pidn n w], 0) = st at ih ⊢
    obtain ⟨L, i⟩ := st
    unfold rkF
    dsimp only at ih ⊢
    split
    · rw [runStep_eq]
      exact (foldl_addN (fun k => HexaK.mul n w (G k) (L.getD i 0)) (List.range ng) L).2.2.1 _ ih
    · exact ih

theorem addN_nodup {L : List Nat} (y : Nat) (h : L.Nodup) : (addN L y).Nodup := by
  unfold addN
  split
  · exact h
  · next hy =>
    rw [List.nodup_append]
    refine ⟨h, List.nodup_singleton y, fun a ha b hb e => hy ?_⟩
    rw [List.mem_singleton.1 hb] at e
    rwa [← e]

theorem foldl_addN_nodup (f : Nat → Nat) : ∀ (ks : List Nat) (L : List Nat), L.Nodup →
    (ks.foldl (fun acc k => addN acc (f k)) L).Nodup
  | [], _, h => h
  | _ :: ks, _, h => foldl_addN_nodup f ks _ (addN_nodup _ h)

theorem runK_nodup (fuel : Nat) : (runK n w ng G fuel).Nodup := by
  rw [runK_iter]
  induction fuel with
  | zero => exact List.nodup_singleton _
  | succ f ih =>
    rw [Function.iterate_succ_apply']
    generalize (rkF n w ng G)^[f] ([pidn n w], 0) = st at ih ⊢
    obtain ⟨L, i⟩ := st
    unfold rkF
    dsimp only at ih ⊢
    split
    · rw [runStep_eq]
      exact foldl_addN_nodup _ _ L ih
    · exact ih

theorem runK_closed {fuel : Nat} (hf : (runK n w ng G fuel).length ≤ fuel) :
    ∀ y ∈ runK n w ng G fuel, ∀ k < ng, HexaK.mul n w (G k) y ∈ runK n w ng G fuel := by
  have hinv : ∀ f, ((rkF n w ng G)^[f] ([pidn n w], 0)).2 ≤
      ((rkF n w ng G)^[f] ([pidn n w], 0)).1.length ∧
      ∀ j < ((rkF n w ng G)^[f] ([pidn n w], 0)).2, ∀ k < ng,
        HexaK.mul n w (G k) (((rkF n w ng G)^[f] ([pidn n w], 0)).1.getD j 0) ∈
          ((rkF n w ng G)^[f] ([pidn n w], 0)).1 := by
    intro f
    induction f with
    | zero => exact ⟨Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    | succ f ih =>
      rw [Function.iterate_succ_apply']
      generalize (rkF n w ng G)^[f] ([pidn n w], 0) = st at ih ⊢
      obtain ⟨L, i⟩ := st
      obtain ⟨h2, h3⟩ := ih
      dsimp only at h2 h3
      unfold rkF
      dsimp only
      split
      · next hlt =>
        rw [runStep_eq]
        obtain ⟨f1, f2, f3, f4, -⟩ := foldl_addN (fun k => HexaK.mul n w (G k) (L.getD i 0))
          (List.range ng) L
        refine ⟨Nat.succ_le_of_lt (lt_of_lt_of_le hlt f1), fun j hj k hk => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [f2 j (by omega)]
          exact f3 _ (h3 j hj k hk)
        · rw [f2 _ hlt]
          exact f4 k (List.mem_range.2 hk)
      · exact ⟨h2, h3⟩
  have hI := hinv fuel
  rw [runK_iter] at hf ⊢
  generalize hst : (rkF n w ng G)^[fuel] ([pidn n w], 0) = st at hf hI ⊢
  have hfin : st.2 = st.1.length := by
    rcases rkF_count (n := n) (w := w) (ng := ng) (G := G) ([pidn n w], 0) rfl fuel with h | h
    · rw [hst] at h
      omega
    · rw [hst] at h
      by_contra hne
      have hlt : st.2 < st.1.length := by omega
      have e := congrArg Prod.snd h
      unfold rkF at e
      rw [ite_eq_left hlt] at e
      simp at e
  intro y hy k hk
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have := hI.2 j (by omega) k hk
  rwa [List.getD_eq_getElem _ _ hj] at this

theorem runK_PP (hsz : szOK n w = true) (hP : ∀ k < ng, PP n w (G k)) (fuel : Nat) :
    ∀ y ∈ runK n w ng G fuel, PP n w y :=
  runK_ind (PP n w) (PP.id hsz) (fun k hk _ hy => (hP k hk).mul hy) fuel

theorem runK_prod (hsz : szOK n w = true) (hP : ∀ k < ng, PP n w (G k)) {S : List Nat}
    (pS : ∀ y ∈ S, PP n w y) (hS : ∀ y ∈ S, ∀ k < ng, HexaK.mul n w (G k) y ∈ S) (fuel : Nat) :
    ∀ x ∈ runK n w ng G fuel, ∀ y ∈ S, HexaK.mul n w x y ∈ S := by
  have h := runK_ind (fun x => PP n w x ∧ ∀ y ∈ S, HexaK.mul n w x y ∈ S)
    ⟨PP.id hsz, fun y hy => by rw [mulK_id (pS y hy)]; exact hy⟩
    (fun k hk x hx => ⟨(hP k hk).mul hx.1, fun y hy => by
      rw [mulK_assoc (hP k hk) (pS y hy)]
      exact hS _ (hx.2 y hy) k hk⟩) fuel
  exact fun x hx => (h x hx).2

theorem gen_PP {gD : Nat} {GD : Nat → Nat} {a : Nat} (pD : ∀ k < gD, PP n w (GD k))
    (pa : PP n w a) : ∀ k < gD + 1, PP n w (nIf(Nat.blt k gD, GD k, a)) := by
  intro k hk
  rw [nIf_ite]
  split
  · next h => exact pD k (Nat.blt_eq.mp h)
  · exact pa

theorem runK_sub {gD fD fa fb : Nat} {GD : Nat → Nat} {a b d e : Nat} (hsz : szOK n w = true)
    (pD : ∀ k < gD, PP n w (GD k)) (pa : PP n w a) (hd : d ∈ runK n w gD GD fD)
    (he : e ∈ runK n w gD GD fD) (hb : b = HexaK.mul n w d (HexaK.mul n w a e))
    (hf : (runK n w (gD + 1) (fun k => nIf(Nat.blt k gD, GD k, a)) fa).length ≤ fa) :
    ∀ y ∈ runK n w (gD + 1) (fun k => nIf(Nat.blt k gD, GD k, b)) fb,
      y ∈ runK n w (gD + 1) (fun k => nIf(Nat.blt k gD, GD k, a)) fa := by
  have pL := runK_PP hsz (gen_PP pD pa) fa
  have cl := runK_closed hf
  have hDcl : ∀ y ∈ runK n w (gD + 1) (fun k => nIf(Nat.blt k gD, GD k, a)) fa, ∀ k < gD,
      HexaK.mul n w (GD k) y ∈ runK n w (gD + 1) (fun k => nIf(Nat.blt k gD, GD k, a)) fa := by
    intro y hy k hk
    have := cl y hy k (by omega)
    rwa [nIf_ite, if_pos (Nat.blt_eq.mpr hk)] at this
  have hacl : ∀ y ∈ runK n w (gD + 1) (fun k => nIf(Nat.blt k gD, GD k, a)) fa,
      HexaK.mul n w a y ∈ runK n w (gD + 1) (fun k => nIf(Nat.blt k gD, GD k, a)) fa := by
    intro y hy
    have := cl y hy gD (by omega)
    rwa [nIf_ite, if_neg (by rw [Nat.blt_eq]; omega)] at this
  have prod := runK_prod hsz pD pL hDcl fD
  have pDL := runK_PP hsz pD fD
  refine runK_ind _ (pidn_mem_runK fa) (fun k hk y hy => ?_) fb
  rw [nIf_ite]
  split
  · next h => exact hDcl y hy k (Nat.blt_eq.mp h)
  · rw [hb, mulK_assoc (pDL d hd) (pL y hy), mulK_assoc pa (pL y hy)]
    exact prod d hd _ (hacl _ (prod e he y hy))

theorem runK_conj_len {gD fD fa fb : Nat} {GD : Nat → Nat} {a b d e : Nat} (hsz : szOK n w = true)
    (pD : ∀ k < gD, PP n w (GD k)) (pa : PP n w a) (hd : d ∈ runK n w gD GD fD)
    (he : e ∈ runK n w gD GD fD) (hb : b = HexaK.mul n w d (HexaK.mul n w a e))
    (ha : a = HexaK.mul n w e (HexaK.mul n w b d))
    (hf : (runK n w (gD + 1) (fun k => nIf(Nat.blt k gD, GD k, a)) fa).length ≤ fa)
    (hfb : (runK n w (gD + 1) (fun k => nIf(Nat.blt k gD, GD k, a)) fa).length ≤ fb) :
    (runK n w (gD + 1) (fun k => nIf(Nat.blt k gD, GD k, b)) fb).length =
      (runK n w (gD + 1) (fun k => nIf(Nat.blt k gD, GD k, a)) fa).length := by
  have pDL := runK_PP hsz pD fD
  have pb : PP n w b := by
    rw [hb]
    exact (pDL d hd).mul (pa.mul (pDL e he))
  have l1 := ((runK_nodup fb).subperm (runK_sub hsz pD pa hd he hb hf)).length_le
  have l2 := ((runK_nodup fa).subperm (runK_sub (fa := fb) (fb := fa) hsz pD pb he hd ha (by omega))).length_le
  omega

@[expose] noncomputable def conjWK (gD : Nat) (GD : Nat → Nat) (R : List Nat)
    (W : List (Nat × Nat × Nat × Nat)) : Bool :=
  (R.all fun a => (permOK 64 7 (mask 7) (64 * 7) a (pinvS 64 7 (mask 7) a) &&
      Nat.beq (runK 64 7 (Nat.succ gD) (fun k => nIf(Nat.blt k gD, GD k, a)) 200).length 96)) &&
    W.all fun x => memK R x.2.1 && memK (runK 64 7 gD GD 100) x.2.2.1 &&
      memK (runK 64 7 gD GD 100) x.2.2.2 &&
      Nat.beq x.1 (HexaK.mul 64 7 x.2.2.1 (HexaK.mul 64 7 x.2.1 x.2.2.2)) &&
      Nat.beq x.2.1 (HexaK.mul 64 7 x.2.2.2 (HexaK.mul 64 7 x.1 x.2.2.1))

theorem conjWK_sound {gD : Nat} {GD : Nat → Nat} {R : List Nat} {W : List (Nat × Nat × Nat × Nat)}
    (pD : ∀ k < gD, PP 64 7 (GD k)) (h : conjWK gD GD R W = true) :
    ∀ b ∈ W.map Prod.fst,
      (runK 64 7 (Nat.succ gD) (fun k => nIf(Nat.blt k gD, GD k, b)) 200).length = 96 := by
  have hsz : szOK 64 7 = true := by decide
  unfold conjWK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hR, hW⟩ := h
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hW x hx
  rw [memK_eq] at h1 h2 h3
  obtain ⟨pa, la⟩ := hR _ (of_decide_eq_true h1)
  have la' := Nat.eq_of_beq_eq_true la
  exact (runK_conj_len hsz pD (PP_of_permOK hsz pa) (of_decide_eq_true h2) (of_decide_eq_true h3)
    (Nat.eq_of_beq_eq_true h4) (Nat.eq_of_beq_eq_true h5) (la'.le.trans (by decide))
    (la'.le.trans (by decide))).trans la'

theorem memK_append (A B : List Nat) (x : Nat) : memK (A ++ B) x = (memK A x || memK B x) := by
  rw [memK_eq, memK_eq, memK_eq]
  simp only [List.mem_append, Bool.decide_or]

@[expose] noncomputable def addT2 (c : Cls) (S : List Nat) : Cls :=
  ⟨c.gE, c.GE, c.TE, c.T1, c.T2 ++ S, c.gD, c.GD⟩

theorem clsC_addT2 {c : Cls} {S : List Nat}
    (hS : ∀ x ∈ S,
      (runK 64 7 (Nat.succ c.gD) (fun k => nIf(Nat.blt k c.gD, c.GD k, x)) 200).length = 96)
    (t : Nat) : clsC (addT2 c S) t = clsC c t := by
  unfold clsC addT2 clsAt
  simp only [HexaK.orB_eq, memK_append]
  cases h : memK S t
  · rw [Bool.or_false]
  · rw [memK_eq] at h
    rw [hS t (of_decide_eq_true h), Nat.beq_refl]
    simp only [Bool.or_true]

end CFSG.KC.Q47K

end
