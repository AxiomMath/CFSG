module

public import CFSG.Certificates.Kernel.TS8.TabSound
public import CFSG.Certificates.Kernel.S63K.GeoTwinSound
public import CFSG.Certificates.Kernel.MonsterB.Co2PermSound

public section

namespace CFSG.KC.TS8

open CFSG.EvenSporadicStandard.Fin76b.TS8D8 CFSG.EvenSporadicStandard.Fin76b.TS8EA16
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
  CFSG.KC.S63K CFSG.KS.PinvS CFSG.KS.SporSch.M24

variable {n w ng : ℕ} {GW EP W Pa La IT : ℕ → ℕ} {MT : ℕ → ℕ → ℕ}

theorem sortDK_inj {P S : ℕ → ℕ} {N : ℕ} (h : sortDK P S N = true) :
    ∀ a < N, ∀ b < N, P a = P b → a = b := by
  unfold sortDK at h
  rw [MatL.allN_iff] at h
  have h' : ∀ k < N, S k < N ∧ (k + 1 = N ∨ P (S k) < P (S (k + 1))) := by
    intro k hk
    have := h k hk
    rw [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at this
    refine ⟨this.1, ?_⟩
    by_cases hk1 : k + 1 = N
    · exact Or.inl hk1
    · right
      have hb : Nat.beq (Nat.succ k) N = false := by
        cases e : Nat.beq (Nat.succ k) N
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hk1
      have h3 := this.2
      rw [hb] at h3
      exact Nat.blt_eq.mp h3
  have hst : ∀ a b, a < b → b < N → P (S a) < P (S b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab | rfl
      · exact Nat.lt_trans (ih hab (by omega)) ((h' b (by omega)).2.resolve_left (by omega))
      · exact (h' a (by omega)).2.resolve_left (by omega)
  let f : Fin N → Fin N := fun k => ⟨S k.val, (h' k.val k.2).1⟩
  have hinj : Function.Injective f := by
    intro a b e
    have e' : S a.val = S b.val := congrArg Fin.val e
    apply Fin.ext
    rcases Nat.lt_trichotomy a.val b.val with hab | hab | hab
    · have := hst _ _ hab b.2; rw [e'] at this; omega
    · exact hab
    · have := hst _ _ hab a.2; rw [e'] at this; omega
  have hsurj := Finite.surjective_of_injective hinj
  intro a ha b hb e
  obtain ⟨a', ha'⟩ := hsurj ⟨a, ha⟩
  obtain ⟨b', hb'⟩ := hsurj ⟨b, hb⟩
  have ea : S a'.val = a := congrArg Fin.val ha'
  have eb : S b'.val = b := congrArg Fin.val hb'
  rcases Nat.lt_trichotomy a'.val b'.val with hab | hab | hab
  · have := hst _ _ hab b'.2; rw [ea, eb] at this; omega
  · rw [← ea, ← eb, hab]
  · have := hst _ _ hab a'.2; rw [ea, eb] at this; omega

theorem isInvA_PP {p : ℕ} (hp : PP n w p) : isInvA n (unpack n w p) (invCand n (unpack n w p)) = true := by
  apply CFSG.KC.Co2Mem.isInvA_invCand (fun i hi => unpack_lt hp hi)
  intro i j hi hj e
  rw [unpack_getElem!, if_pos hi, unpack_getElem!, if_pos hj] at e
  exact hp.2.2 i hi j hj e

theorem hasChain_eq {M : Array (Array ℕ)} {m : ℕ → ℕ → ℕ} (hM : ∀ a b, (M[a]!)[b]! = m a b) :
    ∀ k S C, hasChainIx M k S C = hasChainF m k S C
  | 0, _, _ => rfl
  | k + 1, S, C => by
    unfold hasChainIx hasChainF
    congr 1
    funext T
    cases T with
    | nil => rfl
    | cons X T' =>
      simp only
      rw [hasChain_eq hM k]
      unfold spanIx spanF commIx commF mulIx
      simp only [hM]

theorem checkEA16_of_K {PA PB PU : ℕ} {ws : List (List ℕ)} (hsz : szOK n w = true)
    (hA : PP n w PA) (hB : PP n w PB) (hU : PP n w PU) (hng : ws.length = ng)
    (hW : ∀ k < ng, wordP n w PA PB PU (ws.getD k []) = GW k)
    (hd : ∀ a < 256, ∀ b < 256, EP a = EP b → a = b) (h0 : EP 0 = pidn n w)
    (hp0 : Pa 0 = 0) (hl0 : La 0 = 0)
    (htree : ∀ c, 0 < c → c < 256 → Pa c < c ∧ La c < ng ∧ W (ng * Pa c + La c) = c)
    (hact : ∀ h < 256, ∀ k < ng, W (ng * h + k) < 256 ∧
      pcomp n w (mask w) (EP h) (GW k) = EP (W (ng * h + k)))
    (hrun : orbRunK W Pa La ng 257 0 1 = 256) (hmt : mtK MT W Pa La ng = true)
    (hit : ∀ a < 256, IT a < 256 ∧ pinvS n w (mask w) (EP a) = EP (IT a))
    (hsearch : searchF (mF MT) (iF IT) = true)
    (hchain : hasChainF (mF MT) 5 [0] (invsF (mF MT)) = false) :
    checkEA16 n (unpack n w PA) (unpack n w PB) (unpack n w PU) ws = true := by
  have hGW : ∀ k < ng, PP n w (GW k) := fun k hk => by
    rw [← hW k hk]
    exact (wordT_eq hsz hA hB hU _).2
  have hgs : (gensT n (unpack n w PA) (unpack n w PB) (unpack n w PU) ws).size = ng := by
    simp [gensT, hng]
  have hg : ∀ k < ng, (gensT n (unpack n w PA) (unpack n w PB) (unpack n w PU) ws)[k]! =
      unpack n w (GW k) := fun k hk => by
    unfold gensT
    rw [getElem!_pos _ k (by simp [hng, hk])]
    simp only [List.getElem_toArray, List.getElem_map]
    rw [(wordT_eq hsz hA hB hU _).1, ← hW k hk, List.getD_eq_getElem _ _ (by omega)]
  have hPP : ∀ i < 256, PP n w (EP i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ c ih =>
      intro hc
      by_cases hc0 : c = 0
      · subst hc0
        rw [h0]
        exact PP.id hsz
      · obtain ⟨h1, h2, h3⟩ := htree c (by omega) hc
        have e := (hact (Pa c) (by omega) (La c) h2).2
        rw [h3] at e
        rw [← e]
        exact (ih (Pa c) h1 (by omega)).mul (hGW (La c) h2)
  obtain ⟨e1, e2, e3, e4, e5, e6, ht⟩ :=
    bfsT_of_K (W := W) hsz hgs hg hPP hGW hd h0 hp0 hl0 hact hrun
  have hMT' := hMT hsz hPP hGW h0 ht hact hmt
  generalize hG : gensT n (unpack n w PA) (unpack n w PB) (unpack n w PU) ws = gens at *
  generalize hE : (bfsT n gens).1 = E at *
  have hM : ∀ a b, ((mulTabT n E (idxT E))[a]!)[b]! = mF MT a b := by
    intro a b
    rw [mulTabT_get]
    unfold mF
    by_cases hab : a < 256 ∧ b < 256
    · rw [if_pos hab, if_pos hab, e2 a hab.1, e2 b hab.2, compA_PP (hPP a hab.1) (hPP b hab.2),
        (hMT' b hab.2 a hab.1).2, idxT_getD e1 e2 hPP hd 0 (hMT' b hab.2 a hab.1).1]
    · rw [if_neg hab, if_neg hab]
  have hI : ∀ a, (invTabT n E (idxT E))[a]! = iF IT a := by
    intro a
    rw [invTabT_get]
    unfold iF
    by_cases ha : a < 256
    · rw [if_pos ha, if_pos ha, e2 a ha, invCand_PP (hPP a ha), (hit a ha).2,
        idxT_getD e1 e2 hPP hd 0 (hit a ha).1]
    · rw [if_neg ha, if_neg ha]
  unfold checkEA16 checkD8 chainFreeCheck
  simp only [hG, hE]
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨isInvA_PP hA, isInvA_PP hB⟩, isInvA_PP hU⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩
  · unfold sizeOKT
    rw [e1]
    rfl
  · unfold idOKT
    rw [e2 0 (by norm_num), h0, idA_eq hsz]
    exact eqA_self _
  · unfold permOKT
    rw [allLt_iff]
    intro a ha
    rw [e2 a ha]
    exact isInvA_PP (hPP a ha)
  · unfold distinctOKT
    rw [allLt_iff]
    intro a ha
    rw [allLt_iff]
    intro b hb
    rw [e2 a ha, e2 b (by omega), eqA_PP (hPP a ha) (hPP b (by omega))]
    have hne : EP a ≠ EP b := fun e => absurd (hd a ha b (by omega) e) (by omega)
    have hb : Nat.beq (EP a) (EP b) = false := by
      cases e : Nat.beq (EP a) (EP b)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hne
    rw [hb]
    rfl
  · unfold genOKT
    rw [allLt_iff]
    intro a ha
    by_cases ha0 : a = 0
    · subst ha0
      rfl
    · obtain ⟨t1, t2, t3⟩ := ht a (by omega) ha
      rw [e4 a ha, e6 a ha, hgs, e2 a ha, e2 (Pa a) (by omega), hg (La a) t2,
        compA_PP (hPP (Pa a) (by omega)) (hGW (La a) t2), t3, eqA_self]
      simp [ha0, t1, t2]
  · unfold mulOKT
    rw [allLt_iff]
    intro a ha
    rw [allLt_iff]
    intro b hb
    rw [hM]
    unfold mF
    rw [if_pos ⟨ha, hb⟩, e2 a ha, e2 b hb, compA_PP (hPP a ha) (hPP b hb),
      (hMT' b hb a ha).2, e2 _ (hMT' b hb a ha).1, eqA_self]
    simp [(hMT' b hb a ha).1]
  · unfold invOKT
    rw [allLt_iff]
    intro a ha
    rw [hI]
    unfold iF
    rw [if_pos ha, e2 a ha, invCand_PP (hPP a ha), (hit a ha).2, e2 _ (hit a ha).1, eqA_self]
    simp [(hit a ha).1]
  · unfold searchD8 ord4Ix involInvIx commIx mulIx invIx
    simp only [hM, hI, allLt_eq_allN]
    unfold searchF ord4F involF commF at hsearch
    exact hsearch
  · rw [hasChain_eq hM]
    unfold invsIx mulIx
    simp only [hM]
    unfold invsF at hchain
    exact hchain

end CFSG.KC.TS8

end
