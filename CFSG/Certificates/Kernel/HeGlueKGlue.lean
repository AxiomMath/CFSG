module

public import Certificates.Data.Kernel.HeGlueK
public import CFSG.Certificates.Kernel.HeModelKGlue
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeGlueTests

public section

namespace CFSG.KC.HeGlueK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.KC.HeModelK CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.HeTri
open CFSG.KLie.CT (anyN andB orB notB)

variable {n w : Nat}

@[expose] noncomputable def sg (n w a : Nat) : Equiv.Perm (Fin n) := permOfArr n (unpack n w a)

theorem rep_sg {a : Nat} (ha : PP n w a) : Rep n (unpack n w a) (sg n w a) :=
  (rep_permOfArr (CFSG.KS.Raw.Orb.isInvA_unpack (CFSG.KS.PinvS.permOK_pinvS ha.1 ha.2))).1

theorem rep_sg_inv {a : Nat} (ha : PP n w a) :
    Rep n (unpack n w (pinvS n w (mask w) a)) (sg n w a)⁻¹ :=
  (rep_permOfArr (CFSG.KS.Raw.Orb.isInvA_unpack (CFSG.KS.PinvS.permOK_pinvS ha.1 ha.2))).2

theorem PP_eq_iff {a b : Nat} (ha : PP n w a) (hb : PP n w b) : a = b ↔ sg n w a = sg n w b :=
  ⟨fun e => e ▸ rfl, fun e => Nat.eq_of_beq_eq_true (by
    rw [← eqA_PP ha hb]
    exact (eqA_iff (rep_sg ha) (rep_sg hb)).2 e)⟩

theorem beq_PP {a b : Nat} (ha : PP n w a) (hb : PP n w b) :
    Nat.beq a b = decide (sg n w a = sg n w b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
  exact PP_eq_iff ha hb

theorem _root_.CFSG.KC.BfsPin.PP.mulK {a b : Nat} (ha : PP n w a) (hb : PP n w b) :
    PP n w (mul n w a b) := ha.mul hb

theorem sg_mul {a b : Nat} (ha : PP n w a) (hb : PP n w b) :
    sg n w (mul n w a b) = sg n w a * sg n w b :=
  (rep_sg (ha.mul hb)).unique (by
    rw [← compA_PP ha hb]
    exact rep_compA (rep_sg ha) (rep_sg hb))

theorem sg_pcomp {a b : Nat} (ha : PP n w a) (hb : PP n w b) :
    sg n w (pcomp n w (mask w) a b) = sg n w a * sg n w b := sg_mul ha hb

theorem sg_id (hsz : szOK n w = true) : sg n w (pidn n w) = 1 :=
  (rep_sg (PP.id hsz)).unique (by rw [← idA_eq hsz]; exact rep_idA)

theorem sg_pinv {a : Nat} (ha : PP n w a) : sg n w (pinvS n w (mask w) a) = (sg n w a)⁻¹ :=
  (rep_sg ha.inv).unique (rep_sg_inv ha)

theorem pinvS_pidn (hsz : szOK n w = true) : pinvS n w (mask w) (pidn n w) = pidn n w :=
  (PP_eq_iff (PP.id hsz).inv (PP.id hsz)).2 (by rw [sg_pinv (PP.id hsz), sg_id hsz, inv_one])

theorem sg_conj {c x : Nat} (hc : PP n w c) (hx : PP n w x) :
    sg n w (conj n w c x) = sg n w c * sg n w x * (sg n w c)⁻¹ := by
  unfold CFSG.KC.HexaK.conj
  rw [strictN_eq']
  change sg n w (mul n w c (mul n w x (pinvS n w (mask w) c))) = _
  rw [sg_mul hc (hx.mulK hc.inv), sg_mul hx hc.inv, sg_pinv hc, mul_assoc]

theorem sg_pw {a : Nat} (ha : PP n w a) : ∀ k, sg n w (pw n w a k) = sg n w a ^ k
  | 0 => by
    change sg n w (pidn n w) = _
    rw [sg_id ha.sz, pow_zero]
  | k + 1 => by
    change sg n w (strictN (pw n w a k) fun acc => mul n w a acc) = _
    rw [strictN_eq', sg_mul ha (ha.pwK k), sg_pw ha k, pow_succ']

theorem conjW_eq (c x : Nat) : conjW n w c (pinvS n w (mask w) c) x = conj n w c x := by
  unfold conjW CFSG.KC.HexaK.conj
  rw [strictN_eq']
  rfl

theorem PP_of_permOK2 {p q : Nat} (hsz : szOK n w = true)
    (h : permOK n w (mask w) (n * w) p q = true) : PP n w p := by
  obtain ⟨h1, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  have hc : canonK n w (mask w) (n * w) p = true := by
    unfold canonK
    simp only [bAnd_iff]
    exact ⟨hsz, Nat.beq_eq.mpr h1,
      CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (h3 i hi).1⟩
  refine ⟨hc, ⟨fun i hi => (h3 i hi).1, fun a ha b hb e => ?_⟩⟩
  rw [← (h3 a ha).2, ← (h3 b hb).2, e]

theorem PP_of_invOK {a b : Nat} (hsz : szOK n w = true) (h : invOK n w a b = true) :
    PP n w a := by
  unfold invOK at h
  rw [andB_eq, Bool.and_eq_true] at h
  exact PP_of_permOK2 hsz h.1

theorem inv_of_invOK {a b : Nat} (ha : PP n w a) (h : invOK n w a b = true) :
    b = pinvS n w (mask w) a := by
  unfold invOK at h
  rw [andB_eq, Bool.and_eq_true] at h
  have rb := rep_inv_of_isInvA (rep_sg ha) (CFSG.KS.Raw.Orb.isInvA_unpack h.1)
  have e := (eqA_iff rb (rep_sg_inv ha)).2 rfl
  rw [eqA_unpack h.2 ha.inv.1] at e
  exact Nat.eq_of_beq_eq_true e

theorem getD_map_range {α : Type} (f : Nat → α) (g j : Nat) (d : α) :
    ((List.range g).map f).getD j d = if j < g then f j else d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split
  · next h => simp [h]
  · next h => simp [h]

structure WG (n w : Nat) (gs : List (Array Nat)) (g : Nat) (G GI : Nat → Nat) : Prop where
  sz : szOK n w = true
  gs : gs = (List.range g).map fun k => unpack n w (G k)
  pp : ∀ k < g, PP n w (G k)
  inv : ∀ k < g, GI k = pinvS n w (mask w) (G k)

variable {gs : List (Array Nat)} {g : Nat} {G GI : Nat → Nat}

theorem letK_eq (hW : WG n w gs g G GI) (l : Nat) :
    CFSG.ComponentClassification.AS81.HeTri.letterA n gs l = unpack n w (letK n w g G GI l) ∧
      PP n w (letK n w g G GI l) := by
  have e1 : Nat.shiftRight l 1 = l / 2 := by
    change l >>> 1 = l / 2
    rw [Nat.shiftRight_eq_div_pow]
  have e2 : Nat.land l 1 = l % 2 := Nat.and_one_is_mod l
  unfold letK CFSG.ComponentClassification.AS81.HeTri.letterA
  rw [strictN_eq', e1, e2, hW.gs, getD_map_range]
  by_cases hj : l / 2 < g
  · rw [ite_eq_left hj, Nat.blt_eq.mpr hj]
    by_cases hl : l % 2 = 0
    · have hb : Nat.beq (l % 2) 1 = false := by rw [hl]; rfl
      rw [ite_eq_left hl, hb]
      exact ⟨rfl, hW.pp _ hj⟩
    · have h1 : l % 2 = 1 := by omega
      have hb : Nat.beq (l % 2) 1 = true := by rw [h1]; rfl
      rw [ite_eq_right hl, hb]
      change _ = unpack n w (GI (l / 2)) ∧ PP n w (GI (l / 2))
      rw [hW.inv _ hj]
      exact ⟨invCand_PP (hW.pp _ hj), (hW.pp _ hj).inv⟩
  · have hf : Nat.blt (l / 2) g = false := by
      cases h : Nat.blt (l / 2) g
      · rfl
      · exact absurd (Nat.blt_eq.mp h) hj
    rw [ite_eq_right hj, hf, idA_eq hW.sz]
    have hp := PP.id hW.sz
    change _ = unpack n w (pidn n w) ∧ PP n w (pidn n w)
    split
    · exact ⟨rfl, hp⟩
    · exact ⟨by rw [invCand_PP hp, pinvS_pidn hW.sz], hp⟩

theorem evalAcc_eq (hW : WG n w gs g G GI) : ∀ (r : List Nat) (acc : Nat), PP n w acc →
    r.foldl (fun a l => compA n a (CFSG.ComponentClassification.AS81.HeTri.letterA n gs l))
        (unpack n w acc) =
      unpack n w (evalAcc n w g G GI r acc) ∧ PP n w (evalAcc n w g G GI r acc)
  | [], _, h => ⟨rfl, h⟩
  | l :: r, acc, h => by
    obtain ⟨e, p⟩ := letK_eq hW l
    have e2 : evalAcc n w g G GI (l :: r) acc =
        evalAcc n w g G GI r (pcomp n w (mask w) acc (letK n w g G GI l)) := by
      change strictN (mul n w acc (letK n w g G GI l)) (evalAcc n w g G GI r) = _
      rw [strictN_eq']
      rfl
    rw [List.foldl_cons, e, compA_PP h p, e2]
    exact evalAcc_eq hW r _ (h.mul p)

theorem evalW_eq (hW : WG n w gs g G GI) (r : List Nat) :
    evalW n gs r = unpack n w (evalK n w g G GI r) ∧ PP n w (evalK n w g G GI r) := by
  unfold evalW evalK
  rw [idA_eq hW.sz]
  exact evalAcc_eq hW r _ (PP.id hW.sz)

theorem relsK_eq (n w g : Nat) (G GI : Nat → Nat) (rs : List (List Nat)) :
    relsK n w g G GI rs = rs.all (relK n w g G GI) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change CFSG.KLie.CT.andB (relK n w g G GI r) (relsK n w g G GI rs) = _
    rw [ih, andB_eq, List.all_cons]

theorem relsW_eq (n w g : Nat) (G GI : Nat → Nat) (rs : List (List Nat)) (f : Nat) :
    relsW n w g G GI rs f = relsK n w g G GI rs := by
  unfold relsW
  cases hb : Nat.blt f rs.length
  · rfl
  · change CFSG.KLie.CT.andB _ _ = _
    rw [andB_eq]
    cases hr : relsK n w g G GI rs
    · exact Bool.and_false _
    · rw [relsK_eq, List.all_eq_true] at hr
      have hf := Nat.blt_eq.mp hb
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hf, Option.getD_some,
        hr _ (List.getElem_mem hf)]
      rfl

theorem relsOK_eq (hW : WG n w gs g G GI) (rs : List (List Nat)) :
    relsOK n gs rs = relsK n w g G GI rs := by
  unfold relsOK
  rw [relsK_eq]
  refine all_congr_mem fun r _ => ?_
  obtain ⟨e, p⟩ := evalW_eq hW r
  rw [e, idA_eq hW.sz, eqA_PP p (PP.id hW.sz)]
  rfl

theorem ord12_eq {x : Nat} (hx : PP n w x) : isOrd12 n (unpack n w x) = ord12K n w x := by
  have hsz := hx.sz
  have p2 := hx.mulK hx
  have p4 := p2.mulK p2
  have p6 := p4.mulK p2
  have p12 := p6.mulK p6
  have hi := PP.id hsz
  unfold isOrd12 ord12K
  simp only [strictB_eq', andB_eq, notB_eq]
  rw [HeModelK.powN_PP hx, HeModelK.powN_PP hx, HeModelK.powN_PP hx, idA_eq hsz,
    eqA_PP (hx.pwK 12) hi, eqA_PP (hx.pwK 6) hi, eqA_PP (hx.pwK 4) hi, beq_PP (hx.pwK 12) hi,
    beq_PP (hx.pwK 6) hi,
    beq_PP (hx.pwK 4) hi, beq_PP p12 hi, beq_PP p6 hi, beq_PP p4 hi, sg_pw hx, sg_pw hx, sg_pw hx,
    sg_mul p6 p6, sg_mul p4 p2, sg_mul p2 p2, sg_mul hx hx, sg_id hsz]
  have e2 : sg n w x * sg n w x = sg n w x ^ 2 := (sq _).symm
  have e4 : sg n w x ^ 2 * sg n w x ^ 2 = sg n w x ^ 4 := by rw [← pow_add]
  have e6 : sg n w x ^ 4 * sg n w x ^ 2 = sg n w x ^ 6 := by rw [← pow_add]
  have e12 : sg n w x ^ 6 * sg n w x ^ 6 = sg n w x ^ 12 := by rw [← pow_add]
  rw [e2, e4, e6, e12, Bool.and_assoc]

theorem distinctK_facts {N : Nat} {T S : Nat → Nat} (h : distinctK N T S = true) :
    (∀ k l, k ≤ l → l < N → T (S k) ≤ T (S l)) ∧ (∀ k < N, S k < N) ∧
      ∀ a < N, ∃ k < N, S k = a := by
  unfold distinctK at h
  simp only [bAnd_iff] at h
  obtain ⟨hlt, hS, -⟩ := h
  have hstep : ∀ k, k + 1 < N → T (S k) < T (S (k + 1)) :=
    fun k hk => Nat.blt_eq.mp (allN_spec hlt k (by change k < N - 1; omega))
  have hmono : ∀ k l, k < l → l < N → T (S k) < T (S l) := by
    intro k l
    induction l with
    | zero => intro h1; omega
    | succ l ih =>
      intro hkl hl
      rcases Nat.lt_or_ge k l with h1 | h1
      · exact Nat.lt_trans (ih h1 (by omega)) (hstep l hl)
      · have e : k = l := by omega
        rw [e]
        exact hstep l hl
  have hS' : ∀ k < N, S k < N := fun k hk => Nat.blt_eq.mp (allN_spec hS k hk)
  refine ⟨fun k l hkl hl => ?_, hS', fun a ha => ?_⟩
  · rcases Nat.lt_or_eq_of_le hkl with h1 | h1
    · exact Nat.le_of_lt (hmono k l h1 hl)
    · rw [h1]
  · let f : Fin N → Fin N := fun k => ⟨S k, hS' k k.2⟩
    have hf : Function.Injective f := fun a b e => by
      have e' : S a = S b := congrArg Fin.val e
      rcases Nat.lt_trichotomy a.1 b.1 with h1 | h1 | h1
      · exact absurd (congrArg T e') (Nat.ne_of_lt (hmono _ _ h1 b.2))
      · exact Fin.ext h1
      · exact absurd (congrArg T e').symm (Nat.ne_of_lt (hmono _ _ h1 a.2))
    obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.1 hf) ⟨a, ha⟩
    exact ⟨k.1, k.2, congrArg Fin.val hk⟩

theorem memS_body {N x k : Nat} {T S : Nat → Nat} (hd : distinctK N T S = true) :
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (anyN N fun j => Nat.beq (T j) x) false
        (CFSG.KLie.CT.orB (CFSG.KLie.CT.andB (Nat.beq k 0) (Nat.blt x (T (S 0))))
          (CFSG.KLie.CT.andB (Nat.blt k N) (CFSG.KLie.CT.andB (Nat.blt (T (S k)) x)
            (CFSG.KLie.CT.orB (Nat.ble N (Nat.succ k)) (Nat.blt x (T (S (Nat.succ k)))))))))
      true (CFSG.KLie.CT.andB (Nat.blt k N) (Nat.beq (T (S k)) x)) =
      anyN N fun j => Nat.beq x (T j) := by
  obtain ⟨hmono, hS, hsurj⟩ := distinctK_facts hd
  have hnot : (∀ j < N, T j ≠ x) → (anyN N fun j => Nat.beq x (T j)) = false := by
    intro hn
    rw [anyN_eq, List.any_eq_false]
    intro j hj e
    exact hn j (List.mem_range.1 hj) (Nat.eq_of_beq_eq_true e).symm
  cases h1 : CFSG.KLie.CT.andB (Nat.blt k N) (Nat.beq (T (S k)) x)
  · cases h2 : CFSG.KLie.CT.orB (CFSG.KLie.CT.andB (Nat.beq k 0) (Nat.blt x (T (S 0))))
        (CFSG.KLie.CT.andB (Nat.blt k N) (CFSG.KLie.CT.andB (Nat.blt (T (S k)) x)
          (CFSG.KLie.CT.orB (Nat.ble N (Nat.succ k)) (Nat.blt x (T (S (Nat.succ k)))))))
    · change (anyN N fun j => Nat.beq (T j) x) = _
      rw [anyN_eq, anyN_eq]
      exact congrArg _ (funext fun j => by
        rw [Bool.eq_iff_iff, Nat.beq_eq, Nat.beq_eq]
        exact eq_comm)
    · change false = _
      refine (hnot fun j hj e => ?_).symm
      obtain ⟨k', hk', rfl⟩ := hsurj j hj
      subst e
      simp only [orB_eq, andB_eq, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq,
        Nat.ble_eq, Nat.succ_eq_add_one] at h2
      rcases h2 with ⟨rfl, h2⟩ | ⟨hk, hx, h3⟩
      · have := hmono 0 k' (Nat.zero_le _) hk'
        omega
      · rcases Nat.lt_or_ge k k' with h4 | h4
        · rcases h3 with h3 | h3
          · omega
          · have := hmono (k + 1) k' h4 hk'
            omega
        · have := hmono k' k h4 hk
          omega
  · change true = _
    rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
    rw [anyN_eq]
    refine (List.any_eq_true.2 ⟨S k, List.mem_range.2 (hS k h1.1), ?_⟩).symm
    rw [← h1.2]
    exact Nat.beq_refl _

theorem memS_eq {N h x : Nat} {T S : Nat → Nat} (hd : distinctK N T S = true) :
    memS N T S h x = CFSG.KC.HexaK.inL N T x := by
  unfold memS CFSG.KC.HexaK.inL
  rw [strictB_eq', strictB_eq', strictB_eq']
  exact memS_body hd

theorem classOK_sound {d : GK} {m a b : Nat} {X E S : Nat → Nat}
    (hk : bfsK 64 7 d.g23 d.G23 d.N23 d.T23 E S = true) (hG : ∀ k < d.g23, PP 64 7 (d.G23 k))
    (hI : ∀ k < d.g23, d.G23I k = pinvS 64 7 (mask 7) (d.G23 k))
    (hT : ∀ i < d.N23, PP 64 7 (d.T23 i)) (h : classOK d m X a b = true) :
    ∀ i < d.N23, conj 64 7 (d.T23 i) a ≠ b := by
  unfold classOK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have hm : 0 < m := Nat.blt_eq.mp h0
  have hX : ∀ s < m, X s < d.N23 := fun s hs => Nat.blt_eq.mp (allN_spec h1 s hs)
  have hPX : ∀ s < m, PP 64 7 (d.T23 (X s)) := fun s hs => hT _ (hX s hs)
  have hsz : szOK 64 7 = true := (hPX 0 hm).sz
  have hcl : ∀ s < m, ∀ k < d.g23, ∃ t < m,
      d.T23 (X t) = conj 64 7 (d.G23 k) (d.T23 (X s)) := by
    intro s hs k hk
    have e := allN_spec h4 s hs
    rw [strictB_eq'] at e
    have e2 := allN_spec e k hk
    rw [strictB_eq', hI k hk, conjW_eq] at e2
    obtain ⟨t, ht, e3⟩ := anyN_spec e2
    exact ⟨t, ht, Nat.eq_of_beq_eq_true e3⟩
  have q0 : ∀ s < m, ∃ t < m, d.T23 (X t) = conj 64 7 (pidn 64 7) (d.T23 (X s)) := fun s hs =>
    ⟨s, hs, (PP_eq_iff (hPX s hs) ((PP.id hsz).conjK (hPX s hs))).2 (by
      rw [sg_conj (PP.id hsz) (hPX s hs), sg_id hsz, one_mul, inv_one, mul_one])⟩
  have qs : ∀ y, (PP 64 7 y ∧ ∀ s < m, ∃ t < m, d.T23 (X t) = conj 64 7 y (d.T23 (X s))) →
      ∀ k < d.g23, PP 64 7 (pcomp 64 7 (mask 7) (d.G23 k) y) ∧
        ∀ s < m, ∃ t < m, d.T23 (X t) = conj 64 7 (pcomp 64 7 (mask 7) (d.G23 k) y)
          (d.T23 (X s)) := by
    intro y hy k hk
    refine ⟨(hG k hk).mul hy.1, fun s hs => ?_⟩
    obtain ⟨t, ht, e⟩ := hy.2 s hs
    obtain ⟨t', ht', e'⟩ := hcl t ht k hk
    have pz := hPX s hs
    refine ⟨t', ht', e'.trans ?_⟩
    rw [e]
    refine (PP_eq_iff ((hG k hk).conjK (hy.1.conjK pz)) (((hG k hk).mul hy.1).conjK pz)).2 ?_
    rw [sg_conj (hG k hk) (hy.1.conjK pz), sg_conj hy.1 pz, sg_conj ((hG k hk).mul hy.1) pz,
      sg_pcomp (hG k hk) hy.1]
    simp only [mul_inv_rev, mul_assoc]
  have hQ := (bfsK_points (fun y => PP 64 7 y ∧
    ∀ s < m, ∃ t < m, d.T23 (X t) = conj 64 7 y (d.T23 (X s))) ⟨PP.id hsz, q0⟩ qs hk).2.2.1
  intro i hi e
  obtain ⟨t, ht, et⟩ := (hQ i hi).2 0 hm
  rw [Nat.eq_of_beq_eq_true h2] at et
  have h5 : Nat.beq (d.T23 (X t)) b = true := Nat.beq_eq.mpr (et.trans e)
  have h6 := allN_spec h3 t ht
  rw [notB_eq, h5] at h6
  exact absurd h6 (by decide)

end CFSG.KC.HeGlueK

end
