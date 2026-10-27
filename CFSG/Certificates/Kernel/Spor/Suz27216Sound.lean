module

public import Certificates.Data.Kernel.Spor.Suz27216
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KS.Suz27216

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.Prim CFSG.KS.Raw.Orb
open scoped commutatorElement

variable {n w : Nat}

@[expose] def Fix3 (h3 : 3 ≤ n) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ i (hi : i < 3), (g ⟨i, by omega⟩ : Nat) = i

@[expose] def letP (g : Nat → Equiv.Perm (Fin n)) (c : Nat) : Equiv.Perm (Fin n) :=
  if c < 5 then ⁅g 1, g (c + 2)⁆ else ⁅g 1, g (c - 5 + 2)⁆⁻¹

@[expose] def wordP (g : Nat → Equiv.Perm (Fin n)) (L : List Nat) : Equiv.Perm (Fin n) :=
  (L.map (letP g)).prod

theorem strictB_app' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem strictN_app' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem suzPrep_eq {w P : Nat} {g h : Equiv.Perm (Fin n)} (hg : PRep n w P g)
    (hh : PRep n w P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem suzPrep_permOK {w P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    PRep n w P (CFSG.Monster.B.Co2.permOfArr n (unpack n w P)) ∧
      PRep n w Q (CFSG.Monster.B.Co2.permOfArr n (unpack n w P))⁻¹ := by
  have hr := CFSG.Monster.B.Co2.rep_permOfArr (isInvA_unpack h)
  exact ⟨prep_of_rep hr.1, prep_of_rep hr.2⟩

theorem suzPrep_inv {w P Q : Nat} {g : Equiv.Perm (Fin n)}
    (h : permOK n w (mask w) (n * w) P Q = true) (hg : PRep n w P g) : PRep n w Q g⁻¹ := by
  rw [suzPrep_eq hg (suzPrep_permOK h).1]
  exact (suzPrep_permOK h).2

theorem suzNotK_eq (b : Bool) : notK b = !b := by
  cases b <;> rfl

theorem suzInT_spec {cnt : Nat} {T : Nat → Nat} {x : Nat} (h : inT cnt T x = true) :
    ∃ q < cnt, T q = x := by
  unfold inT at h
  rw [suzNotK_eq, Bool.not_eq_true'] at h
  by_contra hc
  simp only [not_exists, not_and] at hc
  have ha : allN cnt (fun q => notK (Nat.beq (T q) x)) = true := allN_iff.2 fun q hq => by
    rw [suzNotK_eq, Bool.not_eq_true']
    cases hb : Nat.beq (T q) x
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) (hc q hq)
  rw [ha] at h
  exact Bool.noConfusion h

theorem suzWptK_eq {k : Nat} {G : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)}
    (hG : ∀ j < k, PRep n w (G j) (g j)) :
    ∀ wd : List Nat, (∀ j ∈ wd, j < k) → ∀ x : Fin n, wptK w G wd x = ((wd.map g).prod x : Nat)
  | [], _, x => by
    have e : wptK w G [] x = x := rfl
    rw [e]
    simp
  | j :: wd, hj, x => by
    have e : wptK w G (j :: wd) x = pg w (mask w) (G j) (wptK w G wd x) := rfl
    rw [e, suzWptK_eq hG wd (fun i hi => hj i (List.mem_cons_of_mem _ hi)) x, List.map_cons,
      List.prod_cons, Equiv.Perm.mul_apply]
    exact hG j (hj j (by simp)) _

theorem suzMemL_mem (q : Nat) : ∀ F : List Nat, memL q F = true → q ∈ F
  | [], h => Bool.noConfusion h
  | y :: F, h => by
    have e : memL q (y :: F) = bIf(Nat.beq q y, true, memL q F) := rfl
    rw [e] at h
    cases hb : Nat.beq q y
    · rw [hb] at h
      exact List.mem_cons_of_mem _ (suzMemL_mem q F h)
    · rw [Nat.eq_of_beq_eq_true hb]
      simp

theorem suzFixAll {w b : Nat} {G : Nat → Nat} : ∀ W : List (List Nat),
    List.rec (motive := fun _ => Bool) true
      (fun wd _ ih => bAnd(Nat.beq (wptK w G wd b) b, ih)) W = true →
    ∀ wd ∈ W, wptK w G wd b = b
  | [], _, _, hv => absurd hv (List.not_mem_nil)
  | v :: W, h, wd, hv => by
    have e : List.rec (motive := fun _ => Bool) true
        (fun wd _ ih => bAnd(Nat.beq (wptK w G wd b) b, ih)) (v :: W) =
        bAnd(Nat.beq (wptK w G v b) b, List.rec (motive := fun _ => Bool) true
          (fun wd _ ih => bAnd(Nat.beq (wptK w G wd b) b, ih)) W) := rfl
    rw [e, bAnd_iff] at h
    rcases List.mem_cons.1 hv with rfl | hv
    · exact Nat.eq_of_beq_eq_true h.1
    · exact suzFixAll W h.2 wd hv

theorem suzMoveNone {w q : Nat} {G : Nat → Nat} : ∀ W : List (List Nat),
    (∀ wd ∈ W, wptK w G wd q = q) →
    List.rec (motive := fun _ => Bool) false
      (fun wd _ ih => bIf(Nat.beq (wptK w G wd q) q, ih, true)) W = false
  | [], _ => rfl
  | v :: W, h => by
    have e : List.rec (motive := fun _ => Bool) false
        (fun wd _ ih => bIf(Nat.beq (wptK w G wd q) q, ih, true)) (v :: W) =
        bIf(Nat.beq (wptK w G v q) q, List.rec (motive := fun _ => Bool) false
          (fun wd _ ih => bIf(Nat.beq (wptK w G wd q) q, ih, true)) W, true) := rfl
    rw [e, h v (by simp), Nat.beq_refl]
    exact suzMoveNone W (fun u hu => h u (List.mem_cons_of_mem _ hu))

theorem chainK_parts {LR TR : Nat → Nat} (h : chainK n w LR TR = true) :
    (∀ i < 3, trK n (n * w) LR TR i 0 = pidn n w) ∧
    (∀ a < rcnt (LR 0), rpos w (mask w) (n * w) (LR 0)
      (pg w (mask w) (trK n (n * w) LR TR 0 a) 0) = a) ∧
    (∀ b < rcnt (LR 1), pg w (mask w) (trK n (n * w) LR TR 1 b) 0 = 0 ∧
      rpos w (mask w) (n * w) (LR 1) (pg w (mask w) (trK n (n * w) LR TR 1 b) 1) = b) ∧
    (∀ c < rcnt (LR 2), pg w (mask w) (trK n (n * w) LR TR 2 c) 0 = 0 ∧
      pg w (mask w) (trK n (n * w) LR TR 2 c) 1 = 1 ∧
      rpos w (mask w) (n * w) (LR 2) (pg w (mask w) (trK n (n * w) LR TR 2 c) 2) = c) := by
  unfold chainK at h
  rw [strictB_app'] at h
  obtain ⟨h0, h1, h2, h3⟩ := (by simpa only [bAnd_iff] using h :
    allN 3 (fun i => Nat.beq (trK n (Nat.mul n w) LR TR i 0) (pidn n w)) = true ∧
    allN (rcnt (LR 0)) (fun a => Nat.beq (rpos w (mask w) (Nat.mul n w) (LR 0)
      (pg w (mask w) (trK n (Nat.mul n w) LR TR 0 a) 0)) a) = true ∧
    allN (rcnt (LR 1)) (fun b => strictB (trK n (Nat.mul n w) LR TR 1 b) (fun B =>
      bAnd(Nat.beq (pg w (mask w) B 0) 0,
        Nat.beq (rpos w (mask w) (Nat.mul n w) (LR 1) (pg w (mask w) B 1)) b))) = true ∧
    allN (rcnt (LR 2)) (fun c => strictB (trK n (Nat.mul n w) LR TR 2 c) (fun C =>
      bAnd(Nat.beq (pg w (mask w) C 0) 0, bAnd(Nat.beq (pg w (mask w) C 1) 1,
        Nat.beq (rpos w (mask w) (Nat.mul n w) (LR 2) (pg w (mask w) C 2)) c)))) = true)
  refine ⟨fun i hi => Nat.eq_of_beq_eq_true (allN_spec h0 i hi),
    fun a ha => Nat.eq_of_beq_eq_true (allN_spec h1 a ha), fun b hb => ?_, fun c hc => ?_⟩
  · have e := allN_spec h2 b hb
    rw [strictB_app', bAnd_iff] at e
    exact ⟨Nat.eq_of_beq_eq_true e.1, Nat.eq_of_beq_eq_true e.2⟩
  · have e := allN_spec h3 c hc
    rw [strictB_app', bAnd_iff, bAnd_iff] at e
    exact ⟨Nat.eq_of_beq_eq_true e.1, Nat.eq_of_beq_eq_true e.2.1, Nat.eq_of_beq_eq_true e.2.2⟩

theorem fixOK_sound {k : Nat} {G : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)}
    {W : List (List Nat)} {b : Nat} {F : List Nat} (h : fixOK n w G W b F = true)
    (hW : ∀ wd ∈ W, ∀ j ∈ wd, j < k) (hG : ∀ j < k, PRep n w (G j) (g j))
    {τ : Equiv.Perm (Fin n)} (hτ : ∀ j < k, τ * g j = g j * τ) (hb : b < n) :
    ((τ ⟨b, hb⟩ : Fin n) : Nat) ∈ F := by
  unfold fixOK at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hu : ∀ wd ∈ W, wptK w G wd (τ ⟨b, hb⟩ : Nat) = (τ ⟨b, hb⟩ : Nat) := fun wd hwd => by
    have hb' := suzFixAll W h1 wd hwd
    rw [suzWptK_eq hG wd (hW wd hwd) ⟨b, hb⟩] at hb'
    have hfix : (wd.map g).prod ⟨b, hb⟩ = ⟨b, hb⟩ := Fin.ext hb'
    rw [suzWptK_eq hG wd (hW wd hwd) (τ ⟨b, hb⟩)]
    have hc : Commute τ (wd.map g).prod := Commute.list_prod_right _ _ (fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact hτ j (hW wd hwd j hj))
    have e := congrArg (fun f : Equiv.Perm (Fin n) => f ⟨b, hb⟩) hc.eq
    simp only [Equiv.Perm.mul_apply, hfix] at e
    rw [← e]
  by_contra hF
  have e := allN_spec h2 _ (τ ⟨b, hb⟩).2
  have hm : memL (τ ⟨b, hb⟩ : Nat) F = false := by
    cases hmm : memL (τ ⟨b, hb⟩ : Nat) F
    · rfl
    · exact absurd (suzMemL_mem _ _ hmm) hF
  rw [hm] at e
  exact Bool.noConfusion (e.symm.trans (suzMoveNone W hu))

theorem suzRecMem {body : Nat → Bool → Bool} : ∀ L : List Nat,
    List.rec (motive := fun _ => Bool) true (fun p _ ih => body p ih) L = true →
    (∀ p r, body p r = true → r = true) → ∀ p ∈ L, body p true = true
  | [], _, _, _, hp => absurd hp List.not_mem_nil
  | v :: L, h, hb, p, hp => by
    have e : List.rec (motive := fun _ => Bool) true (fun p _ ih => body p ih) (v :: L) =
        body v (List.rec (motive := fun _ => Bool) true (fun p _ ih => body p ih) L) := rfl
    rw [e] at h
    have hr := hb _ _ h
    rcases List.mem_cons.1 hp with rfl | hp
    · rwa [hr] at h
    · exact suzRecMem L hr hb p hp

theorem centK_sound {LR TR TRI G : Nat → Nat} {k : Nat} {g : Nat → Equiv.Perm (Fin n)}
    {SV F1 F2 : List Nat} {lo len : Nat} (h3 : 3 ≤ n) (T : Nat → Nat → Equiv.Perm (Fin n))
    (hT : ∀ i < 3, ∀ a < rcnt (LR i), PRep n w (trK n (n * w) LR TR i a) (T i a) ∧
      PRep n w (triK n (n * w) LR TRI i a) (T i a)⁻¹)
    (hch : chainK n w LR TR = true) (h : centK n w LR TR TRI G k SV F1 F2 lo len = true)
    (hG : ∀ j < k, PRep n w (G j) (g j)) {a b c : Nat} (ha : a < rcnt (LR 0))
    (hb : b < rcnt (LR 1)) (hc : c < rcnt (LR 2)) (hlo : lo ≤ a) (hlen : a < lo + len)
    (hτ : ∀ j < k, T 0 a * T 1 b * T 2 c * g j = g j * (T 0 a * T 1 b * T 2 c))
    (h1 : (((T 0 a * T 1 b * T 2 c) ⟨1, by omega⟩ : Fin n) : Nat) ∈ F1)
    (h2 : (((T 0 a * T 1 b * T 2 c) ⟨2, by omega⟩ : Fin n) : Nat) ∈ F2) :
    code3 ((T 0 a * T 1 b * T 2 c) ⟨0, by omega⟩) ((T 0 a * T 1 b * T 2 c) ⟨1, by omega⟩)
      ((T 0 a * T 1 b * T 2 c) ⟨2, by omega⟩) ∈ SV := by
  have h0 : 0 < n := by omega
  obtain ⟨_, _, hc1, hc2⟩ := chainK_parts hch
  obtain ⟨hb0, hb1⟩ := hc1 b hb
  obtain ⟨hc0, hc1', hc2'⟩ := hc2 c hc
  obtain ⟨hA, hAI⟩ := hT 0 (by omega) a ha
  obtain ⟨hB, hBI⟩ := hT 1 (by omega) b hb
  have hC := (hT 2 (by omega) c hc).1
  have eB0 : T 1 b ⟨0, h0⟩ = ⟨0, h0⟩ := Fin.ext ((hB ⟨0, h0⟩).symm.trans hb0)
  have eC0 : T 2 c ⟨0, h0⟩ = ⟨0, h0⟩ := Fin.ext ((hC ⟨0, h0⟩).symm.trans hc0)
  have eC1 : T 2 c ⟨1, by omega⟩ = ⟨1, by omega⟩ := Fin.ext ((hC ⟨1, by omega⟩).symm.trans hc1')
  set τ := T 0 a * T 1 b * T 2 c with hτd
  have eτ0 : τ ⟨0, h0⟩ = T 0 a ⟨0, h0⟩ := by
    rw [hτd, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, eC0, eB0]
  have ex1 : pg w (mask w) (triK n (n * w) LR TRI 0 a) (τ ⟨1, by omega⟩ : Nat) =
      (T 1 b ⟨1, by omega⟩ : Nat) := by
    rw [hAI (τ ⟨1, by omega⟩), hτd, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, eC1]
    simp
  have hrb : rpos w (mask w) (n * w) (LR 1) (T 1 b ⟨1, by omega⟩ : Nat) = b := by
    rw [← hB ⟨1, by omega⟩]
    exact hb1
  have ex2 : pg w (mask w) (triK n (n * w) LR TRI 0 a) (τ ⟨2, by omega⟩ : Nat) =
      (T 1 b (T 2 c ⟨2, by omega⟩) : Nat) := by
    rw [hAI (τ ⟨2, by omega⟩), hτd, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    simp
  have ey : pg w (mask w) (triK n (n * w) LR TRI 1 b) (T 1 b (T 2 c ⟨2, by omega⟩) : Nat) =
      (T 2 c ⟨2, by omega⟩ : Nat) := by
    rw [hBI (T 1 b (T 2 c ⟨2, by omega⟩))]
    simp
  have hrc : rpos w (mask w) (n * w) (LR 2) (T 2 c ⟨2, by omega⟩ : Nat) = c := by
    rw [← hC ⟨2, by omega⟩]
    exact hc2'
  unfold centK at h
  simp only [strictB_app', Nat.mul_eq, Nat.add_eq] at h
  have hd := allN_spec h (a - lo) (by omega)
  have hla : lo + (a - lo) = a := by omega
  rw [hla, Nat.blt_eq.mpr ha] at hd
  have hc1K : cent1 n w LR TR TRI G k SV F1 F2 (trK n (n * w) LR TR 0 a)
      (triK n (n * w) LR TRI 0 a) = true := hd
  unfold cent1 at hc1K
  simp only [strictB_app', Nat.mul_eq] at hc1K
  have k1 := suzRecMem F1 hc1K (fun p r hr => by
    simp only [bAnd_iff] at hr
    exact hr.2.2) _ h1
  simp only [bAnd_iff] at k1
  have k1' := k1.2.1
  rw [ex1, hrb, Nat.blt_eq.mpr hb] at k1'
  have hc2K : cent2 n w LR TR TRI G k SV F2 (trK n (n * w) LR TR 0 a)
      (triK n (n * w) LR TRI 0 a) (trK n (n * w) LR TR 1 b) (triK n (n * w) LR TRI 1 b)
      (pg w (mask w) (trK n (n * w) LR TR 0 a) 0) (τ ⟨1, by omega⟩ : Nat) = true := k1'
  unfold cent2 at hc2K
  simp only [strictB_app', Nat.mul_eq] at hc2K
  have k2 := suzRecMem F2 hc2K (fun p r hr => by
    simp only [bAnd_iff] at hr
    exact hr.2.2.2) _ h2
  simp only [bAnd_iff] at k2
  have k2' := k2.2.2.1
  rw [ex2, ey, hrc, Nat.blt_eq.mpr hc] at k2'
  have hp0 : pg w (mask w) (trK n (n * w) LR TR 0 a) 0 = (τ ⟨0, h0⟩ : Nat) := by
    rw [eτ0]
    exact hA ⟨0, h0⟩
  cases hm : memL (code3 (pg w (mask w) (trK n (n * w) LR TR 0 a) 0) (τ ⟨1, by omega⟩ : Nat)
      (τ ⟨2, by omega⟩ : Nat)) SV
  ·
    rw [hm] at k2'
    have hrej : rejK w G k (trK n (n * w) LR TR 0 a) (trK n (n * w) LR TR 1 b)
        (trK n (n * w) LR TR 2 c) = true := k2'
    unfold rejK at hrej
    rw [suzNotK_eq, Bool.not_eq_true'] at hrej
    have hpt : ∀ x : Fin n, pt3 w (trK n (n * w) LR TR 0 a) (trK n (n * w) LR TR 1 b)
        (trK n (n * w) LR TR 2 c) x = (τ x : Nat) := fun x => by
      unfold pt3
      rw [hC x, hB, hA, hτd, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have hall : allN k (fun j => strictB (G j) (fun g => Nat.beq (pt3 w (trK n (n * w) LR TR 0 a)
        (trK n (n * w) LR TR 1 b) (trK n (n * w) LR TR 2 c) (pg w (mask w) g 0))
        (pg w (mask w) g (pt3 w (trK n (n * w) LR TR 0 a) (trK n (n * w) LR TR 1 b)
          (trK n (n * w) LR TR 2 c) 0)))) = true := allN_iff.2 fun j hj => by
      rw [strictB_app']
      have eg : pg w (mask w) (G j) 0 = (g j ⟨0, h0⟩ : Nat) := hG j hj ⟨0, h0⟩
      have et : pt3 w (trK n (n * w) LR TR 0 a) (trK n (n * w) LR TR 1 b)
          (trK n (n * w) LR TR 2 c) 0 = (τ ⟨0, h0⟩ : Nat) := hpt ⟨0, h0⟩
      rw [eg, et, hpt, hG j hj]
      have ec := congrArg (fun f : Equiv.Perm (Fin n) => f ⟨0, h0⟩) (hτ j hj)
      simp only [Equiv.Perm.mul_apply] at ec
      rw [ec, Nat.beq_refl]
    rw [hall] at hrej
    exact Bool.noConfusion hrej
  · have hmem := suzMemL_mem _ _ hm
    rwa [hp0] at hmem

theorem suzNget_eq : ∀ (L : List Nat) (i : Nat), CFSG.KS.Mathieu.nget L i = L.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => suzNget_eq L i

theorem suzLenL_eq : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (suzLenL_eq L)

theorem suzMkL (f : Nat → Nat) : ∀ (L : List Nat) (k : List Nat → Bool), mkL f L k = k (L.map f)
  | [], _ => rfl
  | v :: L, k => by
    have e : mkL f (v :: L) k = strictB (f v) (fun s => mkL f L (fun R => k (s :: R))) := rfl
    rw [e, strictB_app']
    exact suzMkL f L (fun R => k (f v :: R))

theorem suzEvW_cons {w P : Nat} {Ws : List Nat} {g h : Equiv.Perm (Fin n)} (hP : PRep n w P g)
    (hW : ∀ x : Fin n, evW w Ws x = (h x : Nat)) :
    ∀ x : Fin n, evW w (P :: Ws) x = ((g * h) x : Nat) := fun x => by
  have e : evW w (P :: Ws) x = pg w (mask w) P (evW w Ws x) := rfl
  rw [e, hW x, hP (h x), Equiv.Perm.mul_apply]

theorem suzEvW_nil (w : Nat) : ∀ x : Fin n, evW w [] x = ((1 : Equiv.Perm (Fin n)) x : Nat) :=
  fun _ => rfl

theorem suzFixB_iff (h3 : 3 ≤ n) {w : Nat} {Ws : List Nat} {g : Equiv.Perm (Fin n)}
    (hW : ∀ x : Fin n, evW w Ws x = (g x : Nat)) : fixB w Ws = true ↔ Fix3 h3 g := by
  have e0 : evW w Ws 0 = (g ⟨0, by omega⟩ : Nat) := hW ⟨0, by omega⟩
  have e1 : evW w Ws 1 = (g ⟨1, by omega⟩ : Nat) := hW ⟨1, by omega⟩
  have e2 : evW w Ws 2 = (g ⟨2, by omega⟩ : Nat) := hW ⟨2, by omega⟩
  unfold fixB Fix3
  rw [bAnd_iff, bAnd_iff, e0, e1, e2, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq]
  constructor
  · rintro ⟨f0, f1, f2⟩ i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact f0
    · exact f1
    · exact f2
  · intro hf
    exact ⟨hf 0 (by omega), hf 1 (by omega), hf 2 (by omega)⟩

theorem suzSqCnt_eq (w : Nat) : ∀ L : List Nat, sqCnt w L = (L.filter (sqB w)).length
  | [] => rfl
  | s :: L => by
    have e : sqCnt w (s :: L) = nIf(sqB w s, Nat.succ (sqCnt w L), sqCnt w L) := rfl
    rw [e, List.filter_cons, suzSqCnt_eq w L]
    cases sqB w s
    · rfl
    · rfl

theorem survK_sound {msift : Nat → Bool} {LR TR TRI : Nat → Nat} {T1 : Nat} {SV : List Nat}
    {r : Nat} (hn : n < 16777216) (h3 : 3 ≤ n) {M : Subgroup (Equiv.Perm (Fin n))}
    (hM : ∀ P g, canonK n w (mask w) (n * w) P = true → PRep n w P g → msift P = true → g ∈ M)
    {t1 : Equiv.Perm (Fin n)} (hT1 : PRep n w T1 t1)
    (h : survK n w msift LR TR TRI T1 SV r = true) :
    ∃ S : Set (Equiv.Perm (Fin n)),
      (∀ v ∈ SV, ∃ s ∈ S, code3 (s ⟨0, by omega⟩) (s ⟨1, by omega⟩) (s ⟨2, by omega⟩) = v) ∧
      (∀ s ∈ S, s ∈ M ∧ s * t1 = t1 * s ∧ (Fix3 h3 (s * s) ∨ Fix3 h3 (s * s * s))) ∧
      (∀ s ∈ S, ∀ t ∈ S, Fix3 h3 (⁅s, t⁆ * ⁅s, t⁆)) ∧
      (∀ s ∈ S, ∀ t ∈ S, Fix3 h3 (s * s) → Fix3 h3 (t * t) → Fix3 h3 (s⁻¹ * t⁻¹ * s * t)) ∧
      {s | s ∈ S ∧ Fix3 h3 (s * s)}.ncard ≤ 4 := by
  have h32 : n < 2 ^ 32 := by omega
  unfold survK at h
  rw [bAnd_iff] at h
  obtain ⟨hlen, h⟩ := h
  rw [suzLenL_eq] at hlen
  have hlen' : SV.length = r := Nat.eq_of_beq_eq_true hlen
  simp only [suzMkL] at h
  generalize hLS : SV.map (fun v => prodOf n w LR TR (posOf n w LR TRI v)) = LS at h
  have hLSl : LS.length = r := by rw [← hLS, List.length_map, hlen']
  generalize LS.map (fun s => pinvS n w (mask w) s) = LI at h
  simp only [bAnd_iff] at h
  obtain ⟨hs1, hs2, hcnt⟩ := h
  let ρ : Nat → Equiv.Perm (Fin n) := fun P => CFSG.Monster.B.Co2.permOfArr n (unpack n w P)
  have hS1 : ∀ i < r, canonK n w (mask w) (n * w) (CFSG.KS.Mathieu.nget LS i) = true ∧
      PRep n w (CFSG.KS.Mathieu.nget LS i) (ρ (CFSG.KS.Mathieu.nget LS i)) ∧
      PRep n w (CFSG.KS.Mathieu.nget LI i) (ρ (CFSG.KS.Mathieu.nget LS i))⁻¹ ∧
      msift (CFSG.KS.Mathieu.nget LS i) = true ∧
      pcomp n w (mask w) (CFSG.KS.Mathieu.nget LS i) T1 =
        pcomp n w (mask w) T1 (CFSG.KS.Mathieu.nget LS i) ∧
      code3 (pg w (mask w) (CFSG.KS.Mathieu.nget LS i) 0)
        (pg w (mask w) (CFSG.KS.Mathieu.nget LS i) 1)
        (pg w (mask w) (CFSG.KS.Mathieu.nget LS i) 2) = CFSG.KS.Mathieu.nget SV i ∧
      bIf(sqB w (CFSG.KS.Mathieu.nget LS i), true, fixB w [CFSG.KS.Mathieu.nget LS i,
        CFSG.KS.Mathieu.nget LS i, CFSG.KS.Mathieu.nget LS i]) = true := fun i hi => by
    have e := allN_spec hs1 i hi
    unfold surv1 at e
    simp only [bAnd_iff] at e
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := e
    exact ⟨e1, (suzPrep_permOK e2).1, (suzPrep_permOK e2).2, e3, Nat.eq_of_beq_eq_true e4,
      Nat.eq_of_beq_eq_true e5, e6⟩
  refine ⟨{s | ∃ i < r, PRep n w (CFSG.KS.Mathieu.nget LS i) s}, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hv
    obtain ⟨_, hP, -, -, -, hcode, -⟩ := hS1 i (by omega)
    refine ⟨_, ⟨i, by omega, hP⟩, ?_⟩
    rw [suzNget_eq SV i, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] at hcode
    rw [← hcode, hP ⟨0, by omega⟩, hP ⟨1, by omega⟩, hP ⟨2, by omega⟩]
  · rintro s ⟨i, hi, hs⟩
    obtain ⟨hcan, hP, -, hm, hcomm, -, hsq⟩ := hS1 i hi
    rw [suzPrep_eq hs hP]
    refine ⟨hM _ _ hcan hP hm, ?_, ?_⟩
    · have e1 := prep_pcomp h32 hP hT1
      rw [hcomm] at e1
      exact suzPrep_eq e1 (prep_pcomp h32 hT1 hP)
    · cases hb : sqB w (CFSG.KS.Mathieu.nget LS i)
      · rw [hb] at hsq
        right
        have hf := (suzFixB_iff h3 (suzEvW_cons hP (suzEvW_cons hP (suzEvW_cons hP
          (suzEvW_nil w))))).1 hsq
        rwa [mul_one, ← mul_assoc] at hf
      · left
        have hf := (suzFixB_iff h3 (suzEvW_cons hP (suzEvW_cons hP (suzEvW_nil w)))).1 hb
        rwa [mul_one] at hf
  · rintro s ⟨i, hi, hs⟩ t ⟨j, hj, ht⟩
    obtain ⟨-, hP, hPI, -⟩ := hS1 i hi
    obtain ⟨-, hQ, hQI, -⟩ := hS1 j hj
    rw [suzPrep_eq hs hP, suzPrep_eq ht hQ]
    have e := allN_spec (allN_spec hs2 i hi) j hj
    unfold surv2 at e
    rw [bAnd_iff] at e
    have hf := (suzFixB_iff h3 (suzEvW_cons hP (suzEvW_cons hQ (suzEvW_cons hPI
      (suzEvW_cons hQI (suzEvW_cons hP (suzEvW_cons hQ (suzEvW_cons hPI (suzEvW_cons hQI
        (suzEvW_nil w)))))))))).1 e.1
    refine (congrArg (Fix3 h3) ?_).mp hf
    simp only [commutatorElement_def, mul_one, mul_assoc]
  · rintro s ⟨i, hi, hs⟩ t ⟨j, hj, ht⟩ hss htt
    obtain ⟨-, hP, hPI, -⟩ := hS1 i hi
    obtain ⟨-, hQ, hQI, -⟩ := hS1 j hj
    rw [suzPrep_eq hs hP] at hss ⊢
    rw [suzPrep_eq ht hQ] at htt ⊢
    have hsP : sqB w (CFSG.KS.Mathieu.nget LS i) = true :=
      (suzFixB_iff h3 (suzEvW_cons hP (suzEvW_cons hP (suzEvW_nil w)))).2 (by rwa [mul_one])
    have hsQ : sqB w (CFSG.KS.Mathieu.nget LS j) = true :=
      (suzFixB_iff h3 (suzEvW_cons hQ (suzEvW_cons hQ (suzEvW_nil w)))).2 (by rwa [mul_one])
    have e := allN_spec (allN_spec hs2 i hi) j hj
    unfold surv2 at e
    rw [bAnd_iff] at e
    have e2 := e.2
    simp only [hsP, hsQ] at e2
    have hf := (suzFixB_iff h3 (suzEvW_cons hPI (suzEvW_cons hQI (suzEvW_cons hP
      (suzEvW_cons hQ (suzEvW_nil w)))))).1 e2
    refine (congrArg (Fix3 h3) ?_).mp hf
    simp only [mul_one, mul_assoc]
  · classical
    have hsub : {s | (∃ i < r, PRep n w (CFSG.KS.Mathieu.nget LS i) s) ∧ Fix3 h3 (s * s)} ⊆
        ↑(((LS.filter (sqB w)).map ρ).toFinset) := by
      rintro s ⟨⟨i, hi, hs⟩, hss⟩
      obtain ⟨-, hP, -⟩ := hS1 i hi
      have hsq : sqB w (CFSG.KS.Mathieu.nget LS i) = true :=
        (suzFixB_iff h3 (suzEvW_cons hP (suzEvW_cons hP (suzEvW_nil w)))).2
          (by rw [mul_one, ← suzPrep_eq hs hP]; exact hss)
      rw [Finset.mem_coe, List.mem_toFinset, List.mem_map]
      refine ⟨CFSG.KS.Mathieu.nget LS i, List.mem_filter.2 ⟨?_, hsq⟩, (suzPrep_eq hs hP).symm⟩
      rw [suzNget_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        Option.getD_some]
      exact List.getElem_mem _
    calc _ ≤ (↑(((LS.filter (sqB w)).map ρ).toFinset) : Set (Equiv.Perm (Fin n))).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (((LS.filter (sqB w)).map ρ).toFinset).card := Set.ncard_coe_finset _
      _ ≤ ((LS.filter (sqB w)).map ρ).length := List.toFinset_card_le _
      _ = sqCnt w LS := by rw [List.length_map, suzSqCnt_eq]
      _ ≤ 4 := Nat.le_of_ble_eq_true hcnt

theorem suzNgetL_eq : ∀ (L : List (List Nat)) (i : Nat), ngetL L i = L.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => suzNgetL_eq L i

theorem suzPrep_ppow {w P : Nat} {g : Equiv.Perm (Fin n)} (hn : n < 16777216)
    (hw : n + 1 < 2 ^ w) (hP : PRep n w P g) :
    ∀ e, PRep n w (ppow n w (mask w) (pidn n w) P e) (g ^ e)
  | 0 => by
    rw [pow_zero]
    exact prep_pidn hn hw
  | e + 1 => by
    have he : ppow n w (mask w) (pidn n w) P (e + 1) =
        pcomp n w (mask w) P (ppow n w (mask w) (pidn n w) P e) := by
      change strictN _ _ = _
      rw [strictN_app']
      rfl
    rw [he, pow_succ']
    exact prep_pcomp (by omega) hP (suzPrep_ppow hn hw hP e)

theorem suzPrep_letK {Gi GiI : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (hG : ∀ j < 7, PRep n w (Gi j) (g j)) (hGI : ∀ j < 7, PRep n w (GiI j) (g j)⁻¹) {c : Nat}
    (hc : c < 10) : PRep n w (letK n w Gi GiI c) (letP g c) := by
  unfold letK letP
  by_cases h5 : c < 5
  · have hb : Nat.blt c 5 = true := Nat.blt_eq.mpr h5
    rw [hb, if_pos h5, commutatorElement_def]
    exact prep_pcomp hn (prep_pcomp hn (prep_pcomp hn (hG 1 (by omega)) (hG (c + 2) (by omega)))
      (hGI 1 (by omega))) (hGI (c + 2) (by omega))
  · have hb : Nat.blt c 5 = false := by
      cases hh : Nat.blt c 5
      · rfl
      · exact absurd (Nat.blt_eq.mp hh) h5
    rw [hb, if_neg h5, commutatorElement_inv, commutatorElement_def]
    exact prep_pcomp hn (prep_pcomp hn (prep_pcomp hn (hG (c - 5 + 2) (by omega)) (hG 1 (by omega)))
      (hGI (c - 5 + 2) (by omega))) (hGI 1 (by omega))

theorem suzPrep_wordK {Gi GiI : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)} (hn : n < 16777216)
    (hw : n + 1 < 2 ^ w) (hG : ∀ j < 7, PRep n w (Gi j) (g j))
    (hGI : ∀ j < 7, PRep n w (GiI j) (g j)⁻¹) :
    ∀ L : List Nat, (∀ c ∈ L, c < 10) → PRep n w (wordK n w Gi GiI L) (wordP g L)
  | [], _ => by
    unfold wordP
    rw [List.map_nil, List.prod_nil]
    exact prep_pidn hn hw
  | c :: L, hL => by
    have e : wordK n w Gi GiI (c :: L) =
        pcomp n w (mask w) (letK n w Gi GiI c) (wordK n w Gi GiI L) := by
      change strictN _ _ = _
      rw [strictN_app']
      rfl
    rw [e]
    unfold wordP
    rw [List.map_cons, List.prod_cons]
    exact prep_pcomp (by omega) (suzPrep_letK (by omega) hG hGI (hL c (by simp)))
      (suzPrep_wordK hn hw hG hGI L (fun x hx => hL x (List.mem_cons_of_mem _ hx)))

theorem wordsK_sound {Gi GiI OW : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)}
    (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (h : wordsK n w Gi GiI OW = true)
    (hG : ∀ j < 7, PRep n w (Gi j) (g j)) :
    (∀ k < 9, canonK n w (mask w) (n * w) (OW k) = true ∧
      PRep n w (OW k) (wordP g (oddCodes.getD k [])) ∧
      wordP g (oddCodes.getD k []) ^ oddExps.getD k 0 = 1) ∧
    PRep n w (OW 9) (wordP g zCode) := by
  have h32 : n < 2 ^ 32 := by omega
  unfold wordsK at h
  simp only [bAnd_iff] at h
  obtain ⟨hgen, hodd, hz⟩ := h
  have hGI : ∀ j < 7, PRep n w (GiI j) (g j)⁻¹ := fun j hj => by
    have e := allN_spec hgen j hj
    rw [bAnd_iff] at e
    exact suzPrep_inv e.2 (hG j hj)
  have hc : ∀ k < 9, ∀ c ∈ oddCodes.getD k [], c < 10 := by decide
  have hzc : ∀ c ∈ zCode, c < 10 := by decide
  refine ⟨fun k hk => ?_, ?_⟩
  · have e := allN_spec hodd k hk
    rw [strictB_app', bAnd_iff, bAnd_iff] at e
    obtain ⟨e1, e2, e3⟩ := e
    rw [suzNgetL_eq] at e2
    have hP : PRep n w (OW k) (wordP g (oddCodes.getD k [])) := by
      rw [Nat.eq_of_beq_eq_true e2]
      exact suzPrep_wordK hn hw hG hGI _ (hc k hk)
    refine ⟨e1, hP, ?_⟩
    have hpow := suzPrep_ppow hn hw hP (CFSG.KS.Mathieu.nget oddExps k)
    rw [Nat.eq_of_beq_eq_true e3, suzNget_eq] at hpow
    exact (suzPrep_eq hpow (prep_pidn hn hw))
  · rw [Nat.eq_of_beq_eq_true hz]
    exact suzPrep_wordK hn hw hG hGI _ hzc

theorem rK_sound {OW G T : Nat → Nat} {cnt : Nat} (hn : n < 2 ^ 32)
    (h : rK n w OW G cnt T = true) {o : Nat → Equiv.Perm (Fin n)}
    (hO : ∀ k < 9, PRep n w (OW k) (o k)) :
    (∀ j < 4, G j = pcomp n w (mask w) (OW (2 * j)) (OW (2 * j + 1))) ∧
      (∃ q < cnt, T q = OW 9) ∧
      ∀ j < 4, ∃ q < cnt, PRep n w (T q) (o 8 * (o (2 * j) * o (2 * j + 1)) * (o 8)⁻¹) := by
  unfold rK at h
  rw [strictB_app'] at h
  simp only [bAnd_iff] at h
  obtain ⟨hp, hG, hz, hc⟩ := h
  have hwI := suzPrep_inv hp (hO 8 (by omega))
  have hGe : ∀ j < 4, G j = pcomp n w (mask w) (OW (2 * j)) (OW (2 * j + 1)) := fun j hj =>
    Nat.eq_of_beq_eq_true (allN_spec hG j hj)
  refine ⟨hGe, suzInT_spec hz, fun j hj => ?_⟩
  obtain ⟨q, hq, e⟩ := suzInT_spec (allN_spec hc j hj)
  refine ⟨q, hq, ?_⟩
  rw [e, hGe j hj]
  exact prep_pcomp hn (prep_pcomp hn (hO 8 (by omega))
    (prep_pcomp hn (hO _ (by omega)) (hO _ (by omega)))) hwI

theorem hK_sound {msift : Nat → Bool} {HP T1 : Nat} {OW G GN : Nat → Nat} (hn : n < 2 ^ 32)
    (h : hK n w msift HP T1 OW G GN = true) {t1 z wg : Equiv.Perm (Fin n)}
    {r : Nat → Equiv.Perm (Fin n)} (hT1 : PRep n w T1 t1) (hz : PRep n w (OW 9) z)
    (hwg : PRep n w (OW 8) wg) (hr : ∀ j < 4, PRep n w (G j) (r j)) :
    ∃ hp : Equiv.Perm (Fin n), PRep n w HP hp ∧ canonK n w (mask w) (n * w) HP = true ∧
      msift HP = true ∧ hp * t1 * hp⁻¹ = z ∧
      ∀ j < 5, PRep n w (GN j) (hp⁻¹ * (if j < 4 then r j else wg) * hp) := by
  unfold hK at h
  rw [strictB_app'] at h
  simp only [bAnd_iff] at h
  obtain ⟨hc, hp, hm, hz', hG⟩ := h
  have hP := (suzPrep_permOK hp).1
  have hPI := (suzPrep_permOK hp).2
  refine ⟨_, hP, hc, hm, ?_, fun j hj => ?_⟩
  · have h1 := prep_pcomp hn (prep_pcomp hn hP hT1) hPI
    rw [Nat.eq_of_beq_eq_true hz'] at h1
    exact suzPrep_eq h1 hz
  · have e := allN_spec hG j hj
    rw [bAnd_iff] at e
    rw [Nat.eq_of_beq_eq_true e.2]
    refine prep_pcomp hn (prep_pcomp hn hPI ?_) hP
    cases hb : Nat.blt j 4
    · have hj4 : ¬ j < 4 := fun hh => by
        rw [Nat.blt_eq.mpr hh] at hb
        exact Bool.noConfusion hb
      rw [if_neg hj4]
      exact hwg
    · have hj4 : j < 4 := Nat.blt_eq.mp hb
      rw [if_pos hj4]
      exact hr j hj4

end CFSG.KS.Suz27216

end
