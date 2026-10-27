module

public import Certificates.Data.Kernel.W4Row.HS119CK
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.HS119

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KS.SporSch

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by
  cases y <;> rfl

theorem fd_eq_pg (w P x : ℕ) : fd w P x = CFSG.KC.Enum.pg w (CFSG.KS.mask w) P x := rfl

theorem fun_fd_eq_pg (w P : ℕ) :
    (fun x => fd w P x) = fun x => CFSG.KC.Enum.pg w (CFSG.KS.mask w) P x :=
  funext fun x => fd_eq_pg w P x

theorem beq_zero_false {k : ℕ} (hk : k ≠ 0) : Nat.beq k 0 = false := by
  cases h : Nat.beq k 0
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true h) hk

@[expose] def eF {G : Type*} [Group G] (PA : ℕ → ℕ) (g : ℕ → G) : ℕ → ℕ → G
  | 0, _ => 1
  | f + 1, k => if k = 0 then 1 else
      eF PA g f (Nat.land (PA k) 16777215) * g (Nat.shiftRight (PA k) 24)

theorem eF_succ {G : Type*} [Group G] (PA : ℕ → ℕ) (g : ℕ → G) (f k : ℕ) :
    eF PA g (f + 1) k = if k = 0 then 1 else
      eF PA g f (Nat.land (PA k) 16777215) * g (Nat.shiftRight (PA k) 24) := rfl

theorem treeAt_spec {M : ℕ → ℕ → ℕ} {one : ℕ} {G : ℕ → ℕ} {nG : ℕ} {E PA : ℕ → ℕ} {k : ℕ}
    (h : CFSG.KC.Misc.Clos.treeAt M one G nG E PA k = true) (hk : k ≠ 0) :
    Nat.land (PA k) 16777215 < k ∧ Nat.shiftRight (PA k) 24 < nG ∧
      E k = M (E (Nat.land (PA k) 16777215)) (G (Nat.shiftRight (PA k) 24)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  change letB (PA (k + 1)) (fun r => letB (Nat.land r 16777215) fun p =>
    letB (Nat.shiftRight r 24) fun l => andB (Nat.blt p (k + 1))
      (andB (Nat.blt l nG) (Nat.beq (E (k + 1)) (M (E p) (G l))))) = true at h
  rw [letB_eq, letB_eq, letB_eq, andB_iff, andB_iff, blt_iff, blt_iff, beq_iff] at h
  exact h

theorem treeAt_zero {M : ℕ → ℕ → ℕ} {one : ℕ} {G : ℕ → ℕ} {nG : ℕ} {E PA : ℕ → ℕ}
    (h : CFSG.KC.Misc.Clos.treeAt M one G nG E PA 0 = true) : E 0 = one :=
  Nat.eq_of_beq_eq_true h

theorem evS_succ (PA G : ℕ → ℕ) (f k x : ℕ) (hk : k ≠ 0) :
    evS PA G (f + 1) k x =
      evS PA G f (Nat.land (PA k) 16777215) (fd 12 (G (Nat.shiftRight (PA k) 24)) x) := by
  change Bool.rec (motive := fun _ => ℕ) (letN (PA k) fun r => evS PA G f (Nat.land r 16777215)
    (fd 12 (G (Nat.shiftRight r 24)) x)) x (Nat.beq k 0) = _
  rw [beq_zero_false hk, letN_eq]

theorem evSI_succ (PA GI : ℕ → ℕ) (f k x : ℕ) (hk : k ≠ 0) :
    evSI PA GI (f + 1) k x =
      fd 12 (GI (Nat.shiftRight (PA k) 24)) (evSI PA GI f (Nat.land (PA k) 16777215) x) := by
  change Bool.rec (motive := fun _ => ℕ) (letN (PA k) fun r => fd 12 (GI (Nat.shiftRight r 24))
    (evSI PA GI f (Nat.land r 16777215) x)) x (Nat.beq k 0) = _
  rw [beq_zero_false hk, letN_eq]

theorem parK_succ (PA : ℕ → ℕ) (gout f k : ℕ) (hk : k ≠ 0) :
    parK PA gout (f + 1) k = Nat.xor (parK PA gout f (Nat.land (PA k) 16777215))
      (Nat.land (Nat.shiftRight gout (Nat.shiftRight (PA k) 24)) 1) := by
  change Bool.rec (motive := fun _ => ℕ) (letN (PA k) fun r =>
    Nat.xor (parK PA gout f (Nat.land r 16777215))
      (Nat.land (Nat.shiftRight gout (Nat.shiftRight r 24)) 1)) 0 (Nat.beq k 0) = _
  rw [beq_zero_false hk, letN_eq]

theorem parK_zero (PA : ℕ → ℕ) (gout f : ℕ) : parK PA gout (f + 1) 0 = 0 := rfl

theorem parK_fuel (PA : ℕ → ℕ) (gout k : ℕ) : parK PA gout 0 k = 2 := rfl

variable {n N nG : ℕ} {PA : ℕ → ℕ}

theorem evS_rep {G : ℕ → ℕ} {g : ℕ → Equiv.Perm (Fin n)}
    (ht : ∀ k < N, k ≠ 0 → Nat.land (PA k) 16777215 < k ∧ Nat.shiftRight (PA k) 24 < nG)
    (hg : ∀ l < nG, RepF n (fun x => fd 12 (G l) x) (g l)) :
    ∀ f k, k < N → RepF n (evS PA G f k) (eF PA g f k) := by
  intro f
  induction f with
  | zero => exact fun _ _ _ _ => rfl
  | succ f ih =>
    intro k hk
    by_cases h0 : k = 0
    · subst h0
      exact fun _ _ => rfl
    · obtain ⟨hp, hl⟩ := ht k hk h0
      have h := (ih _ (lt_trans hp hk)).comp (hg _ hl)
      rw [eF_succ, if_neg h0]
      intro x hx
      rw [evS_succ PA G f k x h0]
      exact h x hx

theorem evSI_rep {GI : ℕ → ℕ} {g : ℕ → Equiv.Perm (Fin n)}
    (ht : ∀ k < N, k ≠ 0 → Nat.land (PA k) 16777215 < k ∧ Nat.shiftRight (PA k) 24 < nG)
    (hg : ∀ l < nG, RepF n (fun x => fd 12 (GI l) x) (g l)⁻¹) :
    ∀ f k, k < N → RepF n (evSI PA GI f k) (eF PA g f k)⁻¹ := by
  intro f
  induction f with
  | zero => exact fun _ _ _ _ => rfl
  | succ f ih =>
    intro k hk
    by_cases h0 : k = 0
    · subst h0
      exact fun _ _ => rfl
    · obtain ⟨hp, hl⟩ := ht k hk h0
      have h := (hg _ hl).comp (ih _ (lt_trans hp hk))
      rw [eF_succ, if_neg h0, mul_inv_rev]
      intro x hx
      rw [evSI_succ PA GI f k x h0]
      exact h x hx

theorem eF_mem {G : Type*} [Group G] {g : ℕ → G} {H : Subgroup G}
    (ht : ∀ k < N, k ≠ 0 → Nat.land (PA k) 16777215 < k ∧ Nat.shiftRight (PA k) 24 < nG)
    (hg : ∀ l < nG, g l ∈ H) : ∀ f k, k < N → eF PA g f k ∈ H := by
  intro f
  induction f with
  | zero => exact fun _ _ => H.one_mem
  | succ f ih =>
    intro k hk
    rw [eF_succ]
    split_ifs with h0
    · exact H.one_mem
    · obtain ⟨hp, hl⟩ := ht k hk h0
      exact H.mul_mem (ih _ (lt_trans hp hk)) (hg _ hl)

theorem img_lt (s i : ℕ) : img s i < 32 := by
  rw [img_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem img_mul32 {s t i : ℕ} (hi : i < 32) : img (mul 32 s t) i = img s (img t i) := by
  unfold mul
  rw [img_eq, ofFn_eq, E_digit (fun j _ => img_lt _ _) hi]

theorem img_one32 {i : ℕ} (hi : i < 32) : img (one 32) i = i := by
  unfold one
  rw [img_eq, ofFn_eq, E_digit (fun j hj => hj) hi]

theorem evS_om {G SEc Gc Om : ℕ → ℕ} (h0 : SEc 0 = one 32)
    (ht : ∀ k < N, k ≠ 0 → Nat.land (PA k) 16777215 < k ∧ Nat.shiftRight (PA k) 24 < nG ∧
      SEc k = mul 32 (SEc (Nat.land (PA k) 16777215)) (Gc (Nat.shiftRight (PA k) 24)))
    (hrho : ∀ l < nG, ∀ i < 32, fd 12 (G l) (Om i) = Om (img (Gc l) i)) :
    ∀ f k, k < N → parK PA 0 f k < 2 → ∀ i < 32, evS PA G f k (Om i) = Om (img (SEc k) i) := by
  intro f
  induction f with
  | zero => intro k _ h; exact absurd h (by rw [parK_fuel]; omega)
  | succ f ih =>
    intro k hk hd i hi
    by_cases hk0 : k = 0
    · subst hk0
      rw [h0, img_one32 hi]
      rfl
    · obtain ⟨hp, hl, he⟩ := ht k hk hk0
      have hd' : parK PA 0 f (Nat.land (PA k) 16777215) < 2 := by
        rw [parK_succ PA 0 f k hk0] at hd
        have e : Nat.land (Nat.shiftRight 0 (Nat.shiftRight (PA k) 24)) 1 = 0 := by
          change (0 >>> _) &&& 1 = 0
          rw [Nat.zero_shiftRight, Nat.zero_and]
        rw [e] at hd
        change (_ ^^^ 0) < 2 at hd
        rwa [Nat.xor_zero] at hd
      rw [evS_succ PA G f k _ hk0, hrho _ hl i hi, ih _ (lt_trans hp hk) hd' _ (img_lt _ _), he,
        img_mul32 hi]

theorem code_of_tree {SEc Gc : ℕ → ℕ} (h0 : SEc 0 = one 32)
    (ht : ∀ k < N, k ≠ 0 → Nat.land (PA k) 16777215 < k ∧ Nat.shiftRight (PA k) 24 < nG ∧
      SEc k = mul 32 (SEc (Nat.land (PA k) 16777215)) (Gc (Nat.shiftRight (PA k) 24)))
    (hG : ∀ l < nG, permK 32 (Gc l) = true) :
    ∀ k < N, ∃ σ : Equiv.Perm (Fin 32), code σ = SEc k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0
      exact ⟨1, by rw [h0, code_one]⟩
    · obtain ⟨hp, hl, he⟩ := ht k hk hk0
      obtain ⟨σ, hσ⟩ := ih _ hp (lt_trans hp hk)
      obtain ⟨τ, hτ⟩ := exists_of_permK (hG _ hl)
      exact ⟨σ * τ, by rw [he, ← hσ, ← hτ, code_mul (by norm_num)]⟩

@[expose] noncomputable def wE {G : Type*} [Group G] (lt : ℕ → G) (W : ℕ) : ℕ → G
  | 0 => 1
  | i + 1 => lt (fd 12 W (i + 1)) * wE lt W i

theorem evW_rep {Le : ℕ → ℕ → ℕ} {lt : ℕ → Equiv.Perm (Fin n)} {W : ℕ}
    (h : ∀ i < fd 12 W 0, RepF n (Le (fd 12 W (i + 1))) (lt (fd 12 W (i + 1)))) :
    RepF n (evW Le W) (wE lt W (fd 12 W 0)) := by
  have key : ∀ m ≤ fd 12 W 0, RepF n (fun x => Nat.rec (motive := fun _ => ℕ) x
      (fun i acc => Le (fd 12 W (Nat.succ i)) acc) m) (wE lt W m) := by
    intro m
    induction m with
    | zero => exact fun _ _ _ => rfl
    | succ m ih =>
      intro hm
      exact (h m hm).comp (ih (by omega))
  exact key _ le_rfl

theorem wE_mem {G : Type*} [Group G] {lt : ℕ → G} {W : ℕ} {H : Subgroup G}
    (h : ∀ i < fd 12 W 0, lt (fd 12 W (i + 1)) ∈ H) : ∀ m ≤ fd 12 W 0, wE lt W m ∈ H := by
  intro m
  induction m with
  | zero => exact fun _ => H.one_mem
  | succ m ih => exact fun hm => H.mul_mem (h m hm) (ih (by omega))

theorem wordOK_spec {p : ℕ → Bool} {W : ℕ} (h : wordOK p W = true) :
    ∀ i < fd 12 W 0, p (fd 12 W (i + 1)) = true :=
  (allN_iff _ _).1 h

theorem xor_lt_two {x b : ℕ} (hx : x < 2) (hb : b < 2) : Nat.xor x b < 2 := by
  interval_cases x <;> interval_cases b <;> decide

theorem lt_two_of_xor {x b : ℕ} (h : Nat.xor x b < 2) (hb : b < 2) : x < 2 := by
  have e : x = Nat.xor (Nat.xor x b) b := by
    change x = (x ^^^ b) ^^^ b
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [e]
  exact xor_lt_two h hb

theorem bit_lt_two (gout l : ℕ) : Nat.land (Nat.shiftRight gout l) 1 < 2 :=
  Nat.lt_succ_of_le Nat.and_le_right

theorem parK_par {gout f k : ℕ} (h : parK PA gout (f + 1) k < 2) (hk : k ≠ 0) :
    parK PA gout f (Nat.land (PA k) 16777215) < 2 := by
  rw [parK_succ PA gout f k hk] at h
  exact lt_two_of_xor h (bit_lt_two _ _)

theorem parK_lt_of_dep (gout : ℕ) : ∀ f k, parK PA 0 f k < 2 → parK PA gout f k < 2 := by
  intro f
  induction f with
  | zero => intro k h; exact absurd h (by rw [parK_fuel]; omega)
  | succ f ih =>
    intro k h
    by_cases hk : k = 0
    · subst hk
      rw [parK_zero]
      omega
    · rw [parK_succ PA gout f k hk]
      exact xor_lt_two (ih _ (parK_par h hk)) (bit_lt_two _ _)

theorem parK_mem {G : Type*} [Group G] {g : ℕ → G} {K R : Subgroup G} {gout : ℕ}
    (ht : ∀ k < N, k ≠ 0 → Nat.land (PA k) 16777215 < k ∧ Nat.shiftRight (PA k) 24 < nG)
    (hR : ∀ l < nG, g l ∈ R) (hK : ∀ x ∈ R, ∀ y ∈ R, (x * y ∈ K ↔ (x ∈ K ↔ y ∈ K)))
    (hO : ∀ l < nG, (g l ∈ K ↔ Nat.land (Nat.shiftRight gout l) 1 = 0)) :
    ∀ f k, k < N → parK PA gout f k < 2 → (eF PA g f k ∈ K ↔ parK PA gout f k = 0) := by
  intro f
  induction f with
  | zero => intro k _ h; exact absurd h (by rw [parK_fuel]; omega)
  | succ f ih =>
    intro k hk h
    by_cases hk0 : k = 0
    · subst hk0
      rw [parK_zero]
      exact ⟨fun _ => rfl, fun _ => K.one_mem⟩
    · obtain ⟨hp, hl⟩ := ht k hk hk0
      have hp2 := parK_par h hk0
      rw [eF_succ, if_neg hk0, hK _ (eF_mem ht hR f _ (lt_trans hp hk)) _ (hR _ hl),
        ih _ (lt_trans hp hk) hp2, hO _ hl, parK_succ PA gout f k hk0]
      have hb := bit_lt_two gout (Nat.shiftRight (PA k) 24)
      generalize parK PA gout f (Nat.land (PA k) 16777215) = x at hp2 ⊢
      generalize Nat.land (Nat.shiftRight gout (Nat.shiftRight (PA k) 24)) 1 = b at hb ⊢
      interval_cases x <;> interval_cases b <;> decide

theorem conjP_succ (CG : ℕ → ℕ) (f c a : ℕ) (hc : c ≠ 0) :
    conjP PA CG (f + 1) c a =
      conjP PA CG f (Nat.land (PA c) 16777215) (fd 8 (CG (Nat.shiftRight (PA c) 24)) a) := by
  change Bool.rec (motive := fun _ => ℕ) (letN (PA c) fun r => conjP PA CG f (Nat.land r 16777215)
    (fd 8 (CG (Nat.shiftRight r 24)) a)) a (Nat.beq c 0) = _
  rw [beq_zero_false hc, letN_eq]

theorem conjP_spec {G : Type*} [Group G] {g ι : ℕ → G} {CG : ℕ → ℕ}
    (ht : ∀ k < N, k ≠ 0 → Nat.land (PA k) 16777215 < k ∧ Nat.shiftRight (PA k) 24 < nG)
    (hCG : ∀ l < nG, ∀ a < 192, fd 8 (CG l) a < 192 ∧ g l * ι a * (g l)⁻¹ = ι (fd 8 (CG l) a)) :
    ∀ f c, c < N → parK PA 0 f c < 2 → ∀ a < 192,
      conjP PA CG f c a < 192 ∧ eF PA g f c * ι a * (eF PA g f c)⁻¹ = ι (conjP PA CG f c a) := by
  intro f
  induction f with
  | zero => intro c _ h; exact absurd h (by rw [parK_fuel]; omega)
  | succ f ih =>
    intro c hc h a ha
    by_cases hc0 : c = 0
    · subst hc0
      exact ⟨ha, by rw [eF_succ, if_pos rfl, one_mul, inv_one, mul_one]; rfl⟩
    · obtain ⟨hp, hl⟩ := ht c hc hc0
      obtain ⟨hb, hg⟩ := hCG _ hl a ha
      obtain ⟨h1, h2⟩ := ih _ (lt_trans hp hc) (parK_par h hc0) _ hb
      rw [conjP_succ CG f c a hc0, eF_succ, if_neg hc0]
      refine ⟨h1, ?_⟩
      rw [← h2, ← hg]
      group

@[expose] noncomputable def letE {G : Type*} [Group G] (e a : ℕ → G) (c : ℕ) : G :=
  if Nat.shiftRight c 10 = 0 then e (Nat.land c 1023)
  else if Nat.shiftRight c 10 = 1 then (e (Nat.land c 1023))⁻¹
  else if Nat.shiftRight c 10 = 2 then a (Nat.land c 1023) else (a (Nat.land c 1023))⁻¹

theorem land1023_lt (c : ℕ) : Nat.land c 1023 < 1024 :=
  Nat.lt_succ_of_le Nat.and_le_right

theorem evL_rep {G GI A AI : ℕ → ℕ} {e a : ℕ → Equiv.Perm (Fin n)}
    (he : ∀ v < 1024, RepF n (evS PA G 9 v) (e v) ∧ RepF n (evSI PA GI 9 v) (e v)⁻¹)
    (ha : ∀ j < 2, RepF n (fun x => fd 12 (A j) x) (a j) ∧ RepF n (fun x => fd 12 (AI j) x) (a j)⁻¹)
    {c : ℕ} (hc : 2 ≤ Nat.shiftRight c 10 → Nat.land c 1023 < 2) :
    RepF n (evL PA G GI A AI c) (letE e a c) := by
  intro x hx
  have hv := land1023_lt c
  unfold evL
  rw [letN_eq, letN_eq, letE]
  generalize ht : Nat.shiftRight c 10 = t at hc ⊢
  generalize Nat.land c 1023 = v at hv hc ⊢
  rcases t with _ | _ | _ | t
  · exact (he v hv).1 x hx
  · exact (he v hv).2 x hx
  · exact (ha v (hc (by omega))).1 x hx
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact (ha v (hc (by omega))).2 x hx

theorem letE_xor {G : Type*} [Group G] (e a : ℕ → G) {c : ℕ} (hc : c < 4096) :
    letE e a (Nat.xor c 1024) = (letE e a c)⁻¹ := by
  have h1 : Nat.land (Nat.xor c 1024) 1023 = Nat.land c 1023 := by
    change (c ^^^ 1024) &&& (2 ^ 10 - 1) = c &&& (2 ^ 10 - 1)
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.xor_mod_two_pow]
    norm_num
  have h2 : Nat.shiftRight c 10 < 4 := by
    change c >>> 10 < 4
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have h3 : Nat.shiftRight (Nat.xor c 1024) 10 = Nat.xor (Nat.shiftRight c 10) 1 := by
    change (c ^^^ 1024) >>> 10 = (c >>> 10) ^^^ 1
    rw [Nat.shiftRight_xor_distrib]
    rfl
  unfold letE
  rw [h1, h3]
  generalize Nat.shiftRight c 10 = t at h2 ⊢
  interval_cases t <;> simp

theorem evWI_rep {Le : ℕ → ℕ → ℕ} {lt : ℕ → Equiv.Perm (Fin n)} {W : ℕ}
    (h : ∀ i < fd 12 W 0, RepF n (Le (Nat.xor (fd 12 W (i + 1)) 1024)) (lt (fd 12 W (i + 1)))⁻¹) :
    RepF n (evWI Le W) (wE lt W (fd 12 W 0))⁻¹ := by
  have key : ∀ m ≤ fd 12 W 0, RepF n (fun x => Nat.rec (motive := fun _ => ℕ) x
      (fun i acc => Le (Nat.xor (fd 12 W (Nat.sub (fd 12 W 0) i)) 1024) acc) m)
      (wE lt W (fd 12 W 0 - m) * (wE lt W (fd 12 W 0))⁻¹) := by
    intro m
    induction m with
    | zero => intro _ x hx; rw [Nat.sub_zero, mul_inv_cancel]; rfl
    | succ m ih =>
      intro hm
      have e : Nat.sub (fd 12 W 0) m = (fd 12 W 0 - m - 1) + 1 := by
        change fd 12 W 0 - m = _
        omega
      have e2 : fd 12 W 0 - m = (fd 12 W 0 - (m + 1)) + 1 := by omega
      have hc := (h (fd 12 W 0 - m - 1) (by omega)).comp (ih (by omega))
      have e3 : (lt (fd 12 W (fd 12 W 0 - m - 1 + 1)))⁻¹ *
          (wE lt W (fd 12 W 0 - m) * (wE lt W (fd 12 W 0))⁻¹) =
          wE lt W (fd 12 W 0 - (m + 1)) * (wE lt W (fd 12 W 0))⁻¹ := by
        rw [e2, wE, ← mul_assoc, ← mul_assoc, show fd 12 W 0 - (m + 1) + 1 - 1 + 1 =
          fd 12 W 0 - (m + 1) + 1 by omega, inv_mul_cancel, one_mul]
      rw [← e3]
      intro x hx
      change Le (Nat.xor (fd 12 W (Nat.sub (fd 12 W 0) m)) 1024) _ = _
      rw [e]
      exact hc x hx
  have h0 := key _ le_rfl
  rw [Nat.sub_self, wE, one_mul] at h0
  intro x hx
  change letN (fd 12 W 0) (fun n => Nat.rec (motive := fun _ => ℕ) x
    (fun i acc => Le (Nat.xor (fd 12 W (Nat.sub n i)) 1024) acc) n) = _
  rw [letN_eq]
  exact h0 x hx

theorem bitB_iff (x i : ℕ) : bitB x i = true ↔ x.testBit i := by
  unfold bitB
  rw [beq_iff, Nat.testBit_eq_decide_div_mod_eq]
  change (x >>> i) &&& 1 = 1 ↔ _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, decide_eq_true_iff]

theorem testBit_fold2 (u v : ℕ → ℕ) (b : ℕ) : ∀ m, (Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.lor (Nat.lor acc (Nat.shiftLeft 1 (u i))) (Nat.shiftLeft 1 (v i))) m).testBit b
      = true ↔ ∃ i < m, u i = b ∨ v i = b := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    change (Nat.lor (Nat.lor (Nat.rec (motive := fun _ => ℕ) 0
      (fun i acc => Nat.lor (Nat.lor acc (Nat.shiftLeft 1 (u i))) (Nat.shiftLeft 1 (v i))) m)
        (Nat.shiftLeft 1 (u m))) (Nat.shiftLeft 1 (v m))).testBit b = true ↔ _
    rw [lor_eq, lor_eq, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true, ih,
      Nat.testBit_two_pow, Nat.testBit_two_pow, decide_eq_true_iff, decide_eq_true_iff]
    constructor
    · rintro ((⟨i, hi, h⟩ | h) | h)
      exacts [⟨i, by omega, h⟩, ⟨m, by omega, Or.inl h⟩, ⟨m, by omega, Or.inr h⟩]
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      exacts [Or.inl (Or.inl ⟨i, hi, h⟩), h.elim (fun h => Or.inl (Or.inr h)) Or.inr]

theorem lMask_testBit (L b : ℕ) :
    (lMask L).testBit b = true ↔ ∃ i < fd 8 L 0, fd 8 L (i + 1) = b :=
  testBit_fold (fun i => fd 8 L (i + 1)) b _

theorem cMask_testBit (CG PT IX : ℕ → ℕ) (c t L b : ℕ) :
    (cMask PA CG PT IX c t L).testBit b = true ↔ ∃ i < fd 8 L 0,
      conjP PA CG 9 c (fd 8 L (i + 1)) = b ∨ conjP PA CG 9 c (pxK PT IX t (fd 8 L (i + 1))) = b := by
  have e : cMask PA CG PT IX c t L = Nat.rec (motive := fun _ => ℕ) 0
      (fun i acc => Nat.lor (Nat.lor acc (Nat.shiftLeft 1 (conjP PA CG 9 c (fd 8 L (i + 1)))))
        (Nat.shiftLeft 1 (conjP PA CG 9 c (pxK PT IX t (fd 8 L (i + 1)))))) (fd 8 L 0) := by
    unfold cMask
    congr 1
    funext i acc
    rw [letN_eq]
  rw [e]
  exact testBit_fold2 _ _ b _

theorem eq5_spec {b5 : ℕ} {f g : ℕ → ℕ} (h : eq5 b5 f g = true) :
    f 0 = g 0 ∧ f 1 = g 1 ∧ f 2 = g 2 ∧ f 3 = g 3 ∧ f b5 = g b5 := by
  have h' := (allN_iff _ _).1 h
  have hq : ∀ q < 5, f (bp b5 q) = g (bp b5 q) := fun q hq => by
    have := h' q hq
    rw [letB_eq, beq_iff] at this
    exact this
  exact ⟨hq 0 (by norm_num), hq 1 (by norm_num), hq 2 (by norm_num), hq 3 (by norm_num),
    hq 4 (by norm_num)⟩

end CFSG.KC.HS119

end
