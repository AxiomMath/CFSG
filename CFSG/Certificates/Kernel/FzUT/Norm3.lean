module

public import Certificates.Data.Kernel.FzUT.Norm3
public import CFSG.Certificates.Kernel.FzUT.Codes
public import CFSG.Certificates.Kernel.FzUT.Transport

public section

namespace CFSG.KC.FzUT

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open CFSG.OddStandard.SmallF3.FritzII

theorem band_iff (a b : Bool) : band a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [band]

theorem bimp_iff (c a : Bool) : bimp c a = true ↔ (c = true → a = true) := by
  cases c <;> simp [bimp]

theorem bnot_iff (a : Bool) : bnot a = true ↔ a = false := by
  cases a <;> simp [bnot]

theorem beq_iff (a b : Nat) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem allN_iff (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    change band (f n) (allN n f) = true ↔ _
    rw [band_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem anyN_iff (n : Nat) (f : Nat → Bool) : anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [anyN]
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) (anyN n f) true (f n) = true ↔ _
    cases h : f n
    · change anyN n f = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨i, hi, h'⟩
        exact ⟨i, Nat.lt_succ_of_lt hi, h'⟩
      · rintro ⟨i, hi, h'⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, h'⟩
        · rw [h] at h'
          exact absurd h' (by simp)
    · exact ⟨fun _ => ⟨n, Nat.lt_succ_self n, h⟩, fun _ => rfl⟩

theorem sb_eq (y : Nat) (k : Nat → Bool) : sb y k = k y := by
  cases y <;> rfl

theorem fldN_eq (P w i : Nat) : fldN P w (2 ^ w - 1) i = P / 2 ^ (w * i) % 2 ^ w := by
  change (P >>> (w * i)) &&& (2 ^ w - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem fldN_lt (P w i : Nat) : fldN P w (2 ^ w - 1) i < 2 ^ w := by
  rw [fldN_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem c4_eq (d i : Nat) : c4 d i = d / 2 ^ (6 * i) % 64 := fldN_eq d 6 i

theorem c4_lt (d i : Nat) : c4 d i < 64 := fldN_lt d 6 i

theorem c4_pk4 {a b c d : Nat} (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : d < 64) :
    c4 (pk4 a b c d) 0 = a ∧ c4 (pk4 a b c d) 1 = b ∧ c4 (pk4 a b c d) 2 = c ∧
      c4 (pk4 a b c d) 3 = d := by
  simp only [c4_eq, pk4]
  norm_num
  omega

theorem pk4_c4 {m : Nat} (hm : m < 16777216) : pk4 (c4 m 0) (c4 m 1) (c4 m 2) (c4 m 3) = m := by
  simp only [c4_eq, pk4]
  norm_num
  omega

theorem fld24_lt (P i : Nat) : fldN P 24 16777215 i < 16777216 := fldN_lt P 24 i

theorem evD_pk4 {a b c d : Nat} (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : d < 64)
    (x : Nat) : evD (pk4 a b c d) x = evN a b c d x := by
  obtain ⟨h0, h1, h2, h3⟩ := c4_pk4 ha hb hc hd
  rw [evD, h0, h1, h2, h3]

@[expose] noncomputable def gc (σ : MulAut FzUT) : Nat :=
  pk4 (enc (σ fzE1)) (enc (σ fzEW)) (enc (σ fzF1)) (enc (σ fzFW))

@[expose] def genE (k : Nat) : FzUT :=
  if k = 0 then fzE1 else if k = 1 then fzEW else if k = 2 then fzF1 else fzFW

theorem enc_genE {k : Nat} (hk : k < 4) : enc (genE k) = Nat.shiftLeft 1 k := by
  interval_cases k <;> decide +kernel

theorem c4_gc (σ : MulAut FzUT) {k : Nat} (hk : k < 4) : c4 (gc σ) k = enc (σ (genE k)) := by
  obtain ⟨h0, h1, h2, h3⟩ := c4_pk4 (enc_lt (σ fzE1)) (enc_lt (σ fzEW)) (enc_lt (σ fzF1))
    (enc_lt (σ fzFW))
  interval_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem evD_gc (σ : MulAut FzUT) (x : FzUT) : evD (gc σ) (enc x) = enc (σ x) := by
  rw [gc, evD_pk4 (enc_lt _) (enc_lt _) (enc_lt _) (enc_lt _)]
  exact (hom_evN σ.toMonoidHom x).symm

theorem enc_dec' {n : Nat} (hn : n < 64) : enc (dec n) = n := enc_dec ⟨n, hn⟩

theorem gc_lt (σ : MulAut FzUT) : gc σ < 16777216 := by
  have := enc_lt (σ fzE1)
  have := enc_lt (σ fzEW)
  have := enc_lt (σ fzF1)
  have := enc_lt (σ fzFW)
  unfold gc pk4
  omega

theorem eq_of_gc {σ τ : MulAut FzUT} (h : gc σ = gc τ) (x : FzUT) : σ x = τ x := by
  apply enc_injective
  rw [← evD_gc, ← evD_gc, h]

theorem gc_one : gc (1 : MulAut FzUT) = pk4 1 2 4 8 := by
  unfold gc
  decide +kernel

theorem enc_mul (x y : FzUT) : enc (x * y) = pmulP (enc x) (enc y) := (pmulP_eq x y).symm

theorem invP_eq : ∀ x : FzUT, invP (enc x) = enc x⁻¹ := by decide +kernel

theorem rho_gens : enc (fzRho0 fzE1) = 3 ∧ enc (fzRho0 fzEW) = 1 ∧ enc (fzRho0 fzF1) = 12 ∧
    enc (fzRho0 fzFW) = 4 := by
  decide +kernel

theorem r0P_eq (x : FzUT) : r0P (enc x) = enc (fzRho0 x) := by
  obtain ⟨h1, h2, h3, h4⟩ := rho_gens
  have := hom_evN fzRho0.toMonoidHom x
  simp only [MulEquiv.coe_toMonoidHom] at this
  rw [this, h1, h2, h3, h4]
  rfl

theorem e1_rho : fzE1 = fzRho0 fzEW := by decide +kernel

theorem f1_rho : fzF1 = fzRho0 fzFW := by decide +kernel

theorem enc_ew : enc fzEW = 2 := by decide +kernel

theorem enc_fw : enc fzFW = 8 := by decide +kernel

theorem f4_add_self (a : F4c) : a + a = 0 := kcF4_add_self a

@[expose] def tauA : MulAut FzUT where
  toFun x := ⟨x.b, x.a, x.c + x.a * x.b⟩
  invFun x := ⟨x.b, x.a, x.c + x.a * x.b⟩
  left_inv x := UT3.ext rfl rfl (by
    change x.c + x.a * x.b + x.b * x.a = x.c
    linear_combination f4_add_self (x.a * x.b))
  right_inv x := UT3.ext rfl rfl (by
    change x.c + x.a * x.b + x.b * x.a = x.c
    linear_combination f4_add_self (x.a * x.b))
  map_mul' x y := UT3.ext rfl rfl (by
    change x.c + y.c + x.a * y.b + (x.a + y.a) * (x.b + y.b) =
      x.c + x.a * x.b + (y.c + y.a * y.b) + x.b * y.a
    linear_combination f4_add_self (x.a * y.b))

@[expose] def scHom (lam mu q q' : F4c) : FzUT →* FzUT where
  toFun x := ⟨lam * x.a, mu * x.b, lam * mu * x.c + q * (x.a * x.a) + q' * (x.b * x.b)⟩
  map_one' := UT3.ext (mul_zero _) (mul_zero _) (by
    change lam * mu * 0 + q * (0 * 0) + q' * (0 * 0) = 0
    ring)
  map_mul' x y := UT3.ext (by change lam * (x.a + y.a) = lam * x.a + lam * y.a; ring)
    (by change mu * (x.b + y.b) = mu * x.b + mu * y.b; ring) (by
      change lam * mu * (x.c + y.c + x.a * y.b) + q * ((x.a + y.a) * (x.a + y.a)) +
          q' * ((x.b + y.b) * (x.b + y.b)) =
        lam * mu * x.c + q * (x.a * x.a) + q' * (x.b * x.b) +
          (lam * mu * y.c + q * (y.a * y.a) + q' * (y.b * y.b)) + lam * x.a * (mu * y.b)
      rw [kcF4_frob_add, kcF4_frob_add]
      ring)

theorem scHom_inj {lam mu q q' : F4c} (hl : lam ≠ 0) (hm : mu ≠ 0) :
    Function.Injective (scHom lam mu q q') := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have ha : lam * x.a = 0 := congrArg UT3.a hx
  have hb : mu * x.b = 0 := congrArg UT3.b hx
  have hc : lam * mu * x.c + q * (x.a * x.a) + q' * (x.b * x.b) = 0 := congrArg UT3.c hx
  have ha' : x.a = 0 := (mul_eq_zero.mp ha).resolve_left hl
  have hb' : x.b = 0 := (mul_eq_zero.mp hb).resolve_left hm
  rw [ha', hb'] at hc
  have hc' : x.c = 0 := by
    have : lam * mu * x.c = 0 := by simpa using hc
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero hl hm)
  exact UT3.ext ha' hb' hc'

@[expose] noncomputable def scA (lam mu q q' : F4c) (hl : lam ≠ 0) (hm : mu ≠ 0) : MulAut FzUT :=
  MulEquiv.ofBijective (scHom lam mu q q')
    ⟨scHom_inj hl hm, Finite.injective_iff_surjective.mp (scHom_inj hl hm)⟩

theorem enc_fields : ∀ x : FzUT, (enc x &&& 3) = enc4 x.a ∧ ((enc x >>> 2) &&& 3) = enc4 x.b ∧
    (enc x >>> 4) = enc4 x.c := by
  decide +kernel

theorem enc4_add : ∀ a b : F4c, enc4 (a + b) = enc4 a ^^^ enc4 b := by decide +kernel

theorem scP_eq (lam mu q q' : F4c) (x : FzUT) :
    scP (enc4 lam) (enc4 mu) (enc4 q) (enc4 q') (enc x) = enc (scHom lam mu q q' x) := by
  obtain ⟨h1, h2, h3⟩ := enc_fields x
  simp only [scP, h1, h2, h3, f4mulP_eq]
  change _ = enc4 (lam * x.a) + 4 * enc4 (mu * x.b) +
    16 * enc4 (lam * mu * x.c + q * (x.a * x.a) + q' * (x.b * x.b))
  rw [enc4_add, enc4_add]

theorem tauP_eq : ∀ x : FzUT, tauP (enc x) = enc (tauA x) := by decide +kernel

theorem enc4_dec4 {n : Nat} (hn : n < 4) : enc4 (dec4 n) = n := by
  interval_cases n <;> decide +kernel

theorem land3_lt (n : Nat) : n &&& 3 < 4 := Nat.lt_succ_of_le Nat.and_le_right

theorem dec4_ne {n : Nat} (hn : n < 4) (h : n ≠ 0) : dec4 n ≠ 0 := by
  intro h'
  apply h
  rw [← enc4_dec4 hn, h']
  rfl

@[expose] noncomputable def betaA (p : Nat) (hp : pOK p = true) : MulAut FzUT :=
  (Bool.rec (motive := fun _ => MulAut FzUT) 1 tauA (Nat.beq ((p >>> 8) &&& 1) 1)).trans
    (scA (dec4 (p &&& 3)) (dec4 ((p >>> 2) &&& 3)) (dec4 ((p >>> 4) &&& 3)) (dec4 ((p >>> 6) &&& 3))
      (dec4_ne (land3_lt p) (by
        have := (band_iff _ _).mp hp
        exact fun h0 => by rw [h0] at this; simp [bnot] at this))
      (dec4_ne (land3_lt _) (by
        have := (band_iff _ _).mp hp
        exact fun h0 => by rw [h0] at this; simp [bnot] at this)))

theorem betaP_eq (p : Nat) (hp : pOK p = true) (x : FzUT) :
    betaP p (enc x) = enc (betaA p hp x) := by
  have e1 := enc4_dec4 (land3_lt p)
  have e2 := enc4_dec4 (land3_lt (p >>> 2))
  have e3 := enc4_dec4 (land3_lt (p >>> 4))
  have e4 := enc4_dec4 (land3_lt (p >>> 6))
  unfold betaP betaA
  cases Nat.beq ((p >>> 8) &&& 1) 1
  · change scP (p &&& 3) ((p >>> 2) &&& 3) ((p >>> 4) &&& 3) ((p >>> 6) &&& 3) (enc x) =
      enc (scHom _ _ _ _ x)
    have := scP_eq (dec4 (p &&& 3)) (dec4 ((p >>> 2) &&& 3)) (dec4 ((p >>> 4) &&& 3))
      (dec4 ((p >>> 6) &&& 3)) x
    rw [e1, e2, e3, e4] at this
    exact this
  · change scP (p &&& 3) ((p >>> 2) &&& 3) ((p >>> 4) &&& 3) ((p >>> 6) &&& 3) (tauP (enc x)) =
      enc (scHom _ _ _ _ (tauA x))
    have := scP_eq (dec4 (p &&& 3)) (dec4 ((p >>> 2) &&& 3)) (dec4 ((p >>> 4) &&& 3))
      (dec4 ((p >>> 6) &&& 3)) (tauA x)
    rw [e1, e2, e3, e4] at this
    rw [tauP_eq]
    exact this

theorem w2_sq : fzW2 * fzW2 = fzW := by decide +kernel

theorem scHom_rho (lam mu q q' : F4c) (x : FzUT) :
    scHom lam mu q q' (fzRho0 x) = fzRho0 (scHom lam mu q q' x) := by
  apply UT3.ext
  · change lam * (fzW2 * x.a) = fzW2 * (lam * x.a)
    ring
  · change mu * (fzW2 * x.b) = fzW2 * (mu * x.b)
    ring
  · change lam * mu * (fzW * x.c) + q * (fzW2 * x.a * (fzW2 * x.a)) +
        q' * (fzW2 * x.b * (fzW2 * x.b)) =
      fzW * (lam * mu * x.c + q * (x.a * x.a) + q' * (x.b * x.b))
    have e : ∀ u : F4c, fzW2 * u * (fzW2 * u) = fzW * (u * u) := by
      intro u
      rw [← w2_sq]
      ring
    rw [e, e]
    ring

theorem tau_rho (x : FzUT) : tauA (fzRho0 x) = fzRho0 (tauA x) := by
  apply UT3.ext
  · rfl
  · rfl
  · change fzW * x.c + fzW2 * x.a * (fzW2 * x.b) = fzW * (x.c + x.a * x.b)
    have e : fzW2 * x.a * (fzW2 * x.b) = fzW * (x.a * x.b) := by
      rw [← w2_sq]
      ring
    rw [e]
    ring

theorem betaA_rho (p : Nat) (hp : pOK p = true) (x : FzUT) :
    betaA p hp (fzRho0 x) = fzRho0 (betaA p hp x) := by
  unfold betaA
  cases Nat.beq ((p >>> 8) &&& 1) 1
  · exact scHom_rho _ _ _ _ x
  · change scHom _ _ _ _ (tauA (fzRho0 x)) = fzRho0 (scHom _ _ _ _ (tauA x))
    rw [tau_rho, scHom_rho]

theorem gc_cj_of_conjOK {p Y T' : Nat} (hp : pOK p = true) (σ : MulAut FzUT)
    (hT' : T' < 16777216) (h : conjOK p Y (gc σ) T' = true) : gc (cj (betaA p hp) σ) = T' := by
  rw [conjOK, allN_iff] at h
  have key : ∀ k < 4, enc (cj (betaA p hp) σ (genE k)) = c4 T' k := by
    intro k hk
    obtain ⟨h1, h2⟩ := (band_iff _ _).mp (h k hk)
    rw [beq_iff] at h1 h2
    set y := dec (c4 Y k)
    have hy : enc y = c4 Y k := enc_dec' (c4_lt Y k)
    rw [← hy, betaP_eq p hp, ← enc_genE hk] at h1
    have hy' : (betaA p hp).symm (genE k) = y := by
      rw [← enc_injective h1, MulEquiv.symm_apply_apply]
    rw [← hy, evD_gc, betaP_eq p hp] at h2
    rw [cj_apply, hy', h2]
  rw [← pk4_c4 hT', gc, ← key 0 (by norm_num), ← key 1 (by norm_num), ← key 2 (by norm_num),
    ← key 3 (by norm_num)]
  rfl

variable {t s l : MulAut FzUT}

theorem inZ_codes' : ∀ z : FzUT, z.a = 0 → z.b = 0 →
    enc z = 0 ∨ enc z = 16 ∨ enc z = 32 ∨ enc z = 48 := by
  decide +kernel

theorem inZ_codes (z : FzUT) (h : FzInZ z) : enc z = 0 ∨ enc z = 16 ∨ enc z = 32 ∨ enc z = 48 :=
  inZ_codes' z h.1 h.2

theorem tcand_of_valid (h : FzValidTriple t s l) :
    ∃ i < 4, ∃ j < 4, gc t = tcand (16 * i) (16 * j) := by
  have hz : ∀ g : FzUT, ∃ i < 4, t g = (t g * g⁻¹) * g ∧ enc (t g * g⁻¹) = 16 * i := by
    intro g
    refine ?_
    rcases inZ_codes _ (h.t_Z g) with e | e | e | e
    · exact ⟨0, by norm_num, by group, e⟩
    · exact ⟨1, by norm_num, by group, e⟩
    · exact ⟨2, by norm_num, by group, e⟩
    · exact ⟨3, by norm_num, by group, e⟩
  obtain ⟨i, hi, e2, c2⟩ := hz fzEW
  obtain ⟨j, hj, e4, c4'⟩ := hz fzFW
  refine ⟨i, hi, j, hj, ?_⟩
  have h2 : enc (t fzEW) = pmulP (16 * i) 2 := by rw [e2, enc_mul, c2, enc_ew]
  have h4 : enc (t fzFW) = pmulP (16 * j) 8 := by rw [e4, enc_mul, c4', enc_fw]
  rw [gc, tcand, e1_rho, f1_rho, h.t_rho, h.t_rho, ← r0P_eq, ← r0P_eq, h2, h4]

theorem scand_of_valid (h : FzValidTriple t s l) :
    ∃ u u' : FzUT, t u = u ∧ t u' = u' ∧ gc s = scand (enc u) (enc u') := by
  refine ⟨s fzEW * fzEW⁻¹, s fzFW * fzFW⁻¹, h.s_fix _, h.s_fix _, ?_⟩
  have h2 : enc (s fzEW) = pmulP (enc (s fzEW * fzEW⁻¹)) 2 := by
    rw [← enc_ew, ← enc_mul, inv_mul_cancel_right]
  have h4 : enc (s fzFW) = pmulP (enc (s fzFW * fzFW⁻¹)) 8 := by
    rw [← enc_fw, ← enc_mul, inv_mul_cancel_right]
  rw [gc, scand, e1_rho, f1_rho, h.s_rho, h.s_rho, ← r0P_eq, ← r0P_eq, h2, h4]

theorem lcand_of_valid (h : FzValidTriple t s l) :
    gc l = lcand (enc (l fzEW)) (enc (l fzFW)) := by
  rw [gc, lcand, e1_rho, f1_rho, h.l_rho, h.l_rho, ← r0P_eq, ← r0P_eq, ← r0P_eq, ← r0P_eq]

theorem inv_of_aut (σ : MulAut FzUT) (g : FzUT) (hg : g * g = 1) (h1 : g ≠ 1) :
    pmulP (enc (σ g)) (enc (σ g)) = 0 ∧ enc (σ g) ≠ 0 := by
  refine ⟨by rw [← enc_mul, ← map_mul, hg, map_one, enc_one], fun h0 => h1 ?_⟩
  have : σ g = 1 := enc_injective (by rw [h0, enc_one])
  simpa using this

theorem mem_of_invOK {IV : Nat} (hIV : invOK IV = true) {v : Nat} (hv : v < 64)
    (hsq : pmulP v v = 0) (h0 : v ≠ 0) : ∃ a < 27, fldN IV 6 63 a = v := by
  rw [invOK, allN_iff] at hIV
  have h := (bimp_iff _ _).mp (hIV v hv) ((beq_iff _ _).mpr hsq)
  have hb : Nat.beq v 0 = false := by
    cases hb : Nat.beq v 0
    · rfl
    · exact absurd ((beq_iff _ _).mp hb) h0
  rw [hb] at h
  obtain ⟨a, ha, hav⟩ := (anyN_iff _ _).mp h
  exact ⟨a, ha, (beq_iff _ _).mp hav⟩

theorem fix_codes (h : FzValidTriple t s l) {F : Nat} (hF : fixOK (gc t) F = true) {u : FzUT}
    (hu : t u = u) : ∃ a < 16, fldN F 6 63 a = enc u := by
  rw [fixOK, allN_iff] at hF
  have h' := (bimp_iff _ _).mp (hF (enc u) (enc_lt u)) ((beq_iff _ _).mpr (by rw [evD_gc, hu]))
  obtain ⟨a, ha, hav⟩ := (anyN_iff _ _).mp h'
  exact ⟨a, ha, (beq_iff _ _).mp hav⟩

theorem sCheap_of_valid (h : FzValidTriple t s l) : sCheap (gc t) (gc s) = true := by
  rw [sCheap, band_iff, band_iff, allN_iff, allN_iff, bnot_iff]
  refine ⟨fun k hk => ?_, ?_, fun x hx => ?_⟩
  · rw [band_iff, beq_iff, beq_iff, c4_gc s hk, c4_gc t hk, evD_gc, evD_gc, evD_gc, h.s_sq,
      h.ts, enc_genE hk]
    exact ⟨rfl, rfl⟩
  · cases hb : Nat.beq (gc s) (pk4 1 2 4 8)
    · rfl
    · obtain ⟨x, hx⟩ := h.s_ne
      exact absurd (eq_of_gc (((beq_iff _ _).mp hb).trans gc_one.symm) x) hx
  · rw [bimp_iff, beq_iff, beq_iff, ← enc_dec' hx, evD_gc, evD_gc, invP_eq]
    intro hf
    rw [h.s_inv _ (enc_injective hf)]

theorem lCheap_of_valid (h : FzValidTriple t s l) : lCheap (gc t) (gc l) = true := by
  rw [lCheap, band_iff, band_iff, allN_iff, anyN_iff, anyN_iff]
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · rw [band_iff, beq_iff, beq_iff, c4_gc l hk, c4_gc t hk]
    simp only [evD_gc]
    rw [h.l_sq, h.tl, enc_genE hk]
    exact ⟨rfl, rfl⟩
  · obtain ⟨z, hz, hlz⟩ := h.l_Z
    have hz1 : z ≠ 1 := fun e => hlz (by rw [e, map_one])
    have hz0 : enc z ≠ 0 := fun e => hz1 (enc_injective (by rw [e, enc_one]))
    have hne : evD (gc l) (enc z) ≠ enc z := by
      rw [evD_gc]
      exact fun e => hlz (enc_injective e)
    have hb : ∀ n, evD (gc l) n ≠ n → bnot (Nat.beq (evD (gc l) n) n) = true := by
      intro n hn
      rw [bnot_iff]
      cases hb : Nat.beq (evD (gc l) n) n
      · rfl
      · exact absurd ((beq_iff _ _).mp hb) hn
    rcases inZ_codes z hz with e | e | e | e
    · exact absurd e hz0
    · rw [e] at hne
      exact ⟨0, by norm_num, hb 16 hne⟩
    · rw [e] at hne
      exact ⟨1, by norm_num, hb 32 hne⟩
    · rw [e] at hne
      exact ⟨2, by norm_num, hb 48 hne⟩
  · obtain ⟨x, hx⟩ := h.l_Q
    refine ⟨enc x, enc_lt x, ?_⟩
    rw [bnot_iff, evD_gc, invP_eq, ← enc_mul, evD_gc]
    cases hb : Nat.beq (enc (t (l x * x⁻¹))) (enc (l x * x⁻¹))
    · rfl
    · exact absurd (enc_injective ((beq_iff _ _).mp hb)) hx

theorem pow_cases (z : FzUT) (hz : z * z = 1) (i : Fin 4) : z ^ (i : ℕ) = 1 ∨ z ^ (i : ℕ) = z := by
  fin_cases i <;> simp [pow_succ, hz, mul_assoc]

theorem noX_of_elemab (h : FzValidTriple t s l) (he : ∀ x, t x = x → x * x = 1) :
    ∀ x₁, ¬ FzValidX t l x₁ := by
  intro x₁ hx
  have h1 : x₁ * x₁ = 1 := he _ hx.fix
  have h2 : l x₁ * l x₁ = 1 := he _ ((hx.gen (l x₁)).mpr ⟨0, 1, by simp⟩)
  have hsub : (Finset.univ.filter fun y : FzUT => t y = y) ⊆ {1, x₁, l x₁, x₁ * l x₁} := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨i, j, rfl⟩ := (hx.gen y).mp hy
    rcases pow_cases _ h1 i with e | e <;> rcases pow_cases _ h2 j with e' | e' <;> simp [e, e']
  have hc := Finset.card_le_card hsub
  rw [h.t_fix] at hc
  have h4 : ({1, x₁, l x₁, x₁ * l x₁} : Finset FzUT).card ≤ 4 := Finset.card_le_four
  omega

theorem e1f1_inv : fzE1⁻¹ * fzF1⁻¹ ≠ (fzE1 * fzF1)⁻¹ := by decide +kernel

theorem id_impossible (h : FzValidTriple t s l) (ht : ∀ x, t x = x) : False := by
  have h1 := h.s_inv fzE1 (ht _)
  have h3 := h.s_inv fzF1 (ht _)
  have h13 := h.s_inv (fzE1 * fzF1) (ht _)
  rw [map_mul, h1, h3] at h13
  exact e1f1_inv h13

theorem id_gens : enc fzIdD.g1 = 1 ∧ enc fzIdD.g2 = 2 ∧ enc fzIdD.g3 = 4 ∧ enc fzIdD.g4 = 8 := by
  decide +kernel

theorem evN_id (x : FzUT) : evN 1 2 4 8 (enc x) = enc x := by
  have := evN_eq fzIdD x
  obtain ⟨h1, h2, h3, h4⟩ := id_gens
  rw [fzEv_id, h1, h2, h3, h4] at this
  exact this

theorem tStage {TG TR : Nat} (ht : tScan TG TR = true) (h : FzValidTriple t s l) :
    (∀ x₁, ¬ FzValidX t l x₁) ∨
      ∃ p, ∃ hp : pOK p = true, ∃ k < 4, gc (cj (betaA p hp) t) = fldN TG 24 16777215 k := by
  obtain ⟨i, hi, j, hj, e⟩ := tcand_of_valid h
  rw [tScan, allN_iff] at ht
  have h1 := (allN_iff _ _).mp (ht i hi) j hj
  rw [← e] at h1
  unfold tRecOK at h1
  cases hk0 : Nat.beq (fldN TR 40 1099511627775 (4 * i + j) &&& 3) 0
  · rw [hk0] at h1
    cases hk1 : Nat.beq (fldN TR 40 1099511627775 (4 * i + j) &&& 3) 1
    · rw [hk1] at h1
      obtain ⟨-, h1⟩ := (band_iff _ _).mp h1
      obtain ⟨hp, h1⟩ := (band_iff _ _).mp h1
      obtain ⟨-, h1⟩ := (band_iff _ _).mp h1
      exact Or.inr ⟨_, hp, _, land3_lt _, gc_cj_of_conjOK hp t (fld24_lt _ _) h1⟩
    · rw [hk1] at h1
      left
      apply noX_of_elemab h
      intro x hx
      rw [elemabOK, allN_iff] at h1
      have := (bimp_iff _ _).mp (h1 (enc x) (enc_lt x)) ((beq_iff _ _).mpr (by rw [evD_gc, hx]))
      rw [beq_iff, ← enc_mul, ← enc_one] at this
      exact enc_injective this
  · rw [hk0] at h1
    exfalso
    apply id_impossible h
    intro x
    have := evD_gc t x
    rw [(beq_iff _ _).mp h1, evD_pk4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      evN_id] at this
    exact (enc_injective this).symm

theorem ew_sq : fzEW * fzEW = 1 ∧ fzEW ≠ 1 ∧ fzFW * fzFW = 1 ∧ fzFW ≠ 1 := by decide +kernel

theorem lScan_ok {IV : Nat} {ok : Nat → Bool} (hiv : invOK IV = true)
    (hl : lScan IV (gc t) ok = true) (h : FzValidTriple t s l) : ok (gc l) = true := by
  obtain ⟨q1, q2, q3, q4⟩ := ew_sq
  have hv := inv_of_aut l fzEW q1 q2
  have hv' := inv_of_aut l fzFW q3 q4
  obtain ⟨c, hc, ec⟩ := mem_of_invOK hiv (enc_lt _) hv.1 hv.2
  obtain ⟨d, hd, ed⟩ := mem_of_invOK hiv (enc_lt _) hv'.1 hv'.2
  rw [lScan, allN_iff] at hl
  have := (allN_iff _ _).mp (hl c hc) d hd
  rw [sb_eq, ec, ed, ← lcand_of_valid h] at this
  exact (bimp_iff _ _).mp this (lCheap_of_valid h)

theorem sStage {RP F Lp K Bp IV : Nat} (hfix : fixOK (gc t) F = true) (hiv : invOK IV = true)
    (hl : lScan IV (gc t) (inL Lp) = true) (hs : sScan RP (gc t) F Lp K Bp = true)
    (h : FzValidTriple t s l) :
    ∃ p, ∃ hp : pOK p = true, ∃ k < 4, gc (cj (betaA p hp) t) = gc t ∧
      gc (cj (betaA p hp) s) = fldN (fldN RP 48 281474976710655 k) 24 16777215 0 ∧
      gc (cj (betaA p hp) l) = fldN (fldN RP 48 281474976710655 k) 24 16777215 1 := by
  obtain ⟨u, u', hu, hu', es⟩ := scand_of_valid h
  obtain ⟨a, ha, ea⟩ := fix_codes h hfix hu
  obtain ⟨b, hb, eb⟩ := fix_codes h hfix hu'
  have hinL := lScan_ok hiv hl h
  rw [inL, anyN_iff] at hinL
  obtain ⟨j, hj, ej⟩ := hinL
  rw [beq_iff] at ej
  rw [sScan, allN_iff] at hs
  have h1 := (allN_iff _ _).mp (hs a ha) b hb
  rw [sb_eq, ea, eb, ← es] at h1
  have h2 := (bimp_iff _ _).mp h1 (sCheap_of_valid h)
  rw [allN_iff] at h2
  have h3 := h2 j hj
  rw [ej] at h3
  unfold pairOK at h3
  have hcomm : allN 4 (fun k => Nat.beq (evD (gc s) (c4 (gc l) k)) (evD (gc l) (c4 (gc s) k))) =
      true := by
    rw [allN_iff]
    intro k hk
    rw [beq_iff, c4_gc s hk, c4_gc l hk, evD_gc, evD_gc, h.sl]
  have h4 := (bimp_iff _ _).mp h3 hcomm
  obtain ⟨-, h4⟩ := (band_iff _ _).mp h4
  obtain ⟨hp, h4⟩ := (band_iff _ _).mp h4
  obtain ⟨ht', h4⟩ := (band_iff _ _).mp h4
  obtain ⟨hs', hl'⟩ := (band_iff _ _).mp h4
  exact ⟨_, hp, _, land3_lt _, gc_cj_of_conjOK hp t (gc_lt t) ht',
    gc_cj_of_conjOK hp s (fld24_lt _ _) hs', gc_cj_of_conjOK hp l (fld24_lt _ _) hl'⟩

theorem genE0_ne : genE 0 ≠ 1 := by decide +kernel

theorem norm_sound {TG TR IV F Lp K Bp RP : Nat} (ht : tScan TG TR = true)
    (ht1 : lScan IV (fldN TG 24 16777215 1) (fun _ => false) = true)
    (ht2 : lScan IV (fldN TG 24 16777215 2) (fun _ => false) = true)
    (hTG3 : fldN TG 24 16777215 3 = 0)
    (hiv : invOK IV = true) (hfix : fixOK (fldN TG 24 16777215 0) F = true)
    (hl : lScan IV (fldN TG 24 16777215 0) (inL Lp) = true)
    (hs : sScan RP (fldN TG 24 16777215 0) F Lp K Bp = true)
    (P : MulAut FzUT → MulAut FzUT → MulAut FzUT → Prop)
    (hP : ∀ β t s l, (∀ x, β (fzRho0 x) = fzRho0 (β x)) → P (cj β t) (cj β s) (cj β l) →
      P t s l)
    (hvac : ∀ t s l, FzValidTriple t s l → (∀ x₁, ¬ FzValidX t l x₁) → P t s l)
    (hrep : ∀ t s l, FzValidTriple t s l → ∀ k < 4, gc t = fldN TG 24 16777215 0 →
      gc s = fldN (fldN RP 48 281474976710655 k) 24 16777215 0 →
      gc l = fldN (fldN RP 48 281474976710655 k) 24 16777215 1 → P t s l) :
    ∀ t s l, FzValidTriple t s l → P t s l := by
  intro t s l h
  rcases tStage ht h with hv | ⟨p, hp, k, hk, e⟩
  · exact hvac t s l h hv
  have hβ : ∀ x, betaA p hp (fzRho0 x) = fzRho0 (betaA p hp x) := betaA_rho p hp
  have h' := validTriple_cj (betaA p hp) hβ h
  apply hP (betaA p hp) t s l hβ
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk' with rfl | rfl | rfl | rfl
  · rw [← e] at hfix hl hs
    obtain ⟨p', hp', k', hk', e1, e2, e3⟩ := sStage hfix hiv hl hs h'
    have hβ' := betaA_rho p' hp'
    apply hP (betaA p' hp') _ _ _ hβ'
    exact hrep _ _ _ (validTriple_cj (betaA p' hp') hβ' h') k' hk' (e1.trans e) e2 e3
  · rw [← e] at ht1
    exact absurd (lScan_ok hiv ht1 h') (by simp)
  · rw [← e] at ht2
    exact absurd (lScan_ok hiv ht2 h') (by simp)
  · rw [hTG3] at e
    exfalso
    have h0 := c4_gc (cj (betaA p hp) t) (k := 0) (by norm_num)
    rw [e] at h0
    have h1 : cj (betaA p hp) t (genE 0) = 1 :=
      enc_injective (by rw [← h0, enc_one]; rfl)
    exact genE0_ne ((cj (betaA p hp) t).injective (h1.trans (map_one _).symm))

theorem classA_of_norm {TG TR IV F Lp K Bp RP : Nat} (ht : tScan TG TR = true)
    (ht1 : lScan IV (fldN TG 24 16777215 1) (fun _ => false) = true)
    (ht2 : lScan IV (fldN TG 24 16777215 2) (fun _ => false) = true)
    (hTG3 : fldN TG 24 16777215 3 = 0)
    (hiv : invOK IV = true) (hfix : fixOK (fldN TG 24 16777215 0) F = true)
    (hl : lScan IV (fldN TG 24 16777215 0) (inL Lp) = true)
    (hs : sScan RP (fldN TG 24 16777215 0) F Lp K Bp = true)
    (hrep : ∀ t s l, FzValidTriple t s l → ∀ k < 4, gc t = fldN TG 24 16777215 0 →
      gc s = fldN (fldN RP 48 281474976710655 k) 24 16777215 0 →
      gc l = fldN (fldN RP 48 281474976710655 k) 24 16777215 1 →
      (∀ x₁, FzValidX t l x₁ → FzShape t s l x₁) ∨ FzAutW t s l) :
    FzClassSpecA := by
  intro t s l h
  refine norm_sound ht ht1 ht2 hTG3 hiv hfix hl hs
    (fun t s l => (∀ x₁, FzValidX t l x₁ → FzShape t s l x₁) ∨ FzAutW t s l) ?_ ?_ hrep t s l h
  · intro β t s l hβ hc
    rcases hc with hc | hc
    · exact Or.inl fun x₁ hx => shape_cj β (hc (β x₁) (validX_cj β hx))
    · exact Or.inr (autW_cj β hc)
  · intro t s l _ hv
    exact Or.inl fun x₁ hx => absurd hx (hv x₁)

end CFSG.KC.FzUT
