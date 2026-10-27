module

public import CFSG.Certificates.Kernel.G2Three.Sec1T1Sound
public import CFSG.Certificates.Kernel.G2Three.Sec1T3Real

public section

set_option exponentiation.threshold 1024

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KS.Mat3 CFSG.KC.Loop CFSG.KD.G2Three CFSG.KD.G2Three.Sec1 CFSG.KD.G2Three.Sec1T3
  CFSG.KC.G2Three.Sec1 CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

abbrev WS : Wm := wanti 1 1

theorem WS_mul_WS : WS * WS = 1 := by
  simp only [WS, wanti_mul_wanti, mul_one, wdiag_one]

theorem WS_pow_xor {p q : ℕ} (hp : p < 2) (hq : q < 2) :
    p ^^^ q < 2 ∧ WS ^ p * WS ^ q = WS ^ (p ^^^ q) := by
  interval_cases p <;> interval_cases q <;> simp [WS_mul_WS]

theorem okP_lt {x : ℕ} (hx : OkP x) : x < 2 ^ 784 := by
  have h1 : x / 2 ^ 392 < 2 ^ 392 := lt_of_canon hx.2
  have e : (2 : ℕ) ^ 784 = 2 ^ 392 * 2 ^ 392 := by rw [← pow_add]
  rw [e]
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 392)).1 h1

theorem split784 {d : ℕ} (f : ℕ) (hd : d < 2 ^ 784) :
    (d + f * 2 ^ 784) % 2 ^ 784 = d ∧ (d + f * 2 ^ 784) / 2 ^ 784 = f :=
  ⟨by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd],
    by rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos 784), Nat.div_eq_of_lt hd, Nat.zero_add]⟩

theorem LF_eq : LF = 2 ^ 784 - 1 := pow_sub_one_eq 784

theorem SIGF_eq : SIGF = ONEP + 1 * 2 ^ 784 := by
  change ONEP + 1 <<< 784 = _
  rw [Nat.shiftLeft_eq]

theorem MULF_eq (a b : ℕ) : MULF a b =
    MULP (a % 2 ^ 784) (if a / 2 ^ 784 = 1 then SWP (b % 2 ^ 784) else b % 2 ^ 784) +
      (a / 2 ^ 784 ^^^ b / 2 ^ 784) * 2 ^ 784 := by
  have hb : ∀ (c : Bool) (u v : ℕ),
      Bool.rec (motive := fun _ => ℕ) v u c = if c = true then u else v := by
    intro c u v
    cases c <;> rfl
  change MULP (a &&& LF) (Bool.rec (motive := fun _ => ℕ) (b &&& LF) (SWP (b &&& LF))
    (Nat.beq (a >>> 784) 1)) + (a >>> 784 ^^^ b >>> 784) <<< 784 = _
  rw [LF_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, hb]
  simp only [Nat.beq_eq]

variable {G : Type} [Group G] (ρ : G →* Wm)

@[expose] def EncF (x : ℕ) (g : G) : Prop :=
  x / 2 ^ 784 < 2 ∧ OkP (x % 2 ^ 784) ∧ ρ g = decP (x % 2 ^ 784) * WS ^ (x / 2 ^ 784)

theorem encF_of_enc {x : ℕ} {g : G} (h : Enc ρ x g) : EncF ρ x g := by
  have hx := okP_lt h.1
  have e1 : x % 2 ^ 784 = x := Nat.mod_eq_of_lt hx
  have e2 : x / 2 ^ 784 = 0 := Nat.div_eq_of_lt hx
  refine ⟨by rw [e2]; norm_num, by rw [e1]; exact h.1, ?_⟩
  rw [e1, e2, pow_zero, mul_one]
  exact h.2

theorem encF_SIGF {s : G} (hs : ρ s = WS) : EncF ρ SIGF s := by
  obtain ⟨e1, e2⟩ := split784 1 (okP_lt okP_ONEP)
  rw [SIGF_eq]
  refine ⟨by rw [e2]; norm_num, by rw [e1]; exact okP_ONEP, ?_⟩
  rw [e1, e2, decP_ONEP, pow_one, one_mul, hs]

theorem encF_MULF {a b : ℕ} {g h : G} (ha : EncF ρ a g) (hb : EncF ρ b h) :
    EncF ρ (MULF a b) (g * h) := by
  obtain ⟨fa, da, ra⟩ := ha
  obtain ⟨fb, db, rb⟩ := hb
  rw [MULF_eq]
  generalize a / 2 ^ 784 = p at fa ra ⊢
  generalize b / 2 ^ 784 = q at fb rb ⊢
  generalize a % 2 ^ 784 = A at da ra ⊢
  generalize b % 2 ^ 784 = B at db rb ⊢
  have hE : OkP (if p = 1 then SWP B else B) ∧
      decP (if p = 1 then SWP B else B) * WS ^ p = WS ^ p * decP B := by
    split_ifs with hp
    · refine ⟨okP_SWP db, ?_⟩
      rw [hp, pow_one, decP_SWP db, mul_assoc, WS_mul_WS, mul_one]
    · have hp0 : p = 0 := by omega
      exact ⟨db, by rw [hp0, pow_zero, mul_one, one_mul]⟩
  generalize (if p = 1 then SWP B else B) = E at hE ⊢
  have hd := okP_MULP da hE.1
  obtain ⟨e1, e2⟩ := split784 (p ^^^ q) (okP_lt hd)
  obtain ⟨hx, hW⟩ := WS_pow_xor fa fb
  refine ⟨by rw [e2]; exact hx, by rw [e1]; exact hd, ?_⟩
  rw [e1, e2, map_mul, ra, rb, decP_MULP da hE.1, ← hW]
  calc decP A * WS ^ p * (decP B * WS ^ q) = decP A * (WS ^ p * decP B) * WS ^ q := by
        simp only [mul_assoc]
    _ = decP A * (decP E * WS ^ p) * WS ^ q := by rw [hE.2]
    _ = decP A * decP E * (WS ^ p * WS ^ q) := by simp only [mul_assoc]

theorem encF_unique {ρ : G →* Wm} (hρ : Function.Injective ρ) {a : ℕ} {g h : G}
    (hg : EncF ρ a g) (hh : EncF ρ a h) : g = h :=
  hρ (hg.2.2.trans hh.2.2.symm)

theorem wdiag_eq_zero_of_eq_wanti {A B C D : Matrix (Fin 14) (Fin 14) (ZMod 3)}
    (h : wdiag A B = wanti C D) : wdiag A B = 0 := by
  unfold wdiag wanti at h
  obtain ⟨h1, -, -, h4⟩ := Matrix.fromBlocks_inj.1 h
  rw [wdiag, h1, h4, Matrix.fromBlocks_zero]

theorem rho_ne_zero (g : G) : ρ g ≠ 0 := by
  intro h
  have e : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at e
  have e' := congrFun (congrFun e (Sum.inl 0)) (Sum.inl 0)
  rw [Matrix.zero_apply, Matrix.one_apply_eq] at e'
  exact absurd e' (by decide)

theorem not_decP_eq_mul_WS {g : G} {x y : ℕ} (hg : ρ g = decP x) (h : decP x = decP y * WS) :
    False := by
  apply rho_ne_zero ρ g
  rw [hg]
  unfold decP at h ⊢
  rw [WS, wdiag_mul_wanti] at h
  exact wdiag_eq_zero_of_eq_wanti h

theorem encF_inj {a b : ℕ} {g : G} (ha : EncF ρ a g) (hb : EncF ρ b g) : a = b := by
  obtain ⟨fa, da, ra⟩ := ha
  obtain ⟨fb, db, rb⟩ := hb
  have key : a % 2 ^ 784 = b % 2 ^ 784 ∧ a / 2 ^ 784 = b / 2 ^ 784 := by
    generalize a / 2 ^ 784 = p at fa ra ⊢
    generalize b / 2 ^ 784 = q at fb rb ⊢
    generalize a % 2 ^ 784 = A at da ra ⊢
    generalize b % 2 ^ 784 = B at db rb ⊢
    have e := ra.symm.trans rb
    interval_cases p <;> interval_cases q
    · rw [pow_zero, mul_one, mul_one] at e
      exact ⟨decP_inj da db e, rfl⟩
    · simp only [pow_zero, mul_one, pow_one] at e ra
      exact (not_decP_eq_mul_WS ρ ra e).elim
    · simp only [pow_zero, mul_one, pow_one] at e rb
      exact (not_decP_eq_mul_WS ρ rb e.symm).elim
    · rw [pow_one] at e
      have e2 := congrArg (· * WS) e
      simp only [mul_assoc, WS_mul_WS, mul_one] at e2
      exact ⟨decP_inj da db e2, rfl⟩
  rw [← Nat.mod_add_div a (2 ^ 784), ← Nat.mod_add_div b (2 ^ 784), key.1, key.2]

theorem closR_at {X Gd : ℕ → ℕ} {RT lo m hi : ℕ} (h : closR X Gd RT lo m hi = true)
    (hm : m ≤ 64 * hi) (q : ℕ) (h1 : lo ≤ q) (h2 : q < lo + m) :
    X (rtA RT (q / 6) (q % 6)) = MULF (X (q / 6)) (Gd (q % 6)) := by
  have := allBelow_spec h hm (q - lo) (by omega)
  have e : Nat.add lo (q - lo) = q := by
    change lo + (q - lo) = q
    omega
  dsimp only at this
  rw [e] at this
  exact Nat.eq_of_beq_eq_true this

theorem flag_tab {X Gd : ℕ → ℕ} {RT PA PB : ℕ} {g : ℕ → G}
    (hg : ∀ s < 6, EncF ρ (Gd s) (g s)) (h0 : X 0 = ONEP)
    (hcl : ∀ i < 128, ∀ s < 6, X (rtA RT i s) = MULF (X i) (Gd s))
    (hpar : ∀ j < 127, parA PA j ≤ j ∧ parA PB j < 6 ∧ rtA RT (parA PA j) (parA PB j) = j + 1) :
    ∀ i < 128, ∃ x : G, EncF ρ (X i) x := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | j
    · exact ⟨1, by rw [h0]; exact encF_of_enc ρ (enc_one ρ)⟩
    · obtain ⟨hpa, hpb, hp⟩ := hpar j (by omega)
      obtain ⟨x, hx⟩ := ih (parA PA j) (by omega) (by omega)
      refine ⟨x * g (parA PB j), ?_⟩
      rw [← hp, hcl _ (by omega) _ hpb]
      exact encF_MULF ρ hx (hg _ hpb)

variable {ρ} in
theorem flag_realT (hρ : Function.Injective ρ) {X Gd : ℕ → ℕ} {RT PA PB P C V Q : ℕ}
    {g : ℕ → G} (hg : ∀ s < 6, EncF ρ (Gd s) (g s)) (h0 : X 0 = ONEP)
    (hcl : ∀ i < 128, ∀ s < 6, X (rtA RT i s) = MULF (X i) (Gd s))
    (hpar : ∀ j < 127, parA PA j ≤ j ∧ parA PB j < 6 ∧ rtA RT (parA PA j) (parA PB j) = j + 1)
    (hX : ∀ i < 128, ∀ j < 128, X i = X j → i = j)
    (htab : ∀ i < 128, atR (rowT P i) 0 = i ∧
      ∀ j < 127, atR (rowT P i) (j + 1) = rtA RT (atR (rowT P i) (parA PA j)) (parA PB j))
    (hcol : ∀ i < 128, ∀ j < 128, atR (rowT C j) i = atR (rowT P i) j)
    (hinv : ∀ i < 128, atR (rowT P i) (atR V i) = 0)
    (hsq : ∀ i < 128, atR Q i = atR (rowT P i) i) :
    ∃ elt : ℕ → G, RealT elt P C V Q ∧ ∀ i < 128, ∀ s < 6, elt (rtA RT i s) = elt i * g s := by
  choose! e he using flag_tab ρ hg h0 hcl hpar
  have h1 : e 0 = 1 :=
    encF_unique hρ (he 0 (by norm_num)) (by rw [h0]; exact encF_of_enc ρ (enc_one ρ))
  have hrt : ∀ i < 128, ∀ s < 6, rtA RT i s < 128 ∧ e (rtA RT i s) = e i * g s := by
    intro i hi s hs
    have hlt : rtA RT i s < 128 := fld127_lt _ _
    refine ⟨hlt, encF_unique hρ (he _ hlt) ?_⟩
    rw [hcl i hi s hs]
    exact encF_MULF ρ (he i hi) (hg s hs)
  have hinj : ∀ i < 128, ∀ j < 128, e i = e j → i = j := fun i hi j hj hij =>
    hX i hi j hj (encF_inj ρ (he i hi) (by rw [hij]; exact he j hj))
  exact ⟨e, realT_of h1 hrt hinj hpar htab hcol hinv hsq, fun i hi s hs => (hrt i hi s hs).2⟩

end CFSG.KC.G2Three.Sec1T3

end
