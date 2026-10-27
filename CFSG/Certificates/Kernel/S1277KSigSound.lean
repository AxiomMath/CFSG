module

public import Certificates.Data.Kernel.S1277KSig
public import CFSG.Certificates.Kernel.S1277KChainSound
public import CFSG.Certificates.Kernel.S1277KLatSound
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSSig

public section

namespace CFSG.KS.S1277Sig

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sig CFSG.KS.S1277Lat CFSG.KS.S1277Mod
  CFSG.Quasithin.H13.I1277 Certificates.Data.S1277Sig CFSG.KS.S1277Chain

@[expose] def φL (L : ℕ) (e : ℕ) : ℕ := if L.testBit e then 1 else 0

theorem φL_eq_iff {L a b : ℕ} : φL L a = φL L b ↔ L.testBit a = L.testBit b := by
  unfold φL
  cases L.testBit a <;> cases L.testBit b <;> simp

theorem apK_eq (t : List ℕ) : ∀ x, apK t x = applyCols t x := by
  induction t with
  | nil => intro x; rfl
  | cons c cs ih =>
    intro x
    change c * (x % 2) ^^^ apK cs (x / 2) = _
    rw [applyCols_cons, ih]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem orMask_testBit (f : ℕ → ℕ) (y : ℕ) :
    ∀ n, (orMask n f).testBit y = true ↔ ∃ x < n, f x = y := by
  intro n
  induction n with
  | zero => simp [orMask]
  | succ n ih =>
    change (orMask n f ||| 1 <<< f n).testBit y = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
    constructor
    · rintro (⟨x, hx, rfl⟩ | h)
      · exact ⟨x, by omega, rfl⟩
      · exact ⟨n, by omega, of_decide_eq_true h⟩
    · rintro ⟨x, hx, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr (decide_eq_true rfl)

theorem eqL_iff : ∀ {l l' : List ℕ}, eqL l l' = true ↔ l = l'
  | [], [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], _ :: _ => ⟨fun h => absurd h (by simp [eqL]), fun h => absurd h (by simp)⟩
  | _ :: _, [] => ⟨fun h => absurd h (by simp [eqL]), fun h => absurd h (by simp)⟩
  | a :: l, b :: l' => by
    change (Nat.beq a b && eqL l l') = true ↔ _
    rw [Bool.and_eq_true, Nat.beq_eq, eqL_iff, List.cons.injEq]

theorem surj_of_mask {d : ℕ} {f : ℕ → ℕ} (h : orMask (2 ^ d) f = 2 ^ 2 ^ d - 1) :
    ∀ y < 2 ^ d, ∃ x < 2 ^ d, f x = y := by
  intro y hy
  have : (orMask (2 ^ d) f).testBit y = true := by
    rw [h, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hy
  exact (orMask_testBit f y _).1 this

theorem applyCols_map (F : ℕ → ℕ) (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b) :
    ∀ (b : List ℕ) (y : ℕ), F (applyCols b y) = applyCols (b.map F) y := by
  have h0 : F 0 = 0 := by
    have := hF 0 0
    rw [Nat.xor_self, Nat.xor_self] at this
    exact this
  intro b
  induction b with
  | nil => intro y; rw [applyCols_nil, List.map_nil, applyCols_nil, h0]
  | cons c cs ih =>
    intro y
    rw [List.map_cons, applyCols_cons, applyCols_cons, hF, ih]
    split_ifs <;> simp [h0]

section Chain

variable {d L : ℕ} {b : List ℕ}

noncomputable def Gk (d L : ℕ) (b : List ℕ) (k : ℕ) : Subgroup (Equiv.Perm (Fin (2 ^ d))) where
  carrier := {σ | σ ∈ Sig d (φL L) ∧ ∀ i < k, ∀ h : b.getD i 0 < 2 ^ d,
    σ ⟨b.getD i 0, h⟩ = ⟨b.getD i 0, h⟩}
  one_mem' := ⟨(Sig d (φL L)).one_mem, fun _ _ _ => rfl⟩
  mul_mem' := fun {σ τ} hσ hτ => ⟨(Sig d (φL L)).mul_mem hσ.1 hτ.1, fun i hi h => by
    rw [Equiv.Perm.mul_apply, hτ.2 i hi h, hσ.2 i hi h]⟩
  inv_mem' := fun {σ} hσ => ⟨(Sig d (φL L)).inv_mem hσ.1, fun i hi h => by
    rw [Equiv.Perm.inv_eq_iff_eq, hσ.2 i hi h]⟩

theorem val_eq {σ : Equiv.Perm (Fin (2 ^ d))} (hσ : σ ∈ Sig d (φL L)) (x : Fin (2 ^ d)) :
    (σ x).1 = applyCols (colsOf σ) x.1 := applyCols_colsOf hσ.1 x

theorem fix_span (hlen : b.length = d) (hblt : ∀ c ∈ b, c < 2 ^ d) {k : ℕ} (hk : k ≤ d) {σ : Equiv.Perm (Fin (2 ^ d))}
    (hσ : σ ∈ Gk d L b k) {y : ℕ} (hy : y < 2 ^ k) :
    applyCols (colsOf σ) (applyCols b y) = applyCols b y := by
  have hkl : (b.take k).length = k := by rw [List.length_take]; omega
  have e : applyCols b y = applyCols (b.take k) y := by
    conv_lhs => rw [← List.take_append_drop k b]
    exact applyCols_append_lt _ _ y (by rw [hkl]; exact hy)
  rw [e, applyCols_map _ (applyCols_xor _)]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_map]
  have hi : i < k := by rw [hkl] at h2; exact h2
  have hbi : (b.take k)[i] = b.getD i 0 := by
    rw [List.getElem_take, getD_eq_get _ (by omega)]
  have hlt : b.getD i 0 < 2 ^ d := by
    rw [getD_eq_get _ (by omega)]
    exact hblt _ (List.getElem_mem _)
  rw [hbi, ← val_eq hσ.1 ⟨_, hlt⟩, hσ.2 i hi hlt]

theorem perm_of_tChk {k : ℕ} {t : List ℕ} (h : tChk d L b k t = true) :
    ∃ σ ∈ Gk d L b k, ∀ x : Fin (2 ^ d), (σ x).1 = applyCols t x.1 := by
  rw [tChk] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, hlt⟩, hfix⟩, hmask⟩, hlab⟩ := h
  have hlt' : ∀ c ∈ t, c < 2 ^ d := fun c hc => by
    have := (allL_iff.1 hlt) c hc
    rwa [Nat.blt_eq] at this
  let f : Fin (2 ^ d) → Fin (2 ^ d) := fun x => ⟨applyCols t x.1, applyCols_lt hlt' x.1⟩
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := surj_of_mask (Nat.eq_of_beq_eq_true hmask) y.1 y.2
    refine ⟨⟨x, hx⟩, Fin.ext ?_⟩
    change applyCols t x = y.1
    rw [← apK_eq]
    exact hxy
  have hbij : Function.Bijective f := ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  refine ⟨Equiv.ofBijective f hbij, ⟨⟨fun a b' c habc => ?_, fun a => ?_⟩, fun i hi hb => ?_⟩,
    fun x => rfl⟩
  · change applyCols t a.1 ^^^ applyCols t b'.1 = applyCols t c.1
    rw [← applyCols_xor, habc]
  · change φL L (applyCols t a.1) = φL L a.1
    rw [φL_eq_iff, ← apK_eq]
    exact beq_iff_eq.1 ((allLt_iff.1 hlab) a.1 a.2)
  · apply Fin.ext
    change applyCols t (b.getD i 0) = b.getD i 0
    rw [← apK_eq]
    exact Nat.eq_of_beq_eq_true ((allLt_iff.1 hfix) i hi)

theorem injective_of_mask (hm : orMask (2 ^ d) (apK b) = 2 ^ 2 ^ d - 1) (hblt : ∀ c ∈ b, c < 2 ^ d) :
    ∀ x < 2 ^ d, ∀ y < 2 ^ d, applyCols b x = applyCols b y → x = y := by
  let f : Fin (2 ^ d) → Fin (2 ^ d) := fun x => ⟨applyCols b x.1, applyCols_lt hblt x.1⟩
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := surj_of_mask hm y.1 y.2
    refine ⟨⟨x, hx⟩, Fin.ext ?_⟩
    change applyCols b x = y.1
    rw [← apK_eq]
    exact hxy
  intro x hx y hy hxy
  have := Finite.injective_iff_surjective.2 hsurj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Fin.ext hxy)
  exact congrArg Fin.val this

theorem card_level (hlen : b.length = d) (hblt : ∀ c ∈ b, c < 2 ^ d)
    (hm : orMask (2 ^ d) (apK b) = 2 ^ 2 ^ d - 1) {k : ℕ} (hk : k < d) {ts : List (List ℕ)}
    (hl : lvlChk d L b k ts = true) :
    Nat.card (Gk d L b k) = ts.length * Nat.card (Gk d L b (k + 1)) := by
  rw [lvlChk, Bool.and_eq_true, eqL_iff] at hl
  obtain ⟨hck, hts⟩ := hl
  have hbk : b.getD k 0 < 2 ^ d := by
    rw [getD_eq_get _ (by omega)]
    exact hblt _ (List.getElem_mem _)
  have hbk' : b.getD k 0 = applyCols b (2 ^ k) := by
    rw [applyCols_pow b k (by omega), getD_eq_get _ (by omega)]
  have hkd : 2 ^ k < 2 ^ d := Nat.pow_lt_pow_right (by norm_num) hk
  set bk : Fin (2 ^ d) := ⟨b.getD k 0, hbk⟩ with hbkdef
  have hinj := injective_of_mask hm hblt
  have hstab : Gk d L b k ⊓ MulAction.stabilizer (Equiv.Perm (Fin (2 ^ d))) bk =
      Gk d L b (k + 1) := by
    ext σ
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    constructor
    · rintro ⟨⟨hσ, hfix⟩, hσk⟩
      refine ⟨hσ, fun i hi h => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hfix i hi h
      · exact hσk
    · rintro ⟨hσ, hfix⟩
      exact ⟨⟨hσ, fun i hi h => hfix i (by omega) h⟩, hfix k (by omega) hbk⟩
  have hnd : (ckL d L b k).Nodup := List.nodup_range.filter _
  rw [card_eq_mul_stab' (Gk d L b k) bk Fin.val Fin.val_injective (ckL d L b k).toFinset ?_ ?_,
    hstab, List.toFinset_card_of_nodup hnd, hck, List.length_map]
  · intro g hg
    rw [Equiv.Perm.smul_def, List.mem_toFinset, ckL, List.mem_filter]
    refine ⟨List.mem_range.2 (g bk).2, allLt_iff.2 fun y hy => ?_⟩
    have hsy : applyCols b y < 2 ^ d := applyCols_lt hblt y
    have hfs := fix_span hlen hblt hk.le hg hy
    rw [apK_eq, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq]
    have hc : (g bk).1 = applyCols (colsOf g) (b.getD k 0) := val_eq hg.1 bk
    constructor
    · cases hb : Nat.beq (g bk).1 (applyCols b y) with
      | false => rfl
      | true =>
        exfalso
        have e := Nat.eq_of_beq_eq_true hb
        have e2 : g bk = g ⟨applyCols b y, hsy⟩ := by
          apply Fin.ext
          rw [e, val_eq hg.1 ⟨applyCols b y, hsy⟩, hfs]
        have e3 := congrArg Fin.val (g.injective e2)
        change b.getD k 0 = applyCols b y at e3
        rw [hbk'] at e3
        have := hinj _ hkd y (lt_trans hy hkd) e3
        omega
    · have hx : b.getD k 0 ^^^ applyCols b y < 2 ^ d := Nat.xor_lt_two_pow hbk hsy
      have e : (g bk).1 ^^^ applyCols b y = (g ⟨_, hx⟩).1 := by
        rw [val_eq hg.1 ⟨_, hx⟩, applyCols_xor, hfs, hc]
      rw [e]
      exact φL_eq_iff.1 (hg.1.2 ⟨_, hx⟩)
  · intro c hc
    rw [List.mem_toFinset, hck] at hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    have htc := (allL_iff.1 hts) j (List.mem_range.2 hj)
    rw [getD_eq_get _ hj] at htc
    obtain ⟨σ, hσ, hσt⟩ := perm_of_tChk htc
    refine ⟨σ, hσ, ?_⟩
    rw [Equiv.Perm.smul_def, hσt, apK_eq]

theorem Gk_zero : Gk d L b 0 = Sig d (φL L) := by
  ext σ
  exact ⟨fun h => h.1, fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩⟩

theorem card_Gk_top (hlen : b.length = d) (hblt : ∀ c ∈ b, c < 2 ^ d)
    (hm : orMask (2 ^ d) (apK b) = 2 ^ 2 ^ d - 1) : Nat.card (Gk d L b d) = 1 := by
  have : Gk d L b d = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun σ hσ => Equiv.ext fun x => Fin.ext ?_
    obtain ⟨y, hy, hyx⟩ := surj_of_mask hm x.1 x.2
    rw [apK_eq] at hyx
    rw [val_eq hσ.1 x, ← hyx, fix_span hlen hblt le_rfl hσ hy, hyx]
    rfl
  rw [this, Subgroup.card_bot]

theorem card_Sig_of_chk {T : List (List (List ℕ))} (h : sigChk d L b T = true) :
    Nat.card (Sig d (φL L)) = ((List.range d).map fun k => (T.getD k []).length).prod := by
  rw [sigChk] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hlen, hblt⟩, hm⟩, hlv⟩ := h
  have hlen' := Nat.eq_of_beq_eq_true hlen
  have hblt' : ∀ c ∈ b, c < 2 ^ d := fun c hc => by
    have := (allL_iff.1 hblt) c hc
    rwa [Nat.blt_eq] at this
  have hm' := Nat.eq_of_beq_eq_true hm
  have key : ∀ n k, k + n = d → Nat.card (Gk d L b k) =
      ((List.range' k n).map fun k => (T.getD k []).length).prod := by
    intro n
    induction n with
    | zero =>
      intro k hk
      rw [Nat.add_zero] at hk
      subst hk
      rw [card_Gk_top hlen' hblt' hm', List.range'_zero, List.map_nil, List.prod_nil]
    | succ n ih =>
      intro k hk
      rw [card_level hlen' hblt' hm' (by omega) ((allL_iff.1 hlv) k (List.mem_range.2 (by omega))),
        ih (k + 1) (by omega), List.range'_succ, List.map_cons, List.prod_cons]
  rw [← Gk_zero (b := b), key d 0 (by omega), List.range_eq_range']

end Chain

end CFSG.KS.S1277Sig

end
