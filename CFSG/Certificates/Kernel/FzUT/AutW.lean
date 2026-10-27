module

public import Certificates.Data.Kernel.FzUT.AutW
public import CFSG.Certificates.Kernel.FzUT.Shape
public import CFSG.Certificates.Kernel.FzUT.BU

public section

namespace CFSG.KC.FzUT

open CFSG.OddStandard.SmallF3.FritzII

@[expose] def vdec (n : Nat) : FzV :=
  (((n % 2 : ℕ) : ZMod 2), ((n / 2 % 2 : ℕ) : ZMod 2), ((n / 4 % 2 : ℕ) : ZMod 2))

theorem vcode_vdec : ∀ n : Fin 8, vcode (vdec n) = n := by decide +kernel

theorem vcode_W : ∀ v : FzV, (vcode v &&& 6 = 0 ↔ v.2.1 = 0 ∧ v.2.2 = 0) := by decide +kernel

@[expose] def decE (c : Nat) : FzElt := (dec (c % 64), vdec (c / 64))

theorem encE_decE {c : Nat} (hc : c < 512) : encE (decE c) = c := by
  have h1 : enc (dec (c % 64)) = c % 64 := enc_dec ⟨c % 64, Nat.mod_lt _ (by norm_num)⟩
  have h2 : vcode (vdec (c / 64)) = c / 64 := vcode_vdec ⟨c / 64, by omega⟩
  change enc (dec (c % 64)) + 64 * vcode (vdec (c / 64)) = c
  rw [h1, h2]
  omega

theorem card_codes (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range 512).filter P).card = (Finset.univ.filter fun x : FzElt => P (encE x)).card := by
  symm
  apply Finset.card_bij (fun x _ => encE x)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨encE_lt x, hx⟩
  · intro x _ y _ h
    exact encE_injective h
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_range] at hc
    refine ⟨decE c, ?_, encE_decE hc.1⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [encE_decE hc.1]
    exact hc.2

@[expose] def IsAutC (t s l : MulAut FzUT) (α : FzElt ≃ FzElt) : Prop :=
  ∀ x y, α (fzMulC t s l x y) = fzMulC t s l (α x) (α y)

@[expose] def InvL (t s l : MulAut FzUT) (Λ : ℕ → ℕ) : Prop :=
  ∀ α, IsAutC t s l α → ∀ x, Λ (encE (α x)) = Λ (encE x)

variable {t s l : MulAut FzUT}

theorem emPT_eq {AT : ℕ} (hA : atOK (gc t) (gc s) (gc l) AT = true) (x y : FzElt) :
    emPT AT (encE x) (encE y) = encE (fzMulC t s l x y) := by
  have hy := enc_lt y.1
  have hi : 64 * vcode x.2 + enc y.1 < 512 := by
    have := vcode_lt x.2
    omega
  have hA' := (beq_iff _ _).1 ((allN_iff _ _).1 hA _ hi)
  have h1 : (64 * vcode x.2 + enc y.1) >>> 6 = vcode x.2 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have h2 : (64 * vcode x.2 + enc y.1) &&& 63 = enc y.1 := by
    change _ &&& (2 ^ 6 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [h1, h2] at hA'
  rw [← emP_eq]
  unfold emPT emP
  rw [encE_fst, encE_snd, encE_fst, encE_snd, hA']

theorem fzMulC_one (x : FzElt) : fzMulC t s l x fzOneC = x := by
  simp [fzMulC, fzOneC, fzAct_one]

theorem one_fzMulC (x : FzElt) : fzMulC t s l fzOneC x = x := by
  simp [fzMulC, fzOneC, fzAct_zero]

theorem aut_one {α : FzElt ≃ FzElt} (hα : IsAutC t s l α) : α fzOneC = fzOneC := by
  have h := hα fzOneC (α.symm fzOneC)
  rw [one_fzMulC, Equiv.apply_symm_apply, fzMulC_one] at h
  exact h.symm

theorem card_reindex (α : FzElt ≃ FzElt) (P Q : FzElt → Prop) [DecidablePred P]
    [DecidablePred Q] (h : ∀ y, Q (α y) ↔ P y) :
    (Finset.univ.filter Q).card = (Finset.univ.filter P).card :=
  (Finset.card_equiv α fun y => by simp [h]).symm

@[expose] noncomputable def nRoots (t s l : MulAut FzUT) (x : FzElt) : ℕ :=
  (Finset.univ.filter fun y => fzMulC t s l y y = x).card

theorem nRoots_aut {α : FzElt ≃ FzElt} (hα : IsAutC t s l α) (x : FzElt) :
    nRoots t s l (α x) = nRoots t s l x :=
  card_reindex α _ _ fun y => by rw [← hα, α.injective.eq_iff]

theorem beq_one_aut {α : FzElt ≃ FzElt} (hα : IsAutC t s l α) (z : FzElt) :
    Nat.beq (encE (α z)) 0 = Nat.beq (encE z) 0 := by
  have e : α z = fzOneC ↔ z = fzOneC :=
    ⟨fun e => α.injective (e.trans (aut_one hα).symm), fun e => e ▸ aut_one hα⟩
  rw [Bool.eq_iff_iff, beq_iff, beq_iff, ← encE_one, encE_injective.eq_iff,
    encE_injective.eq_iff]
  exact e

theorem lt_of_succ {g : ℕ → ℕ} {n : ℕ} (h : ∀ j, j + 1 < n → g j < g (j + 1)) {i j : ℕ}
    (hij : i < j) (hj : j < n) : g i < g j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
    · exact (ih h' (by omega)).trans (h j hj)
    · exact h i hj

theorem injOn_of_succ {g : ℕ → ℕ} {n : ℕ} (h : ∀ j, j + 1 < n → g j < g (j + 1)) :
    Set.InjOn g (Finset.range n) := by
  intro i hi j hj e
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases lt_trichotomy i j with h' | h' | h'
  · exact absurd e (lt_of_succ h h' hj).ne
  · exact h'
  · exact absurd e (lt_of_succ h h' hi).ne'

theorem rlA_lt (RL j : ℕ) : rlA RL j < 512 := fldN_lt RL 9 j

theorem rfA_eq (RO c : ℕ) : rfA RO c = roA RO (c + 1) - roA RO c := rfl

theorem roots_count {f : ℕ → ℕ} (hf : ∀ y < 512, f y < 512) {RL RO : ℕ}
    (h0 : roA RO 0 = 0) (h512 : roA RO 512 = 512)
    (hmono : ∀ c < 512, roA RO c ≤ roA RO (c + 1))
    (hsq : ∀ c < 512, ∀ j < rfA RO c, f (rlA RL (roA RO c + j)) = c)
    (hinc : ∀ c < 512, ∀ j, j + 1 < rfA RO c →
      rlA RL (roA RO c + j) < rlA RL (roA RO c + (j + 1))) :
    ∀ c < 512, rfA RO c = ((Finset.range 512).filter fun y => f y = c).card := by
  have hle : ∀ c ∈ Finset.range 512,
      rfA RO c ≤ ((Finset.range 512).filter fun y => f y = c).card := by
    intro c hc
    rw [Finset.mem_range] at hc
    have := Finset.card_le_card_of_injOn (fun j => rlA RL (roA RO c + j))
      (s := Finset.range (rfA RO c)) (t := (Finset.range 512).filter fun y => f y = c)
      (fun j hj => by
        rw [Finset.mem_coe, Finset.mem_range] at hj
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        exact ⟨rlA_lt _ _, hsq c hc j hj⟩)
      (injOn_of_succ (g := fun j => rlA RL (roA RO c + j)) (hinc c hc))
    rwa [Finset.card_range] at this
  have hsum1 : ∑ c ∈ Finset.range 512, rfA RO c = 512 := by
    have : ∀ n ≤ 512, ∑ c ∈ Finset.range n, rfA RO c = roA RO n := by
      intro n hn
      induction n with
      | zero => simp [h0]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih (by omega), rfA_eq]
        have := hmono n (by omega)
        omega
    rw [this 512 le_rfl, h512]
  have hsum2 : ∑ c ∈ Finset.range 512, ((Finset.range 512).filter fun y => f y = c).card = 512 := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.range 512)
      (t := Finset.range 512) (fun y hy => Finset.mem_range.2 (hf y (Finset.mem_range.1 hy)))]
    exact Finset.card_range 512
  intro c hc
  exact (Finset.sum_eq_sum_iff_of_le hle).1 (hsum1.trans hsum2.symm) c (Finset.mem_range.2 hc)

theorem rootsOK_spec {AT RL RO : ℕ} (h : rootsOK AT RL RO = true) :
    roA RO 0 = 0 ∧ roA RO 512 = 512 ∧ ∀ c < 512, roA RO c ≤ roA RO (c + 1) ∧
      ∀ j < rfA RO c, emPT AT (rlA RL (roA RO c + j)) (rlA RL (roA RO c + j)) = c ∧
        (j + 1 < rfA RO c → rlA RL (roA RO c + j) < rlA RL (roA RO c + (j + 1))) := by
  unfold rootsOK at h
  obtain ⟨h0, h⟩ := (band_iff _ _).1 h
  obtain ⟨h1, h⟩ := (band_iff _ _).1 h
  refine ⟨(beq_iff _ _).1 h0, (beq_iff _ _).1 h1, fun c hc => ?_⟩
  obtain ⟨hm, hj⟩ := (band_iff _ _).1 ((allN_iff _ _).1 h c hc)
  refine ⟨Nat.le_of_ble_eq_true hm, fun j hj' => ?_⟩
  have := (allN_iff _ _).1 hj j hj'
  rw [sb_eq] at this
  obtain ⟨e, i⟩ := (band_iff _ _).1 this
  refine ⟨(beq_iff _ _).1 e, fun hlt => ?_⟩
  have hb := (bimp_iff _ _).1 i (by simpa [Nat.blt_eq] using hlt)
  simpa [Nat.blt_eq] using hb

theorem nRoots_code {AT RL RO : ℕ} (hA : atOK (gc t) (gc s) (gc l) AT = true)
    (h : rootsOK AT RL RO = true) (x : FzElt) : rfA RO (encE x) = nRoots t s l x := by
  obtain ⟨h0, h1, h⟩ := rootsOK_spec h
  have hf : ∀ y < 512, emPT AT y y < 512 := fun y hy => by
    rw [← encE_decE hy, emPT_eq hA]
    exact encE_lt _
  rw [roots_count hf h0 h1 (fun c hc => (h c hc).1) (fun c hc j hj => ((h c hc).2 j hj).1)
    (fun c hc j hj => ((h c hc).2 j (by omega)).2 hj) _ (encE_lt x), card_codes]
  exact congrArg Finset.card
    (Finset.filter_congr fun y _ => by rw [emPT_eq hA, encE_injective.eq_iff])

theorem lab0_inv {AT RL RO LT : ℕ} (hA : atOK (gc t) (gc s) (gc l) AT = true)
    (hr : rootsOK AT RL RO = true) (h : lab0OK AT RO LT = true) : InvL t s l (ltA LT) := by
  have key : ∀ x, ltA LT (encE x) = lab0F RO (encE x) (encE (fzMulC t s l x x))
      (encE (fzMulC t s l (fzMulC t s l x x) (fzMulC t s l x x))) := by
    intro x
    have := (allN_iff _ _).1 h (encE x) (encE_lt x)
    rw [sb_eq, sb_eq, emPT_eq hA, emPT_eq hA] at this
    exact (beq_iff _ _).1 this
  intro α hα x
  rw [key, key, ← hα, ← hα]
  simp only [lab0F, nRoots_code hA hr, nRoots_aut hα, beq_one_aut hα]

theorem count_list {Λ : ℕ → ℕ} {u n : ℕ} {g : ℕ → ℕ} (hg : ∀ j, g j < 512)
    (hn : ((Finset.range 512).filter fun y => Λ y = u).card = n)
    (hu : ∀ j < n, Λ (g j) = u) (hinc : ∀ j, j + 1 < n → g j < g (j + 1)) (p : ℕ → Prop)
    [DecidablePred p] :
    ((Finset.range 512).filter fun y => Λ y = u ∧ p y).card =
      ((Finset.range n).filter fun j => p (g j)).card := by
  have hinj := injOn_of_succ hinc
  have himg : (Finset.range n).image g = (Finset.range 512).filter fun y => Λ y = u := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hg j), hu j (Finset.mem_range.1 hj)⟩
    · rw [hn, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [← Finset.filter_filter, ← himg, Finset.filter_image,
    Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))]

theorem round_inv {AT LT LT' u n UL : ℕ} (hA : atOK (gc t) (gc s) (gc l) AT = true)
    (hL : InvL t s l (ltA LT)) (h : roundOK AT LT LT' u n UL = true) :
    InvL t s l (ltA LT') := by
  unfold roundOK at h
  obtain ⟨hn, h⟩ := (band_iff _ _).1 h
  obtain ⟨hl, h⟩ := (band_iff _ _).1 h
  rw [beq_iff, cntB_eq] at hn
  have hn' : ((Finset.range 512).filter fun y => ltA LT y = u).card = n := by
    rw [← hn]
    exact congrArg Finset.card (Finset.filter_congr fun y _ => (beq_iff _ _).symm)
  have hu : ∀ j < n, ltA LT (rlA UL j) = u := fun j hj =>
    (beq_iff _ _).1 ((band_iff _ _).1 ((allN_iff _ _).1 hl j hj)).1
  have hinc : ∀ j, j + 1 < n → rlA UL j < rlA UL (j + 1) := fun j hj => by
    have := (bimp_iff _ _).1 ((band_iff _ _).1 ((allN_iff _ _).1 hl j (by omega))).2
      (by simpa [Nat.blt_eq] using hj)
    simpa [Nat.blt_eq] using this
  have key : ∀ x, ltA LT' (encE x) = 16 * ltA LT (encE x) +
      (Finset.univ.filter fun y : FzElt =>
        ltA LT (encE y) = u ∧ fzMulC t s l x y = fzMulC t s l y x).card := by
    intro x
    rw [(beq_iff _ _).1 ((allN_iff _ _).1 h (encE x) (encE_lt x)), cntB_eq]
    have hc := count_list (rlA_lt UL) hn' hu hinc
      (fun y => cmT AT (encE x) y = true)
    rw [← hc, card_codes]
    exact congrArg (fun k => 16 * ltA LT (encE x) + k) (congrArg Finset.card
      (Finset.filter_congr fun y _ => by
        unfold cmT
        rw [emPT_eq hA, emPT_eq hA, beq_iff, encE_injective.eq_iff]))
  intro α hα x
  rw [key, key, hL α hα x]
  exact congrArg (fun k => 16 * ltA LT (encE x) + k)
    (card_reindex α _ _ fun y => by rw [hL α hα y, ← hα, ← hα, α.injective.eq_iff])

theorem inWc_iff (x : FzElt) : inWc (gc t) (encE x) = true ↔ fzInW t x := by
  unfold inWc fzInW
  rw [band_iff, beq_iff, beq_iff, encE_fst, evD_gc, enc_injective.eq_iff, encE_snd, vcode_W]

theorem autW_of_final {LT LW nw : ℕ} (hL : InvL t s l (ltA LT))
    (h : finalOK (gc t) LT LW nw = true) : FzAutW t s l := by
  have key : ∀ x, fzInW t x ↔
      anyN nw (fun i => Nat.beq (ltA LW i) (ltA LT (encE x))) = true := by
    intro x
    have := (allN_iff _ _).1 h (encE x) (encE_lt x)
    rw [sb_eq] at this
    rw [← inWc_iff]
    cases hw : inWc (gc t) (encE x)
    · rw [hw] at this
      change bnot _ = true at this
      rw [bnot_iff] at this
      rw [this]
    · rw [hw] at this
      exact ⟨fun _ => this, fun _ => rfl⟩
  intro α hα x
  rw [key, key, hL α hα x]

end CFSG.KC.FzUT
