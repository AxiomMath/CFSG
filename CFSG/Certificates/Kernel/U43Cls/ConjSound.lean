module

public import Certificates.Data.Kernel.U43Cls.Defs
public import CFSG.Certificates.Kernel.U43Mod.KTreeSound

public section

namespace CFSG.KS.U43Cls

open CFSG.KC.Enum CFSG.KC.U43Cls CFSG.KS CFSG.KS.U43Mod

variable {n : ℕ}

@[expose] noncomputable def letW (W j : ℕ) : ℕ := fld(W, Nat.mul (nat_lit 5) j, nat_lit 31)

@[expose] noncomputable def wVal (g : ℕ → Equiv.Perm (Fin n)) (W : ℕ) : ℕ → Equiv.Perm (Fin n)
  | 0 => 1
  | j + 1 => wVal g W j * g (letW W j)

@[expose] noncomputable def recW (r : ℕ) : ℕ := fld(r, nat_lit 0, nat_lit 33554431)

@[expose] noncomputable def recLen (r : ℕ) : ℕ := fld(r, nat_lit 25, nat_lit 7)

@[expose] noncomputable def recKind (r : ℕ) : ℕ := fld(r, nat_lit 58, nat_lit 1)

@[expose] noncomputable def cjV (g : ℕ → Equiv.Perm (Fin n)) (A : Equiv.Perm (Fin n)) (r : ℕ) :
    Equiv.Perm (Fin n) :=
  wVal g (recW r) (recLen r) * A * (wVal g (recW r) (recLen r))⁻¹

@[expose] def PairRep (n : ℕ) (u v : ℕ → ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ q (hq : q < n), u q = (σ ⟨q, hq⟩ : ℕ) ∧ v q = (σ⁻¹ ⟨q, hq⟩ : ℕ)

theorem PairRep.inv {u v : ℕ → ℕ} {σ : Equiv.Perm (Fin n)} (h : PairRep n u v σ) :
    PairRep n v u σ⁻¹ := fun q hq => by
  rw [inv_inv]
  exact ⟨(h q hq).2, (h q hq).1⟩

theorem PairRep.comp {u v u' v' : ℕ → ℕ} {σ τ : Equiv.Perm (Fin n)} (h : PairRep n u v σ)
    (h' : PairRep n u' v' τ) : PairRep n (fun q => u (u' q)) (fun q => v' (v q)) (σ * τ) :=
  fun q hq => by
    refine ⟨?_, ?_⟩
    · change u (u' q) = _
      rw [(h' q hq).1, (h _ (Fin.is_lt _)).1, Fin.eta, Equiv.Perm.mul_apply]
    · change v' (v q) = _
      rw [(h q hq).2, (h' _ (Fin.is_lt _)).2, Fin.eta, mul_inv_rev, Equiv.Perm.mul_apply]

theorem fpow_eq {f : ℕ → ℕ} {σ : Equiv.Perm (Fin n)}
    (hf : ∀ q (hq : q < n), f q = (σ ⟨q, hq⟩ : ℕ)) :
    ∀ (o q : ℕ) (hq : q < n), fpow f o q = ((σ ^ o) ⟨q, hq⟩ : ℕ)
  | 0, q, hq => by simp only [pow_zero]; rfl
  | o + 1, q, hq => by
    change strictN (f q) (fpow f o) = _
    rw [strictN_eq, hf q hq, fpow_eq hf o _ (Fin.is_lt _), Fin.eta, pow_succ,
      Equiv.Perm.mul_apply]

variable {G Gi : ℕ → ℕ → ℕ} {g : ℕ → Equiv.Perm (Fin n)}

theorem PairRep.letRep {c : ℕ} (h : PairRep n (G c) (Gi c) (g c)) : LetRep n G Gi g c := h

theorem wP_eq {W : ℕ} : ∀ len : ℕ, (∀ j < len, LetRep n G Gi g (letW W j)) →
    ∀ q (hq : q < n), wP G W len q = (wVal g W len ⟨q, hq⟩ : ℕ) ∧
      wPI Gi W len q = ((wVal g W len)⁻¹ ⟨q, hq⟩ : ℕ)
  | 0, _, q, hq => ⟨rfl, by simp only [wVal, inv_one]; rfl⟩
  | len + 1, h, q, hq => by
    have ih := wP_eq len fun j hj => h j (Nat.lt_succ_of_lt hj)
    have hl := h len (Nat.lt_succ_self len)
    constructor
    · change strictN (G (letW W len) q) (wP G W len) = _
      rw [strictN_eq, (hl q hq).1, (ih _ (Fin.is_lt _)).1, Fin.eta]
      rfl
    · change strictN (wPI Gi W len q) (Gi (letW W len)) = _
      rw [strictN_eq, (ih q hq).2, (hl _ (Fin.is_lt _)).2, Fin.eta]
      change _ = ((wVal g W len * g (letW W len))⁻¹ ⟨q, hq⟩ : ℕ)
      rw [mul_inv_rev, Equiv.Perm.mul_apply]

theorem cjP_eq {W len : ℕ} (hW : ∀ j < len, LetRep n G Gi g (letW W j)) {a : ℕ → ℕ}
    {A : Equiv.Perm (Fin n)} (hA : ∀ q (hq : q < n), a q = (A ⟨q, hq⟩ : ℕ)) (q : ℕ)
    (hq : q < n) :
    cjP G Gi a W len q = ((wVal g W len * A * (wVal g W len)⁻¹) ⟨q, hq⟩ : ℕ) := by
  unfold cjP
  simp only [strictN_eq]
  rw [(wP_eq len hW q hq).2, hA _ (Fin.is_lt _), Fin.eta, (wP_eq len hW _ (Fin.is_lt _)).1,
    Fin.eta]
  simp only [Equiv.Perm.mul_apply]

theorem lettersOK_iff {k W : ℕ} : ∀ len : ℕ, lettersOK k W len = true ↔ ∀ j < len, letW W j < k
  | 0 => by simp [lettersOK]
  | len + 1 => by
    change Bool.rec (motive := fun _ => Bool) false (lettersOK k W len)
      (Nat.blt (letW W len) k) = true ↔ _
    rw [bAnd_iff, lettersOK_iff len, blt_iff]
    constructor
    · rintro ⟨h0, h1⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h1 j hj
      · exact h0
    · intro h
      exact ⟨h len (Nat.lt_succ_self len), fun j hj => h j (Nat.lt_succ_of_lt hj)⟩

theorem wVal_mem {H : Subgroup (Equiv.Perm (Fin n))} {W : ℕ} :
    ∀ len : ℕ, (∀ j < len, g (letW W j) ∈ H) → wVal g W len ∈ H
  | 0, _ => H.one_mem
  | len + 1, h =>
    H.mul_mem (wVal_mem len fun j hj => h j (Nat.lt_succ_of_lt hj)) (h len (Nat.lt_succ_self _))

theorem ncommAt_sound {F Y : Equiv.Perm (Fin n)} {f y yi : ℕ → ℕ}
    (hf : ∀ q (hq : q < n), f q = (F ⟨q, hq⟩ : ℕ)) (hy : ∀ q (hq : q < n), y q = (Y ⟨q, hq⟩ : ℕ))
    (hyi : ∀ q (hq : q < n), yi q = (Y⁻¹ ⟨q, hq⟩ : ℕ)) {p : ℕ} (hp : p < n)
    (h : ncommAt f y yi p = true) : F * (Y * F * Y⁻¹) ≠ Y * F * Y⁻¹ * F := by
  intro e
  unfold ncommAt at h
  simp only [strictB_eq, strictN_eq] at h
  have h1 : f (y (f (yi p))) = ((F * (Y * F * Y⁻¹)) ⟨p, hp⟩ : ℕ) := by
    rw [hyi p hp, hf _ (Fin.is_lt _), Fin.eta, hy _ (Fin.is_lt _), Fin.eta, hf _ (Fin.is_lt _),
      Fin.eta]
    simp only [Equiv.Perm.mul_apply]
  have h2 : y (f (yi (f p))) = ((Y * F * Y⁻¹ * F) ⟨p, hp⟩ : ℕ) := by
    rw [hf p hp, hyi _ (Fin.is_lt _), Fin.eta, hf _ (Fin.is_lt _), Fin.eta, hy _ (Fin.is_lt _),
      Fin.eta]
    simp only [Equiv.Perm.mul_apply]
  rw [h1, h2, e, Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem nIf_cases (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = t ∨ Bool.rec (motive := fun _ => ℕ) e t c = e := by
  cases c
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem key_eq (r : ℕ) : fld(r, 28, 1073741823) =
    fld(r, 28, 1023) + 1024 * fld(r, 38, 1023) + 1048576 * fld(r, 48, 1023) := by
  have e30 : (1073741823 : ℕ) = 2 ^ 30 - 1 := by norm_num
  have e10 : (1023 : ℕ) = 2 ^ 10 - 1 := by norm_num
  rw [e30, e10, fld_eq', fld_eq', fld_eq', fld_eq']
  have q38 : (2 : ℕ) ^ 38 = 2 ^ 28 * 1024 := by norm_num
  have q48 : (2 : ℕ) ^ 48 = 2 ^ 28 * 1048576 := by norm_num
  have p10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
  have p30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  rw [q38, q48, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, p10, p30]
  generalize r / 2 ^ 28 = x
  omega

theorem cRec_spec {R : ℕ → ℕ} {a : ℕ → ℕ} {Y Yi : ℕ → ℕ → ℕ} {k p₀ p₁ p₂ i : ℕ}
    (h : cRec R G Gi a Y Yi k p₀ p₁ p₂ i = true) :
    lettersOK k (recW (R i)) (recLen (R i)) = true ∧
    cjP G Gi a (recW (R i)) (recLen (R i)) p₀ = fld(R i, 28, 1023) ∧
    cjP G Gi a (recW (R i)) (recLen (R i)) p₁ = fld(R i, 38, 1023) ∧
    cjP G Gi a (recW (R i)) (recLen (R i)) p₂ = fld(R i, 48, 1023) ∧
    (i = 0 ∨ fld(R (i - 1), 28, 1073741823) < fld(R i, 28, 1073741823)) ∧
    ncommAt (cjP G Gi a (recW (R i)) (recLen (R i))) (Y (recKind (R i))) (Yi (recKind (R i)))
      (Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ) p₂ p₁ (Nat.beq fld(R i, 59, 3) 1)) p₀
        (Nat.beq fld(R i, 59, 3) 0)) = true := by
  unfold cRec at h
  simp only [strictB_eq] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h5, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h6⟩ := (bAnd_iff _ _).1 h
  refine ⟨h1, beq_iff.1 h2, beq_iff.1 h3, beq_iff.1 h4, ?_, h6⟩
  obtain ⟨h5a, h5b⟩ := bIf_spec h5
  cases hi : Nat.beq i (nat_lit 0)
  · exact Or.inr (blt_iff.1 (h5b hi))
  · exact Or.inl (Nat.eq_of_beq_eq_true hi)

theorem cBlk_spec {R : ℕ → ℕ} {a : ℕ → ℕ} {Y Yi : ℕ → ℕ → ℕ} {k p₀ p₁ p₂ N : ℕ}
    (h : ∀ c, 64 * c < N → cBlk R G Gi a Y Yi k p₀ p₁ p₂ N c = true) :
    ∀ i < N, cRec R G Gi a Y Yi k p₀ p₁ p₂ i = true := by
  intro i hi
  have hc := h (i / 64) (by omega)
  unfold cBlk at hc
  rw [strictB_eq] at hc
  have hd : i = Nat.add (Nat.mul 64 (i / 64)) (i % 64) := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  have hlen : i % 64 < Bool.rec (motive := fun _ => ℕ) 64 (Nat.sub N (Nat.mul 64 (i / 64)))
      (Nat.blt (Nat.sub N (Nat.mul 64 (i / 64))) 64) := by
    cases hb : Nat.blt (Nat.sub N (Nat.mul 64 (i / 64))) 64
    · exact Nat.mod_lt i (by norm_num)
    · change i % 64 < N - 64 * (i / 64)
      omega
  rw [hd]
  exact allBlk_spec hc _ hlen

variable {R : ℕ → ℕ} {a : ℕ → ℕ} {Y Yi : ℕ → ℕ → ℕ} {k p₀ p₁ p₂ N : ℕ}
  {A : Equiv.Perm (Fin n)} {y : ℕ → Equiv.Perm (Fin n)}

theorem cRec_sound (hG : ∀ c < k, LetRep n G Gi g c)
    (hA : ∀ q (hq : q < n), a q = (A ⟨q, hq⟩ : ℕ)) (hY : ∀ s < 2, LetRep n Y Yi y s)
    (h₀ : p₀ < n) (h₁ : p₁ < n) (h₂ : p₂ < n)
    (h : ∀ i < N, cRec R G Gi a Y Yi k p₀ p₁ p₂ i = true) :
    (∀ i < N, ∀ H : Subgroup (Equiv.Perm (Fin n)), (∀ c < k, g c ∈ H) →
      ∃ w ∈ H, cjV g A (R i) = w * A * w⁻¹) ∧
    (∀ i < N, ∀ i' < N, cjV g A (R i) = cjV g A (R i') → i = i') ∧
    (∀ i < N, ∃ s < 2, cjV g A (R i) * (y s * cjV g A (R i) * (y s)⁻¹) ≠
      y s * cjV g A (R i) * (y s)⁻¹ * cjV g A (R i)) := by
  have hL : ∀ i < N, ∀ j < recLen (R i), letW (recW (R i)) j < k := fun i hi =>
    (lettersOK_iff _).1 (cRec_spec (h i hi)).1
  have hW : ∀ i < N, ∀ j < recLen (R i), LetRep n G Gi g (letW (recW (R i)) j) :=
    fun i hi j hj => hG _ (hL i hi j hj)
  have hF : ∀ i < N, ∀ q (hq : q < n),
      cjP G Gi a (recW (R i)) (recLen (R i)) q = (cjV g A (R i) ⟨q, hq⟩ : ℕ) :=
    fun i hi => cjP_eq (hW i hi) hA
  refine ⟨fun i hi H hH => ⟨wVal g (recW (R i)) (recLen (R i)),
    wVal_mem _ fun j hj => hH _ (hL i hi j hj), rfl⟩, ?_, ?_⟩
  ·
    have hkey : ∀ i < N, fld(R i, 28, 1073741823) = (cjV g A (R i) ⟨p₀, h₀⟩ : ℕ) +
        1024 * (cjV g A (R i) ⟨p₁, h₁⟩ : ℕ) + 1048576 * (cjV g A (R i) ⟨p₂, h₂⟩ : ℕ) := by
      intro i hi
      obtain ⟨-, k0, k1, k2, -⟩ := cRec_spec (h i hi)
      rw [key_eq, ← k0, ← k1, ← k2, hF i hi p₀ h₀, hF i hi p₁ h₁, hF i hi p₂ h₂]
    have hinc : ∀ i i', i < i' → i' < N →
        fld(R i, 28, 1073741823) < fld(R i', 28, 1073741823) := by
      intro i i' hii' hi'
      induction i' with
      | zero => omega
      | succ i' ih =>
        rcases (cRec_spec (h (i' + 1) hi')).2.2.2.2.1 with h1 | h1
        · omega
        rw [Nat.add_sub_cancel] at h1
        rcases Nat.lt_succ_iff_lt_or_eq.1 hii' with h2 | rfl
        · exact (ih h2 (by omega)).trans h1
        · exact h1
    have key : ∀ i i', i < i' → i' < N → cjV g A (R i) ≠ cjV g A (R i') := by
      intro i i' hii' hi' he
      have h1 := hinc i i' hii' hi'
      rw [hkey i (by omega), hkey i' hi', he] at h1
      exact lt_irrefl _ h1
    intro i hi i' hi' he
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · exact absurd he (key i i' hlt hi')
    · exact heq
    · exact absurd he.symm (key i' i hgt hi)
  ·
    intro i hi
    obtain ⟨-, -, -, -, -, hn⟩ := cRec_spec (h i hi)
    have hs : recKind (R i) < 2 := by
      change Nat.shiftRight (R i) 58 &&& 1 < 2
      exact Nat.lt_succ_of_le Nat.and_le_right
    refine ⟨_, hs, ncommAt_sound (hF i hi) (fun q hq => (hY _ hs q hq).1)
      (fun q hq => (hY _ hs q hq).2) ?_ hn⟩
    rcases nIf_cases (Nat.beq fld(R i, 59, 3) 0) p₀
      (Bool.rec (motive := fun _ => ℕ) p₂ p₁ (Nat.beq fld(R i, 59, 3) 1)) with e | e <;> rw [e]
    · exact h₀
    · rcases nIf_cases (Nat.beq fld(R i, 59, 3) 1) p₁ p₂ with e' | e' <;> rw [e']
      · exact h₁
      · exact h₂

end CFSG.KS.U43Cls

end
