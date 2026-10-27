module

public import CFSG.LieType.SpecialLinear.ExteriorModel.FixedLine
public import CFSG.LieType.Universal.Unitary.CurtisDatum
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
public import CFSG.LieType.SpecialLinear.ExteriorModel.Extraction

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.LieType.SpecialLinear.ExteriorModel CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]

@[expose] noncomputable def suSL (σ : F ≃+* F) (n : ℕ) : SU σ n →* SpecialLinearGroup (Fin n) F where
  toFun A := ⟨(A : GL (Fin n) F), (mem_SU.mp A.2).1⟩
  map_one' := by ext; rfl
  map_mul' := by intro A B; ext; rfl

omit [Finite F] [CharP F 2] in
theorem coe_suSL (σ : F ≃+* F) (n : ℕ) (g : SU σ n) :
    (suSL σ n g : Matrix (Fin n) (Fin n) F) = SUExtras.mat σ n g := rfl

variable {k : Type} [Field k]

@[expose] noncomputable def suFrob (φ₀ : F →+* k) (f : ℕ) : Fin f → F →+* k :=
  fun r => φ₀.comp (iterateFrobenius F 2 r)

@[expose] noncomputable def suTwist (φ₀ : F →+* k) (f n : ℕ) :
    SU (unitaryInvolution F 2 f) n →* (Fin f → SpecialLinearGroup (Fin n) k) :=
  (twistHom (suFrob φ₀ f)).comp (suSL _ n)

theorem coe_suTwist_apply (φ₀ : F →+* k) (n : ℕ) (g : SU (unitaryInvolution F 2 f) n) (r : Fin f) :
    (suTwist φ₀ f n g r : Matrix (Fin n) (Fin n) k) = (SUExtras.mat _ n g).map (suFrob φ₀ f r) := rfl

omit [Finite F] in
theorem suFrob_apply (φ₀ : F →+* k) (r : Fin f) (x : F) :
    suFrob φ₀ f r x = φ₀ x ^ 2 ^ (r : ℕ) := by
  simp [suFrob, iterateFrobenius_def, map_pow]

theorem suFrob_apply_unitaryInvolution (_hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k)
    (r : Fin f) (t : F) :
    suFrob φ₀ f r (unitaryInvolution F 2 f t) = φ₀ t ^ 2 ^ (f + (r : ℕ)) := by
  rw [unitaryInvolution_apply, suFrob_apply, map_pow, ← pow_mul, ← pow_add]

theorem bFirst_suTwist_mulVec_homComp_mem_bRad [CharP k 2] {n : ℕ}
    (ε : Fin f → Finset (Fin n)) (φ₀ : F →+* k) {w : BIdx ε → k}
    (hU : ∀ g : SU (unitaryInvolution F 2 f) n, (∀ a b, b < a → SUExtras.mat _ n g a b = 0) →
      (∀ a, SUExtras.mat _ n g a a = 1) →
      bMat ε (fun r => (suTwist φ₀ f n g r : Matrix (Fin n) (Fin n) k)) *ᵥ w - w ∈ bRad ε)
    {g : SU (unitaryInvolution F 2 f) n}
    (hg : ∀ a b, b < a → SUExtras.mat _ n g a b = 0)
    (hg1 : ∀ a, SUExtras.mat _ n g a a = 1)
    (e : ℤ) (htop : ∀ e', e < e' → homComp (fun s : BIdx ε => (kdeg s : ℤ)) e' w ∈ bRad ε) :
    bFirst ε (fun r => (suTwist φ₀ f n g r : Matrix (Fin n) (Fin n) k)) *ᵥ
      homComp (fun s : BIdx ε => (kdeg s : ℤ)) e w ∈ bRad ε := by
  refine bFirst_mulVec_homComp_mem_bRad ε (h := fun r => suTwist φ₀ f n g r) ?_ ?_
    (hU g hg hg1) e htop
  · intro r a b hab
    rw [coe_suTwist_apply, Matrix.map_apply, hg a b hab, map_zero]
  · intro r a
    rw [coe_suTwist_apply, Matrix.map_apply, hg1 a, map_one]

theorem bFirst_eq_sum_two [CharP k 2] {n : ℕ} (ε : Fin f → Finset (Fin n))
    (G : Fin f → Matrix (Fin n) (Fin n) k) {a₁ a₂ b₁ b₂ : Fin n}
    (hb₁ : (b₁ : ℕ) = a₁ + 1) (hb₂ : (b₂ : ℕ) = a₂ + 1) (hne : a₁ ≠ a₂)
    (c₁ c₂ : Fin f → k)
    (hG : ∀ (r : Fin f) (a b : Fin n), (b : ℕ) = a + 1 →
      G r a b = if a = a₁ then c₁ r else if a = a₂ then c₂ r else 0) :
    bFirst ε G = ∑ r, (c₁ r • bDer ε (r, a₁, b₁) + c₂ r • bDer ε (r, a₂, b₂)) := by
  simp only [bFirst]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hinner : ∀ a : Fin n,
      (∑ b : Fin n, if (b : ℕ) = a + 1 then G r a b • bDer ε (r, a, b)
        else (0 : Matrix (BIdx ε) (BIdx ε) k)) =
        if a = a₁ then c₁ r • bDer ε (r, a₁, b₁)
        else if a = a₂ then c₂ r • bDer ε (r, a₂, b₂)
        else (0 : Matrix (BIdx ε) (BIdx ε) k) := by
    intro a
    by_cases ha₁ : a = a₁
    · subst ha₁
      rw [if_pos rfl]
      have hcond : ∀ b : Fin n, ((b : ℕ) = a + 1) ↔ b = b₁ := by
        intro b
        exact ⟨fun hb => Fin.ext (by rw [hb, hb₁]), fun hb => by rw [hb, hb₁]⟩
      rw [show (∑ b : Fin n, if (b : ℕ) = a + 1 then G r a b • bDer ε (r, a, b)
            else (0 : Matrix (BIdx ε) (BIdx ε) k))
          = ∑ b : Fin n, if b = b₁ then G r a b • bDer ε (r, a, b)
            else (0 : Matrix (BIdx ε) (BIdx ε) k) from by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hcond b]]
      rw [Fintype.sum_ite_eq', hG r a b₁ hb₁, if_pos rfl]
    · by_cases ha₂ : a = a₂
      · subst ha₂
        rw [if_neg ha₁, if_pos rfl]
        have hcond : ∀ b : Fin n, ((b : ℕ) = a + 1) ↔ b = b₂ := by
          intro b
          exact ⟨fun hb => Fin.ext (by rw [hb, hb₂]), fun hb => by rw [hb, hb₂]⟩
        rw [show (∑ b : Fin n, if (b : ℕ) = a + 1 then G r a b • bDer ε (r, a, b)
              else (0 : Matrix (BIdx ε) (BIdx ε) k))
            = ∑ b : Fin n, if b = b₂ then G r a b • bDer ε (r, a, b)
              else (0 : Matrix (BIdx ε) (BIdx ε) k) from by
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [hcond b]]
        rw [Fintype.sum_ite_eq', hG r a b₂ hb₂, if_neg ha₁, if_pos rfl]
      · rw [if_neg ha₁, if_neg ha₂]
        refine Finset.sum_eq_zero fun b _ => ?_
        by_cases hb : (b : ℕ) = a + 1
        · rw [if_pos hb, hG r a b hb, if_neg ha₁, if_neg ha₂]
          simp
        · rw [if_neg hb]
  calc ∑ a : Fin n, (∑ b : Fin n,
        if (b : ℕ) = a + 1 then G r a b • bDer ε (r, a, b)
        else (0 : Matrix (BIdx ε) (BIdx ε) k))
      = ∑ a : Fin n, (if a = a₁ then c₁ r • bDer ε (r, a₁, b₁)
          else if a = a₂ then c₂ r • bDer ε (r, a₂, b₂)
          else (0 : Matrix (BIdx ε) (BIdx ε) k)) :=
        Finset.sum_congr rfl fun a _ => hinner a
    _ = c₁ r • bDer ε (r, a₁, b₁) + c₂ r • bDer ε (r, a₂, b₂) := by
        have hsplit : (∑ a : Fin n, (if a = a₁ then c₁ r • bDer ε (r, a₁, b₁)
              else if a = a₂ then c₂ r • bDer ε (r, a₂, b₂)
              else (0 : Matrix (BIdx ε) (BIdx ε) k)))
            = (∑ a : Fin n, (if a = a₁ then c₁ r • bDer ε (r, a₁, b₁)
                else (0 : Matrix (BIdx ε) (BIdx ε) k))) +
              ∑ a : Fin n, (if a = a₂ then c₂ r • bDer ε (r, a₂, b₂)
                else (0 : Matrix (BIdx ε) (BIdx ε) k)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          by_cases h₁ : a = a₁
          · subst h₁
            simp [hne]
          · by_cases h₂ : a = a₂
            · subst h₂
              simp [h₁]
            · simp [h₁, h₂]
        rw [hsplit, Fintype.sum_ite_eq', Fintype.sum_ite_eq']

theorem bFirst_eq_sum_one [CharP k 2] {n : ℕ} (ε : Fin f → Finset (Fin n))
    (G : Fin f → Matrix (Fin n) (Fin n) k) {a₁ b₁ : Fin n}
    (hb₁ : (b₁ : ℕ) = a₁ + 1) (c₁ : Fin f → k)
    (hG : ∀ (r : Fin f) (a b : Fin n), (b : ℕ) = a + 1 →
      G r a b = if a = a₁ then c₁ r else 0) :
    bFirst ε G = ∑ r, c₁ r • bDer ε (r, a₁, b₁) := by
  simp only [bFirst]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hinner : ∀ a : Fin n,
      (∑ b : Fin n, if (b : ℕ) = a + 1 then G r a b • bDer ε (r, a, b)
        else (0 : Matrix (BIdx ε) (BIdx ε) k)) =
        if a = a₁ then c₁ r • bDer ε (r, a₁, b₁)
        else (0 : Matrix (BIdx ε) (BIdx ε) k) := by
    intro a
    by_cases ha : a = a₁
    · subst ha
      rw [if_pos rfl]
      have hcond : ∀ b : Fin n, ((b : ℕ) = a + 1) ↔ b = b₁ := by
        intro b
        exact ⟨fun hb => Fin.ext (by rw [hb, hb₁]), fun hb => by rw [hb, hb₁]⟩
      rw [show (∑ b : Fin n, if (b : ℕ) = a + 1 then G r a b • bDer ε (r, a, b)
            else (0 : Matrix (BIdx ε) (BIdx ε) k))
          = ∑ b : Fin n, if b = b₁ then G r a b • bDer ε (r, a, b)
            else (0 : Matrix (BIdx ε) (BIdx ε) k) from by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hcond b]]
      rw [Fintype.sum_ite_eq', hG r a b₁ hb₁, if_pos rfl]
    · rw [if_neg ha]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : (b : ℕ) = a + 1
      · rw [if_pos hb, hG r a b hb, if_neg ha]
        simp
      · rw [if_neg hb]
  calc ∑ a : Fin n, (∑ b : Fin n, if (b : ℕ) = a + 1 then G r a b • bDer ε (r, a, b)
        else (0 : Matrix (BIdx ε) (BIdx ε) k))
      = ∑ a : Fin n, (if a = a₁ then c₁ r • bDer ε (r, a₁, b₁)
          else (0 : Matrix (BIdx ε) (BIdx ε) k)) :=
        Finset.sum_congr rfl fun a _ => hinner a
    _ = c₁ r • bDer ε (r, a₁, b₁) := by rw [Fintype.sum_ite_eq']

theorem bFirst_mulVec_eq_sum_one [CharP k 2] {n : ℕ} (ε : Fin f → Finset (Fin n))
    (G : Fin f → Matrix (Fin n) (Fin n) k) {a₁ b₁ : Fin n}
    (hb₁ : (b₁ : ℕ) = a₁ + 1) (c₁ : Fin f → k)
    (hG : ∀ (r : Fin f) (a b : Fin n), (b : ℕ) = a + 1 →
      G r a b = if a = a₁ then c₁ r else 0) (v : BIdx ε → k) :
    bFirst ε G *ᵥ v = ∑ r, c₁ r • (bDer ε (r, a₁, b₁) *ᵥ v) := by
  rw [bFirst_eq_sum_one ε G hb₁ c₁ hG, Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun r _ => by rw [Matrix.smul_mulVec]

theorem bFirst_mulVec_eq_sum_two [CharP k 2] {n : ℕ} (ε : Fin f → Finset (Fin n))
    (G : Fin f → Matrix (Fin n) (Fin n) k) {a₁ a₂ b₁ b₂ : Fin n}
    (hb₁ : (b₁ : ℕ) = a₁ + 1) (hb₂ : (b₂ : ℕ) = a₂ + 1) (hne : a₁ ≠ a₂)
    (c₁ c₂ : Fin f → k)
    (hG : ∀ (r : Fin f) (a b : Fin n), (b : ℕ) = a + 1 →
      G r a b = if a = a₁ then c₁ r else if a = a₂ then c₂ r else 0)
    (v : BIdx ε → k) :
    bFirst ε G *ᵥ v =
      ∑ r, (c₁ r • (bDer ε (r, a₁, b₁) *ᵥ v) + c₂ r • (bDer ε (r, a₂, b₂) *ᵥ v)) := by
  rw [bFirst_eq_sum_two ε G hb₁ hb₂ hne c₁ c₂ hG, Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun r _ => by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]

omit [CharP F 2] in
theorem bDer_mulVec_mem_bRad_of_two_positions [CharP k 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k) {n : ℕ} (ε : Fin f → Finset (Fin n))
    {v : BIdx ε → k} {a₁ b₁ a₂ b₂ : Fin n} (_hb₁ : (b₁ : ℕ) = a₁ + 1)
    (_hb₂ : (b₂ : ℕ) = a₂ + 1)
    (h : ∀ t : F, (∑ r : Fin f, (φ₀ t ^ 2 ^ (r : ℕ) • (bDer ε (r, a₁, b₁) *ᵥ v) +
        φ₀ t ^ 2 ^ (f + (r : ℕ)) • (bDer ε (r, a₂, b₂) *ᵥ v))) ∈ bRad ε)
    (r : Fin f) : bDer ε (r, a₁, b₁) *ᵥ v ∈ bRad ε := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ (2 * f) := by
    rw [← Nat.card_eq_fintype_card, hF, ← pow_mul]
    congr 1
    omega
  let W : Fin f ⊕ Fin f → BIdx ε → k :=
    Sum.elim (fun r => bDer ε (r, a₁, b₁) *ᵥ v) (fun r => bDer ε (r, a₂, b₂) *ᵥ v)
  let E : Fin f ⊕ Fin f → ℕ := Sum.elim (fun r => 2 ^ (r : ℕ)) (fun r => 2 ^ (f + (r : ℕ)))
  have hE : Function.Injective E := by
    rintro (i | i) (j | j) h <;> simp only [E, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (Fin.ext (Nat.pow_right_injective (a := 2) (by norm_num) h))
    · exfalso
      have h' : (i : ℕ) = f + (j : ℕ) := Nat.pow_right_injective (a := 2) (by norm_num) h
      omega
    · exfalso
      have h' : f + (i : ℕ) = (j : ℕ) := Nat.pow_right_injective (a := 2) (by norm_num) h
      omega
    · have h' : f + (i : ℕ) = f + (j : ℕ) := Nat.pow_right_injective (a := 2) (by norm_num) h
      exact congrArg Sum.inr (Fin.ext (by omega))
  have hbound : ∀ i, E i < Fintype.card F := by
    rintro (i | i)
    · rw [hcard]
      simp only [E, Sum.elim_inl]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · rw [hcard]
      simp only [E, Sum.elim_inr]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hsum : ∀ t : F, ∑ i, φ₀ t ^ E i • W i ∈ bRad ε := by
    intro t
    rw [Fintype.sum_sum_type]
    have ht := h t
    rw [Finset.sum_add_distrib] at ht
    simpa only [E, W, Sum.elim_inl, Sum.elim_inr] using ht
  have := mem_of_forall_sum_pow_map_smul_mem (F := F) φ₀ (bRad ε) E hE hbound W hsum (Sum.inl r)
  simpa only [W, Sum.elim_inl] using this

theorem bDer_mulVec_mem_bRad_of_fixed_of_trace [CharP k 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k) {n : ℕ} (ε : Fin f → Finset (Fin n))
    {v : BIdx ε → k} {a₁ b₁ : Fin n} (_hb₁ : (b₁ : ℕ) = a₁ + 1)
    (h : ∀ c : F, unitaryInvolution F 2 f c = c →
      (∑ r : Fin f, φ₀ c ^ 2 ^ (r : ℕ) • (bDer ε (r, a₁, b₁) *ᵥ v)) ∈ bRad ε)
    (r : Fin f) : bDer ε (r, a₁, b₁) *ᵥ v ∈ bRad ε := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype (fixedSubfield F 2 f) := Fintype.ofFinite _
  have hcard : Fintype.card (fixedSubfield F 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card, card_fixedSubfield (p := 2) hF]
  let W : Fin f → BIdx ε → k := fun r => bDer ε (r, a₁, b₁) *ᵥ v
  let E : Fin f → ℕ := fun r => 2 ^ (r : ℕ)
  have hE : Function.Injective E := fun i j h =>
    Fin.ext (Nat.pow_right_injective (a := 2) (by norm_num) h)
  have hbound : ∀ i, E i < Fintype.card (fixedSubfield F 2 f) := by
    intro i
    rw [hcard]
    exact Nat.pow_lt_pow_right (by norm_num) i.isLt
  have hsum : ∀ c : fixedSubfield F 2 f,
      ∑ i, (φ₀.comp (fixedSubfield F 2 f).subtype) c ^ E i • W i ∈ bRad ε := by
    intro c
    have hc : unitaryInvolution F 2 f (c : F) = (c : F) := mem_fixedSubfield.mp c.2
    simpa only [E, W, RingHom.comp_apply, Subfield.coe_subtype] using h (c : F) hc
  exact mem_of_forall_sum_pow_map_smul_mem (F := fixedSubfield F 2 f)
    (φ₀.comp (fixedSubfield F 2 f).subtype) (bRad ε) E hE hbound W hsum r

noncomputable def suOfMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (hdet : M.det = 1)
    (hiso : conjTr (unitaryInvolution F 2 f) M * antidiag n * M = antidiag n) :
    SU (unitaryInvolution F 2 f) n :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero),
    mem_SU.mpr ⟨by simpa using hdet, by simpa using hiso⟩⟩

@[simp] theorem mat_suOfMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (hdet : M.det = 1)
    (hiso : conjTr (unitaryInvolution F 2 f) M * antidiag n * M = antidiag n) :
    SUExtras.mat (unitaryInvolution F 2 f) n (suOfMatrix M hdet hiso) = M := by
  rw [SUExtras.mat_apply]
  rfl

theorem rootMatrix_apply {n : ℕ} {i j : Fin n} (c : F) (p q : Fin n) :
    rootMatrix (unitaryInvolution F 2 f) i j c p q =
      (if p = q then 1 else 0) + (if i = p ∧ j = q then c else 0) -
        (if Fin.rev j = p ∧ Fin.rev i = q then unitaryInvolution F 2 f c else 0) := by
  rw [rootMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Matrix.single_apply]

theorem rootMatrix_upper {n : ℕ} {i j : Fin n} (hij : (j : ℕ) = i + 1) (c : F) :
    ∀ p q : Fin n, q < p → rootMatrix (unitaryInvolution F 2 f) i j c p q = 0 := by
  intro p q hpq
  have hi : (i : ℕ) < n := i.isLt
  have hj : (j : ℕ) < n := j.isLt
  rw [rootMatrix_apply]
  have hpq' : ¬ p = q := by intro h; rw [h] at hpq; exact lt_irrefl _ hpq
  have h1 : ¬ (i = p ∧ j = q) := by
    rintro ⟨rfl, rfl⟩
    simp only [Fin.lt_def] at hpq
    omega
  have h2 : ¬ (Fin.rev j = p ∧ Fin.rev i = q) := by
    rintro ⟨rfl, rfl⟩
    simp only [Fin.lt_def, Fin.val_rev] at hpq
    omega
  rw [if_neg hpq', if_neg h1, if_neg h2]
  ring

theorem rootMatrix_diag {n : ℕ} {i j : Fin n} (hij : (j : ℕ) = i + 1) (c : F) (p : Fin n) :
    rootMatrix (unitaryInvolution F 2 f) i j c p p = 1 := by
  rw [rootMatrix_apply]
  have h1 : ¬ (i = p ∧ j = p) := by
    rintro ⟨h1, h2⟩
    have hji : j = i := h2.trans h1.symm
    rw [hji] at hij
    omega
  have h2 : ¬ (Fin.rev j = p ∧ Fin.rev i = p) := by
    rintro ⟨h1, h2⟩
    have hji : j = i := Fin.rev_injective (h1.trans h2.symm)
    rw [hji] at hij
    omega
  rw [if_pos rfl, if_neg h1, if_neg h2]
  ring

theorem rootMatrix_apply_of_super {n : ℕ} {i j a b : Fin n} (hij : (j : ℕ) = i + 1)
    (hno : (i : ℕ) + (j : ℕ) ≠ n - 1) (hab : (b : ℕ) = a + 1) (c : F) :
    rootMatrix (unitaryInvolution F 2 f) i j c a b =
      if a = i then c else if a = Fin.rev j then - unitaryInvolution F 2 f c else 0 := by
  have hi : (i : ℕ) < n := i.isLt
  have hj : (j : ℕ) < n := j.isLt
  rw [rootMatrix_apply]
  by_cases ha : a = i
  · rw [ha, if_pos rfl]
    have hb : b = j := Fin.ext (by rw [ha] at hab; rw [hab, hij])
    rw [hb]
    rw [if_neg (by intro h; rw [h] at hij; omega), if_pos ⟨rfl, rfl⟩,
      if_neg (by rintro ⟨h1, h2⟩; apply hno; simp only [Fin.ext_iff, Fin.val_rev] at h1 h2; omega)]
    ring
  · rw [if_neg ha]
    by_cases ha' : a = Fin.rev j
    · rw [ha', if_pos rfl]
      have hb : b = Fin.rev i := Fin.ext (by
        rw [ha'] at hab
        simp only [Fin.val_rev] at hab ⊢
        omega)
      rw [hb]
      rw [if_neg (by intro h; have hji : j = i := Fin.rev_injective h; rw [hji] at hij; omega),
        if_neg (by rintro ⟨h1, h2⟩; apply hno; simp only [Fin.ext_iff, Fin.val_rev] at h1 h2; omega),
        if_pos ⟨rfl, rfl⟩]
      ring
    · rw [if_neg ha']
      rw [if_neg (by intro h; have := congrArg Fin.val h; omega),
        if_neg (fun h => ha h.1.symm), if_neg (fun h => ha' h.1.symm)]
      ring

omit [Finite F] [CharP F 2] in
theorem longRootMatrix_apply {n : ℕ} {i : Fin n} (c : F) (p q : Fin n) :
    longRootMatrix (F := F) i c p q =
      (if p = q then 1 else 0) + (if i = p ∧ Fin.rev i = q then c else 0) := by
  rw [longRootMatrix, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

omit [Finite F] [CharP F 2] in
theorem longRootMatrix_upper {n : ℕ} {i : Fin n} (hii : (Fin.rev i : ℕ) = i + 1) (c : F) :
    ∀ p q : Fin n, q < p → longRootMatrix (F := F) i c p q = 0 := by
  intro p q hpq
  have hi : (i : ℕ) < n := i.isLt
  rw [longRootMatrix_apply]
  have hpq' : ¬ p = q := by intro h; rw [h] at hpq; exact lt_irrefl _ hpq
  have h1 : ¬ (i = p ∧ Fin.rev i = q) := by
    rintro ⟨rfl, rfl⟩
    simp only [Fin.lt_def, Fin.val_rev] at hpq
    simp only [Fin.val_rev] at hii
    omega
  rw [if_neg hpq', if_neg h1]
  ring

omit [Finite F] [CharP F 2] in
theorem longRootMatrix_diag {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) (c : F) (p : Fin n) :
    longRootMatrix (F := F) i c p p = 1 := by
  rw [longRootMatrix_apply]
  have h1 : ¬ (i = p ∧ Fin.rev i = p) := by
    rintro ⟨h1, h2⟩
    exact hi (h1.trans h2.symm)
  rw [if_pos rfl, if_neg h1]
  ring

omit [Finite F] [CharP F 2] in
theorem longRootMatrix_apply_of_super {n : ℕ} {i a b : Fin n} (hii : (Fin.rev i : ℕ) = i + 1)
    (hab : (b : ℕ) = a + 1) (c : F) :
    longRootMatrix (F := F) i c a b = if a = i then c else 0 := by
  rw [longRootMatrix_apply]
  by_cases ha : a = i
  · rw [ha, if_pos rfl]
    have hb : b = Fin.rev i := Fin.ext (by rw [ha] at hab; rw [hab, hii])
    rw [hb]
    rw [if_neg (by intro h; rw [h] at hii; omega), if_pos ⟨rfl, rfl⟩]
    ring
  · rw [if_neg ha]
    rw [if_neg (by intro h; have := congrArg Fin.val h; omega),
      if_neg (fun h => ha h.1.symm)]
    ring

theorem heisenbergMatrix_apply {n : ℕ} {i k : Fin n} (c d : F) (p q : Fin n) :
    heisenbergMatrix (unitaryInvolution F 2 f) i k c d p q =
      (if p = q then 1 else 0) + (if i = p ∧ k = q then c else 0) -
        (if k = p ∧ Fin.rev i = q then unitaryInvolution F 2 f c else 0) +
        (if i = p ∧ Fin.rev i = q then d else 0) := by
  rw [heisenbergMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Matrix.single_apply, Matrix.single_apply]

theorem heisenbergMatrix_upper {n : ℕ} {i k : Fin n} (hik : (k : ℕ) = i + 1)
    (hki : (Fin.rev i : ℕ) = k + 1) (c d : F) :
    ∀ p q : Fin n, q < p →
      heisenbergMatrix (unitaryInvolution F 2 f) i k c d p q = 0 := by
  intro p q hpq
  have hi : (i : ℕ) < n := i.isLt
  have hk : (k : ℕ) < n := k.isLt
  rw [heisenbergMatrix_apply]
  have hpq' : ¬ p = q := by intro h; rw [h] at hpq; exact lt_irrefl _ hpq
  have h1 : ¬ (i = p ∧ k = q) := by
    rintro ⟨rfl, rfl⟩
    simp only [Fin.lt_def] at hpq
    omega
  have h2 : ¬ (k = p ∧ Fin.rev i = q) := by
    rintro ⟨rfl, rfl⟩
    simp only [Fin.lt_def, Fin.val_rev] at hpq
    simp only [Fin.val_rev] at hki
    omega
  have h3 : ¬ (i = p ∧ Fin.rev i = q) := by
    rintro ⟨rfl, rfl⟩
    simp only [Fin.lt_def, Fin.val_rev] at hpq
    simp only [Fin.val_rev] at hki
    omega
  rw [if_neg hpq', if_neg h1, if_neg h2, if_neg h3]
  ring

theorem heisenbergMatrix_diag {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik' : i ≠ k)
    (hv : k ≠ Fin.rev i) (c d : F) (p : Fin n) :
    heisenbergMatrix (unitaryInvolution F 2 f) i k c d p p = 1 := by
  rw [heisenbergMatrix_apply]
  have h1 : ¬ (i = p ∧ k = p) := by
    rintro ⟨h1, h2⟩
    exact hik' (h1.trans h2.symm)
  have h2 : ¬ (k = p ∧ Fin.rev i = p) := by
    rintro ⟨h1, h2⟩
    exact hv (h1.trans h2.symm)
  have h3 : ¬ (i = p ∧ Fin.rev i = p) := by
    rintro ⟨h1, h2⟩
    exact hi (h1.trans h2.symm)
  rw [if_pos rfl, if_neg h1, if_neg h2, if_neg h3]
  ring

theorem heisenbergMatrix_apply_of_super {n : ℕ} {i k a b : Fin n} (hik : (k : ℕ) = i + 1)
    (hki : (Fin.rev i : ℕ) = k + 1) (hik' : i ≠ k) (hv : k ≠ Fin.rev i)
    (hab : (b : ℕ) = a + 1) (c d : F) :
    heisenbergMatrix (unitaryInvolution F 2 f) i k c d a b =
      if a = i then c else if a = k then - unitaryInvolution F 2 f c else 0 := by
  have hi : (i : ℕ) < n := i.isLt
  have hk : (k : ℕ) < n := k.isLt
  rw [heisenbergMatrix_apply]
  by_cases ha : a = i
  · rw [ha, if_pos rfl]
    have hb : b = k := Fin.ext (by rw [ha] at hab; rw [hab, hik])
    rw [hb]
    rw [if_neg (by intro h; exact hik' h), if_pos ⟨rfl, rfl⟩,
      if_neg (by rintro ⟨h1, -⟩; exact hik' h1.symm),
      if_neg (by rintro ⟨-, h2⟩; exact hv h2.symm)]
    ring
  · rw [if_neg ha]
    by_cases ha' : a = k
    · rw [ha', if_pos rfl]
      have hb : b = Fin.rev i := Fin.ext (by
        rw [ha'] at hab
        simp only [Fin.val_rev] at hab hki ⊢
        omega)
      rw [hb]
      rw [if_neg (by intro h; exact hv h),
        if_neg (by rintro ⟨h1, -⟩; exact hik' h1),
        if_pos ⟨rfl, rfl⟩,
        if_neg (by rintro ⟨h1, -⟩; exact hik' h1)]
      ring
    · rw [if_neg ha']
      rw [if_neg (by intro h; have := congrArg Fin.val h; omega),
        if_neg (fun h => ha h.1.symm), if_neg (fun h => ha' h.1.symm),
        if_neg (fun h => ha h.1.symm)]
      ring

@[expose] noncomputable def suRep [CharP k 2] (φ₀ : F →+* k) (n : ℕ) (ε : Fin f → Finset (Fin n)) :
    Representation k (SU (unitaryInvolution F 2 f) n) (BModel k ε) :=
  (bRep ε).comp (suTwist φ₀ f n)

theorem bDer_mulVec_homComp_mem_bRad_of_fixed [CharP k 2] (hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k)
    {n : ℕ} (ε : Fin f → Finset (Fin n)) {w : BIdx ε → k}
    (hU : ∀ g : SU (unitaryInvolution F 2 f) n, (∀ a b, b < a → SUExtras.mat _ n g a b = 0) →
      (∀ a, SUExtras.mat _ n g a a = 1) →
      bMat ε (fun r => (suTwist φ₀ f n g r : Matrix (Fin n) (Fin n) k)) *ᵥ w - w ∈ bRad ε)
    (e : ℤ) (htop : ∀ e', e < e' → homComp (fun s : BIdx ε => (kdeg s : ℤ)) e' w ∈ bRad ε)
    (r : Fin f) (a b : Fin n) (hab : (b : ℕ) = a + 1) :
    bDer ε (r, a, b) *ᵥ homComp (fun s : BIdx ε => (kdeg s : ℤ)) e w ∈ bRad ε := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ : ∀ c : F, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    fun c => unitaryInvolution_involutive hF c
  have hStep : ∀ (g : SU (unitaryInvolution F 2 f) n),
      (∀ x y, y < x → SUExtras.mat (unitaryInvolution F 2 f) n g x y = 0) →
      (∀ x, SUExtras.mat (unitaryInvolution F 2 f) n g x x = 1) →
      bFirst ε (fun r => (suTwist φ₀ f n g r : Matrix (Fin n) (Fin n) k)) *ᵥ
        homComp (fun s : BIdx ε => (kdeg s : ℤ)) e w ∈ bRad ε :=
    fun g hg hg1 => bFirst_suTwist_mulVec_homComp_mem_bRad ε φ₀ hU hg hg1 e htop
  rcases eq_or_ne n (2 * (a : ℕ) + 2) with hn2 | hn2
  ·
    have hii : (Fin.rev a : ℕ) = b := by simp only [Fin.val_rev]; omega
    have hii' : (Fin.rev a : ℕ) = (a : ℕ) + 1 := by rw [hii, hab]
    have hi : a ≠ Fin.rev a := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_rev] at this
      omega
    have hmem : ∀ c : F, unitaryInvolution F 2 f c = c →
        (∑ r : Fin f, φ₀ c ^ 2 ^ (r : ℕ) •
          (bDer ε (r, a, b) *ᵥ homComp (fun s : BIdx ε => (kdeg s : ℤ)) e w)) ∈ bRad ε := by
      intro c hc
      have hcz : c ∈ traceZero (unitaryInvolution F 2 f) := by
        rw [mem_traceZero, hc, CharTwo.add_self_eq_zero]
      let c' : traceZero (unitaryInvolution F 2 f) := ⟨c, hcz⟩
      let g : SU (unitaryInvolution F 2 f) n :=
        longRootHom (unitaryInvolution F 2 f) hi (Multiplicative.ofAdd c')
      have hgt : SUExtras.mat (unitaryInvolution F 2 f) n g = longRootMatrix (F := F) a c := by
        change SUExtras.mat (unitaryInvolution F 2 f) n
          (longRootHom (unitaryInvolution F 2 f) hi (Multiplicative.ofAdd c')) =
            longRootMatrix (F := F) a c
        simp only [SUExtras.mat_apply, coe_longRootHom, toAdd_ofAdd]
        rfl
      have hg : ∀ x y, y < x → SUExtras.mat (unitaryInvolution F 2 f) n g x y = 0 := by
        intro x y hxy
        rw [hgt]
        exact longRootMatrix_upper hii' c x y hxy
      have hg1 : ∀ x, SUExtras.mat (unitaryInvolution F 2 f) n g x x = 1 := by
        intro x
        rw [hgt]
        exact longRootMatrix_diag hi c x
      have hG : ∀ (r : Fin f) (x y : Fin n), (y : ℕ) = x + 1 →
          (suTwist φ₀ f n g r : Matrix (Fin n) (Fin n) k) x y =
            if x = a then φ₀ c ^ 2 ^ (r : ℕ) else 0 := by
        intro r x y hxy
        rw [coe_suTwist_apply, Matrix.map_apply, hgt, longRootMatrix_apply_of_super hii' hxy]
        by_cases hxa : x = a
        · simp only [if_pos hxa]
          rw [suFrob_apply]
        · simp only [if_neg hxa, map_zero]
      have h := hStep g hg hg1
      rw [bFirst_mulVec_eq_sum_one ε (fun r => (suTwist φ₀ f n g r : Matrix (Fin n) (Fin n) k))
        hab (fun r => φ₀ c ^ 2 ^ (r : ℕ)) hG] at h
      exact h
    exact bDer_mulVec_mem_bRad_of_fixed_of_trace hF φ₀ ε hab hmem r
  · rcases eq_or_ne n (2 * (a : ℕ) + 3) with hn3 | hn3
    ·
      have hrev_b : (Fin.rev b : ℕ) = b := by simp only [Fin.val_rev]; omega
      have hk : Fin.rev b = b := Fin.ext hrev_b
      have hrev_a : (Fin.rev a : ℕ) = b + 1 := by simp only [Fin.val_rev]; omega
      have hne_ab : a ≠ b := by intro h; rw [h] at hab; omega
      have hi_rev : a ≠ Fin.rev a := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_rev] at this
        omega
      have hv : b ≠ Fin.rev a := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_rev] at this
        omega
      have hfar : (Fin.rev a : ℕ) ≠ (a : ℕ) + 1 := by rw [hrev_a]; omega
      have hb₂ : ((Fin.rev a : Fin n) : ℕ) = b + 1 := hrev_a
      have hno : (a : ℕ) + (b : ℕ) ≠ n - 1 := by intro h; omega
      have hex : ∀ t : F, ∃ y : F, y + unitaryInvolution F 2 f y +
          unitaryInvolution F 2 f t * t = 0 := by
        intro t
        have hmem : unitaryInvolution F 2 f t * t ∈ fixedSubfield F 2 f := by
          rw [mem_fixedSubfield, map_mul, hσ t, mul_comm (unitaryInvolution F 2 f t) t]
        obtain ⟨y, hy⟩ := show unitaryInvolution F 2 f t * t ∈
            (unitaryTrace (F := F) (p := 2) (f := f)).range from by
          rw [range_unitaryTrace hF]
          exact hmem
        refine ⟨y, ?_⟩
        show unitaryTrace y + unitaryInvolution F 2 f t * t = 0
        rw [hy]
        exact CharTwo.add_self_eq_zero _
      refine bDer_mulVec_mem_bRad_of_two_positions (f := f) (a₂ := b) (b₂ := Fin.rev a)
        hF φ₀ ε hab hb₂ ?_ r
      intro t
      let y := (hex t).choose
      have hy : y + unitaryInvolution F 2 f y + unitaryInvolution F 2 f t * t = 0 :=
        (hex t).choose_spec
      let gt : SU (unitaryInvolution F 2 f) n :=
        suOfMatrix (heisenbergMatrix (unitaryInvolution F 2 f) a b t y)
          (det_heisenbergMatrix (unitaryInvolution F 2 f) hi_rev hne_ab hk t y)
          (heisenbergMatrix_isometry (unitaryInvolution F 2 f) hσ hi_rev hne_ab hk hy)
      have hgt : SUExtras.mat (unitaryInvolution F 2 f) n gt =
          heisenbergMatrix (unitaryInvolution F 2 f) a b t y := by
        change SUExtras.mat (unitaryInvolution F 2 f) n
          (suOfMatrix (heisenbergMatrix (unitaryInvolution F 2 f) a b t y) _ _) = _
        rw [mat_suOfMatrix]
      have hg : ∀ x z, z < x → SUExtras.mat (unitaryInvolution F 2 f) n gt x z = 0 := by
        intro x z hxz
        rw [hgt]
        exact heisenbergMatrix_upper hab hrev_a t y x z hxz
      have hg1 : ∀ x, SUExtras.mat (unitaryInvolution F 2 f) n gt x x = 1 := by
        intro x
        rw [hgt]
        exact heisenbergMatrix_diag hi_rev hne_ab hv t y x
      have hG : ∀ (r : Fin f) (x z : Fin n), (z : ℕ) = x + 1 →
          (suTwist φ₀ f n gt r : Matrix (Fin n) (Fin n) k) x z =
            if x = a then φ₀ t ^ 2 ^ (r : ℕ)
            else if x = b then φ₀ t ^ 2 ^ (f + (r : ℕ)) else 0 := by
        intro r x z hxz
        rw [coe_suTwist_apply, Matrix.map_apply, hgt,
          heisenbergMatrix_apply_of_super hab hrev_a hne_ab hv hxz]
        by_cases hx1 : x = a
        · simp only [if_pos hx1]
          rw [suFrob_apply]
        · simp only [if_neg hx1]
          by_cases hx2 : x = b
          · simp only [if_pos hx2]
            rw [map_neg, suFrob_apply_unitaryInvolution hF, CharTwo.neg_eq]
          · simp only [if_neg hx2, map_zero]
      have h := hStep gt hg hg1
      rw [bFirst_mulVec_eq_sum_two ε (fun r => (suTwist φ₀ f n gt r : Matrix (Fin n) (Fin n) k))
        hab hb₂ hne_ab (fun r => φ₀ t ^ 2 ^ (r : ℕ)) (fun r => φ₀ t ^ 2 ^ (f + (r : ℕ))) hG] at h
      exact h
    · rcases eq_or_ne n (2 * (a : ℕ) + 1) with hn1 | hn1
      ·
        have ha1 : 0 < (a : ℕ) := by have := b.isLt; omega
        have hrev_a : (Fin.rev a : ℕ) = a := by simp only [Fin.val_rev]; omega
        have hk : Fin.rev a = a := Fin.ext hrev_a
        let a₂ : Fin n := ⟨(a : ℕ) - 1, by omega⟩
        have ha₂val : (a₂ : ℕ) = (a : ℕ) - 1 := rfl
        have hik : (a : ℕ) = (a₂ : ℕ) + 1 := by simp only [ha₂val]; omega
        have hrev_a₂ : (Fin.rev a₂ : ℕ) = (a : ℕ) + 1 := by
          simp only [Fin.val_rev, ha₂val]; omega
        have hik' : a₂ ≠ a := by
          intro h; have := congrArg Fin.val h; simp only [ha₂val] at this; omega
        have hv : a ≠ Fin.rev a₂ := by intro h; rw [h] at hrev_a₂; omega
        have hfar : (Fin.rev a₂ : ℕ) ≠ (a₂ : ℕ) + 1 := by
          rw [hrev_a₂]; simp only [ha₂val]; omega
        have hi_rev : a₂ ≠ Fin.rev a₂ := by
          intro h; have := congrArg Fin.val h; simp only [Fin.val_rev, ha₂val] at this; omega
        have hb₂ : (a : ℕ) = (a₂ : ℕ) + 1 := hik
        have hne : a ≠ a₂ := fun h => hik' h.symm
        have hex : ∀ t : F, ∃ y : F, y + unitaryInvolution F 2 f y + t * unitaryInvolution F 2 f t = 0 := by
          intro t
          have hmem : t * unitaryInvolution F 2 f t ∈ fixedSubfield F 2 f := by
            rw [mem_fixedSubfield, map_mul, hσ t, mul_comm t (unitaryInvolution F 2 f t)]
          obtain ⟨y, hy⟩ := show t * unitaryInvolution F 2 f t ∈
              (unitaryTrace (F := F) (p := 2) (f := f)).range from by
            rw [range_unitaryTrace hF]
            exact hmem
          refine ⟨y, ?_⟩
          show unitaryTrace y + t * unitaryInvolution F 2 f t = 0
          rw [hy]
          exact CharTwo.add_self_eq_zero _
        refine bDer_mulVec_mem_bRad_of_two_positions (f := f) (a₂ := a₂) (b₂ := a)
          hF φ₀ ε hab hb₂ ?_ r
        intro t
        let y := (hex t).choose
        have hy : y + unitaryInvolution F 2 f y + t * unitaryInvolution F 2 f t = 0 :=
          (hex t).choose_spec
        have hy' : y + unitaryInvolution F 2 f y +
            unitaryInvolution F 2 f (unitaryInvolution F 2 f t) * unitaryInvolution F 2 f t = 0 := by
          rw [hσ t]
          exact hy
        let gt : SU (unitaryInvolution F 2 f) n :=
          suOfMatrix (heisenbergMatrix (unitaryInvolution F 2 f) a₂ a
            (unitaryInvolution F 2 f t) y)
            (det_heisenbergMatrix (unitaryInvolution F 2 f) hi_rev hik' hk
              (unitaryInvolution F 2 f t) y)
            (heisenbergMatrix_isometry (unitaryInvolution F 2 f) hσ hi_rev hik' hk hy')
        have hgt : SUExtras.mat (unitaryInvolution F 2 f) n gt =
            heisenbergMatrix (unitaryInvolution F 2 f) a₂ a (unitaryInvolution F 2 f t) y := by
          change SUExtras.mat (unitaryInvolution F 2 f) n
            (suOfMatrix (heisenbergMatrix (unitaryInvolution F 2 f) a₂ a
              (unitaryInvolution F 2 f t) y) _ _) = _
          rw [mat_suOfMatrix]
        have hg : ∀ x z, z < x → SUExtras.mat (unitaryInvolution F 2 f) n gt x z = 0 := by
          intro x z hxz
          rw [hgt]
          exact heisenbergMatrix_upper hik hrev_a₂ (unitaryInvolution F 2 f t) y x z hxz
        have hg1 : ∀ x, SUExtras.mat (unitaryInvolution F 2 f) n gt x x = 1 := by
          intro x
          rw [hgt]
          exact heisenbergMatrix_diag hi_rev hik' hv (unitaryInvolution F 2 f t) y x
        have hG : ∀ (r : Fin f) (x z : Fin n), (z : ℕ) = x + 1 →
            (suTwist φ₀ f n gt r : Matrix (Fin n) (Fin n) k) x z =
              if x = a then φ₀ t ^ 2 ^ (r : ℕ)
              else if x = a₂ then φ₀ t ^ 2 ^ (f + (r : ℕ)) else 0 := by
          intro r x z hxz
          rw [coe_suTwist_apply, Matrix.map_apply, hgt,
            heisenbergMatrix_apply_of_super hik hrev_a₂ hik' hv hxz]
          by_cases hx1 : x = a₂
          · have hxa : ¬ x = a := by rw [hx1]; exact hik'
            simp only [if_pos hx1, if_neg hxa]
            rw [suFrob_apply_unitaryInvolution hF]
          · simp only [if_neg hx1]
            by_cases hx2 : x = a
            · simp only [if_pos hx2]
              rw [hσ t, CharTwo.neg_eq, suFrob_apply]
            · simp only [if_neg hx2, map_zero]
        have h := hStep gt hg hg1
        rw [bFirst_mulVec_eq_sum_two ε (fun r => (suTwist φ₀ f n gt r : Matrix (Fin n) (Fin n) k))
          hab hb₂ hne (fun r => φ₀ t ^ 2 ^ (r : ℕ)) (fun r => φ₀ t ^ 2 ^ (f + (r : ℕ))) hG] at h
        exact h
      ·
        have hne_ab : a ≠ b := by intro h; rw [h] at hab; omega
        have hi_rev : a ≠ Fin.rev a := by
          intro h
          apply hn1
          have := congrArg Fin.val h
          simp only [Fin.val_rev] at this
          omega
        have hj_rev : b ≠ Fin.rev b := by
          intro h
          apply hn3
          have := congrArg Fin.val h
          simp only [Fin.val_rev] at this
          omega
        have hne₂ : a ≠ Fin.rev b := by
          intro h
          apply hn2
          have := congrArg Fin.val h
          simp only [Fin.val_rev] at this
          omega
        have hb₂ : ((Fin.rev a : Fin n) : ℕ) = (Fin.rev b : Fin n) + 1 := by
          simp only [Fin.val_rev]
          omega
        have hno : (a : ℕ) + (b : ℕ) ≠ n - 1 := by intro h; apply hn2; omega
        refine bDer_mulVec_mem_bRad_of_two_positions (f := f) (a₂ := Fin.rev b) (b₂ := Fin.rev a)
          hF φ₀ ε hab hb₂ ?_ r
        intro t
        let g : SU (unitaryInvolution F 2 f) n :=
          rootHom (i := a) (j := b) (unitaryInvolution F 2 f) hσ hne_ab hi_rev hj_rev
            (Multiplicative.ofAdd t)
        have hgt : SUExtras.mat (unitaryInvolution F 2 f) n g =
            rootMatrix (unitaryInvolution F 2 f) a b t := by
          change SUExtras.mat (unitaryInvolution F 2 f) n
            (rootHom (i := a) (j := b) (unitaryInvolution F 2 f) hσ hne_ab hi_rev hj_rev
              (Multiplicative.ofAdd t)) = rootMatrix (unitaryInvolution F 2 f) a b t
          simp only [SUExtras.mat_apply, coe_rootHom, toAdd_ofAdd]
        have hg : ∀ x z, z < x → SUExtras.mat (unitaryInvolution F 2 f) n g x z = 0 := by
          intro x z hxz
          rw [hgt]
          exact rootMatrix_upper hab t x z hxz
        have hg1 : ∀ x, SUExtras.mat (unitaryInvolution F 2 f) n g x x = 1 := by
          intro x
          rw [hgt]
          exact rootMatrix_diag hab t x
        have hG : ∀ (r : Fin f) (x z : Fin n), (z : ℕ) = x + 1 →
            (suTwist φ₀ f n g r : Matrix (Fin n) (Fin n) k) x z =
              if x = a then φ₀ t ^ 2 ^ (r : ℕ)
              else if x = Fin.rev b then φ₀ t ^ 2 ^ (f + (r : ℕ)) else 0 := by
          intro r x z hxz
          rw [coe_suTwist_apply, Matrix.map_apply, hgt,
            rootMatrix_apply_of_super hab hno hxz]
          by_cases hx1 : x = a
          · simp only [if_pos hx1]
            rw [suFrob_apply]
          · simp only [if_neg hx1]
            by_cases hx2 : x = Fin.rev b
            · simp only [if_pos hx2]
              rw [map_neg, suFrob_apply_unitaryInvolution hF, CharTwo.neg_eq]
            · simp only [if_neg hx2, map_zero]
        have h := hStep g hg hg1
        rw [bFirst_mulVec_eq_sum_two ε (fun r => (suTwist φ₀ f n g r : Matrix (Fin n) (Fin n) k))
          hab hb₂ hne₂ (fun r => φ₀ t ^ 2 ^ (r : ℕ)) (fun r => φ₀ t ^ 2 ^ (f + (r : ℕ))) hG] at h
        exact h

theorem sub_smul_bvec_mem_bRad_of_fixed [CharP k 2] (hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k) {n : ℕ}
    (ε : Fin f → Finset (Fin n)) {w : BIdx ε → k} (hw : w ∈ bCyc ε)
    (hU : ∀ g : SU (unitaryInvolution F 2 f) n, (∀ a b, b < a → SUExtras.mat _ n g a b = 0) →
      (∀ a, SUExtras.mat _ n g a a = 1) →
      bMat ε (fun r => (suTwist φ₀ f n g r : Matrix (Fin n) (Fin n) k)) *ᵥ w - w ∈ bRad ε) :
    w - (w ⬝ᵥ bvec ε) • bvec ε ∈ bRad ε :=
  sub_smul_bvec_mem_bRad_of_homComp ε hw fun e htop r a b hab =>
    bDer_mulVec_homComp_mem_bRad_of_fixed hF φ₀ ε hU e htop r a b hab

theorem eq_smul_bTop_of_fixed [CharP k 2] (hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k) {n : ℕ}
    (ε : Fin f → Finset (Fin n)) (x : BModel k ε)
    (hx : ∀ g : SU (unitaryInvolution F 2 f) n, (∀ a b, b < a → SUExtras.mat _ n g a b = 0) →
      (∀ a, SUExtras.mat _ n g a a = 1) → suRep φ₀ n ε g x = x) :
    ∃ c : k, x = c • bTop ε := by
  classical
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective
    (p := (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype) x
  refine ⟨(w : BIdx ε → k) ⬝ᵥ bvec ε, ?_⟩
  have hU : ∀ g : SU (unitaryInvolution F 2 f) n,
      (∀ a b, b < a → SUExtras.mat (unitaryInvolution F 2 f) n g a b = 0) →
      (∀ a, SUExtras.mat (unitaryInvolution F 2 f) n g a a = 1) →
      bMat ε (fun r => (suTwist φ₀ f n g r : Matrix (Fin n) (Fin n) k)) *ᵥ (w : BIdx ε → k) -
        (w : BIdx ε → k) ∈ bRad ε := by
    intro g hg hg1
    have h := hx g hg hg1
    change bRep ε (suTwist φ₀ f n g) (Submodule.Quotient.mk w) = Submodule.Quotient.mk w at h
    rw [bRep_mk, Submodule.Quotient.eq, Submodule.mem_comap] at h
    simpa using h
  have hsub := sub_smul_bvec_mem_bRad_of_fixed hF φ₀ ε w.2 hU
  rw [bTop, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
  simpa using hsub

theorem isSimpleRep_suRep [CharP k 2] (hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k) {n : ℕ} (hn : 2 ≤ n)
    (ε : Fin f → Finset (Fin n)) : CFSG.Quasithin.SmithCurtis.IsSimpleRep (suRep φ₀ n ε) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero (p := 2) (f := f) hF
  let D := curtisDatum (p := 2) hF n hn ζ hζ
  have : Nontrivial (BModel k ε) := ⟨⟨bTop ε, 0, bTop_ne_zero ε⟩⟩
  have hfix : ∀ x : BModel k ε, (∀ u ∈ D.U, suRep φ₀ n ε u x = x) → ∃ c : k, x = c • bTop ε :=
    fun x hx => eq_smul_bTop_of_fixed hF φ₀ ε x (fun g hg hg1 =>
      hx g ((mem_curtisDatum_U_iff (p := 2) hF n hn ζ hζ g).mpr ⟨hg, hg1⟩))
  have hT : ∀ g : SU (unitaryInvolution F 2 f) n, ∃ g' : SU (unitaryInvolution F 2 f) n,
      ∀ r, (suTwist φ₀ f n g' r : Matrix (Fin n) (Fin n) k) =
        (suTwist φ₀ f n g r : Matrix (Fin n) (Fin n) k)ᵀ := by
    intro g
    obtain ⟨B, hB, hBcoe⟩ := transpose_mem_SU (K := F) (σ := unitaryInvolution F 2 f) (n := n) g.2
    refine ⟨⟨B, hB⟩, fun r => ?_⟩
    rw [coe_suTwist_apply, coe_suTwist_apply, SUExtras.mat_apply, SUExtras.mat_apply, hBcoe,
      Matrix.transpose_map]
  have hgen : CFSG.Quasithin.SmithCurtis.orbitSpan (suRep φ₀ n ε) (bTop ε) = ⊤ :=
    orbitSpan_bTop_eq_top (k := k) ε (π := suTwist φ₀ f n) hT D.isPGroup_U
      (fun x hx => eq_smul_bTop_of_fixed hF φ₀ ε x (fun g hg hg1 =>
        hx g ((mem_curtisDatum_U_iff (p := 2) hF n hn ζ hζ g).mpr ⟨hg, hg1⟩)))
  refine CFSG.Quasithin.SmithCurtis.CurtisDatum.isSimpleRep_of_fixU (D := D) (ρ := suRep φ₀ n ε) ?_ hgen
  intro x hx
  exact eq_smul_bTop_of_fixed hF φ₀ ε x (fun g hg hg1 =>
    hx g ((mem_curtisDatum_U_iff (p := 2) hF n hn ζ hζ g).mpr ⟨hg, hg1⟩))

end CFSG.LieType.Universal.Unitary
