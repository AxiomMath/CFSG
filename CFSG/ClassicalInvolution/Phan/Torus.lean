module

public import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.ClassicalInvolution.Phan

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section NormOne

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem card_normOne (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (normOne (unitaryInvolution K p f)) = p ^ f + 1 := by
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have heq : normOne (unitaryInvolution K p f) =
      (powMonoidHom (p ^ f + 1) : Kˣ →* Kˣ).ker := by
    ext u
    rw [mem_normOne, MonoidHom.mem_ker, powMonoidHom_apply, ← Units.val_eq_one,
      Units.val_pow_eq_pow_val, unitaryInvolution_apply, ← pow_succ]
  rw [heq, IsCyclic.card_powMonoidHom_ker, CFSG.ClassicalGroups.Unitary.card_units_of_card hK]
  have : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
    zify [hq, Nat.one_le_pow 2 (p ^ f) hq]
    ring
  rw [this, Nat.gcd_mul_right_left]

end NormOne

section Diag

variable {F : Type*} [Field F] (σ : F ≃+* F)

@[expose] def detKer (m : ℕ) : Subgroup (Fin m → normOne σ) where
  carrier := {d | ∏ a, d a = 1}
  mul_mem' {d e} hd he := by
    have hd' : ∏ a, d a = 1 := hd
    have he' : ∏ a, e a = 1 := he
    change ∏ a, (d * e) a = 1
    simp only [Pi.mul_apply, Finset.prod_mul_distrib]
    rw [hd', he', one_mul]
  one_mem' := by simp
  inv_mem' {d} hd := by
    have hd' : ∏ a, d a = 1 := hd
    change ∏ a, (d⁻¹) a = 1
    simp only [Pi.inv_apply, Finset.prod_inv_distrib]
    rw [hd', inv_one]

variable {σ}

theorem mem_detKer {m : ℕ} {d : Fin m → normOne σ} : d ∈ detKer σ m ↔ ∏ a, d a = 1 :=
  Iff.rfl

theorem det_diagonal_normOne {m : ℕ} {d : Fin m → normOne σ} (hd : d ∈ detKer σ m) :
    (Matrix.diagonal fun a => ((d a : normOne σ) : Fˣ).val).det = 1 := by
  rw [Matrix.det_diagonal]
  have h1 : ((∏ a, d a : normOne σ) : Fˣ) = ∏ a, ((d a : normOne σ) : Fˣ) :=
    map_prod (normOne σ).subtype d Finset.univ
  have h2 : ((∏ a, ((d a : normOne σ) : Fˣ) : Fˣ) : F) = ∏ a, (((d a : normOne σ) : Fˣ) : F) :=
    map_prod (Units.coeHom F) _ _
  rw [← h2, ← h1, mem_detKer.1 hd]
  rfl

theorem conjTr_diagonal_mul_self {m : ℕ} (d : Fin m → normOne σ) :
    conjTr σ (Matrix.diagonal fun a => ((d a : normOne σ) : Fˣ).val) *
      Matrix.diagonal (fun a => ((d a : normOne σ) : Fˣ).val) = 1 := by
  rw [conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  exact (d a).2

variable (σ)

@[expose] def diagSU {m : ℕ} (d : Fin m → normOne σ) (hd : d ∈ detKer σ m) : SUid σ m :=
  ⟨diagGL fun a => ((d a : normOne σ) : Fˣ), by
    rw [coe_diagGL]
    exact det_diagonal_normOne hd, by
    rw [coe_diagGL]
    exact conjTr_diagonal_mul_self d⟩

variable {σ}

theorem coe_diagSU {m : ℕ} (d : Fin m → normOne σ) (hd : d ∈ detKer σ m) :
    ((diagSU σ d hd : SUid σ m) : GL (Fin m) F) = diagGL fun a => ((d a : normOne σ) : Fˣ) :=
  rfl

theorem coe_coe_diagSU {m : ℕ} (d : Fin m → normOne σ) (hd : d ∈ detKer σ m) :
    (((diagSU σ d hd : SUid σ m) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      Matrix.diagonal fun a => ((d a : normOne σ) : Fˣ).val :=
  rfl

theorem coe_inv_diagSU {m : ℕ} (d : Fin m → normOne σ) (hd : d ∈ detKer σ m) :
    ((((diagSU σ d hd)⁻¹ : SUid σ m) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      Matrix.diagonal fun a => (((d a : normOne σ) : Fˣ)⁻¹).val :=
  rfl

variable (σ)

@[expose] def diagSUHom (m : ℕ) : detKer σ m →* SUid σ m :=
  MonoidHom.mk' (fun d => diagSU σ d.1 d.2) fun d e => Subtype.ext (Units.ext (by
    simp only [coe_coe_diagSU, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul,
      Matrix.diagonal_mul_diagonal]
    rfl))

variable {σ}

theorem diagSUHom_apply {m : ℕ} (d : detKer σ m) : diagSUHom σ m d = diagSU σ d.1 d.2 :=
  rfl

theorem diagSUHom_injective (m : ℕ) : Function.Injective (diagSUHom σ m) := by
  intro d e h
  have h' := congrArg (fun g : SUid σ m => (((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F))) h
  refine Subtype.ext (funext fun a => Subtype.ext (Units.ext ?_))
  have := congrFun (congrFun h' a) a
  simpa [diagSUHom_apply, coe_coe_diagSU] using this

variable (σ)

@[expose] def torus (m : ℕ) : Subgroup (SUid σ m) := (diagSUHom σ m).range

variable {σ}

theorem diagSU_mem_torus {m : ℕ} (d : Fin m → normOne σ) (hd : d ∈ detKer σ m) :
    diagSU σ d hd ∈ torus σ m :=
  ⟨⟨d, hd⟩, rfl⟩

@[expose] noncomputable def torusDetKerEquiv (m : ℕ) : detKer σ m ≃* torus σ m :=
  MonoidHom.ofInjective (diagSUHom_injective m)

theorem mem_torus_iff {m : ℕ} (g : SUid σ m) :
    g ∈ torus σ m ↔
      ∀ a b : Fin m, a ≠ b → ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) a b = 0 := by
  constructor
  · rintro ⟨⟨d, hd⟩, rfl⟩ a b hab
    exact Matrix.diagonal_apply_ne _ hab
  · intro hg
    set M : Matrix (Fin m) (Fin m) F := ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) with hM
    have hdiag : M = Matrix.diagonal fun a => M a a := by
      ext a b
      by_cases hab : a = b
      · subst hab
        rw [Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ hab, hg a b hab]
    have hdet : ∏ a, M a a = 1 := by
      have := g.2.1
      rw [← hM, hdiag, Matrix.det_diagonal] at this
      exact this
    have hne : ∀ a, M a a ≠ 0 := fun a h0 => by
      have : ∏ a, M a a = 0 := Finset.prod_eq_zero (Finset.mem_univ a) h0
      rw [hdet] at this
      exact one_ne_zero this
    have hnorm : ∀ a, σ (M a a) * M a a = 1 := by
      intro a
      have h2 := congrFun (congrFun g.2.2 a) a
      rw [← hM, Matrix.mul_apply, Finset.sum_eq_single a] at h2
      · simpa [conjTr] using h2
      · intro c _ hca
        simp [conjTr, hg c a hca]
      · simp
    let d : Fin m → normOne σ := fun a => ⟨Units.mk0 (M a a) (hne a), hnorm a⟩
    have hd : d ∈ detKer σ m := by
      rw [mem_detKer]
      refine Subtype.ext (Units.ext ?_)
      have h1 : ((∏ a, d a : normOne σ) : Fˣ) = ∏ a, ((d a : normOne σ) : Fˣ) :=
        map_prod (normOne σ).subtype d Finset.univ
      have h2 : ((∏ a, ((d a : normOne σ) : Fˣ) : Fˣ) : F) = ∏ a, (((d a : normOne σ) : Fˣ) : F) :=
        map_prod (Units.coeHom F) _ _
      rw [Subgroup.coe_one, Units.val_one]
      change ((∏ a, d a : normOne σ) : Fˣ).val = 1
      rw [h1, h2]
      exact hdet
    refine ⟨⟨d, hd⟩, Subtype.ext (Units.ext ?_)⟩
    rw [diagSUHom_apply, coe_coe_diagSU]
    exact hdiag.symm

theorem diagSU_smul {m : ℕ} (d : Fin m → normOne σ) (hd : d ∈ detKer σ m) (v : Fin m → F) :
    diagSU σ d hd • v = fun a => ((d a : normOne σ) : Fˣ).val * v a := by
  funext a
  rw [CFSG.ClassicalGroups.Unitary.smul_def, coe_coe_diagSU, Matrix.mulVec_diagonal]

theorem torus_mul_comm {m : ℕ} {s t : SUid σ m} (hs : s ∈ torus σ m) (ht : t ∈ torus σ m) :
    s * t = t * s := by
  obtain ⟨d, rfl⟩ := hs
  obtain ⟨e, rfl⟩ := ht
  rw [← map_mul, ← map_mul, mul_comm]

end Diag

section ConjDiag

variable {F : Type*} [Field F] {m k i : ℕ}

theorem diagonal_mul_blockMat_mul_diagonal (h : i + k ≤ m) (v w : Fin m → F)
    (hvw : ∀ a, v a * w a = 1) (A : Matrix (Fin k) (Fin k) F) :
    Matrix.diagonal v * blockMat m i A * Matrix.diagonal w =
      blockMat m i (Matrix.diagonal (fun x => v (blockIdx i h x)) * A *
        Matrix.diagonal (fun x => w (blockIdx i h x))) := by
  refine conj_blockMat_of_intertwine (i' := i) (D := Matrix.diagonal fun x => v (blockIdx i h x))
    (D' := Matrix.diagonal fun x => w (blockIdx i h x)) ?_ ?_ ?_ ?_ A
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hvw)
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext fun x => hvw _)
  · ext a y
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, blockSel_apply]
    by_cases hay : a.val = i + y.val
    · have : a = blockIdx i h y := Fin.ext hay
      rw [ite_eq_left hay, this]
      simp
    · rw [ite_eq_right hay]
      simp
  · ext y a
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, transpose_apply, blockSel_apply]
    by_cases hay : a.val = i + y.val
    · have : a = blockIdx i h y := Fin.ext hay
      rw [ite_eq_left hay, this]
      simp
    · rw [ite_eq_right hay]
      simp

end ConjDiag

section ConjDiagSU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def conjDiag (hK : Nat.card K = (p ^ f) ^ 2) {k : ℕ}
    (e : Fin k → normOne (unitaryInvolution K p f)) : Su K p f k →* Su K p f k :=
  ((MulAut.conj (diagGL fun x => ((e x : normOne (unitaryInvolution K p f)) : Kˣ))).toMonoidHom.comp
    (SUid (unitaryInvolution K p f) k).subtype).codRestrict _ fun A =>
    conj_mem_SUid (unitaryInvolution_involutive hK) (conjTr_diagonal_mul_self e) A.2

theorem coe_conjDiag (hK : Nat.card K = (p ^ f) ^ 2) {k : ℕ}
    (e : Fin k → normOne (unitaryInvolution K p f)) (A : Su K p f k) :
    ((conjDiag hK e A : Su K p f k) : GL (Fin k) K) =
      diagGL (fun x => ((e x : normOne (unitaryInvolution K p f)) : Kˣ)) * A *
        (diagGL (fun x => ((e x : normOne (unitaryInvolution K p f)) : Kˣ)))⁻¹ :=
  rfl

theorem diagSU_mul_blockEmb_mul_inv (hK : Nat.card K = (p ^ f) ^ 2) {m k i : ℕ}
    (d : Fin m → normOne (unitaryInvolution K p f)) (hd : d ∈ detKer (unitaryInvolution K p f) m)
    (h : i + k ≤ m) (A : Su K p f k) :
    diagSU (unitaryInvolution K p f) d hd * blockEmb K p f m k i h A *
        (diagSU (unitaryInvolution K p f) d hd)⁻¹ =
      blockEmb K p f m k i h (conjDiag hK (fun x => d (blockIdx i h x)) A) := by
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  refine (diagonal_mul_blockMat_mul_diagonal h _ _ (fun a => ?_) _).trans ?_
  · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rfl

theorem torus_conj_range_blockEmb (hK : Nat.card K = (p ^ f) ^ 2) {m k i : ℕ} (h : i + k ≤ m)
    {t : Su K p f m} (ht : t ∈ torus (unitaryInvolution K p f) m) {x : Su K p f m}
    (hx : x ∈ (blockEmb K p f m k i h).range) : t * x * t⁻¹ ∈ (blockEmb K p f m k i h).range := by
  obtain ⟨⟨d, hd⟩, rfl⟩ := ht
  obtain ⟨A, rfl⟩ := hx
  exact ⟨_, (diagSU_mul_blockEmb_mul_inv hK d hd h A).symm⟩

theorem torus_le_normalizer_range_blockEmb (hK : Nat.card K = (p ^ f) ^ 2) {m k i : ℕ}
    (h : i + k ≤ m) :
    torus (unitaryInvolution K p f) m ≤
      Subgroup.normalizer ((blockEmb K p f m k i h).range : Set (Su K p f m)) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => torus_conj_range_blockEmb hK h ht hx, fun hx => ?_⟩
  have := torus_conj_range_blockEmb hK h (inv_mem ht) hx
  rwa [inv_inv, show t⁻¹ * (t * x * t⁻¹) * t = x by group] at this

theorem coe_conjDiag_apply (hK : Nat.card K = (p ^ f) ^ 2) {k : ℕ}
    (e : Fin k → normOne (unitaryInvolution K p f)) (A : Su K p f k) (x y : Fin k) :
    (((conjDiag hK e A : Su K p f k) : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) x y =
      ((e x : normOne (unitaryInvolution K p f)) : Kˣ).val *
        (((A : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) x y) *
        (((e y : normOne (unitaryInvolution K p f)) : Kˣ)⁻¹).val := by
  change (Matrix.diagonal (fun a => ((e a : normOne _) : Kˣ).val) *
    ((A : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) *
      Matrix.diagonal (fun a => (((e a : normOne _) : Kˣ)⁻¹).val)) x y = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem conjDiag_two (hK : Nat.card K = (p ^ f) ^ 2) (a b : normOne (unitaryInvolution K p f)) :
    conjDiag hK ![a, b] = conjDiag hK ![a * b⁻¹, 1] := by
  refine MonoidHom.ext fun A => Subtype.ext (Units.ext (Matrix.ext fun x y => ?_))
  rw [coe_conjDiag_apply, coe_conjDiag_apply]
  fin_cases x <;> fin_cases y <;> simp <;> field_simp

end ConjDiagSU

section PartialProd

variable {N : Type*} [CommGroup N]

@[expose] def extTuple {m : ℕ} (d : Fin m → N) (b : ℕ) : N :=
  if h : b < m then d ⟨b, h⟩ else 1

@[expose] def extShift {m : ℕ} (d : Fin m → N) : ℕ → N
  | 0 => 1
  | b + 1 => extTuple d b

@[expose] def partialProd {m : ℕ} (d : Fin m → N) (k : ℕ) : N :=
  ∏ b ∈ Finset.range (k + 1), extTuple d b

@[expose] def ratio {n : ℕ} (s : Fin n → N) : Fin (n + 1) → N :=
  fun a => extTuple s a.val * (extShift s a.val)⁻¹

theorem extTuple_of_lt {m : ℕ} (d : Fin m → N) {b : ℕ} (h : b < m) : extTuple d b = d ⟨b, h⟩ :=
  dite_eq_left h

theorem extTuple_of_le {m : ℕ} (d : Fin m → N) {b : ℕ} (h : m ≤ b) : extTuple d b = 1 :=
  dite_eq_right (by omega)

theorem partialProd_zero {m : ℕ} (d : Fin m → N) : partialProd d 0 = extTuple d 0 := by
  simp [partialProd]

theorem partialProd_succ {m : ℕ} (d : Fin m → N) (k : ℕ) :
    partialProd d (k + 1) = partialProd d k * extTuple d (k + 1) := by
  simp only [partialProd]
  rw [Finset.prod_range_succ _ (k + 1)]

theorem partialProd_mul {m : ℕ} (d e : Fin m → N) (k : ℕ) :
    partialProd (d * e) k = partialProd d k * partialProd e k := by
  simp only [partialProd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  by_cases h : b < m <;> simp [extTuple, h]

theorem partialProd_one {m : ℕ} (k : ℕ) : partialProd (1 : Fin m → N) k = 1 := by
  simp only [partialProd]
  refine Finset.prod_eq_one fun b _ => ?_
  by_cases h : b < m <;> simp [extTuple, h]

theorem prod_eq_partialProd {n : ℕ} (d : Fin (n + 1) → N) : ∏ a, d a = partialProd d n := by
  have := Fin.prod_univ_eq_prod_range (extTuple d) (n + 1)
  rw [partialProd]
  rw [← this]
  exact Finset.prod_congr rfl fun a _ => (extTuple_of_lt d a.isLt).symm.trans (by simp)

theorem partialProd_ratio {n : ℕ} (s : Fin n → N) (k : ℕ) :
    partialProd (ratio s) k = extTuple s k := by
  have hext : ∀ b : ℕ, extTuple (ratio s) (b + 1) = extTuple s (b + 1) * (extTuple s b)⁻¹ := by
    intro b
    by_cases hb : b + 1 < n + 1
    · rw [extTuple_of_lt _ hb]
      rfl
    · rw [extTuple_of_le _ (by omega), extTuple_of_le s (by omega : n ≤ b + 1),
        extTuple_of_le s (by omega : n ≤ b), inv_one, one_mul]
  induction k with
  | zero =>
    rw [partialProd_zero, extTuple_of_lt _ (by omega : 0 < n + 1)]
    simp [ratio, extShift]
  | succ k ih =>
    rw [partialProd_succ, ih, hext]
    simp

theorem extTuple_mulSingle {n : ℕ} (k : Fin n) (u : N) (b : ℕ) :
    extTuple (Pi.mulSingle k u : Fin n → N) b = if b = k.val then u else 1 := by
  by_cases hb : b < n
  · rw [extTuple_of_lt _ hb, Pi.mulSingle_apply]
    simp [Fin.ext_iff]
  · rw [extTuple_of_le _ (by omega), ite_eq_right (by have := k.isLt; omega)]

theorem extShift_mulSingle {n : ℕ} (k : Fin n) (u : N) (b : ℕ) :
    extShift (Pi.mulSingle k u : Fin n → N) b = if b = k.val + 1 then u else 1 := by
  cases b with
  | zero => simp [extShift]
  | succ b => simp [extShift, extTuple_mulSingle]

theorem ratio_mulSingle {n : ℕ} (k : Fin n) (u : N) (a : Fin (n + 1)) :
    ratio (Pi.mulSingle k u : Fin n → N) a =
      if a.val = k.val then u else if a.val = k.val + 1 then u⁻¹ else 1 := by
  rw [ratio, extTuple_mulSingle, extShift_mulSingle]
  by_cases h1 : a.val = k.val
  · have h2 : ¬ a.val = k.val + 1 := by omega
    simp [h1]
  · by_cases h2 : a.val = k.val + 1
    · simp [h2]
    · simp [h1, h2]

end PartialProd

section TorusEquiv

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

variable (σ n) in
@[expose] def partialProdHom : detKer σ (n + 1) →* (Fin n → normOne σ) where
  toFun d := fun k => partialProd d.1 k.val
  map_one' := by
    funext k
    exact partialProd_one _
  map_mul' d e := by
    funext k
    exact partialProd_mul d.1 e.1 k.val

theorem ratio_mem_detKer (s : Fin n → normOne σ) : ratio s ∈ detKer σ (n + 1) := by
  rw [mem_detKer, prod_eq_partialProd, partialProd_ratio, extTuple_of_le s le_rfl]

theorem partialProdHom_ratio (s : Fin n → normOne σ) :
    partialProdHom σ n ⟨ratio s, ratio_mem_detKer s⟩ = s := by
  funext k
  change partialProd (ratio s) k.val = s k
  rw [partialProd_ratio, extTuple_of_lt s k.isLt]

theorem partialProdHom_injective : Function.Injective (partialProdHom σ n) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  have h1 : ∀ k : ℕ, k < n → partialProd d.1 k = 1 := fun k hk => congrFun hd ⟨k, hk⟩
  have h2 : partialProd d.1 n = 1 := by
    rw [← prod_eq_partialProd]
    exact mem_detKer.1 d.2
  have h3 : ∀ k : ℕ, k ≤ n → partialProd d.1 k = 1 := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · exact h1 k hk
    · exact h2
  refine Subtype.ext (funext fun a => ?_)
  obtain ⟨b, hb⟩ := a
  cases b with
  | zero =>
    have := h3 0 (by omega)
    rw [partialProd_zero, extTuple_of_lt _ hb] at this
    exact this
  | succ b =>
    have e1 := h3 (b + 1) (by omega)
    have e0 := h3 b (by omega)
    rw [partialProd_succ, e0, one_mul, extTuple_of_lt _ hb] at e1
    exact e1

variable (σ n) in
@[expose] noncomputable def partialProdEquiv : detKer σ (n + 1) ≃* (Fin n → normOne σ) :=
  MulEquiv.ofBijective (partialProdHom σ n)
    ⟨partialProdHom_injective, fun s => ⟨⟨ratio s, ratio_mem_detKer s⟩, partialProdHom_ratio s⟩⟩

theorem partialProdEquiv_symm_apply (s : Fin n → normOne σ) :
    (partialProdEquiv σ n).symm s = ⟨ratio s, ratio_mem_detKer s⟩ :=
  (MulEquiv.symm_apply_eq _).2 (partialProdHom_ratio s).symm

variable (σ n) in
@[expose] noncomputable def torusEquiv : (Fin n → normOne σ) ≃* torus σ (n + 1) :=
  (partialProdEquiv σ n).symm.trans (torusDetKerEquiv (n + 1))

theorem coe_torusEquiv (s : Fin n → normOne σ) :
    ((torusEquiv σ n s : torus σ (n + 1)) : SUid σ (n + 1)) =
      diagSU σ (ratio s) (ratio_mem_detKer s) := by
  change diagSUHom σ (n + 1) ((partialProdEquiv σ n).symm s) = _
  rw [partialProdEquiv_symm_apply]
  rfl

end TorusEquiv

section TorusEquivSU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem card_torus (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ) :
    Nat.card (torus (unitaryInvolution K p f) (n + 1)) = (p ^ f + 1) ^ n := by
  rw [← Nat.card_congr (torusEquiv (unitaryInvolution K p f) n).toEquiv, Nat.card_pi,
    Finset.prod_const, card_normOne hK, Finset.card_univ, Fintype.card_fin]

theorem coe_torusEquiv_mulSingle (k : Fin n) (u : normOne (unitaryInvolution K p f)) :
    ((torusEquiv (unitaryInvolution K p f) n (Pi.mulSingle k u) :
        torus (unitaryInvolution K p f) (n + 1)) : Su K p f (n + 1)) =
      blockEmb2 K p f n k (torusTwo (unitaryInvolution K p f) u) := by
  rw [coe_torusEquiv]
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => ?_))
  change Matrix.diagonal (fun a => ((ratio (Pi.mulSingle k u : Fin n → normOne _) a : normOne _) :
    Kˣ).val) a b = blockMat (n + 1) k.val
      ((torusTwo (unitaryInvolution K p f) u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a b
  rw [blockMat_apply, coe_torusTwo]
  by_cases hblk : (k.val ≤ a.val ∧ a.val < k.val + 2) ∧ (k.val ≤ b.val ∧ b.val < k.val + 2)
  · rw [dite_eq_left hblk]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ratio_mulSingle]
      by_cases h1 : a.val = k.val
      · rw [ite_eq_left h1]
        have : (⟨a.val - k.val, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp; omega)
        rw [this]
        simp
      · have h2 : a.val = k.val + 1 := by omega
        rw [ite_eq_right h1, ite_eq_left h2]
        have : (⟨a.val - k.val, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp; omega)
        rw [this]
        simp
    · have hab' : (⟨a.val - k.val, by omega⟩ : Fin 2) ≠ ⟨b.val - k.val, by omega⟩ := by
        intro h
        exact hab (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))
      rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab']
  · rw [dite_eq_right hblk]
    by_cases hab : a = b
    · subst hab
      have h1 : ¬ a.val = k.val := fun h => hblk ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      have h2 : ¬ a.val = k.val + 1 := fun h => hblk ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, ratio_mulSingle, ite_eq_right h1,
        ite_eq_right h2]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]

theorem coe_torusEquiv_mul_blockEmb2_mul_inv (hK : Nat.card K = (p ^ f) ^ 2)
    (s : Fin n → normOne (unitaryInvolution K p f)) (j : Fin n) (A : Su K p f 2) :
    ((torusEquiv (unitaryInvolution K p f) n s : torus (unitaryInvolution K p f) (n + 1)) :
        Su K p f (n + 1)) * blockEmb2 K p f n j A *
      ((torusEquiv (unitaryInvolution K p f) n s : torus (unitaryInvolution K p f) (n + 1)) :
        Su K p f (n + 1))⁻¹ =
      blockEmb2 K p f n j
        (conjDiag hK (fun x : Fin 2 => ratio s ⟨j.val + x.val, by have := x.isLt; omega⟩) A) := by
  rw [coe_torusEquiv]
  exact diagSU_mul_blockEmb_mul_inv hK _ _ _ A

theorem blockEmb2_torusTwo_mul_blockEmb2_mul_inv (hK : Nat.card K = (p ^ f) ^ 2) (k j : Fin n)
    (u : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    blockEmb2 K p f n k (torusTwo (unitaryInvolution K p f) u) * blockEmb2 K p f n j A *
        (blockEmb2 K p f n k (torusTwo (unitaryInvolution K p f) u))⁻¹ =
      blockEmb2 K p f n j
        (conjDiag hK (fun x : Fin 2 =>
          if j.val + x.val = k.val then u
          else if j.val + x.val = k.val + 1 then u⁻¹ else 1) A) := by
  rw [← coe_torusEquiv_mulSingle, coe_torusEquiv_mul_blockEmb2_mul_inv hK]
  simp only [ratio_mulSingle]

theorem exists_torusTwo_of_mem_torus (k : Fin n)
    {t : Su K p f (n + 1)} (ht : t ∈ torus (unitaryInvolution K p f) (n + 1))
    (hk : t ∈ (blockEmb2 K p f n k).range) :
    ∃ u : normOne (unitaryInvolution K p f),
      blockEmb2 K p f n k (torusTwo (unitaryInvolution K p f) u) = t := by
  obtain ⟨A, rfl⟩ := hk
  rw [mem_torus_iff] at ht
  change ∀ a b : Fin (n + 1), a ≠ b →
    ((blockEmb K p f (n + 1) 2 k.val (by omega) A : Su K p f (n + 1)) :
      GL (Fin (n + 1)) K).val a b = 0 at ht
  set M : Matrix (Fin 2) (Fin 2) K := ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hM
  have hoff : ∀ x y : Fin 2, x ≠ y → M x y = 0 := by
    intro x y hxy
    have h := ht (blockIdx k.val (by omega) x) (blockIdx k.val (by omega) y)
      (fun h => hxy (blockIdx_injective _ h))
    rw [coe_coe_blockEmb, blockMat_apply_blockIdx] at h
    exact h
  have hdiag : M = Matrix.diagonal fun x => M x x := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hxy, hoff x y hxy]
  have hdet : M 0 0 * M 1 1 = 1 := by
    have := A.2.1
    rw [← hM, hdiag, Matrix.det_diagonal, Fin.prod_univ_two] at this
    exact this
  have hnorm : unitaryInvolution K p f (M 0 0) * M 0 0 = 1 := by
    have h2 := congrFun (congrFun A.2.2 0) 0
    rw [← hM, Matrix.mul_apply, Fin.sum_univ_two, hoff 1 0 (by decide)] at h2
    simpa [conjTr] using h2
  have hne : M 0 0 ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hdet
    exact zero_ne_one hdet
  refine ⟨⟨Units.mk0 (M 0 0) hne, hnorm⟩, ?_⟩
  have h1 : M 1 1 = (M 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  refine congrArg (blockEmb2 K p f n k) (Subtype.ext (Units.ext ?_))
  rw [coe_torusTwo, ← hM]
  conv_rhs => rw [hdiag]
  congr 1
  funext i
  fin_cases i
  · simp
  · simp [h1]

theorem torus_inf_range_blockEmb2 (k : Fin n) :
    torus (unitaryInvolution K p f) (n + 1) ⊓ (blockEmb2 K p f n k).range =
      ((blockEmb2 K p f n k).comp (torusTwo (unitaryInvolution K p f))).range := by
  ext t
  constructor
  · rintro ⟨ht, hk⟩
    obtain ⟨u, hu⟩ := exists_torusTwo_of_mem_torus k ht hk
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    refine ⟨?_, ⟨_, rfl⟩⟩
    rw [MonoidHom.comp_apply, ← coe_torusEquiv_mulSingle]
    exact (torusEquiv (unitaryInvolution K p f) n (Pi.mulSingle k u)).2

end TorusEquivSU

end CFSG.ClassicalInvolution.Phan
