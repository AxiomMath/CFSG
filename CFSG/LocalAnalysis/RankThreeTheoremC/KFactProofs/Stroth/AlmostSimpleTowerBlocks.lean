module

public import CFSG.LieType.SeitzGeneration.ThreeIndepBlock

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Block

variable {F : Type*} [Field F] {e r n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def blkMat (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n) :
    (ι → Matrix (Fin e) (Fin e) F) →* Matrix (Fin n) (Fin n) F where
  toFun X := reindex σ σ (fromBlocks (blockDiagonal X) 0 0 1)
  map_one' := by
    rw [blockDiagonal_one, fromBlocks_one, reindex_apply, submatrix_one_equiv]
  map_mul' X Y := by
    have hXY : blockDiagonal (X * Y) = blockDiagonal X * blockDiagonal Y := blockDiagonal_mul X Y
    rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv _ _ _ σ.symm,
      fromBlocks_multiply, hXY]
    simp

theorem blkMat_apply (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n) (X : ι → Matrix (Fin e) (Fin e) F) :
    blkMat σ X = reindex σ σ (fromBlocks (blockDiagonal X) 0 0 1) := rfl

theorem det_blkMat (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n) (X : ι → Matrix (Fin e) (Fin e) F) :
    (blkMat σ X).det = ∏ t, (X t).det := by
  rw [blkMat_apply, det_reindex_self, det_fromBlocks_zero₂₁, det_blockDiagonal, det_one,
    mul_one]

theorem blkMat_injective (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n) :
    Function.Injective (blkMat (F := F) σ) := by
  intro X Y h
  rw [blkMat_apply, blkMat_apply] at h
  have h1 := (reindex σ σ).injective h
  obtain ⟨h2, -⟩ := fromBlocks_inj.1 h1
  exact blockDiagonal_injective h2

theorem blkMat_map {K : Type*} [Field K] (φ : F →+* K) (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n)
    (X : ι → Matrix (Fin e) (Fin e) F) :
    (blkMat σ X).map φ = blkMat σ (fun t => (X t).map φ) := by
  rw [blkMat_apply, blkMat_apply, reindex_apply, reindex_apply, ← submatrix_map,
    fromBlocks_map, blockDiagonal_map _ _ (map_zero φ)]
  simp [Matrix.map_zero, Matrix.map_one, map_zero, map_one]

@[expose] noncomputable def blkSL (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n) :
    (ι → SpecialLinearGroup (Fin e) F) →* SpecialLinearGroup (Fin n) F where
  toFun h := ⟨blkMat σ (fun t => (h t : Matrix (Fin e) (Fin e) F)), by
    rw [det_blkMat]
    simp⟩
  map_one' := by
    apply Subtype.ext
    change blkMat σ (fun t => (((1 : ι → SpecialLinearGroup (Fin e) F) t :
      SpecialLinearGroup (Fin e) F) : Matrix (Fin e) (Fin e) F)) = 1
    have : (fun t => (((1 : ι → SpecialLinearGroup (Fin e) F) t :
        SpecialLinearGroup (Fin e) F) : Matrix (Fin e) (Fin e) F)) = 1 := by
      funext t
      simp
    rw [this, map_one]
  map_mul' h k := by
    apply Subtype.ext
    change blkMat σ (fun t => (((h * k) t : SpecialLinearGroup (Fin e) F) :
      Matrix (Fin e) (Fin e) F)) = blkMat σ (fun t => (h t : Matrix (Fin e) (Fin e) F)) *
        blkMat σ (fun t => (k t : Matrix (Fin e) (Fin e) F))
    have : (fun t => (((h * k) t : SpecialLinearGroup (Fin e) F) : Matrix (Fin e) (Fin e) F)) =
        (fun t => (h t : Matrix (Fin e) (Fin e) F)) *
          fun t => (k t : Matrix (Fin e) (Fin e) F) := by
      funext t
      simp
    rw [this, map_mul]

theorem blkSL_injective (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n) :
    Function.Injective (blkSL (F := F) σ) := by
  intro h k hhk
  have h1 := blkMat_injective σ (congrArg Subtype.val hhk)
  funext t
  exact Subtype.ext (congrFun h1 t)

theorem map_blkSL {K : Type*} [Field K] (φ : F →+* K) (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n)
    (h : ι → SpecialLinearGroup (Fin e) F) :
    SpecialLinearGroup.map φ (blkSL σ h) =
      blkSL σ (fun t => SpecialLinearGroup.map φ (h t)) := by
  apply Subtype.ext
  change (blkMat σ (fun t => (h t : Matrix (Fin e) (Fin e) F))).map φ =
    blkMat σ (fun t => ((SpecialLinearGroup.map φ (h t) : SpecialLinearGroup (Fin e) K) :
      Matrix (Fin e) (Fin e) K))
  rw [blkMat_map]
  rfl

end Block

section Independence

theorem two_indep_of_blockHom {G H Q : Type*} [Group G] [Group H] [Group Q] {p : ℕ}
    (φ : (Fin 2 → G) →* H) (hφ : Function.Injective φ) (π : H →* Q) {g : G}
    (hg : orderOf g = p) (hker : ∀ y : H, π y = 1 → y ^ p = 1 → y = 1) :
    Commute (π (φ (Pi.mulSingle 0 g))) (π (φ (Pi.mulSingle 1 g))) ∧
      π (φ (Pi.mulSingle 0 g)) ^ p = 1 ∧ π (φ (Pi.mulSingle 1 g)) ^ p = 1 ∧
      ∀ i j : ℤ, π (φ (Pi.mulSingle 0 g)) ^ i * π (φ (Pi.mulSingle 1 g)) ^ j = 1 →
        (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
  have hgp : g ^ p = 1 := hg ▸ pow_orderOf_eq_one g
  obtain ⟨x, hx⟩ : ∃ x : Fin 2 → H, x = fun t => φ (Pi.mulSingle t g) := ⟨_, rfl⟩
  have hxt : ∀ t, x t = φ (Pi.mulSingle t g) := fun t => by rw [hx]
  have hcomm : Commute (x 0) (x 1) := by
    rw [hxt, hxt]
    exact (Pi.mulSingle_apply_commute (fun _ : Fin 2 => g) 0 1).map φ
  have hpow : ∀ t, x t ^ p = 1 := fun t => by
    rw [hxt, ← map_pow, ← Pi.mulSingle_pow, hgp, Pi.mulSingle_one, map_one]
  have hprod : ∀ i j : ℤ, x 0 ^ i * x 1 ^ j =
      φ (Pi.mulSingle 0 (g ^ i) * Pi.mulSingle 1 (g ^ j)) := by
    intro i j
    rw [hxt, hxt, map_mul, ← map_zpow, ← map_zpow, ← Pi.mulSingle_zpow, ← Pi.mulSingle_zpow]
  rw [← hxt 0, ← hxt 1]
  refine ⟨hcomm.map π, ?_, ?_, fun i j h => ?_⟩
  · rw [← map_pow, hpow, map_one]
  · rw [← map_pow, hpow, map_one]
  have hyp : (x 0 ^ i * x 1 ^ j) ^ p = 1 := by
    have c1 : Commute (x 0 ^ i) (x 1 ^ j) := (hcomm.zpow_left i).zpow_right j
    have key : ∀ (t : Fin 2) (m : ℤ), (x t ^ m) ^ p = 1 := fun t m => by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hpow,
        _root_.one_zpow]
    rw [c1.mul_pow, key, key, one_mul]
  have hy1 : x 0 ^ i * x 1 ^ j = 1 := by
    refine hker _ ?_ hyp
    rw [map_mul, map_zpow, map_zpow]
    exact h
  rw [hprod] at hy1
  have h2 := hφ (hy1.trans (map_one _).symm)
  have e0 := congrFun h2 0
  have e1 := congrFun h2 1
  simp only [Pi.mul_apply, Pi.one_apply] at e0 e1
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), mul_one] at e0
  rw [Pi.mulSingle_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), Pi.mulSingle_eq_same, one_mul] at e1
  refine ⟨?_, ?_⟩
  · rw [← hg]; exact orderOf_dvd_iff_zpow_eq_one.2 e0
  · rw [← hg]; exact orderOf_dvd_iff_zpow_eq_one.2 e1

variable {K : Type} [Field K] [Finite K] {p n : ℕ}

theorem eq_one_of_mem_scalars_of_pow_eq_one (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1)
    (hn : 0 < n) {y : SpecialLinearGroup (Fin n) K} (hy : y ∈ scalars n K) (hyp : y ^ p = 1) :
    y = 1 := by
  obtain ⟨c, -, hyc⟩ := hy
  have hcp : c ^ p = 1 := by
    have h1 : ((y ^ p : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [hyp]
      rfl
    rw [Matrix.SpecialLinearGroup.coe_pow, hyc, ← map_pow] at h1
    have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
    rw [scalar_apply, diagonal_apply_eq, one_apply_eq] at h2
    exact Units.ext (by simpa using h2)
  have hcq : c ^ (Nat.card K - 1) = 1 := by
    rw [← Nat.card_units]
    exact pow_card_eq_one'
  have hcop : Nat.Coprime p (Nat.card K - 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpK
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hcp, hcq⟩
    rwa [hcop, pow_one] at this
  apply Subtype.ext
  rw [hyc, hc1]
  simp

theorem two_indep_blocks (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1) (hn : 0 < n) {e r : ℕ}
    (σ : (Fin e × Fin 2) ⊕ Fin r ≃ Fin n) {g : SpecialLinearGroup (Fin e) K} (hg : orderOf g = p) :
    Commute (proj n K (blkSL σ (Pi.mulSingle 0 g))) (proj n K (blkSL σ (Pi.mulSingle 1 g))) ∧
      proj n K (blkSL σ (Pi.mulSingle 0 g)) ^ p = 1 ∧
      proj n K (blkSL σ (Pi.mulSingle 1 g)) ^ p = 1 ∧
      ∀ i j : ℤ, proj n K (blkSL σ (Pi.mulSingle 0 g)) ^ i *
        proj n K (blkSL σ (Pi.mulSingle 1 g)) ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
  refine two_indep_of_blockHom (blkSL σ) (blkSL_injective σ) (proj n K) hg ?_
  intro y hy hyp
  exact eq_one_of_mem_scalars_of_pow_eq_one hp hpK hn (proj_eq_one_iff.1 hy) hyp

end Independence

section PrimeField

variable {K : Type} [Field K] [Finite K]

theorem exists_two_indep_fixed_blocks {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 ≤ p) (hpℓ : p ≠ ℓ) (hpK : ¬ p ∣ Nat.card K - 1) {n : ℕ} (hn : 2 * (p - 1) ≤ n) :
    ∃ x₁ x₂ : projectiveSL n K, Commute x₁ x₂ ∧ x₁ ^ p = 1 ∧ x₂ ^ p = 1 ∧
      (∀ i j : ℤ, x₁ ^ i * x₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) ∧
      ∀ σ : K ≃+* K, fieldAut n K σ x₁ = x₁ ∧ fieldAut n K σ x₂ = x₂ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have he1 : 1 ≤ p - 1 := by omega
  have hcardℓ : Nat.card (ZMod ℓ) = ℓ := Nat.card_zmod ℓ
  have hpe : p ∣ Nat.card (ZMod ℓ) ^ (p - 1) - 1 := by
    rw [hcardℓ]
    have hz : ((ℓ : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp Fact.out).1 hd)
    have h2 : ((ℓ : ℕ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hz
    have h4 : ℓ ^ (p - 1) ≡ 1 [MOD p] := by
      refine (ZMod.natCast_eq_natCast_iff _ _ _).1 ?_
      push_cast
      exact h2
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos)).1 h4.symm
  have hp1 : ¬ p ∣ Nat.card (ZMod ℓ) - 1 := by
    rw [hcardℓ]
    intro hd
    apply hpK
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨f, -, hf⟩ := FiniteField.card K ℓ
    have hKf : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
    rw [hKf]
    refine hd.trans ?_
    simpa using Nat.sub_dvd_pow_sub_pow ℓ 1 (f : ℕ)
  obtain ⟨g₀, hg₀⟩ := CFSG.LieType.SeitzGeneration.exists_sl_orderOf_eq (F := ZMod ℓ) he1 hp
    hpe hp1
  let φ : ZMod ℓ →+* K := ZMod.castHom (dvd_refl ℓ) K
  have hφinj : Function.Injective φ := φ.injective
  have hmapinj : Function.Injective (SpecialLinearGroup.map (n := Fin (p - 1)) φ) :=
    fun a b h => Subtype.ext (Matrix.map_injective hφinj (congrArg Subtype.val h))
  set g : SpecialLinearGroup (Fin (p - 1)) K := SpecialLinearGroup.map φ g₀ with hgdef
  have hg : orderOf g = p := (orderOf_injective _ hmapinj g₀).trans hg₀
  let σ₂ : (Fin (p - 1) × Fin 2) ⊕ Fin (n - 2 * (p - 1)) ≃ Fin n :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
      (finSumFinEquiv.trans (finCongr (by omega)))
  have hn0 : 0 < n := by omega
  obtain ⟨hc, h0, h1, hi⟩ := two_indep_blocks hp hpK hn0 σ₂ hg
  refine ⟨_, _, hc, h0, h1, hi, fun τ => ?_⟩
  have hτg : SpecialLinearGroup.map τ.toRingHom g = g := by
    have hτφ : τ.toRingHom.comp φ = φ := RingHom.ext_zmod _ _
    apply Subtype.ext
    rw [hgdef]
    ext i j
    have := congrArg (fun f : ZMod ℓ →+* K => f ((g₀ : Matrix (Fin (p - 1)) (Fin (p - 1)) (ZMod ℓ)) i j))
      hτφ
    simpa using this
  have hmul : ∀ t : Fin 2, fieldAut n K τ (proj n K (blkSL σ₂ (Pi.mulSingle t g))) =
      proj n K (blkSL σ₂ (Pi.mulSingle t g)) := by
    intro t
    rw [fieldAut_proj, map_blkSL]
    congr 2
    funext s
    by_cases hst : s = t
    · subst hst
      simp only [Pi.mulSingle_eq_same]
      exact hτg
    · simp [Pi.mulSingle_eq_of_ne hst]
  exact ⟨hmul 0, hmul 1⟩

end PrimeField

section Unipotent

variable {K : Type} [Field K] {n : ℕ}

@[expose] def uMat (hn : 3 ≤ n) (a b : K) : Matrix (Fin n) (Fin n) K :=
  1 + Matrix.single (⟨0, by omega⟩ : Fin n) ⟨2, by omega⟩ a +
    Matrix.single (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩ b

theorem uMat_mul (hn : 3 ≤ n) (a b a' b' : K) :
    uMat hn a b * uMat hn a' b' = uMat hn (a + a') (b + b') := by
  have h02 : (⟨2, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨2, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  simp only [uMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ h02 _, Matrix.single_mul_single_of_ne _ _ _ _ h12 _,
    Matrix.single_add]
  abel

theorem uMat_zero (hn : 3 ≤ n) : uMat hn (0 : K) 0 = 1 := by
  simp [uMat]

theorem det_uMat (hn : 3 ≤ n) (a b : K) : (uMat hn a b).det = 1 := by
  have h12 : (⟨2, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h : uMat hn a b = Matrix.transvection (⟨0, by omega⟩ : Fin n) ⟨2, by omega⟩ a *
      Matrix.transvection (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩ b := by
    simp only [uMat, Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.single_mul_single_of_ne _ _ _ _ h12 _]
    abel
  rw [h, Matrix.det_mul, Matrix.det_transvection_of_ne _ _ (by simp [Fin.ext_iff]),
    Matrix.det_transvection_of_ne _ _ (by simp [Fin.ext_iff]), one_mul]

@[expose] def uHom (hn : 3 ≤ n) : Multiplicative (K × K) →* SpecialLinearGroup (Fin n) K where
  toFun x := ⟨uMat hn (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2, det_uMat hn _ _⟩
  map_one' := Subtype.ext (uMat_zero hn)
  map_mul' x y := Subtype.ext (by
    change uMat hn (Multiplicative.toAdd (x * y)).1 (Multiplicative.toAdd (x * y)).2 =
      uMat hn (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 *
        uMat hn (Multiplicative.toAdd y).1 (Multiplicative.toAdd y).2
    rw [uMat_mul]
    rfl)

theorem coe_uHom (hn : 3 ≤ n) (a b : K) :
    ((uHom hn (Multiplicative.ofAdd (a, b)) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = uMat hn a b := rfl

theorem uMat_apply_zero_two (hn : 3 ≤ n) (a b : K) :
    uMat hn a b ⟨0, by omega⟩ ⟨2, by omega⟩ = a := by
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h10 : (⟨1, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  simp [uMat, Matrix.one_apply_ne h02, Matrix.single_apply, h10]

theorem uMat_apply_one_two (hn : 3 ≤ n) (a b : K) :
    uMat hn a b ⟨1, by omega⟩ ⟨2, by omega⟩ = b := by
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  simp [uMat, Matrix.one_apply_ne h12, Matrix.single_apply, h01]

theorem exists_two_indep_fixed_unip {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hn : 3 ≤ n) :
    ∃ x₁ x₂ : projectiveSL n K, Commute x₁ x₂ ∧ x₁ ^ ℓ = 1 ∧ x₂ ^ ℓ = 1 ∧
      (∀ i j : ℤ, x₁ ^ i * x₂ ^ j = 1 → (ℓ : ℤ) ∣ i ∧ (ℓ : ℤ) ∣ j) ∧
      ∀ σ : K ≃+* K, fieldAut n K σ x₁ = x₁ ∧ fieldAut n K σ x₂ = x₂ := by
  set y₁ : SpecialLinearGroup (Fin n) K := uHom hn (Multiplicative.ofAdd ((1 : K), (0 : K)))
    with hy₁
  set y₂ : SpecialLinearGroup (Fin n) K := uHom hn (Multiplicative.ofAdd ((0 : K), (1 : K)))
    with hy₂
  have hzpow : ∀ (a b : K) (m : ℤ), (uHom hn (Multiplicative.ofAdd (a, b))) ^ m =
      uHom hn (Multiplicative.ofAdd (m • a, m • b)) := by
    intro a b m
    rw [← map_zpow]
    congr 1
  have hcomm : Commute y₁ y₂ := by
    apply Subtype.ext
    change uMat hn 1 0 * uMat hn 0 1 = uMat hn 0 1 * uMat hn 1 0
    rw [uMat_mul, uMat_mul, add_comm, add_comm (0 : K)]
  refine ⟨proj n K y₁, proj n K y₂, hcomm.map _, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hy₁]
    have : (uHom hn (Multiplicative.ofAdd ((1 : K), (0 : K)))) ^ ℓ = 1 := by
      have h := hzpow 1 0 (ℓ : ℤ)
      rw [zpow_natCast] at h
      rw [h]
      have : ((ℓ : ℤ) • (1 : K), (ℓ : ℤ) • (0 : K)) = ((0 : K), (0 : K)) := by
        simp
      rw [this]
      exact map_one _
    rw [this, map_one]
  · rw [← map_pow, hy₂]
    have : (uHom hn (Multiplicative.ofAdd ((0 : K), (1 : K)))) ^ ℓ = 1 := by
      have h := hzpow 0 1 (ℓ : ℤ)
      rw [zpow_natCast] at h
      rw [h]
      have : ((ℓ : ℤ) • (0 : K), (ℓ : ℤ) • (1 : K)) = ((0 : K), (0 : K)) := by
        simp
      rw [this]
      exact map_one _
    rw [this, map_one]
  · intro i j hij
    have h1 : proj n K (y₁ ^ i * y₂ ^ j) = 1 := by
      rw [map_mul, map_zpow, map_zpow]
      exact hij
    have hmem := proj_eq_one_iff.1 h1
    obtain ⟨c, -, hc⟩ := hmem
    have hprod : y₁ ^ i * y₂ ^ j = uHom hn (Multiplicative.ofAdd ((i : K), (j : K))) := by
      rw [hy₁, hy₂, hzpow, hzpow, ← map_mul, ← ofAdd_add]
      congr 2
      simp
    rw [hprod, coe_uHom] at hc
    have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
    have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
    have e1 := congrFun (congrFun hc ⟨0, by omega⟩) ⟨2, by omega⟩
    have e2 := congrFun (congrFun hc ⟨1, by omega⟩) ⟨2, by omega⟩
    rw [uMat_apply_zero_two, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h02] at e1
    rw [uMat_apply_one_two, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h12] at e2
    exact ⟨(CharP.intCast_eq_zero_iff K ℓ i).1 e1, (CharP.intCast_eq_zero_iff K ℓ j).1 e2⟩
  · intro τ
    have hfix : ∀ a b : K, τ a = a → τ b = b →
        fieldAut n K τ (proj n K (uHom hn (Multiplicative.ofAdd (a, b)))) =
          proj n K (uHom hn (Multiplicative.ofAdd (a, b))) := by
      intro a b ha hb
      rw [fieldAut_proj]
      congr 1
      apply Subtype.ext
      change (uMat hn a b).map τ = uMat hn a b
      have h : (uMat hn a b).map τ = uMat hn (τ a) (τ b) := by
        simp [uMat, Matrix.map_add, Matrix.map_single]
      rw [h, ha, hb]
    exact ⟨hfix 1 0 (map_one τ) (map_zero τ), hfix 0 1 (map_zero τ) (map_one τ)⟩

end Unipotent

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
