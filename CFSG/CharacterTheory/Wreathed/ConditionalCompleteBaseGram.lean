module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseBridge
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseFamily
public import CFSG.CharacterTheory.Wreathed.ConditionalFirstFourierRowsCharacters
public import CFSG.CharacterTheory.Wreathed.ConditionalFirstFourierRowsCore

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.ConditionalFiveFixed CFSG.Wreathed.ConditionalOddFourier
  CFSG.Wreathed.ConditionalFirstFourierRows

section Columns

variable {ι : Type*} {B : Finset ι}

theorem int_sum_conj {a b : ι → ℂ} {z w : ι → ℤ} (ha : ∀ φ ∈ B, a φ = z φ)
    (hb : ∀ φ ∈ B, b φ = w φ) {k : ℤ} (h : ∑ φ ∈ B, a φ * conj (b φ) = k) :
    ∑ φ ∈ B, z φ * w φ = k := by
  rw [Finset.sum_congr rfl fun φ hφ => by rw [ha φ hφ, hb φ hφ, map_intCast (starRingEnd ℂ)]]
    at h
  exact_mod_cast h

theorem int_sum_cast {a : ι → ℂ} {z w : ι → ℤ} (ha : ∀ φ ∈ B, a φ = z φ) {k : ℤ}
    (h : ∑ φ ∈ B, a φ * (w φ : ℂ) = k) : ∑ φ ∈ B, z φ * w φ = k := by
  rw [Finset.sum_congr rfl fun φ hφ => by rw [ha φ hφ]] at h
  exact_mod_cast h

theorem natCast_zmod_ne {m a b : ℕ} (ha : a < m) (hb : b < m) (h : a ≠ b) :
    (a : ZMod m) ≠ (b : ZMod m) := by
  rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact h

theorem natCast_zmod_ne_zero {m a : ℕ} (h0 : 0 < a) (ha : a < m) : (a : ZMod m) ≠ 0 := by
  have h := natCast_zmod_ne ha (b := 0) (by omega) (by omega)
  rwa [Nat.cast_zero] at h

variable [DecidableEq ι]

theorem baseFamily_of_columns {p A Bq Dq ω : ι} {σ τ₀ κ : ℤ} {J : Finset ℕ} {χ : ℕ → ι}
    {m M : ℕ} (hm : m = 2 * M) (hM : 2 ≤ M) (hJm : ∀ j ∈ J, j ∈ Finset.Ico 1 m)
    {yc xc : ℕ → ι → ℤ} (cb : ZMod m → ZMod m → ι → ℂ) (Cz : ZMod m → ZMod m → ι → ℤ)
    (hCz : ∀ i j, ∀ φ ∈ B, cb i j φ = Cz i j φ) (Xc : ZMod m → ι → ℂ)
    (hXc : ∀ j ∈ Finset.Ico 1 m, ∀ φ ∈ B, Xc (j : ZMod m) φ = xc j φ)
    (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ (yc 0) (Cz M M) xc)
    {γ : ℕ → Fin 4 → ι} {ε : ℕ → Fin 4 → ℤ}
    (hQ : ∀ r ∈ Finset.Ico 1 M,
      Quadruple B p A Bq Dq ω σ τ₀ κ J χ (γ r) (ε r) (xc (m - 2 * r)) (yc r))
    (hdisj : ∀ r ∈ Finset.Ico 1 M, ∀ t ∈ Finset.Ico 1 M, r ≠ t → ∀ l l', γ r l ≠ γ t l')
    {V : Finset (ZMod m × ZMod m)} (hV0 : ∀ I ∈ V, I ≠ (0, 0))
    (hcprin : ∀ i j, (i, j) ≠ (0, 0) → cb i j p = 1)
    (hgram : (∀ r : ZMod m, r ≠ 0 → ∑ φ ∈ B, cb r r φ * conj (cb r r φ) = 8) ∧
      (∀ I ∈ V, ∑ φ ∈ B, cb I.1 I.2 φ * conj (cb I.1 I.2 φ) = 7) ∧
      (∀ r r' : ZMod m, r ≠ 0 → r' ≠ 0 → r ≠ r' →
        ∑ φ ∈ B, cb r r φ * conj (cb r' r' φ) = 6) ∧
      (∀ r : ZMod m, r ≠ 0 → ∀ I ∈ V,
        ∑ φ ∈ B, cb r r φ * conj (cb I.1 I.2 φ) = 6 ∧
          ∑ φ ∈ B, cb I.1 I.2 φ * conj (cb r r φ) = 6) ∧
      ∀ I ∈ V, ∀ I' ∈ V, I ≠ I' → ∑ φ ∈ B, cb I.1 I.2 φ * conj (cb I'.1 I'.2 φ) = 6)
    (hcX : ∀ i j, ∀ j' ∈ Finset.Ico 1 m, ∑ φ ∈ B, cb i j φ * conj (Xc j' φ) = 0)
    (hcY : ∀ i j, ∀ r < M, ∑ φ ∈ B, cb i j φ * (yc r φ : ℂ) = 0)
    (hcpar : ∀ j ∈ Finset.Ico 1 m, Even j → ∀ r : ZMod m, 2 * r = -(j : ZMod m) → ∀ φ ∈ B,
      ∃ k : ℤ, Xc j φ - (cb M M φ + cb r r φ + cb (r + M) (r + M) φ) = 2 * k) :
    BaseFamily B p A Bq Dq ω σ τ₀ κ J χ (yc 0) (Cz M M) xc M γ ε (fun r => xc (m - 2 * r)) yc
      (fun r => Cz r r) (fun r => Cz ((r + M : ℕ) : ZMod m) ((r + M : ℕ) : ZMod m)) V
      (fun I => Cz I.1 I.2) := by
  obtain ⟨h8, h7, h6d, h6g, h6gg⟩ := hgram
  have hlt : ∀ r ∈ Finset.Ico 1 M, 0 < r ∧ r < m ∧ r + M < m ∧ r < M := fun r hr => by
    rw [Finset.mem_Ico] at hr
    omega
  have hMne : (M : ZMod m) ≠ 0 := natCast_zmod_ne_zero (by omega) (by omega)
  have hr0 : ∀ r ∈ Finset.Ico 1 M, (r : ZMod m) ≠ 0 := fun r hr =>
    natCast_zmod_ne_zero (hlt r hr).1 (hlt r hr).2.1
  have hrM0 : ∀ r ∈ Finset.Ico 1 M, ((r + M : ℕ) : ZMod m) ≠ 0 := fun r hr =>
    natCast_zmod_ne_zero (by omega) (hlt r hr).2.2.1
  have hrM : ∀ r ∈ Finset.Ico 1 M, (r : ZMod m) ≠ (M : ZMod m) := fun r hr =>
    natCast_zmod_ne (hlt r hr).2.1 (by omega) (by have := hlt r hr; omega)
  have hrMM : ∀ r ∈ Finset.Ico 1 M, ((r + M : ℕ) : ZMod m) ≠ (M : ZMod m) := fun r hr =>
    natCast_zmod_ne (hlt r hr).2.2.1 (by omega) (by have := (hlt r hr).1; omega)
  have hone : ∀ i j, (i, j) ≠ (0, 0) → Cz i j p = 1 := fun i j h => by
    have h' := hcprin i j h
    rw [hCz i j p hS.hp] at h'
    exact_mod_cast h'
  have hX : ∀ i j, ∀ j' ∈ Finset.Ico 1 m, ∑ φ ∈ B, Cz i j φ * xc j' φ = 0 := fun i j j' hj' =>
    int_sum_conj (hCz i j) (hXc j' hj') (k := 0) (by rw [hcX i j j' hj']; simp)
  have hY : ∀ i j, ∀ r < M, ∑ φ ∈ B, Cz i j φ * yc r φ = 0 := fun i j r hr =>
    int_sum_cast (hCz i j) (k := 0) (by rw [hcY i j r hr]; simp)
  have h8' : ∀ r : ZMod m, r ≠ 0 → ∑ φ ∈ B, Cz r r φ * Cz r r φ = 8 := fun r hr =>
    int_sum_conj (hCz r r) (hCz r r) (k := 8) (by rw [h8 r hr]; norm_num)
  have h7' : ∀ I ∈ V, ∑ φ ∈ B, Cz I.1 I.2 φ * Cz I.1 I.2 φ = 7 := fun I hI =>
    int_sum_conj (hCz I.1 I.2) (hCz I.1 I.2) (k := 7) (by rw [h7 I hI]; norm_num)
  have h6d' : ∀ r r' : ZMod m, r ≠ 0 → r' ≠ 0 → r ≠ r' →
      ∑ φ ∈ B, Cz r r φ * Cz r' r' φ = 6 := fun r r' hr hr' hrr' =>
    int_sum_conj (hCz r r) (hCz r' r') (k := 6) (by rw [h6d r r' hr hr' hrr']; norm_num)
  have h6g' : ∀ r : ZMod m, r ≠ 0 → ∀ I ∈ V, ∑ φ ∈ B, Cz I.1 I.2 φ * Cz r r φ = 6 :=
    fun r hr I hI => int_sum_conj (hCz I.1 I.2) (hCz r r) (k := 6)
      (by rw [(h6g r hr I hI).2]; norm_num)
  have h6gg' : ∀ I ∈ V, ∀ I' ∈ V, I ≠ I' → ∑ φ ∈ B, Cz I.1 I.2 φ * Cz I'.1 I'.2 φ = 6 :=
    fun I hI I' hI' hII' => int_sum_conj (hCz I.1 I.2) (hCz I'.1 I'.2) (k := 6)
      (by rw [h6gg I hI I' hI' hII']; norm_num)
  have hbase : ∀ i j, (i, j) ≠ (0, 0) → ∑ φ ∈ B, Cz i j φ * Cz M M φ = 6 →
      IsBaseColumn B p (yc 0) (Cz M M) J xc (Cz i j) := fun i j hij h6 =>
    ⟨hone i j hij, hY i j 0 (by omega), fun j' hj' => hX i j j' (hJm j' hj'), h6⟩
  have hpair0 : ∀ r : ZMod m, r ≠ 0 → (r, r) ≠ (0, 0) := fun r hr h =>
    hr (Prod.ext_iff.mp h).1
  have hdiagC : ∀ r : ZMod m, r ≠ 0 → r ≠ (M : ZMod m) →
      ∑ φ ∈ B, Cz r r φ * Cz M M φ = 6 := fun r hr hrM' => h6d' r M hr hMne hrM'
  have hkI : ∀ t ∈ Finset.Ico 1 M, m - 2 * t ∈ Finset.Ico 1 m := fun t ht => by
    have := hlt t ht
    rw [Finset.mem_Ico]
    omega
  refine ⟨hQ, hdisj, fun r hr => ⟨hbase r r (hpair0 _ (hr0 r hr)) (hdiagC _ (hr0 r hr) (hrM r hr)),
      hbase _ _ (hpair0 _ (hrM0 r hr)) (hdiagC _ (hrM0 r hr) (hrMM r hr))⟩,
    fun I hI => hbase I.1 I.2 (hV0 I hI) (h6g' M hMne I hI),
    fun r _ t ht => ⟨hX _ _ _ (hkI t ht), hY _ _ t (hlt t ht).2.2.2, hX _ _ _ (hkI t ht),
      hY _ _ t (hlt t ht).2.2.2⟩,
    fun I _ t ht => ⟨hX _ _ _ (hkI t ht), hY _ _ t (hlt t ht).2.2.2⟩,
    fun r hr => ⟨h8' _ (hr0 r hr), h8' _ (hrM0 r hr)⟩, h7',
    fun r hr => h6d' _ _ (hr0 r hr) (hrM0 r hr)
      (natCast_zmod_ne (hlt r hr).2.1 (hlt r hr).2.2.1 (by have := hlt r hr; omega)),
    fun r hr t ht hrt => ⟨h6d' _ _ (hr0 r hr) (hr0 t ht)
        (natCast_zmod_ne (hlt r hr).2.1 (hlt t ht).2.1 hrt),
      h6d' _ _ (hr0 r hr) (hrM0 t ht)
        (natCast_zmod_ne (hlt r hr).2.1 (hlt t ht).2.2.1 (by have := (hlt r hr).2.2.2; omega)),
      h6d' _ _ (hrM0 r hr) (hrM0 t ht)
        (natCast_zmod_ne (hlt r hr).2.2.1 (hlt t ht).2.2.1 (by omega))⟩,
    fun I hI r hr => ⟨h6g' _ (hr0 r hr) I hI, h6g' _ (hrM0 r hr) I hI⟩, h6gg',
    fun r hr φ hφ => ?_⟩
  have hlt' := hlt r hr
  have hev : Even (m - 2 * r) := ⟨M - r, by omega⟩
  have h2r : 2 * (r : ZMod m) = -((m - 2 * r : ℕ) : ZMod m) := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    push_cast
    ring
  obtain ⟨k, hk⟩ := hcpar (m - 2 * r) (hkI r hr) hev (r : ZMod m) h2r φ hφ
  rw [hXc _ (hkI r hr) φ hφ, hCz _ _ φ hφ, hCz _ _ φ hφ, hCz _ _ φ hφ] at hk
  have hk' : xc (m - 2 * r) φ - (Cz M M φ + Cz r r φ +
      Cz ((r : ZMod m) + M) ((r : ZMod m) + M) φ) = 2 * k := by exact_mod_cast hk
  have hcast : ((r + M : ℕ) : ZMod m) = (r : ZMod m) + M := by push_cast; rfl
  show Cz r r φ + Cz ((r + M : ℕ) : ZMod m) ((r + M : ℕ) : ZMod m) φ ≡
    xc (m - 2 * r) φ + Cz M M φ [ZMOD 2]
  rw [hcast]
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨-(Cz M M φ) - k, by linarith⟩)

end Columns

section Class

variable {G : Type} [Group G] [Fintype G] {basis : FiniteIrreducibleCharacterBasis G}
  {B : Finset basis.index} {p A Bq Dq ω : basis.index}

theorem coreSetting_of_class (hprincipal : (basis.representation p).character = 1)
    (hp : p ∈ B) (hA : A ∈ B) (hBq : Bq ∈ B) (hDq : Dq ∈ B) (hω : ω ∈ B) (hAp : A ≠ p)
    (hBp : Bq ≠ p) (hDp : Dq ≠ p) (hωp : ω ≠ p) (hBA : Bq ≠ A) (hDA : Dq ≠ A) (hωA : ω ≠ A)
    (hDB : Dq ≠ Bq) (hωB : ω ≠ Bq) (hωD : ω ≠ Dq) {σ τ₀ κ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hτ₀ : τ₀ = 1 ∨ τ₀ = -1) (hκ : κ = 1 ∨ κ = -1) {J : Finset ℕ} {χ : ℕ → basis.index}
    (hχB : ∀ j ∈ J, χ j ∈ B) (hχinj : Set.InjOn χ J)
    (hχcore : ∀ j ∈ J, χ j ≠ p ∧ χ j ≠ A ∧ χ j ≠ Bq ∧ χ j ≠ Dq ∧ χ j ≠ ω)
    {y₀ C : basis.index → ℤ} {xj : ℕ → basis.index → ℤ}
    (hY : basisCombination basis B y₀ = 1 + (σ : ℂ) • (basis.representation A).character -
      (τ₀ : ℂ) • (basis.representation Bq).character +
      (κ : ℂ) • (basis.representation Dq).character)
    (hX : ∀ j ∈ J, basisCombination basis B (xj j) =
      -1 - (σ : ℂ) • (basis.representation A).character -
        (τ₀ : ℂ) • (basis.representation Bq).character +
        (κ : ℂ) • (basis.representation Dq).character +
        (2 * σ : ℂ) • (basis.representation (χ j)).character)
    (hC : basisCombination basis B C = 1 - (σ : ℂ) • (basis.representation A).character -
      (τ₀ : ℂ) • (basis.representation Bq).character -
      (κ : ℂ) • (basis.representation Dq).character +
      (2 * τ₀ : ℂ) • (basis.representation ω).character) :
    CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj := by
  refine ⟨hp, hA, hBq, hDq, hω, hAp, hBp, hDp, hωp, hBA, hDA, hωA, hDB, hωB, hωD, hσ, hτ₀, hκ,
    hχB, hχinj, hχcore, fun φ hφ => ?_, fun j hj φ hφ => ?_, fun φ hφ => ?_⟩
  · rw [← basisCombination_y0 hprincipal hp hA hBq hDq σ τ₀ κ] at hY
    exact eq_of_basisCombination_eq hY hφ
  · have h := hX j hj
    rw [← basisCombination_xj hprincipal hp hA hBq hDq (hχB j hj) σ τ₀ κ] at h
    exact eq_of_basisCombination_eq h hφ
  · rw [← basisCombination_C hprincipal hp hA hBq hDq hω σ τ₀ κ] at hC
    exact eq_of_basisCombination_eq hC hφ

theorem quadruple_of_class (hprincipal : (basis.representation p).character = 1)
    (hp : p ∈ B) (hA : A ∈ B) (hBq : Bq ∈ B) (hDq : Dq ∈ B) {σ τ₀ κ : ℤ} {J : Finset ℕ}
    {χ : ℕ → basis.index} {γ : Fin 4 → basis.index} {ε : Fin 4 → ℤ}
    (hinj : Function.Injective γ) (hmem : ∀ l, γ l ∈ B) (hsign : ∀ l, ε l = 1 ∨ ε l = -1)
    (hcore : ∀ l, γ l ≠ p ∧ γ l ≠ A ∧ γ l ≠ Bq ∧ γ l ≠ Dq ∧ γ l ≠ ω)
    (hodd : ∀ l, ∀ j ∈ J, γ l ≠ χ j) {xk yr : basis.index → ℤ}
    (hX : basisCombination basis B xk = -1 - (σ : ℂ) • (basis.representation A).character -
      (τ₀ : ℂ) • (basis.representation Bq).character +
      (κ : ℂ) • (basis.representation Dq).character +
      ∑ l, (ε l : ℂ) • (basis.representation (γ l)).character)
    (hY : basisCombination basis B yr = (ε 0 : ℂ) • (basis.representation (γ 0)).character +
      (ε 1 : ℂ) • (basis.representation (γ 1)).character -
      (ε 2 : ℂ) • (basis.representation (γ 2)).character -
      (ε 3 : ℂ) • (basis.representation (γ 3)).character) :
    Quadruple B p A Bq Dq ω σ τ₀ κ J χ γ ε xk yr := by
  refine ⟨hinj, hmem, hsign, hcore, hodd, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · rw [← basisCombination_xk hprincipal hp hA hBq hDq hmem σ τ₀ κ ε] at hX
    exact eq_of_basisCombination_eq hX hφ
  · rw [← basisCombination_yr hmem ε] at hY
    exact eq_of_basisCombination_eq hY hφ

end Class

end CFSG.Wreathed.ConditionalCompleteBase
