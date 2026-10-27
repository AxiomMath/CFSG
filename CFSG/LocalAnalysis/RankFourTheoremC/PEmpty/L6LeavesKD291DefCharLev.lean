module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharXfer
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.LinearAlgebra.Matrix.Notation
public import CFSG.Open.StatedDefs
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open Subgroup CFSG.Open

section Fil

variable {ι : Type} [Fintype ι]

@[expose] def Fil (K : Type) [Field K] (pos : ι → ℕ) (k : ℕ) : Submodule K (Matrix ι ι K) where
  carrier := {M | ∀ a b, pos b < pos a + k → M a b = 0}
  add_mem' {M N} hM hN := fun a b h => by simp [hM a b h, hN a b h]
  zero_mem' := fun a b _ => rfl
  smul_mem' c M hM := fun a b h => by simp [hM a b h]

variable {K : Type} [Field K] (pos : ι → ℕ)

theorem mem_Fil {M : Matrix ι ι K} {k : ℕ} :
    M ∈ Fil K pos k ↔ ∀ a b, pos b < pos a + k → M a b = 0 := Iff.rfl

theorem Fil_mono {j k : ℕ} (h : j ≤ k) : Fil K pos k ≤ Fil K pos j :=
  fun _ hM a b hab => hM a b (by omega)

theorem Fil_mul {j k : ℕ} {M N : Matrix ι ι K} (hM : M ∈ Fil K pos j) (hN : N ∈ Fil K pos k) :
    M * N ∈ Fil K pos (j + k) := by
  intro a c hac
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hab : pos b < pos a + j
  · rw [hM a b hab, zero_mul]
  · rw [hN b c (by omega), mul_zero]

theorem eq_zero_of_mem_Fil {k : ℕ} (hD : ∀ a b : ι, pos b < pos a + k) {M : Matrix ι ι K}
    (hM : M ∈ Fil K pos k) : M = 0 :=
  Matrix.ext fun a b => hM a b (hD a b)

theorem one_mem_Fil_zero [DecidableEq ι] : (1 : Matrix ι ι K) ∈ Fil K pos 0 := by
  intro a b hab
  have : a ≠ b := by
    rintro rfl
    omega
  exact Matrix.one_apply_ne this

theorem Fil_pow [DecidableEq ι] {j : ℕ} {M : Matrix ι ι K} (hM : M ∈ Fil K pos j) (n : ℕ) :
    M ^ n ∈ Fil K pos (n * j) := by
  induction n with
  | zero => simpa using one_mem_Fil_zero pos
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact Fil_mul pos ih hM

end Fil

section Lev

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {G : Type} [Group G]
  [Finite G] (ρ : G →* Matrix ι ι K) (pos : ι → ℕ)

def LevMonoid (k : ℕ) (hk : 1 ≤ k) : Submonoid G where
  carrier := {g | ρ g - 1 ∈ Fil K pos k}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    have e : ρ (g * h) - 1 = (ρ g - 1) * (ρ h - 1) + (ρ g - 1) + (ρ h - 1) := by
      rw [map_mul]
      noncomm_ring
    show ρ (g * h) - 1 ∈ Fil K pos k
    rw [e]
    exact add_mem (add_mem (Fil_mono pos (by omega : k ≤ k + k) (Fil_mul pos hg hh)) hg) hh

def Lev (k : ℕ) (hk : 1 ≤ k) : Subgroup G :=
  { LevMonoid ρ pos k hk with
    inv_mem' := by
      intro g hg
      have e : g⁻¹ = g ^ (orderOf g - 1) := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
      show g⁻¹ ∈ LevMonoid ρ pos k hk
      rw [e]
      exact (LevMonoid ρ pos k hk).pow_mem hg _ }

variable {ρ pos}

theorem mem_Lev {k : ℕ} {hk : 1 ≤ k} {g : G} :
    g ∈ Lev ρ pos k hk ↔ ρ g - 1 ∈ Fil K pos k := Iff.rfl

theorem Lev_mono {j k : ℕ} {hj : 1 ≤ j} {hk : 1 ≤ k} (h : j ≤ k) :
    Lev ρ pos k hk ≤ Lev ρ pos j hj :=
  fun _ hg => Fil_mono pos h hg

theorem commutator_mem_Lev {k : ℕ} {hk : 1 ≤ k} {g a : G} (hg : g ∈ Lev ρ pos 1 le_rfl)
    (ha : a ∈ Lev ρ pos k hk) : g * a * g⁻¹ * a⁻¹ ∈ Lev ρ pos (k + 1) (by omega) := by
  have hga : g⁻¹ * a⁻¹ ∈ Lev ρ pos 1 le_rfl :=
    mul_mem (inv_mem hg) (inv_mem (Lev_mono hk ha))
  have h0 : ρ (g⁻¹ * a⁻¹) ∈ Fil K pos 0 := by
    have : ρ (g⁻¹ * a⁻¹) = (ρ (g⁻¹ * a⁻¹) - 1) + 1 := by abel
    rw [this]
    exact add_mem (Fil_mono pos (Nat.zero_le 1) hga) (one_mem_Fil_zero pos)
  have e : ρ (g * a * g⁻¹ * a⁻¹) - 1 =
      ((ρ g - 1) * (ρ a - 1) - (ρ a - 1) * (ρ g - 1)) * ρ (g⁻¹ * a⁻¹) := by
    have h1 : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : ρ a * ρ a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have e1 : ρ (g * a * g⁻¹ * a⁻¹) = ρ g * ρ a * (ρ g⁻¹ * ρ a⁻¹) := by
      simp only [map_mul, mul_assoc]
    have e2 : ρ (g⁻¹ * a⁻¹) = ρ g⁻¹ * ρ a⁻¹ := map_mul _ _ _
    rw [e1, e2]
    calc ρ g * ρ a * (ρ g⁻¹ * ρ a⁻¹) - 1
        = ρ g * ρ a * (ρ g⁻¹ * ρ a⁻¹) - ρ a * (ρ g * ρ g⁻¹) * ρ a⁻¹ := by
          rw [h1, mul_one, h2]
      _ = _ := by noncomm_ring
  show ρ (g * a * g⁻¹ * a⁻¹) - 1 ∈ Fil K pos (k + 1)
  rw [e]
  have hX : ρ g - 1 ∈ Fil K pos 1 := hg
  have hY : ρ a - 1 ∈ Fil K pos k := ha
  have h1 : (ρ g - 1) * (ρ a - 1) ∈ Fil K pos (1 + k) := Fil_mul pos hX hY
  have h2 : (ρ a - 1) * (ρ g - 1) ∈ Fil K pos (k + 1) := Fil_mul pos hY hX
  have h3 : (ρ g - 1) * (ρ a - 1) - (ρ a - 1) * (ρ g - 1) ∈ Fil K pos (k + 1) :=
    sub_mem (by rwa [add_comm] at h1) h2
  have := Fil_mul pos h3 h0
  rwa [add_zero] at this

theorem Lev_comm (hρ : Function.Injective ρ) {k : ℕ} {hk : 1 ≤ k}
    (hD : ∀ a b : ι, pos b < pos a + 2 * k) {g h : G} (hg : g ∈ Lev ρ pos k hk)
    (hh : h ∈ Lev ρ pos k hk) : g * h = h * g := by
  apply hρ
  have e : ρ (g * h) - ρ (h * g) = (ρ g - 1) * (ρ h - 1) - (ρ h - 1) * (ρ g - 1) := by
    rw [map_mul, map_mul]
    noncomm_ring
  have h0 : (ρ g - 1) * (ρ h - 1) - (ρ h - 1) * (ρ g - 1) ∈ Fil K pos (k + k) :=
    sub_mem (Fil_mul pos hg hh) (Fil_mul pos hh hg)
  have := eq_zero_of_mem_Fil pos (k := k + k) (by simpa [two_mul] using hD) h0
  rw [← e] at this
  exact sub_eq_zero.mp this

theorem Lev_pow_apply {k : ℕ} {hk : 1 ≤ k} (hD : ∀ a b : ι, pos b < pos a + 2 * k) {g : G}
    (hg : g ∈ Lev ρ pos k hk) (n : ℕ) : ρ (g ^ n) = 1 + n • (ρ g - 1) := by
  have hsq : (ρ g - 1) * (ρ g - 1) = 0 :=
    eq_zero_of_mem_Fil pos (k := k + k) (by simpa [two_mul] using hD) (Fil_mul pos hg hg)
  set X : Matrix ι ι K := ρ g - 1 with hX
  have hg' : ρ g = 1 + X := by rw [hX]; abel
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul, ih, hg']
    have h1 : (1 + n • X) * (1 + X) = 1 + (n + 1) • X + n • (X * X) := by
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      noncomm_ring
    rw [h1, hsq, smul_zero, add_zero]

theorem Lev_pow_eq_one (hρ : Function.Injective ρ) {p : ℕ} [CharP K p] {k : ℕ} {hk : 1 ≤ k}
    (hD : ∀ a b : ι, pos b < pos a + 2 * k) {g : G} (hg : g ∈ Lev ρ pos k hk) : g ^ p = 1 := by
  apply hρ
  rw [Lev_pow_apply hD hg, map_one]
  have : p • (ρ g - 1) = 0 := by
    ext a b
    simp [Matrix.smul_apply, nsmul_eq_mul, CharP.cast_eq_zero]
  rw [this, add_zero]

theorem isPGroup_Lev (hρ : Function.Injective ρ) {p : ℕ} [hp : Fact p.Prime] [CharP K p]
    [Nonempty ι] {D : ℕ} (hD : ∀ a b : ι, pos b < pos a + D) :
    IsPGroup p (Lev ρ pos 1 le_rfl) := by
  intro g
  refine ⟨D, ?_⟩
  apply Subtype.ext
  show (g : G) ^ p ^ D = 1
  apply hρ
  have hX : ρ (g : G) - 1 ∈ Fil K pos 1 := g.2
  have hg' : ρ (g : G) = 1 + (ρ (g : G) - 1) := by abel
  rw [map_pow, hg', add_pow_char_pow_of_commute p D (Commute.one_left _), one_pow]
  have hlt : D < p ^ D := Nat.lt_pow_self hp.out.one_lt
  have h1 : (ρ (g : G) - 1) ^ p ^ D ∈ Fil K pos (p ^ D * 1) := Fil_pow pos hX _
  rw [mul_one] at h1
  have h0 := eq_zero_of_mem_Fil pos (k := D) hD (Fil_mono pos hlt.le h1)
  rw [h0, add_zero, map_one]

theorem Lev_pow_mul_apply {k : ℕ} {hk : 1 ≤ k} (hD : ∀ a b : ι, pos b < pos a + 2 * k)
    {g₁ g₂ : G} (h₁ : g₁ ∈ Lev ρ pos k hk) (h₂ : g₂ ∈ Lev ρ pos k hk) (i j : ℕ) :
    ρ (g₁ ^ i * g₂ ^ j) - 1 = i • (ρ g₁ - 1) + j • (ρ g₂ - 1) := by
  have hsq : (ρ g₁ - 1) * (ρ g₂ - 1) = 0 :=
    eq_zero_of_mem_Fil pos (k := k + k) (by simpa [two_mul] using hD) (Fil_mul pos h₁ h₂)
  rw [map_mul, Lev_pow_apply hD h₁, Lev_pow_apply hD h₂]
  have h3 : (i • (ρ g₁ - 1)) * (j • (ρ g₂ - 1)) = 0 := by
    rw [smul_mul_smul_comm, hsq, smul_zero]
  calc (1 + i • (ρ g₁ - 1)) * (1 + j • (ρ g₂ - 1)) - 1
      = i • (ρ g₁ - 1) + j • (ρ g₂ - 1) + (i • (ρ g₁ - 1)) * (j • (ρ g₂ - 1)) := by
        rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul]
        abel
    _ = _ := by rw [h3, add_zero]

theorem independent_of_entries {p : ℕ} [CharP K p] {k : ℕ} {hk : 1 ≤ k}
    (hD : ∀ a b : ι, pos b < pos a + 2 * k) {g₁ g₂ : G} (h₁ : g₁ ∈ Lev ρ pos k hk)
    (h₂ : g₂ ∈ Lev ρ pos k hk) {a₁ b₁ a₂ b₂ : ι} (hb₁ : pos b₁ = pos a₁ + k)
    (hb₂ : pos b₂ = pos a₂ + k) (e11 : (ρ g₁ - 1) a₁ b₁ = 1) (e12 : (ρ g₁ - 1) a₂ b₂ = 0)
    (e21 : (ρ g₂ - 1) a₁ b₁ = 0) (e22 : (ρ g₂ - 1) a₂ b₂ = 1) (i j : ℕ)
    (hmem : g₁ ^ i * g₂ ^ j ∈ Lev ρ pos (k + 1) (by omega)) : p ∣ i ∧ p ∣ j := by
  have key := Lev_pow_mul_apply hD h₁ h₂ i j
  have h0 : ρ (g₁ ^ i * g₂ ^ j) - 1 ∈ Fil K pos (k + 1) := hmem
  have z1 := h0 a₁ b₁ (by omega)
  have z2 := h0 a₂ b₂ (by omega)
  rw [key] at z1 z2
  simp only [Matrix.add_apply, Matrix.smul_apply, e11, e12, e21, e22] at z1 z2
  simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at z1 z2
  exact ⟨(CharP.cast_eq_zero_iff K p i).mp z1, (CharP.cast_eq_zero_iff K p j).mp z2⟩

theorem rankThreeCent_of_corner {p : ℕ} [hp : Fact p.Prime] [CharP K p] [Nonempty ι]
    {S : Type} [Group S] [Finite S] (hρ : Function.Injective ρ) {k : ℕ} (hk : 1 ≤ k)
    (hD : ∀ a b : ι, pos b < pos a + 2 * k) (π : G →* S) (hπ : Function.Surjective π)
    (hπinj : ∀ u ∈ Lev ρ pos 1 le_rfl, π u = 1 → u = 1)
    (hidx : ¬ p ∣ (Lev ρ pos 1 le_rfl).index) {g₁ g₂ b₀ : G} (h₁ : g₁ ∈ Lev ρ pos k hk)
    (h₂ : g₂ ∈ Lev ρ pos k hk) (hb₀ : b₀ ∈ Lev ρ pos (k + 1) (by omega)) (hb₀1 : b₀ ≠ 1)
    {a₁ b₁ a₂ b₂ : ι} (hb₁ : pos b₁ = pos a₁ + k) (hb₂ : pos b₂ = pos a₂ + k)
    (e11 : (ρ g₁ - 1) a₁ b₁ = 1) (e12 : (ρ g₁ - 1) a₂ b₂ = 0) (e21 : (ρ g₂ - 1) a₁ b₁ = 0)
    (e22 : (ρ g₂ - 1) a₂ b₂ = 1) : RankThreeCent p S := by
  have hk1 : 1 ≤ k + 1 := by omega
  have hU : IsPGroup p (Lev ρ pos 1 le_rfl) := isPGroup_Lev hρ (D := 2 * k) hD
  have hA : IsElemAbelian p (Lev ρ pos k hk) :=
    ⟨⟨⟨fun x y => Subtype.ext (Lev_comm hρ hD x.2 y.2)⟩⟩, fun g hg => Lev_pow_eq_one hρ hD hg⟩
  have hBA : Lev ρ pos (k + 1) hk1 ≤ Lev ρ pos k hk := Lev_mono (Nat.le_succ k)
  have hcard : Nat.card (Lev ρ pos (k + 1) hk1) * p ^ 2 ≤ Nat.card (Lev ρ pos k hk) :=
    card_mul_le_of_independent hA hBA h₁ h₂ fun i j hmem =>
      independent_of_entries hD h₁ h₂ hb₁ hb₂ e11 e12 e21 e22 i j hmem
  have hb₀p : orderOf b₀ = p :=
    orderOf_eq_prime (Lev_pow_eq_one hρ hD (hBA hb₀)) hb₀1
  have hBp : p ≤ Nat.card (Lev ρ pos (k + 1) hk1) := by
    have := Subgroup.card_le_of_le (zpowers_le.mpr hb₀)
    rwa [Nat.card_zpowers, hb₀p] at this
  refine rankThreeCent_of_witness_map π hπ hU hidx (Lev_mono hk) hBA hA
    (fun u hu a ha => commutator_mem_Lev hu ha) hcard (Or.inl ?_) hπinj
  calc p ^ 3 = p * p ^ 2 := by ring
    _ ≤ Nat.card (Lev ρ pos (k + 1) hk1) * p ^ 2 := Nat.mul_le_mul_right _ hBp
    _ ≤ _ := hcard

theorem independent_of_entry {p : ℕ} [CharP K p] {k : ℕ} {hk : 1 ≤ k}
    (hD : ∀ a b : ι, pos b < pos a + 2 * k) {g₁ g₂ : G} (h₁ : g₁ ∈ Lev ρ pos k hk)
    (h₂ : g₂ ∈ Lev ρ pos k hk) {a b : ι} (hb : pos b = pos a + k) {x₁ x₂ : K}
    (e₁ : (ρ g₁ - 1) a b = x₁) (e₂ : (ρ g₂ - 1) a b = x₂)
    (hx : ∀ i j : ℕ, (i : K) * x₁ + (j : K) * x₂ = 0 → p ∣ i ∧ p ∣ j) (i j : ℕ)
    (hmem : g₁ ^ i * g₂ ^ j ∈ Lev ρ pos (k + 1) (by omega)) : p ∣ i ∧ p ∣ j := by
  have key := Lev_pow_mul_apply hD h₁ h₂ i j
  have h0 : ρ (g₁ ^ i * g₂ ^ j) - 1 ∈ Fil K pos (k + 1) := hmem
  have z := h0 a b (by omega)
  rw [key] at z
  simp only [Matrix.add_apply, Matrix.smul_apply, e₁, e₂] at z
  simp only [nsmul_eq_mul] at z
  exact hx i j z

theorem rankThreeCent_of_corner_ind {p : ℕ} [hp : Fact p.Prime] [CharP K p] [Nonempty ι]
    {S : Type} [Group S] [Finite S] (hρ : Function.Injective ρ) {k : ℕ} (hk : 1 ≤ k)
    (hD : ∀ a b : ι, pos b < pos a + 2 * k) (π : G →* S) (hπ : Function.Surjective π)
    (hπinj : ∀ u ∈ Lev ρ pos 1 le_rfl, π u = 1 → u = 1)
    (hidx : ¬ p ∣ (Lev ρ pos 1 le_rfl).index) {g₁ g₂ b₀ : G} (h₁ : g₁ ∈ Lev ρ pos k hk)
    (h₂ : g₂ ∈ Lev ρ pos k hk) (hb₀ : b₀ ∈ Lev ρ pos (k + 1) (by omega)) (hb₀1 : b₀ ≠ 1)
    (hind : ∀ i j : ℕ, g₁ ^ i * g₂ ^ j ∈ Lev ρ pos (k + 1) (by omega) → p ∣ i ∧ p ∣ j) :
    RankThreeCent p S := by
  have hk1 : 1 ≤ k + 1 := by omega
  have hU : IsPGroup p (Lev ρ pos 1 le_rfl) := isPGroup_Lev hρ (D := 2 * k) hD
  have hA : IsElemAbelian p (Lev ρ pos k hk) :=
    ⟨⟨⟨fun x y => Subtype.ext (Lev_comm hρ hD x.2 y.2)⟩⟩, fun g hg => Lev_pow_eq_one hρ hD hg⟩
  have hBA : Lev ρ pos (k + 1) hk1 ≤ Lev ρ pos k hk := Lev_mono (Nat.le_succ k)
  have hcard : Nat.card (Lev ρ pos (k + 1) hk1) * p ^ 2 ≤ Nat.card (Lev ρ pos k hk) :=
    card_mul_le_of_independent hA hBA h₁ h₂ hind
  have hb₀p : orderOf b₀ = p :=
    orderOf_eq_prime (Lev_pow_eq_one hρ hD (hBA hb₀)) hb₀1
  have hBp : p ≤ Nat.card (Lev ρ pos (k + 1) hk1) := by
    have := Subgroup.card_le_of_le (zpowers_le.mpr hb₀)
    rwa [Nat.card_zpowers, hb₀p] at this
  refine rankThreeCent_of_witness_map π hπ hU hidx (Lev_mono hk) hBA hA
    (fun u hu a ha => commutator_mem_Lev hu ha) hcard (Or.inl ?_) hπinj
  calc p ^ 3 = p * p ^ 2 := by ring
    _ ≤ Nat.card (Lev ρ pos (k + 1) hk1) * p ^ 2 := Nat.mul_le_mul_right _ hBp
    _ ≤ _ := hcard

theorem rankThreeCent_of_center {p : ℕ} [hp : Fact p.Prime] [CharP K p] [Nonempty ι]
    {S : Type} [Group S] [Finite S] (hρ : Function.Injective ρ) {k : ℕ} (hk : 1 ≤ k)
    (hD : ∀ a b : ι, pos b < pos a + 2 * k) (hD' : ∀ a b : ι, pos b < pos a + (k + 1))
    (π : G →* S) (hπ : Function.Surjective π)
    (hπinj : ∀ u ∈ Lev ρ pos 1 le_rfl, π u = 1 → u = 1)
    (hidx : ¬ p ∣ (Lev ρ pos 1 le_rfl).index)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S))
    (hcard : p ^ 2 ≤ Nat.card (Lev ρ pos k hk)) : RankThreeCent p S := by
  have hk1 : 1 ≤ k + 1 := by omega
  have hU : IsPGroup p (Lev ρ pos 1 le_rfl) := isPGroup_Lev hρ (D := 2 * k) hD
  have hA : IsElemAbelian p (Lev ρ pos k hk) :=
    ⟨⟨⟨fun x y => Subtype.ext (Lev_comm hρ hD x.2 y.2)⟩⟩, fun g hg => Lev_pow_eq_one hρ hD hg⟩
  have hB : Lev ρ pos (k + 1) hk1 = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
    have h0 : ρ g - 1 = 0 := eq_zero_of_mem_Fil pos hD' hg
    exact hρ (by rw [map_one]; exact sub_eq_zero.mp h0)
  have hcomm : ∀ u ∈ Lev ρ pos 1 le_rfl, ∀ a ∈ Lev ρ pos k hk, u * a * u⁻¹ * a⁻¹ = 1 := by
    intro u hu a ha
    have := commutator_mem_Lev (hk := hk) hu ha
    rw [hB] at this
    exact (Subgroup.mem_bot.mp this)
  refine rankThreeCent_of_witness_map (B := ⊥) π hπ hU hidx (Lev_mono hk) bot_le hA
    (fun u hu a ha => by rw [hcomm u hu a ha]; exact one_mem _) ?_
    (Or.inr ⟨fun u hu a ha => ?_, h3⟩) hπinj
  · rw [Subgroup.card_bot, one_mul]
    exact hcard
  · have := hcomm u hu a ha
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this

end Lev


section Proj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def matrixHom (H : Subgroup (GL ι K)) : ↥H →* Matrix ι ι K :=
  (Units.coeHom (Matrix ι ι K)).comp H.subtype

@[simp] theorem matrixHom_apply (H : Subgroup (GL ι K)) (g : H) :
    matrixHom H g = ((g : GL ι K) : Matrix ι ι K) := rfl

theorem matrixHom_injective (H : Subgroup (GL ι K)) : Function.Injective (matrixHom H) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem mk_injOn_Lev [Finite K] [Nonempty ι] (H : Subgroup (GL ι K)) (pos : ι → ℕ) :
    ∀ u ∈ Lev (matrixHom H) pos 1 le_rfl,
      (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)) u = 1 → u = 1 := by
  intro u hu h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨a⟩ := ‹Nonempty ι›
  have h1 : (((u : GL ι K) : Matrix ι ι K) a a) = 1 := by
    have := hu a a (by omega)
    simp only [matrixHom_apply, Matrix.sub_apply, Matrix.one_apply_eq] at this
    exact sub_eq_zero.mp this
  have hc' : ((u : GL ι K) : Matrix ι ι K) = Matrix.scalar ι (c : K) := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  have hc1 : (c : K) = 1 := by
    rw [hc'] at h1
    simpa [Matrix.scalar_apply] using h1
  have : matrixHom H u = 1 := by
    rw [matrixHom_apply, hc', hc1]
    simp
  exact matrixHom_injective H (this.trans (map_one _).symm)

end Proj


section Reindex

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem sub_one_mem_Fil_one_iff_reindex {N : ℕ} (e : ι ≃ Fin N) (M : Matrix ι ι K) :
    M - 1 ∈ Fil K (fun x => (e x : ℕ)) 1 ↔
      (Matrix.reindex e e M).IsUpperTriangular ∧ ∀ a, Matrix.reindex e e M a a = 1 := by
  have key : ((Matrix.reindex e e M).IsUpperTriangular ∧
      ∀ a, Matrix.reindex e e M a a = 1) ↔
      ((∀ i j : Fin N, j < i → M (e.symm i) (e.symm j) = 0) ∧
        ∀ a : Fin N, M (e.symm a) (e.symm a) = 1) := Iff.rfl
  rw [key, mem_Fil]
  simp only [Matrix.sub_apply]
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun a => ?_⟩
    · have hlt : (j : ℕ) < (i : ℕ) := hij
      have := h (e.symm i) (e.symm j) (by simp only [Equiv.apply_symm_apply]; omega)
      have hne : e.symm i ≠ e.symm j := fun h' => by
        have := congrArg e h'
        simp only [Equiv.apply_symm_apply] at this
        omega
      rwa [Matrix.one_apply_ne hne, sub_zero] at this
    · have := h (e.symm a) (e.symm a) (by omega)
      rw [Matrix.one_apply_eq] at this
      exact sub_eq_zero.mp this
  · rintro ⟨h1, h2⟩ a b hab
    by_cases hba : b = a
    · subst hba
      have := h2 (e b)
      simp only [Equiv.symm_apply_apply] at this
      rw [this, Matrix.one_apply_eq, sub_self]
    · have hlt : e b < e a := by
        refine lt_of_le_of_ne (Fin.le_def.mpr (by omega)) fun h' => hba ?_
        exact e.injective h'
      have := h1 (e a) (e b) hlt
      simp only [Equiv.symm_apply_apply] at this
      rw [this, Matrix.one_apply_ne (Ne.symm hba), sub_self]

theorem mem_Lev_one_iff_reindex [Finite K] {N : ℕ} (e : ι ≃ Fin N) (H : Subgroup (GL ι K))
    (g : H) :
    g ∈ Lev (matrixHom H) (fun x => (e x : ℕ)) 1 le_rfl ↔
      (Matrix.reindex e e ((g : GL ι K) : Matrix ι ι K)).IsUpperTriangular ∧
        ∀ a, Matrix.reindex e e ((g : GL ι K) : Matrix ι ι K) a a = 1 :=
  sub_one_mem_Fil_one_iff_reindex e _

theorem sub_one_mem_Fil_one_iff_blockTriangular {pos : ι → ℕ} (hpos : Function.Injective pos)
    (M : Matrix ι ι K) :
    M - 1 ∈ Fil K pos 1 ↔ M.BlockTriangular pos ∧ ∀ a, M a a = 1 := by
  rw [mem_Fil]
  simp only [Matrix.sub_apply]
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun a => ?_⟩
    · have := h i j (by omega)
      have hne : i ≠ j := fun h' => by
        subst h'
        omega
      rwa [Matrix.one_apply_ne hne, sub_zero] at this
    · have := h a a (by omega)
      rw [Matrix.one_apply_eq] at this
      exact sub_eq_zero.mp this
  · rintro ⟨h1, h2⟩ a b hab
    by_cases hba : b = a
    · subst hba
      rw [h2 b, Matrix.one_apply_eq, sub_self]
    · have hlt : pos b < pos a := lt_of_le_of_ne (by omega) fun h' => hba (hpos h')
      rw [h1 hlt, Matrix.one_apply_ne (Ne.symm hba), sub_self]

theorem mem_Lev_one_iff_blockTriangular [Finite K] {pos : ι → ℕ} (hpos : Function.Injective pos)
    (H : Subgroup (GL ι K)) (g : H) :
    g ∈ Lev (matrixHom H) pos 1 le_rfl ↔
      ((g : GL ι K) : Matrix ι ι K).BlockTriangular pos ∧
        ∀ a, ((g : GL ι K) : Matrix ι ι K) a a = 1 :=
  sub_one_mem_Fil_one_iff_blockTriangular hpos _


end Reindex

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
