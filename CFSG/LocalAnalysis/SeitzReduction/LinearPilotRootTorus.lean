module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHsyl
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCoresTori
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Split

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def IsRootSplit (a b : Fin n) (h : SpecialLinearGroup (Fin n) K) : Prop :=
  h ∈ blockSpecialLinear ({a, b} : Finset (Fin n)) ∧
    (∀ i j, i ≠ j → (h : Matrix (Fin n) (Fin n) K) i j = 0) ∧
      (h : Matrix (Fin n) (Fin n) K) a a ≠ (h : Matrix (Fin n) (Fin n) K) b b

variable {a b : Fin n} {h : SpecialLinearGroup (Fin n) K}

namespace IsRootSplit

theorem ne (hh : IsRootSplit a b h) : a ≠ b := fun hab => hh.2.2 (by rw [hab])

theorem apply_eq_one (hh : IsRootSplit a b h) {i : Fin n}
    (hi : i ∉ ({a, b} : Finset (Fin n))) : (h : Matrix (Fin n) (Fin n) K) i i = 1 := by
  rw [hh.1 i i (Or.inl hi), one_apply_eq]

theorem eq_diagonal (hh : IsRootSplit a b h) :
    (h : Matrix (Fin n) (Fin n) K) = diagonal fun i => (h : Matrix (Fin n) (Fin n) K) i i := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq]
  · rw [hh.2.1 i j hij, diagonal_apply_ne _ hij]

theorem mul_apply_left (hh : IsRootSplit a b h) (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ((h : Matrix (Fin n) (Fin n) K) * M) i j = (h : Matrix (Fin n) (Fin n) K) i i * M i j := by
  conv_lhs => rw [hh.eq_diagonal]
  rw [diagonal_mul]

theorem mul_apply_right (hh : IsRootSplit a b h) (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (M * (h : Matrix (Fin n) (Fin n) K)) i j = M i j * (h : Matrix (Fin n) (Fin n) K) j j := by
  conv_lhs => rw [hh.eq_diagonal]
  rw [mul_diagonal]

theorem mul_eq_one (hh : IsRootSplit a b h) :
    (h : Matrix (Fin n) (Fin n) K) a a * (h : Matrix (Fin n) (Fin n) K) b b = 1 := by
  have hd := det_eq_of_agrees_one_pair hh.ne hh.1
  rw [h.2, hh.2.1 a b hh.ne, zero_mul, sub_zero] at hd
  exact hd.symm

theorem apply_left_ne_one (hh : IsRootSplit a b h) : (h : Matrix (Fin n) (Fin n) K) a a ≠ 1 := by
  intro h1
  apply hh.2.2
  have h2 := hh.mul_eq_one
  rw [h1, one_mul] at h2
  rw [h1, h2]

theorem apply_right_ne_one (hh : IsRootSplit a b h) : (h : Matrix (Fin n) (Fin n) K) b b ≠ 1 := by
  intro h1
  apply hh.2.2
  have h2 := hh.mul_eq_one
  rw [h1, mul_one] at h2
  rw [h1, h2]

theorem apply_ne_of_mem_iff_notMem (hh : IsRootSplit a b h) {i j : Fin n}
    (hij : i ∈ ({a, b} : Finset (Fin n)) ↔ j ∉ ({a, b} : Finset (Fin n))) :
    (h : Matrix (Fin n) (Fin n) K) i i ≠ (h : Matrix (Fin n) (Fin n) K) j j := by
  have key : ∀ i j, i ∈ ({a, b} : Finset (Fin n)) → j ∉ ({a, b} : Finset (Fin n)) →
      (h : Matrix (Fin n) (Fin n) K) i i ≠ (h : Matrix (Fin n) (Fin n) K) j j := by
    intro i j hi hj
    rw [hh.apply_eq_one hj]
    have hi2 : i = a ∨ i = b := by simpa using hi
    rcases hi2 with hia | hib
    · rw [hia]
      exact hh.apply_left_ne_one
    · rw [hib]
      exact hh.apply_right_ne_one
  by_cases hi : i ∈ ({a, b} : Finset (Fin n))
  · exact key i j hi (hij.1 hi)
  · have hj : j ∈ ({a, b} : Finset (Fin n)) := by tauto
    exact (key j i hj hi).symm

theorem four_le_card [Finite K] (hh : IsRootSplit a b h) : 4 ≤ Nat.card K := by
  classical
  have := Fintype.ofFinite K
  have hxy := hh.mul_eq_one
  have hx0 : (h : Matrix (Fin n) (Fin n) K) a a ≠ 0 := left_ne_zero_of_mul_eq_one hxy
  have hy0 : (h : Matrix (Fin n) (Fin n) K) b b ≠ 0 := right_ne_zero_of_mul_eq_one hxy
  have hx1 := hh.apply_left_ne_one
  have hy1 := hh.apply_right_ne_one
  have hcard : ({0, 1, (h : Matrix (Fin n) (Fin n) K) a a, (h : Matrix (Fin n) (Fin n) K) b b} :
      Finset K).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hh.2.2]
    · simp [hx1.symm, hy1.symm]
    · simp [hx0.symm, hy0.symm]
  rw [Nat.card_eq_fintype_card, ← hcard]
  exact Finset.card_le_univ _

end IsRootSplit

theorem apply_eq_zero_of_mul_diagonal_eq {d : Fin n → K} {A : Matrix (Fin n) (Fin n) K}
    (hA : A * diagonal d = diagonal d * A) {i j : Fin n} (hij : d i ≠ d j) : A i j = 0 := by
  have h1 := congrFun (congrFun hA i) j
  rw [mul_diagonal, diagonal_mul] at h1
  have h2 : A i j * (d j - d i) = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hij.symm)

theorem mul_eq_mul_of_proj_commute_split (hn : 4 ≤ n) (hh : IsRootSplit a b h)
    {A : SpecialLinearGroup (Fin n) K}
    (hA : LinearFlag.proj n K A * LinearFlag.proj n K h =
      LinearFlag.proj n K h * LinearFlag.proj n K A) : A * h = h * A := by
  have hab := hh.ne
  rw [← map_mul, ← map_mul] at hA
  obtain ⟨μ, hμ⟩ := exists_smul_of_proj_eq hA
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at hμ
  have hentry : ∀ i j, (h : Matrix (Fin n) (Fin n) K) i i * (A : Matrix (Fin n) (Fin n) K) i j =
      (μ : K) * ((A : Matrix (Fin n) (Fin n) K) i j * (h : Matrix (Fin n) (Fin n) K) j j) := by
    intro i j
    have h1 := congrFun (congrFun hμ i) j
    rwa [hh.mul_apply_left, Matrix.smul_apply, smul_eq_mul, hh.mul_apply_right] at h1
  have hμ1 : μ = 1 := by
    by_contra hμ1
    have hμ1' : (μ : K) ≠ 1 := fun h' => hμ1 (Units.ext h')
    have hout : ∀ i, i ∉ ({a, b} : Finset (Fin n)) → (h : Matrix (Fin n) (Fin n) K) i i ≠ μ :=
      fun i hi h' => hμ1' (by rw [← h', hh.apply_eq_one hi])
    obtain ⟨c, hc⟩ : ∃ c : Fin n, ∀ i, i ≠ c → (h : Matrix (Fin n) (Fin n) K) i i ≠ μ := by
      by_cases hμa : (h : Matrix (Fin n) (Fin n) K) a a = μ
      · refine ⟨a, fun i hi => ?_⟩
        by_cases hib : i = b
        · rw [hib, ← hμa]
          exact hh.2.2.symm
        · exact hout i (by simp [hi, hib])
      · by_cases hμb : (h : Matrix (Fin n) (Fin n) K) b b = μ
        · refine ⟨b, fun i hi => ?_⟩
          by_cases hia : i = a
          · rw [hia]
            exact hμa
          · exact hout i (by simp [hi, hia])
        · refine ⟨a, fun i _ => ?_⟩
          by_cases hia : i = a
          · rw [hia]
            exact hμa
          · by_cases hib : i = b
            · rw [hib]
              exact hμb
            · exact hout i (by simp [hia, hib])
    have hzero : ∀ i j, i ≠ c → j ∉ ({a, b} : Finset (Fin n)) →
        (A : Matrix (Fin n) (Fin n) K) i j = 0 := by
      intro i j hi hj
      have h1 := hentry i j
      rw [hh.apply_eq_one hj, mul_one] at h1
      have h2 : ((h : Matrix (Fin n) (Fin n) K) i i - μ) * (A : Matrix (Fin n) (Fin n) K) i j = 0 := by
        linear_combination h1
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (hc i hi))
    obtain ⟨j₁, j₂, hj₁, hj₂, hj⟩ : ∃ j₁ j₂ : Fin n, j₁ ∉ ({a, b} : Finset (Fin n)) ∧
        j₂ ∉ ({a, b} : Finset (Fin n)) ∧ j₁ ≠ j₂ := by
      have hcard : 1 < (({a, b} : Finset (Fin n))ᶜ).card := by
        rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
        omega
      obtain ⟨j₁, h₁, j₂, h₂, h⟩ := Finset.one_lt_card.1 hcard
      exact ⟨j₁, j₂, Finset.mem_compl.1 h₁, Finset.mem_compl.1 h₂, h⟩
    have hdet := det_eq_zero_of_cols (c := c) hj (fun i hi => hzero i j₁ hi hj₁)
      (fun i hi => hzero i j₂ hi hj₂)
    rw [A.2] at hdet
    exact one_ne_zero hdet
  subst hμ1
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hμ, Units.val_one,
    one_smul]

theorem commutator_mem_of_mem_centralizer_split (hh : IsRootSplit a b h)
    {A B : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ Subgroup.centralizer ({h} : Set (SpecialLinearGroup (Fin n) K)))
    (hB : B ∈ Subgroup.centralizer ({h} : Set (SpecialLinearGroup (Fin n) K))) :
    A * B * A⁻¹ * B⁻¹ ∈ blockSpecialLinear (({a, b} : Finset (Fin n))ᶜ) := by
  have hab := hh.ne
  have hzero : ∀ C ∈ Subgroup.centralizer ({h} : Set (SpecialLinearGroup (Fin n) K)),
      ∀ i j, (h : Matrix (Fin n) (Fin n) K) i i ≠ (h : Matrix (Fin n) (Fin n) K) j j →
        (C : Matrix (Fin n) (Fin n) K) i j = 0 := by
    intro C hC i j hij
    rw [Subgroup.mem_centralizer_singleton_iff] at hC
    have h1 : (C : Matrix (Fin n) (Fin n) K) * h = h * C := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hC]
    rw [hh.eq_diagonal] at h1
    exact apply_eq_zero_of_mul_diagonal_eq h1 hij
  have hdiag : ∀ C ∈ Subgroup.centralizer ({h} : Set (SpecialLinearGroup (Fin n) K)),
      ∀ i j, (i ∈ ({a, b} : Finset (Fin n)) ↔ j ∉ ({a, b} : Finset (Fin n))) →
        (C : Matrix (Fin n) (Fin n) K) i j = 0 := fun C hC i j hij =>
    hzero C hC i j (hh.apply_ne_of_mem_iff_notMem hij)
  refine commutator_agrees_one_compl (pair_injective hab) mem_pair_iff_mem_range hdiag
    (fun C hC D hD => ?_) hA hB
  have hCab := hzero C hC a b hh.2.2
  have hCba := hzero C hC b a hh.2.2.symm
  have hDab := hzero D hD a b hh.2.2
  have hDba := hzero D hD b a hh.2.2.symm
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.submatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [hCab, hCba, hDab, hDba, mul_comm]

theorem commutator_mem_blockSL_of_mem_centralizer_split (hn : 4 ≤ n) (hh : IsRootSplit a b h)
    {X : Subgroup (LinearFlag.projectiveSL n K)} (hhX : LinearFlag.proj n K h ∈ X)
    {g g' : LinearFlag.projectiveSL n K}
    (hg : g ∈ Subgroup.centralizer (X : Set (LinearFlag.projectiveSL n K)))
    (hg' : g' ∈ Subgroup.centralizer (X : Set (LinearFlag.projectiveSL n K))) :
    g * g' * g⁻¹ * g'⁻¹ ∈ blockSL (({a, b} : Finset (Fin n))ᶜ) := by
  have hlift : ∀ g ∈ Subgroup.centralizer (X : Set (LinearFlag.projectiveSL n K)),
      ∃ A : SpecialLinearGroup (Fin n) K, LinearFlag.proj n K A = g ∧
        A ∈ Subgroup.centralizer ({h} : Set (SpecialLinearGroup (Fin n) K)) := fun g hg => by
    obtain ⟨A, rfl⟩ := LinearFlag.proj_surjective n K g
    refine ⟨A, rfl, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_eq_mul_of_proj_commute_split hn hh (Subgroup.mem_centralizer_iff.1 hg _ hhX).symm
  obtain ⟨A, rfl, hA⟩ := hlift g hg
  obtain ⟨B, rfl, hB⟩ := hlift g' hg'
  have := proj_mem_blockSL (commutator_mem_of_mem_centralizer_split hh hA hB)
  simpa only [map_mul, map_inv] using this

theorem layer_centralizer_of_split_of_le_centralizer [Finite K] (hn : 4 ≤ n)
    (hh : IsRootSplit a b h) {X : Subgroup (LinearFlag.projectiveSL n K)}
    (hDX : blockSL (({a, b} : Finset (Fin n))ᶜ) ≤
      Subgroup.centralizer (X : Set (LinearFlag.projectiveSL n K)))
    (hhX : LinearFlag.proj n K h ∈ X) :
    inSubgroup layer (Subgroup.centralizer (X : Set (LinearFlag.projectiveSL n K))) =
      blockSL (({a, b} : Finset (Fin n))ᶜ) := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hh.ne]
  exact inSubgroup_layer_eq_of_commutator_mem hDX
    (fun g hg g' hg' => commutator_mem_blockSL_of_mem_centralizer_split hn hh hhX hg hg')
    (isQuasisimple_blockSL (by omega) (by omega) (Or.inr hh.four_le_card))

theorem layer_centralizer_of_split [Finite K] (hn : 4 ≤ n) (hh : IsRootSplit a b h)
    {X : Subgroup (LinearFlag.projectiveSL n K)} (hX : X ≤ rootSL2 a b)
    (hhX : LinearFlag.proj n K h ∈ X) :
    inSubgroup layer (Subgroup.centralizer (X : Set (LinearFlag.projectiveSL n K))) =
      blockSL (({a, b} : Finset (Fin n))ᶜ) :=
  layer_centralizer_of_split_of_le_centralizer hn hh (blockSL_compl_le_centralizer hX) hhX

end Split

section Hsyl

variable {K : Type*} [Field K] [Finite K] [CharP K 2] {n : ℕ} {a b : Fin n}
  {h : SpecialLinearGroup (Fin n) K}

theorem eq_one_of_two_group_fix_split (hn : 5 ≤ n) (hh : IsRootSplit a b h)
    {β : MulAut (LinearFlag.projectiveSL n K)}
    (hβh : β (LinearFlag.proj n K h) = LinearFlag.proj n K h)
    (hβD : ∀ d ∈ blockSL (({a, b} : Finset (Fin n))ᶜ), β d = d) {k : ℕ} (hβk : β ^ 2 ^ k = 1) :
    β = 1 := by
  have hab := hh.ne
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  obtain ⟨A, rfl, hA⟩ := exists_conjAut_eq_of_fix_blockSL (by omega) (by omega) hβD
  have hA' : ∀ i j, (i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) →
      (A : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j := fun i j h =>
    hA i j (by simpa only [Finset.mem_compl] using h)
  obtain ⟨j₀, hj₀⟩ : ∃ j, j ∉ ({a, b} : Finset (Fin n)) := by
    by_contra hcon
    push Not at hcon
    have := Finset.card_le_card (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hcon j)
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hab] at this
    omega
  obtain ⟨μ, hμ⟩ := exists_mul_eq_smul_of_conjAut hβh
  have hμ1 : (μ : K) = 1 := by
    have h1 := congrFun (congrFun hμ j₀) j₀
    rw [hh.mul_apply_left, Matrix.smul_apply, smul_eq_mul, hh.mul_apply_right,
      hh.apply_eq_one hj₀, hA' j₀ j₀ (Or.inl hj₀), one_apply_eq, one_mul, mul_one] at h1
    exact h1.symm
  have hAh : (A : Matrix (Fin n) (Fin n) K) *
      diagonal (fun i => (h : Matrix (Fin n) (Fin n) K) i i) =
        diagonal (fun i => (h : Matrix (Fin n) (Fin n) K) i i) * A := by
    rw [← hh.eq_diagonal, hμ, hμ1, one_smul]
  have hAab : (A : Matrix (Fin n) (Fin n) K) a b = 0 :=
    apply_eq_zero_of_mul_diagonal_eq hAh hh.2.2
  have hAba : (A : Matrix (Fin n) (Fin n) K) b a = 0 :=
    apply_eq_zero_of_mul_diagonal_eq hAh hh.2.2.symm
  have hAdiag : ∀ i j, i ≠ j → (A : Matrix (Fin n) (Fin n) K) i j = 0 := by
    intro i j hij
    by_cases hi : i ∈ ({a, b} : Finset (Fin n))
    · by_cases hj : j ∈ ({a, b} : Finset (Fin n))
      · have hi2 : i = a ∨ i = b := by simpa using hi
        have hj2 : j = a ∨ j = b := by simpa using hj
        rcases hi2 with hia | hib <;> rcases hj2 with hja | hjb
        · exact absurd (hia.trans hja.symm) hij
        · rw [hia, hjb]
          exact hAab
        · rw [hib, hja]
          exact hAba
        · exact absurd (hib.trans hjb.symm) hij
      · rw [hA' i j (Or.inr hj), one_apply_ne hij]
    · rw [hA' i j (Or.inl hi), one_apply_ne hij]
  have hAeq : (A : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => (A : Matrix (Fin n) (Fin n) K) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [hAdiag i j hij, diagonal_apply_ne _ hij]
  have hAk : (A : Matrix (Fin n) (Fin n) K) ^ 2 ^ k = 1 := by
    have h1 : conjAut n K (A ^ 2 ^ k) * fieldAut n K 1 = 1 := by
      rw [map_one, mul_one, map_pow, hβk]
    obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by omega) _ _ h1
    have hu' : (A : Matrix (Fin n) (Fin n) K) ^ 2 ^ k = scalar (Fin n) (u : K) := by
      rw [← Units.val_pow_eq_pow_val, ← hu, Matrix.GeneralLinearGroup.coe_scalar]
    have hjj := agrees_one_pow hA' (2 ^ k) j₀ j₀ (Or.inl hj₀)
    rw [hu', scalar_apply, diagonal_apply_eq, one_apply_eq] at hjj
    rw [hu', hjj, map_one]
  have hAii : ∀ i, (A : Matrix (Fin n) (Fin n) K) i i = 1 := by
    intro i
    have h1 : ((A : Matrix (Fin n) (Fin n) K) ^ 2 ^ k) i i =
        (A : Matrix (Fin n) (Fin n) K) i i ^ 2 ^ k := by
      conv_lhs => rw [hAeq]
      rw [diagonal_pow, diagonal_apply_eq, Pi.pow_apply]
    have h0 : (A : Matrix (Fin n) (Fin n) K) i i ^ 2 ^ k = 1 := by
      rw [← h1, hAk, one_apply_eq]
    have h00 : ((A : Matrix (Fin n) (Fin n) K) i i - 1) ^ 2 ^ k = 0 := by
      rw [sub_pow_char_pow, one_pow, h0, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.1 h00)
  have hA1 : (A : Matrix (Fin n) (Fin n) K) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [hAii, one_apply_eq]
    · rw [hAdiag i j hij, one_apply_ne hij]
  have : A = 1 := Units.ext hA1
  rw [this, map_one]

theorem eq_one_of_isPGroup_fix_split (hn : 5 ≤ n) (hh : IsRootSplit a b h)
    {β : MulAut (LinearFlag.projectiveSL n K)} (hβ2 : IsPGroup 2 (Subgroup.zpowers β))
    (hβh : β (LinearFlag.proj n K h) = LinearFlag.proj n K h)
    (hβD : ∀ d ∈ blockSL (({a, b} : Finset (Fin n))ᶜ), β d = d) : β = 1 := by
  obtain ⟨k, hk⟩ := hβ2 ⟨β, Subgroup.mem_zpowers β⟩
  exact eq_one_of_two_group_fix_split hn hh hβh hβD (k := k) (congrArg Subtype.val hk)

end Hsyl

section Torus

variable {K : Type*} [Field K] {n : ℕ} {a b : Fin n}

theorem isRootSplit_torusDiagSL_rootTorusHom (hab : a ≠ b) {κ : Kˣ} (hκ : κ * κ ≠ 1) :
    IsRootSplit a b (torusDiagSL (rootTorusHom (K := K) hab κ)) := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, ?_⟩
  · rw [coe_torusDiagSL_rootTorusHom]
    by_cases h : i = j
    · subst h
      have hi : i ≠ a ∧ i ≠ b := by
        rcases hij with h1 | h1 <;> simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using h1
      rw [diagonal_apply_eq, rootTorusParam_apply_of_ne hi.1 hi.2, Units.val_one, one_apply_eq]
    · rw [diagonal_apply_ne _ h, one_apply_ne h]
  · rw [coe_torusDiagSL_rootTorusHom, diagonal_apply_ne _ hij]
  · rw [coe_torusDiagSL_rootTorusHom, diagonal_apply_eq, diagonal_apply_eq,
      rootTorusParam_apply_left, rootTorusParam_apply_right hab]
    intro h
    apply hκ
    have h' : κ = κ⁻¹ := Units.ext h
    calc κ * κ = κ * κ⁻¹ := by rw [← h']
      _ = 1 := mul_inv_cancel κ

theorem isCyclic_rootTorus [Finite K] (hab : a ≠ b) :
    IsCyclic (rootTorus (K := K) (n := n) hab) :=
  isCyclic_of_surjective
    ((LinearFlag.proj n K).comp (torusDiagSL.comp (rootTorusHom hab))).rangeRestrict
    ((LinearFlag.proj n K).comp (torusDiagSL.comp (rootTorusHom hab))).rangeRestrict_surjective

theorem odd_card_rootTorus [Finite K] [CharP K 2] (hab : a ≠ b) :
    Odd (Nat.card (rootTorus (K := K) (n := n) hab)) := by
  have hd : Nat.card (rootTorus (K := K) (n := n) hab) ∣ Nat.card Kˣ :=
    Subgroup.card_range_dvd _
  rw [Nat.card_units] at hd
  have hodd : Odd (Nat.card K - 1) := by
    obtain ⟨k, hk⟩ := odd_natCard_add_one (K := K)
    have h1 := Finite.one_lt_card (α := K)
    exact ⟨k - 1, by omega⟩
  exact hodd.of_dvd_nat hd

theorem exists_units_mul_self_ne_one [Finite K] (hq : 4 ≤ Nat.card K) :
    ∃ κ : Kˣ, κ * κ ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hpm : ∀ κ : Kˣ, κ ∈ ({1, -1} : Finset Kˣ) := fun κ => by
    have h1 : ((κ : K) - 1) * ((κ : K) + 1) = 0 := by
      have h2 : (κ : K) * κ = 1 := by rw [← Units.val_mul, hcon κ, Units.val_one]
      linear_combination h2
    rcases mul_eq_zero.1 h1 with h3 | h3
    · have : κ = 1 := Units.ext (by rw [Units.val_one]; linear_combination h3)
      simp [this]
    · have : κ = -1 := Units.ext (by rw [Units.val_neg, Units.val_one]; linear_combination h3)
      simp [this]
  have := Fintype.ofFinite K
  have hle : Nat.card Kˣ ≤ 2 := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact (Finset.card_le_card fun κ _ => hpm κ).trans Finset.card_le_two
  rw [Nat.card_units] at hle
  omega

theorem exists_isRootSplit_proj_mem_rootTorus [Finite K] (hq : 4 ≤ Nat.card K) (hab : a ≠ b) :
    ∃ h : SpecialLinearGroup (Fin n) K, IsRootSplit a b h ∧
      LinearFlag.proj n K h ∈ rootTorus (K := K) hab := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one hq
  exact ⟨_, isRootSplit_torusDiagSL_rootTorusHom hab hκ, proj_torusDiagSL_rootTorusHom_mem hab κ⟩

theorem layer_centralizer_rootTorus [Finite K] (hn : 4 ≤ n) (hq : 4 ≤ Nat.card K)
    (hab : a ≠ b) :
    inSubgroup layer
        (Subgroup.centralizer (rootTorus (K := K) hab : Set (LinearFlag.projectiveSL n K))) =
      blockSL (({a, b} : Finset (Fin n))ᶜ) := by
  obtain ⟨h, hh, hhX⟩ := exists_isRootSplit_proj_mem_rootTorus (n := n) hq hab
  exact layer_centralizer_of_split hn hh (rootTorus_le_rootSL2 hab) hhX

theorem eq_one_of_two_group_fix_rootTorus [Finite K] [CharP K 2] (hn : 5 ≤ n)
    (hq : 4 ≤ Nat.card K) (hab : a ≠ b) {β : MulAut (LinearFlag.projectiveSL n K)}
    (hβX : ∀ x ∈ rootTorus (K := K) hab, β x = x)
    (hβD : ∀ d ∈ blockSL (({a, b} : Finset (Fin n))ᶜ), β d = d) {k : ℕ} (hβk : β ^ 2 ^ k = 1) :
    β = 1 := by
  obtain ⟨h, hh, hhX⟩ := exists_isRootSplit_proj_mem_rootTorus (n := n) hq hab
  exact eq_one_of_two_group_fix_split hn hh (hβX _ hhX) hβD hβk

theorem eq_one_of_isPGroup_fix_rootTorus [Finite K] [CharP K 2] (hn : 5 ≤ n)
    (hq : 4 ≤ Nat.card K) (hab : a ≠ b) {β : MulAut (LinearFlag.projectiveSL n K)}
    (hβ2 : IsPGroup 2 (Subgroup.zpowers β)) (hβX : ∀ x ∈ rootTorus (K := K) hab, β x = x)
    (hβD : ∀ d ∈ blockSL (({a, b} : Finset (Fin n))ᶜ), β d = d) : β = 1 := by
  obtain ⟨k, hk⟩ := hβ2 ⟨β, Subgroup.mem_zpowers β⟩
  exact eq_one_of_two_group_fix_rootTorus hn hq hab hβX hβD (k := k) (congrArg Subtype.val hk)

end Torus

end CFSG.SeitzReduction.LinearPilot
