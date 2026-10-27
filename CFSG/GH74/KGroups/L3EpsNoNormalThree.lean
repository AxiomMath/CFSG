module

public import CFSG.GH74.KGroups.L3EpsUniSyl

public section

namespace CFSG.GH74.KGroups.L3Eps

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

section Center

variable {X : Type} [Group X] {p f : ℕ}

theorem center_model_lin_eq_one (hX : StatedClassicalModel X .PSL 3 p f) {x : X}
    (hx : ∀ y : X, y * x = x * y) : x = 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
  have hmem : e x ∈ Subgroup.center (projectiveSL 3 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := hx (e.symm g)
    have h2 := congrArg e this
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2
  rw [center_projectiveSL_three_eq_bot (K := F), Subgroup.mem_bot] at hmem
  exact e.injective (by rw [hmem, map_one])

theorem conj_injective_model_lin (hX : StatedClassicalModel X .PSL 3 p f) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  apply center_model_lin_eq_one hX
  intro y
  have := congrArg (fun φ : MulAut X => φ y) hx
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  exact (mul_inv_eq_iff_eq_mul.1 this).symm

end Center

section Three

variable {X X' : Type} [Group X] [Group X'] {p f : ℕ}

theorem mulAut_conj_conj (φ : MulAut X) (x : X) : φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]

theorem no_normal_minus_three (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (h3 : p ^ f % 4 = 3)
    (hX : StatedClassicalModel X .PSL 3 p f) (hX' : StatedClassicalModel X' .PSU 3 p f)
    {P : Subgroup X} (hP : IsPGroup 2 P) (hPmax : ∀ T : Subgroup X, IsPGroup 2 T → P ≤ T → T ≤ P)
    (A : Subgroup (MulAut X)) (hA : IsPGroup 2 A)
    (hAP : A ⊓ inner X = P.map (MulAut.conj : X →* MulAut X))
    (M : Subgroup (MulAut X)) (hMA : M ≤ A)
    {R : Subgroup X'} (hR : IsPGroup 2 R) (hRmax : ∀ T : Subgroup X', IsPGroup 2 T → R ≤ T → T ≤ R)
    (e : M ≃* R) : False := by
  obtain ⟨hfin, hXcard⟩ := lin_model_card hp2 hX
  obtain ⟨hfin', hX'card⟩ := uni_model_card hp2 hX'
  have hp : p.Prime := hX.1.1
  have hq2 : 2 ≤ p ^ f := by omega
  set r := ordProj[2] (p ^ f - 1) with hr
  set s := ordProj[2] (p ^ f + 1) with hs
  have hr2 : r = 2 := CFSG.LieType.Steinberg.ordProj_two_sub_one_of_mod_four_eq_three h3
  have hs4 : 4 ≤ s := by
    have hne : p ^ f + 1 ≠ 0 := by omega
    have h4 : 2 ^ 2 ∣ p ^ f + 1 := by
      have : 4 ∣ p ^ f + 1 := by omega
      simpa using this
    have := (Nat.prime_two.pow_dvd_iff_le_factorization hne).1 h4
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p ^ f + 1).factorization 2 := Nat.pow_le_pow_right (by norm_num) this
  have hPcard : Nat.card P = 4 * s := by
    rw [card_of_isMaxPGroup hP hPmax, hXcard, hr2]
    ring
  have hRcard : Nat.card R = 2 * s ^ 2 := by
    rw [card_of_isMaxPGroup hR hRmax, hX'card, hr2]
  have hAcard : Nat.card A ≤ 8 * s := by
    have h1 := card_le_of_inner A hA P hAP.le
    have h2 := lin_outer_two_le hp2 hX h3
    rw [hPcard] at h1
    calc Nat.card A ≤ 4 * s * ordProj[2] (Nat.card (Outer X)) := h1
      _ ≤ 4 * s * 2 := Nat.mul_le_mul_left _ h2
      _ = 8 * s := by ring
  have hMcard : Nat.card M = 2 * s ^ 2 := by rw [Nat.card_congr e.toEquiv, hRcard]
  have hMleA : Nat.card M ≤ Nat.card A := Subgroup.card_le_of_le hMA
  have hs_eq : s = 4 := by
    have : 2 * s ^ 2 ≤ 8 * s := by omega
    nlinarith
  have hMeq : M = A := Subgroup.eq_of_le_of_card_ge hMA (by
    rw [hMcard, hs_eq]
    rw [hs_eq] at hAcard
    omega)
  obtain ⟨z, hzc, hzo⟩ := uni_sylow_three hp2 h3 hX' hR hRmax
  set z₁ : M := e.symm z with hz₁
  have hz₁c : ∀ y : M, y * z₁ = z₁ * y := by
    intro y
    apply e.injective
    rw [map_mul, map_mul, hz₁, MulEquiv.apply_symm_apply]
    exact hzc (e y)
  have hz₁o : orderOf z₁ = 4 := by rw [hz₁, MulEquiv.orderOf_eq, hzo, ← hs, hs_eq]
  set φ : MulAut X := (z₁ : MulAut X) with hφ
  have hφo : orderOf φ = 4 := by rw [hφ, Subgroup.orderOf_coe, hz₁o]
  have hφA : φ ∈ A := hMA z₁.2
  obtain ⟨k, hk⟩ := hA ⟨φ, hφA⟩
  have hφk : φ ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hφfix : ∀ x ∈ P, φ x = x := by
    intro x hx
    have hxA : MulAut.conj x ∈ M := by
      rw [hMeq]
      have : MulAut.conj x ∈ P.map (MulAut.conj : X →* MulAut X) := ⟨x, hx, rfl⟩
      rw [← hAP] at this
      exact this.1
    have hc := hz₁c ⟨MulAut.conj x, hxA⟩
    have hc' : MulAut.conj x * φ = φ * MulAut.conj x := congrArg Subtype.val hc
    have h2 : φ * MulAut.conj x * φ⁻¹ = MulAut.conj x := by
      rw [← hc', mul_assoc, mul_inv_cancel, mul_one]
    rw [mulAut_conj_conj] at h2
    exact conj_injective_model_lin hX h2
  obtain ⟨w, hwP, hwc, hφw⟩ := l3eps_sylow_aut (Or.inl rfl) hp2 h5 hX hP hPmax hφk hφfix
  have hwq : w ^ (p ^ f - 1) = 1 := by
    refine (l3eps_center_sylow (Or.inl rfl) hp2 hX hP hPmax).2.1 rfl w ⟨hwP, ?_⟩
    exact Subgroup.mem_centralizer_iff.2 (fun g hg => hwc g hg)
  obtain ⟨j, hj⟩ := hP ⟨w, hwP⟩
  have hwj : w ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hord2 : orderOf w ∣ 2 := by
    have h1 : orderOf w ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hwj
    obtain ⟨i, hi, hi2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have h2 : orderOf w ∣ p ^ f - 1 := orderOf_dvd_of_pow_eq_one hwq
    rw [hi2] at h2 ⊢
    by_cases hi1 : i ≤ 1
    · exact pow_dvd_pow 2 hi1
    · exfalso
      have : 2 ^ 2 ∣ p ^ f - 1 :=
        (pow_dvd_pow 2 (by omega : 2 ≤ i)).trans h2
      omega
  have hw2 : w ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hord2
  have hφ2 : φ ^ 2 = 1 := by
    rw [hφw, ← map_pow, hw2, map_one]
  have := orderOf_dvd_of_pow_eq_one hφ2
  rw [hφo] at this
  omega

end Three

end CFSG.GH74.KGroups.L3Eps
