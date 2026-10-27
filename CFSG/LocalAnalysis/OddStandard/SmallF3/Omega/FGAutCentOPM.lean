module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Det

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
  {R : QuadraticForm (ZMod 3) W}

theorem fg_subgroup_two_minus (hR : R.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) W = 2) (hs : quadSign R = -1) (B : Subgroup (OGroup R))
    (hB : ∀ g ∈ B, QuadraticMap.orthogonalDet R g = 1) :
    Nat.card B ≤ 2 ∨ Nonempty (↥B ≃* Multiplicative (ZMod 4)) := by
  haveI : Finite (OGroup R) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have h2 : 2 ≤ Module.finrank (ZMod 3) W := by rw [hdim]
  have hpos : 0 < Module.finrank (ZMod 3) W := by rw [hdim]; norm_num
  have hEven : Even (Module.finrank (ZMod 3) W) := by rw [hdim]; exact ⟨1, rfl⟩
  have hsign : quadSign R = (-1 : ℤˣ) ^ (Module.finrank (ZMod 3) W / 2) := by
    rw [hdim, hs, show (2 : ℕ) / 2 = 1 by norm_num, pow_one]
  obtain ⟨p, hp⟩ := (exists_mul_self_eq_piOrth_iff hR).mpr ⟨hEven, hsign⟩
  have hdetp : QuadraticMap.orthogonalDet R p = 1 :=
    orthogonalDet_eq_one_of_mul_self_eq_piOrth hEven hp
  have hpi_ne : piOrth R ≠ 1 := piOrth_ne_one (Q := R) hpos
  have hp2 : p ^ 2 ≠ 1 := by
    rw [pow_two, hp]
    exact hpi_ne
  have hp4 : p ^ 4 = 1 := by
    have h : p ^ 4 = (p ^ 2) * (p ^ 2) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
    rw [h, pow_two, hp, piOrth_mul_self]
  have horder : orderOf p = 4 := by
    have h := orderOf_eq_prime_pow (x := p) (n := 1) (p := 2)
      (by simpa using hp2) (by simpa using hp4)
    simpa using h
  have hzp_card : Nat.card (Subgroup.zpowers p) = 4 := by
    rw [Nat.card_zpowers, horder]
  let K : Subgroup (OGroup R) := (QuadraticMap.orthogonalDet R).ker
  have hzp_le : Subgroup.zpowers p ≤ K := by
    rw [Subgroup.zpowers_le]
    exact MonoidHom.mem_ker.mpr hdetp
  obtain ⟨v, hv⟩ := exists_eq_unit_of_two_le_finrank (R := R) hR h2 (1 : (ZMod 3)ˣ)
  have hRv : R v ≠ 0 := by rw [hv]; exact one_ne_zero
  let _ : Invertible (R v) := invertibleOfNonzero hRv
  have hdet_refl : QuadraticMap.orthogonalDet R
      (TauCeti.QuadraticMap.reflectionOrthogonal R v) = -1 :=
    QuadraticMap.orthogonalDet_reflectionOrthogonal R v
  have hne_one : (-1 : (ZMod 3)ˣ) ≠ 1 := by decide
  have hKne : K ≠ ⊤ := by
    intro htop
    have hmem : TauCeti.QuadraticMap.reflectionOrthogonal R v ∈ K := by
      rw [htop]; exact Subgroup.mem_top _
    exact hne_one (hdet_refl ▸ MonoidHom.mem_ker.mp hmem)
  have hKdvd8 : Nat.card K ∣ 8 := by
    rw [← natCard_oGroup_two_minus (W := W) (R := R) hR hdim hs]
    exact Subgroup.card_subgroup_dvd_card K
  have hKdvd4 : 4 ∣ Nat.card K := by
    rw [← hzp_card]
    exact Subgroup.card_dvd_of_le hzp_le
  have hKpos : 0 < Nat.card K := by
    haveI : Nonempty ↥K := ⟨1, K.one_mem⟩
    exact Finite.card_pos_iff.mpr inferInstance
  have hKle8 : Nat.card K ≤ 8 := Nat.le_of_dvd (by norm_num) hKdvd8
  have hKge4 : 4 ≤ Nat.card K := Nat.le_of_dvd hKpos hKdvd4
  have hKne8 : Nat.card K ≠ 8 := by
    intro h8
    exact hKne (Subgroup.eq_top_of_card_eq (H := K)
      (by rw [h8, natCard_oGroup_two_minus (W := W) (R := R) hR hdim hs]))
  have hKcard : Nat.card K = 4 := by
    have hcases : Nat.card K = 4 ∨ Nat.card K = 5 ∨ Nat.card K = 6 ∨ Nat.card K = 7 ∨
        Nat.card K = 8 := by omega
    rcases hcases with h | h | h | h | h
    · exact h
    · rw [h] at hKdvd4; exact absurd hKdvd4 (by decide : ¬ (4 ∣ 5))
    · rw [h] at hKdvd4; exact absurd hKdvd4 (by decide : ¬ (4 ∣ 6))
    · rw [h] at hKdvd4; exact absurd hKdvd4 (by decide : ¬ (4 ∣ 7))
    · exact absurd h hKne8
  have hK_eq : K = Subgroup.zpowers p :=
    (Subgroup.eq_of_le_of_card_ge hzp_le (le_of_eq (hKcard.trans hzp_card.symm))).symm
  have hB_le_K : B ≤ K := by
    intro g hg
    exact MonoidHom.mem_ker.mpr (hB g hg)
  have hBz : B ≤ Subgroup.zpowers p := hK_eq ▸ hB_le_K
  have hBdvd : Nat.card B ∣ 4 := by
    rw [← hzp_card]
    exact Subgroup.card_dvd_of_le hBz
  by_cases hle2 : Nat.card B ≤ 2
  · exact Or.inl hle2
  · right
    have hge3 : 3 ≤ Nat.card B := by omega
    have hBle4 : Nat.card B ≤ 4 := Nat.le_of_dvd (by norm_num) hBdvd
    have hBcard : Nat.card B = 4 := by
      have hcases : Nat.card B = 3 ∨ Nat.card B = 4 := by omega
      rcases hcases with h | h
      · rw [h] at hBdvd; exact absurd hBdvd (by decide : ¬ (3 ∣ 4))
      · exact h
    have hcyc : IsCyclic ↥B := Subgroup.isCyclic_of_le hBz
    exact ⟨hBcard ▸ (zmodCyclicMulEquiv (G := ↥B) hcyc).symm⟩

end CFSG.OddStandard.SmallF3.Omega
