module

public import CFSG.RankThree.Asc83Table.GL23

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.RankThree.Asc83Table

private def gl23SdR : GL23 := gl23 !![0, 1; 1, 1] !![2, 1; 1, 0] (by decide) (by decide)

private def gl23SdS : GL23 := gl23 !![1, 0; 1, 2] !![1, 0; 1, 2] (by decide) (by decide)

private theorem gl23SdR_pow : gl23SdR ^ 8 = 1 := by decide +kernel

private theorem gl23SdS_pow : gl23SdS ^ 2 = 1 := by decide +kernel

private theorem gl23SdS_conj : gl23SdS * gl23SdR * gl23SdS⁻¹ = gl23SdR ^ 3 := by
  decide +kernel

private theorem gl23Sd_independent : ∀ i : Fin 8, ∀ e : Fin 2,
    gl23SdR ^ (i : ℕ) * gl23SdS ^ (e : ℕ) = 1 → i = 0 ∧ e = 0 := by
  decide +kernel

private noncomputable def gl23SdHom : CFSG.Open.SemidihedralGroup 4 →* GL23 :=
  sdHom gl23SdR gl23SdS gl23SdR_pow gl23SdS_pow gl23SdS_conj

private theorem card_range_gl23SdHom : Nat.card gl23SdHom.range ∣ 16 := by
  haveI : Finite (CFSG.Open.SemidihedralGroup 4) :=
    CFSG.Semidihedral.presentation_finite 4 (by norm_num)
  have hmul := Subgroup.card_ker_mul_card_range gl23SdHom
  rw [CFSG.Semidihedral.card 4 (by norm_num)] at hmul
  exact ⟨Nat.card gl23SdHom.ker, by rw [mul_comm]; exact hmul.symm⟩

private theorem exists_semidihedral_subgroup :
    ∃ S : Subgroup GL23, Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup 4) ∧
      Nat.card S = 16 := by
  haveI : Finite (CFSG.Open.SemidihedralGroup 4) :=
    CFSG.Semidihedral.presentation_finite 4 (by norm_num)
  obtain ⟨e⟩ := nonempty_mulEquiv_semidihedral (H := gl23SdHom.range)
    card_range_gl23SdHom
    (R := gl23SdR) (S := gl23SdS)
    ⟨CFSG.Semidihedral.r 4, sdHom_r gl23SdR gl23SdS gl23SdR_pow gl23SdS_pow gl23SdS_conj⟩
    ⟨CFSG.Semidihedral.s 4, sdHom_s gl23SdR gl23SdS gl23SdR_pow gl23SdS_pow gl23SdS_conj⟩
    gl23SdR_pow gl23SdS_pow gl23SdS_conj gl23Sd_independent
  refine ⟨gl23SdHom.range, ⟨e⟩, ?_⟩
  rw [Nat.card_congr e.toEquiv, CFSG.Semidihedral.card 4 (by norm_num)]
  norm_num

theorem gl23_two_subgroup_quaternion_or_semidihedral
    {P Q : Subgroup GL23} (hP : IsPGroup 2 P) (hQP : Q ≤ P)
    (hQ : Nonempty (↥Q ≃* QuaternionGroup 2)) :
    Nonempty (↥P ≃* QuaternionGroup 2) ∨
      Nonempty (↥P ≃* CFSG.Open.SemidihedralGroup 4) := by
  have hQcard : Nat.card Q = 8 := by
    obtain ⟨e⟩ := hQ
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h8dvd : 8 ∣ Nat.card P := by
    rw [← hQcard]
    exact Subgroup.card_dvd_of_le hQP
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have hdvd : 2 ^ n ∣ 48 := by
    rw [← hn, ← card_GL23]
    exact Subgroup.card_subgroup_dvd_card P
  have hn_le : n ≤ 4 := by
    by_contra h
    have h5 : 2 ^ 5 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have h248 : 2 ^ 5 ∣ 48 := h5.trans hdvd
    norm_num at h248
  have hn_ge : 3 ≤ n := by
    rw [hn] at h8dvd
    have h8' : 2 ^ 3 ∣ 2 ^ n := by simpa using h8dvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h8'
  have hn_cases : n = 3 ∨ n = 4 := by omega
  rcases hn_cases with rfl | rfl
  · left
    have hP8 : Nat.card P = 8 := by rw [hn]; norm_num
    have hQP_eq : P = Q :=
      (Subgroup.eq_of_le_of_card_ge hQP (by rw [hP8, hQcard])).symm
    obtain ⟨e⟩ := hQ
    exact ⟨(MulEquiv.subgroupCongr hQP_eq).trans e⟩
  · right
    have hP16 : Nat.card P = 16 := by rw [hn]; norm_num
    obtain ⟨S, ⟨eS⟩, hScard⟩ := exists_semidihedral_subgroup
    have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 4) (by rw [hScard]; norm_num)
    have hidxP : P.index = 3 := by
      have h := P.index_mul_card
      rw [hP16, card_GL23] at h
      omega
    have hidxS : S.index = 3 := by
      have h := S.index_mul_card
      rw [hScard, card_GL23] at h
      omega
    have hidxP_not : ¬ 2 ∣ P.index := by rw [hidxP]; norm_num
    have hidxS_not : ¬ 2 ∣ S.index := by rw [hidxS]; norm_num
    let SP : Sylow 2 GL23 := hP.toSylow hidxP_not
    let SS : Sylow 2 GL23 := hS2.toSylow hidxS_not
    have hSPcoe : (SP : Subgroup GL23) = P := by
      simpa [SP] using IsPGroup.toSylow_coe hP hidxP_not
    have hSScoe : (SS : Subgroup GL23) = S := by
      simpa [SS] using IsPGroup.toSylow_coe hS2 hidxS_not
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GL23 SS SP
    have eSS : ↥SS ≃* CFSG.Open.SemidihedralGroup 4 :=
      (MulEquiv.subgroupCongr hSScoe).trans eS
    have eConj : ↥SS ≃* ↥SP := hg ▸ SS.equivSMul g
    exact ⟨(MulEquiv.subgroupCongr hSPcoe).symm.trans (eConj.symm.trans eSS)⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
