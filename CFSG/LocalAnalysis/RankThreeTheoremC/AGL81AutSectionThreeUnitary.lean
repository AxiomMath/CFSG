module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeDefs
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
public import CFSG.Permutation.UnitaryThreeRecognition.ModelBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree

open CFSG.AGLEmbedding CFSG.UnitaryThreeRecognition.Model
open CFSG.BenderSuzuki.External CFSG.BenderSuzuki.MatrixGroups

theorem not_eight_dvd_four_mul_of_odd {n : ℕ} (hn : Odd n) : ¬ 8 ∣ 4 * n := by
  obtain ⟨j, rfl⟩ := hn
  intro h
  have h' : 4 * 2 ∣ 4 * (2 * j + 1) := by
    simpa [show (8 : ℕ) = 4 * 2 by norm_num] using h
  have h2 : 2 ∣ 2 * j + 1 := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 4)).mp h'
  obtain ⟨c, hc⟩ := h2
  omega

theorem not_dvd_card_units_of_card_eq_prime_pow_sq {K : Type} [Field K] {p f : ℕ}
    (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) (hf : 1 ≤ f) :
    ¬ p ∣ Nat.card Kˣ := by
  rw [Nat.card_units K, hK]
  intro hdiv
  have hf0 : f ≠ 0 := by omega
  have hpsq : p ∣ (p ^ f) ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left (dvd_pow_self p hf0) _
  have h1 : p ∣ (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) := Nat.dvd_sub hpsq hdiv
  rw [Nat.sub_sub_self (Nat.one_le_pow 2 (p ^ f) (pow_pos hp.pos f))] at h1
  exact hp.not_dvd_one h1

private theorem pow_three_eq_one_of_torus_action_fst {K : Type} [Field K]
    (J : HermitianForm 3 K) {t : Kˣ}
    (h : (t : K) * (J.conj (t : K))⁻¹ ^ 2 = 1) : t ^ 3 = 1 := by
  have ht_ne : (t : K) ≠ 0 := Units.ne_zero t
  have hc0 : J.conj (t : K) ≠ 0 := (map_ne_zero J.conj).2 ht_ne
  have ht_eq : (t : K) = J.conj (t : K) ^ 2 := by
    calc (t : K) = (t : K) * ((J.conj (t : K))⁻¹ * J.conj (t : K)) ^ 2 := by
          rw [inv_mul_cancel₀ hc0, one_pow, mul_one]
      _ = (t : K) * (J.conj (t : K))⁻¹ ^ 2 * J.conj (t : K) ^ 2 := by ring
      _ = 1 * J.conj (t : K) ^ 2 := by rw [h]
      _ = J.conj (t : K) ^ 2 := one_mul _
  have ht4 : (t : K) ^ 4 = (t : K) := by
    have hconj : J.conj (t : K) = (t : K) ^ 2 := by
      have := congrArg J.conj ht_eq
      simpa [map_pow] using this
    calc (t : K) ^ 4 = ((t : K) ^ 2) ^ 2 := by ring
      _ = J.conj (t : K) ^ 2 := by rw [← hconj]
      _ = (t : K) := ht_eq.symm
  have h3 : (t : K) ^ 3 = 1 := by
    apply mul_left_cancel₀ ht_ne
    rw [mul_one]
    calc (t : K) * (t : K) ^ 3 = (t : K) ^ 4 := by ring
      _ = (t : K) := ht4
  exact Units.ext (by simpa using h3)

theorem not_threeAutFour_lie_twistedA_two {d : TauCeti.ValidLieTypeIndex}
    {Q : TauCeti.PrimePower} (hd : d.1 = .twistedA 2 Q) (hQ : Q.p = 3) :
    ¬ ThreeAutFour (TauCeti.CFSGIndex.lie d).Group := by
  intro h
  have hu : IsUnitaryIndex 3 d := ⟨Q, hQ, hd⟩
  obtain ⟨hp, hf, -, K, hField, hFinite, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    CFSG.AGLEmbedding.UnitaryModel.exists_equiv_psu
      (CFSG.AGLEmbedding.UnitaryModel.statedClassicalModel hu ⟨MulEquiv.refl _⟩)
  letI := hField
  letI := hFinite
  have hPSU : ThreeAutFour (ProjectiveSpecialUnitaryMatrixGroup J) :=
    ThreeAutFour.of_injective (f := e.symm.toMonoidHom) e.symm.injective h
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  obtain ⟨k, hk⟩ := hPSU (rootGroup J hJ)
    (CFSG.AGLEmbedding.UnitaryModel.isPGroup_rootGroup J hJ hK hfix) (torus J hJ a)
    (torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ a))
  letI := CFSG.AGLEmbedding.UnitaryModel.charP_of_card hp hK
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    exact absurd ((CharP.cast_eq_zero_iff K 3 2).mp h0) (by norm_num)
  let z : Coord J := ⟨(1, -((2 : K)⁻¹)), by
    change -((2 : K)⁻¹) + J.conj (-((2 : K)⁻¹)) + 1 * J.conj 1 = 0
    rw [map_neg, map_inv₀, map_one, map_ofNat, one_mul]
    field_simp [h2]
    ring⟩
  have hz1 : z.1.1 = 1 := rfl
  set m : ℕ := 4 * 3 ^ k with hm
  have hcent := hk (root J hJ z) (root_mem_rootGroup J hJ z)
  have hact : hermitianTorusAction J (a ^ m) z = z := by
    apply root_injective J hJ
    rw [← torus_mul_root_mul_inv J hJ (a ^ m) z, map_pow, hcent]
    group
  set t : Kˣ := a ^ m with ht
  have hfst : (t : K) * (J.conj (t : K))⁻¹ ^ 2 = 1 := by
    have h1 := congrArg (fun w : Coord J => (w : K × K).1) hact
    simp only [hermitianTorusAction_fst, hz1, one_mul] at h1
    simpa [t] using h1
  have ht3 : t ^ 3 = 1 := pow_three_eq_one_of_torus_action_fst J hfst
  have h3not : ¬ 3 ∣ Nat.card Kˣ :=
    not_dvd_card_units_of_card_eq_prime_pow_sq Nat.prime_three hK hf
  have hcop3 : Nat.Coprime 3 (Nat.card Kˣ) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3not
  have ht1 : t = 1 := by
    have hord3 : orderOf t ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr ht3
    rcases (Nat.dvd_prime Nat.prime_three).mp hord3 with h1 | h3
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h3 ▸ orderOf_dvd_natCard t)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop3)
  have ham : a ^ m = 1 := by
    rw [← ht]
    exact ht1
  have h8m : 8 ∣ m := by
    have h8N : 8 ∣ Nat.card Kˣ := by
      rw [Nat.card_units K, hK]
      exact Nat.eight_dvd_sq_sub_one_of_odd (Odd.pow (by norm_num))
    exact h8N.trans (by
      rw [← ha]
      exact orderOf_dvd_iff_pow_eq_one.mpr ham)
  exact not_eight_dvd_four_mul_of_odd (Odd.pow (by norm_num)) (hm ▸ h8m)

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree
