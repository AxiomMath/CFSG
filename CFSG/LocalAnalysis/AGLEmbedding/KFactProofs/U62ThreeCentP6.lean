module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.U62ThreeCentFrame
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.U62ThreeCentComb
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.U62ThreeCentDet
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU62Fix
import CFSG.RankThree.PartOne.Q1327C.BU5Diag
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.U62ThreeCentGroup

public section

namespace CFSG.AGLEmbedding.U62ThreeCent

open Matrix Equiv
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

theorem exists_units_diag {g : GL (Fin 6) F4}
    (hg : ((g : Matrix (Fin 6) (Fin 6) F4)).IsDiag) : ∃ δ : Fin 6 → F4ˣ, g = diagGL6 δ := by
  have hdet : ((g : Matrix (Fin 6) (Fin 6) F4)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  have hdiag := hg.diagonal_diag
  have hne : ∀ i, ((g : Matrix (Fin 6) (Fin 6) F4)) i i ≠ 0 := by
    intro i hi
    apply hdet
    rw [← hdiag, det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  refine ⟨fun i => Units.mk0 _ (hne i), Units.ext ?_⟩
  rw [coe_diagGL6]
  exact hdiag.symm

theorem hasLarge_of_diag (a : gramSU uData M6) (δ : Fin 6 → F4ˣ)
    (hδ : (a : GL (Fin 6) F4) = diagGL6 δ) : HasLarge (a : P6) := by
  let φ : F4ˣ ≃* Multiplicative (ZMod 3) :=
    mulEquivOfCyclicCardEq (by rw [card_units_F4, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card])
  obtain ⟨σ, hσ3, hσ1, l, hl⟩ := exists_cycle_perm (fun i => Multiplicative.toAdd (φ (δ i)))
  set lam : F4ˣ := φ.symm (Multiplicative.ofAdd l) with hlam_def
  have hlam : ∀ i, δ (σ i) = lam * δ i := by
    intro i
    have h := hl i
    apply φ.injective
    rw [map_mul, hlam_def, MulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_ofAdd]
    simpa [add_comm] using h
  obtain ⟨y, hyC, hyN, hyE, hy3⟩ := exists_y a δ hδ σ hσ3 hσ1 lam hlam
  have hdiag : ((((⟨(a : GL (Fin 6) F4), a.2.1⟩ : GU6)) : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4).IsDiag := by
    change ((a : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).IsDiag
    rw [hδ, coe_diagGL6]
    exact isDiag_diagonal _
  have hEC : torusP6.range ≤ Subgroup.centralizer ({(a : P6)} : Set P6) := by
    rintro _ ⟨z, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := conj6_torusP6 hdiag z
    rw [conj6_gramSU] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  exact hasLarge_of_normalizer hEC isElemAbelian_range_torusP6.1 isElemAbelian_range_torusP6.2
    (by rw [card_range_torusP6]; norm_num) hyC hyN hyE (hy3 ▸ Subgroup.one_mem _)

theorem pow_three_eq_one_of_mem_of_not_nine_dvd {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (h3 : 3 ∣ 2 ^ f + 1) (h9 : ¬ 9 ∣ 2 ^ f + 1)
    (M : Matrix (Fin 6) (Fin 6) K) (g : gramSU h M)
    (hg : (g : primeFormP h M) ^ 3 = 1) :
    (g : GL (Fin 6) K) ^ 3 = 1 := by
  haveI : Finite K := h.finite
  haveI : CharP K 2 := h.charP
  have hmem : g ^ 3 ∈ normOneScalars h (gramSU h M) 6 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hg
  obtain ⟨c, -, -, hc⟩ := hmem
  have hA3 : ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ 3 = (c : K) • 1 := by
    have := congrArg (fun h : GL (Fin 6) K => (h : Matrix (Fin 6) (Fin 6) K)) hc
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar,
      scalar_apply] at this
    rw [smul_one_eq_diagonal]
    exact this
  have hdet : ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := g.2.2
  have h9K : ¬ 9 ∣ Nat.card Kˣ := by
    intro hdiv
    have hcard : Nat.card Kˣ = 2 ^ (2 * f) - 1 := by
      rw [Nat.card_units, h.card]
    rw [hcard] at hdiv
    have hsq : (2 : ℕ) ^ (2 * f) = (2 ^ f) ^ 2 := by
      rw [Nat.mul_comm 2 f, pow_mul]
    rw [hsq] at hdiv
    have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      simpa using Nat.pow_two_sub_pow_two (2 ^ f) 1
    rw [hfac] at hdiv
    have hnot3 : ¬ 3 ∣ 2 ^ f - 1 := by
      intro hd
      have h2 : 3 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h3 hd
      have hsub : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by
        have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        omega
      rw [hsub] at h2
      norm_num at h2
    have hcop9 : Nat.Coprime 9 (2 ^ f - 1) := by
      have hc3 : Nat.Coprime 3 (2 ^ f - 1) :=
        (Nat.prime_three.coprime_iff_not_dvd).mpr hnot3
      have h := (Nat.coprime_pow_left_iff (n := 2) (by norm_num) 3 (2 ^ f - 1)).mpr hc3
      simpa [show (9 : ℕ) = 3 ^ 2 by norm_num] using h
    exact h9 (hcop9.dvd_of_dvd_mul_right hdiv)
  have hc1 : (c : K) = 1 :=
    eq_one_of_det_eq_one_of_pow_three_eq_smul_of_char_two_of_not_nine_dvd h9K hdet hA3
  have hc1u : c = 1 := Units.ext hc1
  have hg3 : ((g ^ 3 : gramSU h M) : GL (Fin 6) K) = 1 := by
    rw [hc, hc1u, map_one]
  simpa using hg3

theorem pow_three_eq_one_of_mem (g : gramSU uData M6) (hg : (g : P6) ^ 3 = 1) :
    (g : GL (Fin 6) F4) ^ 3 = 1 :=
  pow_three_eq_one_of_mem_of_not_nine_dvd uData (by norm_num) (by norm_num) M6 g hg

theorem hasLarge_of_orderOf_eq_three {x : P6} (hx : orderOf x = 3) : HasLarge x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg3 : (g : GL (Fin 6) F4) ^ 3 = 1 := by
    refine pow_three_eq_one_of_mem g ?_
    have := pow_orderOf_eq_one (g : P6)
    rwa [hx] at this
  set g' : GU6 := ⟨(g : GL (Fin 6) F4), g.2.1⟩ with hg'
  have hg'3 : g' ^ 3 = 1 := Subtype.ext hg3
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three
  have hcomm : ∀ u ∈ Subgroup.zpowers g', ∀ v ∈ Subgroup.zpowers g', u * v = v * u := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ((Commute.refl g').zpow_zpow m n).eq
  have hpow : ∀ u ∈ Subgroup.zpowers g', u ^ 3 = 1 := by
    rintro _ ⟨m, rfl⟩
    have := zpow_comm g' m 3
    simpa [hg'3] using this
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m uData hζ
    (by norm_num : 3 ∣ 2 ^ 1 + 1) (Subgroup.zpowers g') hcomm hpow
  have hdiag := hP g' (Subgroup.mem_zpowers g')
  let a : gramSU uData M6 := ⟨(P : GL (Fin 6) F4)⁻¹ * g * (P : GL (Fin 6) F4), by
    simpa using conj_mem_gramSU uData M6 (inv_mem P.2) g.2⟩
  obtain ⟨δ, hδ⟩ := exists_units_diag (g := (a : GL (Fin 6) F4)) hdiag
  have hconj : conj6 P (a : P6) = (g : P6) := by
    rw [primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change (P : GL (Fin 6) F4) * ((P : GL (Fin 6) F4)⁻¹ * g * (P : GL (Fin 6) F4)) *
      (P : GL (Fin 6) F4)⁻¹ = g
    group
  rw [← hconj]
  exact (hasLarge_of_diag a δ hδ).map (conj6 P)

end CFSG.AGLEmbedding.U62ThreeCent
