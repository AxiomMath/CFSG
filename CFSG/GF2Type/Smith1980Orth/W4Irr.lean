module

public import CFSG.GF2Type.Smith1980Orth.FourW4
public import CFSG.LargeExtraspecial.DWW4Rank
import CFSG.GF2Type.Smith1980Orth.Ident

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.Open

section GLFourTwo

open Polynomial

private theorem matrix_pow_five_or_two_of_pow_ten (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (h : A ^ 10 = 1) : A ^ 5 = 1 ∨ A ^ 2 = 1 := by
  set μ := minpoly (ZMod 2) A
  have hint : IsIntegral (ZMod 2) A := Algebra.IsIntegral.isIntegral A
  have hμm : μ.Monic := minpoly.monic hint
  have hdeg : μ.natDegree ≤ 4 := by
    have h1 := natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly A) (Matrix.charpoly_monic A).ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h1
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    have : ((2 : ℕ) : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
    simpa using this
  have h5 : cyclotomic 5 (ZMod 2) * (X - 1) = X ^ 5 - 1 :=
    cyclotomic_prime_mul_X_sub_one (ZMod 2) 5
  have hfac : (X ^ 10 - 1 : (ZMod 2)[X]) = (X ^ 2 - 1) * (cyclotomic 5 (ZMod 2)) ^ 2 := by
    linear_combination (-(cyclotomic 5 (ZMod 2) * (X - 1) + (X ^ 5 - 1))) * h5 +
      (X ^ 5 - 1 + (cyclotomic 5 (ZMod 2)) ^ 2 * (1 - X)) * h2
  have h10 : μ ∣ X ^ 10 - 1 := minpoly.dvd (ZMod 2) A (by simp [h])
  by_cases hd : cyclotomic 5 (ZMod 2) ∣ μ
  · left
    have hΦdeg : (cyclotomic 5 (ZMod 2)).natDegree = 4 := by
      rw [natDegree_cyclotomic]
      decide
    have heq : μ = cyclotomic 5 (ZMod 2) :=
      eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.monic 5 (ZMod 2)) hμm hd
        (by rw [hΦdeg]; exact hdeg)
    have h5' : μ ∣ X ^ 5 - 1 := by
      rw [heq, ← h5]
      exact dvd_mul_right _ _
    obtain ⟨r, hr⟩ := h5'
    have h4 : aeval A (X ^ 5 - 1 : (ZMod 2)[X]) = 0 := by
      rw [hr, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero] using h4
  · right
    have hcop : IsCoprime (cyclotomic 5 (ZMod 2)) μ :=
      (S2.irreducible_cyclotomic_five.coprime_iff_not_dvd).mpr hd
    have hcop2 : IsCoprime μ ((cyclotomic 5 (ZMod 2)) ^ 2) := (hcop.pow_left (m := 2)).symm
    have h3 : μ ∣ X ^ 2 - 1 := hcop2.dvd_of_dvd_mul_right (by rw [← hfac]; exact h10)
    obtain ⟨r, hr⟩ := h3
    have h4 : aeval A (X ^ 2 - 1 : (ZMod 2)[X]) = 0 := by
      rw [hr, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero] using h4

theorem GL4_pow_five_or_two_of_pow_ten (g : GL (Fin 4) (ZMod 2)) (h : g ^ 10 = 1) :
    g ^ 5 = 1 ∨ g ^ 2 = 1 := by
  have hm : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ 10 = 1 := by
    have := congrArg (fun u : GL (Fin 4) (ZMod 2) => (u : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
    simpa [Units.val_pow_eq_pow_val] using this
  rcases matrix_pow_five_or_two_of_pow_ten _ hm with h5 | h2
  · left
    apply Units.ext
    simpa [Units.val_pow_eq_pow_val] using h5
  · right
    apply Units.ext
    simpa [Units.val_pow_eq_pow_val] using h2

end GLFourTwo

private theorem false_of_prod_equiv {M K : Type} [Group M] [Group K] [Finite K]
    (e : M ≃* Equiv.Perm (Fin 3) × K) (h5 : 5 ∣ Nat.card K)
    (hno : ∀ y : M, y ^ 10 = 1 → y ^ 5 = 1 ∨ y ^ 2 = 1) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hτ10 : (Equiv.swap (0 : Fin 3) 1) ^ 10 = 1 := by decide
  have hτ5 : (Equiv.swap (0 : Fin 3) 1) ^ 5 ≠ 1 := by decide
  have hg5 : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
  have hg10 : g ^ 10 = 1 := by rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, hg5, one_pow]
  have hy : (e.symm (Equiv.swap (0 : Fin 3) 1, g)) ^ 10 = 1 := by
    rw [← map_pow, Prod.pow_def, hτ10, hg10]
    exact (map_eq_one_iff _ e.symm.injective).mpr rfl
  rcases hno _ hy with h | h
  · have h' := congrArg e h
    rw [map_pow, MulEquiv.apply_symm_apply, map_one, Prod.pow_def] at h'
    exact hτ5 (congrArg Prod.fst h')
  · have h' := congrArg e h
    rw [map_pow, MulEquiv.apply_symm_apply, map_one, Prod.pow_def] at h'
    have hg2 : g ^ 2 = 1 := congrArg Prod.snd h'
    have := orderOf_dvd_of_pow_eq_one hg2
    rw [hg] at this
    omega

private theorem card_eq_six_mul {M K : Type} [Group M] [Group K]
    (e : M ≃* Equiv.Perm (Fin 3) × K) : Nat.card M = 6 * Nat.card K := by
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin]
  rfl

private theorem omegaOdd_two_true : omegaOdd true 2 = 9 := by decide

private theorem omegaOdd_two_false : omegaOdd false 2 = 15 := by decide

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem OrthData.card_omega_of_width_eq_four (O : OrthData S) (hw : S.width = 4) :
    (timmesfeldPlusType O.q → Nat.card (timmesfeldOmega O.q) = 36) ∧
      (¬ timmesfeldPlusType O.q → Nat.card (timmesfeldOmega O.q) = 60) := by
  have h2 : S.width / 2 = 2 := by omega
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · have h := O.card_omega_exact true ⟨fun _ => hp, fun _ => rfl⟩
    rw [h2, omegaOdd_two_true] at h
    rw [h]
    norm_num
  · have h := O.card_omega_exact false ⟨fun h => absurd h (by simp), fun h => absurd h hp⟩
    rw [h2, omegaOdd_two_false] at h
    rw [h]
    norm_num

theorem OrthData.not_isReducible_of_width_eq_four [IsSimpleGroup G]
    (hThmA : DW.W4Rank.TheoremAWidthFour) (O : OrthData S) (hw : S.width = 4)
    (hne : ∃ g₀ : G, g₀ * S.z * g₀⁻¹ ∈ S.QG ∧ g₀ * S.z * g₀⁻¹ ≠ S.z) : ¬ S.IsReducible := by
  intro hred
  obtain ⟨A, hEA, hA, hM⟩ := hThmA G S hw hne hred
  have hdvd : Nat.card S.Mbar ∣ 20160 := DW.W4Rank.card_Mbar_dvd_of_maxEA hw hA hM
  obtain ⟨eGL⟩ := DW.nonempty_linearEquiv_mulEquiv_GL (hA.finrank_clSub.trans hw)
  have hinj : Function.Injective fun x : S.Mbar => eGL (DW.resAt S A hM x) :=
    eGL.injective.comp (hA.resAt_injective hM)
  have hno : ∀ y : S.Mbar, y ^ 10 = 1 → y ^ 5 = 1 ∨ y ^ 2 = 1 := by
    intro y hy
    have hg : (eGL (DW.resAt S A hM y)) ^ 10 = 1 := by
      rw [← map_pow, ← map_pow, hy, map_one, map_one]
    rcases GL4_pow_five_or_two_of_pow_ten _ hg with h | h
    · left
      apply hinj
      show eGL (DW.resAt S A hM (y ^ 5)) = eGL (DW.resAt S A hM 1)
      rw [map_pow, map_pow, map_one, map_one]
      exact h
    · right
      apply hinj
      show eGL (DW.resAt S A hM (y ^ 2)) = eGL (DW.resAt S A hM 1)
      rw [map_pow, map_pow, map_one, map_one]
      exact h
  obtain ⟨h36, h60⟩ := O.card_omega_of_width_eq_four hw
  have hiso := O.card_isometries
  by_cases hp : timmesfeldPlusType O.q
  · have h36' := h36 hp
    rcases O.iso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hc := card_eq_six_mul e
      rw [h36'] at hc
      rw [hc] at hdvd
      norm_num at hdvd
    · have hc := card_eq_six_mul e
      rw [hiso, h36'] at hc
      rw [hc] at hdvd
      norm_num at hdvd
  · have h60' := h60 hp
    rcases O.iso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · haveI : Finite (timmesfeldOmega O.q) := Nat.finite_of_card_ne_zero (by omega)
      exact false_of_prod_equiv e (by rw [h60']; norm_num) hno
    · haveI : Finite (timmesfeldIsometries O.q) :=
        Nat.finite_of_card_ne_zero (by rw [hiso, h60']; norm_num)
      exact false_of_prod_equiv e (by rw [hiso, h60']; norm_num) hno

theorem fourW4Input_of_thmA (hAS : S14.AschbacherSmithW4Input)
    (hThmA : DW.W4Rank.TheoremAWidthFour) : FourW4Input := by
  intro G _ _ _ S O hw
  by_cases hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z
  · exfalso
    obtain ⟨e⟩ := hAS G S hw (fun P hP => (O.card_le_of_isPGroup_of_width_eq_four hw P hP).trans
      (by norm_num)) hW
    have h := FS77.factorization_card_timmesfeldPSU (m := 6) (by norm_num)
    rw [← Nat.card_congr e.toEquiv] at h
    exact O.factorization_ne_fifteen hw (by rw [h])
  · push Not at hW
    obtain ⟨g, hgQ, hne⟩ := hW
    by_contra hno
    have hcomm : ∀ x y : G, IsConj S.z x → x ∈ S.QG → IsConj S.z y → y ∈ S.QG →
        x * y = y * x := by
      intro x y hx hxQ hy hyQ
      by_contra hxy
      exact hno ⟨x, y, hx, hy, S14.SmithQ.orderOf_mul_eq_four S hxQ hyQ
        (S14.SmithQ.mul_self_eq_one_of_isConj S hx) (S14.SmithQ.mul_self_eq_one_of_isConj S hy) hxy⟩
    exact O.not_isReducible_of_width_eq_four hThmA hw ⟨g, hgQ, hne⟩
      (S14.SmithQ.isReducible_of_commute S (by omega) (isConj_iff.mpr ⟨g, rfl⟩) hgQ hne hcomm)

end CFSG.GF2Type.Smith1980Orth
