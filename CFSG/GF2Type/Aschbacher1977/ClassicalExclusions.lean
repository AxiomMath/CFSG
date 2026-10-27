module

public import CFSG.Blueprint.Catalog
public import CFSG.LargeExtraspecial.S3Basic
import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4Uni
import CFSG.LargeExtraspecial.AS35WL4
import CFSG.LargeExtraspecial.AS35WU4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Aschbacher1977

open CFSG CFSG.Blueprint CFSG.LargeExtraspecial CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag Subgroup

section Adapters

theorem lieModel_PSL_four_three_one {G : Type} [Group G] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h3 : p ^ f = 3) (h : LieModel G .PSL 4 p f) : LieModel G .PSL 4 3 1 := by
  obtain ⟨rfl, rfl⟩ := GH74.Generic.eq_three_of_pow_eq_three hp hf h3
  exact h

theorem lieModel_PSU_four_three_one {G : Type} [Group G] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h3 : p ^ f = 3) (h : LieModel G .PSU 4 p f) : LieModel G .PSU 4 3 1 := by
  obtain ⟨rfl, rfl⟩ := GH74.Generic.eq_three_of_pow_eq_three hp hf h3
  exact h

end Adapters

variable {G : Type} [Group G] [Finite G]

private theorem dvd_of_dvd_card_centralizer {X : Type} [Group X] (S : Setting G)
    (hw : S.width = 2) (e : G ≃* X) {n : ℕ}
    (hn : n ∣ Nat.card ↥(centralizer ({e S.z} : Set X))) : n ∣ 2 ^ 8 * 3 ^ 2 * 5 := by
  rw [← GH74.GLS.IVK.GHInv.card_centralizer_eq_of_mulEquiv e S.z] at hn
  exact hn.trans (S.card_M_dvd_of_width_two hw)

theorem not_lieModel_PSL_four_of_ne_three (S : Setting G) (hw : S.width = 2) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h : LieModel G .PSL 4 p f) (h3 : p ^ f ≠ 3) :
    False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have hdvd := AS35W.sq_dvd_card_centralizer_L4 hodd (z := e S.z)
    (by rw [MulEquiv.orderOf_eq, S.orderOf_z])
  rw [hK] at hdvd
  exact h3 (AS35W.eq_three_of_sq_dvd hp hp2 hf (dvd_of_dvd_card_centralizer S hw e hdvd))

private theorem exists_unitaryData_equiv_four {X : Type} [Group X] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hL : LieModel X .PSU 4 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData p f K),
      Nonempty (X ≃* hypPSU h 2 0) := by
  obtain ⟨K, _, _, hcard, ⟨e₀⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (p ^ f) ^ 2 ∧
        Nonempty (X ≃* Assembly.LowTwoRank.StatedProj
          (Assembly.LowTwoRank.StatedSU 4 (p ^ f) K)) := by
    rcases hL with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hc.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  exact ⟨K, inferInstance, inferInstance, h,
    ⟨e₀.trans (hypPSUEquivStatedProj (r := 2) (ε := 0) h hR₀ (by omega)).symm⟩⟩

private theorem sq_dvd_card_centralizer_U4_of_ne_seven {p f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (h8 : p ^ f % 8 ≠ 7) {z : hypPSU h 2 0}
    (hz : orderOf z = 2) :
    (p ^ f) ^ 2 ∣ Nat.card (centralizer ({z} : Set (hypPSU h 2 0))) := by
  obtain ⟨A, rfl⟩ := hypProj_surjective h 2 0 z
  obtain ⟨l, hl0, -, hcases⟩ :=
    CFSG.ComponentClassification.CatFactsL4U4.InvClassU.classify_inv_U4 h hp2 A.2.1
      (CFSG.ClassicalInvolution.Q3.TA3.L4U4.orderOf_mk_eq_two h hz)
  rcases hcases with ⟨hN, ⟨v, hv, hAv⟩ | ⟨d, hd, v, hv, hAv⟩⟩ |
    ⟨hN, e, g, hAe, hAg, hee, hgg, heg⟩
  · exact AS35W.sq_dvd_of_orthogonal hl0 hN hv hAv
  · exact (CFSG.ClassicalInvolution.Q3.TA3.L4U4.false_of_D1 h hp2 h8 hd hv hAv).elim
  · exact AS35W.sq_dvd_of_paired hl0 hN hAe hAg hee hgg heg

theorem not_lieModel_PSU_four_of_ne_three (S : Setting G) (hw : S.width = 2) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : p ^ f % 8 ≠ 7) (h : LieModel G .PSU 4 p f)
    (h3 : p ^ f ≠ 3) : False := by
  obtain ⟨K, _, _, h', ⟨e⟩⟩ := exists_unitaryData_equiv_four hp hf h
  have hz : orderOf (e S.z) = 2 := by
    rw [MulEquiv.orderOf_eq, S.orderOf_z]
  have hdvd := sq_dvd_card_centralizer_U4_of_ne_seven h' hp2 hq hz
  exact h3 (AS35W.eq_three_of_sq_dvd hp hp2 hf (dvd_of_dvd_card_centralizer S hw e hdvd))

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.Stage2.Signalizer in
theorem not_lieModel_PSL_five (S : Setting G) (hw : S.width = 2) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hq : p ^ f % 4 = 3) (h : LieModel G .PSL 5 p f) : False := by
  have hp2 : p ≠ 2 := AS35W.ne_two_of_mod_four hf (Or.inl hq)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have hz2 : e S.z ^ 2 = 1 := by
    have := pow_orderOf_eq_one (e S.z)
    rwa [MulEquiv.orderOf_eq, S.orderOf_z] at this
  obtain ⟨g, hg⟩ := proj_surjective 5 K (e S.z)
  have : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K ≠ 2 := by
    rw [Ne, FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hK]
    have : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    obtain ⟨k, hk⟩ := this
    omega
  have hz2' : proj 5 K g ^ 2 = 1 := by rw [hg]; exact hz2
  have hB : conjAut (3 + 2) K (Matrix.SpecialLinearGroup.toGL g) ^ 2 = 1 := by
    change conjAut 5 K (Matrix.SpecialLinearGroup.toGL g) ^ 2 = 1
    rw [conjAut_toGL, ← map_pow, hz2', map_one]
  obtain ⟨ρ, hρ, hfix⟩ := Odd87.exists_fixed_sl3_block hchar _ hB
  have hle : ρ.range ≤ centralizer ({e S.z} : Set (projectiveSL 5 K)) := by
    rw [← hg]
    rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := hfix s
    change conjAut 5 K (Matrix.SpecialLinearGroup.toGL g) (ρ s) = ρ s at h1
    rw [conjAut_toGL, MulAut.conj_apply] at h1
    calc ρ s * proj 5 K g = proj 5 K g * ρ s * (proj 5 K g)⁻¹ * proj 5 K g := by rw [h1]
      _ = proj 5 K g * ρ s := by group
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv] at hdvd
  have h3 : (p ^ f) ^ 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [card_SL_eq (by norm_num), hK]
    exact Dvd.intro _ rfl
  exact AS35W.not_cube_dvd hp hp2 hf (dvd_of_dvd_card_centralizer S hw e (h3.trans hdvd))

open CFSG.GH74.GLS.Stage2.Signalizer in
theorem not_lieModel_PSU_five (S : Setting G) (hw : S.width = 2) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hq : p ^ f % 4 = 1) (h : LieModel G .PSU 5 p f) : False := by
  have hp2 : p ≠ 2 := AS35W.ne_two_of_mod_four hf (Or.inr hq)
  obtain ⟨K, _, _, hdat, -, ⟨e⟩⟩ := Odd87.exists_unitaryData_equiv hp hf h
  have hz2 : e S.z ^ 2 = 1 := by
    have := pow_orderOf_eq_one (e S.z)
    rwa [MulEquiv.orderOf_eq, S.orderOf_z] at this
  have hα : (MulAut.conj (e S.z)) ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  rcases Odd87.unitary5_involution_cases hdat hp2 _ hα with ⟨ψ, hψ, hfix⟩ | ⟨hni, -⟩
  · have hle : ((hypProj hdat 2 1).comp ψ).range ≤ centralizer ({e S.z} : Set _) := by
      intro s hs
      rw [mem_centralizer_singleton_iff]
      have h1 := hfix s hs
      rw [MulAut.conj_apply] at h1
      calc s * e S.z = e S.z * s * (e S.z)⁻¹ * e S.z := by rw [h1]
        _ = e S.z * s := by group
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv] at hdvd
    have h3 : (p ^ f) ^ 3 ∣ Nat.card ↥(unitarySU p f K 3) := by
      rw [Odd87.card_unitarySU_three hdat, mul_assoc]
      exact Dvd.intro _ rfl
    exact AS35W.not_cube_dvd hp hp2 hf (dvd_of_dvd_card_centralizer S hw e (h3.trans hdvd))
  · exact hni (e S.z) rfl

end CFSG.GF2Type.Aschbacher1977
