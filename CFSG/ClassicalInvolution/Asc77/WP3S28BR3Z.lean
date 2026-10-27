module

public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinD
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain


public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28B

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Center

theorem sl3_center_no_involution {F : Type} [Field F] {g : SL(3, F)}
    (hg : g ∈ Subgroup.center SL(3, F)) (h2 : g * g = 1) : g = 1 := by
  obtain ⟨r, hr3, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have h1 : Matrix.scalar (Fin 3) (r * r) = (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [map_mul, hrg]
    have := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) h2
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  have hrr : r ^ 2 = 1 := by
    have := congrFun (congrFun h1 0) 0
    rw [pow_two]
    simpa [Matrix.scalar_apply] using this
  have hr1 : r = 1 := by
    have h3 : r ^ 3 = 1 := by simpa using hr3
    have := pow_gcd_eq_one.mpr ⟨h3, hrr⟩
    simpa using this
  apply Subtype.ext
  rw [← hrg, hr1, map_one]
  rfl

end Center

section SU3

variable {p e : ℕ} [Fact p.Prime]

open CFSG.LieType.Universal.Unitary in
theorem su3_center_no_involution (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSU 3 p e)
    {g : (modelUniv .PSU 3 p e Fact.out).K} (hg : g ∈ Subgroup.center _) (h2 : g * g = 1) :
    g = 1 := by
  have hf : 1 ≤ e := hadm.2.1
  have : NeZero (2 * e) := ⟨by omega⟩
  have hF : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.card_galoisField_two_mul_eq hq
  obtain ⟨φ, -⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have hEq := SUid_eq_statedSU (F := GaloisField p (2 * e)) (p := p) (f := e) hF 3
  let ψ : (modelUniv .PSU 3 p e Fact.out).K ≃*
      ↥(StatedSU 3 (p ^ e) (GaloisField p (2 * e))) :=
    φ.trans (MulEquiv.subgroupCongr hEq)
  have hc : ψ g ∈ Subgroup.center ↥(StatedSU 3 (p ^ e) (GaloisField p (2 * e))) := by
    rw [Subgroup.mem_center_iff] at hg ⊢
    intro y
    apply ψ.symm.injective
    simp only [map_mul, MulEquiv.symm_apply_apply]
    exact hg (ψ.symm y)
  have hnq : ((3 : ℕ), p ^ e) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  have hscal := (isQuasisimple_statedSU_of_card (F := GaloisField p (2 * e)) (p := p) (f := e)
    hF (n := 3) le_rfl hnq).2
  rw [hscal, Subgroup.mem_subgroupOf] at hc
  obtain ⟨c, hcg⟩ := hc
  have hdet := det_eq_one_of_mem_statedSU (ψ g).2
  have hψ2 : ψ g * ψ g = 1 := by rw [← map_mul, h2, map_one]
  have hψ2' : ((ψ g : GL (Fin 3) (GaloisField p (2 * e))) *
      (ψ g : GL (Fin 3) (GaloisField p (2 * e)))) = 1 := congrArg Subtype.val hψ2
  rw [← hcg] at hdet hψ2'
  have hc3 : (c : GaloisField p (2 * e)) ^ 3 = 1 := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_smul] using hdet
  have hc2 : (c : GaloisField p (2 * e)) ^ 2 = 1 := by
    have := congrArg (fun x : GL (Fin 3) (GaloisField p (2 * e)) =>
      ((x : GL (Fin 3) (GaloisField p (2 * e))) : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * e))))
      hψ2'
    have h0 := congrFun (congrFun this 0) 0
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h0
    rw [pow_two]
    exact h0
  have hc1F : (c : GaloisField p (2 * e)) = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hc3, hc2⟩
    simpa using this
  have hc1 : c = 1 := Units.ext hc1F
  have hψg : ψ g = 1 := by
    apply Subtype.ext
    rw [← hcg, hc1, map_one]
    rfl
  exact ψ.injective (by rw [hψg, map_one])

theorem center_no_involution_rank3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU) (hadm : StatedLieAdmissible t 3 p e)
    {g : (modelUniv t 3 p e Fact.out).K} (hg : g ∈ Subgroup.center _) (h2 : g * g = 1) :
    g = 1 := by
  rcases ht with rfl | rfl
  · exact sl3_center_no_involution (F := GaloisField p e) hg h2
  · exact su3_center_no_involution hp2 hq hadm hg h2

end SU3

section Image

variable {X H : Type*} [Group X] [Group H]

theorem odd_card_center_of_no_involution [Finite X]
    (h : ∀ g ∈ Subgroup.center X, g * g = 1 → g = 1) : Odd (Nat.card (Subgroup.center X)) := by
  by_contra hev
  have h2 : 2 ∣ Nat.card (Subgroup.center X) := by
    rcases Nat.not_odd_iff_even.mp hev with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hxx : x * x = 1 := by
    rw [← pow_two]
    exact hx ▸ pow_orderOf_eq_one x
  have := h (x : X) x.2 (congrArg Subtype.val hxx)
  have hx1 : x = 1 := Subtype.ext this
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem image_trivial_of_central_involution [Finite X] (ψ : X →* H)
    (hker : ψ.ker ≤ Subgroup.center X) (hperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hnoinv : ∀ g ∈ Subgroup.center X, g * g = 1 → g = 1) {u : X}
    (hu : ∀ g : X, ψ u * ψ g = ψ g * ψ u) (hsq : ψ u * ψ u = 1) : ψ u = 1 := by
  have hcen : u ∈ Subgroup.center X := S28.mem_center_of_map_commutes ψ hker hperf hu
  have hodd := odd_card_center_of_no_involution hnoinv
  have hpow : u ^ Nat.card (Subgroup.center X) = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨u, hcen⟩)
    exact congrArg Subtype.val this
  have h1 : (ψ u) ^ Nat.card (Subgroup.center X) = 1 := by rw [← map_pow, hpow, map_one]
  have h2 : (ψ u) ^ 2 = 1 := by rw [pow_two]; exact hsq
  have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  have hgcd : Nat.gcd (Nat.card (Subgroup.center X)) 2 = 1 :=
    Nat.coprime_two_right.mpr hodd
  rw [hgcd, pow_one] at h3
  exact h3

end Image

end CFSG.ClassicalInvolution.Asc77.S28B
