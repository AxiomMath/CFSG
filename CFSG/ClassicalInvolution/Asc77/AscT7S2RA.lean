module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Model
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4


public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

@[expose] def TwinOuterVacOn (t : StatedLieTag) (M : CFSG.LieType.Universal.LieUniversal) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (ψ : M.K →* H) (R R' : Subgroup M.K) (x x' : M.K),
    TwinPairOn t M ψ R R' x x' → ∀ v : ↥(inducedAutOn ψ.range),
      (∀ r ∈ R, v * innerHom ψ r = innerHom ψ r * v) →
      (∀ r ∈ R', v * innerHom ψ r = innerHom ψ r * v) →
      v * v * (v * v) = 1 → v * v = 1 ∨ v * v = innerHom ψ x

section Model

variable {P : Type} [Group P]

theorem twinOuterVacOn_of_autVac {t : StatedLieTag} (M : CFSG.LieType.Universal.LieUniversal)
    [Group.IsPerfect M.K] (π : M.K →* P) (hπ : Function.Surjective π)
    (hπk : π.ker = Subgroup.center M.K)
    (hvac : ∀ (R R' : Subgroup M.K) (x x' : M.K),
      R ∈ CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups t M.D →
      R' ∈ CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups t M.D → R ≠ R' →
      CFSG.ClassicalInvolution.Generic.Commutes R R' → x ∈ R → x * x = 1 → x ≠ 1 →
      x' ∈ R' → x' * x' = 1 → x' ≠ 1 → x' * x⁻¹ ∈ Subgroup.center M.K →
      ∀ φ : MulAut P, (∀ r ∈ R, φ (π r) = π r) → (∀ r ∈ R', φ (π r) = π r) →
        φ * φ * (φ * φ) = 1 → φ * φ = 1 ∨ φ * φ = MulAut.conj (π x)) :
    TwinOuterVacOn t M := by
  intro H _ _ ψ R R' x x' hpair v hvR hvR' hv4
  have hc : x' * x⁻¹ ∈ Subgroup.center M.K := by
    apply hpair.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpair.same, mul_inv_cancel]
  exact outer_of_autVac ψ hpair.ker π hπ hπk (R := R) (R' := R') (x := x)
    (hvac R R' x x' hpair.mem hpair.mem' hpair.ne hpair.comm hpair.hx hpair.hx2 hpair.hx1
      hpair.hx' hpair.hx'2 hpair.hx'1 hc) v hvR hvR' hv4

end Model

open CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
theorem twinOuterVac_psp2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSp 2 p e) :
    TwinOuterVacOn .PSp (CFSG.ClassicalInvolution.Generic.modelUniv .PSp 2 p e Fact.out) := by
  have hf : 1 ≤ e := hadm.2.1
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by omega)]
    omega
  have : Group.IsPerfect (CFSG.ClassicalInvolution.Generic.modelUniv .PSp 2 p e Fact.out).K :=
    Group.isPerfect_def.2 (modelClauseZero .PSp 2 p e Fact.out trivial hadm).1.1
  refine twinOuterVacOn_of_autVac (t := .PSp)
    (CFSG.ClassicalInvolution.Generic.modelUniv .PSp 2 p e Fact.out)
    (proj 2 (GaloisField p e)) proj_surjective ?_ ?_
  · exact ker_proj.trans (CFSG.LieType.Universal.Symplectic.center_eq 2 _).symm
  · intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc β hβ hβ' _
    left
    exact OuterSp4.psp4_autVac h2 h4
      ((exists_isLongRootSp2_iff h2 R).mpr ((mem_fundamentalSubgroups_PSp_iff hadm R).mp hR))
      ((exists_isLongRootSp2_iff h2 R').mpr ((mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'))
      hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc β hβ hβ'

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem twinOuterVac_psl4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ}
    (hadm : StatedLieAdmissible .PSL 4 p e) :
    TwinOuterVacOn .PSL (CFSG.ClassicalInvolution.Generic.modelUniv .PSL 4 p e Fact.out) := by
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have : Group.IsPerfect (CFSG.ClassicalInvolution.Generic.modelUniv .PSL 4 p e Fact.out).K :=
    Group.isPerfect_def.2 (modelClauseZero .PSL 4 p e Fact.out trivial hadm).1.1
  have hπk : (proj 4 (GaloisField p e)).ker = Subgroup.center SL(4, GaloisField p e) :=
    (ker_proj (n := 4) (K := GaloisField p e)).trans (scalars_eq_center 4 (GaloisField p e))
  refine twinOuterVacOn_of_autVac (t := .PSL)
    (CFSG.ClassicalInvolution.Generic.modelUniv .PSL 4 p e Fact.out)
    (proj 4 (GaloisField p e)) (proj_surjective 4 (GaloisField p e)) hπk ?_
  intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' hφ4
  exact OuterL4.psl4_autVac h2
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR)
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR')
    hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' hφ4

theorem twinOuterVac_psu4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSU 4 p e) :
    TwinOuterVacOn .PSU (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 4 p e Fact.out) := by
  have hf : 1 ≤ e := hadm.2.1
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul_eq hq
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have : Group.IsPerfect (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 4 p e Fact.out).K :=
    Group.isPerfect_def.2 (modelClauseZero .PSU 4 p e Fact.out trivial hadm).1.1
  refine twinOuterVacOn_of_autVac (t := .PSU)
    (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 4 p e Fact.out)
    ((QuotientGroup.mk' (Subgroup.center (Su (GaloisField p (2 * e)) p e 4))).comp
      φ.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp φ.surjective) ?_ ?_
  · ext x
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ x) : Su (GaloisField p (2 * e)) p e 4 ⧸ _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact mulEquiv_mem_center_iff φ x
  · intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc σ hσ hσ' hσ4
    have hne' : R.map φ.toMonoidHom ≠ R'.map φ.toMonoidHom := fun h =>
      hne (Subgroup.map_injective φ.injective h)
    have hc' : φ x' * (φ x)⁻¹ ∈ Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
      have := (mulEquiv_mem_center_iff φ (x' * x⁻¹)).mpr hc
      rwa [map_mul, map_inv] at this
    exact OuterU4.psu4_autVac hK hp2 hq ((hφ R).mp hR) ((hφ R').mp hR') hne' ⟨x, hxR, rfl⟩
      (by rw [← map_mul, hx2, map_one]) (fun h => hx1 (φ.injective (h.trans (map_one φ).symm)))
      ⟨x', hx'R', rfl⟩ (by rw [← map_mul, hx'2, map_one])
      (fun h => hx'1 (φ.injective (h.trans (map_one φ).symm))) hc' σ
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact hσ r hr)
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact hσ' r hr)
      hσ4

theorem twinOuterVac_of_small {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    {t : StatedLieTag} {n : ℕ} (hadm : StatedLieAdmissible t n p e)
    (hsh : (t = .PSp ∧ n = 2) ∨ (t = .PSL ∧ n = 4) ∨ (t = .PSU ∧ n = 4)) :
    TwinOuterVacOn t (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out) := by
  rcases hsh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact twinOuterVac_psp2 hp2 hq hadm
  · exact twinOuterVac_psl4 hp2 hadm
  · exact twinOuterVac_psu4 hp2 hq hadm

end CFSG.ClassicalInvolution.ModelFacts.Orth15
