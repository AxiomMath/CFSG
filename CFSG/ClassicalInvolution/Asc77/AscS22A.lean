module

public import CFSG.ClassicalInvolution.Asc77.AscT7MD
public import CFSG.ClassicalInvolution.Asc77.AscT7MF
import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Model
import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S22

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Asc77.FrameVertex

section Generic

variable {P : Type} [Group P]

theorem noV_of_autSq {t : StatedLieTag} (M : LieUniversal) [Group.IsPerfect M.K]
    (π : M.K →* P) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center M.K)
    (hnc : ∀ R ∈ fundamentalSubgroups t M.D, ∀ r ∈ R, r ∈ Subgroup.center M.K → r = 1)
    (hsq : ∀ (R R' : Subgroup M.K) (x x' : M.K), R ∈ fundamentalSubgroups t M.D →
      R' ∈ fundamentalSubgroups t M.D → R ≠ R' → Commutes R R' → x ∈ R → x * x = 1 → x ≠ 1 →
      x' ∈ R' → x' * x' = 1 → x' ≠ 1 → x' * x⁻¹ ∈ Subgroup.center M.K →
      ∀ φ : MulAut P, (∀ r ∈ R, φ (π r) = π r) → (∀ r ∈ R', φ (π r) = π r) →
        φ * φ = MulAut.conj (π x) → φ * φ = 1)
    {H : Type} [Group H] [Finite H] (ψ : M.K →* H) (R R' : Subgroup M.K) (x x' : M.K)
    (hpair : TwinPairOn t M ψ R R' x x')
    (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvv : v * v = FrameVertex.innerHom ψ x) : False := by
  have hc : x' * x⁻¹ ∈ Subgroup.center M.K := by
    apply hpair.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpair.same, mul_inv_cancel]
  have hfix : ∀ r : M.K, v * innerHom ψ r = innerHom ψ r * v →
      outerAction ψ hpair.ker π hπ hπk v (π r) = π r := by
    intro r hr
    apply (outerEquiv ψ hpair.ker π hπ hπk).injective
    apply Subtype.ext
    rw [outerAction_apply, outerEquiv_apply, hr]
    group
  have hφ : outerAction ψ hpair.ker π hπ hπk v * outerAction ψ hpair.ker π hπ hπk v =
      MulAut.conj (π x) := by
    rw [← map_mul, hvv, outerAction_innerHom]
  have h1 := hsq R R' x x' hpair.mem hpair.mem' hpair.ne hpair.comm hpair.hx hpair.hx2 hpair.hx1
    hpair.hx' hpair.hx'2 hpair.hx'1 hc (outerAction ψ hpair.ker π hπ hπk v)
    (fun r hr => hfix r (hvR r hr)) (fun r hr => hfix r (hvR' r hr)) hφ
  have hv2 : v * v = 1 := by
    apply eq_one_of_outerAction_eq_one ψ hpair.ker π hπ hπk
    rw [map_mul, h1]
  have hxker : innerHom ψ x = 1 := by rw [← hvv, hv2]
  have hxπ : x ∈ π.ker := by
    rw [ker_eq_innerHom_ker ψ hpair.ker π hπk, MonoidHom.mem_ker]
    exact hxker
  rw [hπk] at hxπ
  exact hpair.hx1 (hnc R hpair.mem x hpair.hx hxπ)

end Generic


section Rows

variable {p : ℕ} [Fact p.Prime] {e : ℕ}

open CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
theorem noV_psp2 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hadm : StatedLieAdmissible .PSp 2 p e)
    {H : Type} [Group H] [Finite H] (ψ : (modelUniv .PSp 2 p e Fact.out).K →* H)
    (R R' : Subgroup (modelUniv .PSp 2 p e Fact.out).K)
    (x x' : (modelUniv .PSp 2 p e Fact.out).K)
    (hpair : TwinPairOn .PSp (modelUniv .PSp 2 p e Fact.out) ψ R R' x x')
    (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvv : v * v = FrameVertex.innerHom ψ x) : False := by
  have hf : 1 ≤ e := hadm.2.1
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by omega)]
    omega
  have : Group.IsPerfect (modelUniv .PSp 2 p e Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSp 2 p e Fact.out trivial hadm).1.1
  refine noV_of_autSq (t := .PSp) (modelUniv .PSp 2 p e Fact.out)
    (proj 2 (GaloisField p e)) proj_surjective ?_ ?_ ?_ ψ R R' x x' hpair v hvR hvR' hvv
  · exact ker_proj.trans (CFSG.LieType.Universal.Symplectic.center_eq 2 _).symm
  · exact fund_noncentral_modelUniv trivial hadm (by simp)
  · intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc β hβ hβ' _
    exact OuterSp4.psp4_autVac h2 h4
      ((exists_isLongRootSp2_iff h2 R).mpr ((mem_fundamentalSubgroups_PSp_iff hadm R).mp hR))
      ((exists_isLongRootSp2_iff h2 R').mpr ((mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'))
      hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc β hβ hβ'

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
open scoped MatrixGroups in
theorem noV_psl4_three (hp2 : p ≠ 2) (hq : p ^ e % 4 = 3)
    (hadm : StatedLieAdmissible .PSL 4 p e)
    {H : Type} [Group H] [Finite H] (ψ : (modelUniv .PSL 4 p e Fact.out).K →* H)
    (R R' : Subgroup (modelUniv .PSL 4 p e Fact.out).K)
    (x x' : (modelUniv .PSL 4 p e Fact.out).K)
    (hpair : TwinPairOn .PSL (modelUniv .PSL 4 p e Fact.out) ψ R R' x x')
    (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvv : v * v = FrameVertex.innerHom ψ x) : False := by
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hnsq := not_isSquare_neg_one_galoisField (p := p) hq (by have := hadm.2.1; omega)
  have : Group.IsPerfect (modelUniv .PSL 4 p e Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSL 4 p e Fact.out trivial hadm).1.1
  have hπk : (proj 4 (GaloisField p e)).ker = Subgroup.center SL(4, GaloisField p e) :=
    (ker_proj (n := 4) (K := GaloisField p e)).trans (scalars_eq_center 4 (GaloisField p e))
  refine noV_of_autSq (t := .PSL) (modelUniv .PSL 4 p e Fact.out)
    (proj 4 (GaloisField p e)) (proj_surjective 4 (GaloisField p e)) hπk
    (fund_noncentral_modelUniv trivial hadm (by simp)) ?_ ψ R R' x x' hpair v hvR hvR' hvv
  intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' hφ2
  exact absurd (OuterL4.psl4_autSq h2
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR)
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR')
    hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' hφ2) hnsq

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.ClassicalInvolution.Phan in
theorem noV_psu4_one (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ e) (hq : p ^ e % 4 = 1)
    (hadm : StatedLieAdmissible .PSU 4 p e)
    {H : Type} [Group H] [Finite H] (ψ : (modelUniv .PSU 4 p e Fact.out).K →* H)
    (R R' : Subgroup (modelUniv .PSU 4 p e Fact.out).K)
    (x x' : (modelUniv .PSU 4 p e Fact.out).K)
    (hpair : TwinPairOn .PSU (modelUniv .PSU 4 p e Fact.out) ψ R R' x x')
    (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvv : v * v = FrameVertex.innerHom ψ x) : False := by
  have hf : 1 ≤ e := hadm.2.1
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.card_galoisField_two_mul_eq hq5
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have : Group.IsPerfect (modelUniv .PSU 4 p e Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSU 4 p e Fact.out trivial hadm).1.1
  have h2K : (2 : GaloisField p (2 * e)) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField (2 * e) hp2
  refine noV_of_autSq (t := .PSU) (modelUniv .PSU 4 p e Fact.out)
    ((QuotientGroup.mk' (Subgroup.center (Su (GaloisField p (2 * e)) p e 4))).comp
      φ.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp φ.surjective) ?_
    (fund_noncentral_modelUniv trivial hadm (by simp)) ?_ ψ R R' x x' hpair v hvR hvR' hvv
  · ext x
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ x) : Su (GaloisField p (2 * e)) p e 4 ⧸ _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact CFSG.ClassicalInvolution.ModelFacts.Orth15.mulEquiv_mem_center_iff φ x
  · intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc σ hσ hσ' hσ2
    exfalso
    have hne' : R.map φ.toMonoidHom ≠ R'.map φ.toMonoidHom := fun h =>
      hne (Subgroup.map_injective φ.injective h)
    have hc' : φ x' * (φ x)⁻¹ ∈ Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
      have := (CFSG.ClassicalInvolution.ModelFacts.Orth15.mulEquiv_mem_center_iff φ
        (x' * x⁻¹)).mpr hc
      rwa [map_mul, map_inv] at this
    obtain ⟨ι, hι1, hι2⟩ := OuterU4.psu4_autSq hK hp2 hq5 ((hφ R).mp hR) ((hφ R').mp hR') hne'
      ⟨x, hxR, rfl⟩ (by rw [← map_mul, hx2, map_one])
      (fun h => hx1 (φ.injective (h.trans (map_one φ).symm))) ⟨x', hx'R', rfl⟩
      (by rw [← map_mul, hx'2, map_one])
      (fun h => hx'1 (φ.injective (h.trans (map_one φ).symm))) hc' σ
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact hσ r hr)
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact hσ' r hr)
      (by rw [hσ2]; rfl)
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hι2
    exact no_norm_one_sqrt_neg_one h2K (p ^ e) hq ι hι1 hι2

end Rows

end S22

end CFSG.ClassicalInvolution.Asc77
