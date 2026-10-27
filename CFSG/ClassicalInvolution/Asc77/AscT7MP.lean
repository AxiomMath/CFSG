module

public import CFSG.ClassicalInvolution.Asc77.AscT7MO
public import CFSG.ClassicalInvolution.Asc77.AscT7JSq
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterGen

public section

namespace CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Asc77.FrameVertex
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {e : ℕ}


theorem twinSqAlpha_psl4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hadm : StatedLieAdmissible .PSL 4 p e) :
    TwinSqAlpha p e .PSL 4 := by
  have he : e ≠ 0 := by have := hadm.2.1; omega
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  have : Group.IsPerfect (modelUniv .PSL 4 p e Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSL 4 p e Fact.out trivial hadm).1.1
  set π : (modelUniv .PSL 4 p e Fact.out).K →* projectiveSL 4 (GaloisField p e) :=
    proj 4 (GaloisField p e) with hπdef
  have hπk : π.ker = Subgroup.center (modelUniv .PSL 4 p e Fact.out).K :=
    (ker_proj (n := 4) (K := GaloisField p e)).trans (scalars_eq_center 4 (GaloisField p e))
  have hπ : Function.Surjective π := proj_surjective 4 (GaloisField p e)
  intro H _ _ ψ R R' x x' hpair k hkR hkk v hvR hvR' hvv
  have hc : x' * x⁻¹ ∈ Subgroup.center (modelUniv .PSL 4 p e Fact.out).K := by
    apply hpair.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpair.same, mul_inv_cancel]
  set θ := outerAction ψ hpair.ker π hπ hπk with hθdef
  have hθinj : Function.Injective θ :=
    (injective_iff_map_eq_one θ).mpr fun w hw =>
      eq_one_of_outerAction_eq_one ψ hpair.ker π hπ hπk hw
  set ι : projectiveSL 4 (GaloisField p e) →* ↥(inducedAutOn ψ.range) :=
    ((innerHom ψ).range.subtype).comp (outerEquiv ψ hpair.ker π hπ hπk).toMonoidHom with hιdef
  have hιπ : ∀ s : (modelUniv .PSL 4 p e Fact.out).K, ι (π s) = innerHom ψ s := fun s =>
    outerEquiv_apply ψ hpair.ker π hπ hπk s
  have hθι : ∀ q, θ (ι q) = MulAut.conj q := by
    intro q
    obtain ⟨s, rfl⟩ := hπ q
    rw [hιπ, hθdef, outerAction_innerHom]
  have hfix : ∀ r : (modelUniv .PSL 4 p e Fact.out).K,
      v * innerHom ψ r = innerHom ψ r * v → θ v (π r) = π r := by
    intro r hr
    apply (outerEquiv ψ hpair.ker π hπ hπk).injective
    apply Subtype.ext
    rw [hθdef, outerAction_apply, outerEquiv_apply, hr]
    group
  have hφ2 : θ v * θ v = MulAut.conj (π x) := by
    rw [← map_mul, hvv, hθdef, outerAction_innerHom]
  have hkk' : π k * π k = π x := by
    have h1 : k * k * x⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hkk, mul_inv_cancel]
    have h3 : k * k * x⁻¹ ∈ π.ker := by
      rw [hπk]
      exact hpair.ker h1
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv] at h3
    exact mul_inv_eq_one.mp h3
  obtain ⟨Γ, hΓ1, hΓ2⟩ := ModelFacts.Orth15.SqL4.exists_Gamma h2
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num)
      hpair.mem)
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num)
      hpair.mem')
    hpair.ne hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 hc hkR hkk'
    (fun r hr => hfix r (hvR r hr)) (fun r hr => hfix r (hvR' r hr)) hφ2
  have hy : θ (innerHom ψ k * v) = conjAut 4 (GaloisField p e) Γ *
      conjAut 4 (GaloisField p e) (ModelFacts.Orth15.SqL4.dGL 1) *
        (conjAut 4 (GaloisField p e) Γ)⁻¹ := by
    rw [← hΓ1, map_mul, hθdef, outerAction_innerHom]
    rfl
  have hz : innerHom ψ x = ι (conjAut 4 (GaloisField p e) Γ
      (proj 4 (GaloisField p e) (ModelFacts.Orth15.InnerL4.x0 (GaloisField p e)))) := by
    rw [← hΓ2]
    exact (hιπ x).symm
  have key := ModelFacts.Orth15.SqL4.alphaOf_klein_conj h2 h4 hθinj hθι Γ hy hz
  rw [Set.pair_comm]
  exact key

end CFSG.ClassicalInvolution.Asc77
