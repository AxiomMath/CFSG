module

public import CFSG.ClassicalInvolution.Asc77.AscT7MY
import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Model
public import CFSG.ClassicalInvolution.Asc77.AscT7JSq
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterGen

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.Dichotomy
  CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem alphaOf_klein_frameU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {X : Type} [Group X] [Finite X] {θ : X →* MulAut (PU K p f)} {ι : PU K p f →* X}
    (hθ : Function.Injective θ) (hι : ∀ x, θ (ι x) = MulAut.conj x) (Γ : Su K p f 4) {y z : X}
    (hy : ActsAsD K p f ((MulAut.conj (QuotientGroup.mk Γ : PU K p f))⁻¹ * θ y *
      MulAut.conj (QuotientGroup.mk Γ : PU K p f)) 3)
    (hz : z = ι (MulAut.conj (QuotientGroup.mk Γ : PU K p f) (QuotientGroup.mk (zA K p f)))) :
    alphaOf (Subgroup.closure ({z, y} : Set X)) = ⊥ := by
  set σ : MulAut (PU K p f) := MulAut.conj (QuotientGroup.mk Γ) with hσ
  set θ' : X →* MulAut (PU K p f) := (MulAut.conj σ⁻¹).toMonoidHom.comp θ with hθ'
  set ι' : PU K p f →* X := ι.comp σ.toMonoidHom with hι'def
  have hθ'inj : Function.Injective θ' := (MulAut.conj σ⁻¹).injective.comp hθ
  have hθ'ι' : ∀ x, θ' (ι' x) = MulAut.conj x := by
    intro x
    have h1 : θ' (ι' x) = σ⁻¹ * θ (ι (σ x)) * σ⁻¹⁻¹ := rfl
    rw [h1, hι, mulAut_conj_conj]
    congr 1
    show σ⁻¹ (σ x) = x
    simp
  have hy' : ActsAsD K p f (θ' y) 3 := by
    show ActsAsD K p f (σ⁻¹ * θ y * σ⁻¹⁻¹) 3
    rw [inv_inv]
    exact hy
  have key := alphaOf_klein_diagU hK hp hq hθ'inj hθ'ι' hy'
  have hz' : ι' (QuotientGroup.mk (zA K p f)) = z := by rw [hz]; rfl
  rw [hz'] at key
  exact key

end CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4

namespace CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Asc77.FrameVertex

variable {p : ℕ} [Fact p.Prime] {e : ℕ}


theorem twinSqAlpha_psu4 (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSU 4 p e) : TwinSqAlpha p e .PSU 4 := by
  have hf : 1 ≤ e := hadm.2.1
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.card_galoisField_two_mul_eq hq5
  obtain ⟨φK, hφK⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have : Group.IsPerfect (modelUniv .PSU 4 p e Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSU 4 p e Fact.out trivial hadm).1.1
  set π : (modelUniv .PSU 4 p e Fact.out).K →*
      ModelFacts.Orth15.SqU4.PU (GaloisField p (2 * e)) p e :=
    (QuotientGroup.mk' (Subgroup.center (Su (GaloisField p (2 * e)) p e 4))).comp
      φK.toMonoidHom with hπdef
  have hπk : π.ker = Subgroup.center (modelUniv .PSU 4 p e Fact.out).K := by
    ext x
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φK x) : Su (GaloisField p (2 * e)) p e 4 ⧸ _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact CFSG.ClassicalInvolution.ModelFacts.Orth15.mulEquiv_mem_center_iff φK x
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp φK.surjective
  intro H _ _ ψ R R' x x' hpair k hkR hkk v hvR hvR' hvv
  have hc : x' * x⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K := by
    apply hpair.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpair.same, mul_inv_cancel]
  set θ := outerAction ψ hpair.ker π hπ hπk with hθdef
  have hθinj : Function.Injective θ :=
    (injective_iff_map_eq_one θ).mpr fun w hw =>
      eq_one_of_outerAction_eq_one ψ hpair.ker π hπ hπk hw
  set ι : ModelFacts.Orth15.SqU4.PU (GaloisField p (2 * e)) p e →* ↥(inducedAutOn ψ.range) :=
    ((innerHom ψ).range.subtype).comp (outerEquiv ψ hpair.ker π hπ hπk).toMonoidHom with hιdef
  have hιπ : ∀ s : (modelUniv .PSU 4 p e Fact.out).K, ι (π s) = innerHom ψ s := fun s =>
    outerEquiv_apply ψ hpair.ker π hπ hπk s
  have hθι : ∀ q, θ (ι q) = MulAut.conj q := by
    intro q
    obtain ⟨s, rfl⟩ := hπ q
    rw [hιπ, hθdef, outerAction_innerHom]
  have hfix : ∀ r : (modelUniv .PSU 4 p e Fact.out).K,
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
  have hne' : R.map φK.toMonoidHom ≠ R'.map φK.toMonoidHom := fun h =>
    hpair.ne (Subgroup.map_injective φK.injective h)
  have hc' : φK x' * (φK x)⁻¹ ∈ Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
    have := (CFSG.ClassicalInvolution.ModelFacts.Orth15.mulEquiv_mem_center_iff φK
      (x' * x⁻¹)).mpr hc
    rwa [map_mul, map_inv] at this
  obtain ⟨Γ, hΓ1, hΓ2⟩ := ModelFacts.Orth15.SqU4.exists_Gamma_U hK hp2 hq5
    ((hφK R).mp hpair.mem) ((hφK R').mp hpair.mem') hne' (x := φK x) (x' := φK x')
    ⟨x, hpair.hx, rfl⟩ (by rw [← map_mul, hpair.hx2, map_one])
    (fun h => hpair.hx1 (φK.injective (h.trans (map_one φK).symm)))
    ⟨x', hpair.hx', rfl⟩ (by rw [← map_mul, hpair.hx'2, map_one])
    (fun h => hpair.hx'1 (φK.injective (h.trans (map_one φK).symm))) hc' (k := φK k)
    ⟨k, hkR, rfl⟩ hkk' (φ := θ v)
    (by
      rintro _ ⟨r, hr, rfl⟩
      exact hfix r (hvR r hr))
    (by
      rintro _ ⟨r, hr, rfl⟩
      exact hfix r (hvR' r hr))
    hφ2
  have hy : θ (innerHom ψ k * v) = MulAut.conj (QuotientGroup.mk (φK k) :
      ModelFacts.Orth15.SqU4.PU (GaloisField p (2 * e)) p e) * θ v := by
    rw [map_mul, hθdef, outerAction_innerHom]
    rfl
  have hz : innerHom ψ x = ι (MulAut.conj (QuotientGroup.mk Γ :
      ModelFacts.Orth15.SqU4.PU (GaloisField p (2 * e)) p e)
        (QuotientGroup.mk (ModelFacts.Orth15.SqU4.zA (GaloisField p (2 * e)) p e))) := by
    rw [← hΓ2]
    exact (hιπ x).symm
  have key := ModelFacts.Orth15.SqU4.alphaOf_klein_frameU hK hp2 hq5 hθinj hθι Γ
    (by rw [hy]; exact hΓ1) hz
  rw [Set.pair_comm]
  exact key

end CFSG.ClassicalInvolution.Asc77
