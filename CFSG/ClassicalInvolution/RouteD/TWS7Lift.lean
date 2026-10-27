module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RFixLift
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Lift
public import CFSG.ClassicalInvolution.RouteD.TWS6D4MF
public import CFSG.ClassicalInvolution.RouteD.TWT4Hol
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4Model
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS7

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.TwinY
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

set_option linter.unusedSectionVars false

section Lift

variable {p f : ℕ} [Fact p.Prime]

local notation "Q₄" => quadPlus 4 (GaloisField p f)
local notation "θ₄" => spinAction (quadPlus 4 (GaloisField p f))

theorem map_center_aut {H : Type*} [Group H] (σ : H ≃* H) {c : H}
    (hc : c ∈ Subgroup.center H) : σ c ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  obtain ⟨y', rfl⟩ := σ.surjective y
  rw [← map_mul, ← map_mul, hc y']


theorem exists_lift_isometry (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X]
    (ψ : spinGroup (quadPlus 4 (GaloisField p f)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))))
    (τ : X ≃* X) (hτ2 : ∀ y, τ (τ y) = y) (hτr : ∀ k, τ (ψ k) ∈ ψ.range)
    (fr : OFrame (quadPlus 4 (GaloisField p f)))
    (A B : Subgroup (spinGroup (quadPlus 4 (GaloisField p f))))
    (hA : A.map (spinAction (quadPlus 4 (GaloisField p f))) = fr.La.range)
    (hB : B.map (spinAction (quadPlus 4 (GaloisField p f))) = fr.swap.La.range)
    (hfixA : ∀ r ∈ A, τ (ψ r) = ψ r) (hfixB : ∀ r ∈ B, τ (ψ r) = ψ r) :
    ∃ (α : spinGroup (quadPlus 4 (GaloisField p f)) ≃* spinGroup (quadPlus 4 (GaloisField p f)))
      (w : (Fin 4 ⊕ Fin 4 → GaloisField p f) ≃ₗ[GaloisField p f] (Fin 4 ⊕ Fin 4 → GaloisField p f)),
      (∀ y, ψ (α y) = τ (ψ y)) ∧ w ∈ TauCeti.QuadraticMap.orthogonalGroup
        (quadPlus 4 (GaloisField p f)) ∧ (∀ x ∈ fr.span, w x = x) ∧
      (∀ y, spinAction (quadPlus 4 (GaloisField p f)) (α y) =
        w * spinAction (quadPlus 4 (GaloisField p f)) y * w⁻¹) ∧ w * w = 1 ∧
      (∀ y, α (α y) = y) := by
  classical
  have hf1 : 1 ≤ f := one_le_of_five_le_pow hq
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨Fact.out, hf1, le_refl 4⟩
  have c8 := TWS6.spinCtx8_plus hp2 hq hadm
  have hfin : Finite (spinGroup Q₄) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hFfin : Finite (GaloisField p f) := Nat.finite_of_card_ne_zero (by
    have := c8.h5
    omega)
  have : Group.IsPerfect (spinGroup Q₄) := c8.perfect
  have hτL : ∀ l ∈ ψ.range, τ l ∈ ψ.range := by
    rintro _ ⟨k, rfl⟩
    exact hτr k
  have : Finite ↥ψ.range := Finite.of_surjective _ ψ.rangeRestrict_surjective
  let σ : ↥ψ.range ≃* ↥ψ.range := TWT4.restrictAut ψ.range τ hτL
  have hσc : ∀ l : ↥ψ.range, ((σ l : ↥ψ.range) : X) = τ l := fun l => rfl
  let Fix : Subgroup (spinGroup Q₄) := MonoidHom.eqLocus (τ.toMonoidHom.comp ψ) ψ
  have hFixmem : ∀ g, g ∈ Fix ↔ τ (ψ g) = ψ g := fun g => Iff.rfl
  have hABFix : A ⊔ B ≤ Fix := sup_le (fun r hr => hfixA r hr) (fun r hr => hfixB r hr)
  have hσ : ∀ s : spinGroup Q₄, θ₄ s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, σ (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σ ℓ * (ψ.rangeRestrict s)⁻¹ := by
    intro s hs ℓ
    rw [← hA, ← hB, ← Subgroup.map_sup] at hs
    obtain ⟨s', hs', hθs⟩ := hs
    have hk : s'⁻¹ * s ∈ MonoidHom.ker θ₄ := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθs, inv_mul_cancel]
    have hkc : s'⁻¹ * s ∈ Subgroup.center (spinGroup Q₄) := ker_spinAction_le_center Q₄ hk
    have hs'F : τ (ψ s') = ψ s' := hABFix hs'
    set g := ψ.rangeRestrict s with hg
    set g' := ψ.rangeRestrict s' with hg'
    set gk := ψ.rangeRestrict (s'⁻¹ * s) with hgk
    have hgdec : g = g' * gk := by
      apply Subtype.ext
      simp [hg, hg', hgk, map_mul]
    have hgkc : gk ∈ Subgroup.center ↥ψ.range := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨m, rfl⟩ := ψ.rangeRestrict_surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_center_iff.mp hkc m
    have hσg' : σ g' = g' := Subtype.ext (by rw [hσc]; exact hs'F)
    have hσgkc := map_center_aut σ hgkc
    have hcen : g⁻¹ * σ g ∈ Subgroup.center ↥ψ.range := by
      rw [hgdec, map_mul, hσg']
      have : (g' * gk)⁻¹ * (g' * σ gk) = gk⁻¹ * σ gk := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hgkc) hσgkc
    have hσgeq : σ g = g * (g⁻¹ * σ g) := by group
    rw [map_mul, map_mul, map_inv]
    set c := g⁻¹ * σ g with hc
    have hcc := Subgroup.mem_center_iff.mp hcen
    rw [hσgeq]
    calc g * c * σ ℓ * (g * c)⁻¹ = g * c * σ ℓ * (c⁻¹ * g⁻¹) := by rw [mul_inv_rev]
      _ = g * (c * σ ℓ * c⁻¹) * g⁻¹ := by group
      _ = g * σ ℓ * g⁻¹ := by
        rw [show c * σ ℓ * c⁻¹ = σ ℓ from by rw [← hcc (σ ℓ)]; group]
  have hlift := liftSimFr_of_d4FixLift d4FixLift_proved hp2 hq ψ hψ
  obtain ⟨α, w, hαψ, hwO, hwspan, hθw⟩ := exists_isometry_of_centralizing_at c8.hodd c8.h5
    c8.hrange fr hψ σ (hlift fr σ hσ) hσ
  have hαψ' : ∀ y, ψ (α y) = τ (ψ y) := fun y => congrArg Subtype.val (hαψ y)
  have hα2 : ∀ y, α (α y) = y := by
    have key := CFSG.ClassicalInvolution.ModelFacts.OrthAut.eq_of_inv_mul_mem_center
      ((α : spinGroup Q₄ →* spinGroup Q₄).comp (α : spinGroup Q₄ →* spinGroup Q₄))
      (MonoidHom.id (spinGroup Q₄)) (fun x => by
        apply hψ
        rw [MonoidHom.mem_ker]
        change ψ (x⁻¹ * α (α x)) = 1
        rw [map_mul, map_inv, hαψ', hαψ', hτ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  have hy_mem : w * w ∈ elementaryGroup Q₄ :=
    sq_mem_of_frame c8.hodd c8.hQ fr (by rw [c8.hV]; omega) hwO
  obtain ⟨ŷ, hŷ, hαα⟩ := exists_sq_lift c8.hrange α hy_mem hθw
  have hŷc : ŷ ∈ Subgroup.center (spinGroup Q₄) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := hαα x
    rw [hα2 x] at this
    exact (mul_inv_eq_iff_eq_mul.mp this.symm).symm
  obtain ⟨μ, hμ⟩ := exists_smul_of_central c8.hrange c8.hZ hŷc
  have hww : ∀ v, (w * w) v = μ • v := fun v => by
    rw [← hŷ]
    exact hμ v
  have he₁ : fr.e₁ ∈ fr.span := fr.e₁_mem_span
  have he₁0 : fr.e₁ ≠ 0 := by
    intro h0
    have := fr.polar_e₁_f₁
    rw [h0] at this
    simp at this
  have hμ1 : μ = 1 := by
    have h1 : (w * w) fr.e₁ = fr.e₁ := by
      rw [LinearEquiv.mul_apply, hwspan _ he₁, hwspan _ he₁]
    rw [hww] at h1
    have h2' : (μ - 1) • fr.e₁ = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2').resolve_right he₁0)
  refine ⟨α, w, hαψ', hwO, hwspan, hθw, ?_, hα2⟩
  refine LinearEquiv.ext fun v => ?_
  rw [hww, hμ1, one_smul]
  rfl

end Lift

end CFSG.ClassicalInvolution.RouteD.TWS7
