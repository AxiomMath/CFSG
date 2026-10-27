module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PFix
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

structure FrobModel (X : Type) [Group X] (Y : Subgroup X) (t : X) where
  K : Type
  [field : Field K]
  [fin : Finite K]
  [charP : CharP K 2]
  Fr : K ≃+* K
  card : Nat.card K = 4
  hFr : ∀ x, Fr x = x ^ 2
  ψ : StatedSp 2 K ≃* Y
  h : X
  h_mem : h ∈ Y
  act : ∀ a : StatedSp 2 K,
    (h⁻¹ * t * h) * (ψ a : X) * (h⁻¹ * t * h)⁻¹ = (ψ (fieldSp 2 K Fr a) : X)

variable {X : Type} [Group X] {Y : Subgroup X} {t : X}

theorem nonempty_frobModel (hY : CFSG.Blueprint.LieModel ↥Y .PSp 2 2 2) (ht2 : t * t = 1)
    (htn : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y)
    (hout : ¬ ∃ y ∈ Y, ∀ z ∈ Y, t * z * t⁻¹ = y * z * y⁻¹) :
    Nonempty (FrobModel X Y t) := by
  classical
  obtain ⟨⟨-, hf1, -, -⟩, K, _, _, hKcard, ⟨θ⟩⟩ :=
    CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hY
  haveI hch : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf1 hKcard
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf1 hKcard
  have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  obtain ⟨-, hFr1⟩ := frobenius_facts_four hK4 hFr
  have htnorm : t ∈ normalizer (Y : Set X) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨htn h, fun hh => ?_⟩
    have := htn _ hh
    have e : t * (t * h * t⁻¹) * t⁻¹ = h := by
      rw [inv_eq_of_mul_eq_one_right ht2]
      calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
        _ = h := by rw [ht2]; group
    rw [e] at this
    exact this
  set αY : MulAut Y := Y.normalizerMonoidHom ⟨t, htnorm⟩ with hαYdef
  have hαY : ∀ y : Y, (αY y : X) = t * y * t⁻¹ := fun y => rfl
  set αP : MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr θ αY with hαPdef
  have hαP : ∀ y : Y, αP (θ y) = θ (αY y) := fun y => by
    simp [hαPdef, MulAut.congr_apply]
  have hαYsq : αY * αY = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.mul_apply, hαY, hαY, MulAut.one_apply]
    calc t * (t * (y : X) * t⁻¹) * t⁻¹ = (t * t) * (y : X) * (t * t)⁻¹ := by group
      _ = y := by rw [ht2]; group
  have hαPsq : αP * αP = 1 := by
    rw [hαPdef, ← map_mul, hαYsq, map_one]
  have hαP1 : αP ≠ 1 := by
    intro h
    apply hout
    refine ⟨1, Y.one_mem, fun z hz => ?_⟩
    have h1 : αP (θ ⟨z, hz⟩) = θ ⟨z, hz⟩ := by rw [h, MulAut.one_apply]
    rw [hαP] at h1
    have := congrArg Subtype.val (θ.injective h1)
    rw [hαY] at this
    simpa using this
  have hαP2 : orderOf αP = 2 := orderOf_eq_prime (by rw [sq, hαPsq]) hαP1
  obtain ⟨-, -, -, -, -, -, -, -, -, hinv⟩ :=
    exceptionalAut_structure (by norm_num : 1 ≤ 2) hFr hord hzp
  obtain ⟨g, j, hj, hαg⟩ := hinv αP hαP2
  rcases hj with rfl | rfl
  ·
    exfalso
    rw [pow_zero, mul_one, spInner_eq_conj] at hαg
    apply hout
    refine ⟨(θ.symm (proj 2 K g) : X), (θ.symm (proj 2 K g)).2, fun z hz => ?_⟩
    have h1 : αP (θ ⟨z, hz⟩) = proj 2 K g * θ ⟨z, hz⟩ * (proj 2 K g)⁻¹ := by
      rw [hαg, MulAut.conj_apply]
    rw [hαP] at h1
    have h2 : αY ⟨z, hz⟩ = θ.symm (proj 2 K g) * ⟨z, hz⟩ * (θ.symm (proj 2 K g))⁻¹ := by
      apply θ.injective
      rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have := congrArg Subtype.val h2
    rw [hαY] at this
    simpa using this
  ·
    rw [exceptionalAut_sq hFr] at hαg
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h, hh⟩ :=
      even_symplectic_quadratic_involution_descent (r := 2) (f := 2) (by norm_num)
        (by norm_num) hKcard (a := αP) hαPsq g Fr (by rw [hαg, spInner_apply]) hFr1
    rw [← spInner_apply, spInner_eq_conj] at hh
    set hP : StatedProj (StatedSp 2 K) := proj 2 K h with hhP
    have hαPx : ∀ x, αP x = hP * (fieldAut 2 K Fr) (hP⁻¹ * x * hP) * hP⁻¹ := by
      intro x
      rw [hh, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply]
    let ψ : StatedSp 2 K ≃* Y := (projSpEquiv K).trans θ.symm
    have hψ : ∀ b : StatedSp 2 K, θ (ψ b) = proj 2 K b := fun b => by
      show θ (θ.symm (projSpEquiv K b)) = proj 2 K b
      rw [MulEquiv.apply_symm_apply]
      rfl
    set ĥ : Y := θ.symm hP with hĥ
    refine ⟨⟨K, Fr, hK4, hFr, ψ, (ĥ : X), ĥ.2, fun a => ?_⟩⟩
    have hθĥ : θ ĥ = hP := MulEquiv.apply_symm_apply θ hP
    set yb : Y := ĥ * ψ a * ĥ⁻¹ with hyb
    have hθyb : θ yb = hP * proj 2 K a * hP⁻¹ := by
      rw [hyb, map_mul, map_mul, map_inv, hθĥ, hψ]
    have hkey : ĥ⁻¹ * αY yb * ĥ = ψ (fieldSp 2 K Fr a) := by
      apply θ.injective
      rw [map_mul, map_mul, map_inv, hθĥ, ← hαP, hθyb, hαPx, hψ]
      have : hP⁻¹ * (hP * proj 2 K a * hP⁻¹) * hP = proj 2 K a := by group
      rw [this, fieldAut_proj]
      group
    have hX : ((ĥ : X)⁻¹ * t * ĥ) * (ψ a : X) * ((ĥ : X)⁻¹ * t * ĥ)⁻¹ =
        (((ĥ⁻¹ * αY yb * ĥ : Y)) : X) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hαY, hyb, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hX, hkey]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
