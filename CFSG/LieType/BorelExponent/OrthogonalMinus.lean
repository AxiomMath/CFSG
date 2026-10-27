module

public import CFSG.LieType.BorelExponent.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusBorel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelTransport
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.RankThree.PartOne.KF.ClsOmega
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthMinusPlane
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailLeviPPrime
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LieType.BorelExponent

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

section TailTorus

open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem pow_card_sq_sub_one_eq_one_of_isOmegaTwisted_zero
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)} (hg : IsOmegaTwisted b c g 0) :
    g ^ (Nat.card K ^ 2 - 1) = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Irreducible (omegaPoly b c)) := ⟨omegaPoly_irreducible hirr⟩
  have : Finite ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) := finite_orthLinearEquiv
  let ω : AdjoinRoot (omegaPoly b c) := AdjoinRoot.root (omegaPoly b c)
  have h0 : ω ^ 2 + algebraMap K (AdjoinRoot (omegaPoly b c)) b * ω +
      algebraMap K (AdjoinRoot (omegaPoly b c)) c = 0 := by
    have h : AdjoinRoot.mk (omegaPoly b c) (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
        Polynomial.C c) = 0 := AdjoinRoot.mk_self
    simpa only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
      AdjoinRoot.algebraMap_eq] using h
  have hCharF : CharP (AdjoinRoot (omegaPoly b c)) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (omegaPoly b c))).injective 2
  have h2F : (2 : AdjoinRoot (omegaPoly b c)) = 0 := CharTwo.two_eq_zero
  have hω : ω ^ 2 = algebraMap K (AdjoinRoot (omegaPoly b c)) b * ω +
      algebraMap K (AdjoinRoot (omegaPoly b c)) c := by
    linear_combination h0 - (algebraMap K (AdjoinRoot (omegaPoly b c)) b * ω +
      algebraMap K (AdjoinRoot (omegaPoly b c)) c) * h2F
  have hli : ∀ x y : K, algebraMap K (AdjoinRoot (omegaPoly b c)) x +
      algebraMap K (AdjoinRoot (omegaPoly b c)) y * ω = 0 → x = 0 ∧ y = 0 := by
    intro x y h
    by_cases hy : y = 0
    · subst hy
      simp only [map_zero, zero_mul, add_zero] at h
      exact ⟨(map_eq_zero_iff _ (algebraMap K (AdjoinRoot (omegaPoly b c))).injective).1 h, rfl⟩
    · exfalso
      have hy' : algebraMap K (AdjoinRoot (omegaPoly b c)) y ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap K (AdjoinRoot (omegaPoly b c))).injective).2 hy
      have hωs : ω = algebraMap K (AdjoinRoot (omegaPoly b c)) (-x / y) := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination h
      rw [hωs] at h0
      have : algebraMap K (AdjoinRoot (omegaPoly b c)) ((-x / y) ^ 2 + b * (-x / y) + c) = 0 := by
        simpa using h0
      exact hirr (-x / y)
        ((map_eq_zero_iff _ (algebraMap K (AdjoinRoot (omegaPoly b c))).injective).1 this)
  let φ : ↥(omegaRotations b c) →* AdjoinRoot (omegaPoly b c) :=
    { toFun := fun g => algebraMap K (AdjoinRoot (omegaPoly b c))
          ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 0) +
        algebraMap K (AdjoinRoot (omegaPoly b c))
          ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 1) * ω
      map_one' := by simp
      map_mul' := by
        intro g g'
        have hg : IsOmegaTwisted b c (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) 0 := g.2
        obtain ⟨e0, e1⟩ := omega_apply_coord hg
          ((g' : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1))
        have hmul : ((g * g' : ↥(omegaRotations b c)) : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
            (Pi.single 0 1) = (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
              ((g' : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1)) := rfl
        simp only [hmul, e0, e1, map_add, map_mul]
        linear_combination (-(algebraMap K (AdjoinRoot (omegaPoly b c))
          ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 1) *
          algebraMap K (AdjoinRoot (omegaPoly b c))
          ((g' : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 1))) * hω }
  have hinj : Function.Injective φ := by
    intro g g' h
    have h' : algebraMap K (AdjoinRoot (omegaPoly b c))
        ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 0 -
          (g' : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 0) +
        algebraMap K (AdjoinRoot (omegaPoly b c))
          ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 1 -
            (g' : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 1) * ω = 0 := by
      have : φ g - φ g' = 0 := sub_eq_zero.2 h
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, map_sub] at this ⊢
      linear_combination this
    obtain ⟨h1, h2⟩ := hli _ _ h'
    refine Subtype.ext (LinearEquiv.toLinearMap_injective ?_)
    rw [eq_of_isOmegaTwisted_zero g.2, eq_of_isOmegaTwisted_zero g'.2, sub_eq_zero.1 h1,
      sub_eq_zero.1 h2]
  have : Module.Finite K (AdjoinRoot (omegaPoly b c)) :=
    (AdjoinRoot.powerBasis (omegaPoly_monic (b := b) (c := c)).ne_zero).finite
  have : Finite (AdjoinRoot (omegaPoly b c)) := Module.finite_of_finite K
  have : Fintype (AdjoinRoot (omegaPoly b c)) := Fintype.ofFinite _
  have hdim : Module.finrank K (AdjoinRoot (omegaPoly b c)) = 2 := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis (omegaPoly_monic (b := b) (c := c)).ne_zero),
      AdjoinRoot.powerBasis_dim (omegaPoly_monic (b := b) (c := c)).ne_zero,
      omegaPoly_natDegree]
  have hcardNat : Nat.card (AdjoinRoot (omegaPoly b c)) = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot (omegaPoly b c)), hdim]
  have hcardF : Fintype.card (AdjoinRoot (omegaPoly b c)) = Nat.card K ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardNat
  let G : ↥(omegaRotations b c) := ⟨g, hg⟩
  have hφne : φ G ≠ 0 := by
    intro hzero
    have h1 : φ G * φ G⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    rw [hzero, zero_mul] at h1
    exact zero_ne_one h1
  have hpowF : (φ G) ^ (Nat.card K ^ 2 - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (φ G) hφne
    rwa [hcardF] at this
  have hG : G ^ (Nat.card K ^ 2 - 1) = 1 := by
    apply hinj
    rw [map_pow, hpowF, map_one]
  simpa using congrArg Subtype.val hG

theorem pow_card_sq_sub_one_eq_one_of_mem_tailTorus {r : ℕ}
    (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {z : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))}
    (hz : z ∈ tailTorus r (minusTailForm K b c)) :
    z ^ (Nat.card K ^ 2 - 1) = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hani := anisotropic_minusTailForm hirr
  have hreg := nondegenerate_minusTailForm hirr
  have : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  have hodd : Odd (Nat.card (tailTorus r (minusTailForm K b c))) := by
    have := orthogonal_geometry_tail_small_anisotropic_Levi_p_prime (p := 2) hr hani hreg
      (Or.inr finrank_fin_two_fun)
    exact Nat.odd_iff.2 (by omega)
  obtain ⟨-, t, h, hh, hz'⟩ := mem_tailTorus.1 hz
  let z' : ↥(tailTorus r (minusTailForm K b c)) := ⟨z, hz⟩
  have hzpow : z ^ Nat.card (tailTorus r (minusTailForm K b c)) = 1 := by
    have h : z' ^ Nat.card (tailTorus r (minusTailForm K b c)) = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h
  have hpow : tailDiag r (t ^ Nat.card (tailTorus r (minusTailForm K b c)))
      (h ^ Nat.card (tailTorus r (minusTailForm K b c))) = 1 := by
    rw [← tailDiag_pow, hz']
    exact hzpow
  have hhlin : IsOmegaTwisted b c h 0 := by
    refine plane_isOmegaTwisted_zero hirr hodd h 1 (fun a => by
        have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hh a
        rw [one_mul]
        exact this) (s := 1) (fun a => ?_)
    have h1 := LinearEquiv.congr_fun hpow ((0 : Fin r ⊕ Fin r → K), a)
    rw [tailDiag_apply] at h1
    have h2 := congrArg Prod.snd h1
    rw [one_smul]
    simpa using h2
  have hhpow : h ^ (Nat.card K ^ 2 - 1) = 1 :=
    pow_card_sq_sub_one_eq_one_of_isOmegaTwisted_zero hirr hhlin
  have ht : t ^ (Nat.card K ^ 2 - 1) = 1 := by
    obtain ⟨k, hk⟩ : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2
    rw [hk, pow_mul, units_pi_pow_card_sub_one, one_pow]
  rw [← hz', tailDiag_pow, ht, hhpow, tailDiag_one_one]

end TailTorus

theorem pow_card_sq_sub_one_mem_tailUnipotent {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} {r : ℕ} (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))}
    (hx : x ∈ tailBorel r (minusTailForm K b c)) :
    x ^ (Nat.card K ^ 2 - 1) ∈ tailUnipotent r (minusTailForm K b c) := by
  have hani := anisotropic_minusTailForm hirr
  have := tailUnipotent_normal hani (r := r) (qA := minusTailForm K b c)
  obtain ⟨φ⟩ := nonempty_quotient_mulEquiv_tailTorus hani (r := r) (qA := minusTailForm K b c)
  set y : tailBorel r (minusTailForm K b c) := ⟨x, hx⟩
  have hφ : φ (QuotientGroup.mk (y ^ (Nat.card K ^ 2 - 1))) = 1 := by
    rw [QuotientGroup.mk_pow, map_pow]
    exact Subtype.ext (pow_card_sq_sub_one_eq_one_of_mem_tailTorus hr hirr (φ _).2)
  have h1 : (QuotientGroup.mk (y ^ (Nat.card K ^ 2 - 1)) :
      tailBorel r (minusTailForm K b c) ⧸ (tailUnipotent r (minusTailForm K b c)).subgroupOf
        (tailBorel r (minusTailForm K b c))) = 1 :=
    φ.injective (hφ.trans (map_one φ).symm)
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  simpa [y] using h1

theorem borelExponentAt_POmegaMinus : BorelExponentAt .POmegaMinus := by
  intro X _ _ m f hadm hLie
  have hm4 : 4 ≤ m := by simpa only [StatedLieAdmissible] using hadm.2.2
  obtain ⟨-, K, hK, hfin, hcard, b, c, hirr, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hLie (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hbot : (StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus m K b c)) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (σ := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (K := K)
      (Q := CFSG.LieType.Universal.Spin.quadMinus m K b c) (Q₀ := StatedQuadMinus m K b c)
      (CFSG.LieType.Universal.Spin.coe_quadMinus m K b c)
      ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, by
        rw [CFSG.ClassicalGroups.Orthogonal.quadMinus_single_u]
        exact one_ne_zero⟩
  let eProj : StatedProj (StatedOmega (StatedQuadMinus m K b c)) ≃*
      StatedOmega (StatedQuadMinus m K b c) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  let eTail : StatedOmega (StatedQuadMinus m K b c) ≃*
      orthElementaryGroup (quadTail (m - 1) (minusTailForm K b c)) :=
    tailOmegaEquiv (minusTailIsometry m K b c)
      (CFSG.LieType.Universal.Spin.coe_quadMinus m K b c)
      (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus (n := m) hm4 hirr)
  let eXE : X ≃* orthElementaryGroup (quadTail (m - 1) (minusTailForm K b c)) :=
    e.trans (eProj.trans eTail)
  have : Finite (orthElementaryGroup (quadTail (m - 1) (minusTailForm K b c))) :=
    Finite.of_equiv X eXE.toEquiv
  obtain ⟨⟨S₀, hS₀⟩, hN, -, -⟩ :=
    orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) (K := K) (A := Fin 2 → K)
      (r := m - 1) (qA := minusTailForm K b c) (by omega) (anisotropic_minusTailForm hirr)
      (nondegenerate_minusTailForm hirr) (Or.inr finrank_fin_two_fun)
  refine HasBorelExponent.of_mulEquiv eXE.symm (hasBorelExponent_of_sylow S₀ ?_)
  intro x hx
  rw [hS₀, hN, Subgroup.mem_subgroupOf] at hx
  rw [hS₀, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  have h := pow_card_sq_sub_one_mem_tailUnipotent (r := m - 1) (by omega) hirr hx
  rwa [hcard, ← pow_mul, mul_comm f 2] at h

end CFSG.LieType.BorelExponent

end
