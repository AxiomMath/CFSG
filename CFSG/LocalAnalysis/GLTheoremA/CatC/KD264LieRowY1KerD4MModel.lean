module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerD4MGeom
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerD4MQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3D4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open TauCeti.QuadraticMap QuadraticMap Module
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.RankTwoClassical

noncomputable section

namespace KD4

section Model

variable {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def projEquiv (Q : QuadraticForm K (ι → K)) {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀) :
    StatedProj (StatedOmega Q₀) ≃*
      (↥⁅orthogonalGroup Q, orthogonalGroup Q⁆ ⧸
        (scalars K (ι → K)).subgroupOf ⁅orthogonalGroup Q, orthogonalGroup Q⁆) :=
  QuotientGroup.congr _ _ (statedOmegaEquivCommutator Q hQ₀) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff] at hy
      rw [Subgroup.mem_subgroupOf]
      exact hy
    · intro hx
      refine ⟨(statedOmegaEquivCommutator Q hQ₀).symm x, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
      rw [Subgroup.mem_subgroupOf] at hx
      have h1 : ((statedOmegaEquivCommutator Q hQ₀ ((statedOmegaEquivCommutator Q hQ₀).symm x) :
          ↥⁅orthogonalGroup Q, orthogonalGroup Q⁆) : (ι → K) ≃ₗ[K] (ι → K)) = x := by
        rw [MulEquiv.apply_symm_apply]
      have h2 : ((statedOmegaEquivCommutator Q hQ₀ ((statedOmegaEquivCommutator Q hQ₀).symm x) :
          ↥⁅orthogonalGroup Q, orthogonalGroup Q⁆) : (ι → K) ≃ₗ[K] (ι → K)) =
          toLinEquiv ι K ((statedOmegaEquivCommutator Q hQ₀).symm x : GL ι K) := rfl
      rw [← h2, h1]
      exact hx)

local notation "Ω[" Q "]" => ⁅orthogonalGroup Q, orthogonalGroup Q⁆

theorem geom_hyp (h3 : (3 : K) ≠ 0) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hdim : finrank K V = 8) (hnd : (polarBilin Q).Nondegenerate)
    (hnp : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (P : Subgroup ↥Ω[Q]) (hP : Nat.card P = 27)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    ∃ F : Subgroup ↥Ω[Q], F ≤ P ∧ Nat.card F = 9 ∧
      ∃ H : Subgroup ↥Ω[Q],
        (∀ h ∈ H, ∀ f ∈ F, h * f = f * h) ∧
        (∀ g : ↥Ω[Q], (∀ f ∈ F, g * f = f * g) → ∀ h ∈ H, g * h * g⁻¹ ∈ H) ∧
        CFSG.Open.IsQuasisimple H ∧ 3 ∣ Nat.card (H ⧸ Subgroup.center H) ∧
        (∀ h ∈ H, h ∈ (scalars K V).subgroupOf Ω[Q] → h = 1) := by
  have hG₀O : Ω[Q] ≤ orthogonalGroup Q := commutator_le_self _
  have hP'G : P.map Ω[Q].subtype ≤ Ω[Q] := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hP'card : Nat.card (P.map Ω[Q].subtype) = 27 := by
    rw [Subgroup.card_map_of_injective (Ω[Q]).subtype_injective, hP]
  have hexp' : ∀ x ∈ P.map Ω[Q].subtype, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have := congrArg Subtype.val (hexp x hx)
    simpa using this
  have hcomm' : ∀ x ∈ P.map Ω[Q].subtype, ∀ y ∈ P.map Ω[Q].subtype, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hcomm x hx y hy)
  obtain ⟨F, hFP, hF9, Hv, hHvle, hHvcomm, hHvnorm, hHvq, hHv3, w, hw0, hwfix⟩ :=
    geometry h3 hdim hnd hnp (P.map Ω[Q].subtype) (hP'G.trans hG₀O) hP'card hexp' hcomm'
  have hFG : F ≤ Ω[Q] := hFP.trans hP'G
  refine ⟨F.subgroupOf Ω[Q], ?_, ?_, Hv.subgroupOf Ω[Q], ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := hFP hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFG).toEquiv, hF9]
  · intro h hh f hf
    rw [Subgroup.mem_subgroupOf] at hh hf
    exact Subtype.ext (hHvcomm h.1 hh f.1 hf)
  · intro g hg h hh
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    have hgF : ∀ f ∈ F, g.1 * f = f * g.1 := by
      intro f hf
      have := hg ⟨f, hFG hf⟩ (by rw [Subgroup.mem_subgroupOf]; exact hf)
      exact congrArg Subtype.val this
    have := hHvnorm g.1 (hG₀O g.2) hgF h.1 hh
    simpa using this
  · exact CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.isQuasisimple_equiv
      (Subgroup.subgroupOfEquivOfLe hHvle).symm hHvq
  · rw [← CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.card_quotient_center_equiv
      (Subgroup.subgroupOfEquivOfLe hHvle).symm]
    exact hHv3
  · intro h hh hZ
    rw [Subgroup.mem_subgroupOf] at hh hZ
    obtain ⟨c, hc⟩ := mem_scalars.1 hZ
    have hcw : c • w = w := by rw [← hc w]; exact hwfix h.1 hh
    have hc1 : c = 1 := by
      have : (c - 1) • w = 0 := by rw [sub_smul, hcw, one_smul, sub_self]
      rcases smul_eq_zero.1 this with h' | h'
      · exact sub_eq_zero.1 h'
      · exact absurd h' hw0
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [hc v, hc1, one_smul]
    rfl

theorem scalar_sq_one {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {v₀ : V}
    (hv₀ : Q v₀ = 1) {z : V ≃ₗ[K] V} (hz : z ∈ orthogonalGroup Q) (hs : z ∈ scalars K V) :
    z ^ 2 = 1 := by
  obtain ⟨c, hc⟩ := mem_scalars.1 hs
  have h1 : Q (z v₀) = Q v₀ := map_app_of_mem_orthogonalGroup hz v₀
  rw [hc v₀, QuadraticMap.map_smul, hv₀, smul_eq_mul, mul_one] at h1
  apply LinearEquiv.ext
  intro v
  rw [pow_two, LinearEquiv.mul_apply, hc v, map_smul, hc v, smul_smul, h1, one_smul]
  rfl

end Model

theorem kerConcl_model {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))))
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.KerConcl E := by
  have hQ₀ : ⇑(quadMinus 4 K b c) = StatedQuadMinus 4 K b c := coe_quadMinus 4 K b c
  have hdim : finrank K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) = 8 := by
    have := CFSG.GroupTheory.WeirSylow.finrank_quadMinus_space (K := K) (m := 4) (by norm_num)
    simpa using this
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite 4 K hirr
  have hnp := CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := 4) (by norm_num) hirr
  haveI : Finite (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) := inferInstance
  haveI : Finite ((Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K)) :=
    Finite.of_injective (fun f => (f : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) →
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K))) DFunLike.coe_injective
  have hv₀ : (quadMinus 4 K b c) (minusVec 4) = 1 :=
    (congrFun hQ₀ _).trans (statedQuadMinus_minusVec 4 b c)
  refine CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.kerConcl_of_equiv
    (projEquiv (quadMinus 4 K b c) hQ₀) E ?_
  refine kerConcl_of_central_quotient
    ((scalars K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K)).subgroupOf
      ⁅orthogonalGroup (quadMinus 4 K b c), orthogonalGroup (quadMinus 4 K b c)⁆)
    (fun z hz g => Subtype.ext (commute_of_mem_scalars (Subgroup.mem_subgroupOf.1 hz) g.1))
    (fun z hz => Subtype.ext (scalar_sq_one hv₀ (commutator_le_self _ z.2)
      (Subgroup.mem_subgroupOf.1 hz)))
    (fun P hP hexp hcomm => geom_hyp h3 hdim hnd hnp P hP hexp hcomm) _
    (CFSG.Open.IsElemAbelian.map hE _) ?_
  have hinj : Function.Injective (projEquiv (quadMinus 4 K b c) hQ₀).toMonoidHom :=
    (projEquiv (quadMinus 4 K b c) hQ₀).injective
  rw [Subgroup.card_map_of_injective hinj, hc]

end KD4

end

theorem KD264Y1KerD4Model_holds : KD264Y1KerD4Model := by
  intro G _ _ p f h hp3 E hE hc
  obtain ⟨hadm, K, hKf, hKfin, hKcard, b, c, hirr, ⟨φ⟩⟩ := h
  have hring : ringChar K = p := ringChar_eq_of_card_eq hadm.1 hadm.2.1 hKcard
  have h3 : (3 : K) ≠ 0 := by
    intro h0
    have h0' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h0
    have hdvd : ringChar K ∣ 3 := (CharP.cast_eq_zero_iff K (ringChar K) 3).1 h0'
    have hp3' : ringChar K = 3 :=
      ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left CharP.ringChar_ne_one
    exact hp3 (hring.symm.trans hp3')
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  have hk := KD4.kerConcl_model h3 hirr (E.map φ.toMonoidHom) (CFSG.Open.IsElemAbelian.map hE _)
    (by rw [Subgroup.card_map_of_injective hinj, hc])
  exact CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.kerConcl_of_equiv φ E hk

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
