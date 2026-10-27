module

public import CFSG.LargeExtraspecial.AS35ZMPG
import all CFSG.Fischer.F4
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Fischer.NoF25.Local
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import CFSG.LargeExtraspecial.AS35Fis
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S10Five
public import CFSG.LargeExtraspecial.S10FourA
public import CFSG.LargeExtraspecial.S10SixA
public import CFSG.LargeExtraspecial.S10Three
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S5One
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S5Two
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.Open.QuasithinDefs
public import CFSG.RankThree.Literature.FSmithTheorem2
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZM

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary AS35L
open CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

macro "zm_f4_decide" : tactic =>
  `(tactic| (simp only [ne_eq, omega_eq, ← map_one eF4, ← map_zero eF4, ← map_add, ← map_mul,
    frob_eF4, eF4_inj]; decide))

section Vec

variable {k : ℕ} (hk : 2 ≤ k)

@[expose] noncomputable def eZero : Fin (k + 2) → K := ι k (Pi.single ⟨0, by omega⟩ 1)

@[expose] noncomputable def eOne : Fin (k + 2) → K := ι k (Pi.single ⟨1, by omega⟩ 1)

@[expose] noncomputable def vec4 (a b c d : K) : Fin (k + 2) → K :=
  a • v₀ k + b • u₀ k + c • eZero hk + d • eOne hk

theorem herm_single_self (m : ℕ) (i : Fin m) :
    herm frob (Pi.single i (1 : K)) (Pi.single i 1) = 1 := by
  rw [herm_single_left, map_one, one_mul, Pi.single_eq_same]

theorem herm_single_ne (m : ℕ) {i j : Fin m} (h : i ≠ j) :
    herm frob (Pi.single i (1 : K)) (Pi.single j 1) = 0 := by
  rw [herm_single_left, map_one, one_mul, Pi.single_eq_of_ne h]

theorem herm_vec4 (a b c d a' b' c' d' : K) :
    herm frob (vec4 hk a b c d) (vec4 hk a' b' c' d') =
      frob a * b' + frob b * a' + frob c * c' + frob d * d' := by
  have h00 : herm frob (eZero hk) (eZero hk) = 1 := by
    rw [eZero, herm_ι_ι, herm_single_self]
  have h11 : herm frob (eOne hk) (eOne hk) = 1 := by
    rw [eOne, herm_ι_ι, herm_single_self]
  have h01 : herm frob (eZero hk) (eOne hk) = 0 := by
    rw [eZero, eOne, herm_ι_ι, herm_single_ne _ (by simp [Fin.ext_iff])]
  have h10 : herm frob (eOne hk) (eZero hk) = 0 := by
    rw [eZero, eOne, herm_ι_ι, herm_single_ne _ (by simp [Fin.ext_iff])]
  simp only [vec4, eZero, eOne, herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
    herm_v₀_v₀, herm_u₀_u₀, herm_v₀_u₀, herm_u₀_v₀, herm_v₀_ι, herm_u₀_ι, herm_ι_v₀,
    herm_ι_u₀] at h00 h11 h01 h10 ⊢
  rw [h00, h11, h01, h10]
  ring

theorem vec4_add (a b c d a' b' c' d' : K) :
    vec4 hk a b c d + vec4 hk a' b' c' d' = vec4 hk (a + a') (b + b') (c + c') (d + d') := by
  simp only [vec4, add_smul]
  abel

theorem smul_vec4 (l a b c d : K) :
    l • vec4 hk a b c d = vec4 hk (l * a) (l * b) (l * c) (l * d) := by
  simp only [vec4, smul_add, smul_smul]

theorem tvU_vec4 {a b c d : K} (h : herm frob (vec4 hk a b c d) (vec4 hk a b c d) = 0)
    (a' b' c' d' : K) :
    tvU (vec4 hk a b c d) • vec4 hk a' b' c' d' =
      vec4 hk (a' + herm frob (vec4 hk a b c d) (vec4 hk a' b' c' d') * a)
        (b' + herm frob (vec4 hk a b c d) (vec4 hk a' b' c' d') * b)
        (c' + herm frob (vec4 hk a b c d) (vec4 hk a' b' c' d') * c)
        (d' + herm frob (vec4 hk a b c d) (vec4 hk a' b' c' d') * d) := by
  rw [tvU_smul h, smul_vec4, vec4_add]

theorem vec4_v₀ : vec4 hk 1 0 0 0 = v₀ k := by simp [vec4]

theorem vec4_u₀ : vec4 hk 0 1 0 0 = u₀ k := by simp [vec4]

theorem vec4_congr {k : ℕ} (hk : 2 ≤ k) {a b c d a' b' c' d' : K} (ha : a = a') (hb : b = b')
    (hc : c = c') (hd : d = d') : vec4 hk a b c d = vec4 hk a' b' c' d' := by
  rw [ha, hb, hc, hd]

theorem x_vec4 {k : ℕ} (hk : 2 ≤ k) (a b c d : K) :
    (tvU (v₀ k) * tvU (u₀ k)) • vec4 hk a b c d = vec4 hk b (a + b) c d := by
  have h1 : herm frob (vec4 hk 1 0 0 0) (vec4 hk 1 0 0 0) = 0 := by
    rw [herm_vec4]; zm_f4_decide
  have h2 : herm frob (vec4 hk 0 1 0 0) (vec4 hk 0 1 0 0) = 0 := by
    rw [herm_vec4]; zm_f4_decide
  rw [mul_smul, ← vec4_v₀ hk, ← vec4_u₀ hk, tvU_vec4 hk h2, tvU_vec4 hk h1, herm_vec4,
    herm_vec4]
  refine vec4_congr hk ?_ ?_ ?_ ?_
  · simp only [map_zero, map_one, zero_mul, one_mul, mul_one, mul_zero, zero_add, add_zero]
    rw [← add_assoc, add_comm a b, add_assoc, add_self_K, add_zero]
  · simp only [map_zero, map_one, zero_mul, one_mul, mul_one, mul_zero, zero_add, add_zero]
    rw [add_comm]
  · simp only [map_zero, map_one, zero_mul, one_mul, mul_one, mul_zero, zero_add, add_zero]
  · simp only [map_zero, map_one, zero_mul, one_mul, mul_one, mul_zero, zero_add, add_zero]

end Vec

macro "zm_vec4" hk:term:max hp:term:max : tactic =>
  `(tactic| (rw [tvU_vec4 $hk $hp, herm_vec4]
             refine vec4_congr $hk ?_ ?_ ?_ ?_ <;> zm_f4_decide))

section Mix

variable {L : Type} [Group L] {D : Set L} (hD : IsTClass D) {k : ℕ} (hk : 2 ≤ k)
  (ψ : L ⧸ center L ≃* PG (k + 2)) {r t : L} (hr : r ∈ D) (ht : t ∈ D)
  (hψr : ψ (QuotientGroup.mk r) = tq (v₀ k)) (hψt : ψ (QuotientGroup.mk t) = tq (u₀ k))
include hD hk hr ht hψr hψt

theorem exists_mix :
    ∃ e ∈ D, ∃ d ∈ D, d * r = r * d ∧ d * t = t * d ∧
      e * (r * t * e * (r * t)⁻¹) * (r * t) = r * t * (e * (r * t * e * (r * t)⁻¹)) ∧
      e * (r * t * e * (r * t)⁻¹) * r ≠ r * (e * (r * t * e * (r * t)⁻¹)) ∧
      e * (r * t * e * (r * t)⁻¹) * d ≠ d * (e * (r * t * e * (r * t)⁻¹)) := by
  have hm : 3 ≤ k + 2 := by omega
  have hp₁ : herm frob (vec4 hk 1 ω 1 0) (vec4 hk 1 ω 1 0) = 0 := by
    rw [herm_vec4]; zm_f4_decide
  have hp₂ : herm frob (vec4 hk ω (1 + ω) 1 0) (vec4 hk ω (1 + ω) 1 0) = 0 := by
    rw [herm_vec4]; zm_f4_decide
  have hp₃ : herm frob (vec4 hk (1 + ω) 1 1 0) (vec4 hk (1 + ω) 1 1 0) = 0 := by
    rw [herm_vec4]; zm_f4_decide
  have hne : ∀ {a b c d : K}, herm frob (vec4 hk 1 1 0 0) (vec4 hk a b c d) ≠ 0 →
      vec4 hk a b c d ≠ 0 := fun h h0 => h (by rw [h0, herm_zero_right])
  have hp₁0 : vec4 hk 1 ω 1 0 ≠ 0 := hne (by rw [herm_vec4]; zm_f4_decide)
  obtain ⟨e, he, hψe⟩ := hD.exists_eq hk ψ (tq_mem_DG hp₁0 hp₁)
  set X : SUid frob (k + 2) := tvU (v₀ k) * tvU (u₀ k) with hX
  have hψx : ψ (QuotientGroup.mk (r * t)) = QuotientGroup.mk X := by
    rw [QuotientGroup.mk_mul, map_mul, hψr, hψt, hX, QuotientGroup.mk_mul]
  have hconj : ∀ g : L, ∀ {a b c d : K},
      herm frob (vec4 hk a b c d) (vec4 hk a b c d) = 0 →
      ψ (QuotientGroup.mk g) = tq (vec4 hk a b c d) →
      ψ (QuotientGroup.mk (r * t * g * (r * t)⁻¹)) = tq (vec4 hk b (a + b) c d) := by
    intro g a b c d hiso hg
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, hψx, hg, conj_tq X hiso, hX, x_vec4]
  set e₂ := r * t * e * (r * t)⁻¹ with he₂
  have he₂D : e₂ ∈ D := hD.conj _ e he
  have hψe₂ : ψ (QuotientGroup.mk e₂) = tq (vec4 hk ω (1 + ω) 1 0) := by
    rw [he₂, hconj e hp₁ hψe]
  have hψe₃ : ψ (QuotientGroup.mk (r * t * e₂ * (r * t)⁻¹)) = tq (vec4 hk (1 + ω) 1 1 0) := by
    rw [hconj e₂ hp₂ hψe₂, show ω + (1 + ω) = (1 : K) by zm_f4_decide]
  have hinv₂ : e₂⁻¹ = e₂ := inv_eq_of_mul_eq_one_right (hD.inv e₂ he₂D)
  have he₂e : e₂ * e * e₂ ∈ D := by
    have := hD.conj e₂ e he
    rwa [hinv₂] at this
  have hψe₂e : ψ (QuotientGroup.mk (e₂ * e * e₂)) = tq (vec4 hk (1 + ω) 1 1 0) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul, hψe₂, hψe,
      tq_mul_tq_mul_tq hp₂ hp₁]
    have e1 : tvU (vec4 hk ω (1 + ω) 1 0) • vec4 hk 1 ω 1 0 =
        (1 + ω) • vec4 hk (1 + ω) 1 1 0 := by
      rw [smul_vec4]
      zm_vec4 hk hp₂
    rw [e1]
    change (QuotientGroup.mk (tvU ((1 + ω) • vec4 hk (1 + ω) 1 1 0)) : PG (k + 2)) =
      QuotientGroup.mk (tvU (vec4 hk (1 + ω) 1 1 0))
    rw [tvU_smul_vec hp₃ (by zm_f4_decide)]
  have he₃ : r * t * e₂ * (r * t)⁻¹ = e₂ * e * e₂ :=
    hD.mk_injOn hk ψ (hD.conj _ e₂ he₂D) he₂e (ψ.injective (by rw [hψe₃, hψe₂e]))
  clear_value e₂
  have hyx : e * e₂ * (r * t) = r * t * (e * e₂) := by
    have h1 : r * t * (e * e₂) * (r * t)⁻¹ = e * e₂ := by
      calc r * t * (e * e₂) * (r * t)⁻¹
          = (r * t * e * (r * t)⁻¹) * (r * t * e₂ * (r * t)⁻¹) := by group
        _ = e₂ * (e₂ * e * e₂) := by rw [← he₂, he₃]
        _ = e * e₂ := by rw [← mul_assoc, ← mul_assoc, hD.inv e₂ he₂D, one_mul]
    calc e * e₂ * (r * t) = r * t * (e * e₂) * (r * t)⁻¹ * (r * t) := by rw [h1]
      _ = r * t * (e * e₂) := by group
  set z₀ : Fin k → K := Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1 with hz₀def
  have hz₀ : herm frob z₀ z₀ = 0 :=
    isotropic_single_add_single (by simp [Fin.ext_iff]) one_ne_zero
  have hz₀0 : z₀ ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp [hz₀def, Fin.ext_iff] at this
  obtain ⟨d, hd, hψd, hdr, hdt⟩ := exists_mem_of_vec hD hk ψ hr ht hψr hψt hz₀0 hz₀
  have hιz : ι k z₀ = vec4 hk 0 0 1 1 := by
    simp [hz₀def, vec4, eZero, eOne, map_add]
  rw [hιz] at hψd
  set Y : SUid frob (k + 2) := tvU (vec4 hk 1 ω 1 0) * tvU (vec4 hk ω (1 + ω) 1 0) with hY
  have hψy : ψ (QuotientGroup.mk (e * e₂)) = QuotientGroup.mk Y := by
    rw [QuotientGroup.mk_mul, map_mul, hψe, hψe₂, hY, QuotientGroup.mk_mul]
  have hcomm : ∀ g : L, ∀ {v : Fin (k + 2) → K}, herm frob v v = 0 →
      ψ (QuotientGroup.mk g) = tq v → e * e₂ * g = g * (e * e₂) → tq (Y • v) = tq v := by
    intro g v hv hg hc
    have h1 : ψ (QuotientGroup.mk (e * e₂)) * ψ (QuotientGroup.mk g) =
        ψ (QuotientGroup.mk g) * ψ (QuotientGroup.mk (e * e₂)) := by
      rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]
    rw [hψy, hg] at h1
    rw [← conj_tq Y hv, h1, mul_inv_cancel_right]
  have hYv : Y • vec4 hk 1 0 0 0 = vec4 hk 0 ω 0 0 := by
    have e1 : tvU (vec4 hk ω (1 + ω) 1 0) • vec4 hk 1 0 0 0 = vec4 hk ω 1 ω 0 := by
      zm_vec4 hk hp₂
    rw [hY, mul_smul, e1]
    zm_vec4 hk hp₁
  have hYd : Y • vec4 hk 0 0 1 1 = vec4 hk 0 0 ω 1 := by
    have e1 : tvU (vec4 hk ω (1 + ω) 1 0) • vec4 hk 0 0 1 1 = vec4 hk ω (1 + ω) 0 1 := by
      zm_vec4 hk hp₂
    rw [hY, mul_smul, e1]
    zm_vec4 hk hp₁
  refine ⟨e, he, d, hd, hdr, hdt, by rw [← he₂]; exact hyx, fun h => ?_, fun h => ?_⟩
  · rw [← he₂] at h
    have hv₀ : herm frob (vec4 hk 1 0 0 0) (vec4 hk 1 0 0 0) = 0 := by
      rw [herm_vec4]; zm_f4_decide
    have h1 := hcomm r hv₀ (by rw [vec4_v₀]; exact hψr) h
    rw [hYv] at h1
    obtain ⟨c, hc⟩ := (tq_eq_tq_iff hm (hne (by rw [herm_vec4]; zm_f4_decide))
      (by rw [herm_vec4]; zm_f4_decide) (hne (by rw [herm_vec4]; zm_f4_decide)) hv₀).1 h1
    have h2 := congrArg (herm frob (vec4 hk 0 1 0 0)) hc
    rw [smul_vec4, herm_vec4, herm_vec4] at h2
    simp at h2
  · rw [← he₂] at h
    have hd₀ : herm frob (vec4 hk 0 0 1 1) (vec4 hk 0 0 1 1) = 0 := by
      rw [herm_vec4]; zm_f4_decide
    have h1 := hcomm d hd₀ hψd h
    rw [hYd] at h1
    have hne' : ∀ {a b c d : K}, herm frob (vec4 hk 0 0 1 0) (vec4 hk a b c d) ≠ 0 →
        vec4 hk a b c d ≠ 0 := fun h h0 => h (by rw [h0, herm_zero_right])
    obtain ⟨c, hc⟩ := (tq_eq_tq_iff hm (hne' (by rw [herm_vec4]; zm_f4_decide))
      (by rw [herm_vec4]; zm_f4_decide) (hne' (by rw [herm_vec4]; zm_f4_decide)) hd₀).1 h1
    have h2 := congrArg (herm frob (vec4 hk 0 0 0 1)) hc
    have h3 := congrArg (herm frob (vec4 hk 0 0 1 0)) hc
    rw [smul_vec4, herm_vec4, herm_vec4] at h2 h3
    simp only [map_zero, map_one, zero_mul, one_mul, mul_one, mul_zero, zero_add,
      add_zero] at h2 h3
    rw [← h2, one_mul] at h3
    exact omega_ne_one h3.symm

end Mix

end CFSG.LargeExtraspecial.AS35ZM
