module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmSixMinusChain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmPlus
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply statedOmega_eq_comap
  closure_isometries_eq_comap)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus
  nondegenerate_polarBilin_quadMinus_of_finite)
open scoped commutatorElement

section Transfer

theorem card_centralizer_omEquiv {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) (x : G) :
    Nat.card (centralizer ({ψ x} : Set H)) = Nat.card (centralizer ({x} : Set G)) := by
  have e : (centralizer ({x} : Set G)).map ψ.toMonoidHom = centralizer ({ψ x} : Set H) := by
    ext y
    obtain ⟨y, rfl⟩ := ψ.surjective y
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff, ← map_mul, ← map_mul, ψ.injective.eq_iff]
  rw [← e, Subgroup.card_map_of_injective ψ.injective]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def omCastEquiv (hK : Nat.card K = 2) : ZMod 2 ≃+* K :=
  RingEquiv.ofBijective (omCast K) ⟨omCast_injective, omCast_surjective hK⟩

@[expose] noncomputable def omGLEquiv (hK : Nat.card K = 2) : GL ι (ZMod 2) ≃* GL ι K :=
  Units.mapEquiv (RingEquiv.mapMatrix (omCastEquiv hK)).toMulEquiv

theorem coe_omGLEquiv (hK : Nat.card K = 2) (A : GL ι (ZMod 2)) :
    ((omGLEquiv hK A : GL ι K) : Matrix ι ι K) = omMat K (A : Matrix ι ι (ZMod 2)) :=
  rfl

theorem map_omGLEquiv_omIsoSet (hK : Nat.card K = 2) {Qz : (ι → ZMod 2) → ZMod 2}
    {Qk : (ι → K) → K} (hQ : ∀ v, Qk (omCast K ∘ v) = omCast K (Qz v)) :
    (omGLEquiv hK) '' omIsoSet Qz = omIsoSet Qk := by
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    intro w
    rw [coe_omGLEquiv]
    exact omIsom hK hQ hA w
  · intro hB
    refine ⟨(omGLEquiv hK).symm B, ?_, MulEquiv.apply_symm_apply _ _⟩
    intro v
    apply omCast_injective (K := K)
    have hAB : omMat K (((omGLEquiv hK).symm B : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) =
        (B : Matrix ι ι K) := by
      rw [← coe_omGLEquiv hK, MulEquiv.apply_symm_apply]
    rw [← hQ, ← hQ, ← omMat_mulVec, hAB]
    exact hB _

theorem map_omGLEquiv_statedOmega (hK : Nat.card K = 2) {Qz : (ι → ZMod 2) → ZMod 2}
    {Qk : (ι → K) → K} (hQ : ∀ v, Qk (omCast K ∘ v) = omCast K (Qz v)) :
    (StatedOmega Qz).map (omGLEquiv hK).toMonoidHom = StatedOmega Qk := by
  rw [statedOmega_eq_omIsoSet, statedOmega_eq_omIsoSet, Subgroup.map_commutator,
    MonoidHom.map_closure, MulEquiv.coe_toMonoidHom, map_omGLEquiv_omIsoSet hK hQ]

@[expose] noncomputable def omOmegaEquiv (hK : Nat.card K = 2) {Qz : (ι → ZMod 2) → ZMod 2}
    {Qk : (ι → K) → K} (hQ : ∀ v, Qk (omCast K ∘ v) = omCast K (Qz v)) :
    StatedOmega Qz ≃* StatedOmega Qk :=
  ((omGLEquiv hK).subgroupMap (StatedOmega Qz)).trans
    (MulEquiv.subgroupCongr (map_omGLEquiv_statedOmega hK hQ))

theorem card_centralizer_omTransfer (hK : Nat.card K = 2) {Qz : (ι → ZMod 2) → ZMod 2}
    {Qk : (ι → K) → K} (hQ : ∀ v, Qk (omCast K ∘ v) = omCast K (Qz v))
    {x : StatedOmega Qz} {y : StatedOmega Qk}
    (hxy : ((y : GL ι K) : Matrix ι ι K) = omMat K ((x : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2))) :
    Nat.card (centralizer ({y} : Set (StatedOmega Qk))) =
      Nat.card (centralizer ({x} : Set (StatedOmega Qz))) := by
  have : omOmegaEquiv hK hQ x = y := Subtype.ext (Units.ext hxy.symm)
  rw [← this, card_centralizer_omEquiv]

end Transfer

section Six

theorem omHirrZ : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide

theorem statedOmega_le_omIsoGroup {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : (ι → K) → K) : StatedOmega Q ≤ omIsoGroup Q :=
  (closure_omIsoSet_le Q).trans (closure_omIsoSet Q).le

theorem omIndex_quadMinus_three {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ((StatedOmega (StatedQuadMinus 3 K b c)).subgroupOf
      (omIsoGroup (StatedQuadMinus 3 K b c))).index = 2 := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, -, -, -, hidx, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction (quadMinus 3 K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr)
      (finrank_minusSpace (n := 3) (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero hirr (by norm_num) U hU)
  rw [← hcomm] at hidx
  have h1 := statedOmega_eq_comap (coe_quadMinus 3 K b c)
  have h2 : omIsoGroup (StatedQuadMinus 3 K b c) = (TauCeti.QuadraticMap.orthogonalGroup
      (quadMinus 3 K b c)).comap
        (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).toMonoidHom := by
    rw [← closure_omIsoSet]
    exact closure_isometries_eq_comap (coe_quadMinus 3 K b c)
  change (StatedOmega (StatedQuadMinus 3 K b c)).relIndex (omIsoGroup (StatedQuadMinus 3 K b c)) = 2
  rw [h1, h2, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective
    (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).surjective]
  exact hidx

theorem omNotMem_quadMinus_three {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K)
    (a : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) (ha : StatedQuadMinus 3 K b c a ≠ 0)
    (hg : ∀ v, (g : Matrix _ _ K) *ᵥ v = v - ((StatedQuadMinus 3 K b c a)⁻¹ *
      (StatedQuadMinus 3 K b c (a + v) - StatedQuadMinus 3 K b c a -
        StatedQuadMinus 3 K b c v)) • a) :
    g ∉ StatedOmega (StatedQuadMinus 3 K b c) := by
  intro hr
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr
  rw [statedOmega_eq_comap (coe_quadMinus 3 K b c), Subgroup.mem_comap] at hr
  have hmem := CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ hr
  have : Invertible (quadMinus 3 K b c a) :=
    invertibleOfNonzero (by rw [coe_quadMinus]; exact ha)
  have heq : (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).toMonoidHom g =
      TauCeti.QuadraticMap.reflection (quadMinus 3 K b c) a := by
    apply LinearEquiv.ext
    intro v
    rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, TauCeti.QuadraticMap.reflection_apply,
      invOf_eq_inv, QuadraticMap.polar, coe_quadMinus]
    exact hg v
  rw [heq] at hmem
  have h1 := (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.1 hmem).2
  rw [CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ] at h1
  exact Nat.not_even_one h1

theorem omQ6m_index : ((StatedOmega omQ6m).subgroupOf (omIsoGroup omQ6m)).index = 2 :=
  omIndex_quadMinus_three omHirrZ

@[expose] def omPlRM : Matrix omMI6 omMI6 (ZMod 2) :=
  1 + single (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) 1

theorem omPlRM_sq : omPlRM * omPlRM = 1 := by decide +kernel

@[expose] def omPlRZ : GL omMI6 (ZMod 2) := ⟨omPlRM, omPlRM, omPlRM_sq, omPlRM_sq⟩

theorem omPlRZ_mem_iso : omPlRZ ∈ omIsoGroup omQ6m := by
  change ∀ v, omQ6m (omPlRM *ᵥ v) = omQ6m v
  decide +kernel

theorem omPlRZ_comm_HS : omPlRZ ∈ centralizer ({omPlHSZ} : Set (GL omMI6 (ZMod 2))) :=
  mem_centralizer_singleton_iff.2 (Units.ext (by decide +kernel))

theorem omPlRZ_comm_HL : omPlRZ ∈ centralizer ({omPlHLZ} : Set (GL omMI6 (ZMod 2))) :=
  mem_centralizer_singleton_iff.2 (Units.ext (by decide +kernel))

theorem omPlRZ_not_mem : omPlRZ ∉ StatedOmega omQ6m :=
  omNotMem_quadMinus_three omHirrZ omPlRZ (Pi.single (Sum.inr (Sum.inr 0)) 1) (by decide +kernel)
    (by decide +kernel)

theorem omPl_card_centralizer {h : GL omMI6 (ZMod 2)} (hΩ : h ∈ StatedOmega omQ6m)
    (hr : omPlRZ ∈ centralizer ({h} : Set (GL omMI6 (ZMod 2)))) {n : ℕ}
    (hC : Nat.card (omIsoGroup omQ6m ⊓ centralizer ({h} : Set (GL omMI6 (ZMod 2))) :
      Subgroup (GL omMI6 (ZMod 2))) = 2 * n) :
    Nat.card (centralizer ({(⟨h, hΩ⟩ : StatedOmega omQ6m)} : Set (StatedOmega omQ6m))) = n := by
  have e1 := card_centralizer_singleton_inf_range (StatedOmega omQ6m).subtype_injective
    (⟨h, hΩ⟩ : StatedOmega omQ6m)
  rw [Subgroup.range_subtype] at e1
  rw [← e1]
  have h2 := card_inf_mul_two (G₀ := omIsoGroup omQ6m) (N := StatedOmega omQ6m)
    (H := omIsoGroup omQ6m ⊓ centralizer ({h} : Set (GL omMI6 (ZMod 2)))) inf_le_left
    omQ6m_index ⟨omPlRZ_mem_iso, hr⟩ omPlRZ_not_mem
  have e2 : omIsoGroup omQ6m ⊓ centralizer ({h} : Set (GL omMI6 (ZMod 2))) ⊓
      StatedOmega omQ6m = centralizer ({h} : Set (GL omMI6 (ZMod 2))) ⊓ StatedOmega omQ6m := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨-, hx⟩, hx'⟩
      exact ⟨hx, hx'⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨⟨statedOmega_le_omIsoGroup _ hx', hx⟩, hx'⟩
  rw [e2, hC] at h2
  change Nat.card (centralizer ({h} : Set (GL omMI6 (ZMod 2))) ⊓ StatedOmega omQ6m :
    Subgroup (GL omMI6 (ZMod 2))) = n
  omega

theorem omPlHSZ_mem : omPlHSZ ∈ StatedOmega omQ6m := by
  have e : omPlHSZ = ⁅(⟨omPE1, omPE1, omPE1_sq, omPE1_sq⟩ : GL omMI6 (ZMod 2)),
      ⟨omPE2, omPE2, omPE2_sq, omPE2_sq⟩⁆ := Units.ext omPHS_eq.symm
  rw [e]
  exact commutator_mem_statedOmega omPE1_isom omPE2_isom

theorem omPlHLZ_mem : omPlHLZ ∈ StatedOmega omQ6m := by
  have e : omPlHLZ = ⁅(⟨omPE3, omPE3, omPE3_sq, omPE3_sq⟩ : GL omMI6 (ZMod 2)),
      ⟨omPE4, omPE4, omPE4_sq, omPE4_sq⟩⁆ := Units.ext omPHL_eq.symm
  rw [e]
  exact commutator_mem_statedOmega omPE3_isom omPE4_isom

end Six

theorem omSixMinusCentValues_holds : OmSixMinusCentValues := by
  intro K _ _ _ hK
  refine ⟨?_, ?_⟩
  · rw [card_centralizer_omTransfer hK (statedQuadMinus_omCast 3)
      (x := ⟨omPlHLZ, omPlHLZ_mem⟩) rfl]
    exact omPl_card_centralizer omPlHLZ_mem omPlRZ_comm_HL (by rw [omPl_card_CL])
  · rw [card_centralizer_omTransfer hK (statedQuadMinus_omCast 3)
      (x := ⟨omPlHSZ, omPlHSZ_mem⟩) rfl]
    exact omPl_card_centralizer omPlHSZ_mem omPlRZ_comm_HS (by rw [omPl_card_CS])

theorem twoOmegaPlusModelValues_holds : TwoOmegaPlusModelValues :=
  twoOmegaPlusModelValues_of_six omSixMinusCentValues_holds

end CFSG.SeitzReduction.F4Pilot
