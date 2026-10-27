module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSixSiegel
public import CFSG.RankThree.PartTwo.CTU6.WeakCT

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Models.TwistedPairs (minusLongBlock shortBlock finOne spinMinusModel)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.Steinberg (fixedSubfield card_fixedSubfield)
open CFSG.RankThree.PartOne.CTP (lbEmb sbEmb)
open CFSG.RankThree.PartOne.CTP.SU4Even (exists_kleinDataEven map_minusLongBlock_eq_lbEmb
  map_shortBlock_eq_sbEmb)
open CFSG.RankThree.PartTwo.CTU6 (lbSU4 range_lbSU4 su4Model weakCT_unitary_six_even)
open CFSG.SeitzReduction.F4Pilot (statedSpMap)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Model

variable {K' : Type} [Field K'] [Finite K'] [CharP K' 2] {f : ℕ}

theorem range_lbEmb_sup_range_sbEmb_eq_top (hK : Nat.card K' = (2 ^ f) ^ 2) :
    (lbEmb (unitaryInvolution K' 2 f)).range ⊔
        (sbEmb (unitaryInvolution K' 2 f) (unitaryInvolution_involutive hK)).range = ⊤ := by
  have hF : Nat.card (fixedSubfield K' 2 f) = 2 ^ f := card_fixedSubfield hK
  have : CharP (fixedSubfield K' 2 f) 2 :=
    RingHom.charP (fixedSubfield K' 2 f).subtype (fixedSubfield K' 2 f).subtype.injective 2
  obtain ⟨b, c, hirr⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic
    (fixedSubfield K' 2 f)
  have := CFSG.LieType.Universal.Spin.Twisted.fact_shortField hirr
  obtain ⟨inst, ⟨D⟩⟩ := exists_kleinDataEven hF hK hirr
  have htop := CFSG.RankThree.PartOne.CTP.SU4Even.spinMinusModel_blocks_sup_eq_top_even hirr
  change (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range = ⊤ at htop
  rw [← map_minusLongBlock_eq_lbEmb D hF hK hirr, ← map_shortBlock_eq_sbEmb D hF hK hirr,
    ← Subgroup.map_sup, htop, ← MonoidHom.range_eq_map, D.range_PhiSUEven_eq_top hK hirr]

end Model

section WeakCT

variable {G : Type} [Group G]

theorem exists_weakCT_unitary_six_of_subgroups {K' : Type} [Field K'] [Finite K'] [CharP K' 2]
    {f : ℕ} (hK : Nat.card K' = (2 ^ f) ^ 2) (hf : 2 ≤ f) {U : Fin 3 → Subgroup G}
    {G₀ : Subgroup G} (hcomm : ∀ x ∈ U 0, ∀ y ∈ U 2, x * y = y * x)
    (hpair : ∃ W, LinearBlockStandardPair K' W (U 0) (U 1))
    (htw : ∃ W, (su4Model hK).StandardPair W (U 2) (U 1)) (hgen : ⨆ i, U i = G₀) :
    CFSG.IsQuasisimple G₀ ∧ Odd (Nat.card (center G₀)) ∧
      LieModel (G₀ ⧸ center G₀) .PSU 6 2 f := by
  have hle : ∀ i, U i ≤ G₀ := fun i => hgen ▸ le_iSup U i
  have hUmap : ∀ i, ((U i).subgroupOf G₀).map G₀.subtype = U i := fun i => by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr (hle i)]
  have hcomm' : ∀ u ∈ (U 0).subgroupOf G₀, ∀ v ∈ (U 2).subgroupOf G₀, u * v = v * u := by
    intro u hu v hv
    exact Subtype.ext (hcomm _ (mem_subgroupOf.1 hu) _ (mem_subgroupOf.1 hv))
  have hpair' : ∃ W, LinearBlockStandardPair K' W ((U 0).subgroupOf G₀)
      ((U 1).subgroupOf G₀) := by
    obtain ⟨W, θ, c, -, hker, hcase⟩ := hpair
    have htop : (B12 K').map (MulAut.conj c⁻¹).toMonoidHom ⊔
        (B23 K').map (MulAut.conj c⁻¹).toMonoidHom = ⊤ := by
      rw [← Subgroup.map_sup, CFSG.ClassicalInvolution.WeakCT.B12_sup_B23,
        ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.2 (MulAut.conj c⁻¹).surjective
    have hrange : θ.range = U 0 ⊔ U 1 := by
      rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup]
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, sup_comm]
    have hθG₀ : ∀ A, θ A ∈ G₀ := fun A =>
      sup_le (hle 0) (hle 1) (hrange ▸ (⟨A, rfl⟩ : θ A ∈ θ.range))
    set θ' : SL(3, K') →* G₀ := θ.codRestrict G₀ hθG₀ with hθ'def
    have hθ' : ∀ H : Subgroup SL(3, K'), (H.map θ').map G₀.subtype = H.map θ := fun H => by
      rw [Subgroup.map_map]
      rfl
    refine ⟨θ'.range, θ', c, rfl, ?_, ?_⟩
    · rw [MonoidHom.ker_codRestrict]
      exact hker
    · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨?_, ?_⟩
        · apply Subgroup.map_injective G₀.subtype_injective
          rw [hθ', h1, hUmap]
        · apply Subgroup.map_injective G₀.subtype_injective
          rw [hθ', h2, hUmap]
      · refine Or.inr ⟨?_, ?_⟩
        · apply Subgroup.map_injective G₀.subtype_injective
          rw [hθ', h1, hUmap]
        · apply Subgroup.map_injective G₀.subtype_injective
          rw [hθ', h2, hUmap]
  have htw' : ∃ W, (su4Model hK).StandardPair W ((U 2).subgroupOf G₀) ((U 1).subgroupOf G₀) := by
    obtain ⟨W, θ, -, hker, hl, hs, hU2, hU1⟩ := htw
    have hU2' : (lbSU4 K' f).range.map θ = U 2 := hU2
    have hU1' : (sbEmb (unitaryInvolution K' 2 f) (unitaryInvolution_involutive hK)).range.map θ =
        U 1 := hU1
    have hrange : θ.range = U 2 ⊔ U 1 := by
      rw [MonoidHom.range_eq_map, ← range_lbEmb_sup_range_sbEmb_eq_top hK, Subgroup.map_sup,
        ← range_lbSU4, hU2', hU1']
    have hθG₀ : ∀ A, θ A ∈ G₀ := fun A =>
      sup_le (hle 2) (hle 1) (hrange ▸ (⟨A, rfl⟩ : θ A ∈ θ.range))
    set θ' := θ.codRestrict G₀ hθG₀ with hθ'def
    have hθ' : ∀ H : Subgroup (SU (unitaryInvolution K' 2 f) 4),
        (H.map θ').map G₀.subtype = H.map θ := fun H => by
      rw [Subgroup.map_map]
      rfl
    refine ⟨θ'.range, θ', rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [MonoidHom.ker_codRestrict]
      exact hker
    · intro x y hxy
      exact hl (congrArg Subtype.val hxy)
    · intro x y hxy
      exact hs (congrArg Subtype.val hxy)
    · apply Subgroup.map_injective G₀.subtype_injective
      rw [hθ', hU2, hUmap]
    · apply Subgroup.map_injective G₀.subtype_injective
      rw [hθ', hU1, hUmap]
  have hgen' : ⨆ i, (U i).subgroupOf G₀ = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    simp only [hUmap]
    exact hgen
  obtain ⟨Ψ, -, -, hqs, hcenter, hmodel, -⟩ := weakCT_unitary_six_even hK hf
    (fun i => (U i).subgroupOf G₀) hgen' hcomm' hpair' htw'
  refine ⟨hqs, ?_, hmodel⟩
  rw [hcenter]
  exact Odd.of_dvd_nat (odd_card_center_SU hK (by omega) (by norm_num) (by simp))
    (Subgroup.card_map_dvd _ _)

end WeakCT

section Row

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem spGlobalCoverType_unitaryEven_of_std (hcat : LinearPilot.SLmCatalogueClausesAt 3)
    (hdet : LinearPilot.SLmEvenTypeDetAt 3) (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hn : SpThreeUnitaryNormalized e t f 0 false) : SpGlobalCoverType e f .unitaryEven := by
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨K', _, h, _, C₀, hC, hC₀, ι₀, Φ, hrange, hker, hN1, hN3⟩ := hn
  have : Finite K' := h.finite
  have : CharP K' 2 := h.charP
  have hN1' : ∀ x : StatedSp 2 K,
      Φ (uModelSU h hC₀ (statedSpMap (ι₀ : K →+* h.fixedField) 2 x)) =
        ((e.symm ((complSpEquiv 0 x : complSp K 0) : StatedSp 3 K) : L) : G) := fun x => hN1 x
  obtain ⟨S⟩ := nonempty_siegelFieldParam_of_std hcat hdet
    (oddCentralSplit_siegelLevi (by norm_num)) hset hKc hf e htC ht h hC hC₀ ι₀ Φ hrange hker hN1'
    hN3
  have h2 := pieceCore_two_eq_modelToG_of_std hKc hf e h hC₀ ι₀ Φ hrange hker hN1'
  have hcomm := commute_pieceCore_zero_two_of_siegelFieldParam hset hK4 htC ht
    (barRingEquiv_ne_one (h := h)) (UnitaryPilot.barRingEquiv_mul_self h)
    (barRingEquiv_eq_self_iff h ι₀) S h2
  obtain ⟨hqs, hodd, hmodel⟩ := exists_weakCT_unitary_six_of_subgroups h.card_eq_sq hf
    (U := fun j => pieceCore e ({j} : Finset (Fin 3))) hcomm (S.exists_linearPair_three hK4)
    (exists_su4ModelPair_of_std hKc hf e h hC₀ ι₀ Φ hrange hker hN1') (spGlobal_def e).symm
  exact ⟨hqs, hodd, hmodel⟩

theorem spThreeUnitaryEvenStandardInput_of_clauses (hcat : LinearPilot.SLmCatalogueClausesAt 3)
    (hdet : LinearPilot.SLmEvenTypeDetAt 3) : SpThreeUnitaryEvenStandardInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot hstd
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  exact spGlobalCoverType_unitaryEven_of_std hcat hdet hset hKc hf e htC ht
    (spThreeUnitaryNormalized_of_standard hset hKc hf e htC ht 0 (hroot 0) hstd)

theorem spThreeUnitaryEvenRecognitionInput_of_clauses (hcat : LinearPilot.SLmCatalogueClausesAt 3)
    (hdet : LinearPilot.SLmEvenTypeDetAt 3) : SpThreeUnitaryEvenRecognitionInput :=
  spThreeUnitaryEvenRecognitionInput_of_standardInput
    (spThreeUnitaryEvenStandardInput_of_clauses hcat hdet)

end Row

section TypeDet

theorem spThreeUnitaryEvenRecognitionInput_of_catalogue
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) : SpThreeUnitaryEvenRecognitionInput :=
  spThreeUnitaryEvenRecognitionInput_of_clauses hcat (LinearPilot.slmEvenTypeDetAt le_rfl)

end TypeDet

end CFSG.SeitzReduction.SymplecticPilot
