module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSpFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSLFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverBasic

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.OddStandard.SmallF3.HypA2 (TypU)
open scoped MatrixGroups

section Levi


theorem a2l_subsystemGroup_mono {τ : Tag} {K : Type} [Field K] {A B : Set (Fin τ.rank)}
    (h : A ⊆ B) : subsystemGroup τ K A ≤ subsystemGroup τ K B :=
  Subgroup.closure_mono fun _ ⟨i, hi, c, hg⟩ => ⟨i, h hi, c, hg⟩

theorem a2l_levi_component_toral {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1)
    {H Q : Subgroup (ModGL τ K)} (hS : rootSpan τ K (rootCharKernel a) = H ⊔ Q)
    (hcomm : ∀ x ∈ H, ∀ y ∈ Q, x * y = y * x) (hqH : CFSG.IsQuasisimple ↥H) :
    CFSG.Assembly.IsComponentOf H
      (adjointGroup τ K ⊓ centralizer ({rootDiagUnit τ a} : Set (ModGL τ K))) := by
  haveI : Finite (ModGL τ K) := finite_modGL
  obtain ⟨hSX, hSn, -⟩ := odd_toral_involution_centralizer_p_component_root_reduction τ K hK2 a ha
  have hSX' : H ⊔ Q ≤ toralCentralizer τ K a := hS ▸ hSX
  have hSn' : ((H ⊔ Q).subgroupOf (toralCentralizer τ K a)).Normal := hS ▸ hSn
  have hHX : H ≤ toralCentralizer τ K a := le_sup_left.trans hSX'
  have hHn : (H.subgroupOf (H ⊔ Q)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx y hy)
  exact ⟨hHX, .step le_sup_left hHn (.step hSX' hSn' (.refl _)),
    (AssemblyBPredicates.isQuasisimple_iff_native _).2 hqH⟩

end Levi

section SL27

theorem a2l_exists_sl2_27_of_sl6 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {G : Type} [Group G] (Ψ : SL(6, K) →* G) (hker : Ψ.ker ≤ center SL(6, K)) {z : G}
    (hz1 : z ≠ 1) (hzr : z ∈ Ψ.range) (hzc : ∀ x ∈ Ψ.range, z * x = x * z) :
    ∃ N : Subgroup G, N ≤ Ψ.range ∧ z ∈ N ∧ HarrisLit.IsSLTwoOver 27 ↥N := by
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK]; norm_num
  haveI : CharP K 3 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three le_rfl
      hK'
  have hP : Group.IsPerfect SL(6, K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  obtain ⟨F, _, _, ι, hFcard, hιinj, hιneg⟩ := a2l_exists_sl2_27_sl6 (K := K) hK
  have hg₀ : ((ι (a2lNegOne F) : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = -1 := hιneg _ rfl
  have hcen : ∀ s ∈ center SL(6, K), s = 1 ∨ s = ι (a2lNegOne F) := fun s hs => by
    rcases a2l_center_sl_cases hK (by norm_num) hs with h | h
    · exact Or.inl (Subtype.ext (by rw [h]; rfl))
    · exact Or.inr (Subtype.ext (h.trans hg₀.symm))
  have hzc' : (⟨z, hzr⟩ : Ψ.range) ∈ center Ψ.range := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2).symm
  have hker₂ : Ψ.rangeRestrict.ker ≤ center SL(6, K) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hΨneg : Ψ.rangeRestrict (ι (a2lNegOne F)) = ⟨z, hzr⟩ :=
    a2l_map_eq_of_center_pair hP Ψ.rangeRestrict Ψ.rangeRestrict_surjective hker₂ hcen hzc'
      (fun h => hz1 (congrArg Subtype.val h))
  have hΨneg' : Ψ (ι (a2lNegOne F)) = z := congrArg Subtype.val hΨneg
  have hΨinj : Function.Injective Ψ :=
    a2l_injective_of_center_pair Ψ hker hcen (by rw [hΨneg']; exact hz1)
  refine ⟨(Ψ.comp ι).range, ?_, ⟨a2lNegOne F, hΨneg'⟩, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨ι g, rfl⟩
  · have hinj : Function.Injective (Ψ.comp ι) := hΨinj.comp hιinj
    haveI := Fintype.ofFinite F
    exact ⟨F, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card, hFcard],
      ⟨(MonoidHom.ofInjective hinj).symm⟩⟩

end SL27

section Datum

theorem a2l_datum_of_levi_a5 {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) {z : ModGL τ K} {T : Subgroup (ModGL τ K)}
    (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hTc : CFSG.Assembly.IsComponentOf T
      (adjointGroup τ K ⊓ centralizer ({z} : Set (ModGL τ K)))) (hTU : TypU ↥T)
    (Ψ : SL(6, K) →* ModGL τ K) (hker : Ψ.ker ≤ center SL(6, K)) (hΨT : Ψ.range ≤ T)
    (hzr : z ∈ Ψ.range) : a2lDatum ↥(adjointGroup τ K) := by
  haveI : Finite (ModGL τ K) := finite_modGL
  have hzc : ∀ x ∈ Ψ.range, z * x = x * z := fun x hx =>
    mem_centralizer_singleton_iff.1 (hTc.1 (hΨT hx)).2 |>.symm
  obtain ⟨N, hNΨ, hzN, hN⟩ := a2l_exists_sl2_27_of_sl6 hK Ψ hker hz1 hzr hzc
  exact a2lDatum_of_subgroup_component_of_le (adjointGroup τ K) (hTc.1 (hΨT hzr)).1 hz2 hz1
    ⟨13, by norm_num⟩ (by norm_num) hTc (hNΨ.trans hΨT) hzN hN hTU

end Datum

end CFSG.OddStandard.SmallF3.HypA2Leaves
