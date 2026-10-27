module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6RootSL2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatLeafProof
open CFSG.Timmesfeld.LevisExtras (tv01_eq_sl2Upper tv10_eq_sl2Lower)
open CFSG.ClassicalInvolution.WeakCT (spBlock hom_ext_sl2 blk blk_zero_tv01 blk_zero_tv10
  blk_one_tv01 blk_one_tv10 tv_zero_one_one_ne_one)
open scoped MatrixGroups Matrix


@[expose] def a5Node : Fin 5 → Fin TwistTag.E6.tag.rank :=
  ![⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩]

theorem a5Node_adj : ∀ i j : Fin 5, j.val = i.val + 1 → a5Node i ≠ a5Node j ∧
    Tag.cartan .E6 (a5Node i) (a5Node j) = -1 ∧ Tag.cartan .E6 (a5Node j) (a5Node i) = -1 ∧
    ∃ l : Fin 6,
      ¬ (3 : ℤ) ∣ Tag.cartan .E6 (a5Node i) l + 2 * Tag.cartan .E6 (a5Node j) l := by
  decide

@[expose] def a5Gens (K : Type) [Field K] : Set (ModGL TwistTag.E6.tag K) :=
  ⋃ k : Fin 5, Set.range (xUnit TwistTag.E6.tag K (a5Node k)) ∪
    Set.range (yUnit TwistTag.E6.tag K (a5Node k))

variable {K : Type} [Field K] [Finite K]

theorem exists_e6_sl6 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) :
    ∃ Ψ : SL(5 + 1, K) →* ModGL TwistTag.E6.tag K, Ψ.ker ≤ Subgroup.center SL(5 + 1, K) ∧
      Ψ.range ≤ Subgroup.closure (a5Gens K) ∧
      ∀ (k : Fin 5) (c : K),
        Ψ (tv k.castSucc k.succ c) = xUnit TwistTag.E6.tag K (a5Node k) c ∧
          Ψ (tv k.succ k.castSucc c) = yUnit TwistTag.E6.tag K (a5Node k) c := by
  classical
  have hadm : StatedLieAdmissible .PSL (5 + 1) p f :=
    ⟨hp, hf, by norm_num, fun h => by simp at h, fun h => by simp at h⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hinj : Function.Injective (simpleRootSL2 TwistTag.E6.tag K (a5Node 0)) := by
    by_cases h2 : ringChar K = 2
    · haveI : CharP K 2 := ringChar.of_eq h2
      exact CFSG.RankThree.Chevalley.simpleRootSL2_injective_of_charTwo _
    · exact simpleRootSL2_injective h2 _
  set H : Subgroup (ModGL TwistTag.E6.tag K) := Subgroup.closure (a5Gens K) with hHdef
  have hxH : ∀ k c, xUnit TwistTag.E6.tag K (a5Node k) c ∈ H := fun k c =>
    Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inl ⟨c, rfl⟩⟩)
  have hyH : ∀ k c, yUnit TwistTag.E6.tag K (a5Node k) c ∈ H := fun k c =>
    Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inr ⟨c, rfl⟩⟩)
  have hρH : ∀ k, (simpleRootSL2 TwistTag.E6.tag K (a5Node k)).range ≤ H := fun k => by
    rw [range_simpleRootSL2, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hxH k c
    · exact hyH k c
  let u : Fin 5 → K → H := fun k c => ⟨_, hxH k c⟩
  let v : Fin 5 → K → H := fun k c => ⟨_, hyH k c⟩
  have hfr : SimplyLacedFrame (SpecialLinear.rootDatum 5 K) K (fun i j => j.val = i.val + 1)
      u v := by
    refine ⟨fun i j h => ?_, fun k => ?_, fun i j hne h1 h2 c d => ?_⟩
    · obtain ⟨hne, hc1, hc2, hl⟩ := a5Node_adj i j h
      obtain ⟨ψ, hψ0, hψ1⟩ := exists_e6_sl3 K hne hc1 hc2 hl
      have hle : ψ.range ≤ H :=
        range_le_of_blk ψ (by rw [hψ0]; exact hρH i) (by rw [hψ1]; exact hρH j)
      refine ⟨ψ.codRestrict H fun A => hle ⟨A, rfl⟩, fun c => ⟨?_, ?_, ?_, ?_⟩⟩ <;>
        apply Subtype.ext <;> simp only [MonoidHom.codRestrict_apply]
      · rw [← blk_zero_tv01, ← MonoidHom.comp_apply, hψ0, simpleRootSL2_tv01]
      · rw [← blk_zero_tv10, ← MonoidHom.comp_apply, hψ0, simpleRootSL2_tv10]
      · rw [← blk_one_tv01, ← MonoidHom.comp_apply, hψ1, simpleRootSL2_tv01]
      · rw [← blk_one_tv10, ← MonoidHom.comp_apply, hψ1, simpleRootSL2_tv10]
    · refine ⟨(simpleRootSL2 TwistTag.E6.tag K (a5Node k)).codRestrict H
        fun A => hρH k ⟨A, rfl⟩, fun c => ⟨Subtype.ext ?_, Subtype.ext ?_⟩⟩
      · exact simpleRootSL2_tv01 _ c
      · exact simpleRootSL2_tv10 _ c
    · have horth : ∀ i j : Fin 5, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
          a5Node i ≠ a5Node j ∧
          (Pi.single (a5Node i) 1 : Fin TwistTag.E6.tag.rank → ℤ) ⬝ᵥ
            (TwistTag.E6.tag.symmetrizedCartan *ᵥ
              (Pi.single (a5Node j) 1 : Fin TwistTag.E6.tag.rank → ℤ)) = 0 := by
        decide
      obtain ⟨hij, h0⟩ := horth i j hne h1 h2
      have hc := commute_simpleRootSL2_of_orth (K := K) hij h0
      refine ⟨?_, ?_, ?_, ?_⟩ <;> refine Subtype.ext ?_ <;>
        simp only [Subgroup.coe_mul, u, v]
      · rw [← simpleRootSL2_tv01, ← simpleRootSL2_tv01]
        exact (hc _ _).eq
      · rw [← simpleRootSL2_tv01, ← simpleRootSL2_tv10]
        exact (hc _ _).eq
      · rw [← simpleRootSL2_tv10, ← simpleRootSL2_tv01]
        exact (hc _ _).eq
      · rw [← simpleRootSL2_tv10, ← simpleRootSL2_tv10]
        exact (hc _ _).eq
  have hgen : Subgroup.closure (⋃ k, Set.range (u k) ∪ Set.range (v k)) = ⊤ := by
    have hset : (⋃ k, Set.range (u k) ∪ Set.range (v k)) =
        ((↑) : H → ModGL TwistTag.E6.tag K) ⁻¹' a5Gens K := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range, Set.mem_preimage, a5Gens]
      refine exists_congr fun k => or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · rintro ⟨c, rfl⟩
        exact ⟨c, rfl⟩
      · rintro ⟨c, hc⟩
        exact ⟨c, Subtype.ext hc⟩
      · rintro ⟨c, rfl⟩
        exact ⟨c, rfl⟩
      · rintro ⟨c, hc⟩
        exact ⟨c, Subtype.ext hc⟩
    rw [hset]
    exact Subgroup.closure_closure_coe_preimage
  have hnt : ∃ k c, u k c ≠ 1 := by
    refine ⟨0, 1, fun h => ?_⟩
    have h1 : simpleRootSL2 TwistTag.E6.tag K (a5Node 0) (tv 0 1 1) =
        simpleRootSL2 TwistTag.E6.tag K (a5Node 0) 1 := by
      rw [simpleRootSL2_tv01, map_one]
      exact congrArg Subtype.val h
    exact tv_zero_one_one_ne_one (hinj h1)
  obtain ⟨Ψ, hΨu, hΨv, -, hker, -⟩ := exists_surjective_of_simplyLacedFrame
    (CurtisTits.curtisTitsConclusion_specialLinear hadm hK (by norm_num))
    (leviConePresented_specialLinear 5 K) (ARS.simplyLacedLevis_specialLinear 5 K) hfr hgen hnt
  refine ⟨H.subtype.comp Ψ, fun B hB => hker ?_, ?_, fun k c => ⟨?_, ?_⟩⟩
  · exact Subtype.ext (MonoidHom.mem_ker.1 hB)
  · rintro _ ⟨B, rfl⟩
    exact (Ψ B).2
  · rw [MonoidHom.comp_apply, ← ARS.Linear.x_sroot]
    exact congrArg Subtype.val (hΨu k c)
  · rw [MonoidHom.comp_apply, ← ARS.Linear.x_neg_sroot]
    exact congrArg Subtype.val (hΨv k c)

end CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6
