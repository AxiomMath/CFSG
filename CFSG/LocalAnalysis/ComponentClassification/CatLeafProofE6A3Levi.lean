module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSp4SL4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6RootSL2

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.LocalAnalysis.ComponentInitial
open CFSG.Timmesfeld.LevisExtras (tv01_eq_sl2Upper tv10_eq_sl2Lower)
open CFSG.ClassicalInvolution.WeakCT (spBlock hom_ext_sl2 blk blk_zero_tv01 blk_zero_tv10
  blk_one_tv01 blk_one_tv10 tv_zero_one_one_ne_one)
open scoped MatrixGroups Matrix

section A3

@[expose] def e6A3Node : Fin 3 → Fin TwistTag.E6.tag.rank :=
  ![⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]

@[expose] def e6A3Gens
    (K : Type) [Field K] : Set (ModGL TwistTag.E6.tag K) :=
  ⋃ k : Fin 3, Set.range (xUnit TwistTag.E6.tag K (e6A3Node k)) ∪
    Set.range (yUnit TwistTag.E6.tag K (e6A3Node k))

variable {K : Type} [Field K] [Finite K]

theorem exists_e6_sl4
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    ∃ Ψ : SL(3 + 1, K) →* ModGL TwistTag.E6.tag K, ∀ (k : Fin 3) (c : K),
      Ψ (tv k.castSucc k.succ c) = xUnit TwistTag.E6.tag K (e6A3Node k) c ∧
        Ψ (tv k.succ k.castSucc c) = yUnit TwistTag.E6.tag K (e6A3Node k) c := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .PSL (3 + 1) p f :=
    ⟨hp, hf, by norm_num, fun h => by simp at h, fun h => by simp at h⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  set H : Subgroup (ModGL TwistTag.E6.tag K) := Subgroup.closure (e6A3Gens K) with hHdef
  have hxH : ∀ k c, xUnit TwistTag.E6.tag K (e6A3Node k) c ∈ H := fun k c =>
    Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inl ⟨c, rfl⟩⟩)
  have hyH : ∀ k c, yUnit TwistTag.E6.tag K (e6A3Node k) c ∈ H := fun k c =>
    Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inr ⟨c, rfl⟩⟩)
  have hρH : ∀ k, (simpleRootSL2 TwistTag.E6.tag K (e6A3Node k)).range ≤ H := fun k => by
    rw [range_simpleRootSL2, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hxH k c
    · exact hyH k c
  let u : Fin 3 → K → H := fun k c => ⟨_, hxH k c⟩
  let v : Fin 3 → K → H := fun k c => ⟨_, hyH k c⟩
  have hfr : SimplyLacedFrame (SpecialLinear.rootDatum 3 K) K (fun i j => j.val = i.val + 1)
      u v := by
    refine ⟨fun i j h => ?_, fun k => ?_, fun i j hne h1 h2 c d => ?_⟩
    · have hedge : ∀ i j : Fin 3, j.val = i.val + 1 → e6A3Node i ≠ e6A3Node j ∧
          Tag.cartan .E6 (e6A3Node i) (e6A3Node j) = -1 ∧
          Tag.cartan .E6 (e6A3Node j) (e6A3Node i) = -1 ∧
          ∃ l : Fin 6, ¬ (3 : ℤ) ∣
            Tag.cartan .E6 (e6A3Node i) l + 2 * Tag.cartan .E6 (e6A3Node j) l := by
        decide
      obtain ⟨hne, hc1, hc2, hl⟩ := hedge i j h
      obtain ⟨ψ, hψ0, hψ1⟩ := exists_e6_sl3 K hne hc1 hc2 hl
      have hle : ψ.range ≤ H :=
        range_le_of_blk ψ (by rw [hψ0]; exact hρH i) (by rw [hψ1]; exact hρH j)
      refine ⟨ψ.codRestrict H fun A => hle ⟨A, rfl⟩, fun c => ⟨?_, ?_, ?_, ?_⟩⟩ <;>
        apply Subtype.ext <;> simp only [MonoidHom.codRestrict_apply]
      · rw [← blk_zero_tv01, ← MonoidHom.comp_apply, hψ0, simpleRootSL2_tv01]
      · rw [← blk_zero_tv10, ← MonoidHom.comp_apply, hψ0, simpleRootSL2_tv10]
      · rw [← blk_one_tv01, ← MonoidHom.comp_apply, hψ1, simpleRootSL2_tv01]
      · rw [← blk_one_tv10, ← MonoidHom.comp_apply, hψ1, simpleRootSL2_tv10]
    · refine ⟨(simpleRootSL2 TwistTag.E6.tag K (e6A3Node k)).codRestrict H
        fun A => hρH k ⟨A, rfl⟩, fun c => ⟨Subtype.ext ?_, Subtype.ext ?_⟩⟩
      · exact simpleRootSL2_tv01 _ c
      · exact simpleRootSL2_tv10 _ c
    · have horth : ∀ i j : Fin 3, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
          e6A3Node i ≠ e6A3Node j ∧
          (Pi.single (e6A3Node i) 1 : Fin TwistTag.E6.tag.rank → ℤ) ⬝ᵥ
            (TwistTag.E6.tag.symmetrizedCartan *ᵥ
              (Pi.single (e6A3Node j) 1 : Fin TwistTag.E6.tag.rank → ℤ)) = 0 := by
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
        ((↑) : H → ModGL TwistTag.E6.tag K) ⁻¹' e6A3Gens K := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range, Set.mem_preimage, e6A3Gens]
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
    have h1 : simpleRootSL2 TwistTag.E6.tag K (e6A3Node 0) (tv 0 1 1) =
        simpleRootSL2 TwistTag.E6.tag K (e6A3Node 0) 1 := by
      rw [simpleRootSL2_tv01, map_one]
      exact congrArg Subtype.val h
    exact tv_zero_one_one_ne_one (simpleRootSL2_injective hK2 _ h1)
  obtain ⟨Ψ, hΨu, hΨv, -⟩ := exists_surjective_of_simplyLacedFrame
    (CurtisTits.curtisTitsConclusion_specialLinear hadm hK le_rfl)
    (leviConePresented_specialLinear 3 K) (ARS.simplyLacedLevis_specialLinear 3 K) hfr hgen hnt
  refine ⟨H.subtype.comp Ψ, fun k c => ⟨?_, ?_⟩⟩
  · rw [MonoidHom.comp_apply, ← ARS.Linear.x_sroot]
    exact congrArg Subtype.val (hΨu k c)
  · rw [MonoidHom.comp_apply, ← ARS.Linear.x_neg_sroot]
    exact congrArg Subtype.val (hΨv k c)

theorem exists_e6_sp4
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (hc : ∀ A B : SL(2, K), Commute (simpleRootSL2 TwistTag.E6.tag K ⟨2, by decide⟩ A)
      (simpleRootSL2 TwistTag.E6.tag K ⟨4, by decide⟩ B)) :
    ∃ ψ : StatedSp 2 K →* ModGL TwistTag.E6.tag K,
      ψ.comp (spBlock K 1) = simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩ ∧
        ψ.comp (spBlock K 0) = pairHom (simpleRootSL2 TwistTag.E6.tag K ⟨2, by decide⟩)
          (simpleRootSL2 TwistTag.E6.tag K ⟨4, by decide⟩) hc := by
  obtain ⟨Ψ, hΨ⟩ := exists_e6_sl4 hp hp2 hK
  refine ⟨Ψ.comp sp4ToSL4, hom_ext_sl2 (fun c => ?_) (fun c => ?_),
    hom_ext_sl2 (fun c => ?_) (fun c => ?_)⟩ <;>
    simp only [MonoidHom.comp_apply]
  · rw [sp4ToSL4_long_tv01, simpleRootSL2_tv01]
    exact (hΨ 1 c).1
  · rw [sp4ToSL4_long_tv10, simpleRootSL2_tv10]
    exact (hΨ 1 c).2
  · rw [sp4ToSL4_short_tv01, map_mul, pairHom_apply, simpleRootSL2_tv01, simpleRootSL2_tv01]
    exact congrArg₂ (· * ·) (hΨ 0 c).1 (hΨ 2 c).1
  · rw [sp4ToSL4_short_tv10, map_mul, pairHom_apply, simpleRootSL2_tv10, simpleRootSL2_tv10]
    exact congrArg₂ (· * ·) (hΨ 0 c).2 (hΨ 2 c).2

end A3

end CFSG.ComponentClassification.CatLeafProof
