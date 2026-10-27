module

public import CFSG.CharacterTheory.Wreathed.FullCentralizerFromProjectiveModel
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldLayer

public noncomputable section

namespace CFSG.Wreathed.ComponentCoveringLocal

open FullSylowCoveringObstruction SmallerRecognitionOriginalField
open FullCentralizerFromProjectiveModel

universe u v

theorem commutator_eq_of_quasisimple_cyclic_quotient
    {H : Type u} [Group H] (M : Subgroup H) [M.Normal]
    (hM : CFSG.IsQuasisimple M) [IsCyclic (H ⧸ M)] : commutator H = M := by
  let : Group.IsPerfect M := hM.1
  apply le_antisymm
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  · rw [← Subgroup.commutator_eq_self (H := M)]
    exact Subgroup.commutator_mono le_top le_top

theorem normal_subgroup_odd_core_eq_bot
    {H : Type u} [Group H] [Finite H] (D : Subgroup H) [D.Normal]
    (hcore : CFSG.oddCore H = ⊥) : CFSG.oddCore D = ⊥ := by
  have h := CFSG.ComponentClassification.OddCore.normal_intersection H D
  change (CFSG.oddCore D).map D.subtype = D ⊓ CFSG.oddCore H at h
  apply Subgroup.map_injective D.subtype_injective
  rw [h, hcore, inf_bot_eq, Subgroup.map_bot]

theorem odd_kernel_eq_odd_core_of_corefree_target
    {B : Type u} {D : Type v} [Group B] [Group D] [Finite B]
    (f : B →* D) (hf : Function.Surjective f)
    (hker : Odd (Nat.card f.ker)) (hcore : CFSG.oddCore D = ⊥) :
    CFSG.oddCore B = f.ker := by
  have hnormal : ((CFSG.oddCore B).map f).Normal :=
    Subgroup.Normal.map inferInstance f hf
  have hodd : Odd (Nat.card ((CFSG.oddCore B).map f)) :=
    (CFSG.ComponentClassification.OddCore.odd_card B).of_dvd_nat
      (Subgroup.card_map_dvd (CFSG.oddCore B) f)
  have hle : (CFSG.oddCore B).map f ≤ CFSG.oddCore D := le_sSup ⟨hnormal, hodd⟩
  apply le_antisymm
  · exact (Subgroup.map_eq_bot_iff (CFSG.oddCore B)).mp
      (le_antisymm (hle.trans_eq hcore) bot_le)
  · exact le_sSup ⟨inferInstance, hker⟩

variable {G : Type} [Group G] [Finite G]

abbrev originalCentralizerSubgroup (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :=
  K.subgroupOf (involutionCentralizer n S e)

abbrev originalImage (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :=
  (originalCentralizerSubgroup n S e K).map (centralizerOddCoreMap n S e)

@[expose] def originalImageMap (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :
    originalCentralizerSubgroup n S e K →* originalImage n S e K :=
  ((centralizerOddCoreMap n S e).comp
    (originalCentralizerSubgroup n S e K).subtype).codRestrict
      (originalImage n S e K)
      (fun b => Subgroup.mem_map_of_mem (centralizerOddCoreMap n S e) b.property)

omit [Finite G] in
theorem originalImageMap_coe (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (b : originalCentralizerSubgroup n S e K) :
    (originalImageMap n S e K b : centralizerOddCoreQuotient n S e) =
      centralizerOddCoreMap n S e (b : involutionCentralizer n S e) := rfl

omit [Finite G] in
theorem originalImageMap_surjective (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :
    Function.Surjective (originalImageMap n S e K) := by
  rintro ⟨h, hh⟩
  obtain ⟨b, hb, hbh⟩ := Subgroup.mem_map.mp hh
  exact ⟨⟨b, hb⟩, Subtype.ext hbh⟩

omit [Finite G] in
theorem originalImageMap_ker (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :
    (originalImageMap n S e K).ker =
      (centralizerOddCore n S e).subgroupOf (originalCentralizerSubgroup n S e K) := by
  ext b
  change originalImageMap n S e K b = 1 ↔ _
  rw [← Subtype.coe_inj, originalImageMap_coe]
  exact QuotientGroup.eq_one_iff (b : involutionCentralizer n S e)

theorem original_quotient_sylow_le_image (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (hSK : (S : Subgroup G) ≤ K) :
    (centralizerOddCoreSylow n hn S e : Subgroup (centralizerOddCoreQuotient n S e)) ≤
      originalImage n S e K := by
  rw [centralizerOddCoreSylow, Sylow.coe_mapSurjective]
  apply Subgroup.map_mono
  rw [centralizerSylow_coe]
  exact Subgroup.comap_mono hSK

theorem original_image_odd_index (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (hSK : (S : Subgroup G) ≤ K) : Odd (originalImage n S e K).index := by
  have hodd : Odd (centralizerOddCoreSylow n hn S e :
      Subgroup (centralizerOddCoreQuotient n S e)).index :=
    Nat.not_even_iff_odd.mp
      (fun he => (centralizerOddCoreSylow n hn S e).not_dvd_index (even_iff_two_dvd.mp he))
  exact hodd.of_dvd_nat
    (Subgroup.index_dvd_of_le (original_quotient_sylow_le_image n hn S e K hSK))

variable [IsSimpleGroup G]

theorem original_derived_eq_layer
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    commutator (centralizerOddCoreQuotient n S e) =
      CFSG.layer (centralizerOddCoreQuotient n S e) := by
  obtain ⟨F, hfield, hfinite, _, _, _, theta, rho, eta, hin, hrho, _, hdata⟩ :=
    actual_projective_layer_model_determines_full_centralizer
      hnonab n hn S e hfour p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  let : (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := hin.layer_normal
  let : IsCyclic (centralizerOddCoreQuotient n S e ⧸
      CFSG.layer (centralizerOddCoreQuotient n S e)) := hdata.quotient_cyclic
  exact commutator_eq_of_quasisimple_cyclic_quotient _ hdata.structural.component.1

theorem component_cover_image_normal_odd_index
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    (originalImage n S e K).Normal ∧ Odd (originalImage n S e K).index := by
  have hderived := original_derived_eq_layer hnonab n hn S e hfour p f hp hpodd hf hmodel
  exact ⟨Subgroup.Normal.of_commutator_le _ (hderived.le.trans hcover),
    original_image_odd_index n hn S e K hSK⟩

omit [IsSimpleGroup G] in
theorem original_centralizer_odd_core_eq_kernel
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (hnormal : (originalImage n S e K).Normal) :
    CFSG.oddCore (originalCentralizerSubgroup n S e K) =
      (centralizerOddCore n S e).subgroupOf (originalCentralizerSubgroup n S e K) := by
  let : (originalImage n S e K).Normal := hnormal
  have hcore := normal_subgroup_odd_core_eq_bot (originalImage n S e K)
    (centralizerOddCoreQuotient_oddCore_eq_bot n S e)
  have hodd : Odd (Nat.card (originalImageMap n S e K).ker) := by
    rw [originalImageMap_ker]
    exact (CFSG.ComponentClassification.OddCore.odd_card
      (involutionCentralizer n S e)).of_dvd_nat
        (Subgroup.card_comap_dvd_of_injective (centralizerOddCore n S e)
          (originalCentralizerSubgroup n S e K).subtype
          (originalCentralizerSubgroup n S e K).subtype_injective)
  exact (odd_kernel_eq_odd_core_of_corefree_target (originalImageMap n S e K)
    (originalImageMap_surjective n S e K) hodd hcore).trans (originalImageMap_ker n S e K)

omit [IsSimpleGroup G] in
theorem original_centralizer_odd_core_quotient_equiv
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (hnormal : (originalImage n S e K).Normal) :
    ∃ E : originalCentralizerSubgroup n S e K ⧸
        CFSG.oddCore (originalCentralizerSubgroup n S e K) ≃* originalImage n S e K,
      (∀ b : originalCentralizerSubgroup n S e K,
        E (QuotientGroup.mk' (CFSG.oddCore (originalCentralizerSubgroup n S e K)) b) =
          originalImageMap n S e K b) ∧
      (∀ b : originalCentralizerSubgroup n S e K,
        E.symm (originalImageMap n S e K b) =
          QuotientGroup.mk' (CFSG.oddCore (originalCentralizerSubgroup n S e K)) b) := by
  have hker : CFSG.oddCore (originalCentralizerSubgroup n S e K) =
      (originalImageMap n S e K).ker :=
    (original_centralizer_odd_core_eq_kernel n S e K hnormal).trans
      (originalImageMap_ker n S e K).symm
  let E := (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective (originalImageMap n S e K)
      (originalImageMap_surjective n S e K))
  refine ⟨E, fun _ => rfl, ?_⟩
  intro b
  exact E.symm_apply_apply
    (QuotientGroup.mk' (CFSG.oddCore (originalCentralizerSubgroup n S e K)) b)

end CFSG.Wreathed.ComponentCoveringLocal
