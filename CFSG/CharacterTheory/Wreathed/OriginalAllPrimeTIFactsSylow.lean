module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeNFactsBasic
public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalQuotient
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Data

public section

namespace CFSG.Wreathed.OriginalAllPrime.TIFacts

open CFSG.ABGTheoremB CFSG.QuasiDihedralFusion
open CFSG.Wreathed.BaseFourCentralizerStructure

variable {G : Type} [Group G]

theorem wreathedSetting_T_eq_modelOmega (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    (wreathedSetting n S e p f).T = BrauerWong.modelOmega S e := by
  rw [BrauerWong.modelOmega, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem wreathedSetting_F₀_eq [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) : (wreathedSetting n S e p f).F₀ = modelBase S e := by
  have hn1 : 1 ≤ n := by omega
  change (wreathedSetting n S e p f).D ⊓
    Subgroup.centralizer ((wreathedSetting n S e p f).T : Set G) = _
  rw [wreathedSetting_D_eq n hn1 S e p f, wreathedSetting_T_eq n hn1 S e p f]
  have hBC := modelBase_le_modelTCentralizer n hn1 S e
  apply le_antisymm
  · have hQp : IsPGroup 2 (((S : Subgroup G) ⊓
        Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
          (Subgroup.centralizer (modelT n S e : Set G))) :=
      (S.isPGroup'.to_le inf_le_left).comap_subtype
    have hle : (modelBaseFourCentralizerSylow n hn S e :
        Subgroup (Subgroup.centralizer (modelT n S e : Set G))) ≤
        ((S : Subgroup G) ⊓ Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
          (Subgroup.centralizer (modelT n S e : Set G)) := by
      rw [modelBaseFourCentralizerSylow_coe]
      exact Subgroup.comap_mono (le_inf (modelBase_le_sylow S e) hBC)
    have heq := (modelBaseFourCentralizerSylow n hn S e).is_maximal' hQp hle
    intro g hg
    have hgC : g ∈ Subgroup.centralizer (modelT n S e : Set G) := (Subgroup.mem_inf.mp hg).2
    have hmem : (⟨g, hgC⟩ : Subgroup.centralizer (modelT n S e : Set G)) ∈
        ((S : Subgroup G) ⊓ Subgroup.centralizer (modelT n S e : Set G)).subgroupOf
          (Subgroup.centralizer (modelT n S e : Set G)) := Subgroup.mem_subgroupOf.mpr hg
    rw [heq, modelBaseFourCentralizerSylow_coe] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  · exact le_inf (modelBase_le_sylow S e) hBC

theorem wreathedSetting_F₀_abelian [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    ∀ g ∈ (wreathedSetting n S e p f).F₀, ∀ h ∈ (wreathedSetting n S e p f).F₀,
      g * h = h * g := by
  rw [wreathedSetting_F₀_eq n hn S e p f]
  exact fun g hg h hh => BrauerWong.modelBase_commute S e g h hg hh

theorem wreathedSetting_F₀_omega [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    ∀ g ∈ (wreathedSetting n S e p f).F₀, g ^ 2 = 1 → g ∈ (wreathedSetting n S e p f).T := by
  rw [wreathedSetting_F₀_eq n hn S e p f, wreathedSetting_T_eq_modelOmega n S e p f]
  exact fun g hg hsq => (BrauerWong.mem_modelOmega_iff S e (by omega) g).mpr ⟨hg, hsq⟩

theorem wreathedSetting_C_eq [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    oddCoreIn (wreathedSetting n S e p f).C ⊔ (wreathedSetting n S e p f).F₀ =
      (wreathedSetting n S e p f).C := by
  have hsplit := modelBaseFourCentralizer_split_and_unique n hn S e
  dsimp only at hsplit
  rw [wreathedSetting_F₀_eq n hn S e p f]
  change oddCoreIn (Subgroup.centralizer ((wreathedSetting n S e p f).T : Set G)) ⊔ _ =
    Subgroup.centralizer ((wreathedSetting n S e p f).T : Set G)
  rw [wreathedSetting_T_eq n (by omega) S e p f]
  exact hsplit.1.symm

theorem wreathedSetting_commutator_le
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ⁅(wreathedSetting n S e p f).N, (wreathedSetting n S e p f).N⁆ ≤
      (wreathedSetting n S e p f).L₀ := by
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  have hderived := ComponentCoveringLocal.original_derived_eq_layer hnonab n hn S e hfour p f hp
    hp2 hf hlocal
  have h1 : ⁅(⊤ : Subgroup (involutionCentralizer n S e)), ⊤⁆ ≤
      (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e) := by
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (centralizerOddCoreMap_surjective n S e), ← hderived,
      _root_.commutator_def]
  have h2 := Subgroup.map_mono (f := (involutionCentralizer n S e).subtype) h1
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact h2

end CFSG.Wreathed.OriginalAllPrime.TIFacts
