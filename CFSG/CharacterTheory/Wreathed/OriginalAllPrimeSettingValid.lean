module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeSetting
public import CFSG.CharacterTheory.Wreathed.FullCentralizerFromProjectiveModel
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockAtoms
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Wreathed.BrauerWong
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearCuspidalCharacters
public import CFSG.CharacterTheory.Wreathed.CharacterDegreeCongruence
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.OneBlock
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThree.InductionGram
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB CFSG.QuasiDihedralFusion
open CFSG.Wreathed.BaseFourCentralizerStructure

variable {G : Type} [Group G] [Finite G]

theorem wreathedSetting_sylow (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) : HasQDOrWreathedSylowOfHeight G (wreathedSetting n S e p f).height := by
  refine Or.inr ⟨hn, fun S' => ?_⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S S'
  exact ⟨(S.equivSMul g).symm.trans e⟩

omit [Finite G] in
theorem wreathedSetting_x_mem_center (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    (wreathedSetting n S e p f).x ∈ centerOf ((wreathedSetting n S e p f).S : Subgroup G) := by
  show wreathModelHom S e (Original.x (2 ^ n)) ∈ centerOf (S : Subgroup G)
  refine Subgroup.mem_inf.mpr ⟨(e.symm (Original.x (2 ^ n))).property, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h := BrauerWong.modelHom_x_central S e hn hg
  calc g * wreathModelHom S e (Original.x (2 ^ n)) =
      g * (g⁻¹ * wreathModelHom S e (Original.x (2 ^ n)) * g) := by rw [h]
    _ = wreathModelHom S e (Original.x (2 ^ n)) * g := by group

omit [Finite G] in
theorem wreathedSetting_center_involution (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    ∀ y ∈ centerOf ((wreathedSetting n S e p f).S : Subgroup G), orderOf y = 2 →
      y = (wreathedSetting n S e p f).x := by
  intro y hy hy2
  have hy' := Subgroup.mem_inf.mp hy
  have hyZ : y ∈ modelCenter S e := by
    rw [← BrauerWong.center_map_eq_modelCenter n hn S e]
    refine Subgroup.mem_map.mpr ⟨⟨y, hy'.1⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hy'.2 g g.2
  rw [BrauerWong.modelCenter_eq_zpowers] at hyZ
  have hA : orderOf (wreathModelHom S e (Original.a (2 ^ n))) = 2 ^ n := by
    rw [orderOf_injective _ (wreathModelHom_injective S e)]
    exact (wreath_center_involution_and_quaternion_coordinates n hn).generator_orders.2.2.1
  rw [AdaptedBaseFusion.eq_pow_half_of_mem_zpowers (by omega) hA hyZ hy2, ← map_pow,
    ← BrauerWong.WreathGenerators.half_eq (by omega)]
  rfl

omit [Finite G] in
theorem wreathedSetting_S_le_normalizer_T (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    ((wreathedSetting n S e p f).S : Subgroup G) ≤
      Subgroup.normalizer ((wreathedSetting n S e p f).T : Set G) := by
  show (S : Subgroup G) ≤ Subgroup.normalizer (Subgroup.closure
    {wreathModelHom S e (Original.x (2 ^ n)), wreathModelHom S e (Original.x2 (2 ^ n))} : Set G)
  rw [← CompatibleFamilies.modelT_eq_closure S e hn]
  exact (sylow_le_modelBase_normalizer S e).trans
    (modelBase_normalizer_le_modelT_normalizer n hn S e)

omit [Finite G] in
theorem wreathedSetting_ON_le_L₀ (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    (wreathedSetting n S e p f).ON ≤ (wreathedSetting n S e p f).L₀ := by
  have hk : (centralizerOddCoreMap n S e).ker = centralizerOddCore n S e :=
    QuotientGroup.ker_mk' _
  show (CFSG.oddCore (involutionCentralizer n S e)).map (involutionCentralizer n S e).subtype ≤
    ((CFSG.layer (centralizerOddCoreQuotient n S e)).comap
      (centralizerOddCoreMap n S e)).map (involutionCentralizer n S e).subtype
  apply Subgroup.map_mono
  change centralizerOddCore n S e ≤ _
  rw [← hk]
  exact MonoidHom.ker_le_comap _ _

omit [Finite G] in
theorem wreathedSetting_N_le_normalizer_L₀ (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) :
    (wreathedSetting n S e p f).N ≤
      Subgroup.normalizer ((wreathedSetting n S e p f).L₀ : Set G) := by
  have : (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := by
    rw [CFSG.layer_eq_componentClassification]
    exact CFSG.ComponentClassification.Layer.normal _
  have : ((CFSG.layer (centralizerOddCoreQuotient n S e)).comap
      (centralizerOddCoreMap n S e)).Normal := Subgroup.Normal.comap inferInstance _
  exact le_normalizer_map_subtype (involutionCentralizer n S e) _

omit [Finite G] in
theorem wreathedSetting_L₀_surjection_of_layer_equiv (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) {H : Type*} [Group H]
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃* H) :
    ∃ ψ : (wreathedSetting n S e p f).L₀ →* H, Function.Surjective ψ ∧
      ψ.ker = (wreathedSetting n S e p f).ON.subgroupOf (wreathedSetting n S e p f).L₀ := by
  let N := involutionCentralizer n S e
  let π := centralizerOddCoreMap n S e
  let K := (CFSG.layer (centralizerOddCoreQuotient n S e)).comap π
  let e₁ : K ≃* (wreathedSetting n S e p f).L₀ :=
    K.equivMapOfInjective N.subtype N.subtype_injective
  have hk : π.ker = centralizerOddCore n S e := QuotientGroup.ker_mk' _
  refine ⟨eta.toMonoidHom.comp ((π.subgroupComap _).comp e₁.symm.toMonoidHom), ?_, ?_⟩
  · exact eta.surjective.comp ((π.subgroupComap_surjective _
      (centralizerOddCoreMap_surjective n S e)).comp e₁.symm.surjective)
  · ext g
    have hg : (((e₁.symm g : K) : N) : G) = g := congrArg Subtype.val (e₁.apply_symm_apply g)
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, MonoidHom.comp_apply,
      ← OneMemClass.coe_eq_one]
    change π ((e₁.symm g : K) : N) = 1 ↔ (g : G) ∈ (CFSG.oddCore N).map N.subtype
    rw [← MonoidHom.mem_ker, hk, ← hg]
    exact (Subgroup.mem_map_iff_mem N.subtype_injective).symm

theorem wreathedSetting_isValid
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    (wreathedSetting n S e p f).IsValid := by
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  obtain ⟨F, hfield, hfinite, hcard, -, -, _theta, _rho, eta, -⟩ :=
    FullCentralizerFromProjectiveModel.actual_projective_layer_model_determines_full_centralizer
      hnonab n hn S e hfour p f hp hp2 hf hlocal
  obtain ⟨ψ, hψ, hker⟩ := wreathedSetting_L₀_surjection_of_layer_equiv n S e p f eta
  exact {
    simple := inferInstance
    nonabelian := hnonab
    sylow := wreathedSetting_sylow n hn S e p f
    x_order := CompatibleFamilies.orderOf_x S e hn
    x_mem_center := wreathedSetting_x_mem_center n hn S e p f
    center_involution := wreathedSetting_center_involution n hn S e p f
    x₂_order := CompatibleFamilies.orderOf_x2 S e hn
    x₂_mem := (e.symm (Original.x2 (2 ^ n))).property
    commute := BrauerWong.modelBase_commute S e _ _ (BrauerWong.modelHom_x_mem_modelBase S e)
      (BrauerWong.modelHom_x2_mem_modelBase S e)
    x_ne_x₂ := BrauerWong.modelHom_x_ne_x2 S e (by omega)
    T_normal := fun _ => wreathedSetting_S_le_normalizer_T n (by omega) S e p f
    p_prime := hp
    p_ne_two := hp2
    one_le_f := hf
    five_lt_q := hq
    L₀_le_N := Subgroup.map_subtype_le _
    ON_le_L₀ := wreathedSetting_ON_le_L₀ n S e p f
    N_le_normalizer_L₀ := wreathedSetting_N_le_normalizer_L₀ n S e p f
    L₀_quotient := ⟨F, hfield, hfinite, hcard, ψ, hψ, hker⟩ }

end CFSG.Wreathed.OriginalAllPrime
