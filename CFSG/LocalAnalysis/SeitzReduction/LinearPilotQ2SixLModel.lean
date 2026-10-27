module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGSix
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem seitzLeviBar_facts_six (hset : SeitzSetting G L) {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {c : Fin 6}
    {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 10) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G)) :
    t ∉ W₁ ∧
      orderOf (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htN⟩) = 2 ∧
      seitzLeviBar e c W₁ ≤ centralizer
        ({QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htN⟩} :
          Set (seitzBar W₁)) ∧
      CFSG.Open.IsQuasisimple (seitzLeviBar e c W₁) ∧ center (seitzLeviBar e c W₁) = ⊥ ∧
      centralizer ({QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htN⟩} :
          Set (seitzBar W₁)) ≤
        seitzLeviBar e c W₁ ⊔
          zpowers (QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htN⟩) := by
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht
    exact absurd ht (by decide)
  have htW : t ∉ W₁ := fun h => by
    have h' : t ∈ W₁ ⊓ centralizer ({t} : Set G) :=
      Subgroup.mem_inf.2 ⟨h, mem_centralizer_singleton_iff.2 rfl⟩
    rw [hW₁t] at h'
    exact not_mem_of_mem_centralizer hset.center_eq_bot htC ht1 (modelToG_le e _ h')
  have hWc : ∀ v ∈ W₁, ∀ w ∈ W₁, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW₁2 hv hw
  set s : seitzBar W₁ := QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨t, htN⟩
    with hs_def
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : orderOf s = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hs_def, ← map_pow]
      have : (⟨t, htN⟩ : normalizer (W₁ : Set G)) ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
      rw [this, map_one]
    · intro h1
      rw [hs_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      exact htW h1
  have hLs : seitzLeviBar e c W₁ ≤ centralizer ({s} : Set (seitzBar W₁)) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [mem_centralizer_singleton_iff, hs_def, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_iff.1 htC) _ (modelToG_le e _ (mem_subgroupOf.1 hl))
  obtain ⟨hsimp, hnonab⟩ := isSimpleGroup_seitzLeviBar hK e c hWc hLN
  obtain ⟨hLq, hLZ⟩ := open_isQuasisimple_and_center_of_isSimpleGroup
    (X := seitzLeviBar e c W₁) hnonab
  exact ⟨htW, hs, hLs, hLq, hLZ,
    lSixNOneCentralizerInput G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN⟩

theorem exists_specialLinear_three_le_centralizer_of_fieldType (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 6 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {c : Fin 6}
    {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 10) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hLK : seitzLeviHat e c W₁ < Kc)
    (hKt' : Kc.map (MulAut.conj (seitzHatMap W₁ ⟨t, htN⟩)).toMonoidHom = Kc)
    (hmodel : LieModel Kc .PSL 5 2 2) {a b : Fin 6} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL 6 K)} (hX₀ : X₀ ≤ rootSL2 a b) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ 2 ∧
      ∃ S : Subgroup (seitzHat W₁), S ≤ Kc ∧ ⁅S, S⁆ = S ∧
        S ≤ centralizer ((((modelToG e X₀).subgroupOf (normalizer (W₁ : Set G))).map
          (seitzHatMap W₁) : Subgroup (seitzHat W₁)) : Set (seitzHat W₁)) ∧
        Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 3) F) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  obtain ⟨htW, hs, hLs, hLq, hLZ, hCs⟩ :=
    seitzLeviBar_facts_six hset hK e ht hKt hW₁c hW₁2 hW₁t htN hLN
  have hmap : (seitzLeviBar e c W₁).map (QuotientGroup.mk' (oddCore (seitzBar W₁))) =
      seitzLeviHat e c W₁ := by
    rw [seitzLeviBar, seitzLeviHat, Subgroup.map_map]
    rfl
  obtain ⟨hcomp, -, -⟩ := inheritance_of_centralizer_le_sup hs hLs hLq hLZ hCs
  rw [hmap] at hcomp
  have hZL : center (seitzLeviHat e c W₁) = ⊥ := by
    rw [← hmap, ← map_center_eq (mapOddCoreMulEquivOfCenter hLq hLZ), hLZ, Subgroup.map_bot]
  have hNcard : ({c}ᶜ : Finset (Fin 6)).card = 5 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hNc5 : ({c}ᶜ : Finset (Fin 6)).card < 6 := by rw [hNcard]; norm_num
  let eN : ({c}ᶜ : Finset (Fin 6)) ≃ Fin 5 := Finset.equivFinOfCardEq hNcard
  have hmemN : ∀ B : Matrix.SpecialLinearGroup (Fin 5) K,
      ((e.symm ((blockSLEquivOfEquiv (K := K) hNc5 eN B : blockSL (K := K)
        ({c}ᶜ : Finset (Fin 6))) : LinearFlag.projectiveSL 6 K) : L) : G) ∈
        normalizer (W₁ : Set G) :=
    fun B => hLN (symm_mem_modelToG e (blockSLEquivOfEquiv (K := K) hNc5 eN B).2)
  let φ₀ : Matrix.SpecialLinearGroup (Fin 5) K →* normalizer (W₁ : Set G) :=
    (L.subtype.comp (e.symm.toMonoidHom.comp
      ((blockSL (K := K) ({c}ᶜ : Finset (Fin 6))).subtype.comp
        (blockSLEquivOfEquiv (K := K) hNc5 eN).toMonoidHom))).codRestrict _ hmemN
  let φ : Matrix.SpecialLinearGroup (Fin 5) K →* seitzHat W₁ := (seitzHatMap W₁).comp φ₀
  have hφ₀ : φ₀.range = (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6)))).subgroupOf
      (normalizer (W₁ : Set G)) := by
    ext y
    constructor
    · rintro ⟨B, rfl⟩
      exact mem_subgroupOf.2 (symm_mem_modelToG e (blockSLEquivOfEquiv (K := K) hNc5 eN B).2)
    · intro hy
      obtain ⟨x, hx, hxy⟩ := (mem_modelToG e).1 (mem_subgroupOf.1 hy)
      refine ⟨(blockSLEquivOfEquiv (K := K) hNc5 eN).symm ⟨x, hx⟩, Subtype.ext ?_⟩
      show ((e.symm ((blockSLEquivOfEquiv (K := K) hNc5 eN
        ((blockSLEquivOfEquiv (K := K) hNc5 eN).symm ⟨x, hx⟩) :
          blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) : LinearFlag.projectiveSL 6 K) : L) : G) =
        (y : G)
      rw [MulEquiv.apply_symm_apply]
      exact hxy
  have hφ : φ.range = seitzLeviHat e c W₁ := by
    rw [MonoidHom.range_comp, hφ₀]
  have hne : φ.range ≠ ⊥ := hφ ▸ ne_bot_of_isQuasisimple hcomp.2.2
  obtain ⟨ε, hεinj, hεrange, hεapp⟩ := SymplecticPilot.exists_projectiveSL_embedding_of_hom
    (Kc := Kc) (by norm_num) φ hne (hφ ▸ hZL) (hφ ▸ hLK.le)
  obtain ⟨F, _, _, hF, ⟨ψ₀⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hmodel
  obtain ⟨ι, σ, hσ1, hσσ, hfix⟩ :=
    exists_subfield_involution (K := K) (F := F) le_rfl hK1 (hF.trans (by norm_num))
  have hsN : seitzHatMap W₁ ⟨t, htN⟩ ∈ normalizer (Kc : Set (seitzHat W₁)) :=
    mem_normalizer_iff_map_conj_eq.2 hKt'
  have hŝ2 : seitzHatMap W₁ ⟨t, htN⟩ ^ 2 = 1 := by
    rw [← orderOf_seitzHatMap_eq_two htN ht htW, pow_orderOf_eq_one]
  have hθ : Kc.normalizerMonoidHom ⟨_, hsN⟩ * Kc.normalizerMonoidHom ⟨_, hsN⟩ = 1 := by
    rw [← sq]
    exact F4Pilot.normalizerMonoidHom_sq_eq_one Kc hsN hŝ2
  have hDs : seitzLeviHat e c W₁ ≤
      centralizer ({seitzHatMap W₁ ⟨t, htN⟩} : Set (seitzHat W₁)) := hcomp.1
  have hDc : IsComponent ((seitzLeviHat e c W₁).subgroupOf
      (centralizer ({seitzHatMap W₁ ⟨t, htN⟩} : Set (seitzHat W₁)))) :=
    (isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hcomp)
  have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hLK.le
  have hD'c : IsComponent (((seitzLeviHat e c W₁).subgroupOf Kc).subgroupOf
      (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩))) :=
    F4Pilot.isComponent_subgroupOf_subgroupOf
      (F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN) hDcomp
  have hεθ : ε.range ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩) := by
    rw [hεrange, hφ, F4Pilot.fixedSubgroup_normalizerMonoidHom]
    intro x hx
    exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
  obtain ⟨ψ, hψε, -⟩ := exists_mulEquiv_projMap_eq_of_isComponent (n := 5) (by norm_num)
    (f := 1) le_rfl hK1 ι hσ1 hσσ hfix ψ₀ hθ ε hεinj hεθ (by rw [hεrange, hφ]; exact hD'c)
  have ha : a ∈ ({c}ᶜ : Finset (Fin 6)) :=
    Finset.mem_compl.2 fun h => hca (Finset.mem_singleton.1 h).symm
  have hb : b ∈ ({c}ᶜ : Finset (Fin 6)) :=
    Finset.mem_compl.2 fun h => hcb (Finset.mem_singleton.1 h).symm
  have hab' : eN ⟨a, ha⟩ ≠ eN ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val (eN.injective h))
  have hT₅ : (({eN ⟨a, ha⟩, eN ⟨b, hb⟩} : Finset (Fin 5))ᶜ).card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab']
  have hT₅5 : (({eN ⟨a, ha⟩, eN ⟨b, hb⟩} : Finset (Fin 5))ᶜ).card < 5 := by
    rw [hT₅]
    norm_num
  set S₀ : Subgroup Kc := (blockSL (K := F) (({eN ⟨a, ha⟩, eN ⟨b, hb⟩} : Finset (Fin 5))ᶜ)).map
    ψ.symm.toMonoidHom with hS₀
  refine ⟨F, inferInstance, inferInstance, hF, S₀.map Kc.subtype, map_subtype_le _, ?_, ?_, ?_⟩
  ·
    rw [← map_commutator, hS₀, ← map_commutator,
      commutator_blockSL_eq_of_three_le (by rw [hT₅])]
  ·
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x₀, hx₀, hx₀y⟩ := (mem_modelToG e).1 (mem_subgroupOf.1 hy)
    have hx₀' : x₀ ∈ rootSL2 (K := K) a b := hX₀ hx₀
    rw [← map_blockSLEquivOfEquiv_pair hNc5 eN ha hb] at hx₀'
    obtain ⟨_, ⟨B, hB, rfl⟩, rfl⟩ := hx₀'
    have hφB : φ B = seitzHatMap W₁ y := by
      show seitzHatMap W₁ (φ₀ B) = seitzHatMap W₁ y
      congr 1
      exact Subtype.ext hx₀y
    have hyK : seitzHatMap W₁ y ∈ Kc := by
      rw [← hφB]
      exact hLK.le (hφ ▸ (⟨B, rfl⟩ : φ B ∈ φ.range))
    have hεB : ε (LinearFlag.proj 5 K B) = ⟨seitzHatMap W₁ y, hyK⟩ :=
      Subtype.ext (by rw [hεapp, hφB])
    have hψy : ψ ⟨seitzHatMap W₁ y, hyK⟩ ∈
        blockSL (K := F) ({eN ⟨a, ha⟩, eN ⟨b, hb⟩} : Finset (Fin 5)) := by
      rw [← hεB, hψε, projMap_proj]
      exact proj_mem_blockSL (map_ringHom_mem_blockSpecialLinear ι hB)
    obtain ⟨z, hz, rfl⟩ := hk
    have h1 : ψ ⟨seitzHatMap W₁ y, hyK⟩ * z = z * ψ ⟨seitzHatMap W₁ y, hyK⟩ :=
      mem_centralizer_iff.1 (blockSL_le_centralizer_blockSL_of_disjoint disjoint_compl_left hz) _
        hψy
    have h2 : (⟨seitzHatMap W₁ y, hyK⟩ : Kc) * ψ.symm z = ψ.symm z * ⟨seitzHatMap W₁ y, hyK⟩ := by
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h1]
    exact congrArg Subtype.val h2
  ·
    exact ⟨((S₀.equivMapOfInjective Kc.subtype Kc.subtype_injective).symm.trans
      ((blockSL (K := F) (({eN ⟨a, ha⟩, eN ⟨b, hb⟩} : Finset (Fin 5))ᶜ)).equivMapOfInjective
        ψ.symm.toMonoidHom ψ.symm.injective).symm).trans
      (blockSLEquivOfEquiv (K := F) hT₅5 (Finset.equivFinOfCardEq hT₅)).symm⟩

end CFSG.SeitzReduction.LinearPilot
