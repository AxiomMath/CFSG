module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListLevi2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2b
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualTriality
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem perfectCore_le_commutator' {G : Type*} [Group G] [Finite G] (M : Subgroup G) :
    perfectCore M ≤ ⁅M, M⁆ :=
  calc perfectCore M = ⁅perfectCore M, perfectCore M⁆ := (perfectCore_perfect M).symm
    _ ≤ ⁅M, M⁆ := Subgroup.commutator_mono (perfectCore_le M) (perfectCore_le M)

theorem eq_one_of_sq_eq_one_charTwo {F : Type*} [Field F] [CharP F 2] {l : F} (hl : l ^ 2 = 1) :
    l = 1 := by
  have h2 : (l - 1) ^ 2 = 0 := by
    linear_combination hl + (1 - l) * (CharTwo.two_eq_zero : (2 : F) = 0)
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)

section Fixed

variable {t : TwistTag} {K : Type} [Field K] (σ : K ≃+* K) (a : Fin t.foldedTag.rank)

theorem fixed_structure
    :
    ∃ R : SL2 (orbitField t K σ.toRingHom a) →* ModGL t.tag K,
      graphFixedSimpleComplement t K σ.toRingHom a ≤ fixedPosWeylGroup t K σ.toRingHom a ∧
      fixedPosWeylGroup t K σ.toRingHom a ≤
        Subgroup.normalizer (graphFixedSimpleComplement t K σ.toRingHom a : Set (ModGL t.tag K)) ∧
      graphFixedSimpleComplement t K σ.toRingHom a ⊔ R.range =
        fixedPosWeylGroup t K σ.toRingHom a ∧
      R.range ≤
        Subgroup.normalizer (graphFixedSimpleComplement t K σ.toRingHom a : Set (ModGL t.tag K)) ∧
      ∀ g ∈ R.ker, ∃ l : (orbitField t K σ.toRingHom a)ˣ,
        ((l : orbitField t K σ.toRingHom a) ^ 2 = 1) ∧
          (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ.toRingHom a)) =
            (l : orbitField t K σ.toRingHom a) •
              (1 : Matrix (Fin 2) (Fin 2) (orbitField t K σ.toRingHom a)) := by
  obtain ⟨R, hRx, hRy, -, hRW, hRn, hrange, -, hker, -⟩ :=
    exceptional_fixed_rank_one_central_image t K σ.toRingHom a
  obtain ⟨hVU, hVnormal, hmul, -, -, -, -, hnV, -, himage⟩ :=
    fixed_simple_positive_complement t K σ a
  have hUnormV : graphFixedPosUnipotent t K σ.toRingHom ≤
      Subgroup.normalizer (graphFixedSimpleComplement t K σ.toRingHom a : Set (ModGL t.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVU).mp hVnormal
  have hX : ∀ c, (orbitX t K σ.toRingHom a c : ModGL t.tag K) ∈
      graphFixedPosUnipotent t K σ.toRingHom :=
    fun c => orbitX_mem_graphFixedPosUnipotent t σ.toRingHom a c
  have hUN := graphFixedPosUnipotent_le_fixedPosWeylGroup (t := t) (K := K) (σ := σ.toRingHom) a
  have hRN : R.range ≤ fixedPosWeylGroup t K σ.toRingHom a := by
    rw [hrange]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hUN (hX c)
    · exact orbitY_mem_fixedPosWeylGroup a c
  have hRnorm : R.range ≤
      Subgroup.normalizer (graphFixedSimpleComplement t K σ.toRingHom a : Set (ModGL t.tag K)) := by
    rw [hrange]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hUnormV (hX c)
    · have hy : (orbitY t K σ.toRingHom a c : ModGL t.tag K) ∈
          (fun g => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * g *
            (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹) ''
            Set.range (fun c : orbitField t K σ.toRingHom a =>
              (orbitX t K σ.toRingHom a c : ModGL t.tag K)) := by
        rw [himage]
        exact ⟨c, rfl⟩
      obtain ⟨_, ⟨c', rfl⟩, hyc⟩ := hy
      show (orbitY t K σ.toRingHom a c : ModGL t.tag K) ∈
        Subgroup.normalizer (graphFixedSimpleComplement t K σ.toRingHom a : Set (ModGL t.tag K))
      rw [← hyc]
      exact mul_mem (mul_mem hnV (hUnormV (hX c'))) (inv_mem hnV)
  refine ⟨R, hVU.trans hUN, ?_, ?_, hRnorm, hker⟩
  · exact sup_le hUnormV ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hnV))
  · refine le_antisymm (sup_le (hVU.trans hUN) hRN) ?_
    refine sup_le (fun u hu => ?_) ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 ?_))
    · have hu' : u ∈ (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K)) := hu
      rw [hmul] at hu'
      obtain ⟨v, hv, _, ⟨c, rfl⟩, rfl⟩ := hu'
      exact mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right ⟨uSL c, hRx c⟩)
    · exact Subgroup.mem_sup_right ⟨WSL, by rw [hRW, hRn]⟩

theorem fixed_rankOne_injective [CharP K 2] {R : SL2 (orbitField t K σ.toRingHom a) →* ModGL t.tag K}
    (hker : ∀ g ∈ R.ker, ∃ l : (orbitField t K σ.toRingHom a)ˣ,
      ((l : orbitField t K σ.toRingHom a) ^ 2 = 1) ∧
        (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ.toRingHom a)) =
          (l : orbitField t K σ.toRingHom a) •
            (1 : Matrix (Fin 2) (Fin 2) (orbitField t K σ.toRingHom a))) :
    Function.Injective R := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  obtain ⟨l, hl, hgl⟩ := hker g hg
  have hl1 : (l : orbitField t K σ.toRingHom a) = 1 := eq_one_of_sq_eq_one_charTwo hl
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [hgl, hl1, one_smul]
  rfl

variable [Finite K]

theorem fixed_perfectCore_eq
    :
    perfectCore (graphFixedParabolic t K σ.toRingHom {a}) =
      perfectCore (fixedPosWeylGroup t K σ.toRingHom a) := by
  have : Finite (ModGL t.tag K) := finite_modGL
  exact le_antisymm
    (le_perfectCore_of_perfect
      ((perfectCore_le_commutator' _).trans
        (commutator_graphFixedParabolic_le_fixedPosWeylGroup σ.surjective a))
      (perfectCore_perfect _))
    (perfectCore_mono (fixedPosWeylGroup_le_graphFixedParabolic_singleton σ.surjective a))

theorem exists_levi_hom_fixed
    [CharP K 2]
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent t K σ.toRingHom))
    (hL4 : ∃ s : Finset ↥(orbitField t K σ.toRingHom a), s.card = 4) :
    ∃ g : ↥(perfectCore ((graphFixedParabolic t K σ.toRingHom {a}).subgroupOf
        (graphFixedRootGroup t K σ.toRingHom))) →* SL2 ↥(orbitField t K σ.toRingHom a),
      Function.Surjective g ∧ IsPGroup 2 g.ker := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL t.tag K) := finite_modGL
  obtain ⟨R, hVN, hNV, hsup, hRV, hker⟩ := fixed_structure σ a
  have hRinj : Function.Injective R := fixed_rankOne_injective σ a hker
  have hsimple : IsSimpleGroup (SL2 ↥(orbitField t K σ.toRingHom a)) := sl2_isSimple hL4
  have hperfSL : Group.IsPerfect (SL2 ↥(orbitField t K σ.toRingHom a)) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect hL4
  let e : SL2 ↥(orbitField t K σ.toRingHom a) ≃* ↥R.range := MonoidHom.ofInjective hRinj
  have hsimpleM : IsSimpleGroup ↥R.range := e.symm.isSimpleGroup
  have hMperf : ⁅R.range, R.range⁆ = R.range := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range R)
  have hVU : graphFixedSimpleComplement t K σ.toRingHom a ≤ graphFixedPosUnipotent t K σ.toRingHom :=
    graphFixedSimpleComplement_le a
  have hV2 : IsPGroup 2 ↥(graphFixedSimpleComplement t K σ.toRingHom a) :=
    IsPGroup.of_injective hU (Subgroup.inclusion hVU) (Subgroup.inclusion_injective hVU)
  obtain ⟨g, hg, hk⟩ := exists_levi_hom_final (C := graphFixedRootGroup t K σ.toRingHom)
    (fixedPosWeylGroup_le_graphFixedParabolic_singleton σ.surjective a)
    (graphFixedParabolic_le _ _ _ _) (fixed_perfectCore_eq σ a) hVN hNV hsup hRV hV2 hMperf
  refine ⟨e.symm.toMonoidHom.comp g, e.symm.surjective.comp hg, ?_⟩
  have hkerEq : (e.symm.toMonoidHom.comp g).ker = g.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact MulEquiv.map_eq_one_iff e.symm
  rw [hkerEq]
  exact hk

theorem fixed_leviData
    [CharP K 2] (hU : IsPGroup 2 ↥(graphFixedPosUnipotent t K σ.toRingHom)) :
    LeviData ((graphFixedParabolic t K σ.toRingHom {a}).subgroupOf
      (graphFixedRootGroup t K σ.toRingHom)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL t.tag K) := finite_modGL
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card ↥(orbitField t K σ.toRingHom a) = 2 ^ m := by
    have : Fintype ↥(orbitField t K σ.toRingHom a) := Fintype.ofFinite _
    obtain ⟨n, -, hn⟩ := FiniteField.card ↥(orbitField t K σ.toRingHom a) 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hpos : 1 < Nat.card ↥(orbitField t K σ.toRingHom a) := Finite.one_lt_card
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  ·
    left
    have hm1 : m = 1 := by
      rcases Nat.lt_or_ge m 1 with h0 | h1
      · have h00 : m = 0 := by omega
        rw [h00, pow_zero] at hm
        omega
      · omega
    subst hm1
    obtain ⟨R, hVN, hNV, hsup, hRV, hker⟩ := fixed_structure σ a
    have hVU : graphFixedSimpleComplement t K σ.toRingHom a ≤
        graphFixedPosUnipotent t K σ.toRingHom := graphFixedSimpleComplement_le a
    have hV2 : IsPGroup 2 ↥(graphFixedSimpleComplement t K σ.toRingHom a) :=
      IsPGroup.of_injective hU (Subgroup.inclusion hVU) (Subgroup.inclusion_injective hVU)
    have hVs : Group.IsSolvable ↥(graphFixedSimpleComplement t K σ.toRingHom a) := by
      have := hV2.isNilpotent
      infer_instance
    have hsolvSL : Group.IsSolvable (SL2 ↥(orbitField t K σ.toRingHom a)) := by
      refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hm]
      norm_num
    have hMs : Group.IsSolvable ↥R.range :=
      Group.isSolvable_of_surjective (f := R.rangeRestrict) (MonoidHom.rangeRestrict_surjective R)
    have hNs : Group.IsSolvable ↥(fixedPosWeylGroup t K σ.toRingHom a) :=
      isSolvable_of_levi hVN hNV hsup hVs hMs
    have hpcN : perfectCore (fixedPosWeylGroup t K σ.toRingHom a) = ⊥ :=
      (isSolvable_iff_perfectCore_eq_bot _).mp hNs
    have hPC : graphFixedParabolic t K σ.toRingHom {a} ≤ graphFixedRootGroup t K σ.toRingHom :=
      graphFixedParabolic_le _ _ _ _
    apply Subgroup.map_injective (graphFixedRootGroup t K σ.toRingHom).subtype_injective
    rw [perfectCore_map_subgroupOf hPC, fixed_perfectCore_eq σ a, hpcN, Subgroup.map_bot]
  ·
    right
    have hL4 : ∃ s : Finset ↥(orbitField t K σ.toRingHom a), s.card = 4 := by
      refine exists_finset_card_four ?_
      rw [hm]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    obtain ⟨g, hg, hker⟩ := exists_levi_hom_fixed σ a hU hL4
    exact ⟨↥(orbitField t K σ.toRingHom a), inferInstance, inferInstance, inferInstance, m, hm, hm2,
      g, hg, hker⟩

end Fixed

section D4

variable {K : Type} [Field K] [Finite K]

theorem a312For_D4
    {f : ℕ} (hf : 1 ≤ f) (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hq : CFSG.IsQuasisimple ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hR : IsRank2LieChar2 ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    A312For ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
  refine a312For_of_rank2_levi_gen hq hU₀ (triality_residualOvergroupsAt σ) ?_ hR ?_
  · intro j c hc
    have hc' : (c : ModGL TwistTag.D4.tag K) ∈
        Subgroup.normalizer (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
          Set (ModGL TwistTag.D4.tag K)) := by
      have key : ∀ v : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
          (v : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ↔
          ((c * v * c⁻¹ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
        fun v => Subgroup.mem_normalizer_iff.1 hc v
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        exact (key ⟨u, hUC hu⟩).1 hu
      · intro hcu
        have huC : u ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
          have : u = (c : ModGL TwistTag.D4.tag K)⁻¹ *
              ((c : ModGL TwistTag.D4.tag K) * u * (c : ModGL TwistTag.D4.tag K)⁻¹) *
              (c : ModGL TwistTag.D4.tag K) := by group
          rw [this]
          exact mul_mem (mul_mem (inv_mem c.2) (hUC hcu)) c.2
        exact (key ⟨u, huC⟩).2 hcu
    obtain ⟨-, -, -, -, -, -, hNU, -⟩ := fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀
    have hB : (c : ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
      rw [← hNU]
      exact ⟨c.2, hc'⟩
    exact graphFixedRootBorel_le_graphFixedParabolic _ _ _ _ hB
  · intro j
    exact fixed_leviData σ (d4Index j) hUsyl.2.1

end D4

theorem d4
    : FamD4 := by
  intro X _ _ f hq hf hX
  obtain ⟨-, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hX
  have hR : IsRank2LieChar2 X :=
    Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hX⟩))))⟩
  exact A312For.of_mulEquiv e (a312For_D4 hf σ hK (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq)
    (IsRank2LieChar2.of_mulEquiv e hR))

end CFSG.QuasithinUnique.Vol2Native.A312L
