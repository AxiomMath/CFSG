module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4Stab
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthChev
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExceptionalBase
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTriality
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4FieldFrob

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Dickson.I271 (isChevSimple_of_mulEquiv isLTwoTwentySeven_of_mulEquiv)
open CFSG.ComponentClassification.CatLeafProof (lieModel_graphFixedRootGroup_trialityD4_odd)
open CFSG.HardMathSupport.Lang.E6Descent (twistedEntrywiseAut_pow_order
  fixedSubgroup_twistedEntrywiseAut_one)
open scoped commutatorElement

set_option linter.unusedSectionVars false


section Field

variable {K : Type} [Field K] [Finite K]

theorem outerCentData_entrywise_D4 [CharP K 3] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (T : K ≃+* K) (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1)
    (hout : entrywiseAdjointAut Tag.D4 T ∉ innerAut (adjointGroup Tag.D4 K)) :
    OuterCentData 3 (entrywiseAdjointAut Tag.D4 T) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  set β := entrywiseAdjointAut Tag.D4 T with hβ
  have hβ3 : β ^ 3 = 1 := by
    rw [hβ, ← entrywiseAdjointAut_pow, hT3, entrywiseAdjointAut_one]
  have hβ1 : β ≠ 1 := fun h => hout (h ▸ (innerAut _).one_mem)
  have hord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  have hZ : Subgroup.center (adjointGroup Tag.D4 K) = ⊥ := center_adjointGroup_eq_bot_field _ K
  have hk2 : ringChar (fixSubfield T) ≠ 2 := by
    intro h
    have h0 : ((2 : ℕ) : fixSubfield T) = 0 := by
      rw [← h]
      exact ringChar.Nat.cast_ringChar
    apply Ring.two_ne_zero hM
    have := congrArg (fixSubfield T).subtype h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  obtain ⟨hs, hnc, -⟩ := odd_pinned_Chevalley_p_components Tag.D4 (fixSubfield T) hk2
  obtain ⟨-, -, -, hJΓ, -, hnormal, -, hder⟩ :=
    Chevalley_coordinate_field_fixed_structure Tag.D4 K hM T
  have hJA : fixedFieldImage Tag.D4 T ≤ adjointGroup Tag.D4 K := hJΓ.trans inf_le_left
  have hΓ : ∀ n : ↥(fixSubgroup β), ((n : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈
      entrywiseFixedGroup Tag.D4 T := fun n =>
    ⟨(n : ↥(adjointGroup Tag.D4 K)).2, by
      have h1 : β n = n := n.2
      have := congrArg Subtype.val h1
      rwa [coe_entrywiseAdjointAut] at this⟩
  set J : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (fixedFieldImage Tag.D4 T).subgroupOf (adjointGroup Tag.D4 K) with hJ
  have hmemJ : ∀ x : ↥(adjointGroup Tag.D4 K), x ∈ J ↔ (x : ModGL Tag.D4 K) ∈
      fixedFieldImage Tag.D4 T := fun x => Iff.rfl
  have hJC : J ≤ fixSubgroup β := fun x hx => by
    rw [mem_fixSubgroup]
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact (hJΓ ((hmemJ x).1 hx)).2
  have hJn : (J.subgroupOf (fixSubgroup β)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, hmemJ] at hn ⊢
    have h1 := hnormal.conj_mem ⟨((n : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K), hΓ n⟩
      (Subgroup.mem_subgroupOf.2 hn) ⟨((g : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K), hΓ g⟩
    simpa using Subgroup.mem_subgroupOf.1 h1
  let eJ : ↥J ≃* adjointGroup Tag.D4 (fixSubfield T) :=
    (Subgroup.subgroupOfEquivOfLe hJA).trans (fixedFieldImageEquiv T).symm
  haveI := hs
  haveI hJs : IsSimpleGroup ↥J := eJ.isSimpleGroup
  have hncJ : ∃ x y : ↥J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eJ.symm x, eJ.symm y, fun h => hxy (by simpa using congrArg eJ h)⟩
  have hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ J.subgroupOf (fixSubgroup β)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [h1, Subgroup.mem_subgroupOf, hmemJ]
    have h2 : (((⁅y⁻¹, x⁻¹⁆ : ↥(fixSubgroup β)) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        ⁅(((y⁻¹ : ↥(fixSubgroup β)) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K),
          (((x⁻¹ : ↥(fixSubgroup β)) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)⁆ := by
      simp [commutatorElement_def]
    rw [h2, ← hder]
    exact Subgroup.commutator_mem_commutator (hΓ _) (hΓ _)
  have hstab : ∀ w : MulAut (adjointGroup Tag.D4 K), w * β = β * w → (∀ x ∈ J, w x = x) →
      w ∈ Subgroup.zpowers β := fun w _ hw =>
    mem_zpowers_of_forall_fixedFieldImage T fun j hj => hw j ((hmemJ j).2 hj)
  have hordT : orderOf T = 3 := orderOf_eq_prime hT3 hT1
  obtain ⟨hdvd3, hkcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_three hf hK T
  rw [hordT] at hdvd3 hkcard
  have hfp : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd hf hdvd3) (by norm_num)
  obtain ⟨Φ⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup
      (fixSubfield T)
  have hmodelJ : StatedClassicalModel ↥J .POmegaPlus 4 3 (f / 3) :=
    ⟨⟨Nat.prime_three, hfp, le_rfl⟩, ↥(fixSubfield T), inferInstance, inferInstance, hkcard,
      ⟨eJ.trans Φ.symm⟩⟩
  have ht : (StatedLieTag.POmegaPlus = .PSp ∧ 2 ≤ 4) ∨
      (StatedLieTag.POmegaPlus = .POmegaOdd ∧ 3 ≤ 4) ∨
      (StatedLieTag.POmegaPlus = .POmegaPlus ∧ 4 ≤ 4) ∨
      (StatedLieTag.POmegaPlus = .POmegaMinus ∧ 4 ≤ 4) := Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl⟩))
  exact OuterCentData.ofStabilizer Nat.prime_three hord hout hZ hJC hJn hJs hncJ hsol hstab
    (isChevSimple_of_pomegaPlus hmodelJ) (dvd_card hmodelJ ht)
    (fun _ => not_isLTwoTwentySeven hmodelJ ht)

end Field

section GraphField

variable {K : Type} [Field K] [Finite K]

theorem ofStabilizer_of_fix_eq {p : ℕ} {T : Type} [Group T] [Finite T] (hp : p.Prime)
    {α : MulAut T} (hα : orderOf α = p) (hout : α ∉ innerAut T) (hZ : Subgroup.center T = ⊥)
    {M N : Subgroup T} (hN : fixSubgroup α = N) (hle : M ≤ N) (hn : (M.subgroupOf N).Normal)
    (hs : IsSimpleGroup ↥M) (hnab : ∃ a b : ↥M, a * b ≠ b * a)
    (hsol : Group.IsSolvable (↥N ⧸ M.subgroupOf N))
    (hstab : ∀ w : MulAut T, w * α = α * w → (∀ x ∈ M, w x = x) → w ∈ Subgroup.zpowers α)
    (hchev : IsChevSimple p ↥M) (hdvd : p ∣ Nat.card ↥M) (hL27 : p = 3 → ¬ IsLTwoTwentySeven ↥M) :
    OuterCentData p α := by
  subst hN
  exact OuterCentData.ofStabilizer hp hα hout hZ hle hn hs hnab hsol hstab hchev hdvd hL27

theorem outerCentData_alphaOne [CharP K 3] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hout : alphaOne σ ∉ innerAut (adjointGroup Tag.D4 K)) :
    OuterCentData 3 (alphaOne σ) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hσσσ : ∀ c, σ (σ (σ c)) = c := fun c => by
    have h := congrArg (fun g : K ≃+* K => g c) hσ3
    simpa [pow_succ] using h
  have hβ3 : alphaOne σ ^ 3 = 1 := by
    rw [← twistedEntrywiseAut_one_eq]
    exact twistedEntrywiseAut_pow_order TwistTag.D4 1 σ hσ3
  have hβ1 : alphaOne σ ≠ 1 := fun h => hout (h ▸ (innerAut _).one_mem)
  have hord : orderOf (alphaOne σ) = 3 := orderOf_eq_prime hβ3 hβ1
  have hZ : Subgroup.center (adjointGroup Tag.D4 K) = ⊥ := center_adjointGroup_eq_bot_field _ K
  obtain ⟨hs, hnc, -⟩ := odd_diagram_field_fixed_p_components TwistTag.D4 K hM σ
  obtain ⟨hnormal, -, hcomm, -, -⟩ := fixed_root_generated_normal_subgroup TwistTag.D4 K σ
  have hC0Γ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤
      twistedFixedGroup TwistTag.D4 K σ.toRingHom := graphFixedRootGroup_le _ _ _
  have hΓA : twistedFixedGroup TwistTag.D4 K σ.toRingHom ≤ adjointGroup Tag.D4 K :=
    twistedFixedGroup_le_adjointGroup _ _ _
  have hC0A : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤ adjointGroup Tag.D4 K :=
    hC0Γ.trans hΓA
  have hfix : fixSubgroup (alphaOne σ) =
      (twistedFixedGroup TwistTag.D4 K σ.toRingHom).subgroupOf (adjointGroup Tag.D4 K) := by
    rw [← twistedEntrywiseAut_one_eq]
    exact fixedSubgroup_twistedEntrywiseAut_one TwistTag.D4 σ
  have hnormal' := (Subgroup.normal_subgroupOf_iff hC0Γ).1 hnormal
  set J : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subgroupOf (adjointGroup Tag.D4 K) with hJdef
  set N : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (twistedFixedGroup TwistTag.D4 K σ.toRingHom).subgroupOf (adjointGroup Tag.D4 K) with hNdef
  have hJN : J ≤ N := fun x hx => hC0Γ hx
  have hJn : (J.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff hJN).2 fun h k hh hk => hnormal' _ _ hh hk
  let eJ : ↥J ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    Subgroup.subgroupOfEquivOfLe hC0A
  haveI := hs
  haveI hJs : IsSimpleGroup ↥J := eJ.isSimpleGroup
  have hncJ : ∃ x y : ↥J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨eJ.symm x, eJ.symm y, fun h => hxy ?_⟩
    have h' := congrArg eJ h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  have hmemJ : ∀ x : ↥(adjointGroup Tag.D4 K), x ∈ J ↔ (x : ModGL Tag.D4 K) ∈
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun x => Iff.rfl
  have hΓmem : ∀ n : ↥N, ((n : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈
      twistedFixedGroup TwistTag.D4 K σ.toRingHom := fun n => n.2
  have hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [h1, Subgroup.mem_subgroupOf, hmemJ]
    have h2 : (((⁅y⁻¹, x⁻¹⁆ : ↥N) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        ⁅(((y⁻¹ : ↥N) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K),
          (((x⁻¹ : ↥N) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)⁆ := by
      simp [commutatorElement_def]
    rw [h2]
    exact hcomm (Subgroup.commutator_mem_commutator (hΓmem _) (hΓmem _))
  have hstab : ∀ w : MulAut (adjointGroup Tag.D4 K), w * alphaOne σ = alphaOne σ * w →
      (∀ x ∈ J, w x = x) → w ∈ Subgroup.zpowers (alphaOne σ) := fun w hw hwJ =>
    mem_zpowers_of_forall_graphFixedRootGroup σ hσσσ hw fun j hj => hwJ j hj
  obtain ⟨d, T, hd0, hdf, hT, -, hσT⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_frobenius_of_cube Nat.prime_three hf K hK σ hσ3 hσ1
  have hk3 : Nat.card K = (3 ^ d) ^ 3 := by rw [hK, ← hdf, pow_mul]
  have hσ₀ : (∀ c, σ c = c ^ 3 ^ d) ∨ ∀ c, σ c = c ^ (3 ^ d) ^ 2 := by
    rcases hσT with h | h
    · exact Or.inl fun c => by rw [h]; exact hT c
    · refine Or.inr fun c => ?_
      rw [h, pow_two, RingAut.mul_apply, hT, hT, ← pow_mul, sq]
  have hLM := lieModel_graphFixedRootGroup_trialityD4_odd Nat.prime_three (by norm_num) hd0 hk3
    σ hσ₀
  have hCEM := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hLM (by decide)
  obtain ⟨hchev0, hdvd0, hL270⟩ := excModel_facts (t := .trialityD4) (by decide) (by norm_num)
    hCEM
  exact ofStabilizer_of_fix_eq Nat.prime_three hord hout hZ hfix hJN hJn hJs hncJ hsol hstab
    (isChevSimple_of_mulEquiv eJ.symm hchev0)
    (by rw [Nat.card_congr eJ.toEquiv]; exact hdvd0)
    (fun h3 hL => hL270 h3 (isLTwoTwentySeven_of_mulEquiv eJ hL))

end GraphField

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4
