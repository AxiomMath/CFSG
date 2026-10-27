module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Goldschmidt.Steps.G3aGlue
public import CFSG.Goldschmidt75.B1Comp2
public import CFSG.Goldschmidt75.OddCore
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt CFSG.Walter Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_coreHyp (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ T) (hAab : IsMulCommutative A)
    (hA : fusionStronglyClosed (A : Set G) T) (hO : goldschmidtOddCore G = ⊥) :
    ∃ TM : Sylow 2 (normalClosure (A : Set G)),
      (TM : Subgroup _).map (normalClosure (A : Set G)).subtype =
        (T : Subgroup G) ⊓ normalClosure (A : Set G) ∧
      CoreHyp (normalClosure (A : Set G)) TM (A.subgroupOf (normalClosure (A : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := normalClosure (A : Set G) with hM
  have : M.Normal := normalClosure_normal
  have hTG : fusionIsSylowIn 2 (T : Subgroup G) ⊤ :=
    ⟨le_top, T.isPGroup', fun _ _ hP hTP => T.is_maximal' hP hTP⟩
  obtain ⟨TM, hTM⟩ := G310.exists_sylow_of_fusionIsSylowIn
    (G3a.fusionIsSylowIn_inf hTG le_top (Subgroup.normal_subgroupOf (N := M) (H := ⊤)).isSubnormal)
  have hmem : ∀ x : M, x ∈ (TM : Subgroup M) ↔ (x : G) ∈ (T : Subgroup G) := by
    intro x
    constructor
    · intro hx
      have : (x : G) ∈ (TM : Subgroup M).map M.subtype := ⟨x, hx, rfl⟩
      rw [hTM] at this
      exact (mem_inf.mp this).1
    · intro hx
      have : (x : G) ∈ (T : Subgroup G) ⊓ M := mem_inf.mpr ⟨hx, x.2⟩
      rw [← hTM] at this
      obtain ⟨y, hy, hyx⟩ := this
      rwa [show x = y from Subtype.ext hyx.symm]
  refine ⟨TM, hTM, ⟨?_, isMulCommutative_subgroupOf hAab M, ?_,
    normalClosure_subgroupOf_eq_top T hAT hA rfl, oddCore_eq_bot_of_normal hO⟩⟩
  · intro x hx
    rw [hmem]
    exact hAT (mem_subgroupOf.mp hx)
  · intro a ha g hg
    rw [hmem] at hg
    have h1 := hA (a : G) (mem_subgroupOf.mp ha) (g : G) (by simpa using hg)
    exact mem_subgroupOf.mpr (by simpa using h1)

variable {M : Subgroup G} {A : Subgroup G} {TM : Sylow 2 M}

theorem comp_data
    (hcore : CoreHyp M TM (A.subgroupOf M)) {K : Subgroup M}
    (hK : IsComponentOf K ⊤) :
    (IsGoldTypeI K ∨ IsGoldTypeII K) ∧ InducesOmega1 (A.subgroupOf M) K TM ∧
      ∀ a ∈ A.subgroupOf M, ∃ x ∈ A.subgroupOf M ⊓ K, ∀ y ∈ K, a⁻¹ * y * a = x⁻¹ * y * x := by
  obtain ⟨htype, hind⟩ := N21_of N19 _ (ih_all _) M TM _ hcore K hK (Nat.lt_succ_self _)
  have hcov := N17_of N11b M TM _ K hcore.le hcore.comm hcore.closed hcore.oddCore hK htype hind
  exact ⟨G41.isGoldType_of_component TM hcore.comm hK htype hind hcov, hind, hcov⟩

theorem comp_quasi_type
    (hcore : CoreHyp M TM (A.subgroupOf M)) {K : Subgroup M}
    (hK : IsComponentOf K ⊤) :
    CFSG.Open.IsQuasisimple (K.map M.subtype) ∧
      (IsGoldTypeI (K.map M.subtype) ∨ IsGoldTypeII (K.map M.subtype)) := by
  let e : K ≃* K.map M.subtype := K.equivMapOfInjective M.subtype M.subtype_injective
  refine ⟨CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm hK.2.2, ?_⟩
  rcases (comp_data hcore hK).1 with hI | hII
  · exact Or.inl (SStarTransport.isGoldTypeI_of_mulEquiv e hI)
  · exact Or.inr (SStarTransport.isGoldTypeII_of_mulEquiv e hII)

omit [Finite G] in
theorem center_map_eq_bot {M : Subgroup G} {K : Subgroup M} (hZ : Subgroup.center K = ⊥) :
    Subgroup.center (K.map M.subtype) = ⊥ := by
  let e : K ≃* K.map M.subtype := K.equivMapOfInjective M.subtype M.subtype_injective
  rw [← Subgroup.map_center_eq e, hZ, Subgroup.map_bot]

theorem center_comp_eq_bot
    (hcore : CoreHyp M TM (A.subgroupOf M))
    (hZ : CFSG.Open.pCore 2 M = ⊥) {K : Subgroup M} (hK : IsComponentOf K ⊤) :
    Subgroup.center K = ⊥ := by
  have hZp : IsPGroup 2 (Subgroup.center K) := (N8d M hcore.oddCore).1 K hK
  obtain ⟨h1, -, -⟩ := coreStatement M TM _ hcore.le hcore.comm hcore.closed hcore.gen
    hcore.oddCore
  rw [hZ, bot_sup_eq] at h1
  set Zc := (Subgroup.center K).map K.subtype with hZc
  have hZcent : Zc ≤ Subgroup.center M := by
    rintro _ ⟨z, hz, rfl⟩
    have hle : goldschmidtLayer M ≤ centralizer ({(z : M)} : Set M) := by
      refine sSup_le fun K' hK' => ?_
      by_cases hKK : K' = K
      · subst hKK
        intro y hy
        rw [mem_centralizer_singleton_iff]
        exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩))
      · have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne K K' hK hK'
          (Ne.symm hKK)
        intro y hy
        rw [mem_centralizer_singleton_iff]
        have := commutator_mem_commutator z.2 hy
        rw [hc, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this.symm
    rw [h1] at hle
    rw [mem_center_iff]
    intro g
    exact mem_centralizer_singleton_iff.mp (hle (mem_top g))
  have hZcp : IsPGroup 2 Zc := hZp.map _
  have hZcn : Zc.Normal := normal_of_le_center hZcent
  have hle : Zc ≤ CFSG.Open.pCore 2 M :=
    le_sSup ⟨hZcn, hZcp⟩
  rw [hZ, le_bot_iff, hZc] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hle

end CFSG.Goldschmidt75
