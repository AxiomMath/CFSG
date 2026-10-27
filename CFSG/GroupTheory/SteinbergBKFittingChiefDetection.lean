module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12

public section

namespace CFSG.GroupTheory.SteinbergBK

variable {G : Type*} [Group G]

@[expose] def fittingChiefDetection (K : Subgroup G) : Set G :=
  {g | g ∈ K ∧ ∀ X Y : Subgroup G, X.Normal → Y.Normal → Y < X →
    X ≤ (fittingSubgroup K).map K.subtype → (∀ Z : Subgroup G, Z.Normal → ¬ (Y < Z ∧ Z < X)) →
      ⁅Subgroup.zpowers g, X⁆ ≤ Y}

@[expose] def chiefFactorOfPair {X Y : Subgroup G} (hX : X.Normal) (hY : Y.Normal) (hYX : Y < X)
    (hchief : ∀ Z : Subgroup G, Z.Normal → ¬ (Y < Z ∧ Z < X)) : ChiefFactor G where
  V := Y
  U := X
  isChief :=
    { normal_K := hY
      normal_H := hX
      lt := hYX
      is_maximal := fun N hN hYN hNX => by
        rcases eq_or_lt_of_le hYN with h | h
        · exact Or.inl h.symm
        rcases eq_or_lt_of_le hNX with h' | h'
        · exact Or.inr h'
        exact absurd ⟨h, h'⟩ (hchief N hN) }

theorem zpowers_commutator_le_iff (cf : ChiefFactor G) (g : G) :
    ⁅Subgroup.zpowers g, cf.U⁆ ≤ cf.V ↔ g ∈ centralizerSubgroup cf := by
  constructor
  · intro h u hu
    exact h (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers g) hu)
  · intro hg
    rw [Subgroup.commutator_le]
    intro x hx u hu
    have hle : Subgroup.zpowers g ≤ centralizerSubgroup cf :=
      (Subgroup.zpowers_le (H := centralizerSubgroup cf)).mpr hg
    exact hle hx u hu

theorem solvable_fitting_chief_factor_detection [Finite G] (hG : Group.IsSolvable G)
    (K : Subgroup G) [hKn : K.Normal] :
    ∃ D : Subgroup G, (D : Set G) = fittingChiefDetection K ∧ D.Normal ∧
      D ≤ (fittingSubgroup K).map K.subtype ∧
      ((∀ X Y : Subgroup G, X.Normal → Y.Normal → Y < X →
          X ≤ (fittingSubgroup K).map K.subtype → ∃ Z : Subgroup G, Z.Normal ∧ Y < Z ∧ Z < X) →
        fittingChiefDetection K = (K : Set G)) := by
  have := hG
  set F : Subgroup G := fittingSubgroupOf K with hFdef
  let D : Subgroup G := K ⊓ ⨅ (cf : ChiefFactor G) (_ : cf.U ≤ F), centralizerSubgroup cf
  have hmemD : ∀ g, g ∈ D ↔ g ∈ K ∧ ∀ cf : ChiefFactor G, cf.U ≤ F → g ∈ centralizerSubgroup cf :=
    fun g => by simp only [D, Subgroup.mem_inf, Subgroup.mem_iInf]
  have hCn : ∀ cf : ChiefFactor G, (centralizerSubgroup cf).Normal := fun cf => by
    have h := centralizerOfChiefFactor_normal (H := ⊤) Subgroup.normal_top cf
    rwa [centralizerOfChiefFactor, top_inf_eq] at h
  have hDn : D.Normal :=
    Subgroup.normal_inf_normal _ _ (hH := hKn) (hK := Subgroup.normal_iInf_normal fun cf =>
      Subgroup.normal_iInf_normal fun _ => hCn cf)
  have hDK : D ≤ K := inf_le_left
  have hDF : D ≤ F := by
    have hFD : fittingSubgroupOf D ≤ F :=
      le_fittingSubgroupOf_of_normal_nilpotent ((fittingSubgroupOf_le D).trans hDK)
        (fittingSubgroupOf_normal D hDn) (fittingSubgroupOf_isNilpotent D)
    have hle := normal_le_fittingSubgroupOf_of_centralizes_restricted_chiefFactors D hDn
      fun cf hcf g hg => (mem_centralizerOfChiefFactor (H := ⊤)).mpr
        ⟨Subgroup.mem_top g, ((hmemD g).mp hg).2 cf (hcf.trans hFD)⟩
    have heq : fittingSubgroupOf D = D := le_antisymm (fittingSubgroupOf_le D) hle
    have hnil : Group.IsNilpotent D := heq ▸ fittingSubgroupOf_isNilpotent D
    exact le_fittingSubgroupOf_of_normal_nilpotent hDK hDn hnil
  refine ⟨D, ?_, hDn, hDF, fun hempty => ?_⟩
  · ext g
    rw [SetLike.mem_coe, hmemD]
    constructor
    · rintro ⟨hgK, hg⟩
      refine ⟨hgK, fun X Y hX hY hYX hXF hchief => ?_⟩
      exact (zpowers_commutator_le_iff (chiefFactorOfPair hX hY hYX hchief) g).mpr
        (hg _ hXF)
    · rintro ⟨hgK, hg⟩
      refine ⟨hgK, fun cf hcf => (zpowers_commutator_le_iff cf g).mp ?_⟩
      refine hg cf.U cf.V cf.isChief.normal_H cf.isChief.normal_K cf.isChief.lt hcf
        fun Z hZ ⟨h1, h2⟩ => ?_
      rcases cf.isChief.is_maximal Z hZ h1.le h2.le with h | h
      · exact h1.ne h.symm
      · exact h2.ne h
  · ext g
    refine ⟨fun hg => hg.1, fun hg => ⟨hg, fun X Y hX hY hYX hXF hchief => ?_⟩⟩
    obtain ⟨Z, hZ, h1, h2⟩ := hempty X Y hX hY hYX hXF
    exact absurd ⟨h1, h2⟩ (hchief Z hZ)

end CFSG.GroupTheory.SteinbergBK
