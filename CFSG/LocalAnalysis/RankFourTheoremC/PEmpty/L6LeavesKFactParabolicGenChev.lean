module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenDatum
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChIJK CFSG.GroupActions Subgroup

theorem le_sup_zpowers_of_splitBN {G : Type*} [Group G] {B N U : Subgroup G} {ι : Type*}
    {n : ι → N} (h : SplitBN B N U n) : N ≤ B ⊔ ⨆ i, zpowers ((n i : N) : G) := by
  obtain ⟨hnorm, -, -, -, hclos, -⟩ := h
  haveI := hnorm
  set C := (B ⊓ N).subgroupOf N with hC
  set M : Subgroup G := B ⊔ ⨆ i, zpowers ((n i : N) : G) with hM
  set M' : Subgroup N := M.subgroupOf N with hM'
  have hker : (QuotientGroup.mk' C).ker ≤ M' := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    have hx' : (x : G) ∈ B ⊓ N := hx
    exact (le_sup_left : B ≤ M) hx'.1
  have hmap : M'.map (QuotientGroup.mk' C) = ⊤ := by
    rw [eq_top_iff, ← hclos, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨n i, ?_, rfl⟩
    show ((n i : N) : G) ∈ M
    exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem i (Subgroup.mem_zpowers _))
  have htop : M' = ⊤ := by
    rw [← Subgroup.comap_map_eq_self hker, hmap, Subgroup.comap_top]
  intro x hx
  have hx' : (⟨x, hx⟩ : N) ∈ M' := htop ▸ Subgroup.mem_top _
  exact hx'

theorem adjointGroup_isSplitBNPair
    {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (t : Tag) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) : IsSplitBNPair p (borelSub t F) (monomialSub t F) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP F p := burnsideI2BN_charP_of_card hp hf hF
  obtain ⟨hsb, hBN, -, -, -, -, -, hpg⟩ := chevalley_split_bn_pair t F
  have hfinG : Finite (adjointGroup t F) := inferInstance
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element t
  let c : ↥(adjointGroup t F) :=
    ⟨canonicalRep (coxeterSystem t) F w₀, canonicalRep_mem_adjointGroup _ F w₀⟩
  have hcN : c ∈ monomialSub t F := canonicalRep_mem_monomialSubgroup F w₀
  have hsat : (⨅ n ∈ monomialSub t F, CFSG.conjugate (borelSub t F) n) =
      borelSub t F ⊓ monomialSub t F := by
    refine burnsideI2BN_sat_of_opposite normal_borelSub_inf_monomialSub hcN ?_
    intro z hz hz'
    have hmap := (opposite_Borel_intersection t F w₀ hw₀).2.1
    have hinter := (opposite_Borel_intersection t F w₀ hw₀).2.2.1
    have hzT : (z : ModGL t F) ∈ torusGroup t F := by
      rw [← hinter]
      refine Subgroup.mem_inf.2 ⟨hz, ?_⟩
      rw [← hmap]
      refine ⟨_, hz', ?_⟩
      simp [MulAut.conj_apply, c, mul_assoc]
    have hzT' : z ∈ torusSub t F := hzT
    rw [← borelSub_inf_monomialSub] at hzT'
    exact (Subgroup.mem_inf.1 hzT').2
  have hT : ¬ p ∣ Nat.card (borelSub t F ⊓ monomialSub t F : Subgroup (adjointGroup t F)) := by
    rw [borelSub_inf_monomialSub]
    have h1 := not_dvd_card_torusGroup (τ := t) (K := F) p
    have h2 : torusGroup t F ≤ adjointGroup t F :=
      torusGroup_le_borelGroup.trans borelGroup_le_adjointGroup'
    rwa [torusSub, card_subgroupOf_of_le h2]
  exact burnsideI2BN_of_splitBN hp hsb (hpg p).2 hsat hT

theorem parFam_adjointGroup
    (t : Tag) {f : ℕ} (hf : 0 < f) (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2 ^ f) :
    ∃ Fam : ParFam ↥(adjointGroup t F) (Fin t.rank),
      Fam.Q = fun i => (parabolicRadical t F {i}).subgroupOf (adjointGroup t F) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := burnsideI2BN_charP_of_card Nat.prime_two hf hF
  have hBN := adjointGroup_isSplitBNPair Nat.prime_two hf t F hF
  obtain ⟨hsb, -, -, -, -, -, -, hpg⟩ := chevalley_split_bn_pair t F
  have hrank : 2 ≤ t.rank := by cases t <;> decide
  haveI : Nonempty (Fin t.rank) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin t.rank) := Fin.nontrivial_iff_two_le.mpr hrank
  have hne : ∀ i : Fin t.rank, ({i} : Set (Fin t.rank)) ≠ Set.univ := by
    intro i h
    obtain ⟨j, hj⟩ := exists_ne i
    have : j ∈ ({i} : Set (Fin t.rank)) := h ▸ Set.mem_univ j
    exact hj this
  have hradA : ∀ i : Fin t.rank, parabolicRadical t F {i} ≤ adjointGroup t F := fun i =>
    (parabolic_root_radical_Levi_factors t F {i}).1.trans (parabolicSubgroup_le_adjointGroup t F _)
  refine exists_parFam_of_bn_family (B := borelSub t F) (hBN.exists_sylow_normalizer Nat.prime_two)
    (fun i => ((weylRep t F i : monomialSub t F) : ↥(adjointGroup t F)))
    (fun i => (parabolicRadical t F {i}).subgroupOf (adjointGroup t F)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [eq_top_iff, ← hBN.gen]
    exact sup_le le_sup_left (le_sup_zpowers_of_splitBN hsb)
  · intro i
    exact (hpg 2).2.to_le (Subgroup.subgroupOf_mono _ (parabolicRadical_le_posUnipotent {i}))
  · intro i hbot
    have h := Subgroup.map_subgroupOf_eq_of_le (hradA i)
    rw [hbot, Subgroup.map_bot] at h
    exact parabolicRadical_ne_bot (hne i) h.symm
  · intro i
    exact (Subgroup.subgroupOf_mono _ (parabolicRadical_le_posUnipotent {i})).trans
      posUnipotentSub_le_borelSub
  · intro i x hx
    have hx' : (x : ModGL t F) ∈ borelGroup t F := hx
    have h1 : (x : ModGL t F) ∈ normalizer (parabolicRadical t F {i} : Set (ModGL t F)) :=
      borelGroup_le_normalizer_parabolicRadical {i} hx'
    exact mem_normalizer_subgroupOf (hradA i) x.2 h1
  · intro i
    have h1 : weylElt t F i 1 ∈ normalizer (parabolicRadical t F {i} : Set (ModGL t F)) :=
      weylElt_mem_normalizer_parabolicRadical (Set.mem_singleton i)
    exact mem_normalizer_subgroupOf (hradA i) (weylElt_mem_adjointGroup i 1) h1

theorem parGen_adjointGroup
    (t : Tag) {f : ℕ} (hf : 0 < f) (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2 ^ f) :
    HasParGen ↥(adjointGroup t F) :=
  (parFam_adjointGroup t hf F hF).choose.hasParGen

theorem hasParGen_of_untwistedChevalleyModel
    {G : Type} [Group G] [Finite G] {τ : Tag} {f : ℕ} (hf : 0 < f)
    (h : UntwistedChevalleyModel G τ (2 ^ f)) : HasParGen G := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hpg := parGen_adjointGroup τ hf K hK
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  let eA : ↥(adjointGroup τ K) ≃* AdjointQuotient τ K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact hasParGen_of_mulEquiv (eA.trans e.symm) hpg

theorem hasParGen_of_chevalleyExceptionalModel_untwisted
    {G : Type} [Group G] [Finite G] {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {f : ℕ}
    (h : ChevalleyExceptionalModel G t 2 f) (ht : t ≠ .twistedE6) (ht' : t ≠ .trialityD4) :
    HasParGen G := by
  obtain ⟨hadm, hmodel⟩ := h
  have hf : 0 < f := hadm.2.1
  cases t
  all_goals first
    | exact hasParGen_of_untwistedChevalleyModel hf hmodel
    | exact absurd rfl ht
    | exact absurd rfl ht'
    | exact hmodel.elim

end KPGen

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
