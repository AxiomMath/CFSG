module

public import CFSG.ClassicalInvolution.Asc77.AscC25V16
public import CFSG.ClassicalInvolution.AschTight.S1911P3e
public import CFSG.ClassicalInvolution.AschTight.S19MCenter
public import CFSG.ClassicalInvolution.AschTight.S19MFactM0

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section SecAct

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}


theorem fs_exists_conj_comm_of_secAct (hI : IsUniqueInvolution K z) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
    {s : ↥(Subgroup.centralizer ({a} : Set G))} (hs2 : s * s = 1)
    {c : ↥(Subgroup.centralizer ({a} : Set G))}
    (hc : (secImg (conjGen (perfectCoreIn K a)) (conjSub c (perfectCoreIn K a))).map
      (@secAct _ _ (conjGen (perfectCoreIn K a)) (conjGen_normal _) s).toMonoidHom =
        secImg (conjGen (perfectCoreIn K a)) (conjSub c (perfectCoreIn K a))) :
    ∃ v ∈ oddCoreOf (conjGen (perfectCoreIn K a)),
      (v * c)⁻¹ * s * (v * c) * ⟨z, hzA⟩ = ⟨z, hzA⟩ * ((v * c)⁻¹ * s * (v * c)) := by
  have := conjGen_normal (perfectCoreIn K a)
  have hu := fs_isUniqueInvolution_secImg hI hzA hzKa c
  set φ := @secAct _ _ (conjGen (perfectCoreIn K a)) (conjGen_normal _) s with hφ
  set ū := QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K a)))
    ⟨c * ⟨z, hzA⟩ * c⁻¹, le_conjGen ⟨c, rfl⟩
      (fs_isUniqueInvolution_conjSub hI hzA hzKa c).mem⟩ with hū
  have hφu : φ ū = ū := by
    have hmem : φ ū ∈ secImg (conjGen (perfectCoreIn K a)) (conjSub c (perfectCoreIn K a)) := by
      rw [← hc]
      exact ⟨ū, hu.mem, rfl⟩
    have hsq : φ ū * φ ū = 1 := by rw [← map_mul, hu.sq, map_one]
    have hne : φ ū ≠ 1 := fun h => hu.ne_one (φ.injective (h.trans (map_one φ).symm))
    exact (hu.unique _ hmem hsq).resolve_left hne
  have hO := mem_oddCoreOf_of_secAct _ hφu
  have hu2 : c * ⟨z, hzA⟩ * c⁻¹ * (c * ⟨z, hzA⟩ * c⁻¹) = 1 :=
    (fs_isUniqueInvolution_conjSub hI hzA hzKa c).sq
  obtain ⟨v, hvO, hv⟩ := exists_conj_commute_of_odd (oddCoreOf_odd_natCard _) hs2 hu2
    (mem_normalizer_oddCoreOf_conjGen _ s) (mem_normalizer_oddCoreOf_conjGen _ _) hO
  refine ⟨v, hvO, ?_⟩
  calc (v * c)⁻¹ * s * (v * c) * ⟨z, hzA⟩
      = (v * c)⁻¹ * (s * (v * (c * ⟨z, hzA⟩ * c⁻¹) * v⁻¹)) * (v * c) := by group
    _ = (v * c)⁻¹ * ((v * (c * ⟨z, hzA⟩ * c⁻¹) * v⁻¹) * s) * (v * c) := by rw [hv]
    _ = ⟨z, hzA⟩ * ((v * c)⁻¹ * s * (v * c)) := by group

end SecAct

section Typed

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem fs_exists_member_normalized
    (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (h9 : p ^ f ≠ 9)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF : IsFAut R' a)
    (hnoswap : ¬ ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K' = K)
    {s : ↥(Subgroup.centralizer ({a} : Set G))} (hs2 : s * s = 1) :
    ∃ (_ : z ∈ Subgroup.centralizer ({a} : Set G)),
      z ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G)) ∧
      ∃ c : ↥(Subgroup.centralizer ({a} : Set G)),
        (secImg (conjGen (perfectCoreIn K' a)) (conjSub c (perfectCoreIn K' a))).map
          (@secAct _ _ (conjGen (perfectCoreIn K' a)) (conjGen_normal _) s).toMonoidHom =
          secImg (conjGen (perfectCoreIn K' a)) (conjSub c (perfectCoreIn K' a)) := by
  classical
  obtain ⟨e₀, hfe, h5, hzA, hmem, hlt, hIH⟩ := mixed_section_data h h9 haS ha2 hF
  have hp2 : p ≠ 2 := h.hp
  have d' := twinCtx'_of_hyp25 h
  have hzKa : z ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hmem.mem
  refine ⟨hzA, hzKa, ?_⟩
  have := conjGen_normal (perfectCoreIn K' a)
  have hΩ₀ := fs_hypOmegaMod_conjFamily h.hΩ h.hK' h.hz' hzA hmem
  have hDE : Disconnected.DEdgeless (conjFamily (perfectCoreIn K' a)) :=
    (fs_dEdgeless_iff d' h5 hzA hmem).mpr hnoswap
  have hne : (conjFamily (perfectCoreIn K' a)).Nonempty := ⟨_, ⟨1, conjSub_one _⟩⟩
  by_cases hTop : (⊤ : Subgroup (↥(conjGen (perfectCoreIn K' a)) ⧸
      classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a)))) ∈
      oddQuotientFamily (restrictFamily (conjFamily (perfectCoreIn K' a))
        (conjGen (perfectCoreIn K' a)))
  · obtain ⟨c, hc⟩ := (mem_secFamily_iff _ _).mp hTop
    refine ⟨c, ?_⟩
    rw [← hc]
    exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)
  · have hsec := sectionThm6 hp2 h5 (ih8SmallEdge p) hIH hlt hΩ₀ hne hDE hTop
    obtain ⟨tg, k, htag, hsecT⟩ : ∃ tg k, IsT6Tag tg k ∧
        SectionLieType p e₀ (conjFamily (perfectCoreIn K' a)) (conjGen (perfectCoreIn K' a))
          tg k := by
      rcases hsec with h1 | h1 | h1 | h1
      · exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, h1⟩
      · exact ⟨_, _, Or.inr (Or.inl ⟨rfl, rfl⟩), h1⟩
      · exact ⟨_, _, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), h1⟩
      · exact ⟨_, _, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), h1⟩
    obtain ⟨D, hcard, i, hti, hki⟩ := hsecT
    have htag' : IsT6Tag (D.tag i) (D.rank i) := by rw [hti, hki]; exact htag
    have hconj := conjInvariant_oddQuotientFamily
      (inClass_restrict_conjugates hmem).conjInvariant
    have hO := CFSG.ComponentClassification.OddCore.quotient_corefree
      ↥(conjGen (perfectCoreIn K' a))
    have hu1 := fs_isUniqueInvolution_secImg d'.hI hzA hzKa 1
    have : Nontrivial (↥(conjGen (perfectCoreIn K' a)) ⧸
        classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a))) := ⟨⟨_, 1, hu1.ne_one⟩⟩
    have hsimple := isSimpleGroup_of_lieSystemData S19M.factM3 hp2 D hcard i htag' hO
    have M := ih8Model_of_lieSystemData D hcard i hconj
    have hΦne : (oddQuotientFamily (restrictFamily (conjFamily (perfectCoreIn K' a))
        (conjGen (perfectCoreIn K' a)))).Nonempty :=
      ⟨_, (mem_secFamily_iff _ _).mpr ⟨1, rfl⟩⟩
    have hDEΦ := (section_facts hp2 h5 hΩ₀ hne hDE).2.2.2.1
    obtain ⟨X, hX, hXφ⟩ := S19M.factM0' p e₀ hp2 h5 _ _ _ _ _ htag' ⟨M⟩ hΦne hDEΦ
      (secAct (conjGen (perfectCoreIn K' a)) s) (by rw [← map_mul, hs2, map_one])
      (secAct_preserves _ s)
    obtain ⟨c, rfl⟩ := (mem_secFamily_iff _ X).mp hX
    exact ⟨c, hXφ⟩

theorem fs_exists_conj_comm
    (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (h9 : p ^ f ≠ 9)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF : IsFAut R' a)
    (hnoswap : ¬ ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K' = K)
    {b g : G} (hbg : b = g * z * g⁻¹) (hba : b * a = a * b) :
    ∃ d : G, d * a = a * d ∧ (d⁻¹ * b * d) * z = z * (d⁻¹ * b * d) := by
  have d' := twinCtx'_of_hyp25 h
  have hbA : b ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hba
  have hb2 : b * b = 1 := by
    rw [hbg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.hz'.sq]; group
  have hs2 : (⟨b, hbA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) *
      ⟨b, hbA⟩ = 1 := Subtype.ext hb2
  obtain ⟨hzA, hzKa, c, hc⟩ := fs_exists_member_normalized h h9 haS ha2 hF hnoswap hs2
  obtain ⟨v, -, hv⟩ := fs_exists_conj_comm_of_secAct d'.hI hzA hzKa hs2 hc
  refine ⟨((v * c : ↥(Subgroup.centralizer ({a} : Set G))) : G), ?_, ?_⟩
  · have := (v * c).2
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  · have h1 := congrArg Subtype.val hv
    simpa using h1

end Typed

end CFSG.ClassicalInvolution.Asc77.C25V
