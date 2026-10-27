module

public import CFSG.ClassicalInvolution.Uniform.U7Star

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement


section Section

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaGen_members_eq_range (hΩ : HypOmegaModU (.sl2 3 1) Ω) (C : G2Comp Ω)
    {R : Subgroup G2Model} (hR : R ∈ G2Fund) (hRΩ : R.map C.ψ ∈ Ω) :
    omegaGen C.members = C.ψ.range := by
  have hsimple : IsSimpleGroup G2Model :=
    isSimpleGroup_model_of_g2d4 (p := 3) (e := 1) (by norm_num) g2Adm3 (Or.inl rfl)
  apply le_antisymm
  · refine iSup₂_le fun M hM => ?_
    obtain ⟨-, R', -, rfl⟩ := hM
    exact Subgroup.map_le_range _ _
  · obtain ⟨z, hz⟩ := hΩ.classical _ hRΩ
    have hRne : R ≠ ⊥ := fun h => hz.ne_one (by
      have := hz.mem
      rwa [h, Subgroup.map_bot, Subgroup.mem_bot] at this)
    have hN : Subgroup.normalClosure (R : Set G2Model) = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.normalClosure (R : Set G2Model)) with h | h
      · exact absurd (eq_bot_iff.mpr (fun x hx => by
          have := Subgroup.subset_normalClosure hx
          rwa [h] at this)) hRne
      · exact h
    have hle : Subgroup.normalClosure (R : Set G2Model) ≤ (omegaGen C.members).comap C.ψ := by
      show Subgroup.closure (Group.conjugatesOfSet (R : Set G2Model)) ≤ _
      rw [Subgroup.closure_le]
      intro y hy
      obtain ⟨a, haR, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
      obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
      have hmem : (conjSub c R).map C.ψ ∈ C.members := by
        refine ⟨?_, conjSub c R, RouteD.conjSub_mem_fundamentalSubgroups hR c, rfl⟩
        rw [AscQuot.map_conjSub]
        exact hΩ.conjInvariant _ _ hRΩ
      exact le_omegaGen hmem (Subgroup.mem_map_of_mem _ (conj_mem_conjSub haR))
    rintro _ ⟨k, rfl⟩
    exact hle (hN ▸ Subgroup.mem_top k)

omit [Finite G] in
theorem subgroupOf_range_map' {M : Type} [Group M] (ψ : M →* G) (R : Subgroup M) :
    (R.map ψ).subgroupOf ψ.range = R.map ψ.rangeRestrict := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨r, hr, hrx⟩
    exact ⟨r, hr, Subtype.ext hrx⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, rfl⟩

@[expose] noncomputable def sectionLieDataU3 (C : G2Comp Ω)
    (hO : classicalInvolutionOddCore ↥C.ψ.range = ⊥)
    (hfund : ∀ L ∈ Ω, L ≤ C.ψ.range → ∃ R ∈ G2Fund, L = R.map C.ψ)
    (hmeet : ∃ R ∈ G2Fund, R.map C.ψ ∈ Ω) (hcard : ∀ L ∈ Ω, Nat.card L = 24) :
    LieSystemDataU 3 1 (Fin 1) (↥C.ψ.range ⧸ classicalInvolutionOddCore ↥C.ψ.range)
      (oddQuotientFamily (restrictFamily Ω C.ψ.range)) where
  kind := fun _ => compModel 3 1 .G2 0
  valid := fun _ => Or.inl ⟨.G2, 0, 1, trivial, g2Adm3, Or.inl rfl, rfl⟩
  hom := fun _ => (QuotientGroup.mk' (classicalInvolutionOddCore ↥C.ψ.range)).comp
    C.ψ.rangeRestrict
  ker_le_center := by
    intro _ x hx
    have h1 : C.ψ.rangeRestrict x ∈ classicalInvolutionOddCore ↥C.ψ.range :=
      (QuotientGroup.eq_one_iff _).mp hx
    rw [hO, Subgroup.mem_bot] at h1
    have h2 : C.ψ x = 1 := congrArg Subtype.val h1
    have : x = 1 := C.inj (h2.trans (map_one _).symm)
    rw [this]
    exact Subgroup.one_mem _
  commute := fun a b hab => absurd (Subsingleton.elim a b) hab
  generate := by
    rw [iSup_const, eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨x, hx⟩ := y.2
    have hxy : C.ψ.rangeRestrict x = y := Subtype.ext hx
    exact ⟨x, by show QuotientGroup.mk' _ (C.ψ.rangeRestrict x) = _; rw [hxy]⟩
  fundamental := by
    rintro _ ⟨_, ⟨L₀, hL₀, hL₀Y, rfl⟩, rfl⟩
    obtain ⟨R, hR, rfl⟩ := hfund L₀ hL₀ hL₀Y
    refine ⟨0, R, hR, ?_⟩
    show ((R.map C.ψ).subgroupOf C.ψ.range).map _ = R.map _
    rw [subgroupOf_range_map', Subgroup.map_map]
  meets := by
    obtain ⟨R, hR, hRΩ⟩ := hmeet
    refine fun _ => ⟨R, hR, ⟨(R.map C.ψ).subgroupOf C.ψ.range,
      ⟨R.map C.ψ, hRΩ, Subgroup.map_le_range _ _, rfl⟩, ?_⟩⟩
    show ((R.map C.ψ).subgroupOf C.ψ.range).map _ = R.map _
    rw [subgroupOf_range_map', Subgroup.map_map]
  card_eq := by
    intro _ L hL
    obtain ⟨_, ⟨L₀, hL₀, hL₀Y, rfl⟩, rfl⟩ := hL
    have hinj : Function.Injective
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥C.ψ.range)) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO]
    rw [Subgroup.card_map_of_injective hinj]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₀Y).toEquiv).trans (hcard L₀ hL₀)

variable {z j a : G}

theorem sectionLieTypeU_of_violation (hgen : G2NonToralGenerate3)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hcard : ∀ L ∈ Ω, Nat.card L = 24) (C : G2Comp Ω)
    {R S : Subgroup G2Model} (hR : R ∈ G2Fund) (hRΩ : R.map C.ψ ∈ Ω)
    (hQ : QuotViol Ω (R.map C.ψ) (S.map C.ψ) z j a)
    (hJ : S.map C.ψ ∈ aStar Ω (R.map C.ψ)) :
    SectionLieTypeU 3 1 Ω (omegaGen (aStar Ω (R.map C.ψ))) .G2 0 := by
  have hY : omegaGen (aStar Ω (R.map C.ψ)) = C.ψ.range := by
    rw [aStar_eq_members hgen hΩ C hR hRΩ hQ hJ]
    exact omegaGen_members_eq_range hΩ C hR hRΩ
  rw [hY]
  have hsimple : IsSimpleGroup ↥C.ψ.range :=
    haveI : IsSimpleGroup G2Model :=
      isSimpleGroup_model_of_g2d4 (p := 3) (e := 1) (by norm_num) g2Adm3 (Or.inl rfl)
    MulEquiv.isSimpleGroup (MonoidHom.ofInjective C.inj).symm
  have hO : classicalInvolutionOddCore ↥C.ψ.range = ⊥ := by
    have hz := hQ.hz
    have := hsimple
    exact ih8_oddCore_eq_bot_of_simple (G := ↥C.ψ.range)
      (z := ⟨z, Subgroup.map_le_range _ _ hz.mem⟩) (by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one)
  have hfund : ∀ L ∈ Ω, L ≤ C.ψ.range → ∃ R' ∈ G2Fund, L = R'.map C.ψ := by
    intro L hL hLY
    rcases C.cover L hL with h | hc
    · exact h
    · exfalso
      obtain ⟨zz, hzz⟩ := hΩ.classical L hL
      obtain ⟨x, hx, y, hy, hxy⟩ := hzz.exists_noncomm
      exact hxy (hc x hx y (hLY hy))
  exact ⟨sectionLieDataU3 C hO hfund ⟨R, hR, hRΩ⟩ hcard, 1, Or.inl rfl, trivial, g2Adm3, rfl⟩

theorem thm3Lie_of_violation (hgen : G2NonToralGenerate3) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (D : OmegaLieU 3 1 Ω) {K : Subgroup G} (hK : K ∈ Ω) (hnA : ¬ AEmpty Ω K) :
    SectionLieTypeU 3 1 Ω (omegaGen (aStar Ω K)) .G2 0 := by
  obtain ⟨C, R, S, J, zK, zJ, a, hR, hS, rfl, rfl, hv, hQ⟩ := exists_g2Comp hΩ D hK hnA
  have hJ : S.map C.ψ ∈ aStar Ω (R.map C.ψ) :=
    Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨zK, zJ, hv⟩⟩
  exact sectionLieTypeU_of_violation hgen hΩ (D.card_eq (by norm_num)) C hR hK hQ hJ

theorem thm3LieBelowExactU_three (hgen : G2NonToralGenerate3) {n : ℕ}
    (hn : CITBelowT (.sl2 3 1) n) : Thm3LieBelowExactU 3 1 n := by
  intro _ _ G _ _ hlt hO Ω hΩ K hK hnA
  obtain ⟨D⟩ := exists_omegaLieU hn hΩ ⟨K, hK⟩ hO hlt
  exact thm3Lie_of_violation hgen hΩ D hK hnA

end Section

end CFSG.ClassicalInvolution.Uniform
