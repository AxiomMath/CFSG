module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactComm

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models
open scoped commutatorElement

section Model

variable {p : ℕ} [Fact p.Prime]

theorem isSimpleGroup_model_of_g2d4 (hp : p ≠ 2) {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n e : ℕ} (hadm : StatedLieAdmissible t n p e) (ht : t = .G2 ∨ t = .trialityD4) :
    IsSimpleGroup (modelUniv t n p e Fact.out).K := by
  have hfund : Generic.IsFundTag t := by rcases ht with rfl | rfl <;> trivial
  obtain ⟨-, hs⟩ := ModelFacts.isQuasisimple_modelUniv t n p e Fact.out
    (ih8_isFundTag_mf hfund) hadm
  have hbot := RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp ht n hadm.2.1
  have e' : ((modelUniv t n p e Fact.out).K ⧸ Subgroup.center (modelUniv t n p e Fact.out).K) ≃*
      (modelUniv t n p e Fact.out).K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact @MulEquiv.isSimpleGroup _ _ _ _ hs e'.symm

end Model

section Gen

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}

omit [Finite X] in
theorem omegaGen_compMembers_eq_range (hp : p ≠ 2) (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ)
    {i : Fin D.card} (hi : D.tag i = .G2 ∨ D.tag i = .trialityD4) {R : Subgroup (D.model i).K}
    (hR : R ∈ D.cls i) : omegaGen (compMembers D i) = (D.hom i).range := by
  apply le_antisymm
  · refine iSup₂_le fun M hM => ?_
    obtain ⟨R', -, rfl⟩ := hM
    exact Subgroup.map_le_range _ _
  · have : IsSimpleGroup (D.model i).K := isSimpleGroup_model_of_g2d4 hp (D.admissible i) hi
    obtain ⟨z, hz⟩ := hΦ.classical _ hR.2
    have hRne : R ≠ ⊥ := fun h => ih8_member_ne_bot hz (by rw [h, Subgroup.map_bot])
    have hN : Subgroup.normalClosure (R : Set (D.model i).K) = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.normalClosure (R : Set (D.model i).K)) with h | h
      · exact absurd (eq_bot_iff.mpr (fun x hx => by
          have := Subgroup.subset_normalClosure hx
          rwa [h] at this)) hRne
      · exact h
    have hle : Subgroup.normalClosure (R : Set (D.model i).K) ≤
        (omegaGen (compMembers D i)).comap (D.hom i) := by
      show Subgroup.closure (Group.conjugatesOfSet (R : Set (D.model i).K)) ≤ _
      rw [Subgroup.closure_le]
      intro y hy
      obtain ⟨a, haR, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
      obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
      have hmem : conjSub c R ∈ D.cls i := D.cls_conj hΦ.conjInvariant i hR c
      exact le_omegaGen (⟨conjSub c R, hmem, rfl⟩ : (conjSub c R).map (D.hom i) ∈ compMembers D i)
        (Subgroup.mem_map_of_mem _ (conj_mem_conjSub haR))
    rintro _ ⟨k, rfl⟩
    exact hle (hN ▸ Subgroup.mem_top k)

end Gen

section Section

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}

omit [Finite X] in
theorem subgroupOf_range_map {M : Type} [Group M] (ψ : M →* X) (R : Subgroup M) :
    (R.map ψ).subgroupOf ψ.range = R.map ψ.rangeRestrict := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨r, hr, hrx⟩
    exact ⟨r, hr, Subtype.ext hrx⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, rfl⟩

@[expose] noncomputable def sectionLieData (D : OmegaLie p f Φ) (i : Fin D.card)
    (hO : classicalInvolutionOddCore ↥(D.hom i).range = ⊥) (hinj : Function.Injective (D.hom i))
    (hfund : ∀ L ∈ Φ, L ≤ (D.hom i).range → ∃ R ∈ fundamentalSubgroups (D.tag i) (D.model i).D,
      L = R.map (D.hom i))
    (hmeet : ∃ R ∈ fundamentalSubgroups (D.tag i) (D.model i).D, R.map (D.hom i) ∈ Φ) :
    LieSystemData p f (↥(D.hom i).range ⧸ classicalInvolutionOddCore ↥(D.hom i).range)
      (oddQuotientFamily (restrictFamily Φ (D.hom i).range)) where
  card := 1
  tag := fun _ => D.tag i
  rank := fun _ => D.rank i
  exp := fun _ => D.exp i
  hom := fun _ => (QuotientGroup.mk' (classicalInvolutionOddCore ↥(D.hom i).range)).comp
    (D.hom i).rangeRestrict
  isFundTag := fun _ => D.isFundTag i
  admissible := fun _ => D.admissible i
  exp_eq := fun _ => D.exp_eq i
  ker_le_center := by
    intro _ x hx
    have h1 : (D.hom i).rangeRestrict x ∈ classicalInvolutionOddCore ↥(D.hom i).range :=
      (QuotientGroup.eq_one_iff _).mp hx
    rw [hO, Subgroup.mem_bot] at h1
    have h2 : D.hom i x = 1 := congrArg Subtype.val h1
    have : x = 1 := hinj (h2.trans (map_one _).symm)
    rw [this]
    exact Subgroup.one_mem _
  commute := fun a b hab => absurd (Subsingleton.elim a b) hab
  generate := by
    rw [iSup_const, eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨x, hx⟩ := y.2
    have hxy : (D.hom i).rangeRestrict x = y := Subtype.ext hx
    exact ⟨x, by show QuotientGroup.mk' _ ((D.hom i).rangeRestrict x) = _; rw [hxy]⟩
  fundamental := by
    rintro _ ⟨_, ⟨L₀, hL₀, hL₀Y, rfl⟩, rfl⟩
    obtain ⟨R, hR, rfl⟩ := hfund L₀ hL₀ hL₀Y
    refine ⟨0, R, hR, ?_⟩
    show ((R.map (D.hom i)).subgroupOf (D.hom i).range).map _ = R.map _
    rw [subgroupOf_range_map, Subgroup.map_map]
  meets := by
    obtain ⟨R, hR, hRΦ⟩ := hmeet
    refine fun _ => ⟨R, hR, ⟨(R.map (D.hom i)).subgroupOf (D.hom i).range,
      ⟨R.map (D.hom i), hRΦ, Subgroup.map_le_range _ _, rfl⟩, ?_⟩⟩
    show ((R.map (D.hom i)).subgroupOf (D.hom i).range).map _ = R.map _
    rw [subgroupOf_range_map, Subgroup.map_map]

variable (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ)
  {i : Fin D.card}

include hp hq hΦ

theorem sectionLieType_of_violation (hgen : G2CentralizersGenerate p) (hG2 : D.tag i = .G2)
    {R S : Subgroup (D.model i).K} (hR : R ∈ D.cls i) {z j a : X}
    (hQ : QuotViol Φ (R.map (D.hom i)) (S.map (D.hom i)) z j a)
    (hJ : S.map (D.hom i) ∈ aStar Φ (R.map (D.hom i))) :
    SectionLieType p f Φ (omegaGen (aStar Φ (R.map (D.hom i)))) .G2 0 := by
  have hi : D.tag i = .G2 ∨ D.tag i = .trialityD4 := Or.inl hG2
  have hY : omegaGen (aStar Φ (R.map (D.hom i))) = (D.hom i).range := by
    rw [aStar_eq_compMembers hgen hp hq hΦ D hG2 hR hQ hJ]
    exact omegaGen_compMembers_eq_range hp hΦ D hi hR
  rw [hY]
  have hinj := hom_injective_of_g2d4 hp D hi
  have hsimple : IsSimpleGroup ↥(D.hom i).range :=
    haveI := isSimpleGroup_model_of_g2d4 hp (D.admissible i) hi
    MulEquiv.isSimpleGroup (MonoidHom.ofInjective hinj).symm
  have hO : classicalInvolutionOddCore ↥(D.hom i).range = ⊥ := by
    have hz := hQ.hz
    have := hsimple
    exact ih8_oddCore_eq_bot_of_simple (G := ↥(D.hom i).range)
      (z := ⟨z, Subgroup.map_le_range _ _ hz.mem⟩) (by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one)
  have hfund : ∀ L ∈ Φ, L ≤ (D.hom i).range →
      ∃ R' ∈ fundamentalSubgroups (D.tag i) (D.model i).D, L = R'.map (D.hom i) := by
    intro L hL hLY
    obtain ⟨j, R', hR', hLR'⟩ := D.fundamental L hL
    by_cases hji : j = i
    · subst hji
      exact ⟨R', hR', hLR'⟩
    · exfalso
      obtain ⟨zz, hzz⟩ := hΦ.classical L hL
      obtain ⟨x, hx, y, hy, hxy⟩ := ih8_exists_noncomm hzz
      have hxj : x ∈ D.comp j := by
        rw [hLR'] at hx
        exact Subgroup.map_le_range _ _ hx
      exact hxy (D.comp_commute (Ne.symm hji) y (hLY hy) x hxj).symm
  have hadm := D.admissible i
  rw [hG2] at hadm
  obtain ⟨hk, -⟩ := hadm.2.2
  exact ⟨sectionLieData D i hO hinj hfund ⟨R, hR.1, hR.2⟩, rfl, ⟨⟨0, Nat.one_pos⟩, hG2, hk⟩⟩

end Section

section Lie

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}

theorem thm3Lie_of_violation (hgen : G2CentralizersGenerate p) (hD4 : D4NormalizerMax p)
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ)
    {K : Subgroup X} (hK : K ∈ Φ) (hnA : ¬ AEmpty Φ K) :
    SectionLieType p f Φ (omegaGen (aStar Φ K)) .G2 0 := by
  obtain ⟨i, R, S, J, zK, zJ, a, hG2, hR, hS, rfl, rfl, hv, hQ⟩ :=
    exists_component_of_not_aEmpty hD4 hp hq hΦ D hK hnA
  have hJ : S.map (D.hom i) ∈ aStar Φ (R.map (D.hom i)) :=
    Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨zK, zJ, hv⟩⟩
  exact sectionLieType_of_violation hp hq hΦ D hgen hG2 hR hQ hJ

theorem thm3LieBelowExact_of_citBelowU (hgen : G2CentralizersGenerate p)
    (hD4 : D4NormalizerMax p) {n : ℕ} (hn : CITBelowU p f n) : Thm3LieBelowExact p f n := by
  intro hp hq G _ _ hlt hO Ω hΩ K hK hnA
  obtain ⟨D⟩ := ih8_exists_omegaLie hn hΩ.conjInvariant hΩ.classical ⟨K, hK⟩ hO hlt
  exact thm3Lie_of_violation hgen hD4 hp hq hΩ D hK hnA

end Lie

end CFSG.ClassicalInvolution.Asc77.T3Typed
