module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.SignalizerFunctorTheorem.Inheritance.Sections
import CFSG.LocalAnalysis.ComponentClassification.SmallLocalSimpleFitting
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open CFSG.SignalizerFunctorTheorem (IsSectionOf)

@[expose] def UGTAt (G : Type) [Group G] [Finite G] [IsSimpleGroup G] : Prop :=
  (∃ a b : G, a * b ≠ b * a) → CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ z : G, orderOf z = 2 → CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ →
      CFSG.Blueprint.OddLieType G ∨
        ∃ n : ℕ, 7 ≤ n ∧ n % 4 = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin n))

@[expose] def UHered (H : Type) [Group H] : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], IsSectionOf S H → UGTAt S

theorem UHered.of_section {X Y : Type} [Group X] [Group Y] (h : UHered Y)
    (hX : IsSectionOf X Y) : UHered X :=
  fun S _ _ _ hS => h S (hS.trans hX)

theorem UGTAt.of_balanced {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hcore : ∀ t : G, orderOf t = 2 →
      CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥) : UGTAt G :=
  fun _ _ z hz hne => absurd (hcore z hz) hne

open CFSG.ComponentClassification in
theorem UGTAt.of_uOutcome {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (h : (∃ z : G, orderOf z = 2 ∧
        CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) →
      OutcomeLocal.UOutcome G) : UGTAt G := by
  intro hnonab _ z hz hne
  have htop : GeneralizedFitting.subgroup G = ⊤ :=
    (SmallLocal.simple_generalized_fitting_self_local G hnonab).2.2.2.2
  let e : GeneralizedFitting.subgroup G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  rcases h ⟨z, hz, hne⟩ with hU | ⟨n, hodd, h7, ⟨eA⟩, h1⟩ | ⟨-, hlt⟩
  · obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := hU
    exact .inl ⟨t, n, p, f, hp, hp2, hadm, CFSG.Blueprint.LieModel.of_mulEquiv e hm⟩
  · have hn1 : n % 4 ≠ 1 := fun h4 => (h1 h4).ne htop
    obtain ⟨k, rfl⟩ := hodd
    exact .inr ⟨2 * k + 1, h7, by omega, ⟨e.symm.trans eA⟩⟩
  · exact absurd htop hlt.ne

theorem UGTAt.of_mulEquiv {G S : Type} [Group G] [Finite G] [IsSimpleGroup G]
    [Group S] [Finite S] [IsSimpleGroup S] (e : G ≃* S)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (h : UGTAt G) : UGTAt S := by
  intro hnonab _ z hz hne
  have hnonabG : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨e.symm a, e.symm b, fun heq => hab (by
      have h := congrArg e heq
      simpa [map_mul] using h)⟩
  have hordG : orderOf (e.symm z) = 2 := by
    rw [MulEquiv.orderOf_eq, hz]
  have hmap : (Subgroup.centralizer ({e.symm z} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({z} : Set S) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply e.symm.injective
      simpa only [map_mul] using h
    · intro h
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using h
  have hneG : CFSG.oddCore (Subgroup.centralizer ({e.symm z} : Set G)) ≠ ⊥ := by
    intro hbot
    let iso : (Subgroup.centralizer ({e.symm z} : Set G)) ≃*
        (Subgroup.centralizer ({z} : Set S)) :=
      (MulEquiv.subgroupMap e (Subgroup.centralizer ({e.symm z} : Set G))).trans
        (MulEquiv.subgroupCongr hmap)
    exact hne
      (CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
        iso hbot)
  rcases h hnonabG hK (e.symm z) hordG hneG with hL | ⟨n, h7, h4, ⟨θ⟩⟩
  · obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := hL
    exact .inl ⟨t, n, p, f, hp, hp2, hadm, CFSG.Blueprint.LieModel.of_mulEquiv e hm⟩
  · exact .inr ⟨n, h7, h4, ⟨e.symm.trans θ⟩⟩

open CFSG.ComponentClassification in
theorem UHered.of_simple
    (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hG : UGTAt G) : UHered G := by
  intro S _ _ _ hS
  obtain ⟨A, f, hf⟩ := hS
  by_cases hA : A = ⊤
  ·
    let iso : G ≃* A := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hA).symm
    let g : G →* S := f.comp iso.toMonoidHom
    have hgsurj : Function.Surjective g := fun y => by
      obtain ⟨a, ha⟩ := hf y
      exact ⟨iso.symm a, by simpa [g] using ha⟩
    have hker : g.ker = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal g.ker with hbot | htop
      · exact hbot
      · exfalso
        have hone : g = 1 := MonoidHom.ker_eq_top_iff.mp htop
        have hsub : Subsingleton S := by
          refine ⟨fun y z => ?_⟩
          obtain ⟨a, rfl⟩ := hgsurj y
          obtain ⟨b, rfl⟩ := hgsurj z
          simp [hone]
        exact not_subsingleton S hsub
    exact UGTAt.of_mulEquiv
      (MulEquiv.ofBijective g ⟨g.ker_eq_bot_iff.mp hker, hgsurj⟩) hK hG
  · by_cases hnonab : ∃ a b : S, a * b ≠ b * a
    ·
      have hcatS : CFSG.Blueprint.Catalog S :=
        CFSG.KCore.KProperNonab.catalogue_of_surjective
          CFSG.SectionRank.catalog_isoInvariant hK A hA hnonab f hf
      have htop : GeneralizedFitting.subgroup S = ⊤ :=
        (SmallLocal.simple_generalized_fitting_self_local S hnonab).2.2.2.2
      let e : GeneralizedFitting.subgroup S ≃* S :=
        (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      have hFsimple : IsSimpleGroup (GeneralizedFitting.subgroup S) := e.isSimpleGroup
      have hFnonab : ∃ a b : GeneralizedFitting.subgroup S, a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := hnonab
        exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
      have hFcat : CFSG.Blueprint.Catalog (GeneralizedFitting.subgroup S) :=
        CFSG.SectionRank.catalog_of_mulEquiv e hcatS
      exact UGTAt.of_uOutcome fun hz => hCU S hFsimple hFnonab hFcat hz
    · exact fun h => absurd h hnonab

end CFSG.EvenSporadicStandard.Induction.Balance
