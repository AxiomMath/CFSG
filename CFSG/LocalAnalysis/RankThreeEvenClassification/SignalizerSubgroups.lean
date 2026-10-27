module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaSignalizerCompletion

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

structure SignalizerCompatible {G : Type u} [Group G] (prime : ℕ) (actor : Subgroup G)
    (signalizer : G → Subgroup G) (subgroup : Subgroup G) : Prop where
  normalized : actor ≤ Subgroup.normalizer (subgroup : Set G)
  solvable : Group.IsSolvable subgroup
  primeComplement : ¬prime ∣ Nat.card subgroup
  fixed_le : ∀ element ∈ actor, element ≠ 1 →
    subgroup ⊓ Subgroup.centralizer ({element} : Set G) ≤ signalizer element

@[expose] noncomputable def signalizerGenerated {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) : Subgroup G :=
  ⨆ (element : G) (_ : element ∈ actor) (_ : element ≠ 1), signalizer element

@[expose] def SignalizerComplete {G : Type u} [Group G] (prime : ℕ) (actor : Subgroup G)
    (signalizer : G → Subgroup G) : Prop :=
  SignalizerCompatible prime actor signalizer (signalizerGenerated actor signalizer)

theorem signalizer_value_le_generated {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G)
    (element : G) (hmem : element ∈ actor) (hne : element ≠ 1) :
    signalizer element ≤ signalizerGenerated actor signalizer := by
  exact le_iSup_of_le element (le_iSup_of_le hmem (le_iSup_of_le hne le_rfl))

theorem signalizerGenerated_normalized {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer) :
    actor ≤ Subgroup.normalizer (signalizerGenerated actor signalizer : Set G) := by
  apply normalizes_iSup
  intro element
  apply normalizes_iSup
  intro hmem
  apply normalizes_iSup
  intro hne member hmember
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (hsignalizer.invariant element hmem hne member hmember)

theorem SignalizerCompatible.bot {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (signalizer : G → Subgroup G) :
    SignalizerCompatible prime actor signalizer ⊥ := by
  refine ⟨Subgroup.le_normalizer_of_normal, inferInstance, ?_, ?_⟩
  · simpa only [Subgroup.card_bot] using hprime.not_dvd_one
  · intro _ _ _
    simp only [bot_inf_eq, bot_le]

theorem SignalizerCompatible.of_le {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (subgroup smaller : Subgroup G) (hcompatible : SignalizerCompatible prime actor signalizer subgroup)
    (hle : smaller ≤ subgroup) (hnormalized : actor ≤ Subgroup.normalizer (smaller : Set G)) :
    SignalizerCompatible prime actor signalizer smaller := by
  have : Group.IsSolvable subgroup := hcompatible.solvable
  refine ⟨hnormalized,
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle),
    fun hdiv => hcompatible.primeComplement (hdiv.trans (Subgroup.card_dvd_of_le hle)), ?_⟩
  intro element hmem hne
  exact (inf_le_inf hle le_rfl).trans (hcompatible.fixed_le element hmem hne)

theorem signalizer_value_compatible {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (element : G) (hmem : element ∈ actor) (hne : element ≠ 1) :
    SignalizerCompatible prime actor signalizer (signalizer element) := by
  refine ⟨?_, hsignalizer.solvable element hmem hne,
    hprime.coprime_iff_not_dvd.mp (hsignalizer.coprime element hmem hne), ?_⟩
  · intro member hmember
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (hsignalizer.invariant element hmem hne member hmember)
  · intro member hmember hmemberNe
    exact hsignalizer.balance element hmem hne member hmember hmemberNe

theorem SignalizerCompatible.le_generated {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G) (signalizer : G → Subgroup G)
    (hplaneLe : plane ≤ actor) (hpower : ∀ member : plane, member ^ prime = 1)
    (hplaneCard : Nat.card plane = prime ^ 2)
    (subgroup : Subgroup G) (hcompatible : SignalizerCompatible prime actor signalizer subgroup) :
    subgroup ≤ signalizerGenerated actor signalizer := by
  rw [solvable_centralizer_generation_of_plane prime hprime plane subgroup hpower hplaneCard
    hcompatible.solvable hcompatible.primeComplement (hplaneLe.trans hcompatible.normalized)]
  apply iSup_le
  intro member
  apply iSup_le
  intro hne
  have hmemberNe : (member : G) ≠ 1 := fun heq => hne (Subtype.ext heq)
  exact (hcompatible.fixed_le member (hplaneLe member.property) hmemberNe).trans
    (signalizer_value_le_generated actor signalizer member (hplaneLe member.property) hmemberNe)

theorem exists_maximal_signalizer_compatible_above {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (subgroup : Subgroup G) (hcompatible : SignalizerCompatible prime actor signalizer subgroup) :
    ∃ maximal : Subgroup G, subgroup ≤ maximal ∧
      Maximal (SignalizerCompatible prime actor signalizer) maximal := by
  exact Finite.exists_le_maximal hcompatible

theorem signalizer_complete_iff_exists_greatest_compatible
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hplaneLe : plane ≤ actor) (hpower : ∀ member : plane, member ^ prime = 1)
    (hplaneCard : Nat.card plane = prime ^ 2) :
    SignalizerComplete prime actor signalizer ↔
      ∃ greatest : Subgroup G, SignalizerCompatible prime actor signalizer greatest ∧
        ∀ subgroup : Subgroup G, SignalizerCompatible prime actor signalizer subgroup → subgroup ≤ greatest := by
  constructor
  · intro hcomplete
    exact ⟨signalizerGenerated actor signalizer, hcomplete, fun subgroup hcompatible =>
      SignalizerCompatible.le_generated prime hprime actor plane signalizer hplaneLe hpower hplaneCard
        subgroup hcompatible⟩
  · rintro ⟨greatest, hcompatible, hgreatest⟩
    have hgeneratedLe : signalizerGenerated actor signalizer ≤ greatest := by
      apply iSup_le
      intro element
      apply iSup_le
      intro hmem
      apply iSup_le
      intro hne
      exact hgreatest _ (signalizer_value_compatible prime hprime actor signalizer hsignalizer element hmem hne)
    exact SignalizerCompatible.of_le prime actor signalizer greatest _ hcompatible hgeneratedLe
      (signalizerGenerated_normalized prime actor signalizer hsignalizer)

theorem SignalizerComplete.centralizer_eq {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hcomplete : SignalizerComplete prime actor signalizer)
    (element : G) (hmem : element ∈ actor) (hne : element ≠ 1) :
    signalizerGenerated actor signalizer ⊓ Subgroup.centralizer ({element} : Set G) =
      signalizer element := by
  exact le_antisymm (hcomplete.fixed_le element hmem hne)
    (le_inf (signalizer_value_le_generated actor signalizer element hmem hne)
      (hsignalizer.le_centralizer element hmem hne))

theorem thetaPlaneAlpha_solvable_prime_complement_of_signalizer_complete
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G)
    (hab : IsElemAbelian prime actor) (hplaneLe : plane ≤ actor)
    (element : G) (hmem : element ∈ plane) (hne : element ≠ 1)
    (hcomplete : SignalizerComplete prime actor (thetaActorSignalizer prime actor)) :
    Group.IsSolvable (thetaPlaneAlpha prime plane) ∧ ¬prime ∣ Nat.card (thetaPlaneAlpha prime plane) := by
  exact ⟨thetaPlaneAlpha_solvable_of_generated_solvable prime hprime actor plane hab hplaneLe
      element hmem hne hcomplete.solvable,
    thetaPlaneAlpha_prime_complement_of_generated_prime_complement prime hprime actor plane hab
      hplaneLe element hmem hne hcomplete.primeComplement⟩

end CFSG.RankThreeEvenClassification.Helpers
