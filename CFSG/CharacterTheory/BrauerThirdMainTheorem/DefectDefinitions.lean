module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ClassCoefficients

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

@[expose] def subgroupSubconjugate {G : Type*} [Group G] (left right : Subgroup G) : Prop :=
  ∃ conjugator : G, left.map (MulAut.conj conjugator).toMonoidHom ≤ right

@[expose] def classDefect {G : Type*} [Group G] (prime : ℕ) (conjugacyClass : ConjClasses G)
    (defect : Subgroup G) : Prop :=
  ∃ element : G, ConjClasses.mk element = conjugacyClass ∧
    ∃ sylow : Sylow prime (Subgroup.centralizer {element}),
      (sylow : Subgroup (Subgroup.centralizer {element})).map
        (Subgroup.centralizer {element}).subtype = defect

@[expose] def blockDefect {G : Type*} [Group G] (prime : ℕ) (m : Ideal BlocksAlgInt)
    (character : G → ℂ) (defect : Subgroup G) : Prop :=
  (∃ conjugacyClass : ConjClasses G, classDefect prime conjugacyClass defect ∧
    BlocksCentralChar character (classCoefficients conjugacyClass) ∉ BlocksLocalMaxIdeal m) ∧
  ∀ conjugacyClass : ConjClasses G,
    BlocksCentralChar character (classCoefficients conjugacyClass) ∉ BlocksLocalMaxIdeal m →
      ∀ other : Subgroup G, classDefect prime conjugacyClass other → subgroupSubconjugate defect other

theorem subgroupSubconjugate_refl {G : Type*} [Group G] (subgroup : Subgroup G) :
    subgroupSubconjugate subgroup subgroup := by
  refine ⟨1, ?_⟩
  intro element hmember
  obtain ⟨factor, hfactor, rfl⟩ := Subgroup.mem_map.mp hmember
  change 1 * factor * (1 : G)⁻¹ ∈ subgroup
  simpa only [one_mul, inv_one, mul_one] using hfactor

theorem subgroupSubconjugate_trans {G : Type*} [Group G] {left middle right : Subgroup G}
    (hleft : subgroupSubconjugate left middle) (hright : subgroupSubconjugate middle right) :
    subgroupSubconjugate left right := by
  obtain ⟨first, hfirst⟩ := hleft
  obtain ⟨second, hsecond⟩ := hright
  refine ⟨second * first, ?_⟩
  intro element hmember
  obtain ⟨factor, hfactor, rfl⟩ := Subgroup.mem_map.mp hmember
  apply hsecond
  apply Subgroup.mem_map.mpr
  refine ⟨first * factor * first⁻¹, ?_, ?_⟩
  · exact hfirst (Subgroup.mem_map.mpr ⟨factor, hfactor, rfl⟩)
  · change second * (first * factor * first⁻¹) * second⁻¹ =
      (second * first) * factor * (second * first)⁻¹
    group

theorem subgroupSubconjugate_card_le {G : Type*} [Group G] [Finite G]
    {left right : Subgroup G} (hsubconjugate : subgroupSubconjugate left right) :
    Nat.card left ≤ Nat.card right := by
  obtain ⟨conjugator, hconjugator⟩ := hsubconjugate
  have hcard := Nat.card_congr ((MulAut.conj conjugator).subgroupMap left).toEquiv
  exact hcard.symm ▸ Subgroup.card_le_of_le hconjugator

theorem subgroupSubconjugate_symm_of_card_le {G : Type*} [Group G] [Finite G]
    {left right : Subgroup G} (hsubconjugate : subgroupSubconjugate left right)
    (hcard : Nat.card right ≤ Nat.card left) : subgroupSubconjugate right left := by
  obtain ⟨conjugator, hconjugator⟩ := hsubconjugate
  have hmapCard := Nat.card_congr ((MulAut.conj conjugator).subgroupMap left).toEquiv
  have hequal : left.map (MulAut.conj conjugator).toMonoidHom = right :=
    Subgroup.eq_of_le_of_card_ge hconjugator (hmapCard ▸ hcard)
  refine ⟨conjugator⁻¹, ?_⟩
  intro element hmember
  obtain ⟨factor, hfactor, rfl⟩ := Subgroup.mem_map.mp hmember
  rw [← hequal] at hfactor
  obtain ⟨original, horiginal, rfl⟩ := Subgroup.mem_map.mp hfactor
  change conjugator⁻¹ * (conjugator * original * conjugator⁻¹) *
    (conjugator⁻¹)⁻¹ ∈ left
  have helement : conjugator⁻¹ * (conjugator * original * conjugator⁻¹) *
      (conjugator⁻¹)⁻¹ = original := by group
  rw [helement]
  exact horiginal

theorem classDefect_exists {G : Type*} [Group G]
    (prime : ℕ) (conjugacyClass : ConjClasses G) :
    ∃ defect : Subgroup G, classDefect prime conjugacyClass defect := by
  obtain ⟨element, helement⟩ := ConjClasses.exists_rep conjugacyClass
  let sylow : Sylow prime (Subgroup.centralizer {element}) := Classical.choice inferInstance
  exact ⟨(sylow : Subgroup (Subgroup.centralizer {element})).map
    (Subgroup.centralizer {element}).subtype, element, helement, sylow, rfl⟩

theorem classDefect_isPGroup {G : Type*} [Group G] (prime : ℕ)
    {conjugacyClass : ConjClasses G} {defect : Subgroup G}
    (hdefect : classDefect prime conjugacyClass defect) : IsPGroup prime defect := by
  obtain ⟨element, _, sylow, rfl⟩ := hdefect
  exact sylow.isPGroup'.of_equiv
    ((sylow : Subgroup (Subgroup.centralizer {element})).equivMapOfInjective
      (Subgroup.centralizer {element}).subtype (Subgroup.subtype_injective _))

theorem classDefect_centralizes {G : Type*} [Group G] (prime : ℕ)
    {conjugacyClass : ConjClasses G} {defect : Subgroup G}
    (hdefect : classDefect prime conjugacyClass defect) :
    ∃ element : G, ConjClasses.mk element = conjugacyClass ∧ defect ≤ Subgroup.centralizer {element} := by
  obtain ⟨element, helement, sylow, rfl⟩ := hdefect
  exact ⟨element, helement, Subgroup.map_subtype_le _⟩

end CFSG.BrauerThirdMainTheorem.Helpers
