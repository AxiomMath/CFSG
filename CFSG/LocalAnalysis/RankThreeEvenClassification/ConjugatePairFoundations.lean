module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CentralQuotient

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

@[expose] def PrimeConjugatePairs {G : Type u} [Group G] (prime : ℕ) (member : G) : Prop :=
  ∀ conjugator : G,
    IsPGroup prime (Subgroup.zpowers member ⊔ Subgroup.zpowers (conjugator⁻¹ * member * conjugator) : Subgroup G)

theorem PrimeConjugatePairs.cyclic {G : Type u} [Group G] (prime : ℕ) (member : G)
    (hpairs : PrimeConjugatePairs prime member) : IsPGroup prime (Subgroup.zpowers member) :=
  (hpairs 1).to_le le_sup_left

theorem PrimeConjugatePairs.map_surjective {G : Type u} {H : Type v} [Group G] [Group H]
    (prime : ℕ) (member : G) (hpairs : PrimeConjugatePairs prime member)
    (homomorphism : G →* H) (hsurjective : Function.Surjective homomorphism) :
    PrimeConjugatePairs prime (homomorphism member) := by
  intro conjugator
  obtain ⟨conjugator, rfl⟩ := hsurjective conjugator
  have hmapped := (hpairs conjugator).map homomorphism
  apply hmapped.of_equiv
  apply MulEquiv.subgroupCongr
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, map_mul, map_mul, map_inv]

theorem PrimeConjugatePairs.centralizes_normal_complement {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (member : G) (hpairs : PrimeConjugatePairs prime member)
    (normal : Subgroup G) [normal.Normal] (hcomplement : ¬prime ∣ Nat.card normal) :
    member ∈ Subgroup.centralizer (normal : Set G) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro conjugator hconjugator
  let pair := Subgroup.zpowers member ⊔ Subgroup.zpowers (conjugator⁻¹ * member * conjugator)
  have hdisjoint := prime_complement_disjoint_pSubgroup prime hprime normal pair hcomplement (hpairs conjugator)
  have hnormalMem : member⁻¹ * conjugator⁻¹ * member * conjugator ∈ normal :=
    normal.mul_mem ((inferInstance : normal.Normal).conj_mem' conjugator⁻¹
      (normal.inv_mem hconjugator) member) hconjugator
  have hpairMem : member⁻¹ * conjugator⁻¹ * member * conjugator ∈ pair := by
    have hfirst : member ∈ pair :=
      (le_sup_left : Subgroup.zpowers member ≤ pair) (Subgroup.mem_zpowers member)
    have hsecond : conjugator⁻¹ * member * conjugator ∈ pair :=
      (le_sup_right : Subgroup.zpowers (conjugator⁻¹ * member * conjugator) ≤ pair)
        (Subgroup.mem_zpowers _)
    simpa only [mul_assoc] using pair.mul_mem (pair.inv_mem hfirst) hsecond
  have heq := Subgroup.disjoint_def.mp hdisjoint hnormalMem hpairMem
  have hmul := congrArg (fun value : G => member * value * conjugator⁻¹) heq
  have hcommute : conjugator⁻¹ * member = member * conjugator⁻¹ := by
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left, one_mul] using hmul
  calc
    conjugator * member = conjugator * member * conjugator⁻¹ * conjugator := by group
    _ = conjugator * (member * conjugator⁻¹) * conjugator := by group
    _ = conjugator * (conjugator⁻¹ * member) * conjugator := by rw [hcommute]
    _ = member * conjugator := by group

theorem pElement_mem_primeCore_of_central_kernel_pTarget {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G] [Finite H] (prime : ℕ) (hprime : prime.Prime)
    (homomorphism : G →* H) (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (htarget : IsPGroup prime H) (member : G) (hcyclic : IsPGroup prime (Subgroup.zpowers member)) :
    member ∈ pCore prime G := by
  have : Fact prime.Prime := ⟨hprime⟩
  have : Group.IsNilpotent H := htarget.isNilpotent
  have : Group.IsNilpotent G := Subgroup.isNilpotent_of_ker_le_center homomorphism hcentral
  obtain ⟨sylow, hle⟩ := hcyclic.exists_le_sylow
  have hnormal : (sylow : Subgroup G).Normal := inferInstance
  exact le_pCore_of_normal prime _ hnormal sylow.isPGroup' (hle (Subgroup.mem_zpowers member))

theorem cyclic_subtype_isPGroup {G : Type u} [Group G] (prime : ℕ)
    (subgroup : Subgroup G) (member : subgroup)
    (hcyclic : IsPGroup prime (Subgroup.zpowers (member : G))) :
    IsPGroup prime (Subgroup.zpowers member) := by
  have hpreimage := hcyclic.comap_of_injective subgroup.subtype subgroup.subtype_injective
  apply hpreimage.to_le
  exact Subgroup.zpowers_le_of_mem (Subgroup.mem_zpowers (member : G))

end CFSG.RankThreeEvenClassification.Helpers
