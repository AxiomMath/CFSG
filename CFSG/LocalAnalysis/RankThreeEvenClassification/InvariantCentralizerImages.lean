module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem exists_centralizer_preimage_in_normalized_prime_complement_subgroup
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (actor subgroup : Subgroup G) (hpgroup : IsPGroup prime actor)
    (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hnormalized : actor ≤ Subgroup.normalizer (subgroup : Set G))
    (target : H) (htarget : target ∈ subgroup.map homomorphism ⊓
      Subgroup.centralizer (actor.map homomorphism : Set H)) :
    ∃ preimage ∈ subgroup ⊓ Subgroup.centralizer (actor : Set G), homomorphism preimage = target := by
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨representative, hrepresentative, hrepresentativeEq⟩ := htarget.1
  let restriction := homomorphism.comp subgroup.subtype
  let internalRepresentative : subgroup := ⟨representative, hrepresentative⟩
  let fiber := {preimage : subgroup // homomorphism preimage = target}
  let action : MulAction actor fiber :=
    { smul := fun member preimage => ⟨⟨member * preimage.1 * (member : G)⁻¹,
        Subgroup.le_normalizer_iff.mp hnormalized member member.property preimage.1 preimage.1.property⟩, by
        change homomorphism ((member : G) * preimage.1 * (member : G)⁻¹) = target
        rw [map_mul, map_mul, map_inv, preimage.property]
        rw [Subgroup.mem_centralizer_iff.mp htarget.2 (homomorphism member)
          (Subgroup.mem_map_of_mem homomorphism member.property), mul_inv_cancel_right]⟩
      one_smul := fun preimage => Subtype.ext (Subtype.ext (by
        change (1 : G) * (preimage.1 : G) * (1 : G)⁻¹ = preimage.1
        simp))
      mul_smul := fun first second preimage => Subtype.ext (Subtype.ext (by
        change ((first : G) * second) * (preimage.1 : G) * ((first : G) * second)⁻¹ =
          first * ((second : G) * preimage.1 * (second : G)⁻¹) * (first : G)⁻¹
        simp [mul_assoc])) }
  let : MulAction actor fiber := action
  have hcard : Nat.card fiber = Nat.card restriction.ker := by
    have hequivalence := kernelEquivFiber restriction internalRepresentative
    change Nat.card {preimage : subgroup // restriction preimage = target} = _
    have hrepresentativeImage : restriction internalRepresentative = target := hrepresentativeEq
    simpa only [hrepresentativeImage] using (Nat.card_congr hequivalence).symm
  have hkernelComplement : ¬prime ∣ Nat.card restriction.ker :=
    fun hdiv => hcomplement (hdiv.trans (Subgroup.card_subgroup_dvd_card restriction.ker))
  obtain ⟨preimage, hfixed⟩ := hpgroup.nonempty_fixed_point_of_prime_not_dvd_card fiber
    (hcard.symm ▸ hkernelComplement)
  refine ⟨preimage.1, ⟨preimage.1.property, ?_⟩, preimage.property⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have heq := congrArg (fun value : fiber => ((value.1 : subgroup) : G))
    (MulAction.mem_fixedPoints.mp hfixed ⟨member, hmember⟩)
  change member * (preimage.1 : G) * member⁻¹ = preimage.1 at heq
  have hmul := congrArg (fun value : G => value * member) heq
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul

theorem normalized_prime_complement_centralizer_map_eq
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (actor subgroup : Subgroup G) (hpgroup : IsPGroup prime actor)
    (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hnormalized : actor ≤ Subgroup.normalizer (subgroup : Set G)) :
    (subgroup ⊓ Subgroup.centralizer (actor : Set G)).map homomorphism =
      subgroup.map homomorphism ⊓ Subgroup.centralizer (actor.map homomorphism : Set H) := by
  apply le_antisymm
  · exact le_inf (Subgroup.map_mono inf_le_left)
      ((Subgroup.map_mono inf_le_right).trans
        (Subgroup.map_le_iff_le_comap.mpr (centralizer_le_comap_centralizer_map homomorphism actor)))
  · intro target htarget
    obtain ⟨preimage, hpreimage, heq⟩ :=
      exists_centralizer_preimage_in_normalized_prime_complement_subgroup prime hprime homomorphism
        actor subgroup hpgroup hcomplement hnormalized target htarget
    exact ⟨preimage, hpreimage, heq⟩

theorem normalized_prime_complement_singleton_centralizer_map_eq
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (actor subgroup : Subgroup G) (hpgroup : IsPGroup prime actor)
    (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hnormalized : actor ≤ Subgroup.normalizer (subgroup : Set G))
    (member : G) (hmember : member ∈ actor) :
    (subgroup ⊓ Subgroup.centralizer ({member} : Set G)).map homomorphism =
      subgroup.map homomorphism ⊓ Subgroup.centralizer ({homomorphism member} : Set H) := by
  have hmap := normalized_prime_complement_centralizer_map_eq prime hprime homomorphism
    (Subgroup.zpowers member) subgroup (hpgroup.to_le (Subgroup.zpowers_le_of_mem hmember))
      hcomplement ((Subgroup.zpowers_le_of_mem hmember).trans hnormalized)
  rw [MonoidHom.map_zpowers] at hmap
  simpa only [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hmap

end CFSG.RankThreeEvenClassification.Helpers
