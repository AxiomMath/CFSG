module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaSolvableQuotient

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

@[expose] def kernelEquivFiber {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (element : G) :
    homomorphism.ker ≃ {other : G // homomorphism other = homomorphism element} where
  toFun member := ⟨member * element, by simp only [map_mul, MonoidHom.mem_ker.mp member.property, one_mul]⟩
  invFun other := ⟨other * element⁻¹, by
    apply MonoidHom.mem_ker.mpr
    simp only [map_mul, map_inv, other.property, mul_inv_cancel]⟩
  left_inv member := Subtype.ext (mul_inv_cancel_right _ _)
  right_inv other := Subtype.ext (inv_mul_cancel_right _ _)

theorem exists_centralizer_preimage_of_pGroup_prime_complement_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker)
    (actor : Subgroup G) (hpgroup : IsPGroup prime actor) (target : H)
    (htarget : target ∈ Subgroup.centralizer (actor.map homomorphism : Set H)) :
    ∃ element ∈ Subgroup.centralizer (actor : Set G), homomorphism element = target := by
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨representative, hrepresentative⟩ := hsurjective target
  let fiber := {element : G // homomorphism element = target}
  let action : MulAction actor fiber :=
    { smul := fun member element =>
        ⟨member * element * (member : G)⁻¹, by
          have hcomm := Subgroup.mem_centralizer_iff.mp htarget (homomorphism member)
            (Subgroup.mem_map_of_mem homomorphism member.property)
          simp only [map_mul, map_inv, element.property]
          rw [hcomm, mul_inv_cancel_right]⟩
      one_smul := fun element => Subtype.ext (by
        change (1 : G) * (element : G) * (1 : G)⁻¹ = element
        simp)
      mul_smul := fun first second element => Subtype.ext (by
        change ((first : G) * (second : G)) * (element : G) * ((first : G) * (second : G))⁻¹ =
          (first : G) * ((second : G) * (element : G) * (second : G)⁻¹) * (first : G)⁻¹
        simp [mul_assoc]) }
  let : MulAction actor fiber := action
  have hcard : Nat.card fiber = Nat.card homomorphism.ker := by
    have hequivalence := kernelEquivFiber homomorphism representative
    simpa only [hrepresentative] using (Nat.card_congr hequivalence).symm
  obtain ⟨element, hfixed⟩ := hpgroup.nonempty_fixed_point_of_prime_not_dvd_card fiber
    (hcard.symm ▸ hkernelComplement)
  refine ⟨element, ?_, element.property⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have heq := congrArg (fun value : fiber => (value : G))
    (MulAction.mem_fixedPoints.mp hfixed (⟨member, hmember⟩ : actor))
  change member * (element : G) * member⁻¹ = (element : G) at heq
  have hmul := congrArg (fun value : G => value * member) heq
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul

theorem centralizer_map_eq_of_pGroup_prime_complement_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker)
    (actor : Subgroup G) (hpgroup : IsPGroup prime actor) :
    (Subgroup.centralizer (actor : Set G)).map homomorphism =
      Subgroup.centralizer (actor.map homomorphism : Set H) := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr (centralizer_le_comap_centralizer_map homomorphism actor)
  · intro target htarget
    obtain ⟨element, helement, heq⟩ :=
      exists_centralizer_preimage_of_pGroup_prime_complement_kernel prime hprime homomorphism
        hsurjective hkernelComplement actor hpgroup target htarget
    exact Subgroup.mem_map.mpr ⟨element, helement, heq⟩

theorem thetaCoreOf_map_eq_of_solvable_prime_complement_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hkernelSolvable : Group.IsSolvable homomorphism.ker)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker) (subgroup : Subgroup G) :
    (thetaCoreOf prime subgroup).map homomorphism =
      thetaCoreOf prime (subgroup.map homomorphism) := by
  let restriction := homomorphism.subgroupMap subgroup
  let kernelMap : restriction.ker →* homomorphism.ker :=
    { toFun := fun element =>
        ⟨((element : subgroup) : G), congrArg Subtype.val (MonoidHom.mem_ker.mp element.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hkernelMapInjective : Function.Injective kernelMap := by
    intro first second heq
    exact Subtype.ext (Subtype.ext
      (congrArg (fun element : homomorphism.ker => (element : G)) heq))
  have hrestrictionKernelSolvable : Group.IsSolvable restriction.ker := by
    have : Group.IsSolvable homomorphism.ker := hkernelSolvable
    exact Group.isSolvable_of_isSolvable_injective (f := kernelMap) hkernelMapInjective
  have hrestrictionKernelComplement : ¬prime ∣ Nat.card restriction.ker := by
    exact fun hdiv => hkernelComplement
      (hdiv.trans (Subgroup.card_dvd_of_injective kernelMap hkernelMapInjective))
  have hmap := solvablePrimeComplementCore_map_eq_of_solvable_prime_complement_kernel prime hprime
    restriction (homomorphism.subgroupMap_surjective subgroup) hrestrictionKernelSolvable
    hrestrictionKernelComplement
  have hcomposition : (subgroup.map homomorphism).subtype.comp restriction =
      homomorphism.comp subgroup.subtype := by
    ext element
    rfl
  have hresult := congrArg (Subgroup.map (subgroup.map homomorphism).subtype) hmap
  rw [Subgroup.map_map, hcomposition, ← Subgroup.map_map] at hresult
  exact hresult

theorem thetaCoreOf_centralizer_map_eq_of_pGroup_solvable_prime_complement_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hkernelSolvable : Group.IsSolvable homomorphism.ker)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker)
    (actor : Subgroup G) (hpgroup : IsPGroup prime actor) :
    (thetaCoreOf prime (Subgroup.centralizer (actor : Set G))).map homomorphism =
      thetaCoreOf prime (Subgroup.centralizer (actor.map homomorphism : Set H)) := by
  rw [thetaCoreOf_map_eq_of_solvable_prime_complement_kernel prime hprime homomorphism
    hkernelSolvable hkernelComplement,
    centralizer_map_eq_of_pGroup_prime_complement_kernel prime hprime homomorphism hsurjective
      hkernelComplement actor hpgroup]

end CFSG.RankThreeEvenClassification.Helpers
