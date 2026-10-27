module

public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.CoprimeInvariantSylow

@[expose] noncomputable def image {G : Type*} [Group G] [Finite G]
    (prime : ℕ) [Fact prime.Prime] (automorphism : MulAut G) (sylow : Sylow prime G) :
    Sylow prime G := Sylow.mapSurjective (f := automorphism.toMonoidHom) automorphism.surjective sylow

theorem image_subgroup {G : Type*} [Group G] [Finite G]
    (prime : ℕ) [Fact prime.Prime] (automorphism : MulAut G) (sylow : Sylow prime G) :
    (image prime automorphism sylow : Subgroup G) =
      (sylow : Subgroup G).map automorphism.toMonoidHom :=
  Sylow.coe_mapSurjective (f := automorphism.toMonoidHom) automorphism.surjective sylow

@[expose, instance_reducible] noncomputable def action {A G : Type*} [Group A] [Group G] [Finite G]
    (prime : ℕ) [Fact prime.Prime] (homomorphism : A →* MulAut G) :
    MulAction A (Sylow prime G) where
  smul actor sylow := image prime (homomorphism actor) sylow
  one_smul sylow := by
    apply Sylow.ext
    change (image prime (homomorphism 1) sylow : Subgroup G) = sylow
    rw [image_subgroup, homomorphism.map_one]
    change (sylow : Subgroup G).map (MonoidHom.id G) = sylow
    exact Subgroup.map_id _
  mul_smul first second sylow := by
    apply Sylow.ext
    change (image prime (homomorphism (first * second)) sylow : Subgroup G) =
      (image prime (homomorphism first) (image prime (homomorphism second) sylow) : Subgroup G)
    rw [image_subgroup, image_subgroup, image_subgroup, Subgroup.map_map]
    congr 1
    ext member
    exact congrArg (fun automorphism : MulAut G => automorphism member)
      (homomorphism.map_mul first second)

theorem exists_invariant {A G : Type*} [Group A] [Group G] [Finite G]
    (actionPrime sylowPrime : ℕ) [Fact actionPrime.Prime] [Fact sylowPrime.Prime]
    (htype : IsPGroup actionPrime A) (hcoprime : ¬ actionPrime ∣ Nat.card G)
    (homomorphism : A →* MulAut G) :
    ∃ sylow : Sylow sylowPrime G, ∀ actor : A,
      (sylow : Subgroup G).map (homomorphism actor).toMonoidHom = sylow := by
  let := action sylowPrime homomorphism
  let sylow : Sylow sylowPrime G := Classical.choice inferInstance
  have hcount : Nat.card (Sylow sylowPrime G) ∣ Nat.card G :=
    sylow.card_dvd_index.trans (sylow : Subgroup G).index_dvd_card
  have hnot : ¬ actionPrime ∣ Nat.card (Sylow sylowPrime G) :=
    fun hdivides => hcoprime (hdivides.trans hcount)
  obtain ⟨fixed, hfixed⟩ := htype.nonempty_fixed_point_of_prime_not_dvd_card
    (Sylow sylowPrime G) hnot
  refine ⟨fixed, fun actor => ?_⟩
  have heq := MulAction.mem_fixedPoints.mp hfixed actor
  have hsubgroup := congrArg (fun sylow : Sylow sylowPrime G => (sylow : Subgroup G)) heq
  exact (image_subgroup sylowPrime (homomorphism actor) fixed).symm.trans hsubgroup

@[expose] noncomputable def restriction {A G : Type*} [Group A] [Group G]
    (homomorphism : A →* MulAut G) (subgroup : Subgroup G)
    (hinvariant : ∀ actor : A, subgroup.map (homomorphism actor).toMonoidHom = subgroup) :
    A →* MulAut subgroup where
  toFun actor := ((homomorphism actor).subgroupMap subgroup).trans
    (MulEquiv.subgroupCongr (hinvariant actor))
  map_one' := by
    ext member
    exact congrArg (fun automorphism : MulAut G => automorphism member.val) homomorphism.map_one
  map_mul' first second := by
    ext member
    exact congrArg (fun automorphism : MulAut G => automorphism member.val)
      (homomorphism.map_mul first second)

theorem restriction_apply {A G : Type*} [Group A] [Group G]
    (homomorphism : A →* MulAut G) (subgroup : Subgroup G)
    (hinvariant : ∀ actor : A, subgroup.map (homomorphism actor).toMonoidHom = subgroup)
    (actor : A) (member : subgroup) :
    (restriction homomorphism subgroup hinvariant actor member).val =
      (homomorphism actor) member.val := rfl

end CFSG.ComponentClassification.CoprimeInvariantSylow
