module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.FrattiniFoundations
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CharacteristicQuotientActions

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] def FrattiniLifts (G : Type u) [Group G] :=
  {tuple : (G ⧸ frattini G) → G //
    ∀ member, QuotientGroup.mk' (frattini G) (tuple member) = member}

@[expose] noncomputable def frattiniLiftsEquivKernelFunctions (G : Type u) [Group G] :
    FrattiniLifts G ≃ ((G ⧸ frattini G) → (QuotientGroup.mk' (frattini G)).ker) :=
  Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight fun member =>
    MonoidHom.fiberEquivKerOfSurjective (QuotientGroup.mk'_surjective (frattini G)) member)

theorem frattiniLifts_card (G : Type u) [Group G] [Finite G] :
    Nat.card (FrattiniLifts G) = Nat.card (frattini G) ^ Nat.card (G ⧸ frattini G) := by
  rw [Nat.card_congr (frattiniLiftsEquivKernelFunctions G), Nat.card_fun, QuotientGroup.ker_mk']

theorem frattiniLifts_generate {G : Type u} [Group G] [Finite G] (tuple : FrattiniLifts G) :
    Subgroup.closure (Set.range tuple.val) = ⊤ := by
  apply frattini_generators_lift
  apply top_unique
  intro member _
  exact Subgroup.subset_closure ⟨tuple.val member, ⟨member, rfl⟩, tuple.property member⟩

@[expose, instance_reducible]
def frattiniLiftsKernelAction (G : Type u) [Group G] :
    MulAction (characteristicQuotientAction (frattini G)).ker (FrattiniLifts G) where
  smul equivalence tuple := ⟨fun member => (equivalence.val : MulAut G) (tuple.val member),
    fun member =>
      (characteristicQuotientAction_mem_kernel_iff (frattini G) equivalence.val).mp
        equivalence.property (tuple.val member) |>.trans (tuple.property member)⟩
  one_smul tuple := by
    apply Subtype.ext
    funext member
    rfl
  mul_smul first second tuple := by
    apply Subtype.ext
    funext member
    rfl

theorem frattini_automorphism_kernel_isPGroup {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime G) :
    IsPGroup prime (characteristicQuotientAction (frattini G)).ker := by
  classical
  have : Fact prime.Prime := ⟨hprime⟩
  let kernel := (characteristicQuotientAction (frattini G)).ker
  let : MulAction kernel (FrattiniLifts G) := frattiniLiftsKernelAction G
  have hcard := Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := kernel)).ne'
    (p := prime)
  apply IsPGroup.of_card
  apply hcard
  intro otherPrime hotherPrime hdivisor
  by_contra hne
  have : Fact otherPrime.Prime := ⟨hotherPrime⟩
  obtain ⟨equivalence, horder⟩ := exists_prime_orderOf_dvd_card' otherPrime hdivisor
  let cyclic := Subgroup.zpowers equivalence
  have hcyclic : IsPGroup otherPrime cyclic := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, horder, pow_one]
  let : MulAction cyclic (FrattiniLifts G) := MulAction.compHom (FrattiniLifts G) cyclic.subtype
  obtain ⟨dimension, hfrattiniCard⟩ := (hpgroup.to_subgroup (frattini G)).exists_card_eq
  have hcoprime : ¬otherPrime ∣ Nat.card (FrattiniLifts G) := by
    rw [frattiniLifts_card, hfrattiniCard, ← pow_mul]
    intro hdivisor
    have hprimeDivisor := hotherPrime.dvd_of_dvd_pow hdivisor
    exact hne ((Nat.Prime.dvd_iff_eq hprime hotherPrime.ne_one).mp hprimeDivisor).symm
  obtain ⟨tuple, hfixed⟩ := hcyclic.nonempty_fixed_point_of_prime_not_dvd_card (FrattiniLifts G) hcoprime
  have htupleFixed : ∀ member, (equivalence.val : MulAut G) (tuple.val member) = tuple.val member := by
    intro member
    have heq := hfixed (⟨equivalence, Subgroup.mem_zpowers equivalence⟩ : cyclic)
    exact congrArg (fun value : FrattiniLifts G => value.val member) heq
  have heq : (equivalence.val : MulAut G).toMonoidHom = MonoidHom.id G := by
    apply MonoidHom.eq_of_eqOn_dense (frattiniLifts_generate tuple)
    rintro member ⟨representative, rfl⟩
    exact htupleFixed representative
  have hone : equivalence = 1 := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro member
    exact DFunLike.congr_fun heq member
  rw [hone, orderOf_one] at horder
  exact hotherPrime.ne_one horder.symm

end CFSG.RankThreeEvenClassification.Helpers
