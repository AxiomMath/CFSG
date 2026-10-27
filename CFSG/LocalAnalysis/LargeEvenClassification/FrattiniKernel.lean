module

public import CFSG.LocalAnalysis.LargeEvenClassification.LocalCore

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

@[expose] def frattiniKernel (Ambient : Type groupUniverse) [Group Ambient] : Subgroup (MulAut Ambient) where
  carrier := {automorphism | ∀ element : Ambient,
    (automorphism element : Ambient ⧸ frattini Ambient) = (element : Ambient ⧸ frattini Ambient)}
  one_mem' := by
    intro element
    rfl
  mul_mem' := by
    intro first second hfirst hsecond element
    exact (hfirst (second element)).trans (hsecond element)
  inv_mem' := by
    intro automorphism hautomorphism element
    simpa using (hautomorphism (automorphism.symm element)).symm

@[expose] def frattiniLifts (Ambient : Type groupUniverse) [Group Ambient] : Type groupUniverse :=
  (coset : Ambient ⧸ frattini Ambient) →
    {element : Ambient // (element : Ambient ⧸ frattini Ambient) = coset}

instance frattiniLiftsFinite (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient] :
    Finite (frattiniLifts Ambient) := by
  unfold frattiniLifts
  infer_instance

instance frattiniLiftsAction (Ambient : Type groupUniverse) [Group Ambient] :
    MulAction (frattiniKernel Ambient) (frattiniLifts Ambient) where
  smul automorphism lifts coset :=
    ⟨automorphism.val (lifts coset).val,
      (automorphism.property (lifts coset).val).trans (lifts coset).property⟩
  one_smul := by
    intro lifts
    funext coset
    apply Subtype.ext
    rfl
  mul_smul := by
    intro first second lifts
    funext coset
    apply Subtype.ext
    rfl

theorem frattiniLifts_generate (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient]
    (lifts : frattiniLifts Ambient) :
    Subgroup.closure (Set.range (fun coset => (lifts coset).val)) = ⊤ := by
  apply frattini_nongenerating
  apply top_unique
  intro element _
  let representative := (lifts (element : Ambient ⧸ frattini Ambient)).val
  have hrepresentative : representative ∈
      Subgroup.closure (Set.range (fun coset => (lifts coset).val)) :=
    Subgroup.subset_closure ⟨(element : Ambient ⧸ frattini Ambient), rfl⟩
  have hcoset : (representative : Ambient ⧸ frattini Ambient) =
      (element : Ambient ⧸ frattini Ambient) :=
    (lifts (element : Ambient ⧸ frattini Ambient)).property
  have hdifference : representative⁻¹ * element ∈ frattini Ambient := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (frattini Ambient)) (representative⁻¹ * element) = 1
    rw [map_mul, map_inv]
    change (representative : Ambient ⧸ frattini Ambient)⁻¹ *
      (element : Ambient ⧸ frattini Ambient) = 1
    rw [hcoset]
    simp
  have hproduct := (Subgroup.closure (Set.range (fun coset => (lifts coset).val)) ⊔
    frattini Ambient).mul_mem (Subgroup.mem_sup_left hrepresentative)
      (Subgroup.mem_sup_right hdifference)
  simpa using hproduct

theorem frattiniLifts_stabilizer_eq_bot (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] (lifts : frattiniLifts Ambient) :
    MulAction.stabilizer (frattiniKernel Ambient) lifts = ⊥ := by
  apply le_antisymm _ bot_le
  intro automorphism hstabilizer
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply MulEquiv.ext
  intro element
  have hfixed : Set.EqOn automorphism.val (MonoidHom.id Ambient)
      (Set.range (fun coset => (lifts coset).val)) := by
    rintro representative ⟨coset, rfl⟩
    have hlifts := congrFun hstabilizer coset
    exact congrArg Subtype.val hlifts
  have hclosure := MonoidHom.eqOn_closure
    (f := automorphism.val.toMonoidHom) (g := MonoidHom.id Ambient) hfixed
  apply hclosure
  rw [frattiniLifts_generate Ambient lifts]
  trivial

theorem card_dvd_of_trivial_stabilizers (Acting Space : Type groupUniverse) [Group Acting]
    [MulAction Acting Space] [Finite Acting] [Finite Space]
    (hfree : ∀ element : Space, MulAction.stabilizer Acting element = ⊥) :
    Nat.card Acting ∣ Nat.card Space := by
  classical
  let : Fintype Acting := Fintype.ofFinite Acting
  let : Fintype Space := Fintype.ofFinite Space
  let : Fintype (Quotient (MulAction.orbitRel Acting Space)) := Fintype.ofFinite _
  let : (element : Space) → Fintype (MulAction.stabilizer Acting element) :=
    fun element => Fintype.ofFinite (MulAction.stabilizer Acting element)
  have hcard := MulAction.card_eq_sum_card_group_div_card_stabilizer Acting Space
  have hsum : (∑ orbit : Quotient (MulAction.orbitRel Acting Space),
      Fintype.card Acting / Fintype.card (MulAction.stabilizer Acting orbit.out)) =
      ∑ _ : Quotient (MulAction.orbitRel Acting Space), Fintype.card Acting := by
    apply Finset.sum_congr rfl
    intro orbit _
    have hstabilizerCard : Fintype.card (MulAction.stabilizer Acting orbit.out) = 1 := by
      simpa only [Nat.card_eq_fintype_card] using (Subgroup.card_eq_one.mpr (hfree orbit.out))
    rw [hstabilizerCard, Nat.div_one]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard, hsum]
  exact Finset.dvd_sum (fun _ _ => dvd_rfl)

theorem frattiniFiber_card (Ambient : Type groupUniverse) [Group Ambient]
    (coset : Ambient ⧸ frattini Ambient) :
    Nat.card {element : Ambient // (element : Ambient ⧸ frattini Ambient) = coset} =
      Nat.card (frattini Ambient) := by
  obtain ⟨representative, hrepresentative⟩ := QuotientGroup.mk'_surjective
    (frattini Ambient) coset
  subst coset
  have hcard := Nat.card_congr ((QuotientGroup.mk' (frattini Ambient)).fiberEquivKer representative)
  rw [QuotientGroup.ker_mk'] at hcard
  exact hcard

theorem frattiniLifts_card (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient] :
    Nat.card (frattiniLifts Ambient) =
      Nat.card (frattini Ambient) ^ Nat.card (Ambient ⧸ frattini Ambient) := by
  classical
  let : Fintype (Ambient ⧸ frattini Ambient) := Fintype.ofFinite _
  change Nat.card ((coset : Ambient ⧸ frattini Ambient) →
    {element : Ambient // (element : Ambient ⧸ frattini Ambient) = coset}) = _
  rw [Nat.card_pi]
  simp only [frattiniFiber_card]
  simp

theorem frattiniKernel_card_dvd (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient] :
    Nat.card (frattiniKernel Ambient) ∣
      Nat.card (frattini Ambient) ^ Nat.card (Ambient ⧸ frattini Ambient) := by
  have hdivides := card_dvd_of_trivial_stabilizers (frattiniKernel Ambient)
    (frattiniLifts Ambient) (frattiniLifts_stabilizer_eq_bot Ambient)
  rwa [frattiniLifts_card] at hdivides

theorem frattiniKernel_isPGroup (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) :
    IsPGroup prime (frattiniKernel Ambient) := by
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨exponent, hcard⟩ := (hpgroup.to_subgroup (frattini Ambient)).exists_card_eq
  apply IsPGroup.of_card_dvd_pow
  have hdivides := frattiniKernel_card_dvd Ambient
  rw [hcard, ← pow_mul] at hdivides
  exact hdivides

@[expose] def frattiniAutAction (Ambient : Type groupUniverse) [Group Ambient] :
    MulAut Ambient →* MulAut (Ambient ⧸ frattini Ambient) where
  toFun automorphism := QuotientGroup.congr (frattini Ambient) (frattini Ambient)
    automorphism (Subgroup.characteristic_iff_map_eq.mp inferInstance automorphism)
  map_one' := by
    apply MulEquiv.ext
    intro coset
    induction coset using QuotientGroup.induction_on with
    | H representative => rfl
  map_mul' := by
    intro first second
    apply MulEquiv.ext
    intro coset
    induction coset using QuotientGroup.induction_on with
    | H representative => rfl

theorem frattiniAutAction_ker (Ambient : Type groupUniverse) [Group Ambient] :
    (frattiniAutAction Ambient).ker = frattiniKernel Ambient := by
  ext automorphism
  constructor
  · intro hkernel element
    exact congrArg (fun quotientAutomorphism : MulAut (Ambient ⧸ frattini Ambient) =>
      quotientAutomorphism (element : Ambient ⧸ frattini Ambient)) hkernel
  · intro hkernel
    apply MulEquiv.ext
    intro coset
    induction coset using QuotientGroup.induction_on with
    | H representative => exact hkernel representative

theorem frattiniAutAction_isPGroup_ker (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) :
    IsPGroup prime (frattiniAutAction Ambient).ker := by
  rw [frattiniAutAction_ker]
  exact frattiniKernel_isPGroup Ambient hprime hpgroup

theorem frattiniAutAction_odd_injective {Core Acting : Type groupUniverse} [Group Core]
    [Group Acting] [Finite Core] {corePrime actingPrime : ℕ}
    (hcorePrime : corePrime.Prime) (hactingPrime : actingPrime.Prime)
    (hdifferent : actingPrime ≠ corePrime) (hcore : IsPGroup corePrime Core)
    (hacting : IsPGroup actingPrime Acting) (action : Acting →* MulAut Core)
    (hinjective : Function.Injective action) :
    Function.Injective ((frattiniAutAction Core).comp action) := by
  let : Fact corePrime.Prime := ⟨hcorePrime⟩
  let : Fact actingPrime.Prime := ⟨hactingPrime⟩
  have himage : IsPGroup actingPrime action.range := by
    exact hacting.of_surjective action.rangeRestrict action.rangeRestrict_surjective
  have hkernel : IsPGroup corePrime (frattiniAutAction Core).ker :=
    frattiniAutAction_isPGroup_ker Core hcorePrime hcore
  have hdisjoint := IsPGroup.disjoint_of_ne actingPrime corePrime hdifferent
    action.range (frattiniAutAction Core).ker himage hkernel
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro element helement
  apply Subgroup.mem_bot.mpr
  apply hinjective
  rw [map_one]
  apply Subgroup.disjoint_def.mp hdisjoint ⟨element, rfl⟩ helement

theorem charTwo_odd_core_frattini_action_injective {Ambient : Type groupUniverse}
    [Group Ambient] [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : CFSG.Open.IsCharTwoType Ambient)
    (OddSubgroup Local : Subgroup Ambient) (hle : OddSubgroup ≤ Local)
    (hpgroup : IsPGroup prime OddSubgroup)
    (hlocal : CFSG.Open.IsTwoLocal Local) :
    ∃ action : OddSubgroup →* MulAut
        (((CFSG.Open.pCoreOf 2 Local).subgroupOf Local) ⧸
          frattini ((CFSG.Open.pCoreOf 2 Local).subgroupOf Local)),
      Function.Injective action := by
  obtain ⟨action, hinjective⟩ := charTwo_odd_core_action_injective hprime hodd hchar
    OddSubgroup Local hle hpgroup hlocal
  have hcore := (pCoreOf_isPGroup 2 Local).comap_subtype (K := Local)
  refine ⟨(frattiniAutAction _).comp action, ?_⟩
  exact frattiniAutAction_odd_injective Nat.prime_two hprime hodd hcore hpgroup action hinjective

end CFSG.LargeEvenClassification.Helpers
