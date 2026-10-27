module

public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniExact

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse indexUniverse

theorem elementary_independent_kernel_dimension {Source : Type groupUniverse}
    [CommGroup Source] [Finite Source] {Target : Type targetUniverse} [CommGroup Target]
    {Index : Type indexUniverse} [Fintype Index] {prime : ℕ} (hprime : prime.Prime)
    [Module (ZMod prime) (Additive Source)] [Module (ZMod prime) (Additive Target)]
    (quotient : Source →* Target) (hsurjective : Function.Surjective quotient)
    (family : Index → Additive Source) (hindependent : LinearIndependent (ZMod prime) family)
    (hkilled : ∀ index, quotient (family index).toMul = 1) :
    Fintype.card Index + Module.finrank (ZMod prime) (Additive Target) ≤
      Module.finrank (ZMod prime) (Additive Source) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let linearMap := quotient.toAdditive.toZModLinearMap prime
  have hkernel : ∀ index, family index ∈ linearMap.ker := by
    intro index
    change Additive.ofMul (quotient (family index).toMul) = 0
    rw [hkilled]
    rfl
  let kernelFamily : Index → linearMap.ker := fun index => ⟨family index, hkernel index⟩
  have hindependentKernel : LinearIndependent (ZMod prime) kernelFamily := by
    apply LinearIndependent.of_comp linearMap.ker.subtype
    exact hindependent
  have hcount := hindependentKernel.fintype_card_le_finrank
  change Fintype.card Index ≤ Module.finrank (ZMod prime)
    (quotient.toAdditive.toZModLinearMap prime).ker at hcount
  have hdimension := elementary_surjection_finrank hprime quotient hsurjective
  exact hdimension ▸ (by omega)

theorem elementary_log_card_eq_finrank {Elementary : Type groupUniverse} [CommGroup Elementary]
    [Finite Elementary] {prime : ℕ} (hprime : prime.Prime)
    [Module (ZMod prime) (Additive Elementary)] :
    Nat.log prime (Nat.card Elementary) = Module.finrank (ZMod prime) (Additive Elementary) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : NeZero prime := ⟨hprime.ne_zero⟩
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod prime) (V := Additive Elementary)
  have hfieldCard : Nat.card (ZMod prime) = prime := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have helementaryCard : Nat.card (Additive Elementary) = Nat.card Elementary :=
    Nat.card_congr Additive.ofMul.symm
  rw [helementaryCard, hfieldCard] at hcard
  rw [hcard, Nat.log_pow hprime.one_lt]

theorem pGeneratorRank_independent_kernel_loss {Source : Type groupUniverse} [Group Source]
    [Finite Source] {Target : Type targetUniverse} [CommGroup Target]
    {Index : Type indexUniverse} [Fintype Index] {prime : ℕ} (hprime : prime.Prime)
    (hpgroup : IsPGroup prime Source) [Module (ZMod prime) (Additive Target)]
    (quotient : Source →* Target) (hsurjective : Function.Surjective quotient)
    (family : Index → Source) (hkilled : ∀ index, quotient (family index) = 1) :
    let _ : CommGroup (Source ⧸ frattini Source) := pGroupFrattiniCommGroup hprime hpgroup
    ∀ module : Module (ZMod prime) (Additive (Source ⧸ frattini Source)),
      let _ := module
      LinearIndependent (ZMod prime)
        (fun index => Additive.ofMul ((QuotientGroup.mk' (frattini Source)) (family index))) →
      Fintype.card Index + Nat.log prime (Nat.card Target) ≤ pGeneratorRank prime Source := by
  dsimp only
  let : CommGroup (Source ⧸ frattini Source) := pGroupFrattiniCommGroup hprime hpgroup
  intro module
  let := module
  intro hindependent
  let : Finite Target := Finite.of_surjective quotient hsurjective
  have hfrattini := elementary_quotient_kills_frattini hprime quotient hsurjective
  let induced := QuotientGroup.lift (frattini Source) quotient hfrattini
  have hinduced : Function.Surjective induced :=
    QuotientGroup.lift_surjective_of_surjective _ quotient hsurjective hfrattini
  have hinducedKilled : ∀ index,
      induced ((QuotientGroup.mk' (frattini Source)) (family index)) = 1 := by
    intro index
    change (QuotientGroup.lift (frattini Source) quotient hfrattini)
      (family index : Source ⧸ frattini Source) = 1
    rw [QuotientGroup.lift_mk]
    exact hkilled index
  have hdimension := elementary_independent_kernel_dimension hprime induced hinduced
    (fun index => Additive.ofMul ((QuotientGroup.mk' (frattini Source)) (family index)))
    hindependent hinducedKilled
  rw [← pGeneratorRank_eq_frattini_finrank hprime hpgroup module,
    ← elementary_log_card_eq_finrank hprime] at hdimension
  exact hdimension

theorem pGeneratorRank_normal_independent_saving {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {Index : Type indexUniverse} [Fintype Index] {prime : ℕ}
    (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) (Normal : Subgroup Ambient)
    [Normal.Normal] (family : Index → Normal)
    (hfrattini : ∀ index, (family index : Ambient) ∈ frattini Ambient) :
    let _ : CommGroup (Normal ⧸ frattini Normal) :=
      pGroupFrattiniCommGroup hprime (hpgroup.to_subgroup Normal)
    ∀ module : Module (ZMod prime) (Additive (Normal ⧸ frattini Normal)),
      let _ := module
      LinearIndependent (ZMod prime)
        (fun index => Additive.ofMul ((QuotientGroup.mk' (frattini Normal)) (family index))) →
      pGeneratorRank prime Ambient + Fintype.card Index ≤
        pGeneratorRank prime (Ambient ⧸ Normal) + pGeneratorRank prime Normal := by
  dsimp only
  let : CommGroup (Normal ⧸ frattini Normal) :=
    pGroupFrattiniCommGroup hprime (hpgroup.to_subgroup Normal)
  intro module
  let := module
  intro hindependent
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
  let projection := QuotientGroup.mk' (frattini Ambient)
  let Image := Normal.map projection
  let : Module (ZMod prime) (Additive Image) :=
    elementaryZModModule (fun element => by
      apply Subtype.ext
      exact pGroup_frattini_quotient_exponent hprime hpgroup element)
  let restriction := projection.subgroupMap Normal
  have hrestriction : Function.Surjective restriction := projection.subgroupMap_surjective Normal
  have hkilled : ∀ index, restriction (family index) = 1 := by
    intro index
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr (hfrattini index)
  have hloss := pGeneratorRank_independent_kernel_loss hprime (hpgroup.to_subgroup Normal)
    restriction hrestriction family hkilled module hindependent
  have hformula := pGeneratorRank_extension hprime hpgroup (QuotientGroup.mk' Normal)
    (QuotientGroup.mk'_surjective Normal)
  rw [QuotientGroup.ker_mk'] at hformula
  change Fintype.card Index + Nat.log prime
    (Nat.card (Normal.map (QuotientGroup.mk' (frattini Ambient)))) ≤
      pGeneratorRank prime Normal at hloss
  omega

end CFSG.LargeEvenClassification.Helpers
