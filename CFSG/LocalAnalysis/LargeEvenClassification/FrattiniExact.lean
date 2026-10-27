module

public import CFSG.LocalAnalysis.LargeEvenClassification.GeneratorRank

public section

namespace CFSG.LargeEvenClassification.Helpers

universe fieldUniverse groupUniverse targetUniverse

theorem submodule_radical_eq_bot {ScalarField : Type fieldUniverse} [Field ScalarField]
    (Space : Type groupUniverse) [AddCommGroup Space] [Module ScalarField Space] :
    Order.radical (Submodule ScalarField Space) = ⊥ := by
  obtain ⟨complement, hcomplement⟩ :=
    Submodule.exists_isCompl (Order.radical (Submodule ScalarField Space))
  have htop : complement = ⊤ := Order.radical_nongenerating (by
    rw [sup_comm]
    exact hcomplement.sup_eq_top)
  have hbottom := hcomplement.inf_eq_bot
  rwa [htop, inf_top_eq] at hbottom

theorem elementary_frattini_eq_bot {Elementary : Type groupUniverse} [CommGroup Elementary]
    {prime : ℕ} (hprime : prime.Prime) [Module (ZMod prime) (Additive Elementary)] :
    frattini Elementary = ⊥ := by
  let : Fact prime.Prime := ⟨hprime⟩
  let lattice := (Subgroup.toAddSubgroup (G := Elementary)).trans
    (AddSubgroup.toZModSubmodule prime)
  apply lattice.injective
  change lattice (Order.radical (Subgroup Elementary)) = lattice ⊥
  rw [lattice.map_radical, OrderIso.map_bot, submodule_radical_eq_bot]

theorem elementary_quotient_kills_frattini {Source : Type groupUniverse} [Group Source]
    {Target : Type targetUniverse} [CommGroup Target] {prime : ℕ} (hprime : prime.Prime)
    [Module (ZMod prime) (Additive Target)] (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) : frattini Source ≤ quotient.ker := by
  have hle := frattini_le_comap_frattini_of_surjective hsurjective
  rw [elementary_frattini_eq_bot hprime] at hle
  exact hle

theorem pGroup_frattini_map_surjective {Source : Type groupUniverse} [Group Source] [Finite Source]
    {Target : Type targetUniverse} [Group Target] {prime : ℕ} (hprime : prime.Prime)
    (hpgroup : IsPGroup prime Source) (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) :
    (frattini Source).map quotient = frattini Target := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr
      (frattini_le_comap_frattini_of_surjective hsurjective)
  · let image := (frattini Source).map quotient
    let : image.Normal := Subgroup.Normal.map inferInstance quotient hsurjective
    let targetProjection := QuotientGroup.mk' image
    let composite := targetProjection.comp quotient
    have hkernel : frattini Source ≤ composite.ker := by
      intro element helement
      apply (QuotientGroup.eq_one_iff _).mpr
      exact Subgroup.mem_map.mpr ⟨element, helement, rfl⟩
    let induced := QuotientGroup.lift (frattini Source) composite hkernel
    have hinduced : Function.Surjective induced := by
      intro coset
      obtain ⟨element, helement⟩ := QuotientGroup.mk'_surjective image coset
      obtain ⟨source, hsource⟩ := hsurjective element
      refine ⟨QuotientGroup.mk' (frattini Source) source, ?_⟩
      change QuotientGroup.lift (frattini Source) composite hkernel
        (QuotientGroup.mk' (frattini Source) source) = coset
      change QuotientGroup.lift (frattini Source) composite hkernel
        (source : Source ⧸ frattini Source) = coset
      rw [QuotientGroup.lift_mk]
      change (QuotientGroup.mk' image) (quotient source) = coset
      rw [hsource]
      exact helement
    have hcommutative : IsMulCommutative (Target ⧸ image) := by
      apply IsMulCommutative.of_comm
      intro first second
      obtain ⟨firstSource, rfl⟩ := hinduced first
      obtain ⟨secondSource, rfl⟩ := hinduced second
      rw [← map_mul, ← map_mul]
      exact congrArg induced (@mul_comm' (Source ⧸ frattini Source) _
        (pGroup_frattini_quotient_commutative hprime hpgroup) firstSource secondSource)
    let : CommGroup (Target ⧸ image) := { (inferInstance : Group (Target ⧸ image)) with
      mul_comm := @mul_comm' (Target ⧸ image) _ hcommutative }
    have hexponent : ∀ element : Target ⧸ image, element ^ prime = 1 := by
      intro element
      obtain ⟨source, rfl⟩ := hinduced element
      rw [← map_pow, pGroup_frattini_quotient_exponent hprime hpgroup, map_one]
    let : Module (ZMod prime) (Additive (Target ⧸ image)) := elementaryZModModule hexponent
    have hle := elementary_quotient_kills_frattini hprime targetProjection
      (QuotientGroup.mk'_surjective image)
    change frattini Target ≤ (QuotientGroup.mk' image).ker at hle
    simpa only [QuotientGroup.ker_mk'] using hle

def frattiniQuotientMap {Source : Type groupUniverse} [Group Source]
    {Target : Type targetUniverse} [Group Target] (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) :
    (Source ⧸ frattini Source) →* (Target ⧸ frattini Target) :=
  QuotientGroup.map (frattini Source) (frattini Target) quotient
    (frattini_le_comap_frattini_of_surjective hsurjective)

theorem frattiniQuotientMap_surjective {Source : Type groupUniverse} [Group Source]
    {Target : Type targetUniverse} [Group Target] (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) :
    Function.Surjective (frattiniQuotientMap quotient hsurjective) := by
  intro coset
  obtain ⟨element, helement⟩ := QuotientGroup.mk'_surjective (frattini Target) coset
  obtain ⟨source, hsource⟩ := hsurjective element
  refine ⟨QuotientGroup.mk' (frattini Source) source, ?_⟩
  change QuotientGroup.map (frattini Source) (frattini Target) quotient _
    (QuotientGroup.mk' (frattini Source) source) = coset
  rw [QuotientGroup.map_mk', hsource]
  exact helement

theorem frattiniQuotientMap_ker {Source : Type groupUniverse} [Group Source] [Finite Source]
    {Target : Type targetUniverse} [Group Target] {prime : ℕ} (hprime : prime.Prime)
    (hpgroup : IsPGroup prime Source) (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) :
    (frattiniQuotientMap quotient hsurjective).ker =
      quotient.ker.map (QuotientGroup.mk' (frattini Source)) := by
  ext coset
  obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective (frattini Source) coset
  constructor
  · intro helement
    change QuotientGroup.map (frattini Source) (frattini Target) quotient _
      (QuotientGroup.mk' (frattini Source) element) = 1 at helement
    rw [QuotientGroup.map_mk'] at helement
    have hfrattini : quotient element ∈ frattini Target := (QuotientGroup.eq_one_iff _).mp helement
    rw [← pGroup_frattini_map_surjective hprime hpgroup quotient hsurjective] at hfrattini
    obtain ⟨adjustment, hadjustment, hsame⟩ := Subgroup.mem_map.mp hfrattini
    refine Subgroup.mem_map.mpr ⟨element * adjustment⁻¹, ?_, ?_⟩
    · change quotient (element * adjustment⁻¹) = 1
      rw [map_mul, map_inv, hsame, mul_inv_cancel]
    · rw [map_mul, map_inv]
      have hzero : (QuotientGroup.mk' (frattini Source)) adjustment = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hadjustment
      rw [hzero, inv_one, mul_one]
  · intro helement
    obtain ⟨source, hsource, hcoset⟩ := Subgroup.mem_map.mp helement
    rw [← hcoset]
    change QuotientGroup.map (frattini Source) (frattini Target) quotient _
      (QuotientGroup.mk' (frattini Source) source) = 1
    rw [QuotientGroup.map_mk']
    change quotient source = 1 at hsource
    rw [hsource]
    rfl

theorem frattini_extension_card {Source : Type groupUniverse} [Group Source] [Finite Source]
    {Target : Type targetUniverse} [Group Target] {prime : ℕ} (hprime : prime.Prime)
    (hpgroup : IsPGroup prime Source) (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) :
    Nat.card (Source ⧸ frattini Source) = Nat.card (Target ⧸ frattini Target) *
      Nat.card (quotient.ker.map (QuotientGroup.mk' (frattini Source))) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (frattiniQuotientMap quotient hsurjective).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (frattiniQuotientMap quotient hsurjective)
        (frattiniQuotientMap_surjective quotient hsurjective)).toEquiv,
    frattiniQuotientMap_ker hprime hpgroup quotient hsurjective]

theorem elementary_surjection_finrank {Source : Type groupUniverse} [CommGroup Source]
    [Finite Source] {Target : Type targetUniverse} [CommGroup Target] {prime : ℕ}
    (hprime : prime.Prime) [Module (ZMod prime) (Additive Source)]
    [Module (ZMod prime) (Additive Target)] (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) :
    Module.finrank (ZMod prime) (Additive Source) =
      Module.finrank (ZMod prime) (Additive Target) +
        Module.finrank (ZMod prime) ((quotient.toAdditive.toZModLinearMap prime).ker) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let linearMap := quotient.toAdditive.toZModLinearMap prime
  have hlinearSurjective : Function.Surjective linearMap := by
    intro vector
    obtain ⟨source, hsource⟩ := hsurjective vector.toMul
    exact ⟨Additive.ofMul source, congrArg Additive.ofMul hsource⟩
  have hformula := linearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hlinearSurjective,
    (Submodule.topEquiv (R := ZMod prime) (M := Additive Target)).finrank_eq] at hformula
  exact hformula.symm

@[expose] noncomputable def pGeneratorRank (prime : ℕ) (Ambient : Type groupUniverse) [Group Ambient] : ℕ :=
  Nat.log prime (Nat.card (Ambient ⧸ frattini Ambient))

theorem pGeneratorRank_eq_frattini_finrank {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) :
    let _ : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
    ∀ module : Module (ZMod prime) (Additive (Ambient ⧸ frattini Ambient)),
      let _ := module
      pGeneratorRank prime Ambient = Module.finrank (ZMod prime) (Additive (Ambient ⧸ frattini Ambient)) := by
  dsimp only
  let : Fact prime.Prime := ⟨hprime⟩
  let : NeZero prime := ⟨hprime.ne_zero⟩
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
  intro module
  let := module
  have hcard := Module.natCard_eq_pow_finrank
    (K := ZMod prime) (V := Additive (Ambient ⧸ frattini Ambient))
  have hfieldCard : Nat.card (ZMod prime) = prime := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hquotientCard : Nat.card (Additive (Ambient ⧸ frattini Ambient)) =
      Nat.card (Ambient ⧸ frattini Ambient) := Nat.card_congr Additive.ofMul.symm
  unfold pGeneratorRank
  rw [hquotientCard, hfieldCard] at hcard
  rw [hcard, Nat.log_pow hprime.one_lt]

theorem pGeneratorRank_le_generators {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (generators : Finset Ambient) (hgenerates : Subgroup.closure (generators : Set Ambient) = ⊤) :
    pGeneratorRank prime Ambient ≤ generators.card := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
  let module : Module (ZMod prime) (Additive (Ambient ⧸ frattini Ambient)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent hprime hpgroup)
  rw [pGeneratorRank_eq_frattini_finrank hprime hpgroup module]
  exact quotient_frattini_dimension_le_generators (prime := prime)
    (QuotientGroup.mk' (frattini Ambient)) (QuotientGroup.mk'_surjective _) generators hgenerates

theorem pGeneratorRank_generators {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) :
    ∃ generators : Finset Ambient, Subgroup.closure (generators : Set Ambient) = ⊤ ∧
      generators.card = pGeneratorRank prime Ambient := by
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
  let module : Module (ZMod prime) (Additive (Ambient ⧸ frattini Ambient)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent hprime hpgroup)
  obtain ⟨generators, hgenerates, hcard⟩ := exists_frattini_basis_generators hprime hpgroup module
  rw [← pGeneratorRank_eq_frattini_finrank hprime hpgroup module] at hcard
  exact ⟨generators, hgenerates,
    le_antisymm hcard (pGeneratorRank_le_generators hprime hpgroup generators hgenerates)⟩

theorem pGeneratorRank_extension {Source : Type groupUniverse} [Group Source] [Finite Source]
    {Target : Type targetUniverse} [Group Target] {prime : ℕ} (hprime : prime.Prime)
    (hpgroup : IsPGroup prime Source) (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) :
    pGeneratorRank prime Source = pGeneratorRank prime Target +
      Nat.log prime (Nat.card (quotient.ker.map (QuotientGroup.mk' (frattini Source)))) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Finite Target := Finite.of_surjective quotient hsurjective
  have hsourceP := hpgroup.to_quotient (frattini Source)
  have htargetP := (hpgroup.of_surjective quotient hsurjective).to_quotient (frattini Target)
  have hkernelP := hsourceP.to_subgroup (quotient.ker.map (QuotientGroup.mk' (frattini Source)))
  obtain ⟨sourceRank, hsourceCard⟩ := hsourceP.exists_card_eq
  obtain ⟨targetRank, htargetCard⟩ := htargetP.exists_card_eq
  obtain ⟨kernelRank, hkernelCard⟩ := hkernelP.exists_card_eq
  have hcard := frattini_extension_card hprime hpgroup quotient hsurjective
  rw [hsourceCard, htargetCard, hkernelCard, ← Nat.pow_add] at hcard
  have hranks : sourceRank = targetRank + kernelRank :=
    Nat.pow_right_injective hprime.two_le hcard
  unfold pGeneratorRank
  rw [hsourceCard, htargetCard, hkernelCard,
    Nat.log_pow hprime.one_lt, Nat.log_pow hprime.one_lt, Nat.log_pow hprime.one_lt, hranks]

theorem pGroup_nontrivial_log_card {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (Subgroup : Subgroup Ambient) (hnontrivial : Subgroup ≠ ⊥) :
    1 ≤ Nat.log prime (Nat.card Subgroup) := by
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨rank, hcard⟩ := (hpgroup.to_subgroup Subgroup).exists_card_eq
  have hrank : rank ≠ 0 := by
    intro hzero
    exact hnontrivial (Subgroup.card_eq_one.mp (by simpa only [hzero, pow_zero] using hcard))
  rw [hcard, Nat.log_pow hprime.one_lt]
  omega

theorem pGeneratorRank_drop_of_killed_element {Source : Type groupUniverse} [Group Source]
    [Finite Source] {Target : Type targetUniverse} [Group Target] {prime : ℕ}
    (hprime : prime.Prime) (hpgroup : IsPGroup prime Source) (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) (element : Source)
    (hkilled : quotient element = 1) (hnotFrattini : element ∉ frattini Source) :
    pGeneratorRank prime Target + 1 ≤ pGeneratorRank prime Source := by
  let Image := quotient.ker.map (QuotientGroup.mk' (frattini Source))
  have hnontrivial : Image ≠ ⊥ := by
    intro htrivial
    have hmem : (QuotientGroup.mk' (frattini Source)) element ∈ Image :=
      Subgroup.mem_map.mpr ⟨element, hkilled, rfl⟩
    rw [htrivial] at hmem
    have hzero := Subgroup.mem_bot.mp hmem
    exact hnotFrattini ((QuotientGroup.eq_one_iff element).mp hzero)
  have hpositive := pGroup_nontrivial_log_card hprime
    (hpgroup.to_quotient (frattini Source)) Image hnontrivial
  rw [pGeneratorRank_extension hprime hpgroup quotient hsurjective]
  exact Nat.add_le_add_left hpositive _

theorem commutative_frattini_eq_power_range {Ambient : Type groupUniverse} [CommGroup Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) :
    frattini Ambient = (powMonoidHom prime : Ambient →* Ambient).range := by
  let powerMap := (powMonoidHom prime : Ambient →* Ambient)
  apply le_antisymm
  · have hexponent : ∀ element : Ambient ⧸ powerMap.range, element ^ prime = 1 := by
      intro element
      obtain ⟨source, rfl⟩ := QuotientGroup.mk'_surjective powerMap.range element
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨source, rfl⟩
    let : Module (ZMod prime) (Additive (Ambient ⧸ powerMap.range)) := elementaryZModModule hexponent
    have hle := elementary_quotient_kills_frattini hprime (QuotientGroup.mk' powerMap.range)
      (QuotientGroup.mk'_surjective powerMap.range)
    rwa [QuotientGroup.ker_mk'] at hle
  · intro element helement
    obtain ⟨source, rfl⟩ := helement
    exact pGroup_pow_mem_frattini hprime hpgroup source

theorem elementary_pGeneratorRank_eq_log_card {Ambient : Type groupUniverse} [CommGroup Ambient]
    {prime : ℕ} (hprime : prime.Prime) (hexponent : ∀ element : Ambient, element ^ prime = 1) :
    pGeneratorRank prime Ambient = Nat.log prime (Nat.card Ambient) := by
  let : Module (ZMod prime) (Additive Ambient) := elementaryZModModule hexponent
  unfold pGeneratorRank
  rw [elementary_frattini_eq_bot hprime,
    Nat.card_congr (QuotientGroup.quotientBot (G := Ambient)).toEquiv]

theorem elementary_image_generator_loss {Source : Type groupUniverse} [CommGroup Source]
    [Finite Source] {Target : Type targetUniverse} [CommGroup Target] {prime : ℕ}
    (hprime : prime.Prime) (hpgroup : IsPGroup prime Source) (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) (hexponent : ∀ element : Target, element ^ prime = 1)
    (element : Source) (hkilled : quotient element = 1)
    (hnotPower : element ∉ (powMonoidHom prime : Source →* Source).range) :
    Nat.log prime (Nat.card Target) + 1 ≤ pGeneratorRank prime Source := by
  rw [← elementary_pGeneratorRank_eq_log_card hprime hexponent]
  exact pGeneratorRank_drop_of_killed_element hprime hpgroup quotient hsurjective element hkilled
    ((commutative_frattini_eq_power_range hprime hpgroup).symm ▸ hnotPower)

end CFSG.LargeEvenClassification.Helpers
