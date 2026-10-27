module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGFam

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy)

theorem card_of_footeFamilyType {G : Type} [Group G] {K : Subgroup G} (hKt : FooteFamilyType K) :
    Nat.card (K ⧸ Open.fusionZStar K) = 2520 ∨
      ∃ q : ℕ, Odd q ∧ 5 ≤ q ∧ 2 * Nat.card (K ⧸ Open.fusionZStar K) = q * (q ^ 2 - 1) := by
  rcases hKt with hA | ⟨p, f, hp, hp2, -, h5, hm⟩
  · left
    obtain ⟨e⟩ := hA
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  · right
    refine ⟨p ^ f, (hp.odd_of_ne_two hp2).pow, h5, ?_⟩
    rw [GSThmB.card_of_lieModel_psl_two hp2 hm]
    exact RestrictedStd.Spor.two_mul_ordA_one (hp.odd_of_ne_two hp2).pow

theorem sixty_le_card_of_footeFamilyType {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hKt : FooteFamilyType K) : 60 ≤ Nat.card K := by
  have h1 : Nat.card (K ⧸ Open.fusionZStar K) ≤ Nat.card K :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  rcases card_of_footeFamilyType hKt with h | ⟨q, -, hq, h⟩
  · omega
  · have := RestrictedStd.Spor.cubic_mono hq
    norm_num at this
    omega

theorem not_footeOrder_20160 :
    ¬ (20160 = 2520 ∨ ∃ q : ℕ, Odd q ∧ 5 ≤ q ∧ 2 * 20160 = q * (q ^ 2 - 1)) := by
  rintro (h | ⟨q, hodd, -, hq⟩)
  · omega
  · rcases le_or_gt q 34 with hle | hlt
    · have := RestrictedStd.Spor.cubic_mono hle
      rcases Nat.lt_or_ge q 34 with h34 | h34
      · have := RestrictedStd.Spor.cubic_mono (show q ≤ 33 by omega)
        norm_num at this
        omega
      · obtain ⟨k, hk⟩ := hodd
        omega
    · have := RestrictedStd.Spor.cubic_mono (show 35 ≤ q by omega)
      norm_num at this
      omega

variable {X : Type} [Group X] [Finite X] {z : X} {K D : Subgroup X}

omit [Finite X] in
theorem eight_dvd_card_of_isDihedralTwoGroup (hDd : AschbacherTheorem3.IsDihedralTwoGroup D)
    (hD8 : 8 ≤ Nat.card D) : IsPGroup 2 D ∧ 8 ∣ Nat.card D := by
  obtain ⟨m, hm, ⟨eD⟩⟩ := hDd
  have hc : Nat.card D = 2 ^ m := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, ← pow_succ']
    congr 1
    omega
  refine ⟨IsPGroup.of_card hc, ?_⟩
  rw [hc] at hD8 ⊢
  have h3 : 3 ≤ m := by
    by_contra h
    have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact Nat.pow_dvd_pow 2 h3

theorem card_mul_card_le_of_coreActionKernel (hK : IsTwoComponentAt z K)
    (hKs : IsSimpleGroup (K ⧸ pPrimeCore 2 K))
    (hD : D ≤ centralizer ({z} : Set X) ⊓ coreActionKernel K) (hD2 : IsPGroup 2 D) :
    Nat.card D * Nat.card K ≤ Nat.card (centralizer ({z} : Set X)) := by
  have hKna : ∃ a b : K ⧸ pPrimeCore 2 K, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := isQuasisimple_quotient_of_isPComponent hK.2.1 hK.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hDK : ∀ x ∈ D, x ∈ K → x = 1 := by
    intro x hxD hxK
    have hc : (QuotientGroup.mk (⟨x, hxK⟩ : K) : K ⧸ pPrimeCore 2 K) ∈
        center (K ⧸ pPrimeCore 2 K) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨o, ho, hoe⟩ := (mem_inf.mp (hD hxD)).2.2 g g.2
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have h1 : (g * ⟨x, hxK⟩)⁻¹ * (⟨x, hxK⟩ * g) = o⁻¹ := by
        apply Subtype.ext
        rw [coe_inv, show ((o : K) : X) = K.subtype o from rfl, hoe]
        simp only [coe_mul, coe_inv]
        group
      rw [h1]
      exact inv_mem ho
    rw [center_eq_bot_of_isSimpleGroup hKna, mem_bot, QuotientGroup.eq_one_iff] at hc
    have hodd : Nat.Coprime 2 (orderOf (⟨x, hxK⟩ : K)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hc) pPrimeCore_coprime_card
    obtain ⟨k, hk⟩ := hD2 ⟨x, hxD⟩
    have hdvd : orderOf x ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      exact congrArg Subtype.val hk
    rw [Subgroup.orderOf_mk] at hodd
    have h1 : orderOf x = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hodd.symm) hdvd
    exact orderOf_eq_one_iff.mp h1
  let f : ↥D × ↥K → ↥(centralizer ({z} : Set X)) := fun p =>
    ⟨p.1 * p.2, mul_mem (mem_inf.mp (hD p.1.2)).1 (hK.2.1 p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨d, k⟩ ⟨d', k'⟩ h
    have h1 : (d : X) * k = d' * k' := congrArg Subtype.val h
    have h2 : (d' : X)⁻¹ * d = k' * (k : X)⁻¹ := by
      calc (d' : X)⁻¹ * d = (d' : X)⁻¹ * (d * k) * (k : X)⁻¹ := by group
        _ = (d' : X)⁻¹ * (d' * k') * (k : X)⁻¹ := by rw [h1]
        _ = k' * (k : X)⁻¹ := by group
    have h3 := hDK _ (mul_mem (inv_mem d'.2) d.2) (h2 ▸ mul_mem k'.2 (inv_mem k.2))
    have hdd : d = d' := Subtype.ext (by
      calc (d : X) = d' * ((d' : X)⁻¹ * d) := by group
        _ = d' := by rw [h3, mul_one])
    have hkk : k = k' := Subtype.ext (by
      calc (k : X) = (d : X)⁻¹ * (d * k) := by group
        _ = (d' : X)⁻¹ * (d' * k') := by rw [h1, hdd]
        _ = k' := by group)
    rw [hdd, hkk]
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective f hf

theorem false_of_card_centralizer_lt (hK : IsTwoComponentAt z K)
    (hKs : IsSimpleGroup (K ⧸ pPrimeCore 2 K)) (hKt : FooteFamilyType K)
    (hD : D ≤ centralizer ({z} : Set X) ⊓ coreActionKernel K)
    (hDd : AschbacherTheorem3.IsDihedralTwoGroup D) (hD8 : 8 ≤ Nat.card D)
    (h : Nat.card (centralizer ({z} : Set X)) < 480) : False := by
  have h1 := card_mul_card_le_of_coreActionKernel hK hKs hD
    (eight_dvd_card_of_isDihedralTwoGroup hDd hD8).1
  have h2 := sixty_le_card_of_footeFamilyType hKt
  have h3 : 8 * 60 ≤ Nat.card D * Nat.card K := Nat.mul_le_mul hD8 h2
  omega

theorem isComponent_of_oddCore (hK : IsTwoComponentAt z K)
    (hcore : CFSG.oddCore (centralizer ({z} : Set X)) = ⊥) :
    IsComponent (K.subgroupOf (centralizer ({z} : Set X))) ∧ pPrimeCore 2 K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : IsComponent (K.subgroupOf (centralizer ({z} : Set X))) :=
    ⟨Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hK.2.2,
      hK.2.2.choose_spec.2.1⟩
  refine ⟨hB, ?_⟩
  have hL0 : pPrimeCore 2 ↥(K.subgroupOf (centralizer ({z} : Set X))) = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 _ hB.2,
      ← Sporadic.HeldB.oddCore_eq_pPrimeCore_two', hcore, bot_subgroupOf]
  rw [← pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hK.2.1), hL0, Subgroup.map_bot]

theorem simple_of_oddCore (hK : IsTwoComponentAt z K) (hKs : IsSimpleGroup (K ⧸ pPrimeCore 2 K))
    (hKt : FooteFamilyType K) (hcore : CFSG.oddCore (centralizer ({z} : Set X)) = ⊥) :
    IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧ Open.fusionZStar K = ⊥ := by
  obtain ⟨-, hOK⟩ := isComponent_of_oddCore hK hcore
  let e : K ≃* K ⧸ pPrimeCore 2 K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hOK.symm)
  have hs : IsSimpleGroup K := e.isSimpleGroup
  have hna : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := isQuasisimple_quotient_of_isPComponent hK.2.1 hK.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  refine ⟨hs, hna, ?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Open.fusionZStar K) with h | h
  · exact h
  · exfalso
    have h60 : 60 ≤ Nat.card (K ⧸ Open.fusionZStar K) := by
      rcases card_of_footeFamilyType hKt with h1 | ⟨q, -, hq, h1⟩
      · omega
      · have := RestrictedStd.Spor.cubic_mono hq
        norm_num at this
        omega
    have : Subsingleton (K ⧸ Open.fusionZStar K) := QuotientGroup.subsingleton_iff.mpr h
    rw [Nat.card_unique] at h60
    omega

omit [Finite X] in
theorem le_centralizer_of_pPrimeCore_eq_bot (hOK : pPrimeCore 2 K = ⊥)
    (hD : D ≤ centralizer ({z} : Set X) ⊓ coreActionKernel K) :
    D ≤ centralizer ({z} : Set X) ⊓ centralizer (K : Set X) := by
  intro d hd
  refine mem_inf.mpr ⟨(mem_inf.mp (hD hd)).1, mem_centralizer_iff.mpr fun k hk => ?_⟩
  obtain ⟨-, hdK⟩ := (mem_inf.mp (hD hd)).2
  have h1 := hdK k hk
  rw [hOK, Subgroup.map_bot, mem_bot] at h1
  calc k * d = d * (k * (k⁻¹ * d⁻¹ * k * d)) := by group
    _ = d * k := by rw [h1, mul_one]

theorem smallCentralQuotient_of_oddCore (hK : IsTwoComponentAt z K)
    (hKs : IsSimpleGroup (K ⧸ pPrimeCore 2 K)) (hKt : FooteFamilyType K)
    (hcore : CFSG.oddCore (centralizer ({z} : Set X)) = ⊥) :
    RestrictedStd.SmallCentralQuotient ↥(K.subgroupOf (centralizer ({z} : Set X))) ∧
      Nat.card (↥(K.subgroupOf (centralizer ({z} : Set X))) ⧸
        center ↥(K.subgroupOf (centralizer ({z} : Set X)))) =
        Nat.card (K ⧸ Open.fusionZStar K) := by
  obtain ⟨hs, hna, hZ⟩ := simple_of_oddCore hK hKs hKt hcore
  set B := K.subgroupOf (centralizer ({z} : Set X)) with hBdef
  let eB : B ≃* K := subgroupOfEquivOfLe hK.2.1
  have : IsSimpleGroup B := eB.isSimpleGroup
  have hBna : ∃ a b : B, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨eB.symm a, eB.symm b, fun h => hab (eB.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hZB : center B = ⊥ := center_eq_bot_of_isSimpleGroup hBna
  let e : B ⧸ center B ≃* K ⧸ Open.fusionZStar K :=
    (((QuotientGroup.quotientMulEquivOfEq hZB).trans QuotientGroup.quotientBot).trans eB).trans
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm))
  refine ⟨?_, Nat.card_congr e.toEquiv⟩
  rcases hKt with hA | ⟨p, f, hp, hp2, hf, h5, hm⟩
  · obtain ⟨e7⟩ := hA
    exact Or.inr (Or.inl ⟨e.trans e7⟩)
  · exact Or.inl ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm⟩

theorem false_of_compsSatisfy_not_small (hK : IsTwoComponentAt z K)
    (hKs : IsSimpleGroup (K ⧸ pPrimeCore 2 K)) (hKt : FooteFamilyType K)
    (hcore : CFSG.oddCore (centralizer ({z} : Set X)) = ⊥)
    (h : CompsSatisfy (centralizer ({z} : Set X))
      fun Y _ => ¬ RestrictedStd.SmallCentralQuotient Y) : False :=
  h _ (isComponent_of_oddCore hK hcore).1 (smallCentralQuotient_of_oddCore hK hKs hKt hcore).1

theorem false_of_component_card (hK : IsTwoComponentAt z K)
    (hKs : IsSimpleGroup (K ⧸ pPrimeCore 2 K)) (hKt : FooteFamilyType K)
    (hcore : CFSG.oddCore (centralizer ({z} : Set X)) = ⊥)
    (h : ∀ B : Subgroup (centralizer ({z} : Set X)), IsComponent B →
      Nat.card (B ⧸ center B) = 20160) : False := by
  have h1 := h _ (isComponent_of_oddCore hK hcore).1
  rw [(smallCentralQuotient_of_oddCore hK hKs hKt hcore).2] at h1
  rcases card_of_footeFamilyType hKt with h2 | ⟨q, hq, h5, h2⟩
  · exact not_footeOrder_20160 (Or.inl (h1 ▸ h2))
  · exact not_footeOrder_20160 (Or.inr ⟨q, hq, h5, h1 ▸ h2⟩)

theorem false_of_le_of_not_eight_dvd (hK : IsTwoComponentAt z K)
    (hcore : CFSG.oddCore (centralizer ({z} : Set X)) = ⊥)
    (hD : D ≤ centralizer ({z} : Set X) ⊓ coreActionKernel K)
    (hDd : AschbacherTheorem3.IsDihedralTwoGroup D) (hD8 : 8 ≤ Nat.card D) {H : Subgroup X}
    (hH : centralizer ({z} : Set X) ⊓ centralizer (K : Set X) ≤ H) (h : ¬ 8 ∣ Nat.card H) :
    False := by
  have hDH := (le_centralizer_of_pPrimeCore_eq_bot (isComponent_of_oddCore hK hcore).2 hD).trans hH
  exact h ((eight_dvd_card_of_isDihedralTwoGroup hDd hD8).2.trans (Subgroup.card_dvd_of_le hDH))

theorem oddCore_centralizer_eq_bot_of_sporadicOddCoreFree {s : TauCeti.SporadicName}
    (hs : CatalogueU.SporadicOddCoreFree s) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* Blueprint.NativeSporadic.Carrier s) {t : S}
    (ht : orderOf t = 2) : CFSG.oddCore (centralizer ({t} : Set S)) = ⊥ := by
  have hF : CFSG.generalizedFitting S = ⊤ :=
    (CFSG.generalizedFitting_eq_componentClassification S).trans
      CatLeaf.generalizedFitting_subgroup_eq_top_of_simple
  let eF : CFSG.generalizedFitting S ≃* S := (MulEquiv.subgroupCongr hF).trans topEquiv
  have : IsSimpleGroup (CFSG.generalizedFitting S) := eF.isSimpleGroup
  refine hs S inferInstance ?_ ⟨eF.trans e⟩ t ht
  obtain ⟨a, b, hab⟩ := hna
  exact ⟨eF.symm a, eF.symm b, fun h => hab (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩

theorem endKnownGroupsInputOn_of_false {C : ∀ (Y : Type) [Group Y], Prop}
    (h : ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → C Y → ∀ (z : Y) (K D : Subgroup Y),
      IsTwoComponentAt z K → IsSimpleGroup (K ⧸ pPrimeCore 2 K) → FooteFamilyType K →
      D ≤ centralizer ({z} : Set Y) ⊓ coreActionKernel K →
      AschbacherTheorem3.IsDihedralTwoGroup D → 8 ≤ Nat.card D → False) :
    EndKnownGroupsInputOn C := by
  intro Y _ _ hY hC z t K P D hK _ hKs hKt _ _ _ _ _ _ hD _ hDd hD8 _ _
  exact (h Y hY hC z K D hK hKs hKt hD hDd hD8).elim

end CFSG.ComponentClassification.Foote5
