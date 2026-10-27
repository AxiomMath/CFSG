module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.Alternating.Multipliers.Small
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGBase
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.FooteLit.KG

open CFSG Subgroup CFSG.ComponentClassification.Foote5 CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.RestrictedStd
  CFSG.ComponentClassification.RestrictedStd.Spor

theorem eq_of_isSmallOrder_dvd {c q₁ N₀ : ℕ} (hc : 0 < c) (hq₁ : 2 * c < q₁ * (q₁ ^ 2 - 1))
    (hsmall : ∀ q < q₁, q % 2 = 1 → 5 ≤ q → q * (q ^ 2 - 1) / 2 ≠ N₀ →
      c % (q * (q ^ 2 - 1) / 2) ≠ 0)
    (h2520 : ¬ 2520 ∣ c) (h20160 : ¬ 20160 ∣ c) : ∀ N, IsSmallOrder N → N ∣ c → N = N₀ := by
  rintro N (rfl | rfl | ⟨q, hodd, h5, hq⟩) hN
  · exact absurd hN h2520
  · exact absurd hN h20160
  · rcases lt_or_ge q q₁ with hlt | hge
    · have hN' : N = q * (q ^ 2 - 1) / 2 := by omega
      by_contra hne
      exact hsmall q hlt (Nat.odd_iff.1 hodd) h5 (fun h => hne (hN'.trans h))
        (hN' ▸ Nat.mod_eq_zero_of_dvd hN)
    · have := cubic_mono hge
      have := Nat.le_of_dvd hc hN
      omega

theorem smallCentralQuotient_quot_of_footeFamilyType {G : Type} [Group G] {L : Subgroup G}
    (h : FooteFamilyType L) : SmallCentralQuotient (L ⧸ pPrimeCore 2 L) := by
  obtain ⟨e⟩ := nonempty_fusionZStar_quotient_equiv ↥L
  rcases h with he7 | ⟨p, n, hp, hp2, hn, h5, hm⟩
  · obtain ⟨e7⟩ := he7
    exact Or.inr (Or.inl ⟨e.symm.trans e7⟩)
  · exact Or.inl ⟨p, n, hp, hp2, hn, h5, LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩

theorem isSmallOrder_card_quot {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : FooteFamilyType L) :
    IsSmallOrder (Nat.card ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L))) ∧
      Nat.card ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L)) ∣ Nat.card L :=
  ⟨isSmallOrder_of_smallCentralQuotient (smallCentralQuotient_quot_of_footeFamilyType h),
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)⟩

theorem center_eq_bot_and_nonempty_alt5 {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hL : IsFooteComponent L) {c : ℕ} (hc : Nat.card L ∣ c)
    (h60 : ∀ N, IsSmallOrder N → N ∣ c → N = 60) :
    center (L ⧸ pPrimeCore 2 L) = ⊥ ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨⟨t, -, hLt, hLpc⟩, hfam, hrk⟩ := hL
  have hQ := isQuasisimple_quotient_of_isPComponent hLt hLpc
  obtain ⟨hsm, hdvd⟩ := isSmallOrder_card_quot hfam
  have h60' := h60 _ hsm (hdvd.trans hc)
  have : IsSimpleGroup ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L)) := hQ.2.1
  obtain ⟨e⟩ := QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60'
  have : Group.IsPerfect (L ⧸ pPrimeCore 2 L) := hQ.1
  have hZ2 : Nat.card (center (L ⧸ pPrimeCore 2 L)) ∣ 2 := by
    have h := card_center_dvd_card_hopfMultiplier e
    rwa [Alternating.Multipliers.hopfMultiplier_alternatingGroup_five.2] at h
  have hZ : center (L ⧸ pPrimeCore 2 L) = ⊥ := by
    by_contra hne
    have := pRank_le_one_of_center_ne_bot hQ hfam (Nat.le_of_dvd two_pos hZ2) hne
    omega
  exact ⟨hZ, ⟨QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans e)⟩⟩

theorem pPrimeCore_eq_bot_of_isTwoComponentAt {G : Type} [Group G] [Finite G] {t : G}
    {L : Subgroup G} (ht : IsTwoComponentAt t L)
    (hodd : pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥) : pPrimeCore 2 L = ⊥ := by
  obtain ⟨-, hLC, hLp⟩ := ht
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := L.subgroupOf (centralizer ({t} : Set G))
  have hOM : pPrimeCore 2 ↥M = ⊥ := by
    obtain ⟨hs, -, -⟩ :=
      (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).1 hLp
    have h1 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hs
    rw [hodd, inf_bot_eq] at h1
    exact (map_eq_bot_iff_of_injective _ M.subtype_injective).mp h1
  let e₀ : ↥L ≃* ↥M := (subgroupOfEquivOfLe hLC).symm
  have h1 := pPrimeCore_map_iso 2 e₀
  rw [hOM] at h1
  exact (map_eq_bot_iff_of_injective _ e₀.injective).mp h1

theorem commute_of_mem_coreActionKernel {G : Type} [Group G] {L : Subgroup G}
    (hO : pPrimeCore 2 L = ⊥) {g : G} (hg : g ∈ coreActionKernel L) {j : G} (hj : j ∈ L) :
    g * j = j * g := by
  have h1 := (mem_coreActionKernel.1 hg).2 j hj
  rw [hO, Subgroup.map_bot, mem_bot] at h1
  calc g * j = g * j * (j⁻¹ * g⁻¹ * j * g) := by rw [h1, mul_one]
    _ = j * g := by group

theorem map_conj_inf_centralizer_of_mem {M : Type*} [Group M] (H : Subgroup M) {g : M}
    (hg : g ∈ H) (r : M) :
    (H ⊓ centralizer ({r} : Set M)).map (MulAut.conj g).toMonoidHom =
      H ⊓ centralizer ({g * r * g⁻¹} : Set M) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨w, ⟨hwH, hw⟩, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem hg hwH) (H.inv_mem hg), ?_⟩
    calc g * w * g⁻¹ * (g * r * g⁻¹) = g * (w * r) * g⁻¹ := by group
      _ = g * (r * w) * g⁻¹ := by rw [hw]
      _ = g * r * g⁻¹ * (g * w * g⁻¹) := by group
  · rintro ⟨hyH, hy⟩
    refine ⟨g⁻¹ * y * g, ⟨H.mul_mem (H.mul_mem (H.inv_mem hg) hyH) hg, ?_⟩, by group⟩
    calc g⁻¹ * y * g * r = g⁻¹ * (y * (g * r * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * r * g⁻¹) * y) * g := by rw [hy]
      _ = r * (g⁻¹ * y * g) := by group

theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : center B = ⊥) : center A = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ center B := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx y']
  rw [h, mem_bot, map_eq_one_iff e e.injective] at hex
  exact mem_bot.mpr hex

theorem bddAbove_rank_set (H : Type*) [Group H] [Finite H] :
    BddAbove {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} := by
  refine ⟨Nat.card H, ?_⟩
  rintro r ⟨A, -, hA⟩
  have h1 : r < 2 ^ r := Nat.lt_two_pow_self
  have h2 : Nat.card A ≤ Nat.card H := Subgroup.card_le_card_group A
  change r ≤ Nat.card H
  omega

theorem exists_elemAb_card_pRank (H : Type*) [Group H] [Finite H] :
    ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ CFSG.pRank 2 H := by
  have hbot : IsElementaryAbelian 2 (⊥ : Subgroup H) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun _ => Subsingleton.elim _ _ }
  exact Nat.sSup_mem (s := {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧
    Nat.card A = 2 ^ r}) ⟨0, ⊥, hbot, by simp⟩ (bddAbove_rank_set H)

theorem pRank_le_of_not_dvd {G : Type} [Group G] [Finite G] {k : ℕ}
    (h : ¬ 2 ^ (k + 1) ∣ Nat.card G) : CFSG.pRank 2 G ≤ k := by
  apply csSup_le'
  rintro r ⟨A, -, hA⟩
  by_contra hr
  apply h
  have := Subgroup.card_subgroup_dvd_card A
  rw [hA] at this
  exact (pow_dvd_pow 2 (by omega)).trans this

theorem pRank_coreActionKernel_add_two_le {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hO : pPrimeCore 2 L = ⊥) (hZ : center L = ⊥) (hrk : CFSG.pRank 2 ↥L = 2) :
    CFSG.pRank 2 ↥(coreActionKernel L) + 2 ≤ CFSG.pRank 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hV, hVc⟩ := exists_elemAb_card_pRank ↥L
  obtain ⟨E, hE, hEc⟩ := exists_elemAb_card_pRank ↥(coreActionKernel L)
  rw [hrk] at hVc
  set V' := V.map L.subtype with hV'def
  set E' := E.map (coreActionKernel L).subtype with hE'def
  have hV' : IsElementaryAbelian 2 V' := IsElementaryAbelian.map_subtype
  have hE' : IsElementaryAbelian 2 E' := IsElementaryAbelian.map_subtype
  have hcomm : ∀ x ∈ E', ∀ y ∈ L, x * y = y * x := by
    rintro _ ⟨x, -, rfl⟩ y hy
    exact commute_of_mem_coreActionKernel hO x.2 hy
  have hVL : V' ≤ L := map_subtype_le V
  have hdisj : E' ⊓ V' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxV⟩ := mem_inf.mp hx
    have hxZ : (⟨x, hVL hxV⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (hcomm x hxE y y.2).symm
    rw [hZ, mem_bot] at hxZ
    exact mem_bot.mpr (congrArg Subtype.val hxZ)
  have hcomm' : ∀ (a : E') (b : V'), Commute (E'.subtype a) (V'.subtype b) := fun a b =>
    hcomm a a.2 b (hVL b.2)
  have hinj : Function.Injective (MonoidHom.noncommCoprod E'.subtype V'.subtype hcomm') :=
    (MonoidHom.noncommCoprod_injective _ _ hcomm').2 ⟨E'.subtype_injective,
      V'.subtype_injective, by rw [range_subtype, range_subtype, disjoint_iff]; exact hdisj⟩
  have hrange : (MonoidHom.noncommCoprod E'.subtype V'.subtype hcomm').range = E' ⊔ V' := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  have hEl : IsElementaryAbelian 2 ↥(E' ⊔ V') :=
    IsElementaryAbelian.sup_of_le_centralizer fun y hy =>
      mem_centralizer_iff.mpr fun x hx => hcomm x hx y (hVL hy)
  have hcard : Nat.card ↥(E' ⊔ V') = 2 ^ (CFSG.pRank 2 ↥(coreActionKernel L) + 2) := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
      card_map_of_injective (coreActionKernel L).subtype_injective,
      card_map_of_injective L.subtype_injective, hEc, hVc, pow_add]
  exact le_csSup (bddAbove_rank_set G) ⟨E' ⊔ V', hEl, hcard⟩

theorem footeKnownSmall_of_alt5 {G : Type} [Group G] [Finite G]
    {c : ℕ} (hodd : ∀ t : G, orderOf t = 2 → pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥)
    (hcard : ∀ t : G, orderOf t = 2 → Nat.card ↥(centralizer ({t} : Set G)) ∣ c)
    (h60 : ∀ N, IsSmallOrder N → N ∣ c → N = 60) (hrk : CFSG.pRank 2 G ≤ 3) :
    FooteKnownSmall G := by
  intro L hL
  obtain ⟨t, ht⟩ := hL.1
  have hO := pPrimeCore_eq_bot_of_isTwoComponentAt ht (hodd t ht.1)
  have hLc : Nat.card L ∣ c := (Subgroup.card_dvd_of_le ht.2.1).trans (hcard t ht.1)
  obtain ⟨hZQ, -⟩ := center_eq_bot_and_nonempty_alt5 hL hLc h60
  have hZ : center ↥L = ⊥ := center_eq_bot_of_mulEquiv
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hO.symm)) hZQ
  have := pRank_coreActionKernel_add_two_le hO hZ hL.2.2
  omega

end CFSG.ComponentClassification.FooteLit.KG
