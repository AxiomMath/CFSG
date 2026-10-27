module

public import CFSG.CharacterTheory.Semidihedral.Local.FourGroupCyclingOddControlSupport
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem four_group_cycling_normal_subgroup_controls_invariant_odd_subgroups (n : ℕ)
    (hn : 4 ≤ n) (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) (H A V : Subgroup G)
    (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal) (hVA : V ≤ A) [IsKleinFour V] (t : G)
    (htV : t ∈ V) (ht1 : t ≠ 1)
    (htc : (QuotientGroup.mk (⟨t, hVA htV⟩ : A) : A ⧸ pPrimeCore 2 A) ∈
      Subgroup.center (A ⧸ pPrimeCore 2 A))
    (g : G) (hgH : g ∈ H) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hg : ∀ v ∈ V, v ≠ 1 → g * v * g⁻¹ ≠ v) :
    let R₀ := (pPrimeCore 2 A).map A.subtype
    let R := (pPrimeCore 2 H).map H.subtype
    let barV := (V.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H))
    (∃ P : Sylow 2 A, (P : Subgroup A) = V.subgroupOf A) ∧ R₀ ⊔ V = A ∧
      R₀ ⊔ (H ⊓ Subgroup.normalizer (V : Set G)) = H ∧ R₀ ≤ R ∧ barV.Normal ∧
      IsKleinFour barV ∧ Subgroup.centralizer (barV : Set (H ⧸ pPrimeCore 2 H)) = barV ∧
      ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → V ≤ Subgroup.normalizer (X : Set G) →
        X ≤ R := by
  intro R₀ R barV
  have hVH : V ≤ H := hVA.trans hAH
  have hHA : H ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mp hAn
  have hHR₀ : H ≤ Subgroup.normalizer (R₀ : Set G) := fun h hh =>
    mem_normalizer_map_pPrimeCore 2 (hHA hh)
  have hR₀A : R₀ ≤ A := Subgroup.map_subtype_le _
  have hR₀H : R₀ ≤ H := hR₀A.trans hAH
  have hR₀cop : Nat.Coprime 2 (Nat.card R₀) := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact pPrimeCore_coprime_card
  have hR₀R : R₀ ≤ R := le_map_pPrimeCore_of_le_normalizer 2 hR₀H hHR₀ hR₀cop
  have htcomm : ∀ a ∈ A, t * a * t⁻¹ * a⁻¹ ∈ R₀ := fun a ha =>
    commutator_mem_of_mem_center _ (hVA htV) htc ha
  have huV : g * t * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgV t).mp htV
  have hu1 : g * t * g⁻¹ ≠ 1 := fun h => ht1 (by
    have h' : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [h', h]
    group)
  have htu : t ≠ g * t * g⁻¹ := fun h => hg t htV ht1 h.symm
  have hucomm : ∀ a ∈ A, g * t * g⁻¹ * a * (g * t * g⁻¹)⁻¹ * a⁻¹ ∈ R₀ := fun a ha =>
    conj_commutator_mem (hHA hgH) (hHR₀ hgH) htcomm ha
  have hVcomm : ∀ v ∈ V, ∀ a ∈ A, v * a * v⁻¹ * a⁻¹ ∈ R₀ := by
    intro v hv a ha
    rcases kleinFour_mem_cases V htV huV ht1 hu1 htu hv with rfl | rfl | rfl | rfl
    · exact mul_commutator_mem (hHR₀ (hVH htV)) htcomm hucomm ha
    · exact htcomm a ha
    · exact hucomm a ha
    · simp
  have hV4 : Nat.card V = 4 := IsKleinFour.card_four
  have hVA2 : IsPGroup 2 (V.subgroupOf A) := IsPGroup.of_card (n := 2) (by
    rw [card_subgroupOf_eq, inf_eq_left.mpr hVA, hV4]; norm_num)
  obtain ⟨T, hVT⟩ := hVA2.exists_le_sylow
  have hT : (T : Subgroup A) = V.subgroupOf A :=
    sylow_eq_of_commutator_mem hn S f hVA hVcomm T hVT
  have hA : R₀ ⊔ V = A := map_pPrimeCore_sup_eq hVA T hT hVcomm
  have hcardV : Nat.card V = 2 ^ (Nat.card A).factorization 2 := by
    rw [← Sylow.card_eq_multiplicity T, hT, card_subgroupOf_eq, inf_eq_left.mpr hVA]
  have hVM : V ≤ H ⊓ Subgroup.normalizer (V : Set G) := le_inf hVH Subgroup.le_normalizer
  have hH : R₀ ⊔ (H ⊓ Subgroup.normalizer (V : Set G)) = H := by
    have h := sup_inf_normalizer_eq hAH hAn hVA hcardV
    rwa [← hA, sup_assoc, sup_eq_right.mpr hVM] at h
  have hqsurj : Function.Surjective (QuotientGroup.mk' (pPrimeCore 2 H)) :=
    QuotientGroup.mk'_surjective _
  have hRcop : ¬ 2 ∣ Nat.card (pPrimeCore 2 H) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
  have hVH4 : Nat.card (V.subgroupOf H) = 4 := by
    rw [card_subgroupOf_eq, inf_eq_left.mpr hVH, hV4]
  have hVH2 : IsPGroup 2 (V.subgroupOf H) := IsPGroup.of_card (n := 2) (by rw [hVH4]; norm_num)
  have hR₀ker : R₀.subgroupOf H ≤ pPrimeCore 2 H := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hR₀R (Subgroup.mem_subgroupOf.mp hx)
    rwa [← Subtype.ext hyx]
  have hR₀bar : (R₀.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hR₀ker
  have hbarA : (A.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) = barV := by
    rw [← hA, Subgroup.subgroupOf_sup hR₀H hVH, Subgroup.map_sup, hR₀bar, bot_sup_eq]
  have hbarVn : barV.Normal := by
    rw [← hbarA]
    exact hAn.map _ hqsurj
  have hinj : Function.Injective
      ((QuotientGroup.mk' (pPrimeCore 2 H)).subgroupMap (V.subgroupOf H)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : QuotientGroup.mk' (pPrimeCore 2 H) (x : H) = 1 := congrArg Subtype.val hx
    have hx1 : (x : H) ∈ pPrimeCore 2 H := (QuotientGroup.eq_one_iff _).mp hx'
    have hcop : Nat.Coprime (Nat.card (V.subgroupOf H)) (Nat.card (pPrimeCore 2 H)) := by
      rw [hVH4, show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left 2 pPrimeCore_coprime_card
    exact Subtype.ext (Subgroup.disjoint_def.mp (Subgroup.disjoint_of_coprime_natCard hcop) x.2 hx1)
  have hbarK : IsKleinFour barV := isKleinFour_of_mulEquiv
    ((Subgroup.subgroupOfEquivOfLe hVH).symm.trans (MulEquiv.ofBijective _
      ⟨hinj, (QuotientGroup.mk' (pPrimeCore 2 H)).subgroupMap_surjective _⟩))
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  obtain ⟨S', hVS'⟩ := hV2.exists_le_sylow
  obtain ⟨-, hZK, -, hcomm, -⟩ := four_and_quaternion_eight_local_normalizer_quotients n hn S'
    (f.trans (Sylow.equiv S S')) V hVS' (Or.inl inferInstance)
  have hKnorm : ∀ m ∈ Subgroup.normalizer (V : Set G), m ∈ Subgroup.normalizer
      (((CFSG.oddCore (Subgroup.normalizer (V : Set G))).map
        (Subgroup.normalizer (V : Set G)).subtype : Subgroup G) : Set G) := fun m hm =>
    mem_normalizer_map_of_normal _ hm
  have hZV : (Subgroup.center V).map V.subtype ≤ V := Subgroup.map_subtype_le _
  have hdec : ∀ c ∈ Subgroup.centralizer (V : Set G), ∃ z ∈ V,
      ∃ k ∈ (CFSG.oddCore (Subgroup.normalizer (V : Set G))).map
        (Subgroup.normalizer (V : Set G)).subtype, z * k = c := by
    intro c hc
    rw [← hZK] at hc
    have hc' : c ∈ (((Subgroup.center V).map V.subtype ⊔
        (CFSG.oddCore (Subgroup.normalizer (V : Set G))).map
          (Subgroup.normalizer (V : Set G)).subtype : Subgroup G) : Set G) := hc
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      fun z hz => hKnorm z (Subgroup.le_normalizer (hZV hz))] at hc'
    obtain ⟨z, hz, k, hk, rfl⟩ := Set.mem_mul.mp hc'
    exact ⟨z, hZV hz, k, hk, rfl⟩
  have hMtop : ((H ⊓ Subgroup.normalizer (V : Set G)).subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 H)) = ⊤ := by
    have h1 : (R₀ ⊔ (H ⊓ Subgroup.normalizer (V : Set G))).subgroupOf H = ⊤ := by
      rw [hH]
      exact Subgroup.subgroupOf_self H
    rw [Subgroup.subgroupOf_sup hR₀H inf_le_left] at h1
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (pPrimeCore 2 H))) h1
    rwa [Subgroup.map_sup, hR₀bar, bot_sup_eq,
      Subgroup.map_top_of_surjective _ hqsurj] at h2
  have hDnorm : (((CFSG.oddCore (Subgroup.normalizer (V : Set G))).map
      (Subgroup.normalizer (V : Set G)).subtype).subgroupOf H |>.map
        (QuotientGroup.mk' (pPrimeCore 2 H))).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hMtop]
    refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map _)
    intro m hm
    rw [Subgroup.mem_subgroupOf] at hm
    have hmK := hKnorm m hm.2
    rw [Subgroup.mem_normalizer_iff] at hmK ⊢
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hmK x
  have hDcop : Nat.Coprime 2 (Nat.card (((CFSG.oddCore (Subgroup.normalizer (V : Set G))).map
      (Subgroup.normalizer (V : Set G)).subtype).subgroupOf H |>.map
        (QuotientGroup.mk' (pPrimeCore 2 H)))) := by
    have hKodd : Nat.Coprime 2 (Nat.card ((CFSG.oddCore (Subgroup.normalizer (V : Set G))).map
        (Subgroup.normalizer (V : Set G)).subtype)) := by
      rw [Subgroup.card_map_of_injective (Subgroup.normalizer (V : Set G)).subtype_injective,
        Nat.coprime_two_left]
      exact odd_card_oddCore _
    refine hKodd.coprime_dvd_right ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [card_subgroupOf_eq]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hDker : ((CFSG.oddCore (Subgroup.normalizer (V : Set G))).map
      (Subgroup.normalizer (V : Set G)).subtype).subgroupOf H ≤ pPrimeCore 2 H := by
    have hle : _ ≤ pPrimeCore 2 (H ⧸ pPrimeCore 2 H) := le_sSup ⟨hDnorm, hDcop⟩
    rw [pPrimeCore_quotient_self_eq_bot, le_bot_iff, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk'] at hle
    exact hle
  have hCV : (Subgroup.centralizer ((V.subgroupOf H : Subgroup H) : Set H)).map
      (QuotientGroup.mk' (pPrimeCore 2 H)) ≤ barV := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
    rw [centralizer_subgroupOf_eq hVH, Subgroup.mem_subgroupOf] at hc
    obtain ⟨z, hzV, k, hk, hzk⟩ := hdec c hc
    have hkH : k ∈ H := by
      have h' : k = z⁻¹ * c := by
        rw [← hzk]
        group
      rw [h']
      exact H.mul_mem (H.inv_mem (hVH hzV)) c.2
    have hk1 : QuotientGroup.mk' (pPrimeCore 2 H) ⟨k, hkH⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hDker (Subgroup.mem_subgroupOf.mpr hk))
    have hc' : c = ⟨z, hVH hzV⟩ * ⟨k, hkH⟩ := Subtype.ext hzk.symm
    rw [hc', map_mul, hk1, mul_one]
    exact ⟨⟨z, hVH hzV⟩, Subgroup.mem_subgroupOf.mpr hzV, rfl⟩
  have hcentral : Subgroup.centralizer (barV : Set (H ⧸ pPrimeCore 2 H)) = barV := by
    apply le_antisymm
    · exact (map_centralizer_eq_of_coprime 2 (pPrimeCore 2 H) hRcop (V.subgroupOf H)
        hVH2).symm.le.trans hCV
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact kleinFour_mul_comm barV hy hx
  refine ⟨⟨T, hT⟩, hA, hH, hR₀R, hbarVn, hbarK, hcentral, ?_⟩
  intro X hXH hXodd hVX
  have hXcop : Nat.Coprime (Nat.card ((X.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H))))
      (Nat.card barV) := by
    rw [hbarK.card_four, show (4 : ℕ) = 2 ^ 2 by norm_num]
    refine Nat.Coprime.pow_right 2 (Nat.Coprime.coprime_dvd_left
      ((Subgroup.card_map_dvd _ _).trans ?_) (Nat.coprime_two_right.mpr hXodd))
    rw [card_subgroupOf_eq, inf_eq_left.mpr hXH]
  have hdisj := Subgroup.disjoint_of_coprime_natCard hXcop
  have hXc : (X.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤
      Subgroup.centralizer (barV : Set (H ⧸ pPrimeCore 2 H)) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
    have hvx : v * x * v⁻¹ ∈ X.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (hVX (Subgroup.mem_subgroupOf.mp hv)) x).mp
        (Subgroup.mem_subgroupOf.mp hx)
    have hvbar : QuotientGroup.mk' (pPrimeCore 2 H) v ∈ barV := ⟨v, hv, rfl⟩
    have hc1 : QuotientGroup.mk' (pPrimeCore 2 H) v * QuotientGroup.mk' (pPrimeCore 2 H) x *
        (QuotientGroup.mk' (pPrimeCore 2 H) v)⁻¹ * (QuotientGroup.mk' (pPrimeCore 2 H) x)⁻¹ ∈
        (X.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) :=
      ⟨v * x * v⁻¹ * x⁻¹, (X.subgroupOf H).mul_mem hvx ((X.subgroupOf H).inv_mem hx), by
        simp only [map_mul, map_inv]⟩
    have hc2 : QuotientGroup.mk' (pPrimeCore 2 H) v * QuotientGroup.mk' (pPrimeCore 2 H) x *
        (QuotientGroup.mk' (pPrimeCore 2 H) v)⁻¹ * (QuotientGroup.mk' (pPrimeCore 2 H) x)⁻¹ ∈
        barV := by
      have h1 := hbarVn.conj_mem _ (barV.inv_mem hvbar) (QuotientGroup.mk' (pPrimeCore 2 H) x)
      have h2 := barV.mul_mem hvbar h1
      simpa only [mul_assoc] using h2
    exact mul_comm_of_mul_mul_inv_mul_inv_eq_one (Subgroup.disjoint_def.mp hdisj hc1 hc2)
  have hXbot : (X.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) = ⊥ :=
    le_bot_iff.mp fun y hy =>
      Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hdisj hy (hcentral.le (hXc hy)))
  have hXker : X.subgroupOf H ≤ pPrimeCore 2 H := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hXbot
    exact hXbot
  have h := Subgroup.map_mono (f := H.subtype) hXker
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXH] at h

end CFSG.Semidihedral.Local
