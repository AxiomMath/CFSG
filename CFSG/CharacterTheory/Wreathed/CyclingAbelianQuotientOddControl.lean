module

public import CFSG.CharacterTheory.Wreathed.CyclingAbelianQuotientOddControlSupport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

public section

namespace CFSG.Wreathed

variable {G : Type*} [Group G] [Finite G]

theorem four_group_cycling_with_abelian_centralizer_quotient_controls_odd_subgroups
    (T : Subgroup G) [IsKleinFour T] (x y : G) (hxT : x ∈ T) (_hyT : y ∈ T)
    (hx : orderOf x = 2) (_hy : orderOf y = 2) (_hxy : x ≠ y) (a b : ℕ) (_ha : 1 ≤ a)
    (_hb : 1 ≤ b)
    (hCD : Nonempty (Subgroup.centralizer (T : Set G) ⧸
        pPrimeCore 2 (Subgroup.centralizer (T : Set G)) ≃*
      Multiplicative (ZMod (2 ^ a)) × Multiplicative (ZMod (2 ^ b))))
    (H A : Subgroup G) (hTH : T ≤ H) (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal)
    (hTA : T ≤ A)
    (hxc : (QuotientGroup.mk (⟨x, hTA hxT⟩ : A) : A ⧸ pPrimeCore 2 A) ∈
      Subgroup.center (A ⧸ pPrimeCore 2 A))
    (g : G) (hgH : g ∈ H) (hgT : g ∈ Subgroup.normalizer (T : Set G))
    (hg : ∀ v ∈ T, v ≠ 1 → g * v * g⁻¹ ≠ v) :
    let R₀ := (pPrimeCore 2 A).map A.subtype
    let R := (pPrimeCore 2 H).map H.subtype
    let barT := (T.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H))
    R₀ ≤ R ∧ ((T ⊔ R₀).subgroupOf H).Normal ∧
      R₀ ⊔ (H ⊓ Subgroup.normalizer (T : Set G)) = H ∧ barT.Normal ∧ IsKleinFour barT ∧
      IsPGroup 2 (Subgroup.centralizer (barT : Set (H ⧸ pPrimeCore 2 H))) ∧
      ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → T ≤ Subgroup.normalizer (X : Set G) →
        X ≤ R := by
  intro R₀ R barT
  obtain ⟨e⟩ := hCD
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have hT4 : Nat.card T = 4 := IsKleinFour.card_four
  have hTsq : ∀ t ∈ T, t ^ 2 = 1 := fun t ht => by
    have h := Monoid.pow_exponent_eq_one (⟨t, ht⟩ : T)
    rw [IsKleinFour.exponent_two] at h
    exact congrArg Subtype.val h
  have hHA : H ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mp hAn
  have hHR₀ : H ≤ Subgroup.normalizer (R₀ : Set G) := fun h hh =>
    Semidihedral.Local.mem_normalizer_map_pPrimeCore 2 (hHA hh)
  have hR₀A : R₀ ≤ A := Subgroup.map_subtype_le _
  have hR₀H : R₀ ≤ H := hR₀A.trans hAH
  have hR₀cop : Nat.Coprime 2 (Nat.card R₀) := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact pPrimeCore_coprime_card
  have hR₀R : R₀ ≤ R :=
    Semidihedral.Local.le_map_pPrimeCore_of_le_normalizer 2 hR₀H hHR₀ hR₀cop
  have hxcomm : ∀ w ∈ A, x * w * x⁻¹ * w⁻¹ ∈ R₀ := fun w hw =>
    Semidihedral.Local.commutator_mem_of_mem_center _ (hTA hxT) hxc hw
  have hTcomm : ∀ v ∈ T, ∀ w ∈ A, v * w * v⁻¹ * w⁻¹ ∈ R₀ :=
    commutator_mem_of_cycling T hxT hx1 (hTA.trans (hAH.trans hHR₀)) (hHA hgH) (hHR₀ hgH) hgT
      (hg x hxT hx1) hxcomm
  have hTA2 : IsPGroup 2 (T.subgroupOf A) := IsPGroup.of_card (n := 2) (by
    rw [Semidihedral.Local.card_subgroupOf_eq, inf_eq_left.mpr hTA, hT4]; norm_num)
  have hAcop : ¬ 2 ∣ Nat.card (pPrimeCore 2 A) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
  have hcentA : (Subgroup.centralizer ((T.subgroupOf A : Subgroup A) : Set A)).map
      (QuotientGroup.mk' (pPrimeCore 2 A)) = ⊤ := by
    rw [Semidihedral.Local.map_centralizer_eq_of_coprime 2 (pPrimeCore 2 A) hAcop _ hTA2,
      Subgroup.centralizer_eq_top_iff_subset]
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp (SetLike.mem_coe.mp hz)
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro w
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 A) w
    have hc : v * c * v⁻¹ * c⁻¹ ∈ pPrimeCore 2 A :=
      (Subgroup.mem_map_iff_mem A.subtype_injective).mp
        (hTcomm v (Subgroup.mem_subgroupOf.mp hv) c c.2)
    have h1 : QuotientGroup.mk' (pPrimeCore 2 A) (v * c * v⁻¹ * c⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hc
    simp only [map_mul, map_inv] at h1
    exact (Semidihedral.Local.mul_comm_of_mul_mul_inv_mul_inv_eq_one h1).symm
  have hAB : R₀ ⊔ (Subgroup.centralizer (T : Set G) ⊓ A) = A := by
    have h := Subgroup.comap_map_eq (QuotientGroup.mk' (pPrimeCore 2 A))
      (Subgroup.centralizer ((T.subgroupOf A : Subgroup A) : Set A))
    rw [hcentA, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    have h2 := congrArg (Subgroup.map A.subtype) h
    rw [Subgroup.map_sup, Semidihedral.Local.centralizer_subgroupOf_eq hTA,
      Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    rw [sup_comm]
    exact h2.symm
  have hDcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 (Subgroup.centralizer (T : Set G))).map
      (Subgroup.centralizer (T : Set G)).subtype)) := by
    rw [Subgroup.card_map_of_injective (Subgroup.centralizer (T : Set G)).subtype_injective]
    exact pPrimeCore_coprime_card
  have hDA : ((pPrimeCore 2 (Subgroup.centralizer (T : Set G))).map
      (Subgroup.centralizer (T : Set G)).subtype).subgroupOf A ≤ pPrimeCore 2 A :=
    subgroupOf_le_pPrimeCore_of_sup_eq 2 (M := Subgroup.centralizer (T : Set G) ⊓ A)
      inf_le_right le_rfl hAB
      (fun m hm => Semidihedral.Local.mem_normalizer_map_of_normal _ hm.1) hDcop
  have hTC : T ≤ Subgroup.centralizer (T : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.mpr fun s hs => Semidihedral.Local.kleinFour_mul_comm T hs ht
  have hTC2 : IsPGroup 2 (T.subgroupOf (Subgroup.centralizer (T : Set G))) :=
    IsPGroup.of_card (n := 2) (by
      rw [Semidihedral.Local.card_subgroupOf_eq, inf_eq_left.mpr hTC, hT4]; norm_num)
  have hThat4 : Nat.card ((T.subgroupOf (Subgroup.centralizer (T : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer (T : Set G))))) = 4 := by
    rw [← Nat.card_congr (mapMkPPrimeCoreEquiv 2 _ hTC2).toEquiv,
      Semidihedral.Local.card_subgroupOf_eq, inf_eq_left.mpr hTC, hT4]
  have hThat2 : ∀ r ∈ (T.subgroupOf (Subgroup.centralizer (T : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer (T : Set G)))), r ^ 2 = 1 := by
    intro r hr
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hr
    have ht2 : t ^ 2 = 1 := Subtype.ext (hTsq t (Subgroup.mem_subgroupOf.mp ht))
    rw [← map_pow, ht2, map_one]
  have hCD2 : IsPGroup 2 (Subgroup.centralizer (T : Set G) ⧸
      pPrimeCore 2 (Subgroup.centralizer (T : Set G))) := isPGroup_of_mulEquiv_prod a b e
  have hconjT : ∀ h ∈ H, ∀ t ∈ T, h * t * h⁻¹ ∈ T ⊔ R₀ := by
    intro h hh t ht
    have htA : h * t * h⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hHA hh) t).mp (hTA ht)
    have hmem : h * t * h⁻¹ ∈
        ((R₀ ⊔ (Subgroup.centralizer (T : Set G) ⊓ A) : Subgroup G) : Set G) := by
      rw [hAB]
      exact htA
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R₀ _
      (inf_le_right.trans (hAH.trans hHR₀))] at hmem
    obtain ⟨r, hr, c, hc, hrc⟩ := Set.mem_mul.mp hmem
    have hcC : c ∈ Subgroup.centralizer (T : Set G) := hc.1
    have hcA : c ∈ A := hc.2
    have hsq : r * c * (r * c) = 1 := by
      rw [hrc]
      calc h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
        _ = 1 := by rw [← pow_two, hTsq t ht, mul_one, mul_inv_cancel]
    have hc2 : c ^ 2 ∈ R₀ := by
      have key : c ^ 2 = c * r⁻¹ * c⁻¹ * r⁻¹ * (r * c * (r * c)) := by
        rw [pow_two]
        group
      rw [key, hsq, mul_one]
      exact R₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHR₀ (hAH hcA)) _).mp (R₀.inv_mem hr))
        (R₀.inv_mem hr)
    have hc2D : (⟨c, hcC⟩ : Subgroup.centralizer (T : Set G)) ^ 2 ∈
        pPrimeCore 2 (Subgroup.centralizer (T : Set G)) := by
      refine mem_of_pow_eq_one_of_isPGroup_quotient _ hCD2 hR₀cop (Subtype.ext ?_)
      have h1 : (c ^ 2) ^ Nat.card R₀ = 1 :=
        congrArg Subtype.val (pow_card_eq_one' (G := R₀) (x := ⟨c ^ 2, hc2⟩))
      exact h1
    have hcq : (QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer (T : Set G)))
        ⟨c, hcC⟩) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hc2D
    obtain ⟨t', ht', ht'c⟩ := Subgroup.mem_map.mp
      (mem_of_sq_eq_one_of_card_four a b e _ hThat4 hThat2 hcq)
    have ht'T : (t' : G) ∈ T := Subgroup.mem_subgroupOf.mp ht'
    have hdC : t'⁻¹ * ⟨c, hcC⟩ ∈ pPrimeCore 2 (Subgroup.centralizer (T : Set G)) :=
      QuotientGroup.eq.mp ht'c
    have hdA : (t' : G)⁻¹ * c ∈ A := A.mul_mem (A.inv_mem (hTA ht'T)) hcA
    have hdR : (t' : G)⁻¹ * c ∈ R₀ := by
      have h1 : (⟨(t' : G)⁻¹ * c, hdA⟩ : A) ∈ pPrimeCore 2 A :=
        hDA (Subgroup.mem_subgroupOf.mpr ⟨_, hdC, rfl⟩)
      exact ⟨_, h1, rfl⟩
    have hcTR : c ∈ T ⊔ R₀ := by
      have h' : c = (t' : G) * ((t' : G)⁻¹ * c) := by group
      rw [h']
      exact (T ⊔ R₀).mul_mem (Subgroup.mem_sup_left ht'T) (Subgroup.mem_sup_right hdR)
    rw [← hrc]
    exact (T ⊔ R₀).mul_mem (Subgroup.mem_sup_right hr) hcTR
  have hTR₀H : T ⊔ R₀ ≤ H := sup_le hTH hR₀H
  have hHTR : H ≤ Subgroup.normalizer ((T ⊔ R₀ : Subgroup G) : Set G) :=
    le_normalizer_of_conj_mem fun h hh z hz =>
      conj_mem_sup (hconjT h hh) (fun w hw => Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (hHR₀ hh) w).mp hw)) hz
  have hTRn : ((T ⊔ R₀).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTR₀H).mpr hHTR
  have hdisj : Disjoint R₀ T := Subgroup.disjoint_of_coprime_natCard (by
    rw [hT4, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 hR₀cop.symm)
  have hR₀odd : ¬ 2 ∣ Nat.card R₀ := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hR₀cop
  have hfac : Nat.card T = 2 ^ (Nat.card (R₀ ⊔ T : Subgroup G)).factorization 2 := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer R₀ T (hTH.trans hHR₀)
      hdisj, hT4, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hR₀odd, show (4 : ℕ) = 2 ^ 2 by norm_num,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same, zero_add]
  have hRTn : ((R₀ ⊔ T).subgroupOf H).Normal := by
    rw [sup_comm]
    exact hTRn
  have hTM : T ≤ H ⊓ Subgroup.normalizer (T : Set G) := le_inf hTH Subgroup.le_normalizer
  have hH : R₀ ⊔ (H ⊓ Subgroup.normalizer (T : Set G)) = H := by
    have h := Semidihedral.Local.sup_inf_normalizer_eq (sup_le hR₀H hTH) hRTn le_sup_right hfac
    rwa [sup_assoc, sup_eq_right.mpr hTM] at h
  have hDH : ((pPrimeCore 2 (Subgroup.centralizer (T : Set G))).map
      (Subgroup.centralizer (T : Set G)).subtype).subgroupOf H ≤ pPrimeCore 2 H :=
    subgroupOf_le_pPrimeCore_of_sup_eq 2 (M := H ⊓ Subgroup.normalizer (T : Set G))
      inf_le_left hR₀R hH (fun m hm => Semidihedral.Local.mem_normalizer_map_pPrimeCore 2
        (GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup T hm.2)) hDcop
  have hR₀ker : R₀.subgroupOf H ≤ pPrimeCore 2 H := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hR₀R (Subgroup.mem_subgroupOf.mp hz)
    rwa [← Subtype.ext hwz]
  have hR₀bar : (R₀.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hR₀ker
  have hbarTR : ((T ⊔ R₀).subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) = barT := by
    rw [Subgroup.subgroupOf_sup hTH hR₀H, Subgroup.map_sup, hR₀bar, sup_bot_eq]
  have hbarTn : barT.Normal := by
    rw [← hbarTR]
    exact hTRn.map _ (QuotientGroup.mk'_surjective _)
  have hTH2 : IsPGroup 2 (T.subgroupOf H) := IsPGroup.of_card (n := 2) (by
    rw [Semidihedral.Local.card_subgroupOf_eq, inf_eq_left.mpr hTH, hT4]; norm_num)
  have hbarK : IsKleinFour barT := Semidihedral.Local.isKleinFour_of_mulEquiv
    ((Subgroup.subgroupOfEquivOfLe hTH).symm.trans (mapMkPPrimeCoreEquiv 2 _ hTH2))
  have hHcop : ¬ 2 ∣ Nat.card (pPrimeCore 2 H) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
  have hcentT : Subgroup.centralizer (barT : Set (H ⧸ pPrimeCore 2 H)) =
      (Subgroup.centralizer ((T.subgroupOf H : Subgroup H) : Set H)).map
        (QuotientGroup.mk' (pPrimeCore 2 H)) :=
    (Semidihedral.Local.map_centralizer_eq_of_coprime 2 (pPrimeCore 2 H) hHcop _ hTH2).symm
  have hcentral : IsPGroup 2 (Subgroup.centralizer (barT : Set (H ⧸ pPrimeCore 2 H))) := by
    rw [hcentT]
    intro w
    obtain ⟨y', hy'⟩ := w
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy'
    rw [Semidihedral.Local.centralizer_subgroupOf_eq hTH, Subgroup.mem_subgroupOf] at hc
    obtain ⟨k, hk⟩ := hCD2 (QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer (T : Set G)))
      ⟨c, hc⟩)
    rw [← map_pow] at hk
    have h1 := (QuotientGroup.eq_one_iff _).mp hk
    have h2 : c ^ 2 ^ k ∈ ((pPrimeCore 2 (Subgroup.centralizer (T : Set G))).map
        (Subgroup.centralizer (T : Set G)).subtype).subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr ⟨_, h1, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change QuotientGroup.mk' (pPrimeCore 2 H) c ^ 2 ^ k = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hDH h2)
  refine ⟨hR₀R, hTRn, hH, hbarTn, hbarK, hcentral, ?_⟩
  intro X hXH hXodd hTX
  have hXodd' : Nat.Coprime (Nat.card ((X.subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 H)))) 2 := by
    refine Nat.Coprime.coprime_dvd_left ((Subgroup.card_map_dvd _ _).trans ?_)
      (Nat.coprime_two_right.mpr hXodd)
    rw [Semidihedral.Local.card_subgroupOf_eq, inf_eq_left.mpr hXH]
  have hTXH : T.subgroupOf H ≤ Subgroup.normalizer ((X.subgroupOf H : Subgroup H) : Set H) := by
    rw [Semidihedral.Local.normalizer_subgroupOf_eq hXH]
    exact fun t ht => Subgroup.mem_subgroupOf.mpr (hTX (Subgroup.mem_subgroupOf.mp ht))
  have hXc : (X.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤
      Subgroup.centralizer (barT : Set (H ⧸ pPrimeCore 2 H)) := by
    have := hbarTn
    refine le_centralizer_of_normal_of_coprime
      ((Subgroup.map_mono hTXH).trans (Subgroup.le_normalizer_map _)) ?_
    rw [hbarK.card_four, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 hXodd'
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hcentral
  have hcop : Nat.Coprime (Nat.card ((X.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H))))
      (Nat.card (Subgroup.centralizer (barT : Set (H ⧸ pPrimeCore 2 H)))) := by
    rw [hk]
    exact Nat.Coprime.pow_right k hXodd'
  have hXbot : (X.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) = ⊥ :=
    le_bot_iff.mp fun z hz => Subgroup.mem_bot.mpr
      (Subgroup.disjoint_def.mp (Subgroup.disjoint_of_coprime_natCard hcop) hz (hXc hz))
  have hXker : X.subgroupOf H ≤ pPrimeCore 2 H := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hXbot
    exact hXbot
  have h := Subgroup.map_mono (f := H.subtype) hXker
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXH] at h

end CFSG.Wreathed
