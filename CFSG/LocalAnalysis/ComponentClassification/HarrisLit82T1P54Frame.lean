module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45c
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TBLitConfig
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.Frame

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem exists_involution_lift {A B : Type*} [Group A] [Finite A] [Group B] (φ : A →* B)
    (hφ : ¬ 2 ∣ Nat.card φ.ker) {b : B} (hb : orderOf b = 2) (hbφ : b ∈ φ.range) :
    ∃ a : A, orderOf a = 2 ∧ φ a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, rfl⟩ := hbφ
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  obtain ⟨j, rfl⟩ := hm
  have hb2 : φ y ^ 2 = 1 := hb ▸ pow_orderOf_eq_one (φ y)
  set s := y ^ (2 * j + 1) with hs
  have hφs : φ s = φ y := by rw [hs, map_pow, pow_succ, pow_mul, hb2, one_pow, one_mul]
  have hsk' : s ^ 2 ^ k = 1 := by
    rw [hs, ← pow_mul, mul_comm (2 * j + 1), ← hkm, pow_orderOf_eq_one]
  have hsk : (s ^ 2) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm 2 (2 ^ k), pow_mul, hsk', one_pow]
  have hs2 : s ^ 2 ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hφs, hb2]
  have hd1 : orderOf (s ^ 2) ∣ Nat.card φ.ker := by
    have h := orderOf_dvd_natCard (⟨s ^ 2, hs2⟩ : φ.ker)
    rwa [Subgroup.orderOf_mk] at h
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsk)
  rw [hi] at hd1
  have hi0 : i = 0 := by
    by_contra h0
    exact hφ ((dvd_pow_self 2 h0).trans hd1)
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  refine ⟨s, orderOf_eq_prime hi fun h1 => ?_, hφs⟩
  rw [h1, map_one] at hφs
  rw [← hφs, orderOf_one] at hb
  exact absurd hb (by norm_num)

theorem fusionZStar_eq_center {Q : Type*} [Group Q] (hO : pPrimeCore 2 Q = ⊥) :
    Open.fusionZStar Q = center Q := by
  ext l
  rw [GSThmB.OddQuot.mem_fusionZStar_iff, hO, mem_center_iff]
  constructor
  · intro h m
    have h1 := h m
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  · intro h m
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (h m).symm

variable {X B : Type} [Group X] [Group B] [Finite X] [Finite B] {f : X →* B}

omit [Finite B] in
theorem map_centralizer (hf : Function.Surjective f) (hk : ¬ 2 ∣ Nat.card f.ker) {u : X}
    (hu : u * u = 1) : (centralizer ({u} : Set X)).map f = centralizer {f u} := by
  apply le_antisymm
  · intro q hq
    obtain ⟨c, hc, rfl⟩ := mem_map.mp hq
    rw [mem_centralizer_singleton_iff] at hc ⊢
    rw [← map_mul, ← map_mul, hc]
  · intro b hb
    obtain ⟨x, rfl⟩ := hf b
    rw [mem_centralizer_singleton_iff] at hb
    have hx : x⁻¹ * (u⁻¹ * x * u) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [mul_assoc (f u)⁻¹, hb, inv_mul_cancel_left, inv_mul_cancel]
    obtain ⟨c, hc, hxc⟩ := exists_mem_centralizer_of_inv_mul_conj_mem
      (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hk)) hu hx
    refine ⟨c, hc, ?_⟩
    have h1 := MonoidHom.mem_ker.mp hxc
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm

omit [Finite B] in
theorem exists_involution_lift_commute (hf : Function.Surjective f)
    (hk : ¬ 2 ∣ Nat.card f.ker) {t : X} (ht : t * t = 1) (htZ : f t ∈ center B) {b : B}
    (hb : orderOf b = 2) : ∃ u : X, orderOf u = 2 ∧ f u = b ∧ u * t = t * u := by
  have hbC : b ∈ (centralizer ({t} : Set X)).map f := by
    rw [map_centralizer hf hk ht, mem_centralizer_singleton_iff]
    exact mem_center_iff.mp htZ b
  obtain ⟨a, ha2, hab⟩ := exists_involution_lift (f.domRestrict (centralizer {t}))
    (GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict f hk _) hb (by
      obtain ⟨c, hc, rfl⟩ := mem_map.mp hbC
      exact MonoidHom.mem_range.mpr ⟨⟨c, hc⟩, rfl⟩)
  exact ⟨a, (Subgroup.orderOf_coe a).trans ha2, hab, mem_centralizer_singleton_iff.mp a.2⟩

omit [Finite X] [Finite B] in
theorem orderOf_map_eq_two (hk : ¬ 2 ∣ Nat.card f.ker) {u : X} (hu : orderOf u = 2) :
    orderOf (f u) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (by rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]) fun h1 => hk ?_
  have h2 := orderOf_dvd_natCard (⟨u, MonoidHom.mem_ker.mpr h1⟩ : f.ker)
  rwa [Subgroup.orderOf_mk, hu] at h2

theorem mem_fusionZStar_iff_map (hf : Function.Surjective f) (hk : ¬ 2 ∣ Nat.card f.ker)
    {x : X} : x ∈ Open.fusionZStar X ↔ f x ∈ Open.fusionZStar B := by
  rw [← GSThmB.OddQuot.comap_fusionZStar_of_surjective f hf hk, mem_comap]

theorem nonempty_quot_equivs_of_map_eq (hk : ¬ 2 ∣ Nat.card f.ker) {J : Subgroup X}
    {Y : Subgroup B} (h : J.map f = Y) :
    Nonempty (↥J ⧸ pPrimeCore 2 ↥J ≃* ↥Y ⧸ pPrimeCore 2 ↥Y) ∧
      Nonempty (↥J ⧸ Open.fusionZStar ↥J ≃* ↥Y ⧸ Open.fusionZStar ↥Y) := by
  subst h
  have hJ := GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap f hk J
  exact ⟨GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective (f.subgroupMap J)
      (f.subgroupMap_surjective J) hJ,
    GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective (f.subgroupMap J)
      (f.subgroupMap_surjective J) hJ⟩

theorem map_twoComponent (hf : Function.Surjective f) (hk : ¬ 2 ∣ Nat.card f.ker) {u : X}
    (hu : u * u = 1) {L : Subgroup X} (hL : IsTwoComponentIn L (centralizer {u})) :
    IsTwoComponentIn (L.map f) (centralizer {f u}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (f.subgroupMap (centralizer {u})) (f.subgroupMap_surjective _)
    (GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap f hk _)
  have h1 : IsPComponent 2
      ((L.subgroupOf (centralizer {u})).map (f.subgroupMap (centralizer {u}))) :=
    hbij.mapsTo ((isTwoComponentIn_iff hL.1).mp hL)
  rw [GSThmB.OddQuot.map_subgroupOf_subgroupMap f hL.1] at h1
  have h2 := (isTwoComponentIn_iff (map_mono hL.1)).mpr h1
  rwa [map_centralizer hf hk hu] at h2

theorem eq_of_map_eq (hk : ¬ 2 ∣ Nat.card f.ker) {u : X} {L L' : Subgroup X}
    (hL : IsTwoComponentIn L (centralizer {u})) (hL' : IsTwoComponentIn L' (centralizer {u}))
    (h : L.map f = L'.map f) : L = L' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (f.subgroupMap (centralizer {u})) (f.subgroupMap_surjective _)
    (GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap f hk _)
  have h1 : (L.subgroupOf (centralizer {u})).map (f.subgroupMap (centralizer {u})) =
      (L'.subgroupOf (centralizer {u})).map (f.subgroupMap (centralizer {u})) := by
    rw [GSThmB.OddQuot.map_subgroupOf_subgroupMap f hL.1,
      GSThmB.OddQuot.map_subgroupOf_subgroupMap f hL'.1, h]
  have h2 := hbij.injOn ((isTwoComponentIn_iff hL.1).mp hL) ((isTwoComponentIn_iff hL'.1).mp hL')
    h1
  rwa [Subgroup.subgroupOf_inj, inf_eq_left.mpr hL.1, inf_eq_left.mpr hL'.1] at h2

theorem exists_lift_twoComponent (hf : Function.Surjective f) (hk : ¬ 2 ∣ Nat.card f.ker)
    {u : X} (hu : u * u = 1) {Y : Subgroup B} (hY : IsTwoComponentIn Y (centralizer {f u})) :
    ∃ J : Subgroup X, IsTwoComponentIn J (centralizer {u}) ∧ J.map f = Y ∧
      (∀ w ∈ centralizer ({u} : Set X), (∃ k : ℕ, orderOf w = 2 ^ k) → f w ∈ Y → w ∈ J) ∧
      Nonempty (↥J ⧸ pPrimeCore 2 ↥J ≃* ↥Y ⧸ pPrimeCore 2 ↥Y) ∧
      Nonempty (↥J ⧸ Open.fusionZStar ↥J ≃* ↥Y ⧸ Open.fusionZStar ↥Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({u} : Set X) with hCdef
  have hC : C.map f = centralizer {f u} := map_centralizer hf hk hu
  obtain ⟨-, hlift, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (f.subgroupMap C) (f.subgroupMap_surjective C)
    (GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap f hk C)
  have hYle : Y ≤ C.map f := by
    rw [hC]
    exact hY.1
  have hYp : IsPComponent 2 (Y.subgroupOf (C.map f)) := by
    rw [hC]
    exact (isTwoComponentIn_iff hY.1).mp hY
  obtain ⟨hĴ, hĴmap⟩ := hlift _ hYp
  generalize hĴdef : closure {x : ↥C | x ∈ (Y.subgroupOf (C.map f)).comap (f.subgroupMap C) ∧
    ∃ k : ℕ, orderOf x = 2 ^ k} = Ĵ at hĴ hĴmap
  have hJsub : (Ĵ.map C.subtype).subgroupOf C = Ĵ :=
    comap_map_eq_self_of_injective C.subtype_injective Ĵ
  have hJ : IsTwoComponentIn (Ĵ.map C.subtype) C :=
    (isTwoComponentIn_iff (map_subtype_le Ĵ)).mpr (by rw [hJsub]; exact hĴ)
  have hJY : (Ĵ.map C.subtype).map f = Y := by
    rw [map_map, ← GSThmB.OddQuot.subtype_comp_subgroupMap f C, ← map_map, hĴmap,
      subgroupOf_map_subtype, inf_eq_left.mpr hYle]
  obtain ⟨e₁, e₂⟩ := nonempty_quot_equivs_of_map_eq hk hJY
  refine ⟨Ĵ.map C.subtype, hJ, hJY, fun w hw hw2 hwY => ?_, e₁, e₂⟩
  obtain ⟨k, hk'⟩ := hw2
  have hmem : (⟨w, hw⟩ : ↥C) ∈ Ĵ := by
    rw [← hĴdef]
    refine subset_closure ⟨hwY, k, ?_⟩
    rw [Subgroup.orderOf_mk]
    exact hk'
  exact ⟨⟨w, hw⟩, hmem, rfl⟩

theorem isPGroup_center_bar : IsPGroup 2 (center (X ⧸ pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact TBLit.center_isPGroup_two_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)

theorem card_fusionZStar :
    Nat.card (Open.fusionZStar X) =
      Nat.card (pPrimeCore 2 X) * Nat.card (center (X ⧸ pPrimeCore 2 X)) := by
  rw [TBLit.fusionZStar_eq_centralPreimage, UnbalancingLocal.centralPreimage]
  set N := pPrimeCore 2 X
  set H := center (X ⧸ N)
  have hidx : (H.comap (QuotientGroup.mk' N)).index = H.index :=
    index_comap_of_surjective H (QuotientGroup.mk'_surjective N)
  have h1 := card_mul_index (H.comap (QuotientGroup.mk' N))
  have h2 := card_mul_index H
  have h3 := card_eq_card_quotient_mul_card_subgroup N
  have hpos : 0 < H.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
  rw [hidx] at h1
  have h4 : Nat.card ↥(H.comap (QuotientGroup.mk' N)) * H.index =
      Nat.card N * Nat.card H * H.index := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h4

theorem ordProj_card_fusionZStar :
    ordProj[2] (Nat.card (Open.fusionZStar X)) = Nat.card (center (X ⧸ pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := (IsPGroup.iff_card (p := 2)).mp (isPGroup_center_bar (X := X))
  have hO : ¬ 2 ∣ Nat.card (pPrimeCore 2 X) := fun h =>
    Nat.not_even_iff_odd.mpr (GSThmB.OddQuot.odd_card_pPrimeCore (H := X)) (even_iff_two_dvd.mpr h)
  rw [card_fusionZStar, he,
    Nat.factorization_mul (Nat.card_pos (α := pPrimeCore 2 X)).ne' (pow_ne_zero _ two_ne_zero),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hO, Nat.prime_two.factorization_pow,
    Finsupp.single_eq_same, zero_add]

end CFSG.ComponentClassification.HarrisLit.T1.Frame
