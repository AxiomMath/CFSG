module

public import CFSG.GH74.GLS.C3.Layer1.Th2IV26
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.CompNormal

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndN

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.Th2.IV26
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem exists_involution_lift {x : G} (hxM : x ∈ M) (hx2 : orderOf x = 2) {u : Mb M}
    (hu2 : orderOf u = 2) (hux : u * eb M hxM = eb M hxM * u) :
    ∃ (g : G) (hg : g ∈ M), g * x = x * g ∧ orderOf g = 2 ∧ barMk ↥M ⟨g, hg⟩ = u := by
  have hso : orderOf (⟨x, hxM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk x hxM).trans hx2
  have huC : u ∈ centralizer ({barMk ↥M ⟨x, hxM⟩} : Set (Mb M)) :=
    mem_centralizer_singleton_iff.2 hux
  obtain ⟨c, hc⟩ := barMkCentralizer_surjective hso ⟨u, huC⟩
  have hcu : barMk ↥M (c : ↥M) = u := by
    have := barMkCentralizer_apply hso c
    rw [hc] at this
    exact this.symm
  have hcx : (c : ↥M) * ⟨x, hxM⟩ = ⟨x, hxM⟩ * (c : ↥M) := mem_centralizer_singleton_iff.1 c.2
  set m : ↥M := (c : ↥M) with hm
  have hu1 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at this
  have hmm : m * m ∈ pPrimeCore 2 ↥M := by
    rw [← ker_barMk (Y := ↥M), MonoidHom.mem_ker, map_mul, hcu]
    exact hu1
  set n := Nat.card ↥(pPrimeCore 2 ↥M) with hn
  have hnodd : Odd n := odd_card_pPrimeCore ↥M
  have hmn : (m * m) ^ n = 1 := by
    have h : (⟨m * m, hmm⟩ : ↥(pPrimeCore 2 ↥M)) ^ n = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2
  have hg0 : (m ^ n) * (m ^ n) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, pow_two, hmn]
  have hg0u : barMk ↥M (m ^ n) = u := by
    rw [map_pow, hcu]
    obtain ⟨k, hk⟩ := hnodd
    rw [hk, pow_succ, pow_mul, pow_two, hu1, one_pow, one_mul]
  have hne : m ^ n ≠ 1 := by
    intro h
    rw [h, map_one] at hg0u
    rw [← hg0u, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hord : orderOf (m ^ n) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hg0) hne
  refine ⟨((m ^ n : ↥M) : G), (m ^ n).2, ?_, ?_, hg0u⟩
  · have := (Commute.pow_left (show Commute m ⟨x, hxM⟩ from hcx) n).eq
    exact congrArg Subtype.val this
  · rw [Subgroup.orderOf_coe]
    exact hord


theorem mem_pPrimeCoreOf_of_barMk_mem {K : Subgroup G} (hKM : K ≤ M) {k : G} (hk : k ∈ K)
    (h : barMk ↥M ⟨k, hKM hk⟩ ∈ pPrimeCoreOf 2 (imgM M K)) : k ∈ pPrimeCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq, hqk⟩ := h
  have hodd : Odd (Nat.card ((pPrimeCore 2 ↥(imgM M K)).comap (toImgM hKM))) :=
    CFSG.OrderReductions.OddCore.odd_preimage (toImgM hKM) (toImgM_surjective hKM)
      (odd_card_ker_toImgM hKM) _ (odd_card_pPrimeCore _)
  have hle : (pPrimeCore 2 ↥(imgM M K)).comap (toImgM hKM) ≤ pPrimeCore 2 ↥K :=
    CFSG.GroupTheory.le_pPrimeCore_of_normal inferInstance (Nat.coprime_two_left.2 hodd)
  have hmem : (⟨k, hk⟩ : ↥K) ∈ (pPrimeCore 2 ↥(imgM M K)).comap (toImgM hKM) := by
    rw [Subgroup.mem_comap]
    have : toImgM hKM ⟨k, hk⟩ = q := Subtype.ext hqk.symm
    rw [this]
    exact hq
  exact ⟨⟨k, hk⟩, hle hmem, rfl⟩


theorem barMk_mem_pPrimeCoreOf_centralizer {y : G} (hyM : y ∈ M) (hy2 : orderOf y = 2) {w : G}
    (hw : w ∈ pPrimeCoreOf 2 (centralizer ({y} : Set G) ⊓ M)) (hwM : w ∈ M) :
    barMk ↥M ⟨w, hwM⟩ ∈ pPrimeCoreOf 2 (centralizer ({eb M hyM} : Set (Mb M))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup (Mb M) := centralizer ({eb M hyM} : Set (Mb M)) with hD
  set H₀ : Subgroup G := centralizer ({y} : Set G) ⊓ M with hH₀
  set Oy : Subgroup G := pPrimeCoreOf 2 H₀ with hOy
  have hOyH : Oy ≤ H₀ := TwoThin.pPrimeCoreOf_le H₀
  have hso : orderOf (⟨y, hyM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk y hyM).trans hy2
  have hObD : imgM M Oy ≤ D := by
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hv
    rw [hD, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hOyH hm).1)
  set R' : Subgroup ↥D := (imgM M Oy).subgroupOf D with hR'
  have hRnorm : R'.Normal := by
    refine ⟨fun r hr d => ?_⟩
    rw [hR', Subgroup.mem_subgroupOf] at hr ⊢
    obtain ⟨o, hoO, hor⟩ := mem_imgM_iff.1 hr
    obtain ⟨c, hcd⟩ := barMkCentralizer_surjective hso d
    have hcG : ((c : ↥M) : G) ∈ H₀ := by
      have h := c.2
      rw [mem_centralizer_singleton_iff] at h
      exact ⟨mem_centralizer_singleton_iff.2 (congrArg Subtype.val h), (c : ↥M).2⟩
    have hcdv : (d : Mb M) = barMk ↥M (c : ↥M) := by
      rw [← hcd]
      exact barMkCentralizer_apply hso c
    have hmem : ((c : ↥M) * o * (c : ↥M)⁻¹ : ↥M).1 ∈ Oy := by
      have := TwoThin.pPrimeCoreOf_normalized H₀ hcG hoO
      simpa using this
    refine mem_imgM_iff.2 ⟨(c : ↥M) * o * (c : ↥M)⁻¹, hmem, ?_⟩
    show barMk ↥M ((c : ↥M) * o * (c : ↥M)⁻¹) = (d : Mb M) * (r : Mb M) * (d : Mb M)⁻¹
    rw [map_mul, map_mul, map_inv, hor, hcdv]
  have hRodd : Odd (Nat.card R') := by
    rw [hR', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hObD).toEquiv]
    have h1 : Nat.card (imgM M Oy) ∣ Nat.card (Oy.subgroupOf M) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (Oy.subgroupOf M) ∣ Nat.card Oy := by
      have h3 : Nat.card (Oy.subgroupOf M) = Nat.card ((Oy.subgroupOf M).map M.subtype) :=
        (Subgroup.card_map_of_injective M.subtype_injective).symm
      rw [h3]
      exact Subgroup.card_dvd_of_le (by rintro _ ⟨m, hm, rfl⟩; exact hm)
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd _) (h1.trans h2)
  have hR : R' ≤ pPrimeCore 2 ↥D := le_sSup ⟨hRnorm, Nat.coprime_two_left.2 hRodd⟩
  have hwb : barMk ↥M ⟨w, hwM⟩ ∈ imgM M Oy := mem_imgM_iff.2 ⟨⟨w, hwM⟩, hw, rfl⟩
  exact ⟨⟨_, hObD hwb⟩, hR (Subgroup.mem_subgroupOf.2 hwb), rfl⟩


omit [Finite G] in
theorem eb_mem_commutator_top {x : G} (hxM : x ∈ M) (h : x ∈ ⁅M, M⁆) :
    eb M hxM ∈ ⁅(⊤ : Subgroup (Mb M)), (⊤ : Subgroup (Mb M))⁆ := by
  have hM : (⊤ : Subgroup ↥M).map M.subtype = M := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : ⁅M, M⁆ = (⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆).map M.subtype := by
    rw [Subgroup.map_commutator, hM]
  rw [h1] at h
  obtain ⟨hh, hhm, hhx⟩ := h
  have hhx' : hh = ⟨x, hxM⟩ := Subtype.ext hhx
  have h2 : barMk ↥M hh ∈ (⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆).map (barMk ↥M) :=
    Subgroup.mem_map_of_mem _ hhm
  rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ barMk_surjective] at h2
  rw [hhx'] at h2
  exact h2


theorem hasL2Model_imgM {K : Subgroup G} (hKM : K ≤ M) (hL : HasL2Model (kBar K) (fun q => q = 9)) :
    HasL2Model (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) (fun q => q = 9) := by
  obtain ⟨e⟩ := kBar_equiv_imgM hKM
  exact TwoThin.hasL2Model_of_mulEquiv e.symm hL

theorem two_le_pRank_imgM {K : Subgroup G} (hKM : K ≤ M)
    (hL : HasL2Model (kBar K) (fun q => q = 9)) : 2 ≤ pRank 2 ↥(imgM M K) := by
  have h := hasL2Model_imgM hKM hL
  exact Thm1.two_le_pRank_of_shape (K := imgM M K)
    (Or.inl (C3.Layer1.Back.hasL2Model_mono (fun q hq => by rw [hq]; exact ⟨4, rfl⟩) h))

theorem no_involution_center_imgM {K : Subgroup G} (hKM : K ≤ M)
    (hL : HasL2Model (kBar K) (fun q => q = 9)) :
    ∀ z ∈ Subgroup.center ↥(imgM M K), orderOf (z : Mb M) ≠ 2 := by
  intro z hz hz2
  have h := hasL2Model_imgM hKM hL
  have h' : HasL2Model (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) (fun q => Odd q ∧ 3 < q) :=
    C3.Layer1.Back.hasL2Model_mono (fun q hq => by rw [hq]; exact ⟨⟨4, rfl⟩, by norm_num⟩) h
  have hc : Subgroup.center (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) = ⊥ :=
    Stage1.Thm6.Glue.center_eq_bot_of_isL2Model (Stage1.Thm6.Glue.isL2Model_of_hasL2Model h')
  have hzc : (QuotientGroup.mk z : ↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) ∈
      Subgroup.center (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hz k]
  rw [hc, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hzc
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥(imgM M K))) := odd_card_pPrimeCore _
  have hdvd : orderOf z ∣ Nat.card ↥(pPrimeCore 2 ↥(imgM M K)) := Subgroup.orderOf_dvd_natCard _ hzc
  rw [Subgroup.orderOf_coe] at hz2
  rw [hz2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)


end CFSG.GH74.GLS.C3.Layer1.EndN
