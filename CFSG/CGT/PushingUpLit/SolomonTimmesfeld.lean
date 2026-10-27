module

public import CFSG.CGT.PushingUpLit.T2K.Inputs
public import CFSG.CGT.PushingUpLit.SolK.Tight
public import CFSG.CGT.PushingUpLit.SolK.GenFour
public import CFSG.CGT.PushingUpLit.STT.NatAlt
public import CFSG.CGT.PushingUpLit.STT.SzU3
public import CFSG.CGT.PushingUpLit.BHS.Replacement
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUpLit.BHS7.BlockComm
public import CFSG.CGT.PushingUpLit.BHS7.SevenThree
public import CFSG.CGT.PushingUpLit.BHS7.VFacts
public import CFSG.CGT.PushingUpLit.Glue.ModuleTrivial
public import CFSG.CGT.PushingUpLit.SolK.PermBlock
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.CGT.PushingUpLit.T2K.FourFiveF
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartOne.S12.Sec15Final
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding (TightlyEmbedded)

namespace SolomonTimmesfeld

theorem commute_of_odd_pow_eq_one {G : Type*} [Group G] {R : Subgroup G} [IsCyclic ↥R]
    (hR : Nat.card ↥R = 4) {x : G} (hx : ∀ y ∈ R, x * y * x⁻¹ ∈ R) {m : ℕ} (hm : Odd m)
    (hxm : x ^ m = 1) : ∀ r ∈ R, x * r = r * x := by
  classical
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := ↥R)
  have hzp : ∀ r ∈ R, ∃ i : ℤ, (s : G) ^ i = r := fun r hr => by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hs ⟨r, hr⟩)
    exact ⟨i, by simpa using congrArg Subtype.val hi⟩
  have hord : orderOf (s : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hs, hR]
  have hs4 : (s : G) ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hs2 : (s : G) ^ 2 ≠ 1 := by
    intro h2
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at this
    omega
  obtain ⟨j, hj⟩ := hzp _ (hx _ s.2)
  have hjodd : Odd j := by
    by_contra hnot
    obtain ⟨k, hk⟩ := Int.not_odd_iff_even.1 hnot
    have h1 : (x * (s : G) * x⁻¹) ^ 2 = 1 := by
      rw [← hj, ← zpow_natCast, ← zpow_mul, hk]
      have : (k + k) * ((2 : ℕ) : ℤ) = 4 * k := by push_cast; ring
      rw [this, zpow_mul]
      have h4 : (s : G) ^ (4 : ℤ) = 1 := by exact_mod_cast hs4
      rw [h4, one_zpow]
    rw [conj_pow] at h1
    apply hs2
    have h2 : x * (s : G) ^ 2 * x⁻¹ = 1 := h1
    simpa using h2
  obtain ⟨a, ha⟩ := hjodd
  have hx2 : x ^ 2 * (s : G) * (x ^ 2)⁻¹ = (s : G) := by
    have h1 : x ^ 2 * (s : G) * (x ^ 2)⁻¹ = x * (x * (s : G) * x⁻¹) * x⁻¹ := by
      rw [pow_two]; group
    rw [h1, ← hj, ← conj_zpow, ← hj, ← zpow_mul]
    have : j * j = 4 * (a * a + a) + 1 := by rw [ha]; ring
    rw [this, zpow_add, zpow_mul]
    have h4 : (s : G) ^ (4 : ℤ) = 1 := by exact_mod_cast hs4
    rw [h4, one_zpow, one_mul, zpow_one]
  obtain ⟨b, hb⟩ := hm
  have hxx : x = (x ^ 2) ^ (b + 1) := by
    rw [← pow_mul]
    have : 2 * (b + 1) = m + 1 := by omega
    rw [this, pow_succ, hxm, one_mul]
  have hcomm : Commute x (s : G) := by
    rw [hxx]
    refine Commute.pow_left ?_ _
    exact (mul_inv_eq_iff_eq_mul.1 hx2)
  intro r hr
  obtain ⟨i, rfl⟩ := hzp r hr
  exact (hcomm.zpow_right i).eq

theorem eq_one_of_pow_eq_one_odd_two {G : Type*} [Group G] {x : G} {m k : ℕ} (hm : Odd m)
    (h1 : x ^ m = 1) (h2 : x ^ 2 ^ k = 1) : x = 1 := by
  have hcop : Nat.Coprime m (2 ^ k) := (Nat.coprime_two_right.2 hm).pow_right k
  have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

theorem eq_one_of_odd_pow_of_cyclic_four {G : Type} [Group G] [Finite G] {K M RG : Subgroup G}
    (hKM : K ≤ M) (hMK : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M)
    (hRO : RG = pCoreOf 2 K) [IsCyclic ↥RG] (hc4 : Nat.card ↥RG = 4) :
    ∀ x ∈ K, ∀ m : ℕ, Odd m → x ^ m = 1 → x = 1 := by
  intro x hxK m hm hxm
  have hxM : x ∈ M := hKM hxK
  have hxN : ∀ y ∈ RG, x * y * x⁻¹ ∈ RG := fun y hy => by
    rw [hRO] at hy ⊢
    exact SolK.pCoreOf_normalized K hxK hy
  have hxc : ∀ r ∈ RG, x * r = r * x := commute_of_odd_pow_eq_one hc4 hxN hm hxm
  have hKQ : K ⊓ pCoreOf 2 M ≤ RG := by
    rw [hRO]
    refine SolK.le_pCoreOf_of_normalized inf_le_left (fun k hk z hz => ?_)
      ((SolK.isPGroup_pCoreOf' M).to_le inf_le_right)
    exact Subgroup.mem_inf.2 ⟨K.mul_mem (K.mul_mem hk hz.1) (K.inv_mem hk),
      SolK.pCoreOf_normalized M (hKM hk) hz.2⟩
  have hxQ : x ∈ pCoreOf 2 M := by
    refine hF (Subgroup.mem_inf.2 ⟨hxM, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩)
    have hqM : q ∈ M := SolK.pCoreOf_le_self M hq
    have h1 : x * q * x⁻¹ ∈ pCoreOf 2 M := SolK.pCoreOf_normalized M hxM hq
    have hcQ : x * q * x⁻¹ * q⁻¹ ∈ pCoreOf 2 M :=
      (pCoreOf 2 M).mul_mem h1 ((pCoreOf 2 M).inv_mem hq)
    have hyK : q * x * q⁻¹ ∈ K := hMK q hqM x hxK
    have hcK : x * q * x⁻¹ * q⁻¹ ∈ K := by
      have e : x * q * x⁻¹ * q⁻¹ = x * (q * x * q⁻¹)⁻¹ := by group
      rw [e]
      exact K.mul_mem hxK (K.inv_mem hyK)
    have hcR : x * q * x⁻¹ * q⁻¹ ∈ RG := hKQ (Subgroup.mem_inf.2 ⟨hcK, hcQ⟩)
    set c : G := x * q * x⁻¹ * q⁻¹ with hc
    have hcx : x * c = c * x := hxc c hcR
    have hyx : q * x * q⁻¹ = c⁻¹ * x := by rw [hc]; group
    have hym : (q * x * q⁻¹) ^ m = 1 := by rw [conj_pow, hxm]; group
    have hc4' : c ^ 4 = 1 := by
      have := pow_card_eq_one' (G := ↥RG) (x := (⟨c, hcR⟩ : ↥RG))
      rw [hc4] at this
      simpa using congrArg Subtype.val this
    have hcm : c⁻¹ ^ m = 1 := by
      have hcomm' : Commute c⁻¹ x := ((Commute.inv_left (show Commute c x from hcx.symm)))
      have h2 : (c⁻¹ * x) ^ m = c⁻¹ ^ m * x ^ m := hcomm'.mul_pow m
      rw [← hyx, hym, hxm, mul_one] at h2
      exact h2.symm
    have hc1 : c = 1 := by
      have h1 : c ^ m = 1 := by simpa [inv_pow] using hcm
      have hcop : Nat.Coprime m (2 ^ 2) := (Nat.coprime_two_right.2 hm).pow_right 2
      have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hc4')
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, hcop.gcd_eq_one] at this
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
    have : x * q * x⁻¹ = q := by
      have := congrArg (· * q) hc1
      simpa [hc] using this
    calc q * x = (x * q * x⁻¹) * x := by rw [this]
      _ = x * q := by group
  obtain ⟨k, hk⟩ := (SolK.isPGroup_pCoreOf' M) ⟨x, hxQ⟩
  exact eq_one_of_pow_eq_one_odd_two hm hxm (by simpa using congrArg Subtype.val hk)

theorem eq_zpowers_of_cyclic_four {G : Type} [Group G] [Finite G] {K M RG : Subgroup G}
    (hKM : K ≤ M) (hMK : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M)
    (R : Sylow 2 ↥K) (hRG : (R : Subgroup ↥K).map K.subtype = RG) (hRO : RG = pCoreOf 2 K)
    [IsCyclic ↥RG] (hc4 : Nat.card ↥RG = 4) :
    ∃ s : G, orderOf s = 4 ∧ K = Subgroup.zpowers s := by
  classical
  have hA := eq_one_of_odd_pow_of_cyclic_four hKM hMK hF hRO hc4
  have hK2 : IsPGroup 2 ↥K := by
    intro g
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
    refine ⟨a, Subtype.ext ?_⟩
    have hyK : (g : G) ^ 2 ^ a ∈ K := K.pow_mem g.2 _
    have h1 : ((g : G) ^ 2 ^ a) ^ m = 1 := by rw [← pow_mul, ← hn]; exact pow_orderOf_eq_one _
    have := hA _ hyK m hm h1
    simpa using this
  have hKtop : (R : Subgroup ↥K) = ⊤ := by
    have hT2 : IsPGroup 2 ↥(⊤ : Subgroup ↥K) := hK2.of_equiv Subgroup.topEquiv.symm
    exact (R.is_maximal' hT2 le_top).symm
  have hRGK : RG = K := by
    rw [← hRG, hKtop, Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := ↥RG)
  refine ⟨(s : G), ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hs, hc4]
  · rw [← hRGK]
    refine le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.2 s.2)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hs ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨i, by simpa using congrArg Subtype.val hi⟩

theorem sixteen_mul_card_le_of_two_group {G : Type} [Group G] [Finite G] {V L R : Subgroup G}
    {q B : ℕ} (hV2 : IsPGroup 2 V) (hVL : V ≤ L)
    (hVcard : Nat.card ↥V = q * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G))) (hq : 16 ≤ q)
    (hP : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card ↥P ≤ B)
    (hRC : R ≤ Subgroup.centralizer (L : Set G)) (hR2 : IsPGroup 2 R) :
    16 * Nat.card ↥R ≤ B := by
  classical
  have hcomm : ∀ v ∈ V, ∀ r ∈ R, v * r = r * v := fun v hv r hr =>
    Subgroup.mem_centralizer_iff.1 (hRC hr) v (hVL hv)
  have hc : ∀ r' ∈ R, ∀ w ∈ V, r' * w * r'⁻¹ = w := fun r' hr' w hw => by
    rw [← hcomm w hw r' hr']; group
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := fun r hr => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => by rw [hc r hr h hh]; exact hh, fun hh => ?_⟩
    have h1 := hc r⁻¹ (R.inv_mem hr) _ hh
    have e : r⁻¹ * (r * h * r⁻¹) * r⁻¹⁻¹ = h := by group
    rw [e] at h1
    exact h1.symm ▸ hh
  have hP2 : IsPGroup 2 (V ⊔ R : Subgroup G) := hV2.to_sup_of_normal_left' hR2 hRN
  have hprod := CFSG.CGT.PushingUpLit.BHS.card_sup_mul_card_inf' (X := V) (Y := R) hcomm
  have hinf : Nat.card ↥(V ⊓ R : Subgroup G) ≤
      Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le (inf_le_inf_left V hRC)
  have hZpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := Nat.card_pos
  have key : q * Nat.card ↥R ≤ Nat.card ↥(V ⊔ R : Subgroup G) := by
    refine Nat.le_of_mul_le_mul_right ?_ hZpos
    calc q * Nat.card ↥R * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G)
        = Nat.card ↥V * Nat.card ↥R := by rw [hVcard]; ring
      _ = Nat.card ↥(V ⊔ R : Subgroup G) * Nat.card ↥(V ⊓ R : Subgroup G) := hprod.symm
      _ ≤ Nat.card ↥(V ⊔ R : Subgroup G) *
          Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :=
          Nat.mul_le_mul_left _ hinf
  calc 16 * Nat.card ↥R ≤ q * Nat.card ↥R := Nat.mul_le_mul_right _ hq
    _ ≤ Nat.card ↥(V ⊔ R : Subgroup G) := key
    _ ≤ B := hP _ hP2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}

theorem sixteen_le_two_pow_sq (hn : 2 ≤ n) : 16 ≤ (2 ^ n) ^ 2 := by
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  calc 16 = 4 ^ 2 := by norm_num
    _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2

theorem sixteen_le_card_blockU (h : NatBlock L n) : 16 ≤ Nat.card ↥(blockU L) := by
  have hcard : Nat.card ↥(blockU L) = (2 ^ n) ^ 2 * Nat.card ↥(blockZ L) := h.card_blockU
  have hZ : 1 ≤ Nat.card ↥(blockZ L) := Nat.card_pos
  rw [hcard]
  calc 16 ≤ (2 ^ n) ^ 2 := sixteen_le_two_pow_sq h.two_le
    _ = (2 ^ n) ^ 2 * 1 := (mul_one _).symm
    _ ≤ (2 ^ n) ^ 2 * Nat.card ↥(blockZ L) := Nat.mul_le_mul_left _ hZ

theorem sixteen_mul_card_le (h : NatBlock L n) {B : ℕ}
    (hP : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card ↥P ≤ B) {R : Subgroup G}
    (hRC : R ≤ Subgroup.centralizer (L : Set G)) (hR2 : IsPGroup 2 R) : 16 * Nat.card ↥R ≤ B :=
  sixteen_mul_card_le_of_two_group (isPGroup_blockU' L) (blockU_le L) h.card_blockU
    (sixteen_le_two_pow_sq h.two_le) hP hRC hR2

theorem natBlock_ne_bot (h : NatBlock L n) : L ≠ ⊥ := fun hb =>
  h.not_isPGroup (by
    rw [hb]
    exact IsPGroup.of_card (n := 0) (by rw [Subgroup.card_bot, pow_zero]))

theorem natBlock_not_isSolvable (h : NatBlock L n) : ¬ Group.IsSolvable ↥L := by
  intro hsolv
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 h.perfect
  have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 (natBlock_ne_bot h)
  exact Group.IsPerfect.not_isSolvable _ hsolv

theorem natBlock_exists_noncomm (h : NatBlock L n) : ∃ a b : G, a * b ≠ b * a := by
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 h.perfect
  have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 (natBlock_ne_bot h)
  by_contra hcomm
  push Not at hcomm
  exact Group.IsPerfect.not_isMulCommutative (G := ↥L)
    ⟨⟨fun a b => Subtype.ext (hcomm _ _)⟩⟩

omit [Finite G] in
theorem tightlyEmbedded_of_isTightlyEmbedded {X : Subgroup G} (h : IsTightlyEmbedded X) :
    TightlyEmbedded X :=
  (isTightlyEmbedded_iff_tightlyEmbedded X).1 h

end SolomonTimmesfeld

open SolomonTimmesfeld in
theorem solomonTimmesfeldTight_of_solK (hE2 : SolK.SolomonTimmesfeldTight)
    (hOrd : SolK.TightSmallGroupOrders) : SolomonTimmesfeldTight := by
  classical
  intro G _ _ L M n h _ hK hN
  set K : Subgroup G := Subgroup.centralizer (L : Set G) with hKdef
  have hKM : K ≤ M := by rw [← hN]; exact Subgroup.le_normalizer
  have hMK : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K := fun m hm k hk => by
    have hm' : m ∈ Subgroup.normalizer (K : Set G) := by rw [hN]; exact hm
    exact (Subgroup.mem_normalizer_iff.1 hm' k).1 hk
  have hFM : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    h.charTwo M h.maxLocal.1
  have hmax : IsMaximalTwoLocal (Subgroup.normalizer (K : Set G)) := by
    rw [hN]; exact h.maxLocal
  have hF : Subgroup.normalizer (K : Set G) ⊓
      Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (K : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.normalizer (K : Set G)) := by
    rw [hN]; exact hFM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have h27 := hE2 G h.kproper h.simple (natBlock_exists_noncomm h.natBlock) K
    (tightlyEmbedded_of_isTightlyEmbedded hK) hmax hF R
  obtain ⟨RG, hRG⟩ : ∃ RG : Subgroup G, (R : Subgroup ↥K).map K.subtype = RG := ⟨_, rfl⟩
  rw [hRG] at h27
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 2 RG K := ⟨R, hRG⟩
  have hRGK : RG ≤ K := by rw [← hRG]; exact Subgroup.map_subtype_le _
  have hRG2 : IsPGroup 2 RG := by rw [← hRG]; exact R.isPGroup'.map _
  have hnat : NatBlock L n := h.natBlock
  rcases h27 with ⟨hRO, hab, -⟩ | ⟨-, hdih⟩ | ⟨hQ8, hgrp⟩ | ⟨⟨H, -, hHR, ⟨hHe⟩, -⟩, hL34⟩ |
      hSz | ⟨hRO6, hel, -⟩
  ·
    rcases hab with ⟨hcyc, hc4⟩ | hel
    · left
      have := hcyc
      exact eq_zpowers_of_cyclic_four hKM hMK hFM R hRG hRO hc4
    · right
      refine ⟨RG, hsyl, ⟨fun x hx k => ?_⟩, hel⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [hRO] at hx ⊢
      have := SolK.pCoreOf_normalized K k.2 hx
      simpa using this
  ·
    exfalso
    have hgen2 := SolK.gen2_of_dihedral_or_semidihedral hdih
    have hle : Nat.card ↥(blockU L) ≤ 2 ^ 2 :=
      hgen2.card_le_of_elementary _ hnat.isElemAbelian_blockU
    have h16 := sixteen_le_card_blockU hnat
    omega
  ·
    exfalso
    have hb : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card ↥P ≤ 64 := by
      rcases hgrp with h1 | h1 | h1 | h1 | h1
      · exact hOrd G (Or.inl h1)
      · exact hOrd G (Or.inr (Or.inl h1))
      · exact hOrd G (Or.inr (Or.inr (Or.inl h1)))
      · exact hOrd G (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      · exact hOrd G (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
    have h16 := sixteen_mul_card_le hnat hb hRGK hRG2
    have hcard : Nat.card ↥RG = 8 := by
      rw [Nat.card_congr hQ8.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    omega
  ·
    exfalso
    have hb : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card ↥P ≤ 64 :=
      hOrd G (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL34)))))
    have h16 := sixteen_mul_card_le hnat hb hRGK hRG2
    have hH16 : Nat.card ↥H = 16 := by
      rw [Nat.card_congr hHe.toEquiv, Nat.card_prod,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 4) ≃ ZMod 4), Nat.card_zmod]
    have hle := Subgroup.card_le_of_le hHR
    omega
  ·
    exfalso
    have hLC : L ≤ Subgroup.centralizer (RG : Set G) := fun l hl r hr =>
      (Subgroup.mem_centralizer_iff.1 (hRGK hr) l hl).symm
    have hRne : RG ≠ ⊥ := by
      have := STT.map_sylow_ne_bot hK.1 R
      rwa [hRG] at this
    have hCsolv := STT.isSolvable_centralizer_of_stated_bender hSz hRG2 hRne
    exact natBlock_not_isSolvable hnat
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLC))
  ·
    right
    refine ⟨RG, hsyl, ⟨fun x hx k => ?_⟩, hel⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hRO6] at hx ⊢
    have := SolK.pCoreOf_normalized K k.2 hx
    simpa using this

end CFSG.CGT.PushingUpLit.T2K
