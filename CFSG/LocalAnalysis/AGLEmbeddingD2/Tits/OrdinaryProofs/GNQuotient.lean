module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieRes
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem isSylowTwoOf_gnImg_inf {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) {L : Subgroup (X ⧸ gnC T)} (hL : CFSG.Open.IsSubnormal L ⊤) :
    IsSylowTwoOf (gnImg T T ⊓ L) L := by
  have hTodd : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.2.2
  have hS : IsSylowTwoOf (gnImg T T) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hT.2.1.map (QuotientGroup.mk' (gnC T))
    · rw [show ((gnImg T T).subgroupOf ⊤).index = (gnImg T T).index from
        Subgroup.relIndex_top_right _]
      unfold gnImg
      rw [Subgroup.index_map, QuotientGroup.ker_mk',
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), Subgroup.index_top, mul_one]
      intro h
      exact hTodd (dvd_trans h (Subgroup.index_dvd_of_le le_sup_left))
  exact CFSG.QuasithinUnique.L246C127.isSylowTwoOf_inf_of_isSubnormal' hL hS

theorem isSubnormal_trans_top {W : Type} [Group W] {P L : Subgroup W}
    (h : CFSG.Open.IsSubnormal P L) (hL : CFSG.Open.IsSubnormal L ⊤) :
    CFSG.Open.IsSubnormal P ⊤ :=
  h.trans hL

theorem not_two_dvd_card_center_of_isComponentOf {W : Type} [Group W] [Finite W]
    (hO : CFSG.pCore 2 W = ⊥) {L : Subgroup W} (hL : CFSG.Open.IsComponentOf L ⊤) :
    ¬ 2 ∣ Nat.card (Subgroup.center ↥L) := by
  intro h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hxL : orderOf (Subtype.val x : L) = 2 := (Subgroup.orderOf_coe x).trans hx
  set y : W := Subtype.val (Subtype.val x : L) with hy
  have hyo : orderOf y = 2 := (Subgroup.orderOf_coe (Subtype.val x : L)).trans hxL
  have hyL : y ∈ L := (Subtype.val x : L).2
  have hcomm : ∀ g : L, Commute (g : W) y := by
    intro g
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 g)
  have hPgrp : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hyo]; norm_num⟩
  have hPL : Subgroup.zpowers y ≤ L := Subgroup.zpowers_le.mpr hyL
  have hPn : ((Subgroup.zpowers y).subgroupOf L).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute (g : W) (y ^ k) := (hcomm g).zpow_right k
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hk, hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) k
  have hPL' : CFSG.Open.IsSubnormal (Subgroup.zpowers y) L :=
    CFSG.Open.IsSubnormal.step hPL hPn (CFSG.Open.IsSubnormal.refl L)
  have hPtop := isSubnormal_trans_top hPL' hL.2.1
  have hle := CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hPtop hPgrp
  rw [CFSG.QuasithinUnique.B113Lie.pCoreOf_top_eq_pCore', hO]
    at hle
  have h1 : y = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers y))
  rw [h1, orderOf_one] at hyo
  exact absurd hyo (by norm_num)

theorem le_pPrimeCore_of_isSubnormal_p' {p : ℕ} [Fact p.Prime] {W : Type} [Group W] [Finite W]
    {N : Subgroup W} (hN : N.IsSubnormal) (hcop : Nat.Coprime p (Nat.card N)) :
    N ≤ CFSG.pPrimeCore p W := by
  have htop : CFSG.pPrimeCore p ↥N = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩)
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val ≠ p} hN
  rw [← CFSG.pPrimeCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore, htop, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact inf_eq_left.mp h.symm

theorem exists_mul_eq_of_isComplement' {G : Type} [Group G] {H K : Subgroup G}
    (h : H.IsComplement' K) (g : G) : ∃ s ∈ H, ∃ t ∈ K, s * t = g := by
  obtain ⟨-, hsurj⟩ := h
  obtain ⟨⟨⟨s, hs⟩, ⟨t, ht⟩⟩, hst⟩ := hsurj g
  exact ⟨s, hs, t, ht, hst⟩

theorem not_isPSolvable_of_isComponent {W : Type} [Group W] [Finite W]
    (hO : CFSG.pPrimeCore 3 W = ⊥) {K : Subgroup W} (hK : CFSG.IsComponent K) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥K := by
  intro hA
  obtain ⟨⟨-, hsimp, a0, b0, hab⟩, hsub⟩ := hK
  have hZ : Nat.Coprime 3 (Subgroup.center ↥K).index := by
    have hTeq : ((Subgroup.center ↥K).subgroupOf (⊤ : Subgroup ↥K)).map
        (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥K) ≃* ↥K).toMonoidHom = Subgroup.center ↥K := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.mem_subgroupOf.mp hy
      · intro hx
        exact ⟨⟨x, Subgroup.mem_top x⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    let e := QuotientGroup.congr ((Subgroup.center ↥K).subgroupOf (⊤ : Subgroup ↥K))
      (Subgroup.center ↥K) (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥K) ≃* ↥K) hTeq
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hsimp
    have hsimpT : IsSimpleGroup
        (↥(⊤ : Subgroup ↥K) ⧸ (Subgroup.center ↥K).subgroupOf (⊤ : Subgroup ↥K)) :=
      e.isSimpleGroup
    haveI : ((Subgroup.center ↥K).subgroupOf (⊤ : Subgroup ↥K)).Normal := inferInstance
    have hnsn : (⊤ : Subgroup ↥K).IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
    have hT := hA ⊤ hnsn ((Subgroup.center ↥K).subgroupOf (⊤ : Subgroup ↥K)) hsimpT
    have hidx : ((Subgroup.center ↥K).subgroupOf (⊤ : Subgroup ↥K)).index =
        (Subgroup.center ↥K).index := by
      show Nat.card _ = Nat.card _
      exact Nat.card_congr e.toEquiv
    rcases hT with h3 | h3
    · exfalso
      rw [hidx] at h3
      haveI : IsCyclic (↥K ⧸ Subgroup.center ↥K) := by
        apply isCyclic_of_prime_card (p := 3)
        exact h3
      exact hab (mul_comm a0 b0)
    · rwa [hidx] at h3
  have hcen : ∀ g : ↥K, ∀ k : ℕ, g ^ 3 ^ k = 1 → g ∈ Subgroup.center ↥K := by
    intro g k hk
    have h1 : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf (QuotientGroup.mk' (Subgroup.center ↥K) g) ∣ 3 ^ k :=
      (orderOf_map_dvd _ g).trans h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
    rcases j with _ | j
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact (QuotientGroup.eq_one_iff g).mp hj
    · exfalso
      have h3 : 3 ∣ orderOf (QuotientGroup.mk' (Subgroup.center ↥K) g) := by
        rw [hj]
        exact dvd_pow_self 3 (Nat.succ_ne_zero j)
      have h4 : orderOf (QuotientGroup.mk' (Subgroup.center ↥K) g) ∣
          Nat.card (↥K ⧸ Subgroup.center ↥K) := orderOf_dvd_natCard _
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hZ (h3.trans h4)
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  have hPcen : ∀ g ∈ P.toSubgroup, g ∈ Subgroup.center ↥K := by
    intro g hg
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
    exact hcen g k (by simpa using congrArg Subtype.val hk)
  haveI hPn : P.toSubgroup.Normal := ⟨fun n hn g => by
    rw [(Subgroup.mem_center_iff.mp (hPcen n hn) g), mul_inv_cancel_right]
    exact hn⟩
  have hcop : Nat.Coprime (Nat.card P.toSubgroup) P.toSubgroup.index :=
    Sylow.card_coprime_index P
  obtain ⟨H', hC⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hH'n : H'.Normal := by
    constructor
    intro n hn g
    obtain ⟨s, hs, t, ht, hst⟩ := exists_mul_eq_of_isComplement' hC g
    have hsz : s ∈ Subgroup.center ↥K := hPcen s hs
    have key : g * n * g⁻¹ = t * n * t⁻¹ := by
      rw [← hst]
      have hc := Subgroup.mem_center_iff.mp hsz (t * n * t⁻¹)
      calc s * t * n * (s * t)⁻¹ = s * (t * n * t⁻¹) * s⁻¹ := by group
        _ = t * n * t⁻¹ := by rw [← hc, mul_inv_cancel_right]
    rw [key]
    exact H'.mul_mem (H'.mul_mem ht hn) (H'.inv_mem ht)
  have hle' : H'.map K.subtype ≤ K := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hsn : (H'.map K.subtype).subgroupOf K = H' := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hsnW : (H'.map K.subtype).IsSubnormal := by
    refine Subgroup.IsSubnormal.trans hle' ?_ hsub
    rw [hsn]
    exact Subgroup.Normal.isSubnormal inferInstance
  have hcardH : Nat.card (H'.map K.subtype) = Nat.card H' :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective K)
  have hcopH : Nat.Coprime 3 (Nat.card (H'.map K.subtype)) := by
    rw [hcardH, ← hC.symm.index_eq_card]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (Sylow.not_dvd_index P)
  have hle : H'.map K.subtype ≤ CFSG.pPrimeCore 3 W :=
    le_pPrimeCore_of_isSubnormal_p' hsnW hcopH
  rw [hO] at hle
  have hall : ∀ g : ↥K, g ∈ Subgroup.center ↥K := by
    intro g
    obtain ⟨s, hs, t, ht, hst⟩ := exists_mul_eq_of_isComplement' hC g
    have hmem : K.subtype t ∈ H'.map K.subtype := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    have ht1 : t = 1 := Subtype.ext (Subgroup.mem_bot.mp (hle hmem))
    rw [← hst, ht1, mul_one]
    exact hPcen s hs
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a0
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b0
  have hx : (x : ↥K ⧸ Subgroup.center ↥K) = 1 := (QuotientGroup.eq_one_iff x).mpr (hall x)
  have hy : (y : ↥K ⧸ Subgroup.center ↥K) = 1 := (QuotientGroup.eq_one_iff y).mpr (hall y)
  exact hab (by rw [hx, hy])

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient

end
