module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16Struct
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16Sound
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocal
public import CFSG.GH74.GLS.Balance.SolvCompBasic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution

theorem IsTwoPrimeTwo.subgroupOf {Y : Type} [Group Y] {K H : Subgroup Y} (hKH : K ≤ H)
    (h : IsTwoPrimeTwo K) : IsTwoPrimeTwo (K.subgroupOf H) := by
  obtain ⟨O, hOK, hOn, hOodd, hOall⟩ := h
  have hOH : O ≤ H := hOK.trans hKH
  refine ⟨O.subgroupOf H, fun g hg => hOK hg, ?_, ?_, ?_⟩
  · refine ⟨fun n hn g => ?_⟩
    have hnO : (((n : ↥(K.subgroupOf H)) : ↥H) : Y) ∈ O := hn
    have hnK : (((n : ↥(K.subgroupOf H)) : ↥H) : Y) ∈ K := Subgroup.mem_subgroupOf.mp n.2
    have hgK : (((g : ↥(K.subgroupOf H)) : ↥H) : Y) ∈ K := Subgroup.mem_subgroupOf.mp g.2
    exact hOn.conj_mem ⟨_, hnK⟩ hnO ⟨_, hgK⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv]
    exact hOodd
  · intro g hg
    obtain ⟨m, hm⟩ := hOall ((g : ↥H) : Y) hg
    exact ⟨m, by
      show (((g : ↥H) ^ 2 ^ m : ↥H) : Y) ∈ O
      rw [Subgroup.coe_pow]
      exact hm⟩

theorem le_pCore_comap_of_isSubnormal {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : K.IsSubnormal) (h : IsTwoPrimeTwo K) :
    K ≤ (pCore 2 (G ⧸ pPrimeCore 2 G)).comap (QuotientGroup.mk' (pPrimeCore 2 G)) := by
  obtain ⟨O, hOK, hOn, hOodd, hOall⟩ := h
  have hOs : O.IsSubnormal := Subgroup.IsSubnormal.trans hOK hOn.isSubnormal hK
  have hO : O ≤ pPrimeCore 2 G := by
    have h1 := Walter.map_pPrimeCore_le_of_isSubnormal hOs
    have htop : pPrimeCore 2 O = ⊤ := by
      apply le_antisymm le_top
      apply le_sSup
      exact ⟨Subgroup.normal_top, by
        rw [Subgroup.card_top]
        exact Nat.coprime_two_left.mpr hOodd⟩
    rwa [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  haveI : (pPrimeCore 2 G).Normal := pPrimeCore_normal
  have hKbar : IsPGroup 2 ↥(K.map (QuotientGroup.mk' (pPrimeCore 2 G))) := by
    rintro ⟨_, g, hg, rfl⟩
    obtain ⟨m, hm⟩ := hOall g hg
    refine ⟨m, Subtype.ext ?_⟩
    show (QuotientGroup.mk' (pPrimeCore 2 G) g) ^ 2 ^ m = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 (hO hm)
  have hsub : (K.map (QuotientGroup.mk' (pPrimeCore 2 G))).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) hK
  have hle := GH74.GLS.Balance.SolvComp.map_le_pCore_of_isSubnormal hsub
    (U := ⊤) (hKbar.of_equiv Subgroup.topEquiv.symm)
  intro k hk
  exact hle ⟨⟨QuotientGroup.mk' (pPrimeCore 2 G) k, Subgroup.mem_map_of_mem _ hk⟩,
    Subgroup.mem_top _, rfl⟩

@[expose] def oTwoPrimeTwo {Y : Type} [Group Y] (H : Subgroup Y) : Subgroup Y :=
  ((pCore 2 (↥H ⧸ pPrimeCore 2 ↥H)).comap (QuotientGroup.mk' (pPrimeCore 2 ↥H))).map H.subtype

@[expose] def oTwoPrime {Y : Type} [Group Y] (H : Subgroup Y) : Subgroup Y :=
  (pPrimeCore 2 ↥H).map H.subtype

variable {Y : Type} [Group Y] [Finite Y]

theorem oTwoPrimeTwo_le (H : Subgroup Y) : oTwoPrimeTwo H ≤ H := Subgroup.map_subtype_le _

theorem conj_mem_oTwoPrimeTwo {H : Subgroup Y} {h : Y} (hh : h ∈ H) {d : Y}
    (hd : d ∈ oTwoPrimeTwo H) : h * d * h⁻¹ ∈ oTwoPrimeTwo H := by
  obtain ⟨d₀, hd₀, rfl⟩ := hd
  haveI : (pPrimeCore 2 ↥H).Normal := pPrimeCore_normal
  haveI : (pCore 2 (↥H ⧸ pPrimeCore 2 ↥H)).Normal := pCore_normal
  refine ⟨⟨h, hh⟩ * d₀ * ⟨h, hh⟩⁻¹, ?_, rfl⟩
  exact (Subgroup.Normal.comap inferInstance _).conj_mem d₀ hd₀ ⟨h, hh⟩

theorem conj_mem_oTwoPrime {H : Subgroup Y} {h : Y} (hh : h ∈ H) {d : Y}
    (hd : d ∈ oTwoPrime H) : h * d * h⁻¹ ∈ oTwoPrime H := by
  obtain ⟨d₀, hd₀, rfl⟩ := hd
  haveI : (pPrimeCore 2 ↥H).Normal := pPrimeCore_normal
  exact ⟨⟨h, hh⟩ * d₀ * ⟨h, hh⟩⁻¹, (inferInstance : (pPrimeCore 2 ↥H).Normal).conj_mem d₀ hd₀ _,
    rfl⟩

theorem odd_card_oTwoPrime (H : Subgroup Y) : Odd (Nat.card (oTwoPrime H)) := by
  rw [oTwoPrime, Subgroup.card_map_of_injective H.subtype_injective]
  exact Nat.coprime_two_left.1 pPrimeCore_coprime_card

theorem oTwoPrime_le_oTwoPrimeTwo (H : Subgroup Y) : oTwoPrime H ≤ oTwoPrimeTwo H := by
  rintro _ ⟨o, ho, rfl⟩
  refine ⟨o, ?_, rfl⟩
  show QuotientGroup.mk' (pPrimeCore 2 ↥H) o ∈ pCore 2 (↥H ⧸ pPrimeCore 2 ↥H)
  have : QuotientGroup.mk' (pPrimeCore 2 ↥H) o = 1 := (QuotientGroup.eq_one_iff o).2 ho
  rw [this]
  exact Subgroup.one_mem _

theorem exists_pow_mem_oTwoPrime (H : Subgroup Y) {g : Y} (hg : g ∈ oTwoPrimeTwo H) :
    ∃ k : ℕ, g ^ 2 ^ k ∈ oTwoPrime H := by
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  have h2 : IsPGroup 2 (pCore 2 (↥H ⧸ pPrimeCore 2 ↥H)) := pCore_isPGroup
  obtain ⟨k, hk⟩ := h2 ⟨QuotientGroup.mk' (pPrimeCore 2 ↥H) g₀, hg₀⟩
  refine ⟨k, g₀ ^ 2 ^ k, ?_, ?_⟩
  · have : QuotientGroup.mk' (pPrimeCore 2 ↥H) g₀ ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  · simp

theorem le_oTwoPrimeTwo_of_isSubnormal {H K : Subgroup Y} (hK : IsSubnormal K H)
    (h : IsTwoPrimeTwo K) : K ≤ oTwoPrimeTwo H := by
  have hKH : K ≤ H := hK.le
  have h1 := le_pCore_comap_of_isSubnormal ((CFSG.Open.IsSubnormal.iff_subgroupOf hKH).1 hK)
    (h.subgroupOf hKH)
  intro k hk
  exact ⟨⟨k, hKH hk⟩, h1 (show (⟨k, hKH hk⟩ : ↥H) ∈ K.subgroupOf H from hk), rfl⟩

theorem Q16Q16.local_reduction (N : Subgroup Y) [N.Normal]
    (hC : Subgroup.centralizer (N : Set Y) = ⊥) (hO : Nobq.OutTwoCyclic ↥N)
    {t : Y} {K K' : Subgroup Y}
    (hK : IsSubnormal K (Subgroup.centralizer ({t} : Set Y)))
    (hK' : IsSubnormal K' (Subgroup.centralizer ({t} : Set Y)))
    (h2 : IsTwoPrimeTwo K) (h2' : IsTwoPrimeTwo K')
    {x y x' y' : Y} (hx : x ∈ K) (hy : y ∈ K) (hx' : x' ∈ K') (hy' : y' ∈ K')
    (hq : Q16Q16 x y x' y') (hxt : x ^ 4 = t) :
    ∃ D Ō M : Subgroup Y, D ≤ N ⊓ Subgroup.centralizer ({t} : Set Y) ∧ Ō ≤ D ∧ M ≤ D ∧ t ∈ M ∧
      (∀ c ∈ N ⊓ Subgroup.centralizer ({t} : Set Y), ∀ d ∈ D, c * d * c⁻¹ ∈ D) ∧
      (∀ c ∈ N ⊓ Subgroup.centralizer ({t} : Set Y), ∀ o ∈ Ō, c * o * c⁻¹ ∈ Ō) ∧
      Odd (Nat.card Ō) ∧ (∀ g ∈ D, ∃ k : ℕ, g ^ 2 ^ k ∈ Ō) ∧ IsPGroup 2 M ∧ 64 ≤ Nat.card M := by
  set H := Subgroup.centralizer ({t} : Set Y) with hH
  set Q := Q16Q16.group x y x' y' with hQ
  have hQ2 : IsPGroup 2 Q := by
    refine (isPGroup_sup_of_q16Q16 hq).to_le (sup_le_sup ?_ ?_)
    · refine (Subgroup.closure_le _).2 ?_
      rintro g (rfl | hg)
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · refine (Subgroup.closure_le _).2 ?_
      rintro g (rfl | hg)
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hcyc : IsCyclic ↥(Q.map (QuotientGroup.mk' N)) :=
    Nobq.isCyclic_of_outTwoCyclic N hC hO _ (hQ2.map _)
  have hQK : Subgroup.closure ({x, y} : Set Y) ≤ K := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | hg)
    · exact hx
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hy
  have hQK' : Subgroup.closure ({x', y'} : Set Y) ≤ K' := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | hg)
    · exact hx'
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hy'
  have hQD : Q ≤ oTwoPrimeTwo H :=
    sup_le (hQK.trans (le_oTwoPrimeTwo_of_isSubnormal hK h2))
      (hQK'.trans (le_oTwoPrimeTwo_of_isSubnormal hK' h2'))
  have hxQ : x ∈ Q := Q16Q16.mem_group_left (Subgroup.subset_closure (Set.mem_insert _ _))
  have hx2N : x ^ 2 ∈ N := by
    have h1 := hq.image_sq_eq_one N hcyc x hxQ
    rw [← map_pow] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  have htM : t ∈ N ⊓ Q := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [← hxt, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      exact N.pow_mem hx2N 2
    · rw [← hxt]
      exact Q.pow_mem hxQ 4
  refine ⟨N ⊓ oTwoPrimeTwo H, N ⊓ oTwoPrime H, N ⊓ Q,
    inf_le_inf_left N (oTwoPrimeTwo_le H), inf_le_inf_left N (oTwoPrime_le_oTwoPrimeTwo H),
    inf_le_inf_left N hQD, htM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc d hd
    exact Subgroup.mem_inf.2 ⟨(inferInstance : N.Normal).conj_mem d (Subgroup.mem_inf.1 hd).1 c,
      conj_mem_oTwoPrimeTwo (Subgroup.mem_inf.1 hc).2 (Subgroup.mem_inf.1 hd).2⟩
  · intro c hc o ho
    exact Subgroup.mem_inf.2 ⟨(inferInstance : N.Normal).conj_mem o (Subgroup.mem_inf.1 ho).1 c,
      conj_mem_oTwoPrime (Subgroup.mem_inf.1 hc).2 (Subgroup.mem_inf.1 ho).2⟩
  · exact Odd.of_dvd_nat (odd_card_oTwoPrime H) (Subgroup.card_dvd_of_le inf_le_right)
  · intro g hg
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoPrime H (Subgroup.mem_inf.1 hg).2
    exact ⟨k, Subgroup.mem_inf.2 ⟨N.pow_mem (Subgroup.mem_inf.1 hg).1 _, hk⟩⟩
  · exact hQ2.to_le inf_le_right
  · exact hq.card_inf_ge N hcyc

theorem Q16Q16.exists_orderOf_eight_of_out (N : Subgroup Y) [N.Normal]
    (hC : Subgroup.centralizer (N : Set Y) = ⊥) (hO : Nobq.OutTwoCyclic ↥N)
    {x y x' y' : Y} (hq : Q16Q16 x y x' y') : ∃ g ∈ N, orderOf g = 8 := by
  have hQ2 : IsPGroup 2 (Q16Q16.group x y x' y') := by
    refine (isPGroup_sup_of_q16Q16 hq).to_le (sup_le_sup ?_ ?_)
    · refine (Subgroup.closure_le _).2 ?_
      rintro g (rfl | hg)
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · refine (Subgroup.closure_le _).2 ?_
      rintro g (rfl | hg)
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hcyc : IsCyclic ↥((Q16Q16.group x y x' y').map (QuotientGroup.mk' N)) :=
    Nobq.isCyclic_of_outTwoCyclic N hC hO _ (hQ2.map _)
  exact hq.exists_orderOf_eight N (hq.mul_mem_of_cyclic N hcyc)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
