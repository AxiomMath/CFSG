module

public import CFSG.ClassicalInvolution.Q3.Q3CPSix67
public import CFSG.ClassicalInvolution.Q3.TL3C8

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

structure ThinStd (Ω : Set (Subgroup G)) (K : Subgroup G) : Prop where
  hyp : HypOmegaGen Ω
  two : ∀ J ∈ Ω, IsPGroup 2 J
  card : ∀ J ∈ Ω, Nat.card J = 8
  tight : ∀ J ∈ Ω, ∀ u : G, IsUniqueInvolution J u →
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G)
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J
  mem : K ∈ Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J
  gen : (⨆ J ∈ Ω, J) = ⊤
  conn : Disconnected.DConnected Ω
  sep : SepHyp Ω

@[expose] noncomputable def Qz (z : G) : Subgroup G :=
  pCoreOf 2 (Subgroup.centralizer ({z} : Set G))

omit [Finite G] in
theorem isNormalTwoIn_Qz (z : G) : IsNormalTwoIn (Qz z) z := by
  refine ⟨Subgroup.map_subtype_le _,
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 _, ?_⟩
  intro c hc p hp
  have hN : ((Qz z).subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal := by
    unfold Qz
    rw [CFSG.RankThreeEvenClassification.Helpers.pCoreOf_subgroupOf 2 _ _ le_rfl]
    exact CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_of_normal 2 _
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hpC : p ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.map_subtype_le _ hp
  have := hN.conj_mem ⟨p, hpC⟩ (Subgroup.mem_subgroupOf.mpr hp) ⟨c, hc⟩
  exact Subgroup.mem_subgroupOf.mp this

omit [Finite G] in
theorem le_Qz {P : Subgroup G} {z : G} (hP : IsNormalTwoIn P z) : P ≤ Qz z := by
  obtain ⟨hPC, hP2, hPn⟩ := hP
  refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 P _ hPC
    ⟨fun p hp c => ?_⟩ hP2
  exact Subgroup.mem_subgroupOf.mpr (hPn c c.2 p (Subgroup.mem_subgroupOf.mp hp))

omit [Finite G] in
theorem mem_Qz_of_twoIn {z x : G} (h : TwoIn z x) : x ∈ Qz z := by
  obtain ⟨P, hP, hxP⟩ := h
  exact le_Qz hP hxP

omit [Finite G] in
theorem uAt_of_le_Qz {Ω : Set (Subgroup G)} {z : G} {N U : Subgroup G} (hU : U ∈ USet Ω)
    (hUN : U ≤ N) (hUQ : U ≤ Qz z) : UAt Ω z N :=
  ⟨U, hU, hUN, Qz z, isNormalTwoIn_Qz z, hUQ⟩

variable {Ω : Set (Subgroup G)} {K : Subgroup G} (hS : ThinStd Ω K)
include hS

theorem ThinStd.graphFam : GraphFam Ω (nbrAdj Ω) :=
  TC.graphFam hS.hyp hS.two hS.sep hS.trans hS.gen hS.conn

theorem ThinStd.commutes_of_le {J J' P : Subgroup G} (hJ : J ∈ Ω) (hJ' : J' ∈ Ω)
    (hne : J ≠ J') (hP : IsPGroup 2 P) (hJP : J ≤ P) (hJ'P : J' ≤ P) :
    ∀ x ∈ J, ∀ y ∈ J', x * y = y * x := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  exact Q3CP.l67Gen G Ω hS.hyp S J (mem_RSet_of_isPGroup hJ (hS.two J hJ)) J'
    (mem_RSet_of_isPGroup hJ' (hS.two J' hJ')) (hJP.trans hPS) (hJ'P.trans hPS) hne

theorem ThinStd.commutes_of_nbrAdj {J J' : Subgroup G} (h : nbrAdj Ω J J') :
    ∀ x ∈ J, ∀ y ∈ J', x * y = y * x := by
  have hJ := h.1
  have hJ' := h.2.1
  have hN := ((mem_omegaNbr_iff hS.hyp hS.two).mp h.2).2.2
  have hP : IsPGroup 2 ↥(J' ⊔ J : Subgroup G) :=
    (hS.two J' hJ').to_sup_of_normal_right' (hS.two J hJ) hN
  exact hS.commutes_of_le hJ hJ' h.2.2.1.symm hP le_sup_right le_sup_left

theorem ThinStd.le_centralizer_of_nbrAdj {M N : Subgroup G} (h : nbrAdj Ω M N) {z : G}
    (hz : IsUniqueInvolution M z) : N ≤ Subgroup.centralizer ({z} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hS.commutes_of_nbrAdj (hS.graphFam.graph.symm h) x hx z hz.mem

theorem ThinStd.eq_of_mem_Qz {M N : Subgroup G} (hMN : nbrAdj Ω M N) (hth : ThinAt Ω M N)
    {z u : G} (hz : IsUniqueInvolution M z) (hu : IsUniqueInvolution N u) {x : G} (hxN : x ∈ N)
    (hxQ : x ∈ Qz z) : x = 1 ∨ x = u := by
  have hN := hMN.2.1
  by_cases hx2 : x * x = 1
  · exact hu.unique x hxN hx2
  · exfalso
    apply hth.2 z hz
    have h2 := hS.two N hN
    have h8 := hS.card N hN
    have hxord : orderOf x = 4 := by
      have hdvd : orderOf x ∣ 8 := by
        rw [← h8]
        exact Subgroup.orderOf_dvd_natCard N hxN
      have hx1 : x ≠ 1 := fun h => hx2 (by rw [h, one_mul])
      have hne2 : orderOf x ≠ 2 := fun h => hx2 (by rw [← pow_two, ← h, pow_orderOf_eq_one])
      have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
      have hne8 : orderOf x ≠ 8 := by
        intro h
        obtain ⟨-, P, hPN, hPnc⟩ := hS.hyp.omega1 N hN
        have hzN : Subgroup.zpowers x = N := by
          refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxN) ?_
          rw [Nat.card_zpowers, h, h8]
        apply hPnc
        refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
        have ha : (a : G) ∈ Subgroup.zpowers x := hzN ▸ hPN.1 a.2
        have hb : (b : G) ∈ Subgroup.zpowers x := hzN ▸ hPN.1 b.2
        obtain ⟨i, hi⟩ := ha
        obtain ⟨j, hj⟩ := hb
        show (a : G) * b = b * a
        rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
      have : orderOf x ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
      rw [hdiv] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    have hUcard : Nat.card ↥(Subgroup.zpowers x) = 4 := by rw [Nat.card_zpowers, hxord]
    have hNR : N ∈ RSet Ω := mem_RSet_of_isPGroup hN h2
    have hUU : Subgroup.zpowers x ∈ USet Ω := by
      refine ⟨N, hNR, Subgroup.zpowers_le.mpr hxN, inferInstance, ?_⟩
      have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers x) N
      rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr hxN), hUcard, h8] at h1
      omega
    exact uAt_of_le_Qz hUU (Subgroup.zpowers_le.mpr hxN) (Subgroup.zpowers_le.mpr hxQ)

theorem ThinStd.maxAdj_conj_of_mem {M N : Subgroup G} (h : MaxAdj (nbrAdj Ω) M N) {z : G}
    (hz : IsUniqueInvolution M z) {c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    MaxAdj (nbrAdj Ω) M (conjSub c N) := by
  have hM := h.1.1
  have hcM : conjSub c M = M :=
    conjSub_eq_of_mem_normalizer (hS.tight M hM z hz hc)
  have := maxAdj_conj hS.graphFam h c
  rwa [hcM] at this

theorem ThinStd.conj_eq_or_commutes {M N : Subgroup G} (h : MaxAdj (nbrAdj Ω) M N) {z : G}
    (hz : IsUniqueInvolution M z) {q : G} (hq : q ∈ Qz z) :
    conjSub q N = N ∨ ∀ x ∈ N, ∀ y ∈ conjSub q N, x * y = y * x := by
  by_cases heq : conjSub q N = N
  · exact Or.inl heq
  · right
    have hN : N ∈ Ω := h.1.2.1
    have hNz : N ≤ Subgroup.centralizer ({z} : Set G) := hS.le_centralizer_of_nbrAdj h.1 hz
    have hQ := isNormalTwoIn_Qz z
    have hNQ : N ≤ Subgroup.normalizer (Qz z : Set G) := by
      intro n hn
      rw [Subgroup.mem_normalizer_iff]
      intro p
      constructor
      · exact hQ.2.2 n (hNz hn) p
      · intro hp
        have := hQ.2.2 n⁻¹ ((Subgroup.centralizer ({z} : Set G)).inv_mem (hNz hn)) _ hp
        simpa [mul_assoc] using this
    have hP : IsPGroup 2 ↥(N ⊔ Qz z : Subgroup G) :=
      (hS.two N hN).to_sup_of_normal_right' hQ.2.1 hNQ
    have hqN : conjSub q N ≤ N ⊔ Qz z := by
      intro x hx
      rw [mem_conjSub_iff] at hx
      have e : x = q * (q⁻¹ * x * q) * q⁻¹ := by group
      rw [e]
      exact (N ⊔ Qz z).mul_mem ((N ⊔ Qz z).mul_mem (le_sup_right (α := Subgroup G) hq)
        (le_sup_left (α := Subgroup G) hx))
        ((N ⊔ Qz z).inv_mem (le_sup_right (α := Subgroup G) hq))
    exact hS.commutes_of_le hN (hS.hyp.conjInvariant q N hN) (Ne.symm heq) hP le_sup_left hqN

end CFSG.ClassicalInvolution.Q3.TC.Thin
