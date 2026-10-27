module

public import CFSG.ClassicalInvolution.Q3.Sec13StarHyp
import CFSG.ClassicalInvolution.Q3.TL3T29

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {Ω : Set (Subgroup G)} (h : StarHyp Ω)
include h

omit [Finite G] in
private theorem mem_pCore_of_isUniqueInvolution {L : Subgroup G} (hL : L ∈ Ω) {z : G}
    (hz : IsUniqueInvolution L z) : z ∈ pCore 2 G := by
  obtain ⟨Q, hQn, hQ2, hzQ⟩ := h.thmD.inO2 L hL z hz
  exact (le_sSup ⟨hQn, hQ2⟩ : Q ≤ pCore 2 G) hzQ

private theorem mem_dstarComp_of_four_le {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {X : Subgroup G}
    (hXJ : X ≤ J ⊓ Subgroup.centralizer ({z} : Set G)) (hX2 : IsPGroup 2 X)
    (hX4 : 4 ≤ Nat.card X) : J ∈ dstarComp Ω K := by
  have hΩ := h.thmD.hyp
  by_cases hJK : J = K
  · subst hJK
    exact h.mem_dstarComp_self hJ
  by_cases htw : J ∈ twinSet Ω K
  · obtain ⟨-, z', hz'K, hz'J⟩ := htw
    exact Relation.ReflTransGen.single ⟨hJ, Or.inl (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΩ K
      (Q3CL.T3.twin_mem_omegaNbr hΩ hK hJ hJK hz'K hz'J))⟩
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  obtain ⟨V, hV, hXV⟩ := IsSylow2In.exists_ge hX2 hXJ
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  have hV4 : 4 ≤ Nat.card V := hX4.trans (Subgroup.card_le_of_le hXV)
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
  rcases Sec6Gen.l6_2Gen G Ω hΩ K hK z hz J hJ htw t ht V hV
      (ht.mem_of_le hVJ hV.2.1 (by omega)) with
    ⟨hVt, -⟩ | ⟨hVt, -⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, hVK⟩
  · rw [hVt, Nat.card_zpowers, ht2] at hV4
    omega
  · rw [hVt, Nat.card_zpowers, ht2] at hV4
    omega
  · exact Relation.ReflTransGen.single ⟨hJ, Or.inl ⟨hJ, hJK, V, hVU, hVJ, hVN⟩⟩
  ·
    have hVJ' : V = J := ((Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJ hVR hVJ).eq_of_le
      (h.thmD.two J hJ) le_rfl hVJ).symm
    rw [hVJ', TL4.oddCoreOf_eq_bot_of_isPGroup (h.thmD.two K hK)] at hVK
    refine h.mem_dstarComp_of_commutes hJ hK fun x hx y hy => ?_
    have hc := hVK (Subgroup.commutator_mem_commutator hx hy)
    rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc

theorem mem_dstarComp_of_normalizes {L M : Subgroup G} (hL : L ∈ Ω) (hM : M ∈ Ω) {v : G}
    (hv : IsUniqueInvolution M v) (hvL : v ∈ Subgroup.normalizer (L : Set G)) :
    L ∈ dstarComp Ω M := by
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hL
  obtain ⟨X, hXC, hX2, hX4⟩ := (twinT4Hyp_of h.thmD.hyp h.thmD.two h.thmD.card h.thmD.aEmpty
    h.thmD.odd).exists_le_centralizer hL hM hu hv CFSG.pCore_normal CFSG.pCore_isPGroup
    (h.mem_pCore_of_isUniqueInvolution hL hu) (h.mem_pCore_of_isUniqueInvolution hM hv) hvL
  exact h.mem_dstarComp_of_four_le hM hL hv hXC hX2 hX4

theorem eq_one_or_eq_of_mem_pCore {J M : Subgroup G} (hJ : J ∈ Ω) (hM : M ∈ Ω)
    (hJM : J ∉ dstarComp Ω M) {t : G} (ht : IsUniqueInvolution J t) {x : G} (hxJ : x ∈ J)
    (hxQ : x ∈ pCore 2 G) : x = 1 ∨ x = t := by
  refine or_iff_not_imp_left.mpr fun hx1 => ?_
  by_contra hxt
  have hΩ := h.thmD.hyp
  have hJ2 := h.thmD.two J hJ
  have hJ8 : Nat.card J = 8 := by
    have := h.thmD.card J hJ
    norm_num at this
    exact this
  obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hΩ hM
  have hvJ : v ∉ Subgroup.normalizer (J : Set G) := fun hvJ =>
    hJM (h.mem_dstarComp_of_normalizes hJ hM hv hvJ)
  have hdvd : orderOf x ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hJ8]
    exact Subgroup.orderOf_dvd_natCard J hxJ
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hx4 : orderOf x = 4 := by
    interval_cases k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact absurd hk hx1
    · have hx2 : x * x = 1 := by
        have := pow_orderOf_eq_one x
        rwa [hk, pow_one, pow_two] at this
      exact absurd ((ht.unique x hxJ hx2).resolve_left hx1) hxt
    · rw [hk]
      norm_num
    · exfalso
      have hJx : Subgroup.zpowers x = J :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxJ)
          (by rw [Nat.card_zpowers, hk, hJ8]; norm_num)
      obtain ⟨w, hwJ, hw⟩ := Sec6Gen.exists_noncentral hΩ hJ le_rfl hJ2 (by omega)
      refine hw fun y hy => ?_
      rw [← hJx] at hwJ hy
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwJ
      obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_zpow_self x a b).eq
  have hJs : IsSylow2In J J := ⟨le_rfl, hJ2, fun _ hV'J _ hJV' => le_antisymm hV'J hJV'⟩
  have hU : Subgroup.zpowers x ∈ USet Ω :=
    mem_USet_of_natCard hJ hJs (Subgroup.zpowers_le.mpr hxJ) inferInstance
      (by rw [Nat.card_zpowers, hx4, hJ8])
  exact not_le_of_not_mem_normalizer hΩ h.thmD.two hJ hM hv hvJ CFSG.pCore_normal
    CFSG.pCore_isPGroup hU (Subgroup.zpowers_le.mpr hxJ) (Subgroup.zpowers_le.mpr hxQ)

theorem mem_dstarComp_of_le {P : Subgroup G} (hP : IsPGroup 2 P) {L M : Subgroup G} (hL : L ∈ Ω)
    (hM : M ∈ Ω) (hLP : L ≤ P) (hMP : M ≤ P) : L ∈ dstarComp Ω M := by
  by_cases hLM : L = M
  · subst hLM
    exact h.mem_dstarComp_self hL
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  exact h.mem_dstarComp_of_commutes hL hM (Q3CP.l67Gen G Ω h.thmD.hyp S L
    (TC.mem_RSet_of_isPGroup hL (h.thmD.two L hL)) M
    (TC.mem_RSet_of_isPGroup hM (h.thmD.two M hM)) (hLP.trans hS) (hMP.trans hS) hLM)

theorem le_compStab {P : Subgroup G} (hP : IsPGroup 2 P) {K : Subgroup G} (hK : K ∈ Ω)
    (hKP : K ≤ P) : P ≤ compStab Ω K := fun s hs =>
  (h.mem_compStab_iff hK).mpr (h.mem_dstarComp_of_le hP (h.thmD.hyp.conjInvariant s K hK) hK
    ((conjSub_mono hKP).trans (conjSub_eq_self_of_mem hs).le) hKP)

theorem not_mem_compStab {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hJK : J ∉ dstarComp Ω K) {u : G} (hu : u ∈ J) (hu4 : orderOf u = 4) :
    u ∉ compStab Ω K := by
  intro huC
  have hΩ := h.thmD.hyp
  obtain ⟨S, hKS⟩ := (h.thmD.two K hK).exists_le_sylow
  have hSs : IsSylow2In (S : Subgroup G) (compStab Ω K) :=
    ⟨h.le_compStab S.isPGroup' hK hKS, S.isPGroup', fun _ _ hV2 hSV => S.is_maximal' hV2 hSV⟩
  obtain ⟨T, hT, huT⟩ := IsSylow2In.exists_ge
    ((h.thmD.two J hJ).to_le (Subgroup.zpowers_le.mpr hu)) (Subgroup.zpowers_le.mpr huC)
  obtain ⟨x, hxC, hxT⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hT hSs
  have hJ' : conjSub x J ∈ Ω := hΩ.conjInvariant x J hJ
  have hJ'K : conjSub x J ∉ dstarComp Ω K := fun hc => hJK ((mem_compStab.mp hxC J).mpr hc)
  have hJ'S : 2 < Nat.card ↥(conjSub x J ⊓ (S : Subgroup G)) := by
    have hle : conjSub x (Subgroup.zpowers u) ≤ conjSub x J ⊓ (S : Subgroup G) :=
      le_inf (conjSub_mono (Subgroup.zpowers_le.mpr hu)) ((conjSub_mono huT).trans hxT.le)
    have hc : Nat.card ↥(conjSub x (Subgroup.zpowers u)) = 4 := by
      rw [← hu4, ← Nat.card_zpowers]
      exact Subgroup.card_map_of_injective (MulAut.conj x).injective
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨η, hηS, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hη : η ∈ etaG Ω := ⟨S, hηS, hinv⟩
  have hηle : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hηS.1 hV).2
  have hW2 : IsPGroup 2 ↥(⨆ V ∈ η, V) := TC.etaSpan_isPGroup hη
  have hKW : K ⊓ (⨆ V ∈ η, V) ∈ η := Sec6Gen.l6_11Gen G Ω hΩ S η hη hηle K hK (by
    rw [inf_eq_left.mpr hKS, h.thmD.card K hK]
    norm_num)
  have hJW : conjSub x J ⊓ (⨆ V ∈ η, V) ∈ η :=
    Sec6Gen.l6_11Gen G Ω hΩ S η hη hηle _ hJ' hJ'S
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨-, -, -, -, -, -, -, -, h4K⟩ := Sec6Gen.exists_data_of_mem_USet hΩ (hηS.1 hKW).1
  obtain ⟨-, -, -, -, -, -, -, -, h4J⟩ := Sec6Gen.exists_data_of_mem_USet hΩ (hηS.1 hJW).1
  have hzW : z ∈ ⨆ V ∈ η, V :=
    (hz.mem_of_le inf_le_left (hW2.to_le inf_le_right) (by omega)).2
  have hWc := TC.etaSpan_comm hΩ hη
  have hle : conjSub x J ⊓ (⨆ V ∈ η, V) ≤
      conjSub x J ⊓ Subgroup.centralizer ({z} : Set G) := fun y hy =>
    ⟨hy.1, Subgroup.mem_centralizer_singleton_iff.mpr (hWc y hy.2 z hzW)⟩
  exact hJ'K (h.mem_dstarComp_of_four_le hK hJ' hz hle (hW2.to_le inf_le_right) h4J)

end StarHyp

end CFSG.ClassicalInvolution.Q3.Sec13
