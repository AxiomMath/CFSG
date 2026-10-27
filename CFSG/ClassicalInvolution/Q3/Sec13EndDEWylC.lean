module

public import CFSG.ClassicalInvolution.Q3.Sec13EndDEWylB

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def dewQstar (Ω : Set (Subgroup G)) : Subgroup G :=
  ⨆ K ∈ Ω, ⨆ J ∈ twinSet Ω K, dewDelta K J

@[expose] def dewTauGroup (Ω : Set (Subgroup G)) (u v : G) :
    Subgroup (Equiv.Perm ↥(dew1V Ω u)) :=
  Subgroup.closure {σ | ∃ K ∈ dew1V Ω v, ∃ J ∈ dew1V Ω v,
    ∀ M : ↥(dew1V Ω u), ((σ M : ↥(dew1V Ω u)) : Subgroup G) = dewTau K J (M : Subgroup G)}

theorem dewDelta_le_pCore (K J : Subgroup G) : dewDelta K J ≤ pCore 2 G := inf_le_right

theorem dewQstar_le_pCore (Ω : Set (Subgroup G)) : dewQstar Ω ≤ pCore 2 G :=
  iSup₂_le fun K _ => iSup₂_le fun J _ => dewDelta_le_pCore K J

theorem dewDelta_le_dewQstar {Ω : Set (Subgroup G)} {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ twinSet Ω K) : dewDelta K J ≤ dewQstar Ω :=
  le_iSup₂_of_le K hK (le_iSup₂_of_le J hJ le_rfl)

theorem dewc_conjSub_sup (g : G) (K J : Subgroup G) :
    conjSub g (K ⊔ J) = conjSub g K ⊔ conjSub g J :=
  Subgroup.map_sup _ _ _

theorem dewc_closure_comm {M : Type*} [Group M] (S : Set M)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {a b : M} (ha : a ∈ Subgroup.closure S)
    (hb : b ∈ Subgroup.closure S) : a * b = b * a := by
  have hC : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro c hc
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro t ht
    exact hS t ht c hc
  have hC2 : Subgroup.closure S ≤ Subgroup.centralizer ({b} : Set M) := by
    rw [Subgroup.closure_le]
    intro t ht
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hC hb) t ht
  exact Subgroup.mem_centralizer_singleton_iff.mp (hC2 ha)

theorem dewc_not_mem_zpowers {u w : G} (hu2 : u * u = 1) (hu1 : u ≠ 1) (hw : w ≠ 1)
    (hwu : w ≠ u) : w ∉ Subgroup.zpowers u := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have hk2 := zpow_mod_orderOf u k
  rw [hord] at hk2
  have hk3 : u ^ (k % 2) = u ^ k := by simpa using hk2
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · apply hw
    rw [← hk, ← hk3, h0, zpow_zero]
  · apply hwu
    rw [← hk, ← hk3, h1, zpow_one]

namespace DE4Hyp

variable {Ω : Set (Subgroup G)} (h : DE4Hyp Ω)
include h

theorem dewc_exists_notin_zpowers {u : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1)
    (hu2 : u * u = 1) : ∃ v ∈ zGroup Ω, v ∉ Subgroup.zpowers u := by
  by_contra hcon
  push Not at hcon
  have hle : zGroup Ω ≤ Subgroup.zpowers u := fun x hx => hcon x hx
  have h1 := Subgroup.card_le_of_le hle
  rw [h.card_zGroup, card_zpowers_of_involution hu2 hu1] at h1
  omega

theorem dewQstar_normal : (dewQstar Ω).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hsub : dewQstar Ω ≤ (dewQstar Ω).comap (MulAut.conj g).toMonoidHom := by
    unfold dewQstar
    refine iSup₂_le fun K hK => iSup₂_le fun J hJ => fun x hx => ?_
    obtain ⟨hxKJ, hxQ⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hJΩ, z, hz, hzJ⟩ := hJ
    have htw : conjSub g J ∈ twinSet Ω (conjSub g K) :=
      ⟨h.hyp.conjInvariant g J hJΩ, g * z * g⁻¹, hz.conj g, hzJ.conj g⟩
    have hK' : conjSub g K ∈ Ω := h.hyp.conjInvariant g K hK
    haveI : (pCore 2 G).Normal := CFSG.pCore_normal
    have hmem : g * x * g⁻¹ ∈ dewDelta (conjSub g K) (conjSub g J) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : g * x * g⁻¹ ∈ conjSub g (K ⊔ J) := conj_mem_conjSub hxKJ
        rwa [dewc_conjSub_sup] at h1
      · exact (inferInstance : (pCore 2 G).Normal).conj_mem x hxQ g
    exact dewDelta_le_dewQstar hK' htw hmem
  exact hsub hn

theorem zGroup_le_dewQstar : zGroup Ω ≤ dewQstar Ω := by
  unfold zGroup
  rw [Subgroup.closure_le]
  rintro u ⟨K, hK, hu⟩
  obtain ⟨J, hJ, hJK⟩ : ∃ J ∈ twinSet Ω K, J ≠ K := by
    by_contra hcon
    push Not at hcon
    have hsub : twinSet Ω K ⊆ {K} := fun J hJ => hcon J hJ
    have h1 := Set.ncard_le_ncard hsub (Set.finite_singleton K)
    rw [Set.ncard_singleton, h.twin4 K hK] at h1
    omega
  obtain ⟨hJΩ, z, hz, hzJ⟩ := hJ
  have hzu : u = z := hu.eq hz
  have hJu : IsUniqueInvolution J u := by
    rw [hzu]
    exact hzJ
  have tw : DewTwins Ω K J u := ⟨hK, hJΩ, hu, hJu, hJK.symm⟩
  exact dewDelta_le_dewQstar hK ⟨hJΩ, u, hu, hJu⟩
    (h.zpowers_le_dewDelta tw (Subgroup.mem_zpowers u))

theorem commutator_mem_dewQstar {K : Subgroup G} (hK : K ∈ Ω) {k q : G} (hk : k ∈ K)
    (hq : q ∈ pCore 2 G) : k * q * k⁻¹ * q⁻¹ ∈ dewQstar Ω := by
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
  have hqC : q ∈ Subgroup.centralizer (zGroup Ω : Set G) := h.pCore_le_centralizer_zGroup hq
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hu
  have hcomm : u * q = q * u := Subgroup.mem_centralizer_iff.mp hqC u huD
  have hqu : q * u * q⁻¹ = u := by
    rw [← hcomm]
    group
  have hJ : conjSub q K ∈ twinSet Ω K := by
    refine ⟨h.hyp.conjInvariant q K hK, u, hu, ?_⟩
    have hc := hu.conj q
    rwa [hqu] at hc
  have hkJ : q * k⁻¹ * q⁻¹ ∈ conjSub q K := conj_mem_conjSub (K.inv_mem hk)
  have hKJ : k * (q * k⁻¹ * q⁻¹) ∈ K ⊔ conjSub q K := Subgroup.mul_mem_sup hk hkJ
  have hpc : k * q * k⁻¹ * q⁻¹ ∈ pCore 2 G := by
    have h1 : k * q * k⁻¹ ∈ pCore 2 G := (inferInstance : (pCore 2 G).Normal).conj_mem q hq k
    exact (pCore 2 G).mul_mem h1 ((pCore 2 G).inv_mem hq)
  have hmem : k * q * k⁻¹ * q⁻¹ ∈ dewDelta K (conjSub q K) := by
    refine Subgroup.mem_inf.mpr ⟨?_, hpc⟩
    have e : k * q * k⁻¹ * q⁻¹ = k * (q * k⁻¹ * q⁻¹) := by group
    rw [e]
    exact hKJ
  exact dewDelta_le_dewQstar hK hJ hmem

theorem exists_sylow_dew :
    ∃ (X : Subgroup G) (S : Sylow 2 G), X ≤ (S : Subgroup G) ∧
      pCore 2 G ⊓ X ≤ dewQstar Ω ∧ pCore 2 G ⊔ X = (S : Subgroup G) := by
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  obtain ⟨K, hK, -, -, -⟩ := h.exists_ne
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hK
  have hz1 : z ≠ 1 := hz.ne_one
  have hz2 : z * z = 1 := hz.sq
  have hzD : z ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hz
  obtain ⟨t, htD, htz⟩ := h.dewc_exists_notin_zpowers hzD hz1 hz2
  have ht1 : t ≠ 1 := fun h1 => htz (h1 ▸ Subgroup.one_mem _)
  have htt : t * t = 1 := h.zGroup_mul_self t htD
  have hzt : z ≠ t := fun h1 => htz (h1 ▸ Subgroup.mem_zpowers _)
  have hztz : z ∉ Subgroup.zpowers t := dewc_not_mem_zpowers htt ht1 hz1 hzt
  obtain ⟨L, hL, hLt⟩ := (h.mem_zGroup_iff.mp htD).resolve_left ht1
  have hcardC : Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set G)) = 4 :=
    (h.card_inf_centralizer_dew hL hLt hzD hztz).1
  obtain ⟨x, hxC, hxt⟩ : ∃ x ∈ L ⊓ Subgroup.centralizer ({z} : Set G),
      x ∉ Subgroup.zpowers t := by
    by_contra hcon
    push Not at hcon
    have hle : L ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.zpowers t :=
      fun y hy => hcon y hy
    have h4 := Subgroup.card_le_of_le hle
    rw [hcardC, card_zpowers_of_involution htt ht1] at h4
    omega
  have hxL : x ∈ L := hxC.1
  obtain ⟨i₀, j₀, hi₀, hj₀, hii₀, hjj₀, hji₀, hnf₀⟩ :=
    exists_q8_gen hLt (h.isQuatSub_of_mem hL) (h.card L hL)
  have hxsq : x * x = t := det_tw_q8_sq ⟨hLt, hi₀, hj₀, hii₀, hjj₀, hji₀, hnf₀⟩ hxL hxt
  have hxN : x ∈ Subgroup.normalizer (K : Set G) :=
    h.inf_centralizer_le_normalizer hL hLt hzD hztz (Or.inl ⟨hK, hz⟩) hxC
  have hzpN : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hxN
  have hxKQ : x ∉ K ⊔ pCore 2 G := by
    intro hxKQ'
    obtain ⟨k, hk, q, hq, hkq⟩ := Subgroup.mem_sup_of_normal_right.mp hxKQ'
    have hxC' : x ∉ Subgroup.centralizer (zGroup Ω : Set G) := by
      intro hc
      have hxin : x ∈ L ⊓ Subgroup.centralizer (zGroup Ω : Set G) := ⟨hxL, hc⟩
      rw [h.inf_centralizer_zGroup hL hLt] at hxin
      exact hxt hxin
    obtain ⟨d, hd, hdx⟩ : ∃ d ∈ zGroup Ω, d * x ≠ x * d := by
      by_contra hcon
      push Not at hcon
      exact hxC' (Subgroup.mem_centralizer_iff.mpr fun d hd => hcon d hd)
    have hxd : x * d * x⁻¹ = t * d := by
      rcases h.conj_eq_or_mul hL hLt hxL hd with h1 | h1
      · exfalso
        apply hdx
        calc d * x = x * d * x⁻¹ * x := by rw [h1]
          _ = x * d := by group
      · exact h1
    have hkd : k * d * k⁻¹ = x * d * x⁻¹ := by
      have hdq : d * q = q * d :=
        Subgroup.mem_centralizer_iff.mp (h.pCore_le_centralizer_zGroup hq) d hd
      have hqd : q * d * q⁻¹ = d := by
        rw [← hdq]
        group
      rw [← hkq]
      calc k * d * k⁻¹ = k * (q * d * q⁻¹) * k⁻¹ := by rw [hqd]
        _ = k * q * d * (k * q)⁻¹ := by group
    have hk3 : k * d * k⁻¹ = d ∨ k * d * k⁻¹ = z * d := h.conj_eq_or_mul hK hz hk hd
    rw [hkd, hxd] at hk3
    rcases hk3 with h3 | h3
    · apply ht1
      exact mul_right_cancel (h3.trans (one_mul d).symm)
    · apply hzt
      exact (mul_right_cancel h3).symm
  set X : Subgroup G := K ⊔ Subgroup.zpowers x with hXdef
  set P : Subgroup G := pCore 2 G ⊔ X with hPdef
  have hKX : K ≤ X := le_sup_left
  have hzpX : Subgroup.zpowers x ≤ X := le_sup_right
  have hXP : X ≤ P := le_sup_right
  have hQP : pCore 2 G ≤ P := le_sup_left
  have hKQP : K ⊔ pCore 2 G ≤ P := sup_le (hKX.trans hXP) hQP
  have hxP : x ∈ P := hXP (hzpX (Subgroup.mem_zpowers x))
  have hX2 : IsPGroup 2 X := IsPGroup.to_sup_of_normal_left' (h.two K hK)
    (IsPGroup.to_le (h.two L hL) (Subgroup.zpowers_le.mpr hxL)) hzpN
  have hP2 : IsPGroup 2 P :=
    IsPGroup.to_sup_of_normal_left (CFSG.pCore_isPGroup : IsPGroup 2 (pCore 2 G)) hX2
  have hQidx : (pCore 2 G).index = 168 := by
    rw [← h.centralizer_zGroup_eq_pCore]
    exact h.index_centralizer_zGroup
  have hQK : (pCore 2 G).relIndex K = 4 := by
    have h1 := Subgroup.relIndex_mul_card (pCore 2 G) K
    rw [inf_comm, h.inf_pCore hK hz, card_zpowers_of_involution hz2 hz1, h.card K hK] at h1
    omega
  have hQKX : (pCore 2 G).relIndex (K ⊔ pCore 2 G) = 4 := by
    rw [Subgroup.relIndex_sup_right, hQK]
  have hQP' : (pCore 2 G).relIndex P = 4 * (K ⊔ pCore 2 G).relIndex P := by
    have h1 := Subgroup.relIndex_mul_relIndex (pCore 2 G) (K ⊔ pCore 2 G) P le_sup_right hKQP
    rw [hQKX] at h1
    omega
  have hr2 : (K ⊔ pCore 2 G).relIndex P ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact hxKQ (h1 hxP)
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hP2
  have hrn : (K ⊔ pCore 2 G).relIndex P ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.relIndex_dvd_card _ _
  have hQ168 : (pCore 2 G).relIndex P ∣ 168 := by
    have h1 := Subgroup.relIndex_mul_index hQP
    rw [hQidx] at h1
    exact ⟨P.index, h1.symm⟩
  have hr : (K ⊔ pCore 2 G).relIndex P = 2 := by
    have h42 : (K ⊔ pCore 2 G).relIndex P ∣ 42 := by
      rw [hQP'] at hQ168
      have h4 : 4 * (K ⊔ pCore 2 G).relIndex P ∣ 4 * 42 := hQ168
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4
    have hcop : Nat.Coprime ((K ⊔ pCore 2 G).relIndex P) 21 :=
      Nat.Coprime.coprime_dvd_left hrn (Nat.Coprime.pow_left n (by norm_num))
    have h2 : (K ⊔ pCore 2 G).relIndex P ∣ 2 := by
      have h21 : (K ⊔ pCore 2 G).relIndex P ∣ 2 * 21 := h42
      exact hcop.dvd_of_dvd_mul_right h21
    have hr0 : (K ⊔ pCore 2 G).relIndex P ≠ 0 := by
      intro h0
      rw [h0] at h2
      norm_num at h2
    have hle := Nat.le_of_dvd (by norm_num) h2
    omega
  have hQP8 : (pCore 2 G).relIndex P = 8 := by
    rw [hQP', hr]
  have hcardP : Nat.card P = 8 * Nat.card (pCore 2 G) := by
    have h1 := Subgroup.relIndex_mul_card (pCore 2 G) P
    rw [inf_eq_left.mpr hQP, hQP8] at h1
    omega
  have hPidx : P.index = 21 := by
    have h1 := Subgroup.card_mul_index P
    have h2 := Subgroup.card_mul_index (pCore 2 G)
    rw [hcardP] at h1
    rw [hQidx] at h2
    have hpos : 0 < 8 * Nat.card (pCore 2 G) := by
      have := Nat.card_pos (α := ↥(pCore 2 G))
      omega
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc 8 * Nat.card (pCore 2 G) * P.index = Nat.card G := h1
      _ = Nat.card (pCore 2 G) * 168 := h2.symm
      _ = 8 * Nat.card (pCore 2 G) * 21 := by ring
  have hD : pCore 2 G ⊓ X ≤ zGroup Ω := by
    intro y hy
    obtain ⟨hyQ, hyX⟩ := Subgroup.mem_inf.mp hy
    have hyX' : y ∈ (K : Set G) * (Subgroup.zpowers x : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K (Subgroup.zpowers x) hzpN]
      exact hyX
    obtain ⟨k, hk, w, hw, hkw⟩ := Set.mem_mul.mp hyX'
    have hwKQ : w ∈ K ⊔ pCore 2 G := by
      have e : w = k⁻¹ * y := by
        rw [← hkw]
        group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left (K.inv_mem hk)) (Subgroup.mem_sup_right hyQ)
    have hx2z : x ^ (2 : ℤ) = t := by
      rw [zpow_two, hxsq]
    have hdec : ∀ m : ℤ, x ^ m = x ^ (m % 2) * t ^ (m / 2) := by
      intro m
      have e : m = m % 2 + 2 * (m / 2) := by omega
      conv_lhs => rw [e]
      rw [zpow_add, zpow_mul, hx2z]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hw
    have htQ : t ∈ zGroup Ω := htD
    have hwz : w ∈ zGroup Ω := by
      rcases Int.emod_two_eq_zero_or_one i with he | he
      · rw [← hi, hdec i, he, zpow_zero, one_mul]
        exact Subgroup.zpow_mem _ htD _
      · exfalso
        apply hxKQ
        have e2 : x = w * (t ^ (i / 2))⁻¹ := by
          rw [← hi, hdec i, he, zpow_one]
          group
        have htQ' : t ^ (i / 2) ∈ pCore 2 G := h.zGroup_le_pCore (Subgroup.zpow_mem _ htD _)
        rw [e2]
        exact mul_mem hwKQ (Subgroup.mem_sup_right ((pCore 2 G).inv_mem htQ'))
    have hwQ : w ∈ pCore 2 G := h.zGroup_le_pCore hwz
    have hkz : k ∈ zGroup Ω := by
      have hkQ : k ∈ pCore 2 G := by
        have e3 : k = y * w⁻¹ := by
          rw [← hkw]
          group
        rw [e3]
        exact (pCore 2 G).mul_mem hyQ ((pCore 2 G).inv_mem hwQ)
      have hkK : k ∈ K ⊓ pCore 2 G := Subgroup.mem_inf.mpr ⟨hk, hkQ⟩
      rw [h.inf_pCore hK hz] at hkK
      exact (Subgroup.zpowers_le.mpr hzD) hkK
    rw [← hkw]
    exact mul_mem hkz hwz
  obtain ⟨S, hPS⟩ := IsPGroup.exists_le_sylow hP2
  have hdvd21 : P.relIndex (S : Subgroup G) ∣ 21 := by
    have h1 := Subgroup.relIndex_mul_index hPS
    rw [hPidx] at h1
    exact ⟨(S : Subgroup G).index, h1.symm⟩
  have hSdvd : P.relIndex (S : Subgroup G) ∣ 2 ^ Nat.factorization (Nat.card G) 2 := by
    rw [← Sylow.card_eq_multiplicity S]
    exact Subgroup.relIndex_dvd_card _ _
  have hcop2 : Nat.Coprime (2 ^ Nat.factorization (Nat.card G) 2) 21 :=
    Nat.Coprime.pow_left _ (by norm_num)
  have hrel1 : P.relIndex (S : Subgroup G) = 1 := by
    have h1 := Nat.dvd_gcd hSdvd hdvd21
    rw [Nat.Coprime.gcd_eq_one hcop2] at h1
    exact Nat.dvd_one.mp h1
  have hPS' : P = (S : Subgroup G) := le_antisymm hPS (Subgroup.relIndex_eq_one.mp hrel1)
  refine ⟨X, S, hXP.trans hPS'.le, fun y hy => h.zGroup_le_dewQstar (hD hy), hPS'⟩

theorem pCore_le_dewQstar : pCore 2 G ≤ dewQstar Ω := by
  classical
  haveI := h.dewQstar_normal
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  obtain ⟨X, S, hXS, hXQ, hQX⟩ := h.exists_sylow_dew
  have hperf : (⊤ : Subgroup G) ≤ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
    le_of_eq h.commutator_eq_top.symm
  let Z : Subgroup G :=
    { carrier := {g | ∀ q ∈ pCore 2 G, g * q * g⁻¹ * q⁻¹ ∈ dewQstar Ω}
      one_mem' := fun q _ => by simpa using (dewQstar Ω).one_mem
      mul_mem' := by
        intro g g' hg hg' q hq
        have e : g * g' * q * (g * g')⁻¹ * q⁻¹ =
            g * (g' * q * g'⁻¹ * q⁻¹) * g⁻¹ * (g * q * g⁻¹ * q⁻¹) := by group
        rw [e]
        exact (dewQstar Ω).mul_mem
          ((inferInstance : (dewQstar Ω).Normal).conj_mem _ (hg' q hq) g) (hg q hq)
      inv_mem' := by
        intro g hg q hq
        have e : g⁻¹ * q * g⁻¹⁻¹ * q⁻¹ = g⁻¹ * (g * q * g⁻¹ * q⁻¹)⁻¹ * g⁻¹⁻¹ := by group
        rw [e]
        exact (inferInstance : (dewQstar Ω).Normal).conj_mem _
          ((dewQstar Ω).inv_mem (hg q hq)) g⁻¹ }
  have hZ : Z = ⊤ := by
    rw [eq_top_iff, ← h.gen]
    refine pSpan_le fun K hK k hk q hq => ?_
    exact h.commutator_mem_dewQstar hK hk hq
  have hcent : ∀ g : G, ∀ q ∈ pCore 2 G, QuotientGroup.mk' (dewQstar Ω) g *
      QuotientGroup.mk' (dewQstar Ω) q = QuotientGroup.mk' (dewQstar Ω) q *
      QuotientGroup.mk' (dewQstar Ω) g := by
    intro g q hq
    have hg : g ∈ Z := hZ ▸ Subgroup.mem_top g
    have h1 := Z.inv_mem hg q hq
    have h2 := (inferInstance : (dewQstar Ω).Normal).conj_mem _ h1 q⁻¹
    change ((g : G ⧸ dewQstar Ω) * (q : G ⧸ dewQstar Ω) = (q : G ⧸ dewQstar Ω) * g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have e : (g * q)⁻¹ * (q * g) = q⁻¹ * (g⁻¹ * q * g⁻¹⁻¹ * q⁻¹) * q⁻¹⁻¹ := by group
    rw [e]
    exact h2
  exact deq2_le_of_central_quotient (dewQstar_le_pCore Ω) CFSG.pCore_isPGroup hcent hperf S hXS
    hXQ hQX

theorem dewQstar_eq_pCore : dewQstar Ω = pCore 2 G :=
  le_antisymm (dewQstar_le_pCore Ω) h.pCore_le_dewQstar

theorem dewc_dewTau_comm_base {K X Y : Subgroup G} {u v : G} (hK : K ∈ dew1V Ω v)
    (hX : X ∈ dew1V Ω v) (hY : Y ∈ dew1V Ω v) (hvu : u ≠ v) {N : Subgroup G}
    (hN : N ∈ dew1V Ω u) : dewTau K X (dewTau K Y N) = dewTau K Y (dewTau K X N) := by
  have hXN : dewTau K X N ∈ dew1V Ω u := h.dewTau_mem hK hX hvu hN
  have hYN : dewTau K Y N ∈ dew1V Ω u := h.dewTau_mem hK hY hvu hN
  have hb : dewTau K Y (dewTau K X N) = dewTau X Y N := by
    have h1 := h.dewTau_comp hK hX hY hvu hXN
    rw [h.dewTau_dewTau hK hX hvu hN] at h1
    exact h1.symm
  have hc : dewTau K X (dewTau K Y N) = dewTau X Y N := by
    have h1 : dewTau X Y (dewTau K X (dewTau K Y N)) = N := by
      rw [h.dewTau_comp hK hX hY hvu hYN, h.dewTau_dewTau hK hY hvu hN]
    have hW : dewTau K X (dewTau K Y N) ∈ dew1V Ω u := h.dewTau_mem hK hX hvu hYN
    calc dewTau K X (dewTau K Y N)
        = dewTau X Y (dewTau X Y (dewTau K X (dewTau K Y N))) :=
          (h.dewTau_dewTau hX hY hvu hW).symm
      _ = dewTau X Y N := by rw [h1]
  rw [hb, hc]

theorem dewTau_comm {K J K' J' : Subgroup G} {u v : G} (hK : K ∈ dew1V Ω v)
    (hJ : J ∈ dew1V Ω v) (hK' : K' ∈ dew1V Ω v) (hJ' : J' ∈ dew1V Ω v) (hvu : u ≠ v)
    {M : Subgroup G} (hM : M ∈ dew1V Ω u) :
    dewTau K J (dewTau K' J' M) = dewTau K' J' (dewTau K J M) := by
  have formula : ∀ {A B : Subgroup G}, A ∈ dew1V Ω v → B ∈ dew1V Ω v →
      ∀ {N : Subgroup G}, N ∈ dew1V Ω u → dewTau A B N = dewTau K B (dewTau K A N) := by
    intro A B hA hB N hN
    have hP : dewTau K A N ∈ dew1V Ω u := h.dewTau_mem hK hA hvu hN
    have h1 := h.dewTau_comp hK hA hB hvu hP
    rw [h.dewTau_dewTau hK hA hvu hN] at h1
    exact h1
  have hJM : dewTau K J M ∈ dew1V Ω u := h.dewTau_mem hK hJ hvu hM
  rw [formula hK' hJ' hM, formula hK' hJ' hJM]
  have c1 := h.dewc_dewTau_comm_base hK hJ hJ' hvu (h.dewTau_mem hK hK' hvu hM)
  have c2 := h.dewc_dewTau_comm_base hK hJ hK' hvu hM
  rw [c1, c2]

theorem exists_dewTau_eq {u v v' : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) (hv : v ∈ zGroup Ω)
    (hv' : v' ∈ zGroup Ω) (hvu : v ∉ Subgroup.zpowers u) (hv'u : v' ∉ Subgroup.zpowers u)
    {K J : Subgroup G} (hK : K ∈ dew1V Ω v) (hJ : J ∈ dew1V Ω v) :
    ∃ K' ∈ dew1V Ω v', ∃ J' ∈ dew1V Ω v', ∀ M ∈ dew1V Ω u, dewTau K' J' M = dewTau K J M := by
  obtain ⟨w, hw, hwv⟩ := h.exists_kernel_conj hu hu1 hv hv' hvu hv'u
  obtain ⟨-, hfix⟩ := (h.mem_dewKer_iff).mp hw
  have hvu' : u ≠ v := fun h1 => hvu (h1 ▸ Subgroup.mem_zpowers _)
  have hne : v ≠ v * u := fun h1 => hu1 (mul_left_cancel (a := v) (by rw [mul_one]; exact h1.symm))
  have hK' : conjSub w K ∈ dew1V Ω v' := by
    obtain ⟨hKΩ, hKv⟩ := hK
    refine ⟨h.hyp.conjInvariant w K hKΩ, ?_⟩
    have hc := hKv.conj w
    rwa [hwv] at hc
  have hJ' : conjSub w J ∈ dew1V Ω v' := by
    obtain ⟨hJΩ, hJv⟩ := hJ
    refine ⟨h.hyp.conjInvariant w J hJΩ, ?_⟩
    have hc := hJv.conj w
    rwa [hwv] at hc
  refine ⟨conjSub w K, hK', conjSub w J, hJ', fun M hM => ?_⟩
  have sp1 : DewPair Ω K M v u := ⟨hK.1, hM.1, hK.2, hM.2, hvu'.symm⟩
  have hN : dewStar K M ∈ dew1V Ω (v * u) := h.dewStar_mem_dew1V sp1
  have sp2 : DewPair Ω J (dewStar K M) v (v * u) := ⟨hJ.1, hN.1, hJ.2, hN.2, hne⟩
  have hMfix : conjSub w M = M := hfix M hM
  have e1 : conjSub w (dewStar K M) = dewStar (conjSub w K) M := by
    have := h.conjSub_dewStar sp1 w
    rwa [hMfix] at this
  have e2 := h.conjSub_dewStar sp2 w
  have key : conjSub w (dewTau K J M) = dewTau (conjSub w K) (conjSub w J) M := by
    unfold dewTau
    rw [e2, e1]
  rw [← key]
  exact hfix _ (h.dewTau_mem hK hJ hvu' hM)

theorem dewc_gen_comm {u v : G} (hvu : u ≠ v) {a b : Equiv.Perm ↥(dew1V Ω u)}
    (ha : ∃ K ∈ dew1V Ω v, ∃ J ∈ dew1V Ω v, ∀ M : ↥(dew1V Ω u),
      ((a M : ↥(dew1V Ω u)) : Subgroup G) = dewTau K J (M : Subgroup G))
    (hb : ∃ K ∈ dew1V Ω v, ∃ J ∈ dew1V Ω v, ∀ M : ↥(dew1V Ω u),
      ((b M : ↥(dew1V Ω u)) : Subgroup G) = dewTau K J (M : Subgroup G)) :
    a * b = b * a := by
  obtain ⟨K, hK, J, hJ, ha⟩ := ha
  obtain ⟨K', hK', J', hJ', hb⟩ := hb
  refine Equiv.ext fun M => Subtype.ext ?_
  simp only [Equiv.Perm.mul_apply, ha, hb]
  exact h.dewTau_comm hK hJ hK' hJ' hvu M.2

theorem dewTauGroup_comm {u v : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) (hvu : u ≠ v)
    {σ σ' : Equiv.Perm ↥(dew1V Ω u)} (hσ : σ ∈ dewTauGroup Ω u v)
    (hσ' : σ' ∈ dewTauGroup Ω u v) : σ * σ' = σ' * σ := by
  refine dewc_closure_comm _ ?_ hσ hσ'
  intro a ha b hb
  exact h.dewc_gen_comm hvu ha hb

theorem dewTauGroup_mul_self {u v : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) (hvu : u ≠ v)
    {σ : Equiv.Perm ↥(dew1V Ω u)} (hσ : σ ∈ dewTauGroup Ω u v) : σ * σ = 1 := by
  unfold dewTauGroup at hσ
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨K, hK, J, hJ, hx⟩ := hx
    refine Equiv.ext fun M => Subtype.ext ?_
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hx]
    exact h.dewTau_dewTau hK hJ hvu M.2
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc : x * y = y * x :=
      dewc_closure_comm _ (fun a ha b hb => h.dewc_gen_comm hvu ha hb) hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc]
      _ = x * x * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, mul_one]
  | inv x hx ihx =>
    have h1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right ihx
    rw [h1, ihx]

theorem exists_mem_dewTauGroup {u v : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) (hv : v ∈ zGroup Ω)
    (hvu : v ∉ Subgroup.zpowers u) {q : G} (hq : q ∈ pCore 2 G) :
    ∃ σ ∈ dewTauGroup Ω u v, ∀ M : ↥(dew1V Ω u),
      ((σ M : ↥(dew1V Ω u)) : Subgroup G) = conjSub q (M : Subgroup G) := by
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  have huv : u ≠ v := fun h1 => hvu (h1 ▸ Subgroup.mem_zpowers _)
  have huu : u * u = 1 := h.zGroup_mul_self u hu
  let T : Subgroup G :=
    { carrier := {y | y ∈ pCore 2 G ∧ ∃ σ ∈ dewTauGroup Ω u v, ∀ M : ↥(dew1V Ω u),
        ((σ M : ↥(dew1V Ω u)) : Subgroup G) = conjSub y (M : Subgroup G)}
      one_mem' := ⟨(pCore 2 G).one_mem, 1, one_mem _, fun M => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, σ, hσ, hσa⟩ ⟨hb, τ, hτ, hτb⟩
        refine ⟨(pCore 2 G).mul_mem ha hb, σ * τ, mul_mem hσ hτ, fun M => ?_⟩
        rw [Equiv.Perm.mul_apply, hσa, hτb, conjSub_mul]
      inv_mem' := by
        rintro a ⟨ha, σ, hσ, hσa⟩
        refine ⟨(pCore 2 G).inv_mem ha, σ⁻¹, inv_mem hσ, fun M => ?_⟩
        have h1 : conjSub a ((σ⁻¹ M : ↥(dew1V Ω u)) : Subgroup G) = (M : Subgroup G) := by
          rw [← hσa]
          simp
        rw [← h1, conjSub_inv_conjSub] }
  have hdew : dewQstar Ω ≤ T := by
    unfold dewQstar
    refine iSup₂_le fun K hK => iSup₂_le fun J hJ => ?_
    intro x hx
    obtain ⟨hxKJ, hxQ⟩ := Subgroup.mem_inf.mp hx
    by_cases hJK : J = K
    · rw [hJK, sup_idem] at hxKJ
      obtain ⟨w, hw⟩ := h.exists_isUniqueInvolution hK
      have hxz : x ∈ zGroup Ω := by
        have hxK : x ∈ K ⊓ pCore 2 G := Subgroup.mem_inf.mpr ⟨hxKJ, hxQ⟩
        rw [h.inf_pCore hK hw] at hxK
        exact (Subgroup.zpowers_le.mpr (dew1_involution_mem h.toDEHyp hK hw)) hxK
      refine ⟨hxQ, 1, one_mem _, fun M => ?_⟩
      simp only [Equiv.Perm.one_apply]
      exact (mem_normalizer_iff_conjSub_eq.mp (h.dNorm _ M.2.1 hxz)).symm
    · obtain ⟨hJΩ, z, hz, hzJ⟩ := hJ
      have tw : DewTwins Ω K J z := ⟨hK, hJΩ, hz, hzJ, fun h1 => hJK h1.symm⟩
      obtain ⟨k, hk, j, hj, hxkj, hxQ'⟩ := (h.mem_dewDelta_iff tw).mp hx
      have hkjQ : k * j⁻¹ ∈ pCore 2 G := by
        rw [← hxkj]
        exact hxQ'
      by_cases hzu : z = u
      · have hKu : IsUniqueInvolution K u := by
          rw [← hzu]
          exact hz
        have hJu : IsUniqueInvolution J u := by
          rw [← hzu]
          exact hzJ
        refine ⟨hxQ, 1, one_mem _, fun M => ?_⟩
        simp only [Equiv.Perm.one_apply]
        have hxN : x ∈ Subgroup.normalizer (M : Set G) := by
          rw [hxkj]
          exact mul_mem (h.le_normalizer_of_dew1V hK hKu M.2 hk)
            (inv_mem (h.le_normalizer_of_dew1V hJΩ hJu M.2 hj))
        exact (mem_normalizer_iff_conjSub_eq.mp hxN).symm
      · have hzD : z ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hz
        have hzu' : z ∉ Subgroup.zpowers u := dewc_not_mem_zpowers huu hu1 hz.ne_one hzu
        by_cases hkc : k * u = u * k
        · refine ⟨hxQ, 1, one_mem _, fun M => ?_⟩
          simp only [Equiv.Perm.one_apply]
          rw [hxkj]
          exact (h.dewDelta_act_of_commute tw hk hj hkjQ hu hkc M.2).symm
        · obtain ⟨K', hK', J', hJ', hτ'⟩ :=
            h.exists_dewTau_eq hu hu1 hzD hv hzu' hvu ⟨hK, hz⟩ ⟨hJΩ, hzJ⟩
          let f : ↥(dew1V Ω u) → ↥(dew1V Ω u) := fun N =>
            ⟨dewTau K' J' (N : Subgroup G), h.dewTau_mem hK' hJ' huv N.2⟩
          have hf : Function.Involutive f := fun N =>
            Subtype.ext (h.dewTau_dewTau hK' hJ' huv N.2)
          have hσ : Function.Involutive.toPerm f hf ∈ dewTauGroup Ω u v :=
            Subgroup.subset_closure ⟨K', hK', J', hJ', fun N => rfl⟩
          refine ⟨hxQ, Function.Involutive.toPerm f hf, hσ, fun N => ?_⟩
          have hc : conjSub x (N : Subgroup G) = dewTau K J (N : Subgroup G) := by
            rw [hxkj]
            exact h.dewDelta_act_of_not_commute tw hk hj hkjQ hu hkc N.2
          calc ((Function.Involutive.toPerm f hf N : ↥(dew1V Ω u)) : Subgroup G)
              = dewTau K' J' (N : Subgroup G) := rfl
            _ = dewTau K J (N : Subgroup G) := hτ' N.1 N.2
            _ = conjSub x (N : Subgroup G) := hc.symm
  have hpc : pCore 2 G ≤ T := by
    rw [← h.dewQstar_eq_pCore]
    exact hdew
  obtain ⟨-, σ, hσ, hσq⟩ := hpc hq
  exact ⟨σ, hσ, hσq⟩

theorem pCore_act_comm {u : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) {q q' : G}
    (hq : q ∈ pCore 2 G) (hq' : q' ∈ pCore 2 G) {M : Subgroup G} (hM : M ∈ dew1V Ω u) :
    conjSub q (conjSub q' M) = conjSub q' (conjSub q M) := by
  obtain ⟨v, hvD, hvu⟩ := h.dewc_exists_notin_zpowers hu hu1 (h.zGroup_mul_self u hu)
  have hvu' : u ≠ v := fun h1 => hvu (h1 ▸ Subgroup.mem_zpowers _)
  obtain ⟨σ, hσ, hσq⟩ := h.exists_mem_dewTauGroup hu hu1 hvD hvu hq
  obtain ⟨σ', hσ', hσq'⟩ := h.exists_mem_dewTauGroup hu hu1 hvD hvu hq'
  have hcomm := h.dewTauGroup_comm hu hu1 hvu' hσ hσ'
  have hqC : ∀ x ∈ pCore 2 G, x ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
    fun x hx => h.pCore_le_centralizer_zGroup hx
  have hMq' : conjSub q' M ∈ dew1V Ω u := dew1_conj_mem h.toDEHyp (hqC q' hq') hM
  have hMq : conjSub q M ∈ dew1V Ω u := dew1_conj_mem h.toDEHyp (hqC q hq) hM
  have hs' : σ' ⟨M, hM⟩ = ⟨conjSub q' M, hMq'⟩ := Subtype.ext (hσq' ⟨M, hM⟩)
  have hs : σ ⟨M, hM⟩ = ⟨conjSub q M, hMq⟩ := Subtype.ext (hσq ⟨M, hM⟩)
  have e1 : conjSub q (conjSub q' M) = ((σ * σ') ⟨M, hM⟩ : ↥(dew1V Ω u)) := by
    rw [Equiv.Perm.mul_apply, hs']
    exact (hσq ⟨conjSub q' M, hMq'⟩).symm
  have e2 : conjSub q' (conjSub q M) = ((σ' * σ) ⟨M, hM⟩ : ↥(dew1V Ω u)) := by
    rw [Equiv.Perm.mul_apply, hs]
    exact (hσq' ⟨conjSub q M, hMq⟩).symm
  rw [e1, e2, hcomm]

theorem pCore_act_sq {u : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) {q : G} (hq : q ∈ pCore 2 G)
    {M : Subgroup G} (hM : M ∈ dew1V Ω u) : conjSub q (conjSub q M) = M := by
  obtain ⟨v, hvD, hvu⟩ := h.dewc_exists_notin_zpowers hu hu1 (h.zGroup_mul_self u hu)
  have hvu' : u ≠ v := fun h1 => hvu (h1 ▸ Subgroup.mem_zpowers _)
  obtain ⟨σ, hσ, hσq⟩ := h.exists_mem_dewTauGroup hu hu1 hvD hvu hq
  have hσσ := h.dewTauGroup_mul_self hu hu1 hvu' hσ
  have hs : σ (σ ⟨M, hM⟩) = ⟨M, hM⟩ := by
    have := congrArg (fun π : Equiv.Perm ↥(dew1V Ω u) => π ⟨M, hM⟩) hσσ
    simpa [Equiv.Perm.mul_apply] using this
  have e1 := hσq ⟨M, hM⟩
  have e2 := hσq (σ ⟨M, hM⟩)
  rw [hs, e1] at e2
  exact e2.symm

theorem pCore_act_regular {u : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) {q : G}
    (hq : q ∈ pCore 2 G) {M : Subgroup G} (hM : M ∈ dew1V Ω u) (hqM : conjSub q M = M) :
    ∀ M' ∈ dew1V Ω u, conjSub q M' = M' := by
  intro M' hM'
  have hMM' : M' ∈ twinSet Ω M := by
    rw [← dew1V_eq_twinSet hM.1 hM.2]
    exact hM'
  obtain ⟨q', hq', hqM'⟩ := h.exists_pCore_conj_of_mem_twinSet hM.1 hMM'
  have hcomm := h.pCore_act_comm hu hu1 hq hq' hM
  rw [← hqM', hcomm, hqM]

theorem centralizer_act_eq {u : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) {g : G}
    (hg : g ∈ Subgroup.centralizer ({u} : Set G)) :
    ∃ q ∈ pCore 2 G, ∀ M ∈ dew1V Ω u, conjSub g M = conjSub q M := by
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  rw [h.centralizer_eq_dewKer_sup hu hu1] at hg
  obtain ⟨w, hw, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  refine ⟨q, hq, fun M hM => ?_⟩
  rw [conjSub_mul]
  exact (h.mem_dewKer_iff.mp hw).2 _ (dew1_conj_mem h.toDEHyp (h.pCore_le_centralizer_zGroup hq) hM)

theorem normalizer_fixes_twins {u : G} {K : Subgroup G} (hK : K ∈ dew1V Ω u) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : ∀ J ∈ dew1V Ω u, conjSub g J = J := by
  intro J hJ
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK.1 hK.2
  have hu1 : u ≠ 1 := hK.2.ne_one
  have hgu : g * u * g⁻¹ = u := hK.2.conj_eq (mem_normalizer_iff_conjSub_eq.mp hg)
  have hgC : g ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * u = (g * u * g⁻¹) * g := by group
      _ = u * g := by rw [hgu]
  obtain ⟨q, hq, hqM⟩ := h.centralizer_act_eq huD hu1 hgC
  have hqK : conjSub q K = K := by
    rw [← hqM K hK]
    exact mem_normalizer_iff_conjSub_eq.mp hg
  have hreg := h.pCore_act_regular huD hu1 hq hK hqK
  rw [hqM J hJ]
  exact hreg J hJ

end DE4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
