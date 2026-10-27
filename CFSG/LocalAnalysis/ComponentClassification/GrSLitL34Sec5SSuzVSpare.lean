module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWConfig
public import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
public import CFSG.GroupTheory.ConjTransport
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open scoped commutatorElement

theorem map_conj_one_eq_self {X : Type*} [Group X] (K : Subgroup X) :
    K.map (MulAut.conj (1 : X)).toMonoidHom = K := by
  ext x
  simp [Subgroup.mem_map]

theorem exists_involution_mem_of_normal_two_pgroup
    {H : Type*} [Group H] [Finite H] {P N : Subgroup H} (hP : IsPGroup 2 P)
    (hNP : N ≤ P) (hNn : P ≤ Subgroup.normalizer (N : Set H)) (hNne : N ≠ ⊥) :
    ∃ z ∈ N, orderOf z = 2 ∧ ∀ x ∈ P, z * x = x * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPn : (N.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNn
  have hN'ne : N.subgroupOf P ≠ ⊥ := by
    intro h
    apply hNne
    rw [← Subgroup.map_subgroupOf_eq_of_le hNP, h, Subgroup.map_bot]
  have hLne : N.subgroupOf P ⊓ Subgroup.center ↥P ≠ ⊥ :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot hP
      (N.subgroupOf P) hN'ne
  set L : Subgroup ↥P := N.subgroupOf P ⊓ Subgroup.center ↥P with hL
  have hLP : IsPGroup 2 L := hP.to_subgroup L
  have hLnt : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hLne
  obtain ⟨n, hnpos, hncard⟩ := (hLP.nontrivial_iff_card).mp hLnt
  have h2dvd : 2 ∣ Nat.card ↥L := by
    rw [hncard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hnpos)
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 h2dvd
  refine ⟨((((x : ↥L).val : ↥P)) : H), ?_, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp x.2).1
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hxord]
  · intro y hy
    have hxcent : ((x : ↥L).val : ↥P) ∈ Subgroup.center ↥P := (Subgroup.mem_inf.mp x.2).2
    have := (Subgroup.mem_center_iff.mp hxcent) ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm


theorem exists_involution_centralizing_pair_suz
    {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G}
    (hc : L34WConfigAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t P W)
    (_hM : M = normalizer (W : Set G)) (htM : t ∈ M)
    {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} (hL : IsComponent L)
    (hZ : Nat.card (Subgroup.center ↥L) ≤ 2)
    (hLty : IsSporadic (↥L ⧸ Subgroup.center ↥L) .Suz)
    (hne : L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom ≠ L)
    (hthird : ∃ x : ↥M ⧸ pPrimeCore 2 ↥M, L.map (MulAut.conj x).toMonoidHom ≠ L ∧
      L.map (MulAut.conj x).toMonoidHom ≠
        L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom) :
    ∃ (v : G) (hvM : v ∈ M), orderOf v = 2 ∧ t * v = v * t ∧
      ∀ y ∈ L ⊔ L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom,
        QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨v, hvM⟩ * y =
          y * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨v, hvM⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxL, hxLt⟩ := hthird
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hc.order_two, pow_two] at h
    exact h
  have hs2 : (⟨t, htM⟩ : ↥M) * ⟨t, htM⟩ = 1 := Subtype.ext ht2
  let tbar : ↥M ⧸ pPrimeCore 2 ↥M := QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩
  have htbar2 : tbar * tbar = 1 := by
    rw [show tbar * tbar =
      QuotientGroup.mk' (pPrimeCore 2 ↥M) (⟨t, htM⟩ * ⟨t, htM⟩) from (map_mul _ _ _).symm,
      hs2, map_one]
  have htbar_ne : tbar ≠ 1 := by
    intro h
    apply hne
    rw [show L.map (MulAut.conj tbar).toMonoidHom =
      L.map (MulAut.conj (1 : ↥M ⧸ pPrimeCore 2 ↥M)).toMonoidHom from by rw [h]]
    exact map_conj_one_eq_self L
  have htbord : orderOf tbar = 2 := by
    have hdvd : orderOf tbar ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact htbar2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) htbar_ne
    · exact h
  let L' : Subgroup (↥M ⧸ pPrimeCore 2 ↥M) := L.map (MulAut.conj x).toMonoidHom
  let L'' : Subgroup (↥M ⧸ pPrimeCore 2 ↥M) := L'.map (MulAut.conj tbar).toMonoidHom
  have hL' : IsComponent L' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hL
  have hL'' : IsComponent L'' :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj tbar) hL'
  have hL'_ne_L : L' ≠ L := hxL
  have hL'_ne_Lt : L' ≠ L.map (MulAut.conj tbar).toMonoidHom := hxLt
  have hL''_map : L''.map (MulAut.conj tbar).toMonoidHom = L' := by
    show (L'.map (MulAut.conj tbar).toMonoidHom).map (MulAut.conj tbar).toMonoidHom = L'
    rw [CFSG.GroupTheory.map_conj_map_conj, htbar2]
    exact map_conj_one_eq_self L'
  have hL_twice : (L.map (MulAut.conj tbar).toMonoidHom).map
      (MulAut.conj tbar).toMonoidHom = L := by
    rw [CFSG.GroupTheory.map_conj_map_conj, htbar2]
    exact map_conj_one_eq_self L
  have hL''_ne_L : L'' ≠ L := by
    intro h
    apply hL'_ne_Lt
    have h1 := congrArg (fun K => K.map (MulAut.conj tbar).toMonoidHom) h
    rw [hL''_map] at h1
    exact h1
  have hL''_ne_Lt : L'' ≠ L.map (MulAut.conj tbar).toMonoidHom := by
    intro h
    apply hL'_ne_L
    have h1 : L''.map (MulAut.conj tbar).toMonoidHom =
        (L.map (MulAut.conj tbar).toMonoidHom).map (MulAut.conj tbar).toMonoidHom :=
      congrArg (fun K => K.map (MulAut.conj tbar).toMonoidHom) h
    rwa [hL''_map, hL_twice] at h1
  have hLt_comp : IsComponent (L.map (MulAut.conj tbar).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj tbar) hL
  have hcommL'L : ⁅L', L⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hL' hL with h | h
    · exact absurd h hL'_ne_L
    · exact h
  have hcommL'Lt : ⁅L', L.map (MulAut.conj tbar).toMonoidHom⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hL' hLt_comp with h | h
    · exact absurd h hL'_ne_Lt
    · exact h
  have hcommL''L : ⁅L'', L⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hL'' hL with h | h
    · exact absurd h hL''_ne_L
    · exact h
  have hcommL''Lt : ⁅L'', L.map (MulAut.conj tbar).toMonoidHom⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hL'' hLt_comp with h | h
    · exact absurd h hL''_ne_Lt
    · exact h
  let D : Subgroup (↥M ⧸ pPrimeCore 2 ↥M) := L' ⊔ L''
  have hD_cent : D ≤ Subgroup.centralizer
      ((L ⊔ L.map (MulAut.conj tbar).toMonoidHom : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) :
        Set (↥M ⧸ pPrimeCore 2 ↥M)) := by
    refine CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers ?_ ?_
    · exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommL'L)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommL''L)
    · exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommL'Lt)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommL''Lt)
  have hD_conj : D.map (MulAut.conj tbar).toMonoidHom = D := by
    show (L' ⊔ L'').map (MulAut.conj tbar).toMonoidHom = L' ⊔ L''
    rw [Subgroup.map_sup]
    rw [show L'.map (MulAut.conj tbar).toMonoidHom = L'' from rfl, hL''_map, sup_comm]
  have htbarN : tbar ∈ Subgroup.normalizer (D : Set (↥M ⧸ pPrimeCore 2 ↥M)) := by
    refine CFSG.GroupTheory.mem_normalizer_of_conj_mem fun y hy => ?_
    have h1 : MulAut.conj tbar y ∈ D.map (MulAut.conj tbar).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hy
    rwa [hD_conj] at h1
  have hL_even : 2 ∣ Nat.card ↥L := by
    letI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
    exact (even_iff_two_dvd.mp (CFSG.GH74.even_card_of_nonabelian_simple hL.1.2.2)).trans
      (Subgroup.card_quotient_dvd_card (Subgroup.center ↥L))
  have hL'card : Nat.card ↥L' = Nat.card ↥L := by
    show Nat.card ↥(L.map (MulAut.conj x).toMonoidHom) = Nat.card ↥L
    exact Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hD_even : 2 ∣ Nat.card ↥D := by
    have hdvd : Nat.card ↥L' ∣ Nat.card ↥D := Subgroup.card_dvd_of_le le_sup_left
    rw [hL'card] at hdvd
    exact hL_even.trans hdvd
  let H : Subgroup (↥M ⧸ pPrimeCore 2 ↥M) := D ⊔ Subgroup.zpowers tbar
  have hDH : D ≤ H := le_sup_left
  have htbarH : tbar ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers tbar)
  let tb : H := ⟨tbar, htbarH⟩
  have htword : orderOf tb = 2 := by
    rw [show tb = ⟨tbar, htbarH⟩ from rfl]
    exact (orderOf_injective (Subgroup.subtype H) (Subgroup.subtype_injective H)
      ⟨tbar, htbarH⟩).symm.trans htbord
  have hpgroup : IsPGroup 2 (Subgroup.zpowers tb) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, htword]
    norm_num
  obtain ⟨Q, hQle⟩ := hpgroup.exists_le_sylow
  have hDHnorm : (D.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDH]
    refine sup_le Subgroup.le_normalizer ?_
    rw [Subgroup.zpowers_le]
    exact htbarN
  have hDH_even : 2 ∣ Nat.card ↥(D.subgroupOf H) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv]
  have hDN : (Q : Subgroup H) ≤ Subgroup.normalizer (D.subgroupOf H : Set H) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hDHnorm]
    exact le_top
  have hOddIdx : ¬ 2 ∣ ((D.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf
      (D.subgroupOf H)).index := by
    have hrel : (D.subgroupOf H ⊓ (Q : Subgroup H)).relIndex (D.subgroupOf H) =
        ((D.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf (D.subgroupOf H)).index := rfl
    rw [← hrel]
    have hsecond :=
      (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hDN).1
    rw [inf_comm] at hsecond
    rw [← hsecond]
    have hoddQ : ¬ 2 ∣ (Q : Subgroup H).relIndex (⊤ : Subgroup H) := by
      rw [Subgroup.relIndex_top_right]
      exact Q.not_dvd_index' Subgroup.index_ne_zero_of_finite
    have hdiv : (Q : Subgroup H).relIndex ((Q : Subgroup H) ⊔ D.subgroupOf H) ∣
        (Q : Subgroup H).relIndex (⊤ : Subgroup H) := by
      rw [← Subgroup.relIndex_mul_relIndex (H := (Q : Subgroup H))
        (K := (Q : Subgroup H) ⊔ D.subgroupOf H) (L := ⊤) le_sup_left le_top]
      exact dvd_mul_right _ _
    exact fun h => hoddQ (h.trans hdiv)
  have hInf_even : 2 ∣ Nat.card ↥(D.subgroupOf H ⊓ (Q : Subgroup H)) := by
    have hcard : Nat.card ↥(D.subgroupOf H) =
        Nat.card ↥((D.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf (D.subgroupOf H)) *
          ((D.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf (D.subgroupOf H)).index :=
      (Subgroup.card_mul_index _).symm
    rw [hcard] at hDH_even
    rcases Nat.Prime.dvd_mul Nat.prime_two |>.mp hDH_even with h | h
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
    · exact absurd h hOddIdx
  have hNne : D.subgroupOf H ⊓ (Q : Subgroup H) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hInf_even
    exact absurd hInf_even (by simp)
  have hsubeq : (D.subgroupOf H).subgroupOf (Q : Subgroup H) =
      (D.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf (Q : Subgroup H) := by
    ext y
    simp [Subgroup.mem_subgroupOf]
  have hNn : (Q : Subgroup H) ≤
      Subgroup.normalizer (D.subgroupOf H ⊓ (Q : Subgroup H) : Set H) := by
    have hAn : ((D.subgroupOf H ⊓ (Q : Subgroup H)).subgroupOf (Q : Subgroup H)).Normal := by
      rw [← hsubeq]
      exact hDHnorm.subgroupOf (Q : Subgroup H)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mp hAn
  obtain ⟨z, hzN, hzord, hzcomm⟩ := exists_involution_mem_of_normal_two_pgroup
    (P := (Q : Subgroup H)) (N := D.subgroupOf H ⊓ (Q : Subgroup H)) Q.isPGroup'
    inf_le_right hNn hNne
  have hzD : (z : ↥M ⧸ pPrimeCore 2 ↥M) ∈ D :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hzN).1
  have hzt : (z : ↥M ⧸ pPrimeCore 2 ↥M) * tbar =
      tbar * (z : ↥M ⧸ pPrimeCore 2 ↥M) := by
    have h := hzcomm tb (hQle (Subgroup.mem_zpowers tb))
    exact congrArg (fun u : H => (u : ↥M ⧸ pPrimeCore 2 ↥M)) h
  have hzordX : orderOf (z : ↥M ⧸ pPrimeCore 2 ↥M) = 2 := by
    rw [Subgroup.orderOf_coe, hzord]
  have hzw : (z : ↥M ⧸ pPrimeCore 2 ↥M) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (z : ↥M ⧸ pPrimeCore 2 ↥M)
    rwa [hzordX] at h
  have hzX_ne : (z : ↥M ⧸ pPrimeCore 2 ↥M) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzordX
    exact absurd hzordX (by norm_num)
  let s : ↥M := ⟨t, htM⟩
  let π : ↥M →* (↥M ⧸ pPrimeCore 2 ↥M) := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  have hE : IsPGroup 2 (Subgroup.zpowers s) := by
    apply IsPGroup.of_card (n := 1)
    have hsord : orderOf s = 2 := by
      show orderOf (⟨t, htM⟩ : ↥M) = 2
      rw [Subgroup.orderOf_mk, hc.order_two]
    rw [Nat.card_zpowers, hsord]
    norm_num
  have hker : ¬ 2 ∣ Nat.card (π.domRestrict (⊤ : Subgroup ↥M)).ker := by
    have hcard : Nat.card (π.domRestrict (⊤ : Subgroup ↥M)).ker =
        Nat.card (pPrimeCore 2 ↥M) := by
      have hk : (π.domRestrict (⊤ : Subgroup ↥M)).ker =
          (pPrimeCore 2 ↥M).subgroupOf (⊤ : Subgroup ↥M) := by
        rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
      rw [hk]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv
    rw [hcard, ← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card)
  have hmap := CFSG.ComponentClassification.GSThmB.OddQuot.map_inf_centralizer π hE
    (by rw [Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_top]; exact le_top) hker
  have hw_mem : (z : ↥M ⧸ pPrimeCore 2 ↥M) ∈
      (⊤ : Subgroup ↥M).map π ⊓ Subgroup.centralizer ((Subgroup.zpowers s).map π : Set _) := by
    refine ⟨?_, ?_⟩
    · rw [Subgroup.map_top,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M))]
      exact Subgroup.mem_top _
    · rw [MonoidHom.map_zpowers, CFSG.GroupTheory.centralizer_zpowers_eq]
      have hπs : π s = tbar := rfl
      rw [hπs]
      exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hzt.symm)
  rw [← hmap] at hw_mem
  obtain ⟨h, hh, hπh⟩ := Subgroup.mem_map.mp hw_mem
  have hhcent : h ∈ Subgroup.centralizer ({s} : Set ↥M) := by
    rw [← CFSG.GroupTheory.centralizer_zpowers_eq]
    exact (Subgroup.mem_inf.mp hh).2
  have hhc : h * s = s * h := Subgroup.mem_centralizer_singleton_iff.mp hhcent
  have hhG : (h : G) * t = t * (h : G) := by
    have h' := congrArg (fun y : ↥M => (y : G)) hhc
    simpa [s] using h'
  have hh2ker : h ^ 2 ∈ pPrimeCore 2 ↥M := by
    have h1 : π (h ^ 2) = 1 := by
      rw [map_pow, hπh, hzw]
    have h2 : h ^ 2 ∈ π.ker := MonoidHom.mem_ker.mpr h1
    have hker_eq : π.ker = pPrimeCore 2 ↥M := QuotientGroup.ker_mk' _
    rwa [hker_eq] at h2
  have hodd_h2 : Odd (orderOf (h ^ 2)) := by
    have hdvd : orderOf (h ^ 2) ∣ Nat.card (pPrimeCore 2 ↥M) :=
      Subgroup.orderOf_dvd_natCard _ hh2ker
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) hdvd
  have h2dvd_h : 2 ∣ orderOf h := by
    have h := orderOf_map_dvd π h
    rw [hπh, hzordX] at h
    exact h
  obtain ⟨k, hk⟩ := h2dvd_h
  have hk_dvd : k ∣ orderOf (h ^ 2) := by
    have hpow : h ^ (2 * orderOf (h ^ 2)) = 1 := by
      rw [pow_mul, pow_orderOf_eq_one]
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    rw [hk] at hdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp hdvd
  have hk_odd : Odd k := Odd.of_dvd_nat hodd_h2 hk_dvd
  have hwk : (z : ↥M ⧸ pPrimeCore 2 ↥M) ^ k = (z : ↥M ⧸ pPrimeCore 2 ↥M) := by
    obtain ⟨j, rfl⟩ := hk_odd
    rw [pow_succ, pow_mul, hzw, one_pow, one_mul]
  let vM : ↥M := h ^ k
  have hπv : π vM = (z : ↥M ⧸ pPrimeCore 2 ↥M) := by
    show π (h ^ k) = _
    rw [map_pow, hπh, hwk]
  have hvM2 : vM * vM = 1 := by
    show h ^ k * h ^ k = 1
    rw [← pow_add]
    have hsum : k + k = orderOf h := by omega
    rw [hsum, pow_orderOf_eq_one]
  have hvM_ne : vM ≠ 1 := by
    intro h1
    have h2 : π vM = 1 := by rw [h1, map_one]
    rw [hπv] at h2
    exact hzX_ne h2
  have hvM_ord : orderOf vM = 2 := by
    have hdvd : orderOf vM ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hvM2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hvM_ne
    · exact h
  have hv_ord : orderOf (vM : G) = 2 := by
    rw [Subgroup.orderOf_coe, hvM_ord]
  have hv_t : t * (vM : G) = (vM : G) * t := by
    have h1 : (h : G) ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hhG
    have h2 : (vM : G) ∈ Subgroup.centralizer ({t} : Set G) := by
      have h3 := Subgroup.pow_mem (Subgroup.centralizer ({t} : Set G)) h1 k
      simpa [vM] using h3
    exact Subgroup.mem_centralizer_iff.mp h2 t (by simp)
  have hv_cent : ∀ y ∈ L ⊔ L.map (MulAut.conj tbar).toMonoidHom,
      π vM * y = y * π vM := by
    intro y hy
    have h1 : π vM ∈ D := by
      rw [hπv]
      exact hzD
    exact (Subgroup.mem_centralizer_iff.mp (hD_cent h1) y hy).symm
  refine ⟨(vM : G), vM.2, hv_ord, hv_t, ?_⟩
  intro y hy
  exact hv_cent y hy

end CFSG.ComponentClassification.GrSLit.L34Sec5S
