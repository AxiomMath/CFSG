module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSwapRank
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalTwoGroup

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem swapped_correspondence_large_kernel_centralizer_replacement {a b : G} {J L : Subgroup G}
    (h : UnbalancedGS.GSCorr a J b L) (hne : conjugate L a ≠ L)
    (hd : (pPrimeCore 2 J).index = (pPrimeCore 2 L).index) {S P Q T : Subgroup G}
    (hSH : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)))
    (hbS : b ∈ S)
    (hP : P = S ⊓ (centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J))
    (hQ : Q = S ⊓ centralizer ({b} : Set G)) (hT : T = P ⊓ centralizer ({b} : Set G))
    (hTP : T < P) (hT8 : 8 ≤ Nat.card T) :
    (P.subgroupOf S).Normal ∧ T = P ⊓ Q ∧
    ∃ R : Subgroup G,
      (R : Set G) = {u | u ∈ T ∧ ∀ k ∈ L ⊔ conjugate L a, k⁻¹ * u⁻¹ * k * u ∈
        (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype} ∧
      R ≤ Q ∧ (R.subgroupOf Q).Normal ∧
      zpowers a ⊓ R = ⊥ ∧ zpowers a ⊔ R = T ∧ (∀ x ∈ zpowers a, ∀ y ∈ R, x * y = y * x) ∧
      ∃ w ∈ P, w ∈ normalizer (Q : Set G) ∧ w ∉ Q ∧ w ^ 2 ∈ T ∧
        ∃ e : G, orderOf e = 2 ∧ e ∈ R ⊓ conjugate R w ∧
          Q ⊔ zpowers w ≤ S ⊓ centralizer ({e} : Set G) ∧
          Q < S ⊓ centralizer ({e} : Set G) ∧ e ∈ P ∧ e ∈ normalizer (J : Set G) ∧
          (∀ j ∈ J, j⁻¹ * e⁻¹ * j * e ∈ (pPrimeCore 2 J).map J.subtype) ∧
          (∀ k ∈ L ⊔ conjugate L a, k⁻¹ * e⁻¹ * k * e ∈
            (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype) ∧
          e * a = a * e ∧ e * b = b * e ∧ ∀ y ∈ Q, e * y = y * e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hP hQ hT
  have hnc := (correspondence_normal_closure h rfl rfl rfl).2.2.2
  have hcorr := h
  obtain ⟨hao, hbo, hab, hJa, hJ, hLb, hL, hbN, hcomm, -⟩ := hcorr
  set HJ := centralizer ({a} : Set G) ⊓ normalizer (J : Set G) with hHJdef
  set QJ := HJ ⊓ coreActionKernel J with hQJdef
  set Cb := centralizer ({b} : Set G) with hCbdef
  set N := (pPrimeCore 2 Cb).map Cb.subtype with hNdef
  set P := S ⊓ QJ with hPdef
  set Q := S ⊓ Cb with hQdef
  set T := P ⊓ Cb with hTdef
  have haa : a * a = 1 := by rw [← pow_two, ← hao, pow_orderOf_eq_one]
  obtain ⟨P₀, hP₀⟩ := hSsyl
  have hS2 : IsPGroup 2 S := by
    have h1 : IsPGroup 2 ((P₀ : Subgroup HJ).map HJ.subtype) := P₀.isPGroup'.map HJ.subtype
    rwa [hP₀, map_subgroupOf_eq_of_le hSH] at h1
  have hQJN : HJ ≤ normalizer (QJ : Set G) := fun g hg =>
    normalizer_inf_mem (le_normalizer hg)
      (normalizer_le_normalizer_coreActionKernel J (mem_inf.mp hg).2)
  have hPS : P ≤ S := inf_le_left
  have hPn : (P.subgroupOf S).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hPS]
    exact fun s hs => normalizer_inf_mem (le_normalizer hs) (hQJN (hSH hs))
  have haJ : a ∈ normalizer (J : Set G) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_le_centralizer hJa)
  have haHJ : a ∈ HJ := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, haJ⟩
  have haS : a ∈ S := by
    have hza : zpowers a ≤ HJ := zpowers_le.mpr haHJ
    have hn : ((zpowers a).subgroupOf HJ).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
      have hga : (g : G) * a = a * g := mem_centralizer_singleton_iff.mp (mem_inf.mp g.2).1
      have h1 : (g : G) * (n : G) * (g : G)⁻¹ = n := by
        rw [← hk, (Commute.zpow_right hga k).eq, mul_inv_cancel_right]
      simpa [h1] using hn⟩
    have h2 : IsPGroup 2 ((zpowers a).subgroupOf HJ) :=
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])).comap_subtype
    have h3 := h2.le_sylow_of_normal P₀
    have h4 : (⟨a, haHJ⟩ : HJ) ∈ (P₀ : Subgroup HJ) :=
      h3 (show (⟨a, haHJ⟩ : HJ) ∈ (zpowers a).subgroupOf HJ from mem_zpowers a)
    rw [hP₀] at h4
    exact h4
  have haQJ : a ∈ coreActionKernel J := by
    refine mem_coreActionKernel.mpr ⟨haJ, fun j hj => ?_⟩
    have hja : j * a = a * j := mem_centralizer_singleton_iff.mp (hJa hj)
    rw [show j⁻¹ * a⁻¹ * j * a = j⁻¹ * (a⁻¹ * (j * a)) by group, hja, inv_mul_cancel_left,
      inv_mul_cancel]
    exact one_mem _
  have haCb : a ∈ Cb := mem_centralizer_singleton_iff.mpr hab
  have haT : a ∈ T := mem_inf.mpr ⟨mem_inf.mpr ⟨haS, mem_inf.mpr ⟨haHJ, haQJ⟩⟩, haCb⟩
  have hT2 : IsPGroup 2 T := hS2.to_le (inf_le_left.trans hPS)
  have hTle : T ≤ centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) ⊓ normalizer (J : Set G) :=
    fun u hu => by
      obtain ⟨hP', hCb'⟩ := mem_inf.mp hu
      have hHJ' := (mem_inf.mp (mem_inf.mp hP').2).1
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hHJ').1, hCb'⟩, (mem_inf.mp hHJ').2⟩
  have hJT : ∀ u ∈ T, ∀ j ∈ J, j⁻¹ * u⁻¹ * j * u ∈ (pPrimeCore 2 J).map J.subtype := fun u hu =>
    (mem_coreActionKernel.mp (mem_inf.mp (mem_inf.mp (mem_inf.mp hu).1).2).2).2
  obtain ⟨R, hRset, hzbot, hzsup, hzcomm, hidx, -⟩ :=
    swapped_correspondence_centralizer_rank_bound h hne hd hT2 hTle haT hJT
  have hRT : R ≤ T := fun u hu => by
    have h1 : u ∈ (R : Set G) := hu
    rw [hRset] at h1
    exact h1.1
  have hTQ : T ≤ Q := fun u hu => mem_inf.mpr ⟨hPS (mem_inf.mp hu).1, (mem_inf.mp hu).2⟩
  have hTPQ : T = P ⊓ Q := by
    apply le_antisymm (le_inf inf_le_left hTQ)
    exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  have hQconj : ∀ q ∈ Q, ∀ u ∈ R, q * u * q⁻¹ ∈ R := by
    intro q hq u hu
    obtain ⟨hqS, hqb⟩ := mem_inf.mp hq
    have hqJ : q ∈ normalizer (J : Set G) := (mem_inf.mp (hSH hqS)).2
    have hqK := (hnc q (mem_inf.mpr ⟨hqb, hqJ⟩)).1
    have hqP : q * u * q⁻¹ ∈ P :=
      (mem_normalizer_iff.mp (normalizer_inf_mem (le_normalizer hqS) (hQJN (hSH hqS))) u).mp
        (mem_inf.mp (hRT hu)).1
    have hqT : q * u * q⁻¹ ∈ T := mem_inf.mpr ⟨hqP, mul_mem (mul_mem hqb (hRT hu |>
      fun h1 => (mem_inf.mp h1).2)) (inv_mem hqb)⟩
    have hmem : q * u * q⁻¹ ∈ (R : Set G) := by
      rw [hRset]
      refine ⟨hqT, fun k hk => ?_⟩
      have hu' : u ∈ (R : Set G) := hu
      rw [hRset] at hu'
      have hk' : q⁻¹ * k * q ∈ L ⊔ conjugate L a := by
        have h1 := (mem_normalizer_iff.mp (inv_mem hqK) k).mp hk
        rwa [inv_inv] at h1
      have h1 := hu'.2 _ hk'
      have hqN : q ∈ normalizer (N : Set G) :=
        UnbalancedGS.normalizer_le_normalizer_map_of_characteristic Cb (pPrimeCore 2 Cb)
          (le_normalizer hqb)
      have h2 := (mem_normalizer_iff.mp hqN _).mp h1
      rwa [show q * ((q⁻¹ * k * q)⁻¹ * u⁻¹ * (q⁻¹ * k * q) * u) * q⁻¹ =
        k⁻¹ * (q * u * q⁻¹)⁻¹ * k * (q * u * q⁻¹) by group] at h2
    exact hmem
  have hRQ : R ≤ Q := hRT.trans hTQ
  have hRQn : (R.subgroupOf Q).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact hQconj g g.2 n hn
  have hQS : Q ≤ S := inf_le_left
  have hTS : T ≤ S := hTQ.trans hQS
  have hPQ' : ¬ P.subgroupOf S ≤ Q.subgroupOf S := by
    intro hle
    apply (lt_iff_le_not_ge.mp hTP).2
    intro x hx
    have h1 : (⟨x, hPS hx⟩ : S) ∈ Q.subgroupOf S := hle hx
    rw [hTPQ]
    exact mem_inf.mpr ⟨hx, h1⟩
  have hRn' : ((R.subgroupOf S).subgroupOf (Q.subgroupOf S)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf] at hn ⊢
    have hg : ((g : S) : G) ∈ Q := g.2
    simpa using hQconj _ hg _ hn
  have hRT' : R.subgroupOf S ≤ P.subgroupOf S ⊓ Q.subgroupOf S := by
    intro x hx
    have h1 := hRT hx
    rw [hTPQ] at h1
    exact mem_inf.mpr ⟨(mem_inf.mp h1).1, (mem_inf.mp h1).2⟩
  have hPQS : P.subgroupOf S ⊓ Q.subgroupOf S = T.subgroupOf S := by
    rw [hTPQ]
    ext x
    simp only [mem_inf, mem_subgroupOf]
  have hidx' : (R.subgroupOf S).relIndex (P.subgroupOf S ⊓ Q.subgroupOf S) = 2 := by
    rw [hPQS, relIndex_subgroupOf hTS]
    exact hidx
  have hT8' : 8 ≤ Nat.card ↥(P.subgroupOf S ⊓ Q.subgroupOf S) := by
    rw [hPQS, Nat.card_congr (subgroupOfEquivOfLe hTS).toEquiv]
    exact hT8
  have hS2' : IsPGroup 2 ↥S := hS2
  obtain ⟨w, hwP, hwN, hwQ, hw2, z, hz2, hzR, hQz, hQlt⟩ :=
    SmallLocal.two_group_centralizer_enlargement hS2' hPQ' hRn' hRT' hidx' hT8'
  have hzR' : (z : G) ∈ R := (mem_inf.mp hzR).1
  have hzRw : (z : G) ∈ conjugate R (w : G) := by
    have h1 := (mem_inf.mp hzR).2
    rw [mem_conjugate_iff] at h1 ⊢
    exact h1
  have hzT := hRT hzR'
  have hzP : (z : G) ∈ P := (mem_inf.mp hzT).1
  have hzQJ := (mem_inf.mp hzP).2
  have hQe : Q ≤ S ⊓ centralizer ({(z : G)} : Set G) := by
    intro y hy
    have h1 := hQz (mem_sup_left (show (⟨y, hQS hy⟩ : S) ∈ Q.subgroupOf S from hy))
    rw [mem_centralizer_singleton_iff] at h1
    exact mem_inf.mpr ⟨hQS hy, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h1)⟩
  have hwe : (w : G) ∈ S ⊓ centralizer ({(z : G)} : Set G) := by
    have h1 := hQz (mem_sup_right (mem_zpowers w))
    rw [mem_centralizer_singleton_iff] at h1
    exact mem_inf.mpr ⟨w.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h1)⟩
  have hQlt' : Q < S ⊓ centralizer ({(z : G)} : Set G) := by
    refine lt_of_le_of_ne hQe fun heq => ?_
    obtain ⟨x, hx, hxQ⟩ := IsConcreteLE.exists_of_lt hQlt
    apply hxQ
    have h1 : (x : G) ∈ S ⊓ centralizer ({(z : G)} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hx
      exact mem_inf.mpr ⟨x.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hx)⟩
    rw [← heq] at h1
    exact h1
  have hzK : ∀ k ∈ L ⊔ conjugate L a, k⁻¹ * (z : G)⁻¹ * k * z ∈ N := by
    have h1 : (z : G) ∈ (R : Set G) := hzR'
    rw [hRset] at h1
    exact h1.2
  have hze : ∀ y ∈ Q, (z : G) * y = y * z := fun y hy =>
    (mem_centralizer_singleton_iff.mp (mem_inf.mp (hQe hy)).2).symm
  refine ⟨hPn, hTPQ, R, hRset, hRQ, hRQn, hzbot, hzsup, hzcomm, (w : G), hwP,
    mem_normalizer_of_subgroupOf hQS hwN, hwQ, ?_, (z : G), ?_, mem_inf.mpr ⟨hzR', hzRw⟩,
    sup_le hQe (zpowers_le.mpr hwe), hQlt', hzP, (mem_inf.mp (mem_inf.mp hzQJ).1).2,
    (mem_coreActionKernel.mp (mem_inf.mp hzQJ).2).2, hzK, hze a (hTQ haT),
    hze b (mem_inf.mpr ⟨hbS, mem_centralizer_singleton_iff.mpr rfl⟩), hze⟩
  · have h1 : ((w ^ 2 : S) : G) ∈ P ⊓ Q := hw2
    rw [← hTPQ] at h1
    simpa using h1
  · rw [Subgroup.orderOf_coe, hz2]

end CFSG.ComponentClassification.UnbalancedCorr
