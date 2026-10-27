module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionZStar
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneEmbedding

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open
open scoped commutatorElement

theorem not_dvd_card_of_isPerfect_of_sylow_le_center {K : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] {p : ℕ} [Fact p.Prime] (P : Sylow p K)
    (hP : (P : Subgroup K) ≤ Subgroup.center K) : ¬ p ∣ Nat.card K := by
  have hnc : Subgroup.normalizer ((P : Subgroup K) : Set K) ≤
      Subgroup.centralizer ((P : Subgroup K) : Set K) := fun g _ =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => (Subgroup.mem_center_iff.mp (hP hh) g).symm
  have hker : (MonoidHom.transferSylow P hnc).ker = ⊤ := by
    refine top_unique ?_
    rw [← (Group.IsPerfect.commutator_eq_top : commutator K = ⊤)]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hP (MonoidHom.transferSylow P hnc b).2) _)
  have h := MonoidHom.not_dvd_card_ker_transferSylow P hnc
  rwa [hker, Subgroup.card_top] at h

section ZStarStep

variable {X : Type} [Group X] [Finite X]

theorem orderOf_eq_two_of_mul_self {K : Type*} [Group K] {a : K} (ha : a * a = 1)
    (ha1 : a ≠ 1) : orderOf a = 2 :=
  orderOf_eq_prime (by rw [pow_two, ha]) ha1

omit [Finite X] in
theorem map_eq_one_of_isPGroup_of_mem_oddCore {Y : Type*} [Group Y] [Finite Y] {Q : Subgroup X}
    (hQ : IsPGroup 2 Q) (f : X →* Y) {q : X} (hq : q ∈ Q) (hf : f q ∈ CFSG.oddCore Y) :
    f q = 1 := by
  have hodd := CFSG.Adapters.odd_orderOf_of_mem_oddCore hf
  obtain ⟨n, hn⟩ := hQ ⟨q, hq⟩
  have hqn : q ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hdvd : orderOf (f q) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hqn, map_one])
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.mpr hodd).pow_right n) hdvd)

variable {J : Subgroup X} [hJn : J.Normal] {x : X} {Q : Subgroup X} {C : Subgroup X}

theorem exists_sylow_of_sup_eq_top (hx : orderOf x = 2) (htop : J ⊔ Subgroup.zpowers x = ⊤)
    (hQJ : Q ≤ J) (hQ : IsPGroup 2 Q)
    (hQmax : ∀ R : Subgroup X, R ≤ J → IsPGroup 2 R → Nat.card R ≤ Nat.card Q)
    (hxQ : ∀ q ∈ Q, Commute x q) :
    ∃ P : Sylow 2 X, x ∈ (P : Subgroup X) ∧ (P : Subgroup X) ⊓ J ≤ Q ∧
      ∀ p ∈ (P : Subgroup X), Commute x p := by
  have hQx : IsPGroup 2 (Q ⊔ Subgroup.zpowers x : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right' hQ (isPGroup_zpowers_of_orderOf_eq_two hx) fun q hq =>
      Subgroup.centralizer_le_normalizer _
        (zpowers_le_centralizer_zpowers (hxQ q hq).symm (Subgroup.mem_zpowers q))
  obtain ⟨P, hQxP⟩ := hQx.exists_le_sylow
  have hxP : x ∈ (P : Subgroup X) := hQxP (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hPJ : (P : Subgroup X) ⊓ J ≤ Q :=
    (Subgroup.eq_of_le_of_card_ge (le_inf (le_sup_left.trans hQxP) hQJ)
      (hQmax _ inf_le_right (P.isPGroup'.to_le inf_le_left))).ge
  refine ⟨P, hxP, hPJ, fun p hp => ?_⟩
  obtain ⟨y, hy, j, hj, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp
    (show p ∈ Subgroup.zpowers x ⊔ J by rw [sup_comm, htop]; exact Subgroup.mem_top p)
  have hyP : y ∈ (P : Subgroup X) := hQxP (Subgroup.mem_sup_right hy)
  have hjP : j ∈ (P : Subgroup X) := by
    have := (P : Subgroup X).mul_mem ((P : Subgroup X).inv_mem hyP) hp
    rwa [inv_mul_cancel_left] at this
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ((Commute.refl x).zpow_right n).mul_right (hxQ j (hPJ ⟨hjP, hj⟩))

variable (hJ : CFSG.Open.IsQuasisimple J) (hJeven : Even (Nat.card J)) (hx : orderOf x = 2)
  (htop : J ⊔ Subgroup.zpowers x = ⊤) (hQJ : Q ≤ J) (hQ : IsPGroup 2 Q)
  (hQmax : ∀ R : Subgroup X, R ≤ J → IsPGroup 2 R → Nat.card R ≤ Nat.card Q)
  (hxQ : ∀ q ∈ Q, Commute x q) (hC : C ≤ Subgroup.center X) (hC2 : IsPGroup 2 C)
include hJ hJeven hx htop hQJ hQ hQmax hxQ hC hC2

omit hx htop hxQ hC2 in
theorem commute_of_sup_eq_top_of_mem_oddCore [C.Normal]
    (hiso : ∀ g : X ⧸ C, g * QuotientGroup.mk' C x * g⁻¹ * (QuotientGroup.mk' C x)⁻¹ ∈
      CFSG.oddCore (X ⧸ C)) :
    ∀ j ∈ J, Commute x j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect J := ⟨hJ.1⟩
  set ψ := (QuotientGroup.mk' (CFSG.oddCore (X ⧸ C))).comp (QuotientGroup.mk' C) with hψ
  have hcen : ∀ g : X, Commute (ψ x) (ψ g) := by
    intro g
    have h1 : ψ ⁅g, x⁆ = 1 := by
      rw [hψ, MonoidHom.comp_apply, map_commutatorElement, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, commutatorElement_def]
      exact hiso _
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hcomm : ⁅J, Subgroup.zpowers x⁆ ≤ ψ.ker := by
    refine Subgroup.commutator_le.mpr fun j _ y hy => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, map_zpow]
    exact ((hcen j).zpow_left n).eq.symm
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hJ
      (ψ.ker.subgroupOf J) with hcenter | htopJ
  · have hdouble : ⁅⁅J, Subgroup.zpowers x⁆, J⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have haJ : a ∈ J := Subgroup.commutator_le_left J _ ha
      have hmem : (⟨a, haJ⟩ : J) ∈ ψ.ker.subgroupOf J := Subgroup.mem_subgroupOf.mpr (hcomm ha)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcenter hmem) ⟨j, hj⟩)
    have hbot := CFSG.ComponentClassification.Quasisimple.perfect_double_commutator J
      (Subgroup.zpowers x) hdouble
    intro j hj
    have h1 : ⁅j, x⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hj (Subgroup.mem_zpowers x)
      rwa [hbot, Subgroup.mem_bot] at this
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  · exfalso
    have hJker : J ≤ ψ.ker := Subgroup.subgroupOf_eq_top.mp htopJ
    have hQC : Q ≤ C := by
      intro q hq
      have hψq : ψ q = 1 := hJker (hQJ hq)
      rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hψq
      have h1 := map_eq_one_of_isPGroup_of_mem_oddCore hQ (QuotientGroup.mk' C) hq hψq
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨QJ, hQJeq⟩ := exists_sylow_eq_subgroupOf hQJ hQ hQmax
    have hQJc : (QJ : Subgroup J) ≤ Subgroup.center J := by
      rw [hQJeq]
      intro q hq
      rw [Subgroup.mem_subgroupOf] at hq
      exact Subgroup.mem_center_iff.mpr fun j =>
        Subtype.ext (Subgroup.mem_center_iff.mp (hC (hQC hq)) j)
    exact not_dvd_card_of_isPerfect_of_sylow_le_center QJ hQJc (even_iff_two_dvd.mp hJeven)

theorem zStarStep_of_sup_eq_top :
    (∀ j ∈ J, Commute x j) ∨
      ∃ k ∈ J, ∃ q ∈ Q, q ∉ C ∧ q * q = 1 ∧ k⁻¹ * x * k = x * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hx
  by_cases hxC : x ∈ C
  · exact Or.inl fun j _ => (Subgroup.mem_center_iff.mp (hC hxC) j).symm
  have hCn : C.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (hC hn) g, mul_inv_cancel_right]
    exact hn⟩
  by_cases hiso : ∀ g : X ⧸ C, g * QuotientGroup.mk' C x * g⁻¹ * (QuotientGroup.mk' C x)⁻¹ ∈
      CFSG.oddCore (X ⧸ C)
  · exact Or.inl (commute_of_sup_eq_top_of_mem_oddCore hJ hJeven hQJ hQ hQmax hC hiso)
  right
  push Not at hiso
  obtain ⟨g, hg⟩ := hiso
  obtain ⟨P, hxP, hPJ, hxcP⟩ := exists_sylow_of_sup_eq_top hx htop hQJ hQ hQmax hxQ
  set π := QuotientGroup.mk' C with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective C
  have hx' : orderOf (π x) = 2 := by
    refine orderOf_eq_two_of_mul_self (by rw [← map_mul, hxx, map_one]) fun h => hxC ?_
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hxc' : π x ∈ Subgroup.centralizer
      ((P.mapSurjective hπs : Subgroup (X ⧸ C)) : Set (X ⧸ C)) := by
    rw [Sylow.coe_mapSurjective, Subgroup.mem_centralizer_iff]
    rintro _ ⟨p, hp, rfl⟩
    rw [← map_mul, ← map_mul, (hxcP p hp).eq]
  obtain ⟨h, hhP, hhne⟩ :=
    CFSG.ComponentClassification.AschbacherComponentInvolution.central_involution_moved_in_sylow
      (P.mapSurjective hπs) (π x) hx' hxc' g hg
  obtain ⟨k₀, rfl⟩ := hπs h
  obtain ⟨y, hy, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp
    (show k₀ ∈ Subgroup.zpowers x ⊔ J by rw [sup_comm, htop]; exact Subgroup.mem_top k₀)
  have hconj : (y * k)⁻¹ * x * (y * k) = k⁻¹ * x * k := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxy : x ^ n * x = x * x ^ n := ((Commute.refl x).zpow_left n).eq
    calc (x ^ n * k)⁻¹ * x * (x ^ n * k) = k⁻¹ * ((x ^ n)⁻¹ * (x * x ^ n)) * k := by group
      _ = k⁻¹ * x * k := by rw [← hxy, inv_mul_cancel_left]
  have hkP : k⁻¹ * x * k ∈ (P : Subgroup X) := by
    rw [Sylow.coe_mapSurjective] at hhP
    obtain ⟨p, hp, hpk⟩ := Subgroup.mem_map.mp hhP
    have h1 : π p = π (k⁻¹ * x * k) := by rw [hpk, ← hconj]; simp only [map_mul, map_inv]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have := (P : Subgroup X).mul_mem hp (hC2.le_sylow_of_normal P h1)
    rwa [mul_inv_cancel_left] at this
  set q := x⁻¹ * (k⁻¹ * x * k) with hq
  have hqJ : q ∈ J := by
    have := J.mul_mem (hJn.conj_mem k⁻¹ (J.inv_mem hk) x⁻¹) hk
    rwa [inv_inv, show x⁻¹ * k⁻¹ * x * k = q by rw [hq]; group] at this
  have hqQ : q ∈ Q := hPJ ⟨(P : Subgroup X).mul_mem ((P : Subgroup X).inv_mem hxP) hkP, hqJ⟩
  have hxq : k⁻¹ * x * k = x * q := by rw [hq, mul_inv_cancel_left]
  refine ⟨k, hk, q, hqQ, fun hqC => hhne ?_, ?_, hxq⟩
  · have h1 : (π (y * k))⁻¹ * π x * π (y * k) = π ((y * k)⁻¹ * x * (y * k)) := by
      simp only [map_mul, map_inv]
    rw [h1, hconj, hxq, map_mul, show π q = 1 from (QuotientGroup.eq_one_iff q).mpr hqC,
      mul_one]
  · have hsq : (x * q) * (x * q) = 1 := by
      rw [← hxq]
      calc k⁻¹ * x * k * (k⁻¹ * x * k) = k⁻¹ * (x * x) * k := by group
        _ = 1 := by rw [hxx, mul_one, inv_mul_cancel]
    calc q * q = (x * x) * (q * q) := by rw [hxx, one_mul]
      _ = x * (x * q) * q := by group
      _ = x * (q * x) * q := by rw [(hxQ q hqQ).eq]
      _ = (x * q) * (x * q) := by group
      _ = 1 := hsq

end ZStarStep

theorem zStarStep {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hJ : CFSG.Open.IsQuasisimple J) (hJeven : Even (Nat.card J))
    {x : G} (hx : orderOf x = 2) (hxN : x ∈ Subgroup.normalizer (J : Set G))
    {Q : Subgroup G} (hQJ : Q ≤ J) (hQ : IsPGroup 2 Q)
    (hQmax : ∀ R : Subgroup G, R ≤ J → IsPGroup 2 R → Nat.card R ≤ Nat.card Q)
    (hxQ : ∀ q ∈ Q, Commute x q)
    {C : Subgroup G} (hCJ : C ≤ J) (hCc : C ≤ Subgroup.centralizer (J : Set G))
    (hCx : ∀ c ∈ C, Commute x c) (hC2 : IsPGroup 2 C) :
    (∀ j ∈ J, Commute x j) ∨
      ∃ k ∈ J, ∃ q ∈ Q, q ∉ C ∧ q * q = 1 ∧ k⁻¹ * x * k = x * q := by
  set Y := J ⊔ Subgroup.zpowers x with hY
  have hJY : J ≤ Y := le_sup_left
  have hxY : x ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hQY : Q ≤ Y := hQJ.trans hJY
  have hCY : C ≤ Y := hCJ.trans hJY
  have hJn : (J.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJY).mpr
    (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxN))
  have htop : J.subgroupOf Y ⊔ Subgroup.zpowers (⟨x, hxY⟩ : Y) = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJY, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rfl
  have hcard : ∀ {R : Subgroup G} (_ : R ≤ Y), Nat.card (R.subgroupOf Y) = Nat.card R :=
    fun hR => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv
  have hC : C.subgroupOf Y ≤ Subgroup.center Y := by
    intro c hc
    rw [Subgroup.mem_subgroupOf] at hc
    have hle : Y ≤ Subgroup.centralizer ({(c : G)} : Set G) := sup_le
      (fun j hj => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hCc hc) j hj))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (hCx c hc).eq))
    exact Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hle g.2))
  have hQmax' : ∀ R : Subgroup Y, R ≤ J.subgroupOf Y → IsPGroup 2 R →
      Nat.card R ≤ Nat.card (Q.subgroupOf Y) := by
    intro R hRJ hR
    have hle : R.map Y.subtype ≤ J := by
      rintro _ ⟨r, hr, rfl⟩
      exact hRJ hr
    have h := hQmax _ hle (hR.map Y.subtype)
    rwa [Subgroup.card_map_of_injective Y.subtype_injective, ← hcard hQY] at h
  rcases zStarStep_of_sup_eq_top
      (CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (Subgroup.subgroupOfEquivOfLe hJY) hJ)
      (by rw [hcard hJY]; exact hJeven) (by rw [Subgroup.orderOf_mk]; exact hx) htop
      (fun q hq => hQJ hq) (hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQY).symm) hQmax'
      (fun q hq => Subtype.ext (hxQ q hq).eq) hC
      (hC2.of_equiv (Subgroup.subgroupOfEquivOfLe hCY).symm) with h | h
  · exact Or.inl fun j hj => congrArg Subtype.val (h ⟨j, hJY hj⟩ hj)
  · obtain ⟨k, hk, q, hq, hqC, hqq, hkq⟩ := h
    exact Or.inr ⟨k, hk, q, hq, hqC, congrArg Subtype.val hqq, congrArg Subtype.val hkq⟩

end CFSG.ProperTwoGeneratedCore.Assembly
