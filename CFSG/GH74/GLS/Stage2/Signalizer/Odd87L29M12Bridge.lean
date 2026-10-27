module

public import CFSG.GH74.GLS.Stage2.Local.P27M12Basic
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29M12Abs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29M12Faith
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87NCDm12Aux
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29NonSwap
import CFSG.GH74.GLS.TwoThin.Equivariance
import CFSG.GH74.GLS.AssemblyComponents
public import Certificates.Kernel.ThCent.Leaves
import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21i
import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnSL23
import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnUT3B
import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic4
import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic5
import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic6
import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic7
import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic8
import CFSG.GH74.GLS.Stage1.Thm4.Core98
import CFSG.GH74.GLS.Stage1.Thm4.Statements
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Defs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpQ8
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Class
import CFSG.GH74.GLS.Stage2.Signalizer.Stmt42
import CFSG.GH74.GLS.Stage2.Signalizer.Stmt43E
import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45c
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29M12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.ABGLocalTools
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.GH74.GLS.Stage2.Local.P34NS CFSG.GH74.GLS.Stage2.Local.P27
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87.NCDm12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem exists_two_power_lift {A B : Type} [Group A] [Group B] [Finite A] (π : A →* B)
    (hπ : Function.Surjective π) {c : B} (hc : ∃ m : ℕ, c ^ (2 ^ m) = 1) :
    ∃ a : A, π a = c ∧ ∃ k : ℕ, a ^ (2 ^ k) = 1 := by
  obtain ⟨a₀, rfl⟩ := hπ c
  obtain ⟨m, hm⟩ := hc
  by_cases hm0 : m = 0
  · subst hm0
    refine ⟨1, ?_, 0, by simp⟩
    rw [map_one]
    simpa using hm.symm
  obtain ⟨i, r, hr, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos a₀).ne' 2 (by decide)
  have hcop : Nat.Coprime r (2 ^ m) :=
    Nat.Coprime.pow_right m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hr).symm
  obtain ⟨s, hs0, hs1⟩ := Nat.chineseRemainder hcop 0 1
  have hlt : 1 < 2 ^ m := Nat.one_lt_two_pow hm0
  have hsmod : s % 2 ^ m = 1 := by
    have : s % 2 ^ m = 1 % 2 ^ m := hs1
    rw [this]; exact Nat.mod_eq_of_lt hlt
  have hrs : r ∣ s := (Nat.modEq_zero_iff_dvd).mp hs0
  refine ⟨a₀ ^ s, ?_, i, ?_⟩
  · rw [map_pow]
    have h := Nat.div_add_mod s (2 ^ m)
    rw [hsmod] at h
    rw [← h, pow_add, pow_mul, hm, one_pow, one_mul, pow_one]
  · obtain ⟨t, ht⟩ := hrs
    have h : a₀ ^ (2 ^ i * r) = 1 := by rw [← hord]; exact pow_orderOf_eq_one a₀
    calc (a₀ ^ s) ^ (2 ^ i) = (a₀ ^ (2 ^ i * r)) ^ t := by
          rw [← pow_mul, ← pow_mul, ht]; congr 1; ring
      _ = 1 := by rw [h, one_pow]

section Bridge

variable {G : Type} [Group G] [Finite G]

theorem twoNilp_centralizer_pair_of_m12 {x y : G} {K : Subgroup G} {q : ℕ}
    (hx2 : orderOf x = 2) (hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hKL : IVK.IsL2 (↥K ⧸ pPrimeCore 2 ↥K) (fun r => r = q)) (hq8 : q % 8 = 3 ∨ q % 8 = 5)
    (hyC : y ∈ centralizer ({x} : Set G)) (hy2 : orderOf y = 2) (hPGL : PGLModO K (zpowers y) q)
    (hRO : oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔
        pPrimeCoreOf 2 (centralizer ({x} : Set G)) =
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ zpowers x ⊔ (K ⊔ zpowers y))
    {u : G} (hu : u ∈ centralizer ({x} : Set G)) (hu2 : orderOf u = 2) (hux : u ∉ zpowers x) :
    TwoNilp ↥(centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Odd q := Nat.odd_iff.2 (by omega)
  have h5 : 5 ≤ q := five_le_of_isL2 hKc hKL hq8
  have hx2' : x * x = 1 := by have := pow_orderOf_eq_one x; rwa [hx2, pow_two] at this
  have hy2' : y * y = 1 := by have := pow_orderOf_eq_one y; rwa [hy2, pow_two] at this
  have hu2' : u * u = 1 := by have := pow_orderOf_eq_one u; rwa [hu2, pow_two] at this
  have hxy' : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm
  have hxu : x * u = u * x := (Subgroup.mem_centralizer_singleton_iff.1 hu).symm
  set N : Subgroup G := centralizer ({x} : Set G) with hN
  have hKN : K ≤ N := hKc.1
  have hKy := P27M12.normalizes_of_pgl hq h5 hKL hPGL
  have hJle := P27M12.Jx_le_sup hx2' hy2' hxy' hKN hyC hKy hRO
  have hKJ : K ≤ Jx x := le_sSup hKc
  have hJL := P27M12.isL2_Jx hKc hKJ hJle hKL
  set O : Subgroup ↥N := pPrimeCore 2 ↥N with hO
  set π : ↥N →* ↥N ⧸ O := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hJn : ((Jx x).subgroupOf N).Normal := normal_subgroupOf_of_conj (Jx_normalized x)
  have hJsub : ((Jx x).subgroupOf N).IsSubnormal := hJn.isSubnormal
  set Jt : Subgroup (↥N ⧸ O) := ((Jx x).subgroupOf N).map π with hJt
  have hJtn : Jt.Normal := Subgroup.Normal.map hJn π hπs
  obtain ⟨eJ, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal
      (Jx_le_centralizer x) hJsub
  obtain ⟨F, hF, hFin, hFq, ⟨e₀⟩⟩ := hJL
  have hFq' : Nat.card F = q := hFq
  let e : ↥Jt ≃* IVK.L2 F := eJ.symm.trans e₀
  have hL2F : IVK.L2Field F := ⟨hFq' ▸ hq, by omega⟩
  have h8F : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5 := by rw [hFq']; exact hq8
  let xN : ↥N := ⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  let uN : ↥N := ⟨u, hu⟩
  have hxcen : xN ∈ Subgroup.center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  let ξ : ↥N ⧸ O := π xN
  have hξc : ξ ∈ Subgroup.center (↥N ⧸ O) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := hπs g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hxcen g']
  let v : ↥N ⧸ O := π uN
  have hv2 : v * v = 1 := by
    rw [← map_mul]
    have : uN * uN = 1 := Subtype.ext hu2'
    rw [this, map_one]
  have hv : v ∉ zpowers ξ := by
    rintro ⟨k, hk⟩
    have hk' : π (xN ^ k) = π uN := by rw [map_zpow]; exact hk
    have hk'' : ((xN ^ k : ↥N) : ↥N ⧸ O) = ((uN : ↥N) : ↥N ⧸ O) := hk'
    have hmem : (xN ^ k)⁻¹ * uN ∈ O := QuotientGroup.eq.mp hk''
    have hxuN : Commute xN uN := Subtype.ext hxu
    have hcom : Commute ((xN ^ k)⁻¹) uN := (hxuN.zpow_left k).inv_left
    have hxN2 : xN ^ 2 = 1 := by rw [pow_two]; exact Subtype.ext hx2'
    have huN2 : uN ^ 2 = 1 := by rw [pow_two]; exact Subtype.ext hu2'
    have hsq : ((xN ^ k)⁻¹ * uN) ^ 2 = 1 := by
      rw [hcom.mul_pow, huN2, mul_one, inv_pow]
      have : (xN ^ k) ^ 2 = (xN ^ 2) ^ k := by
        rw [← zpow_natCast, ← zpow_natCast xN 2, ← zpow_mul, ← zpow_mul, mul_comm]
      rw [this, hxN2, one_zpow, inv_one]
    have hodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hord : orderOf ((xN ^ k)⁻¹ * uN) = 1 := by
      have h1 : orderOf ((xN ^ k)⁻¹ * uN) ∣ Nat.card O := by
        have := Subgroup.orderOf_dvd_natCard O hmem
        exact this
      have h2 : orderOf ((xN ^ k)⁻¹ * uN) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · exfalso
        rw [h] at h1
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)
    have hone : (xN ^ k)⁻¹ * uN = 1 := orderOf_eq_one_iff.mp hord
    have huxk : uN = xN ^ k := by
      have := congrArg (fun t => xN ^ k * t) hone
      simpa using this
    apply hux
    refine ⟨k, ?_⟩
    have := congrArg Subtype.val huxk
    simpa using this.symm
  have hKsub : (K.subgroupOf N).IsSubnormal := by
    obtain ⟨_, _, hs, _⟩ := hKc.2
    exact hs
  have hPN : K ⊔ zpowers y ≤ N := sup_le hKN ((zpowers_le).mpr hyC)
  have hxN' : x ∈ N := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hQN : zpowers x ⊔ (K ⊔ zpowers y) ≤ N := sup_le ((zpowers_le).mpr hxN') hPN
  have hOe : (pPrimeCoreOf 2 N).subgroupOf N = O := by
    unfold pPrimeCoreOf
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  have hker : ∀ c ∈ centralizer (Jt : Set (↥N ⧸ O)), (∃ m : ℕ, c ^ (2 ^ m) = 1) →
      c ∈ zpowers ξ := by
    intro c hc hc2
    obtain ⟨n, hnc, k, hnk⟩ := exists_two_power_lift π hπs hc2
    have hnk' : ((n : G)) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hnk
      simpa using this
    have hnP : IsPGroup 2 ↥(zpowers (n : G)) := by
      have hord : orderOf (n : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hnk'
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers]; exact hi)
    have hnN : zpowers (n : G) ≤ N := (zpowers_le).mpr n.2
    have hnR : (n : G) ∈ oPrimeResidualOf 2 N :=
      le_oPrimeResidualOf_of_isPGroup' hnN hnP (Subgroup.mem_zpowers _)
    have hnQ : (n : G) ∈ pPrimeCoreOf 2 N ⊔ (zpowers x ⊔ (K ⊔ zpowers y)) := by
      have h1 : (n : G) ∈ oPrimeResidualOf 2 N ⊔ pPrimeCoreOf 2 N := Subgroup.mem_sup_left hnR
      rw [hRO, sup_assoc] at h1
      exact h1
    have hnQ' : n ∈ (pPrimeCoreOf 2 N ⊔ (zpowers x ⊔ (K ⊔ zpowers y))).subgroupOf N := hnQ
    rw [Subgroup.subgroupOf_sup (TwoThin.pPrimeCoreOf_le N) hQN, hOe] at hnQ'
    have hcQ : c ∈ ((zpowers x ⊔ (K ⊔ zpowers y)).subgroupOf N).map π := by
      have h1 := Subgroup.mem_map_of_mem π hnQ'
      rw [Subgroup.map_sup] at h1
      have hO1 : O.map π = ⊥ := (Subgroup.map_eq_bot_iff _).2 (by rw [hπ, QuotientGroup.ker_mk'])
      rw [hO1, bot_sup_eq, hnc] at h1
      exact h1
    rw [Subgroup.subgroupOf_sup ((zpowers_le).mpr hxN') hPN, Subgroup.map_sup] at hcQ
    have haξ : ∀ a ∈ ((zpowers x).subgroupOf N).map π, a ∈ zpowers ξ := by
      intro a ha
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨j, hj⟩ := ha'
      have : a' = xN ^ j := Subtype.ext (by simpa using hj.symm)
      exact ⟨j, by rw [this, map_zpow]⟩
    have hacen : ∀ a ∈ ((zpowers x).subgroupOf N).map π, a ∈ Subgroup.center (↥N ⧸ O) :=
      fun a ha => (Subgroup.zpowers_le.mpr hξc) (haξ a ha)
    have hcomm : ∀ a ∈ ((zpowers x).subgroupOf N).map π,
        ∀ b ∈ ((K ⊔ zpowers y).subgroupOf N).map π, a * b = b * a :=
      fun a ha b _ => (Subgroup.mem_center_iff.mp (hacen a ha) b).symm
    obtain ⟨a, ha, b, hb, hcab⟩ := exists_mul_of_mem_sup_of_commute_aux hcomm hcQ
    obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp hb
    have hbJ : ∀ t ∈ Jt, π p' * t = t * π p' := by
      intro t ht
      have h1 : t * c = c * t := (Subgroup.mem_centralizer_iff.mp hc t ht)
      rw [hcab] at h1
      have h2 : t * a = a * t := (Subgroup.mem_center_iff.mp (hacen a ha) t)
      have h3 : a * (t * π p') = a * (π p' * t) := by
        calc a * (t * π p') = (a * t) * π p' := by group
          _ = (t * a) * π p' := by rw [h2]
          _ = t * (a * π p') := by group
          _ = (a * π p') * t := h1
          _ = a * (π p' * t) := by group
      exact (mul_left_cancel h3).symm
    have hPnorm : ∀ p ∈ K ⊔ zpowers y, ∀ k ∈ K, p * k * p⁻¹ ∈ K := by
      have hyn : y ∈ normalizer (K : Set G) := P27M12.mem_normalizer_of_involution hy2' hKy
      have hPn : K ⊔ zpowers y ≤ normalizer (K : Set G) :=
        sup_le Subgroup.le_normalizer ((zpowers_le).mpr hyn)
      intro p hp k hk
      exact (Subgroup.mem_normalizer_iff.mp (hPn hp) k).mp hk
    have hpP : (p' : G) ∈ K ⊔ zpowers y := hp'
    have hcomm' : ∀ k ∈ K, (p' : G) * k * (p' : G)⁻¹ * k⁻¹ ∈ pPrimeCoreOf 2 K := by
      intro k hk
      let kN : ↥N := ⟨k, hKN hk⟩
      have hkJ : π kN ∈ Jt :=
        Subgroup.mem_map_of_mem π (show kN ∈ (Jx x).subgroupOf N from hKJ hk)
      have h1 := hbJ _ hkJ
      have h2 : π (p' * kN * p'⁻¹ * kN⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      have hgK : (p' : G) * k * (p' : G)⁻¹ * k⁻¹ ∈ K :=
        K.mul_mem (hPnorm _ hpP k hk) (K.inv_mem hk)
      have hgN : (p' : G) * k * (p' : G)⁻¹ * k⁻¹ ∈ N := hKN hgK
      refine TwoThin.mem_pPrimeCoreOf_of_barMk_eq_one hKN hKsub hgK hgN ?_
      have : (⟨(p' : G) * k * (p' : G)⁻¹ * k⁻¹, hgN⟩ : ↥N) = p' * kN * p'⁻¹ * kN⁻¹ :=
        Subtype.ext (by simp [kN])
      rw [this]
      exact h2
    have hmemK := mem_pPrimeCoreOf_of_commutes hq h5 hKL hPGL hpP hcomm'
    have hp1 : π p' = 1 := by
      rw [TwoThin.pPrimeCoreOf_eq_map_subgroupOf hKN] at hmemK
      obtain ⟨m₁, hm₁, hm₁e⟩ := hmemK
      obtain ⟨m₂, hm₂, hm₂e⟩ := hm₁
      have hker2 := ker_restrict_eq_pPrimeCore hKsub
      have hm₂k : m₂ ∈ ((QuotientGroup.mk' (pPrimeCore 2 ↥N)).comp (K.subgroupOf N).subtype).ker :=
        by rw [hker2]; exact hm₂
      have hπm : π ((K.subgroupOf N).subtype m₂) = 1 := hm₂k
      have hp'e : p' = (K.subgroupOf N).subtype m₂ := by
        apply Subtype.ext
        rw [← hm₁e, ← hm₂e]
        rfl
      rw [hp'e]
      exact hπm
    rw [hcab, hp1, mul_one]
    exact haξ a ha
  have hY := twoNilp_centralizer_of_normal_L2 hL2F h8F e ξ hξc hker hv2 hv
  have hle : N ⊓ centralizer ({u} : Set G) ≤ N := inf_le_left
  let f0 : ↥(N ⊓ centralizer ({u} : Set G)) →* ↥N ⧸ O := π.comp (Subgroup.inclusion hle)
  have hmaps : ∀ d : ↥(N ⊓ centralizer ({u} : Set G)),
      f0 d ∈ centralizer ({v} : Set (↥N ⧸ O)) := by
    intro d
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdu : (d : G) * u = u * d := Subgroup.mem_centralizer_singleton_iff.mp d.2.2
    show π (Subgroup.inclusion hle d) * π uN = π uN * π (Subgroup.inclusion hle d)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hdu
  let f : ↥(N ⊓ centralizer ({u} : Set G)) →* ↥(centralizer ({v} : Set (↥N ⧸ O))) :=
    f0.codRestrict _ hmaps
  have hkerf : f.ker = f0.ker := by
    ext d
    simp [f, MonoidHom.mem_ker]
  have hodd : Odd (Nat.card f.ker) := by
    rw [hkerf]
    let φ : ↥f0.ker →* ↥O :=
      ((Subgroup.inclusion hle).comp f0.ker.subtype).codRestrict O fun d =>
        (QuotientGroup.eq_one_iff _).mp d.2
    have hinj : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : ↥O => ((t : ↥N) : G)) hab
    have hdvd : Nat.card f0.ker ∣ Nat.card O := Subgroup.card_dvd_of_injective φ hinj
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hdvd
  exact twoNilp_of_odd_ker f hodd hY
end Bridge

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29M12
