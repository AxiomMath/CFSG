module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import CFSG.CharacterTheory.Semidihedral.CentralQuotients
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralDerivedInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open Subgroup

namespace RankOne

theorem quaternion_central (q : ℕ) (hq : 2 ≤ q) (x : QuaternionGroup q)
    (hx : x ∈ center (QuaternionGroup q)) :
    x = 1 ∨ x = QuaternionGroup.a (q : ZMod (2 * q)) := by
  have : NeZero (2 * q) := ⟨by omega⟩
  rw [mem_center_iff] at hx
  cases x with
  | a j =>
    have h := hx (QuaternionGroup.xa 0)
    simp only [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa, zero_add, zero_sub,
      QuaternionGroup.xa.injEq] at h
    have h2 : ((2 * j.val : ℕ) : ZMod (2 * q)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hlt : j.val < 2 * q := ZMod.val_lt j
    have hdvd : q ∣ j.val := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
    obtain ⟨c, hc⟩ := hdvd
    have hc2 : c < 2 := by
      by_contra hcon
      push Not at hcon
      have : q * 2 ≤ q * c := Nat.mul_le_mul_left q hcon
      omega
    interval_cases c
    · left
      have : j = 0 := by
        rw [← ZMod.natCast_zmod_val j, hc, mul_zero, Nat.cast_zero]
      rw [this, QuaternionGroup.a_zero]
    · right
      congr 1
      rw [← ZMod.natCast_zmod_val j, hc, mul_one]
  | xa i =>
    exfalso
    have h := hx (QuaternionGroup.a 1)
    simp only [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a,
      QuaternionGroup.xa.injEq] at h
    have h2 : ((2 : ℕ) : ZMod (2 * q)) = 0 := by
      push_cast
      linear_combination -h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega

theorem quaternion_half_sq (q : ℕ) :
    QuaternionGroup.a (q : ZMod (2 * q)) ^ 2 = 1 := by
  rw [pow_two, QuaternionGroup.a_mul_a, ← QuaternionGroup.a_zero]
  congr 1
  rw [← two_mul]
  exact_mod_cast ZMod.natCast_self (2 * q)

theorem mem_zpowers_of_sq {H : Type*} [Group H] {x y : H} (hx : x ^ 2 = 1)
    (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  have hsq : x * x = 1 := by rw [← pow_two]; exact hx
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  have hpow : x ^ k = x ^ (k % 2) := by
    conv_lhs => rw [hk]
    rw [zpow_add, zpow_mul, zpow_two, hsq, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hpow, h, zpow_zero]
  · right
    rw [hpow, h, zpow_one]

end RankOne

open RankOne

theorem rankOne_quotient_center {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (hr : Open.pRank 2 (⊤ : Subgroup K) ≤ 1) :
    HasDihedralSylowTwo (K ⧸ center K) ∧ (Nat.card (center K)).factorization 2 ≤ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : CFSG.IsQuasisimple K := CatalogueBAlternating.quasisimple_iff_native.2 hK
  have hr' : CFSG.pRank 2 K ≤ 1 := by
    rw [SectionRank.pRank_eq_open_pRank_top]
    exact hr
  obtain ⟨-, -, hcen, hsyl⟩ :=
    LocalAnalysis.ComponentInitial.quasisimple_rank_one_unique_central_involution hK' hr'
  let T : Sylow 2 K := default
  obtain ⟨r, hr3, ⟨e⟩⟩ := hsyl T
  set q := 2 ^ (r - 2) with hq
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero q := ⟨by omega⟩
  let φ : (T : Subgroup K) →* DihedralGroup q :=
    (Semidihedral.CentralQuotients.quaternionToDihedral q).comp e.toMonoidHom
  have hφ : Function.Surjective φ :=
    (Semidihedral.CentralQuotients.quaternionToDihedral_surjective q).comp e.surjective
  let ψ : (T : Subgroup K) →* K ⧸ center K :=
    (QuotientGroup.mk' (center K)).comp (T : Subgroup K).subtype
  have hker : ψ.ker = φ.ker := by
    ext t
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change (QuotientGroup.mk (t : K) : K ⧸ center K) = 1 ↔
      Semidihedral.CentralQuotients.quaternionToDihedral q (e t) = 1
    rw [QuotientGroup.eq_one_iff, ← MonoidHom.mem_ker,
      Semidihedral.CentralQuotients.quaternionToDihedral_ker]
    constructor
    · intro ht
      have hc : e t ∈ center (QuaternionGroup q) := by
        rw [mem_center_iff]
        intro y
        obtain ⟨s, rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext ((mem_center_iff.1 ht) s)
      rcases quaternion_central q hq2 _ hc with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact mem_zpowers _
    · intro ht
      rcases mem_zpowers_of_sq (quaternion_half_sq q) ht with h | h
      · rw [(MulEquiv.map_eq_one_iff e).1 h]
        exact one_mem _
      · apply hcen
        rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e, h]
        exact (Semidihedral.QuaternionAutomorphismLifting.unique_involution q (by omega) _).2 rfl
  let T' : Sylow 2 (K ⧸ center K) := T.mapSurjective (QuotientGroup.mk'_surjective (center K))
  have hT' : (T' : Subgroup (K ⧸ center K)) = ψ.range := by
    rw [Sylow.coe_mapSurjective, MonoidHom.range_comp, Subgroup.range_subtype]
  have iso : (T' : Subgroup (K ⧸ center K)) ≃* DihedralGroup q :=
    (MulEquiv.subgroupCongr hT').trans ((QuotientGroup.quotientKerEquivRange ψ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ)))
  refine ⟨⟨T', r - 1, by omega, ?_⟩, ?_⟩
  · have hexp : r - 1 - 1 = r - 2 := by omega
    rw [hexp]
    exact ⟨iso⟩
  ·
    let P : Sylow 2 (center K) := default
    have hcardP : Nat.card P = 2 ^ (Nat.card (center K)).factorization 2 :=
      P.card_eq_multiplicity
    set P' : Subgroup K := (P : Subgroup (center K)).map (center K).subtype with hP'
    have hP'c : P' ≤ center K := by
      rintro x ⟨y, -, rfl⟩
      exact y.2
    have hP'n : P'.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have : g * n * g⁻¹ = n := by
        rw [mem_center_iff.1 (hP'c hn) g, mul_inv_cancel_right]
      rw [this]
      exact hn
    have hP'2 : IsPGroup 2 P' := P.isPGroup'.map _
    have hP'T : P' ≤ T := hP'2.le_sylow_of_normal T
    have hle : P'.subgroupOf (T : Subgroup K) ≤ ψ.ker := by
      intro t ht
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk (t : K) : K ⧸ center K) = 1
      rw [QuotientGroup.eq_one_iff]
      exact hP'c ht
    have hcardker : Nat.card φ.ker = 2 := by
      have hQ : Nat.card (QuaternionGroup q) = 4 * q := by
        rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
      have h1 := Subgroup.card_mul_index φ.ker
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hφ, Subgroup.card_top,
        DihedralGroup.nat_card, Nat.card_congr e.toEquiv, hQ] at h1
      have hq0 : 0 < 2 * q := by omega
      have : Nat.card φ.ker * (2 * q) = 2 * (2 * q) := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_right hq0 this
    have hcardP' : Nat.card P = Nat.card P' := by
      rw [hP']
      exact (Nat.card_congr ((P : Subgroup (center K)).equivMapOfInjective _
        (center K).subtype_injective).toEquiv)
    have hle2 : Nat.card P ≤ 2 := by
      rw [hcardP', ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'T).toEquiv]
      calc Nat.card (P'.subgroupOf (T : Subgroup K)) ≤ Nat.card ψ.ker :=
            Subgroup.card_le_of_le hle
        _ = Nat.card φ.ker := by rw [hker]
        _ = 2 := hcardker
    rw [hcardP] at hle2
    by_contra hcon
    push Not at hcon
    have : 2 ^ 2 ≤ 2 ^ (Nat.card (center K)).factorization 2 :=
      Nat.pow_le_pow_right (by norm_num) hcon
    omega

theorem dihedral_quotient_center {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (hd : HasDihedralSylowTwo K) :
    HasDihedralSylowTwo (K ⧸ center K) ∧ (Nat.card (center K)).factorization 2 = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, n, hn, ⟨e⟩⟩ := hd
  obtain ⟨-, -, -, -, hconj⟩ :=
    Semidihedral.Principal.dihedral_derived_involutions_conjugate S hn ⟨e.symm⟩
  have hall := hconj hK.1
  set m := 2 ^ (n - 1) with hm
  have hm2 : 2 ≤ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Fact (1 < m) := ⟨by omega⟩
  set s0 : K := ((e.symm (DihedralGroup.sr 0) : (S : Subgroup K)) : K)
  set s1 : K := ((e.symm (DihedralGroup.sr 1) : (S : Subgroup K)) : K)
  have hs0 : orderOf s0 = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  have hs1 : orderOf s1 = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  have hne : s0 ≠ s1 := by
    intro h
    have h' := e.symm.injective (Subtype.ext h)
    exact zero_ne_one (DihedralGroup.sr.inj h')
  have hnoinv : ∀ z : K, z ∈ center K → orderOf z ≠ 2 := by
    intro z hz hz2
    have huniq : ∀ t : K, orderOf t = 2 → t = z := by
      intro t ht
      obtain ⟨c, hc⟩ := isConj_iff.1 (hall t z ht hz2)
      have hzc : c⁻¹ * z = z * c⁻¹ := mem_center_iff.1 hz c⁻¹
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = c⁻¹ * z * c := by rw [hc]
        _ = z := by rw [hzc]; group
    exact hne ((huniq s0 hs0).trans (huniq s1 hs1).symm)
  have hodd : (Nat.card (center K)).factorization 2 = 0 := by
    by_contra h
    have h2 : 2 ∣ Nat.card (center K) :=
      Nat.dvd_of_factorization_pos h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center K) 2 h2
    exact hnoinv z z.2 (by rw [Subgroup.orderOf_coe]; exact hz)
  refine ⟨?_, hodd⟩
  let ψ : (S : Subgroup K) →* K ⧸ center K :=
    (QuotientGroup.mk' (center K)).comp (S : Subgroup K).subtype
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    have htc : (t : K) ∈ center K := (QuotientGroup.eq_one_iff _).1 ht
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 S.isPGroup' t
    have hdvd : orderOf (⟨t, htc⟩ : center K) ∣ Nat.card (center K) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hj] at hdvd
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
      rw [hj]
      exact one_mem _
    · exfalso
      have h2 : 2 ∣ Nat.card (center K) := (dvd_pow_self 2 hjpos.ne').trans hdvd
      have hpos : 0 < (Nat.card (center K)).factorization 2 :=
        (Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2)
      omega
  let T' : Sylow 2 (K ⧸ center K) := S.mapSurjective (QuotientGroup.mk'_surjective (center K))
  have hT' : (T' : Subgroup (K ⧸ center K)) = ψ.range := by
    rw [Sylow.coe_mapSurjective, MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨T', n, hn,
    ⟨(MulEquiv.subgroupCongr hT').trans ((MonoidHom.ofInjective hinj).symm.trans e)⟩⟩

end CFSG.ComponentClassification.AschbacherKnownGroup
