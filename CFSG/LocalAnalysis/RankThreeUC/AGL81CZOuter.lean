module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

theorem dvd_card_mulAut_of_not_mem_centralizer {X : Type*} [Group X] {d : ℕ} (hd : d.Prime)
    {J : Subgroup X} {u : X} (hdu : ∃ n : ℕ, u ^ d ^ n = 1)
    (huJ : u ∈ normalizer (J : Set X)) (hu : u ∉ centralizer (J : Set X)) :
    d ∣ Nat.card (MulAut J) := by
  obtain ⟨n, hn⟩ := hdu
  have hgpow : (⟨u, huJ⟩ : ↥(normalizer (J : Set X))) ^ d ^ n = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hn
  have hσ1 : Subgroup.normalizerMonoidHom J ⟨u, huJ⟩ ≠ 1 := by
    intro hσ
    have hgker : (⟨u, huJ⟩ : ↥(normalizer (J : Set X))) ∈
        (Subgroup.normalizerMonoidHom J).ker := MonoidHom.mem_ker.mpr hσ
    rw [Subgroup.normalizerMonoidHom_ker] at hgker
    exact hu (Subgroup.mem_subgroupOf.mp hgker)
  have hσpow : (Subgroup.normalizerMonoidHom J ⟨u, huJ⟩) ^ d ^ n = 1 := by
    rw [← MonoidHom.map_pow, hgpow, MonoidHom.map_one]
  have hord : orderOf (Subgroup.normalizerMonoidHom J ⟨u, huJ⟩) ∣ d ^ n :=
    orderOf_dvd_of_pow_eq_one hσpow
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hd).mp hord
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm
    exact hσ1 hm
  refine dvd_trans ?_ (orderOf_dvd_natCard (Subgroup.normalizerMonoidHom J ⟨u, huJ⟩))
  rw [hm]
  exact dvd_pow_self d hm0

theorem not_mem_sup_centralizer_of_not_dvd {X : Type*} [Group X] [Finite X] {d : ℕ}
    (hd : d.Prime) {J : Subgroup X} (hJ : ¬ d ∣ Nat.card J) {u : X}
    (hdu : ∃ n : ℕ, u ^ d ^ n = 1) (huJ : u ∈ normalizer (J : Set X))
    (hu : u ∉ centralizer (J : Set X)) : u ∉ J ⊔ centralizer (J : Set X) := by
  obtain ⟨n, hn⟩ := hdu
  intro huR
  have hcomm : ∀ a ∈ J, ∀ b ∈ centralizer (J : Set X), a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp hb a ha
  obtain ⟨j, hj, c, hc, hjc⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm huR
  have hcx : ∀ x ∈ J, x * c = c * x := fun x hx => Subgroup.mem_centralizer_iff.mp hc x hx
  have hσ : Subgroup.normalizerMonoidHom J ⟨u, huJ⟩ = MulAut.conj (⟨j, hj⟩ : ↥J) := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
    show u * (x : X) * u⁻¹ = j * (x : X) * j⁻¹
    have hconj : c * (x : X) * c⁻¹ = (x : X) := by
      rw [← hcx x x.2]
      group
    calc u * (x : X) * u⁻¹
        = (j * c) * (x : X) * (j * c)⁻¹ := by rw [hjc]
      _ = j * (c * (x : X) * c⁻¹) * j⁻¹ := by group
      _ = j * (x : X) * j⁻¹ := by rw [hconj]
  have hτ : orderOf (MulAut.conj (⟨j, hj⟩ : ↥J)) ∣ Nat.card J :=
    dvd_trans (orderOf_map_dvd (MulAut.conj : ↥J →* MulAut ↥J) (⟨j, hj⟩ : ↥J))
      (orderOf_dvd_natCard (⟨j, hj⟩ : ↥J))
  rw [← hσ] at hτ
  have hgpow : (⟨u, huJ⟩ : ↥(normalizer (J : Set X))) ^ d ^ n = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hn
  have hσpow : (Subgroup.normalizerMonoidHom J ⟨u, huJ⟩) ^ d ^ n = 1 := by
    rw [← MonoidHom.map_pow, hgpow, MonoidHom.map_one]
  have hord : orderOf (Subgroup.normalizerMonoidHom J ⟨u, huJ⟩) ∣ d ^ n :=
    orderOf_dvd_of_pow_eq_one hσpow
  have hcop : Nat.Coprime (d ^ n) (Nat.card J) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hd).mpr hJ)
  have hone : orderOf (Subgroup.normalizerMonoidHom J ⟨u, huJ⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hord hτ
  have hσ1 : Subgroup.normalizerMonoidHom J ⟨u, huJ⟩ = 1 := orderOf_eq_one_iff.mp hone
  have hgker : (⟨u, huJ⟩ : ↥(normalizer (J : Set X))) ∈
      (Subgroup.normalizerMonoidHom J).ker := MonoidHom.mem_ker.mpr hσ1
  rw [Subgroup.normalizerMonoidHom_ker] at hgker
  exact hu (Subgroup.mem_subgroupOf.mp hgker)

theorem eq_top_of_isPGroup_quotient {X : Type*} [Group X] [Finite X] {d : ℕ} (hd : d.Prime)
    (hno : ∀ N : Subgroup X, N.Normal → N.index ≠ d) {N : Subgroup X} [N.Normal]
    (hq : IsPGroup d (X ⧸ N)) : N = ⊤ := by
  by_contra hN
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hq
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hN (Subgroup.index_eq_one.mp (by rw [Subgroup.index_eq_card, hm]))
  obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime d (n := m - 1)
    (by rw [hm]; exact pow_dvd_pow d (Nat.sub_le m 1))
  have hKindex : K.index = d := by
    have h := Subgroup.index_mul_card K
    rw [hKcard, hm] at h
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)
    have hpow : d ^ m = d * d ^ (m - 1) := by
      conv_lhs => rw [← hm1]
      rw [pow_succ']
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hd.pos (m - 1)) h
  have hmin : (Nat.card (X ⧸ N)).minFac = d := by
    rw [hm, Nat.pow_minFac hm0, Nat.Prime.minFac_eq hd]
  have hKnormal : K.Normal :=
    Subgroup.normal_of_index_eq_minFac_card (G := X ⧸ N) (H := K) (by rw [hKindex, hmin])
  have hN'normal : (K.comap (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.comap hKnormal (QuotientGroup.mk' N)
  have hN'index : (K.comap (QuotientGroup.mk' N)).index = d := by
    rw [Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective N), hKindex]
  exact hno (K.comap (QuotientGroup.mk' N)) hN'normal hN'index

theorem mem_of_not_dvd_index {X : Type*} [Group X] [Finite X] {d : ℕ} (hd : d.Prime)
    {R : Subgroup X} [R.Normal] (hR : ¬ d ∣ R.index) {u : X} (hdu : ∃ n : ℕ, u ^ d ^ n = 1) :
    u ∈ R := by
  obtain ⟨n, hn⟩ := hdu
  have hπpow : (QuotientGroup.mk' R u) ^ d ^ n = 1 := by
    rw [← MonoidHom.map_pow, hn, MonoidHom.map_one]
  have hord1 : orderOf (QuotientGroup.mk' R u) ∣ d ^ n := orderOf_dvd_of_pow_eq_one hπpow
  have hord2 : orderOf (QuotientGroup.mk' R u) ∣ R.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (d ^ n) R.index :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hd).mpr hR)
  have hone : orderOf (QuotientGroup.mk' R u) = 1 := Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
  have hπu : QuotientGroup.mk' R u = 1 := orderOf_eq_one_iff.mp hone
  rw [QuotientGroup.mk'_apply] at hπu
  exact (QuotientGroup.eq_one_iff u).mp hπu

theorem not_normal_of_not_mem_centralizer (hk : KFactNormalComplement) {X : Type} [Group X]
    [Finite X] (hX : CFSG.Open.IsKGroup X) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hno : ∀ N : Subgroup X, N.Normal → N.index ≠ d) {J : Subgroup X}
    (hJ : CFSG.IsComponent J) (hJd : ¬ d ∣ Nat.card J) {u : X} (hdu : ∃ n : ℕ, u ^ d ^ n = 1)
    (huJ : u ∈ normalizer (J : Set X)) (hu : u ∉ centralizer (J : Set X)) : ¬ J.Normal := by
  intro hJn
  haveI : J.Normal := hJn
  unfold KFactNormalComplement at hk
  obtain ⟨N, hNn, _, hrel, hq⟩ := hk X hX J hJ hJn d hd hd2 hJd
  haveI : N.Normal := hNn
  have hNtop : N = ⊤ := eq_top_of_isPGroup_quotient hd hno hq
  have hrel' : ¬ d ∣ (J ⊔ Subgroup.centralizer (J : Set X)).index := by
    rw [← Subgroup.relIndex_top_right (J ⊔ Subgroup.centralizer (J : Set X)), ← hNtop]
    exact hrel
  haveI : (J ⊔ Subgroup.centralizer (J : Set X)).Normal :=
    Subgroup.sup_normal J (Subgroup.centralizer (J : Set X))
  exact not_mem_sup_centralizer_of_not_dvd hd hJd hdu huJ hu
    (mem_of_not_dvd_index hd hrel' hdu)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
