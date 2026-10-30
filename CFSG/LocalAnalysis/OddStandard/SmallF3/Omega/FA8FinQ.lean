module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem fa8fin_quat_partner (g : QuaternionGroup 2) (h1 : g ≠ 1)
    (h2 : g ≠ QuaternionGroup.a 2) :
    ∃ h : QuaternionGroup 2, h * g * h⁻¹ = QuaternionGroup.a 2 * g := by
  revert g
  decide +kernel

private lemma fa8fin_h_a2_central (y : QuaternionGroup 2) :
    y * QuaternionGroup.a 2 = QuaternionGroup.a 2 * y := by
  revert y
  decide +kernel

private lemma fa8fin_h_eq_of_mem_zpowers {G : Type*} [Group G] {z w : G} (hz2 : z * z = 1)
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hw : w ∈ zpowers z) : w = z := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hmod : z ^ k = z ^ (k % 2) :=
    zpow_eq_zpow_emod k (by rw [zpow_ofNat, pow_two, hz2])
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [hmod, h0] at hk
    simp only [zpow_zero] at hk
    exact absurd hk.symm hw1
  · rw [hmod, h1] at hk
    rw [zpow_one] at hk
    exact hk.symm

private lemma fa8fin_h_factor_z {G : Type} [Group G] {Q P R : Subgroup G} {z : G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hz : centerIn R = zpowers z)
    (hQR : Q ≤ R) (hPR : P ≤ R) (hsup : Q ⊔ P = R)
    (hcross : ∀ x ∈ Q, ∀ y ∈ P, x * y = y * x)
    (e : ↥Q ≃* QuaternionGroup 2) :
    ∃ hzQ : z ∈ Q, e ⟨z, hzQ⟩ = QuaternionGroup.a 2 := by
  let w : ↥Q := e.symm (QuaternionGroup.a 2)
  have hwdef : w = e.symm (QuaternionGroup.a 2) := rfl
  have hwsq : (w : G) * w = 1 := by
    have ha2 : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by
      decide +kernel
    have h : w * w = 1 := by
      show e.symm (QuaternionGroup.a 2) * e.symm (QuaternionGroup.a 2) = 1
      rw [← map_mul, ha2, map_one]
    simpa using congrArg Subtype.val h
  have hwne : (w : G) ≠ 1 := by
    intro hcon
    have h1 : w = 1 := Subtype.ext hcon
    have h2 : (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := by
      have h3 : e.symm (QuaternionGroup.a 2) = 1 := by
        rw [← hwdef]
        exact h1
      simpa using congrArg e h3
    exact (by decide +kernel : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1) h2
  have hwcentQ : w ∈ Subgroup.center ↥Q := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply e.injective
    rw [map_mul, map_mul, hwdef, MulEquiv.apply_symm_apply]
    exact fa8fin_h_a2_central (e x)
  have hwcent : ∀ x ∈ Q, x * (w : G) = (w : G) * x := by
    intro x hx
    have := Subgroup.mem_center_iff.mp hwcentQ (⟨x, hx⟩ : ↥Q)
    simpa using congrArg Subtype.val this
  have hcentR : ∀ g ∈ R, g * (w : G) = (w : G) * g := by
    have hQ : Q ≤ Subgroup.centralizer ({(w : G)} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hwcent x hx
    have hP : P ≤ Subgroup.centralizer ({(w : G)} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcross (w : G) w.2 y hy).symm
    have hle : Q ⊔ P ≤ Subgroup.centralizer ({(w : G)} : Set G) := sup_le hQ hP
    rw [hsup] at hle
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have hwmem : (w : G) ∈ zpowers z := by
    have hmem : (w : G) ∈ centerIn R := by
      rw [centerIn, Subgroup.mem_map]
      refine ⟨⟨(w : G), hQR w.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcentR y y.2)
    rwa [hz] at hmem
  have heq : (w : G) = z := fa8fin_h_eq_of_mem_zpowers hz2 hwsq hwne hwmem
  have hzQ : z ∈ Q := by
    rw [← heq]
    exact w.2
  refine ⟨hzQ, ?_⟩
  have hsub : (⟨z, hzQ⟩ : ↥Q) = w := Subtype.ext (by rw [heq])
  rw [hsub]
  exact MulEquiv.apply_symm_apply e _

private lemma fa8fin_h_sq {G : Type*} [Group G] {Q : Subgroup G} {z : G}
    (hzQ : z ∈ Q) (e : ↥Q ≃* QuaternionGroup 2)
    (hez : e ⟨z, hzQ⟩ = QuaternionGroup.a 2) :
    ∀ g ∈ Q, g * g = 1 ∨ g * g = z := by
  have hfact : ∀ y : QuaternionGroup 2, y * y = 1 ∨ y * y = QuaternionGroup.a 2 := by
    decide +kernel
  intro g hg
  rcases hfact (e ⟨g, hg⟩) with h | h
  · left
    have h1 : (⟨g, hg⟩ : ↥Q) * ⟨g, hg⟩ = 1 := by
      apply e.injective
      rw [map_mul, h, map_one]
    simpa using congrArg Subtype.val h1
  · right
    have h1 : (⟨g, hg⟩ : ↥Q) * ⟨g, hg⟩ = ⟨z, hzQ⟩ := by
      apply e.injective
      rw [map_mul, h, hez]
    simpa using congrArg Subtype.val h1

private lemma fa8fin_h_single_partner {G : Type*} [Group G] {Q : Subgroup G} {z : G}
    (hzQ : z ∈ Q) (e : ↥Q ≃* QuaternionGroup 2)
    (hez : e ⟨z, hzQ⟩ = QuaternionGroup.a 2)
    {g : G} (hg : g ∈ Q) (hg1 : g ≠ 1) (hgz : g ≠ z) :
    ∃ h ∈ Q, h * g * h⁻¹ = z * g := by
  let xg : ↥Q := ⟨g, hg⟩
  have hx1 : e xg ≠ 1 := by
    intro hx
    apply hg1
    have h1 : xg = 1 := by
      simpa using congrArg e.symm hx
    simpa [xg] using congrArg Subtype.val h1
  have hx2 : e xg ≠ QuaternionGroup.a 2 := by
    intro hx
    apply hgz
    have h1 : xg = e.symm (QuaternionGroup.a 2) := by
      simpa using congrArg e.symm hx
    have h2 : (⟨z, hzQ⟩ : ↥Q) = e.symm (QuaternionGroup.a 2) := by
      simpa using congrArg e.symm hez
    have h3 : (⟨z, hzQ⟩ : ↥Q) = xg := h2.trans h1.symm
    simpa [xg] using (congrArg Subtype.val h3).symm
  obtain ⟨h', hh'⟩ := fa8fin_quat_partner (e xg) hx1 hx2
  refine ⟨(e.symm h' : ↥Q), (e.symm h').2, ?_⟩
  have hQ : (e.symm h' : ↥Q) * xg * (e.symm h')⁻¹ = ⟨z, hzQ⟩ * xg := by
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [hh', hez]
  simpa [xg] using congrArg Subtype.val hQ

private lemma fa8fin_h_mem_sup {G : Type*} [Group G] {Q₁ Q₂ : Subgroup G}
    (hcomm : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x) :
    ∀ g ∈ Q₁ ⊔ Q₂, ∃ x ∈ Q₁, ∃ y ∈ Q₂, g = x * y := by
  have hle : Q₁ ≤ Subgroup.centralizer (Q₂ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y hy).symm
  have hnorm : Q₁ ≤ Subgroup.normalizer (Q₂ : Set G) :=
    hle.trans (Subgroup.centralizer_le_normalizer (Q₂ : Set G))
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right Q₁ Q₂ hnorm
  intro g hg
  have hg' : g ∈ (↑(Q₁ ⊔ Q₂) : Set G) := hg
  rw [hcoe, Set.mem_mul] at hg'
  obtain ⟨x, hx, y, hy, hxy⟩ := hg'
  exact ⟨x, hx, y, hy, hxy.symm⟩

private lemma fa8fin_h_center_mem {G : Type} [Group G] {R : Subgroup G} {z : G}
    (hz : centerIn R = zpowers z) : z ∈ R ∧ ∀ g ∈ R, g * z = z * g := by
  have hzR : z ∈ centerIn R := by
    rw [hz]
    exact Subgroup.mem_zpowers z
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hzR
  have hval : (c : G) = z := hcz
  refine ⟨?_, ?_⟩
  · rw [← hval]
    exact c.2
  · intro g hg
    have hy := Subgroup.mem_center_iff.mp hc (⟨g, hg⟩ : R)
    simpa [hval] using congrArg Subtype.val hy

theorem fa8fin_partner {G : Type} [Group G] {Q₁ Q₂ : Subgroup G} {z : G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (h₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)) (h₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2))
    (hc : ⁅Q₁, Q₂⁆ = ⊥) (hz : centerIn (Q₁ ⊔ Q₂) = zpowers z) :
    z ∈ Q₁ ⊔ Q₂ ∧ (∀ g ∈ Q₁ ⊔ Q₂, g * z = z * g) ∧
      (∀ g ∈ Q₁ ⊔ Q₂, g * g = 1 ∨ g * g = z) ∧
      ∀ g ∈ Q₁ ⊔ Q₂, g ≠ 1 → g ≠ z → ∃ h ∈ Q₁ ⊔ Q₂, h * g * h⁻¹ = z * g := by
  classical
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  have hcomm : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := by
    intro x hx y hy
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm
  obtain ⟨hzR, hzcent⟩ := fa8fin_h_center_mem hz
  obtain ⟨hzQ1, hez1⟩ :=
    fa8fin_h_factor_z hz2 hz1 hz le_sup_left le_sup_right rfl hcomm e₁
  obtain ⟨hzQ2, hez2⟩ :=
    fa8fin_h_factor_z hz2 hz1 hz le_sup_right le_sup_left (sup_comm Q₂ Q₁)
      (fun x hx y hy => (hcomm y hy x hx).symm) e₂
  refine ⟨hzR, hzcent, ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, y, hy, hxy⟩ := fa8fin_h_mem_sup hcomm g hg
    have hx' := fa8fin_h_sq hzQ1 e₁ hez1 x hx
    have hy' := fa8fin_h_sq hzQ2 e₂ hez2 y hy
    have hmul : (x * y) * (x * y) = (x * x) * (y * y) := by
      have hcxy : Commute x y := hcomm x hx y hy
      calc (x * y) * (x * y) = (x * y) ^ 2 := by rw [pow_two]
        _ = x ^ 2 * y ^ 2 := hcxy.mul_pow 2
        _ = (x * x) * (y * y) := by rw [pow_two, pow_two]
    have hprod : (x * x) * (y * y) = 1 ∨ (x * x) * (y * y) = z := by
      rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy' <;>
        simp [hx', hy', hz2]
    rw [hxy, hmul]
    exact hprod
  · intro g hg hg1 hgz
    obtain ⟨x, hx, y, hy, hxy⟩ := fa8fin_h_mem_sup hcomm g hg
    by_cases hx0 : x = 1 ∨ x = z
    · have hxQ2 : x ∈ Q₂ := by
        rcases hx0 with rfl | rfl
        · exact Q₂.one_mem
        · exact hzQ2
      have hgQ2 : g ∈ Q₂ := by
        rw [hxy]
        exact Q₂.mul_mem hxQ2 hy
      obtain ⟨h, hhQ, hh⟩ := fa8fin_h_single_partner hzQ2 e₂ hez2 hgQ2 hg1 hgz
      exact ⟨h, (le_sup_right : Q₂ ≤ Q₁ ⊔ Q₂) hhQ, hh⟩
    · push Not at hx0
      obtain ⟨hx1, hxz⟩ := hx0
      obtain ⟨h, hhQ, hh⟩ := fa8fin_h_single_partner hzQ1 e₁ hez1 hx hx1 hxz
      refine ⟨h, (le_sup_left : Q₁ ≤ Q₁ ⊔ Q₂) hhQ, ?_⟩
      have hyc : h * y * h⁻¹ = y := by
        rw [hcomm h hhQ y hy, mul_assoc, mul_inv_cancel, mul_one]
      calc h * g * h⁻¹ = h * (x * y) * h⁻¹ := by rw [hxy]
        _ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
        _ = (z * x) * y := by rw [hh, hyc]
        _ = z * (x * y) := by group
        _ = z * g := by rw [hxy]

theorem fa8fin_cover_inj {A P : Type*} [Group A] [Group P] {ρ : A →* P}
    (h : OddCentralCover ρ) {k : ℕ} {a b : A} (ha : a ^ 2 ^ k = 1) (hb : b ^ 2 ^ k = 1)
    (hab : ρ a = ρ b) : a = b := by
  have hn : a⁻¹ * b ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  have hc : a⁻¹ * b ∈ Subgroup.center A := h.ker_le_center hn
  have hcomm : Commute a (a⁻¹ * b) := Subgroup.mem_center_iff.mp hc a
  have hb' : b = a * (a⁻¹ * b) := by group
  have hpow : (a⁻¹ * b) ^ 2 ^ k = 1 := by
    have h1 : (a * (a⁻¹ * b)) ^ 2 ^ k = 1 := by
      rw [← hb']
      exact hb
    rw [hcomm.mul_pow (2 ^ k), ha, one_mul] at h1
    exact h1
  have hdvd2 : orderOf (a⁻¹ * b) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
  have hdvdN : orderOf (a⁻¹ * b) ∣ Nat.card ρ.ker :=
    Subgroup.orderOf_dvd_natCard ρ.ker hn
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ρ.ker) :=
    (Nat.coprime_two_left.mpr h.odd_card_ker).pow_left k
  have hone : orderOf (a⁻¹ * b) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdN
  exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp hone)

end CFSG.OddStandard.SmallF3.Omega
