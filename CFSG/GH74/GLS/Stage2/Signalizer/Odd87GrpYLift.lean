module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpComp
public import CFSG.GH74.GLS.Stage2.Local.Concl
import CFSG.GH74.GLS.IVK.L2.Lemma113
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Abstract

variable {Q : Type} [Group Q]

private theorem eq_one_of_mem_odd_of_pow_two_pow [Finite Q] {N : Subgroup Q} (hodd : Odd (Nat.card N)) {n : Q}
    (hn : n ∈ N) {k : ℕ} (hk : n ^ (2 ^ k) = 1) : n = 1 := by
  have hcop : Nat.Coprime (2 ^ k) (Nat.card N) := (Nat.coprime_two_left.mpr hodd).pow_left k
  exact orderOf_eq_one_iff.mp
    ((Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk) hcop).eq_one_of_dvd
      (Subgroup.orderOf_dvd_natCard N hn))

private theorem eq_of_orderOf_two_of_mulEquiv_sl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {X : Type} [Group X] (e : X ≃* IVK.SL2 F) {t₁ t₂ : X} (h₁ : orderOf t₁ = 2) (h₂ : orderOf t₂ = 2) :
    t₁ = t₂ := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  let φ : X ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  have key : ∀ t : X, orderOf t = 2 →
      ((φ t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    intro t ht
    have hord : orderOf (φ t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
    refine CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 _ ?_ ?_
    · have := pow_orderOf_eq_one (φ t)
      rwa [hord] at this
    · intro h1
      rw [h1, orderOf_one] at hord
      exact absurd hord (by norm_num)
  exact φ.injective (Matrix.SpecialLinearGroup.ext _ _ fun i j => by rw [key t₁ h₁, key t₂ h₂])

private theorem commutator_mem_of_orderOf_two_quot {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (N : Subgroup Q) [N.Normal] (e : Q ⧸ N ≃* IVK.SL2 F) {s : Q} (hs : orderOf (s : Q ⧸ N) = 2) (q : Q) :
    q * s * q⁻¹ * s⁻¹ ∈ N := by
  have h1 : orderOf ((q * s * q⁻¹ : Q) : Q ⧸ N) = 2 := by
    have : ((q * s * q⁻¹ : Q) : Q ⧸ N) = MulAut.conj (q : Q ⧸ N) (s : Q ⧸ N) := by
      simp [MulAut.conj_apply]
    rw [this, MulEquiv.orderOf_eq]
    exact hs
  have h2 := eq_of_orderOf_two_of_mulEquiv_sl2 hodd e h1 hs
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h2, mul_inv_cancel]

private theorem exists_lift_order_four [Finite Q] (N : Subgroup Q) [N.Normal] (hodd : Odd (Nat.card N))
    (x : Q ⧸ N) (hx : orderOf x = 4) :
    ∃ (y₀ : Q) (r : ℕ), Odd r ∧ (y₀ : Q ⧸ N) = x ^ r ∧ orderOf (y₀ : Q ⧸ N) = 4 ∧ y₀ ^ 4 = 1 := by
  obtain ⟨q₀, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, r, hr, hok⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos q₀).ne'
  have hr0 : r ≠ 0 := hr.pos.ne'
  have hmk : ((q₀ ^ r : Q) : Q ⧸ N) = (q₀ : Q ⧸ N) ^ r := QuotientGroup.mk_pow N q₀ r
  have hord : orderOf (q₀ ^ r) = 2 ^ k := by
    rw [orderOf_pow_of_dvd hr0 ⟨2 ^ k, by rw [hok, mul_comm]⟩, hok, Nat.mul_div_cancel _ hr.pos]
  have hcop : Nat.Coprime (orderOf (q₀ : Q ⧸ N)) r := by
    rw [hx]
    exact (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ (Nat.coprime_two_left.mpr hr).pow_left 2
  have hx4 : orderOf ((q₀ ^ r : Q) : Q ⧸ N) = 4 := by
    rw [hmk, hcop.orderOf_pow, hx]
  have h4 : (q₀ : Q ⧸ N) ^ 4 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one _
  have hmem : (q₀ ^ r) ^ 4 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, ← pow_mul, mul_comm, pow_mul, h4,
      one_pow]
  have hk : ((q₀ ^ r) ^ 4) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
  exact ⟨q₀ ^ r, r, hr, hmk, hx4, eq_one_of_mem_odd_of_pow_two_pow hodd hmem hk⟩

private theorem exists_inverted_lift_abstract [Finite Q] {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) (N : Subgroup Q) [N.Normal] (hNodd : Odd (Nat.card N)) (hNc : N ≤ center Q)
    (e : Q ⧸ N ≃* IVK.SL2 F) (c : Q ≃* Q) (hcc : ∀ q, c (c q) = q) (hcN : N.map c.toMonoidHom = N)
    (hnt : ∃ q : Q, c q * q⁻¹ ∉ N) :
    ∃ y₀ : Q, y₀ * y₀ ≠ 1 ∧ (y₀ * y₀) * (y₀ * y₀) = 1 ∧
      (∀ q : Q, q * (y₀ * y₀) * q⁻¹ * (y₀ * y₀)⁻¹ ∈ N) ∧ c y₀ = y₀⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a : MulAut (Q ⧸ N) := QuotientGroup.congr N N c hcN
  have ha : ∀ q : Q, a (q : Q ⧸ N) = ((c q : Q) : Q ⧸ N) := fun q => QuotientGroup.congr_mk N N c hcN q
  have haa : a * a = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | _ q => rw [MulAut.mul_apply, ha, ha, hcc, MulAut.one_apply]
  have ha1 : a ≠ 1 := by
    intro h
    obtain ⟨q, hq⟩ := hnt
    apply hq
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← ha, h,
      MulAut.one_apply, mul_inv_cancel]
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact haa) ha1
  obtain ⟨x, hx4, hax⟩ := IVK.ivk_1_13 F hodd h3 (Q ⧸ N) e a ha2
  obtain ⟨y₀, r, hr, hy₀x, hy₀ord, hy₀pow⟩ := exists_lift_order_four N hNodd x hx4
  have hay : a (y₀ : Q ⧸ N) = (y₀ : Q ⧸ N)⁻¹ := by
    rw [hy₀x, map_pow, hax, inv_pow]
  have hn : c y₀ * y₀ ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← ha, hay, inv_mul_cancel]
  have hcy : c y₀ = y₀⁻¹ := by
    have hcomm : Commute (c y₀ * y₀) y₀⁻¹ := (Subgroup.mem_center_iff.mp (hNc hn) y₀⁻¹).symm
    have hcy' : c y₀ = (c y₀ * y₀) * y₀⁻¹ := by group
    have hn4 : (c y₀ * y₀) ^ (2 ^ 2) = 1 := by
      have h1 : (c y₀) ^ 4 = 1 := by rw [← map_pow, hy₀pow, map_one]
      rw [hcy', hcomm.mul_pow, inv_pow, hy₀pow, inv_one, mul_one] at h1
      simpa using h1
    have : c y₀ * y₀ = 1 := eq_one_of_mem_odd_of_pow_two_pow hNodd hn hn4
    rw [hcy', this, one_mul]
  have hsq : ((y₀ * y₀ : Q) : Q ⧸ N) = (y₀ : Q ⧸ N) ^ 2 := by
    rw [QuotientGroup.mk_mul, pow_two]
  have hs2 : orderOf ((y₀ * y₀ : Q) : Q ⧸ N) = 2 := by
    rw [hsq, orderOf_pow_of_dvd (by norm_num) (by rw [hy₀ord]; norm_num), hy₀ord]
  refine ⟨y₀, fun h => ?_, ?_, fun q => commutator_mem_of_orderOf_two_quot hodd N e hs2 q, hcy⟩
  · have h' : (y₀ : Q ⧸ N) ^ 2 = 1 := by rw [← hsq, h, QuotientGroup.mk_one]
    have := orderOf_dvd_of_pow_eq_one h'
    rw [hy₀ord] at this
    omega
  · calc (y₀ * y₀) * (y₀ * y₀) = y₀ ^ 2 * y₀ ^ 2 := by rw [pow_two]
      _ = y₀ ^ 4 := by rw [← pow_add]
      _ = 1 := hy₀pow

end Abstract

section Ambient

variable {A : Type} [Group A] [Finite A]

theorem pPrimeCore_le_center_comp {J : Subgroup A} (hJ : IsQuasisimple ↥J) : pPrimeCore 2 ↥J ≤ center ↥J := by
  intro n hn
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥J)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hcent := quasisimple_odd_normal_le_center (J := J) (N := pPrimeCoreOf 2 J) hJ
    (Subgroup.map_subtype_le _) ?_ ?_
  · rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_map_of_mem J.subtype hn)) (q : A) q.2)
  · have : (pPrimeCoreOf 2 J).subgroupOf J = pPrimeCore 2 ↥J :=
      Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
    rw [this]
    exact pPrimeCore_normal
  · show Odd (Nat.card ((pPrimeCore 2 ↥J).map J.subtype))
    rw [Subgroup.card_map_of_injective J.subtype_injective]
    exact hodd

private theorem eq_one_or_eq_of_mem_zpowers_sq {B : Type} [Group B] {s g : B} (hs : s * s = 1)
    (hg : g ∈ zpowers s) : g = 1 ∨ g = s := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, hs, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hs, one_zpow, one_mul]

private def conjOfNormalizer (J : Subgroup A) {z : A} (hz : z ∈ normalizer (J : Set A)) : ↥J ≃* ↥J where
  toFun q := ⟨z * q * z⁻¹, (Subgroup.mem_normalizer_iff.mp hz q).mp q.2⟩
  invFun q := ⟨z⁻¹ * q * z, by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hz) q).mp q.2⟩
  left_inv q := by ext; simp [mul_assoc]
  right_inv q := by ext; simp [mul_assoc]
  map_mul' p q := by ext; simp [mul_assoc]

theorem exists_inverted_lift {J : Subgroup A} {z : A} (hJ : IsComponent J) (hzJ : z ∈ normalizer (J : Set A))
    (hz2 : z * z = 1) (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Hat J ≃* IVK.SL2 F) (hnt : ∃ j ∈ J, z * j * z⁻¹ * j⁻¹ ∉ pPrimeCoreOf 2 J) :
    ∃ y ∈ J, y * y ≠ 1 ∧ (y * y) * (y * y) = 1 ∧ (∀ j ∈ J, (y * y) * j = j * (y * y)) ∧
      z * y * z⁻¹ = y⁻¹ := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥J)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hNc : pPrimeCore 2 ↥J ≤ center ↥J := pPrimeCore_le_center_comp hJ.1
  let cz : ↥J ≃* ↥J := conjOfNormalizer J hzJ
  have hcz : ∀ q : ↥J, ((cz q : ↥J) : A) = z * q * z⁻¹ := fun q => rfl
  have hcc : ∀ q : ↥J, cz (cz q) = q := by
    intro q
    apply Subtype.ext
    rw [hcz, hcz, hzinv]
    calc z * (z * (q : A) * z) * z = (z * z) * (q : A) * (z * z) := by group
      _ = q := by rw [hz2]; group
  have hcN : (pPrimeCore 2 ↥J).map cz.toMonoidHom = pPrimeCore 2 ↥J := pPrimeCore_map_iso 2 cz
  have hnt' : ∃ q : ↥J, cz q * q⁻¹ ∉ pPrimeCore 2 ↥J := by
    obtain ⟨j, hj, hjn⟩ := hnt
    refine ⟨⟨j, hj⟩, fun h => hjn ?_⟩
    exact Subgroup.mem_map_of_mem J.subtype h
  obtain ⟨y₀, hy2, hy4, hycomm, hyinv⟩ :=
    exists_inverted_lift_abstract hodd h3 (pPrimeCore 2 ↥J) hNodd hNc e cz hcc hcN hnt'
  refine ⟨(y₀ : A), y₀.2, fun h => hy2 (Subtype.ext h), congrArg Subtype.val hy4, ?_, ?_⟩
  ·
    set s : A := (y₀ : A) * y₀
    have hsJ : s ∈ J := J.mul_mem y₀.2 y₀.2
    have hs2 : s * s = 1 := congrArg Subtype.val hy4
    have hXJ : zpowers s ≤ J := Subgroup.zpowers_le.mpr hsJ
    have hcentr : ∀ g₁ ∈ J, g₁ * s * g₁⁻¹ * s⁻¹ ∈ centralizer (J : Set A) := by
      intro g₁ hg₁
      have hn := hNc (hycomm ⟨g₁, hg₁⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have := Subgroup.mem_center_iff.mp hn ⟨h, hh⟩
      exact congrArg Subtype.val this
    have hle : ⁅J, zpowers s⁆ ≤ centralizer (J : Set A) := by
      refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
      rcases eq_one_or_eq_of_mem_zpowers_sq hs2 hg₂ with rfl | rfl
      · simp
      · exact hcentr g₁ hg₁
    have hbot : ⁅J, zpowers s⁆ = ⊥ :=
      comm_eq_bot_of_central (Subgroup.isPerfect_iff.mp hJ.1.1) (hXJ.trans Subgroup.le_normalizer) hle
    intro j hj
    have h1 : ⁅j, s⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hj (Subgroup.mem_zpowers s)
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  · exact congrArg Subtype.val hyinv

end Ambient

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
