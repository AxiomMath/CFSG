module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Leaves
import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ExcShape
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
open scoped MatrixGroups

namespace Ivk93M12F

theorem sl2_three_pow_twelve : ∀ x : SL(2, ZMod 3), x ^ 12 = 1 := by decide

theorem sl2_three_core : ∀ x : SL(2, ZMod 3), x ≠ 1 →
    x ^ 3 ≠ 1 ∨ ∃ g h : SL(2, ZMod 3), g * x = h * g ∧ (x * h) ^ 3 ≠ 1 := by decide

theorem sl2_three_pow_three_of_odd {x : SL(2, ZMod 3)} (hx : Odd (orderOf x)) : x ^ 3 = 1 := by
  have hd : orderOf x ∣ 3 * 4 := orderOf_dvd_of_pow_eq_one (sl2_three_pow_twelve x)
  have hc : Nat.Coprime (orderOf x) 4 := by
    have h2 : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.2 hx
    simpa using Nat.Coprime.pow_right 2 h2
  exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_right hd)

theorem eq_bot_of_normal_odd_sl2_three {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3)
    {G : Type} [Group G] (e : G ≃* SL(2, F)) (M : Subgroup G) [hM : M.Normal]
    (hodd : ∀ m ∈ M, Odd (orderOf m)) : M = ⊥ := by
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact h3
  let σ : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three hc
  let e' : G ≃* SL(2, ZMod 3) := e.trans (Ivk47ab.slMap σ.symm)
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_bot]
  by_contra hne
  have hx1 : e' m ≠ 1 := fun h => hne (e'.injective (h.trans (map_one e').symm))
  rcases sl2_three_core (e' m) hx1 with h | ⟨g, h, hgh, hbad⟩
  · exact h (sl2_three_pow_three_of_odd (by rw [MulEquiv.orderOf_eq]; exact hodd m hm))
  · have hconj : e'.symm h = e'.symm g * m * (e'.symm g)⁻¹ := by
      have : h = g * e' m * g⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        exact hgh.symm
      rw [this]
      simp
    have hmem : m * e'.symm h ∈ M :=
      M.mul_mem hm (by rw [hconj]; exact hM.conj_mem m hm _)
    apply hbad
    apply sl2_three_pow_three_of_odd
    have := hodd _ hmem
    rwa [← MulEquiv.orderOf_eq e', map_mul, MulEquiv.apply_symm_apply] at this

theorem pPrimeCore_eq_bot_of_equiv_sl2_three {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3)
    {G : Type} [Group G] [Finite G] (e : G ≃* SL(2, F)) : pPrimeCore 2 G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pPrimeCore 2 G).Normal := CFSG.pPrimeCore_normal
  refine eq_bot_of_normal_odd_sl2_three h3 e (pPrimeCore 2 G) ?_
  intro m hm
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 G)) :=
    Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := G))
  have hd : orderOf (⟨m, hm⟩ : ↥(pPrimeCore 2 G)) ∣ Nat.card ↥(pPrimeCore 2 G) :=
    orderOf_dvd_natCard _
  rw [← Subgroup.orderOf_coe ⟨m, hm⟩] at hd
  exact Odd.of_dvd_nat hodd hd

theorem card_ge_of_shape_three {Y : Type} [Group Y] [Finite Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Finite F₁] [Finite F₂] (S : Ivk47ab.Shape Y F₁ F₂) (h₁ : Nat.card F₁ = 3)
    (h₂ : Nat.card F₂ = 3) : 288 ≤ Nat.card Y := by
  have hn₂ := GHInv.normal_I₂ S
  have hc := Ivk93M12.card_sup_mul_card_inf_of_normal' S.I₁ S.I₂
  have hI₁ : Nat.card ↥S.I₁ = 24 := by
    rw [Nat.card_congr S.e₁.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h₁]
    norm_num
  have hI₂ : Nat.card ↥S.I₂ = 24 := by
    rw [Nat.card_congr S.e₂.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h₂]
    norm_num
  have hz : Nat.card ↥(S.I₁ ⊓ S.I₂) = 2 := by
    rw [S.inter, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact S.z_sq) S.z_ne
  rw [hI₁, hI₂, hz] at hc
  have := Subgroup.card_le_card_group (S.I₁ ⊔ S.I₂)
  omega

theorem mul_self_mem_of_sup_zpowers {Y : Type} [Group Y] {J : Subgroup Y} [J.Normal] {t : Y}
    (ht : t * t = 1) (hgen : J ⊔ Subgroup.zpowers t = ⊤) (y : Y) : y * y ∈ J := by
  have h1 : y ∈ J ⊔ Subgroup.zpowers t := by rw [hgen]; trivial
  rw [Subgroup.mem_sup_of_normal_left] at h1
  obtain ⟨j, hj, a, ha, rfl⟩ := h1
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hcomm : (t ^ m * t ^ m) = 1 := by
    rw [← (Commute.refl t).mul_zpow m, ht, one_zpow]
  have hmem : j * (t ^ m * j * (t ^ m)⁻¹) ∈ J :=
    J.mul_mem hj ((inferInstance : J.Normal).conj_mem j hj (t ^ m))
  have : j * t ^ m * (j * t ^ m) = j * (t ^ m * j * (t ^ m)⁻¹) * (t ^ m * t ^ m) := by group
  rw [this, hcomm, mul_one]
  exact hmem

theorem exists_eq_sq_pow_of_odd {G : Type*} [Group G] {n : G} (h : Odd (orderOf n)) :
    ∃ k : ℕ, n = (n * n) ^ k := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  rw [← pow_two, ← pow_mul]
  have : 2 * (k + 1) = orderOf n + 1 := by omega
  rw [this, pow_succ, pow_orderOf_eq_one, one_mul]

theorem mul_self_eq_one_of_central {F : Type} [Field F] {Y : Type} [Group Y] {I : Subgroup Y}
    (e : ↥I ≃* SL(2, F)) {a : Y} (ha : a ∈ I) (hc : ∀ a' ∈ I, a * a' = a' * a) :
    a * a = 1 := by
  have hmem : e ⟨a, ha⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc x x.2).symm
  have h1 : e ⟨a, ha⟩ * e ⟨a, ha⟩ = 1 := by
    rcases Ivk47ab.eq_one_or_neg_one_of_mem_center hmem with h | h
    · rw [h, mul_one]
    · rw [h]
      apply Subtype.ext
      simp
  have h2 : (⟨a, ha⟩ : ↥I) * ⟨a, ha⟩ = 1 := by
    apply e.injective
    rw [map_mul, h1, map_one]
  exact congrArg Subtype.val h2

theorem pPrimeCore_eq_bot_of_shape_three {Y : Type} [Group Y] [Finite Y] {F₁ F₂ : Type} [Field F₁]
    [Field F₂] [Finite F₁] [Finite F₂] (S : Ivk47ab.Shape Y F₁ F₂) (h₁ : Nat.card F₁ = 3)
    (h₂ : Nat.card F₂ = 3) : pPrimeCore 2 Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb₁ : pPrimeCore 2 ↥S.I₁ = ⊥ := pPrimeCore_eq_bot_of_equiv_sl2_three h₁ S.e₁
  have hb₂ : pPrimeCore 2 ↥S.I₂ = ⊥ := pPrimeCore_eq_bot_of_equiv_sl2_three h₂ S.e₂
  have hn₁ := GHInv.normal_I₁ S
  have hn₂ := GHInv.normal_I₂ S
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hodd : Odd (orderOf n) := by
    have hodd' : Odd (Nat.card ↥(pPrimeCore 2 Y)) :=
      Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := Y))
    have hd : orderOf (⟨n, hn⟩ : ↥(pPrimeCore 2 Y)) ∣ Nat.card ↥(pPrimeCore 2 Y) :=
      orderOf_dvd_natCard _
    rw [← Subgroup.orderOf_coe ⟨n, hn⟩] at hd
    exact Odd.of_dvd_nat hodd' hd
  have hc₁ : ∀ a ∈ S.I₁, n * a = a * n := fun a ha =>
    Ivk93Exc.commute_pPrimeCore hn₁ hb₁ hn ha
  have hc₂ : ∀ b ∈ S.I₂, n * b = b * n := fun b hb =>
    Ivk93Exc.commute_pPrimeCore hn₂ hb₂ hn hb
  have hJ : n ∈ S.I₁ ⊔ S.I₂ := by
    obtain ⟨k, hk⟩ := exists_eq_sq_pow_of_odd hodd
    rw [hk]
    exact (S.I₁ ⊔ S.I₂).pow_mem
      (mul_self_mem_of_sup_zpowers (J := S.I₁ ⊔ S.I₂) S.t_sq S.gen n) k
  obtain ⟨a, ha, b, hb, rfl⟩ := Ivk47ab.mem_sup_of_commute S.comm hJ
  have hba : b * a = a * b := (S.comm a ha b hb).symm
  have ha1 : ∀ a' ∈ S.I₁, a * a' = a' * a := by
    intro a' ha'
    have h := hc₁ a' ha'
    have hb' : b * a' = a' * b := (S.comm a' ha' b hb).symm
    have h2 : a * a' * b = a' * a * b := by
      calc a * a' * b = a * (a' * b) := mul_assoc _ _ _
        _ = a * (b * a') := by rw [hb']
        _ = a * b * a' := (mul_assoc _ _ _).symm
        _ = a' * (a * b) := h
        _ = a' * a * b := (mul_assoc _ _ _).symm
    exact mul_right_cancel h2
  have hb1 : ∀ b' ∈ S.I₂, b * b' = b' * b := by
    intro b' hb'
    have h := hc₂ b' hb'
    have ha' : a * b' = b' * a := S.comm a ha b' hb'
    have h2 : a * (b * b') = a * (b' * b) := by
      calc a * (b * b') = a * b * b' := (mul_assoc _ _ _).symm
        _ = b' * (a * b) := h
        _ = b' * a * b := (mul_assoc _ _ _).symm
        _ = a * b' * b := by rw [ha']
        _ = a * (b' * b) := mul_assoc _ _ _
    exact mul_left_cancel h2
  have hsq₁ : a * a = 1 := mul_self_eq_one_of_central S.e₁ ha ha1
  have hsq₂ : b * b = 1 := mul_self_eq_one_of_central S.e₂ hb hb1
  have hsq : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hba]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [hsq₁, hsq₂, one_mul]
  obtain ⟨k, hk⟩ := exists_eq_sq_pow_of_odd hodd
  rw [hk, hsq, one_pow]

theorem data_false_of_shape_three {J : Type} [Group J] [Finite J] {y : J}
    (hD : Ivk93M12Data J y) {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (S : Ivk47ab.Shape ↥(centralizer ({y} : Set J)) F₁ F₂) (h₁ : Nat.card F₁ = 3)
    (h₂ : Nat.card F₂ = 3) : False := by
  obtain ⟨P, _, _, zc, hP, N, hN, hz, φ, hφ, hodd, -⟩ := hD.quot
  have hcard := hP.card_eq
  have hY := card_ge_of_shape_three S h₁ h₂
  have hbot := pPrimeCore_eq_bot_of_shape_three S h₁ h₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : φ.ker = ⊥ := by
    have hcop : Nat.Coprime 2 (Nat.card φ.ker) := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      intro hdvd
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
      have := hodd (x : ↥(centralizer ({y} : Set J))) x.2
      rw [Subgroup.orderOf_coe, hx] at this
      exact absurd this (by decide)
    exact CFSG.pPrimeCore_eq_bot_iff.1 hbot φ.ker inferInstance hcop
  have h1 : Nat.card ↥(centralizer ({y} : Set J)) = Nat.card N * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
  rw [hker, Subgroup.card_bot, mul_one] at h1
  have h2 := Subgroup.card_le_card_group N
  omega

theorem data_false_of_shape_card {J : Type} [Group J] [Finite J] {y : J}
    (hD : Ivk93M12Data J y) {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    (S : Ivk47ab.Shape ↥(centralizer ({y} : Set J)) F₁ F₂) (h4 : 4 ≤ Nat.card F₁) : False := by
  have hq : CFSG.IsQuasisimple ↥S.I₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv S.e₁.symm (GHInv.isQuasisimple_sl2 h4)
  have := hD.solvable
  have hs : Group.IsSolvable ↥S.I₁ :=
    Group.isSolvable_of_isSolvable_injective (f := S.I₁.subtype) S.I₁.subtype_injective
  have : Group.IsPerfect ↥S.I₁ := hq.1
  have := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact Group.IsPerfect.not_isSolvable ↥S.I₁ hs

end Ivk93M12F

open Ivk93M12F

theorem ivk93m12_g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93M12Empty (fun X _ => LieModel X .G2 0 p f) := by
  intro p f hp hp2 hf J _ _ hJ y hD
  obtain ⟨F, hF, hFin, S, hcard, -⟩ := GHInv.exists_shape_G2 hp hp2 hJ y hD.central.1
  by_cases h3 : Nat.card F = 3
  · exact data_false_of_shape_three hD S h3 h3
  · have hodd : Odd (Nat.card F) := by
      rw [hcard]
      exact (hp.odd_of_ne_two hp2).pow
    have h4 : 4 ≤ Nat.card F := by
      have := Finite.one_lt_card (α := F)
      obtain ⟨m, hm⟩ := hodd
      omega
    exact data_false_of_shape_card hD S h4

theorem ivk93m12_d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93M12Empty (fun X _ => LieModel X .trialityD4 0 p f) := by
  intro p f hp hp2 hf J _ _ hJ y hD
  obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hc₁, hc₂, -⟩ :=
    GHInv.exists_shape_D4 hp hp2 hJ y hD.central.1
  have hn3 : 3 ≤ p ^ f := by
    have h2 := hp.two_le
    have h3 := Nat.le_self_pow (show f ≠ 0 by omega) p
    have : p ≠ 2 := hp2
    omega
  have h4 : 4 ≤ Nat.card F₁ := by
    rw [hc₁]
    calc 4 ≤ 3 ^ 3 := by norm_num
      _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hn3 3
  exact data_false_of_shape_card hD S h4

end CFSG.GH74.GLS.IVK.Proofs2
