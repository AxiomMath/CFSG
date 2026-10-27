module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Rho
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13Basic
public import CFSG.LargeExtraspecial.O62Rank
public import CFSG.RankThree.Literature.FSmithInvolution
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace Sec2W

section Group

variable {G : Type} [Group G]

theorem isElemAbelian_zpowers {i : G} (hi : i * i = 1) : IsElemAbelian 2 (zpowers i) :=
  CFSG.Open.isElemAbelian_zpowers (by rw [pow_two]; exact hi)

theorem two_le_pRank [Finite G] {H : Subgroup G} {z i : G} (hz : orderOf z = 2)
    (hi : i * i = 1) (hiz : i ∉ zpowers z) (hc : i * z = z * i) (hiH : i ∈ H) (hzH : z ∈ H) :
    2 ≤ Open.pRank 2 H := by
  have hz2 : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hi1 : i ≠ 1 := fun h => hiz (h ▸ one_mem _)
  have hoi : orderOf i = 2 := orderOf_eq_prime (by rw [sq, hi]) hi1
  have hzi : zpowers z ≤ centralizer (zpowers i : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute i z from hc) n).eq
  have hiz' : zpowers i ≤ centralizer (zpowers z : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute z i from hc.symm) n).eq
  have hE := isElemAbelian_sup_of_le_centralizer (isElemAbelian_zpowers hz2)
    (isElemAbelian_zpowers hi) hzi
  have hinf : zpowers z ⊓ zpowers i = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxz, hxi⟩
    rcases Sec2.eq_one_or_eq_of_mem_zpowers hoi hxi with h | h
    · exact (mem_bot).mpr h
    · exact absurd (h ▸ hxz) hiz
  have hcard := card_sup_mul_card_inf (H := zpowers z) (R := zpowers i)
    (hiz'.trans (centralizer_le_normalizer _))
  rw [hinf, card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoi, hz] at hcard
  refine CFSG.SectionRank.le_pRank one_lt_two (sup_le (zpowers_le.mpr hzH) (zpowers_le.mpr hiH))
    hE (k := 2) ?_
  rw [hcard]
  norm_num

end Group

section Vectors

theorem add_self (v : Fin 6 → ZMod 2) : v + v = 0 := by
  funext k
  exact CharTwo.add_self_eq_zero (v k)

theorem add_ne_zero_of_ne {v w : Fin 6 → ZMod 2} (h : v ≠ w) : v + w ≠ 0 := by
  intro h0
  apply h
  have := congrArg (· + w) h0
  simp only [add_assoc, add_self, add_zero, zero_add] at this
  exact this

theorem polar_self (w : Fin 6 → ZMod 2) : QuadraticMap.polar Sec2Omega.qMinusForm w w = 0 := by
  rw [QuadraticMap.polar, add_self, QuadraticMap.map_zero]
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (Sec2Omega.qMinusForm w) with
    h | h <;> rw [h] <;> decide

theorem polar_eq_one {w₁ w₂ : Fin 6 → ZMod 2} (h1 : qMinus w₁ = 1) (h2 : qMinus w₂ = 1)
    (h12 : qMinus (w₁ + w₂) = 1) : QuadraticMap.polar Sec2Omega.qMinusForm w₁ w₂ = 1 := by
  rw [QuadraticMap.polar, Sec2Omega.qMinusForm_apply, Sec2Omega.qMinusForm_apply,
    Sec2Omega.qMinusForm_apply, h1, h2, h12]
  decide

theorem reflect_mul_reflect_ne {w₁ w₂ : Fin 6 → ZMod 2} (h1 : qMinus w₁ = 1)
    (h2 : qMinus w₂ = 1) (h12 : qMinus (w₁ + w₂) = 1) (hw₁ : w₁ ≠ 0) :
    reflect Sec2Omega.qMinusForm w₁ * reflect Sec2Omega.qMinusForm w₂ ≠
      reflect Sec2Omega.qMinusForm w₂ * reflect Sec2Omega.qMinusForm w₁ := by
  intro h
  have hq1 : Sec2Omega.qMinusForm w₁ = 1 := by rw [Sec2Omega.qMinusForm_apply]; exact h1
  have hq2 : Sec2Omega.qMinusForm w₂ = 1 := by rw [Sec2Omega.qMinusForm_apply]; exact h2
  have hp : QuadraticMap.polar Sec2Omega.qMinusForm w₁ w₂ = 1 := polar_eq_one h1 h2 h12
  have hp' : QuadraticMap.polar Sec2Omega.qMinusForm w₂ w₁ = 1 := by
    rw [QuadraticMap.polar_comm]
    exact hp
  have e1 : reflect Sec2Omega.qMinusForm w₂ w₁ = w₁ + w₂ := by
    rw [reflect_apply_of_map_eq_one hq2, hp, one_smul]
  have e2 : reflect Sec2Omega.qMinusForm w₁ w₁ = w₁ := by
    rw [reflect_apply_of_map_eq_one hq1, polar_self, zero_smul, add_zero]
  have e3 : reflect Sec2Omega.qMinusForm w₁ (w₁ + w₂) = w₂ := by
    rw [reflect_apply_of_map_eq_one hq1, QuadraticMap.polar_add_left, polar_self, hp', zero_add,
      one_smul, add_comm w₁ w₂, add_assoc, add_self, add_zero]
  have e := congrArg (fun f : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) => f w₁) h
  simp only [LinearEquiv.mul_apply] at e
  rw [e1, e3, e2, e1] at e
  apply hw₁
  have := congrArg (· + w₂) e
  simp only [add_assoc, add_self, add_zero] at this
  exact this.symm

theorem mem_of_card_eq
    {U : Subgroup ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))}
    (hUO : U ≤ TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm)
    (hab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (h2 : ∀ x ∈ U, x ^ 2 = 1) (hU : Nat.card U = 16)
    {r : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)}
    (hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm) (hr2 : r * r = 1)
    (hrU : ∀ x ∈ U, x * r = r * x) : r ∈ U := by
  have := LargeExtraspecial.O62.finite_linearEquiv (V := Fin 6 → ZMod 2)
  by_contra hr
  have hEU : IsElemAbelian 2 U := ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, h2⟩
  have hle : U ≤ centralizer (zpowers r : Set _) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute r x from (hrU x hx).symm) n).eq
  have hle' : zpowers r ≤ centralizer (U : Set _) :=
    zpowers_le.mpr (mem_centralizer_iff.mpr fun x hx => hrU x hx)
  have hE := isElemAbelian_sup_of_le_centralizer hEU (isElemAbelian_zpowers hr2) hle
  have hr1 : r ≠ 1 := fun h => hr (h ▸ U.one_mem)
  have hor : orderOf r = 2 := orderOf_eq_prime (by rw [sq, hr2]) hr1
  have hinf : U ⊓ zpowers r = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, hxr⟩
    rcases Sec2.eq_one_or_eq_of_mem_zpowers hor hxr with h | h
    · exact (mem_bot).mpr h
    · exact absurd (h ▸ hxU) hr
  have hcard := card_sup_mul_card_inf (H := U) (R := zpowers r)
    (hle'.trans (centralizer_le_normalizer _))
  rw [hinf, card_bot, mul_one, Nat.card_zpowers, hor, hU] at hcard
  have hbound := LargeExtraspecial.O62.card_le_of_elemAbelian Sec2Omega.finrank_fin_six
    Sec2Omega.qMinusForm_nondegenerate (sup_le hUO (zpowers_le.mpr hrO))
    (fun x hx y hy => congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hE.2
  omega

end Vectors

section Psi

variable {G : Type} [Group G] {Q : Subgroup G} {z : G} {ψ : G → (Fin 6 → ZMod 2)}
  (hadd : ∀ a ∈ Q, ∀ b ∈ Q, ψ (a * b) = ψ a + ψ b)
  (hsurj : ∀ v : Fin 6 → ZMod 2, ∃ a ∈ Q, ψ a = v)
  (hker : ∀ a ∈ Q, ψ a = 0 ↔ a ∈ zpowers z)
include hadd hsurj hker

theorem card_le_two_mul_card (hz : orderOf z = 2) {X : Subgroup G} (hXQ : X ≤ Q)
    (F : Finset (Fin 6 → ZMod 2)) (hF : ∀ a ∈ X, ψ a ∈ F) : Nat.card X ≤ 2 * F.card := by
  classical
  have hcoset : ∀ a ∈ Q, a = Sec2.lift hsurj (ψ a) ∨ a = z * Sec2.lift hsurj (ψ a) := by
    intro a ha
    have h1 := (Sec2.psi_eq_iff hadd hker ha (Sec2.lift_mem hsurj (ψ a))).mp
      (Sec2.psi_lift hsurj _).symm
    rcases Sec2.eq_one_or_eq_of_mem_zpowers hz h1 with h | h
    · exact Or.inl (mul_inv_eq_one.mp h)
    · right
      rw [← h]
      group
  let f : X → F × Bool := fun a =>
    (⟨ψ a, hF a a.2⟩, decide ((a : G) = Sec2.lift hsurj (ψ a)))
  have hinj : Function.Injective f := by
    intro a b hab
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    rw [decide_eq_decide, h1] at h2
    apply Subtype.ext
    by_cases hal : (a : G) = Sec2.lift hsurj (ψ b)
    · exact hal.trans (h2.mp hal).symm
    · have hbl : ¬ (b : G) = Sec2.lift hsurj (ψ b) := fun h => hal (h2.mpr h)
      have ha := (hcoset a (hXQ a.2)).resolve_left (by rwa [h1])
      have hb := (hcoset b (hXQ b.2)).resolve_left hbl
      rw [ha, hb, h1]
  calc Nat.card X ≤ Nat.card (F × Bool) := Nat.card_le_card_of_injective f hinj
    _ = 2 * F.card := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_coe,
        Fintype.card_bool, mul_comm]

end Psi

end Sec2W

namespace Sec2Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F T₀ Q : Subgroup G}
  {u y z : G}

theorem mem_Q_of_isPGroup (h24 : Step24) (h26 : Step26) (h212 : Step212) (h216 : Step216)
    (hQ : Sec2Q G A R g E F T₀ Q u y z) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXN : X ≤ normalizer (Q : Set G)) {r : G} (hr : r ∈ X)
    (hrQ : ∀ a ∈ Q, r * a * r⁻¹ * a⁻¹ ∈ zpowers z) : r ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzQ := hQ.z_mem_Q
  set H : Subgroup G := Q ⊔ X with hH
  have hQH : Q ≤ H := le_sup_left
  have hrH : r ∈ H := (le_sup_right : X ≤ H) hr
  have hHN : H ≤ normalizer (Q : Set G) := sup_le le_normalizer hXN
  have hH2 : IsPGroup 2 H := IsPGroup.to_sup_of_normal_left' (IsPGroup.of_card hQ.q8.2.1) hX hXN
  have hCH : H ⊓ centralizer (Q : Set G) = zpowers z :=
    (hQ.sylow_zpowers_centralizer h24 h26 h212 h216).eq_of_le
      (le_inf (zpowers_le.mpr (hQH hzQ)) (zpowers_le.mpr hQ.z_mem_centralizer_Q)) inf_le_right
      (hH2.to_le inf_le_left)
  have hQn : (Q.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hQH).mpr hHN
  have hQ' : CFSG.IsExtraspecialPGroup 2 (Q.subgroupOf H) :=
    CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      (subgroupOfEquivOfLe hQH).symm hQ.q8.1
  let _ := CFSG.GroupTheory.extraspecialQuotientModule hQ'
  have hCQ' : centralizer ((Q.subgroupOf H : Subgroup H) : Set H) ≤ Q.subgroupOf H := by
    intro c hc
    have hcQ : (c : G) ∈ centralizer (Q : Set G) := mem_centralizer_iff.mpr fun q hq =>
      congrArg Subtype.val (mem_centralizer_iff.mp hc ⟨q, hQH hq⟩ hq)
    have hmem : (c : G) ∈ H ⊓ centralizer (Q : Set G) := ⟨c.2, hcQ⟩
    rw [hCH] at hmem
    exact (zpowers_le.mpr hzQ) hmem
  have hz₀ : ∀ c : ↥H, c * ⟨z, hQH hzQ⟩ = ⟨z, hQH hzQ⟩ * c := fun c =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (hQ.normalizer_le_centralizer (hHN c.2)))
  have hz₀1 : (⟨z, hQH hzQ⟩ : ↥H) ≠ 1 := fun h => by
    have h1 : z = 1 := congrArg Subtype.val h
    have := hQ.order
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hρ1 : CFSG.RankThree.Literature.FSmith.extraspecialConjOrth hQ' hQn ⟨r, hrH⟩ = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    obtain ⟨x, rfl⟩ := CFSG.RankThree.Literature.FSmith.exists_ofMul_of v
    rw [CFSG.RankThree.Literature.FSmith.extraspecialConjOrth_apply, OneMemClass.coe_one,
      LinearEquiv.coe_one, id, CFSG.RankThree.Literature.FSmith.ofMul_of_eq_iff hQ',
      CFSG.RankThree.Literature.FSmith.mem_center_iff_coe hQ' hz₀ hz₀1 hzQ]
    have hmem := hrQ ((x : H) : G) x.2
    have e : (((CFSG.RankThree.Literature.FSmith.conjAut hQn ⟨r, hrH⟩ x * x⁻¹ :
        ↥(Q.subgroupOf H)) : ↥H) : G) = r * ((x : H) : G) * r⁻¹ * ((x : H) : G)⁻¹ := by
      simp [CFSG.RankThree.Literature.FSmith.conjAut_apply]
    rcases Sec2.eq_one_or_eq_of_mem_zpowers hQ.order hmem with h | h
    · left
      exact Subtype.ext (e.trans h)
    · right
      exact Subtype.ext (e.trans h)
  exact CFSG.RankThree.Literature.FSmith.mem_of_extraspecialConjOrth_eq_one hQ' hQn hCQ' hρ1

theorem one_lt_pRank_inf (h24 : Step24) (h26 : Step26)
    (h212 : Step212) (h216 : Step216) (hQ : Sec2Q G A R g E F T₀ Q u y z) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) (hN : rightConjugate Q c ≤ normalizer (Q : Set G)) :
    1 < Open.pRank 2 (Q ⊓ rightConjugate Q c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, -, hadd, hsurj, hker, hsq, -, -, -⟩ := h216 G A R g E F T₀ Q u y z hQ
  have hzQ := hQ.z_mem_Q
  have hcz : c * z = z * c := mem_centralizer_singleton_iff.mp hc
  have hcz' : c⁻¹ * z = z * c⁻¹ := (show Commute c z from hcz).inv_left.eq
  have hQz : Q ≤ centralizer ({z} : Set G) := le_normalizer.trans hQ.normalizer_le_centralizer
  have hzc : ∀ x : G, c * x * c⁻¹ ∈ zpowers z → x ∈ zpowers z := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hx
    refine mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 : c⁻¹ * z ^ k * c = z ^ k := by simpa using Sec2.conj_zpow_eq hcz' k
    calc z ^ k = c⁻¹ * z ^ k * c := h1.symm
      _ = c⁻¹ * (c * x * c⁻¹) * c := by rw [hk]
      _ = x := by group
  set Qc := rightConjugate Q c with hQc
  have hmemQc : ∀ x, x ∈ Qc ↔ c * x * c⁻¹ ∈ Q := fun x => mem_rightConjugate_iff Q c x
  have hzQc : z ∈ Qc := (hmemQc z).mpr (by rw [hcz, mul_inv_cancel_right]; exact hzQ)
  have hQcz : Qc ≤ centralizer ({z} : Set G) := by
    intro x hx
    have h1 := mem_centralizer_singleton_iff.mp (hQz ((hmemQc x).mp hx))
    rw [mem_centralizer_singleton_iff]
    have e1 : c * (x * z) * c⁻¹ = (c * x * c⁻¹) * z := by
      calc c * (x * z) * c⁻¹ = (c * x * c⁻¹) * (c * z * c⁻¹) := by group
        _ = (c * x * c⁻¹) * z := by rw [hcz, mul_inv_cancel_right]
    have e2 : c * (z * x) * c⁻¹ = z * (c * x * c⁻¹) := by
      calc c * (z * x) * c⁻¹ = (c * z * c⁻¹) * (c * x * c⁻¹) := by group
        _ = z * (c * x * c⁻¹) := by rw [hcz, mul_inv_cancel_right]
    exact mul_left_cancel (mul_right_cancel (e1.trans (h1.trans e2.symm)))
  have hsqQ : ∀ a ∈ Q, a * a ∈ zpowers z := fun a ha =>
    (hker _ (Q.mul_mem ha ha)).mp (by rw [hadd a ha a ha]; exact Sec2W.add_self (ψ a))
  have hcommQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ zpowers z := fun a ha b hb =>
    commutator_mem_of_extraspecial hQ.q8.1 hQ.centerIn_Q ha hb
  have hsqQc : ∀ a ∈ Qc, a * a ∈ zpowers z := fun a ha => hzc _ (by
    have := hsqQ _ ((hmemQc a).mp ha)
    rwa [show c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ by group] at this)
  have hcommQc : ∀ a ∈ Qc, ∀ b ∈ Qc, a * b * a⁻¹ * b⁻¹ ∈ zpowers z := fun a ha b hb =>
    hzc _ (by
      have := hcommQ _ ((hmemQc a).mp ha) _ ((hmemQc b).mp hb)
      rwa [show c * a * c⁻¹ * (c * b * c⁻¹) * (c * a * c⁻¹)⁻¹ * (c * b * c⁻¹)⁻¹ =
        c * (a * b * a⁻¹ * b⁻¹) * c⁻¹ by group] at this)
  by_contra hlt
  have hinv : ∀ a ∈ Q ⊓ Qc, a * a = 1 → a ∈ zpowers z := by
    intro a ha ha2
    by_contra haz
    have := Sec2W.two_le_pRank hQ.order ha2 haz (mem_centralizer_singleton_iff.mp (hQz ha.1)) ha
      ⟨hzQ, hzQc⟩
    omega
  have hns : ∀ a ∈ Q ⊓ Qc, ψ a ≠ 0 → qMinus (ψ a) = 1 := by
    intro a ha ha0
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (qMinus (ψ a)) with h | h
    · exact absurd ((hker a ha.1).mpr (hinv a ha ((hsq a ha.1).mp h))) ha0
    · exact h
  have hK : Qc ≤ normalizer (Q : Set G) ⊓ centralizer ({z} : Set G) := le_inf hN hQcz
  set ρ := Sec2.rho hadd hsurj hker hK with hρ
  have hρz : ∀ a : Qc, (a : G) ∈ zpowers z → ρ a = 1 := by
    intro a ha
    rw [hρ, Sec2.rho_eq_one_iff]
    intro b hb
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ha
    have hzb : Commute z b := (mem_centralizer_iff.mp hQ.z_mem_centralizer_Q b hb).symm
    have e : (a : G) * b * (a : G)⁻¹ = b := by
      rw [← hk, (hzb.zpow_left k).eq, mul_inv_cancel_right]
    rw [e, mul_inv_cancel]
    exact one_mem _
  have hab : ∀ x ∈ ρ.range, ∀ x' ∈ ρ.range, x * x' = x' * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have h1 : ρ (a * b * a⁻¹ * b⁻¹) = 1 := hρz _ (by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hcommQc a a.2 b b.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc ρ a * ρ b = (ρ a * ρ b * (ρ a)⁻¹ * (ρ b)⁻¹) * (ρ b * ρ a) := by group
      _ = ρ b * ρ a := by rw [h1, one_mul]
  have h2 : ∀ x ∈ ρ.range, x ^ 2 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, sq]
    exact hρz _ (by simpa only [Subgroup.coe_mul] using hsqQc a a.2)
  have hρO : ρ.range ≤ TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm := by
    rintro _ ⟨a, rfl⟩
    exact Sec2.rho_mem_orthogonalGroup hadd hsurj hker hK hsq a
  have hU : Nat.card ρ.range ≤ 2 ^ 4 :=
    LargeExtraspecial.O62.card_le_of_elemAbelian Sec2Omega.finrank_fin_six
      Sec2Omega.qMinusForm_nondegenerate hρO hab h2
  have hQc2 : IsPGroup 2 Qc := IsPGroup.of_card (n := 7) (by rw [rightConjugate_card]; exact hQ.q8.2.1)
  have hkerQ : ∀ a : Qc, ρ a = 1 → (a : G) ∈ Q := fun a ha =>
    hQ.mem_Q_of_isPGroup h24 h26 h212 h216 hQc2 hN a.2
      ((Sec2.rho_eq_one_iff hadd hsurj hker hK a).mp ha)
  have hprod : Nat.card ρ.range * Nat.card ρ.ker = 128 := by
    rw [mul_comm, ← Subgroup.index_ker, Subgroup.card_mul_index, rightConjugate_card, hQ.q8.2.1]
    norm_num
  have hkle : Nat.card ρ.ker ≤ Nat.card (Q ⊓ Qc : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun a => ⟨((a : Qc) : G), hkerQ a (MonoidHom.mem_ker.mp a.2), (a : Qc).2⟩) ?_
    intro a b hab
    have h := congrArg Subtype.val hab
    simp only at h
    exact Subtype.ext (Subtype.ext h)
  have hfix : ∀ x ∈ ρ.range, ∀ a ∈ Q ⊓ Qc, x (ψ a) = ψ a := by
    rintro _ ⟨b, rfl⟩ a ha
    rw [hρ, Sec2.rho_psi hadd hsurj hker hK b ha.1]
    have hba := (mem_normalizer_iff.mp (hN b.2) a).mp ha.1
    exact (Sec2.psi_eq_iff hadd hker hba ha.1).mpr (hcommQc b b.2 a ha.2)
  have hrefl : ∀ a ∈ Q ⊓ Qc, ∀ x ∈ ρ.range,
      x * reflect Sec2Omega.qMinusForm (ψ a) = reflect Sec2Omega.qMinusForm (ψ a) * x := by
    intro a ha x hx
    have h1 := reflect_conj (hρO hx) (ψ a)
    rw [hfix x hx a ha] at h1
    calc x * reflect Sec2Omega.qMinusForm (ψ a) =
        x * reflect Sec2Omega.qMinusForm (ψ a) * x⁻¹ * x := by group
      _ = reflect Sec2Omega.qMinusForm (ψ a) * x := by rw [h1]
  have hpick : ∀ S : Finset (Fin 6 → ZMod 2), 2 * S.card < Nat.card (Q ⊓ Qc : Subgroup G) →
      ∃ a ∈ Q ⊓ Qc, ψ a ∉ S := by
    intro S hS
    by_contra hcon
    push Not at hcon
    have := Sec2W.card_le_two_mul_card hadd hsurj hker hQ.order inf_le_left S hcon
    omega
  have h8 : 8 ≤ Nat.card (Q ⊓ Qc : Subgroup G) := by
    refine le_trans ?_ hkle
    by_contra h
    push Not at h
    have : Nat.card ρ.range * Nat.card ρ.ker ≤ 16 * 7 :=
      Nat.mul_le_mul (by simpa using hU) (by omega)
    omega
  obtain ⟨a₁, ha₁, hψ₁⟩ := hpick {0} (by rw [Finset.card_singleton]; omega)
  have hc2 : ({0, ψ a₁} : Finset (Fin 6 → ZMod 2)).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])
  obtain ⟨a₂, ha₂, hψ₂⟩ := hpick {0, ψ a₁} (by omega)
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hψ₁ hψ₂
  obtain ⟨hw₂, hw₂₁⟩ := hψ₂
  have h12 : a₁ * a₂ ∈ Q ⊓ Qc := mul_mem ha₁ ha₂
  have hψ12 : ψ (a₁ * a₂) = ψ a₁ + ψ a₂ := hadd a₁ ha₁.1 a₂ ha₂.1
  have hq₁ := hns a₁ ha₁ hψ₁
  have hq₂ := hns a₂ ha₂ hw₂
  have hq₁₂ : qMinus (ψ a₁ + ψ a₂) = 1 := by
    rw [← hψ12]
    exact hns _ h12 (by rw [hψ12]; exact Sec2W.add_ne_zero_of_ne (Ne.symm hw₂₁))
  have hdvd : Nat.card ρ.range ∣ 2 ^ 7 := ⟨Nat.card ρ.ker, by rw [hprod]; norm_num⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hi4 : i ≤ 4 := by
    by_contra h
    push Not at h
    have : 2 ^ 5 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
    rw [← hi] at this
    have := hU
    norm_num at this
    omega
  rcases (show i = 4 ∨ i ≤ 3 by omega) with rfl | hi3
  ·
    have hU16 : Nat.card ρ.range = 16 := by rw [hi]; norm_num
    have hr₁ := Sec2W.mem_of_card_eq hρO hab h2 hU16 (reflect_mem_orthogonalGroup _ (ψ a₁))
      (reflect_mul_self _ (ψ a₁)) (fun x hx => hrefl a₁ ha₁ x hx)
    have hr₂ := Sec2W.mem_of_card_eq hρO hab h2 hU16 (reflect_mem_orthogonalGroup _ (ψ a₂))
      (reflect_mul_self _ (ψ a₂)) (fun x hx => hrefl a₂ ha₂ x hx)
    exact Sec2W.reflect_mul_reflect_ne hq₁ hq₂ hq₁₂ hψ₁ (hab _ hr₁ _ hr₂)
  ·
    have h16 : 16 ≤ Nat.card (Q ⊓ Qc : Subgroup G) := by
      refine le_trans ?_ hkle
      have hU8 : Nat.card ρ.range ≤ 8 := by
        rw [hi]
        calc 2 ^ i ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hi3
          _ = 8 := by norm_num
      by_contra h
      push Not at h
      have : Nat.card ρ.range * Nat.card ρ.ker ≤ 8 * 15 := Nat.mul_le_mul hU8 (by omega)
      omega
    have hc4 : ({0, ψ a₁, ψ a₂, ψ a₁ + ψ a₂} : Finset (Fin 6 → ZMod 2)).card ≤ 4 := by
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      simp
    obtain ⟨a₃, ha₃, hψ₃⟩ := hpick {0, ψ a₁, ψ a₂, ψ a₁ + ψ a₂} (by omega)
    simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hψ₃
    obtain ⟨hw₃, hw₃₁, hw₃₂, hw₃₁₂⟩ := hψ₃
    have hq₃ := hns a₃ ha₃ hw₃
    have hq₁₃ : qMinus (ψ a₁ + ψ a₃) = 1 := by
      rw [← hadd a₁ ha₁.1 a₃ ha₃.1]
      exact hns _ (mul_mem ha₁ ha₃) (by
        rw [hadd a₁ ha₁.1 a₃ ha₃.1]
        exact Sec2W.add_ne_zero_of_ne (Ne.symm hw₃₁))
    have hq₂₃ : qMinus (ψ a₂ + ψ a₃) = 1 := by
      rw [← hadd a₂ ha₂.1 a₃ ha₃.1]
      exact hns _ (mul_mem ha₂ ha₃) (by
        rw [hadd a₂ ha₂.1 a₃ ha₃.1]
        exact Sec2W.add_ne_zero_of_ne (Ne.symm hw₃₂))
    have hψ123 : ψ (a₁ * a₂ * a₃) = ψ a₁ + ψ a₂ + ψ a₃ := by
      rw [hadd _ h12.1 a₃ ha₃.1, hψ12]
    have hq₁₂₃ : qMinus (ψ a₁ + ψ a₂ + ψ a₃) = 1 := by
      rw [← hψ123]
      exact hns _ (mul_mem h12 ha₃) (by
        rw [hψ123]
        exact Sec2W.add_ne_zero_of_ne (Ne.symm hw₃₁₂))
    have key := map_add_add Sec2Omega.qMinusForm (ψ a₁) (ψ a₂) (ψ a₃)
    simp only [Sec2Omega.qMinusForm_apply] at key
    rw [hq₁₂₃, hq₁₂, hq₁₃, hq₂₃, hq₁, hq₂, hq₃] at key
    have h0 : (1 : ZMod 2) + 1 + 1 - 1 - 1 - 1 = 0 := by ring
    rw [h0] at key
    exact one_ne_zero key

end Sec2Q

theorem step219_of (h24 : Step24) (h26 : Step26) (h212 : Step212)
    (h216 : Step216) (h218 : Step218) : Step219 := by
  intro G _ _ A R g E F T₀ Q u y z hQ c hc hN
  exact h218 G A R g E F T₀ Q u y z hQ c hc (hQ.one_lt_pRank_inf h24 h26 h212 h216 hc hN)

end CFSG.ComponentClassification.AS81
