module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64TwoA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Outside
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma mem_centralizer_of_conj_eq {y s : G} (h : s * y * s⁻¹ = y) :
    s ∈ centralizer ({y} : Set G) := by
  intro z hz
  have hzy : z = y := by simpa using hz
  rw [hzy]
  have h' : s * y = y * s := by
    have h'' := congrArg (fun w => w * s) h
    simpa [mul_assoc] using h''
  exact h'.symm

private lemma centralizer_of_normalizer_of_cyclic_two [Finite G] {U : Subgroup G} {y s : G}
    (hU : IsCyclic ↥U) (hy2 : orderOf y = 2) (hyU : y ∈ U)
    (hsN : s ∈ Subgroup.normalizer (U : Set G)) : s ∈ centralizer ({y} : Set G) := by
  have hyU' : s * y * s⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hsN y).mp hyU
  have hord : orderOf (s * y * s⁻¹) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj s) y
    simpa [MulAut.conj_apply, hy2] using h
  have heq : s * y * s⁻¹ = y := sec64_unique_inv hU hyU' hyU hord hy2
  exact mem_centralizer_of_conj_eq heq

private lemma mem_zpowers_involution_of_cyclic_two [Finite G] {U : Subgroup G} {y a : G}
    (hU2 : IsPGroup 2 U) (hU : IsCyclic ↥U) (hy2 : orderOf y = 2) (hyU : y ∈ U)
    (haU : a ∈ U) (ha1 : a ≠ 1) : y ∈ Subgroup.zpowers a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (Subgroup.zpowers a) := hU2.to_le (Subgroup.zpowers_le.mpr haU)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  rw [Nat.card_zpowers] at hk
  have hk1 : k ≠ 0 := by
    intro hk0
    apply ha1
    rw [← orderOf_eq_one_iff, hk, hk0]
    norm_num
  have h2dvd : 2 ∣ orderOf a := by
    rw [hk]
    exact Nat.pow_dvd_pow 2 (Nat.one_le_iff_ne_zero.mpr hk1)
  have hdiv : orderOf a / 2 * 2 = orderOf a := Nat.div_mul_cancel h2dvd
  have hb2 : (a ^ (orderOf a / 2)) ^ 2 = 1 := by
    rw [← pow_mul, hdiv, pow_orderOf_eq_one]
  have hn2pos : 0 < orderOf a / 2 := by
    have hge : 2 ≤ orderOf a := by
      rw [hk]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hk1)
    exact Nat.div_pos hge (by norm_num)
  have hbne : a ^ (orderOf a / 2) ≠ 1 := by
    intro h
    have hdvd : orderOf a ∣ orderOf a / 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    have hle := Nat.le_of_dvd hn2pos hdvd
    have hlt : orderOf a / 2 < orderOf a := Nat.div_lt_self (by omega) (by norm_num)
    omega
  have hbU : a ^ (orderOf a / 2) ∈ U := U.pow_mem haU _
  have hbord : orderOf (a ^ (orderOf a / 2)) = 2 := orderOf_eq_prime hb2 hbne
  have heq : a ^ (orderOf a / 2) = y := sec64_unique_inv hU hbU hyU hbord hy2
  rw [← heq]
  exact Subgroup.npow_mem_zpowers a _

private lemma exists_sq_ne_one_of_cyclic_card_ge_four [Finite G] {U : Subgroup G}
    (hU : IsCyclic ↥U) (hcard : 4 ≤ Nat.card ↥U) : ∃ g ∈ U, g ^ 2 ≠ 1 := by
  haveI : IsCyclic ↥U := hU
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥U)
  refine ⟨(g : G), g.2, ?_⟩
  intro h2
  have hdvd : orderOf g ∣ 2 := by
    have h := orderOf_dvd_iff_pow_eq_one.mpr h2
    rwa [← Subgroup.orderOf_mk (g : G) g.2] at h
  have hle : orderOf g ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  rw [hg] at hle
  omega

private lemma not_isElemAbelian_of_cyclic_card_ge_four [Finite G] {U : Subgroup G}
    (hU : IsCyclic ↥U) (hcard : 4 ≤ Nat.card ↥U) : ¬ CFSG.Open.IsElemAbelian 2 U := by
  obtain ⟨g, hgU, hg2⟩ := exists_sq_ne_one_of_cyclic_card_ge_four hU hcard
  intro h
  exact hg2 (h.2 g hgU)

theorem sec64_ti_conj [Finite G] (hout : Asc82Outside) {T H : Subgroup G} {x y : G}
    (c : Sec64Cfg T H x y) (hcard : 4 ≤ Nat.card ↥(T ⊓ centralizer ({y} : Set G) ⊓ H)) {s : G}
    (hsT : s ∈ T) (hsy : s ∉ centralizer ({y} : Set G)) :
    (T ⊓ centralizer ({y} : Set G) ⊓ H) ⊓ CFSG.conjugate (T ⊓ centralizer ({y} : Set G) ⊓ H) s =
        ⊥ ∧
      CFSG.conjugate (T ⊓ centralizer ({y} : Set G) ⊓ H) s ≤ T ⊓ centralizer ({y} : Set G) ∧
      ∀ u ∈ T ⊓ centralizer ({y} : Set G) ⊓ H,
        ∀ b ∈ CFSG.conjugate (T ⊓ centralizer ({y} : Set G) ⊓ H) s, u * b = b * u := by
  classical
  let R : Subgroup G := T ⊓ centralizer ({y} : Set G)
  let U : Subgroup G := R ⊓ H
  have hUc : IsCyclic ↥U := c.hU
  have hyU : y ∈ U := c.mem_U
  have hy2 : orderOf y = 2 := c.hy
  have hUT : U ≤ T := by
    rw [show U = T ⊓ centralizer ({y} : Set G) ⊓ H from rfl]
    exact le_trans inf_le_left inf_le_left
  have hU2 : IsPGroup 2 U := c.isPGroup.to_le hUT
  have hne : ¬ CFSG.Open.IsElemAbelian 2 U := not_isElemAbelian_of_cyclic_card_ge_four hUc hcard
  have hsN : s ∉ Subgroup.normalizer (U : Set G) := fun hs =>
    hsy (centralizer_of_normalizer_of_cyclic_two hUc hy2 hyU hs)
  have hTI : ∀ s' ∈ T, s' ∉ Subgroup.normalizer (U : Set G) →
      U ⊓ CFSG.conjugate U s' = ⊥ := by
    intro s' hs'T hs'N
    rw [eq_bot_iff]
    intro a ha
    by_contra ha1
    have haU : a ∈ U := (Subgroup.mem_inf.mp ha).1
    have haV : a ∈ CFSG.conjugate U s' := (Subgroup.mem_inf.mp ha).2
    have hconjU : s' * a * s'⁻¹ ∈ U := mem_conjugate_iff'.mp haV
    have hconj_ne : s' * a * s'⁻¹ ≠ 1 := by
      intro h
      apply ha1
      have h' := congrArg (fun w => s'⁻¹ * w * s') h
      simpa [mul_assoc] using h'
    have hy_a : y ∈ Subgroup.zpowers a :=
      mem_zpowers_involution_of_cyclic_two hU2 hUc hy2 hyU haU ha1
    have hy_c : y ∈ Subgroup.zpowers (s' * a * s'⁻¹) :=
      mem_zpowers_involution_of_cyclic_two hU2 hUc hy2 hyU hconjU hconj_ne
    have hconjy_mem : s' * y * s'⁻¹ ∈ Subgroup.zpowers (s' * a * s'⁻¹) := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy_a
      rw [← hn, ← conj_zpow]
      exact Subgroup.zpow_mem_zpowers _ _
    have hconjy2 : orderOf (s' * y * s'⁻¹) = 2 := by
      have h := MulEquiv.orderOf_eq (MulAut.conj s') y
      simpa [MulAut.conj_apply, hy2] using h
    have hconj_eq_self : s' * y * s'⁻¹ = y :=
      sec64_unique_inv (Subgroup.isCyclic_zpowers (s' * a * s'⁻¹)) hconjy_mem hy_c
        hconjy2 hy2
    have hcent : s' ∈ centralizer ({y} : Set G) := mem_centralizer_of_conj_eq hconj_eq_self
    have hs'R : s' ∈ T ⊓ centralizer ({y} : Set G) := ⟨hs'T, hcent⟩
    refine hs'N (Subgroup.mem_normalizer_iff.mpr fun u => ⟨?_, ?_⟩)
    · intro hu
      exact c.norm_U hs'R hu
    · intro hu
      have h : s'⁻¹ * (s' * u * s'⁻¹) * (s'⁻¹)⁻¹ ∈ U := c.norm_U (R.inv_mem hs'R) hu
      simpa [mul_assoc] using h
  have hh := hout.lemma11 G T U c.isPGroup hUT hne hTI s hsT hsN
  refine ⟨hh.1, ?_, hh.2⟩
  intro b hb
  have hbU : s * b * s⁻¹ ∈ U := mem_conjugate_iff'.mp hb
  refine ⟨?_, ?_⟩
  · have h : s⁻¹ * (s * b * s⁻¹) * s ∈ T :=
      T.mul_mem (T.mul_mem (T.inv_mem hsT) (hUT hbU)) hsT
    simpa [mul_assoc] using h
  · intro z hz
    have hzy : z = y := by simpa using hz
    rw [hzy]
    exact hh.2 y hyU b hb

theorem sec64_ti_index [Finite G] (hout : Asc82Outside) {T H : Subgroup G} {x y : G}
    (c : Sec64Cfg T H x y) (hcard : 4 ≤ Nat.card ↥(T ⊓ centralizer ({y} : Set G) ⊓ H))
    (hTR : ¬ T ≤ centralizer ({y} : Set G)) :
    Nat.card ↥(T ⊓ centralizer ({y} : Set G) ⊓ H) ≤ H.relIndex (T ⊓ centralizer ({y} : Set G)) := by
  classical
  let R : Subgroup G := T ⊓ centralizer ({y} : Set G)
  let U : Subgroup G := R ⊓ H
  obtain ⟨s, hsT, hsy⟩ := SetLike.not_le_iff_exists.mp hTR
  have hti := sec64_ti_conj hout c hcard hsT hsy
  let V : Subgroup G := CFSG.conjugate U s
  have hUV : U ⊓ V = ⊥ := hti.1
  have hVR : V ≤ R := hti.2.1
  have hUR : U ≤ R := by
    rw [show U = R ⊓ H from rfl]
    exact inf_le_left
  have hcardV : Nat.card ↥V = Nat.card ↥U := by
    rw [show V = U.map (MulAut.conj s⁻¹).toMonoidHom from rfl]
    exact Subgroup.card_map_of_injective (MulAut.conj s⁻¹).injective
  let f : ↥U × ↥V → ↥R :=
    fun p => ⟨(p.1 : G) * (p.2 : G), R.mul_mem (hUR p.1.2) (hVR p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨u1, v1⟩ ⟨u2, v2⟩ h
    have hG : (u1 : G) * (v1 : G) = (u2 : G) * (v2 : G) := by
      simpa [f] using congrArg Subtype.val h
    have key : (u1 : G)⁻¹ * (u2 : G) = (v1 : G) * (v2 : G)⁻¹ := by
      calc (u1 : G)⁻¹ * (u2 : G)
          = (u1 : G)⁻¹ * ((u2 : G) * (v2 : G)) * (v2 : G)⁻¹ := by group
        _ = (u1 : G)⁻¹ * ((u1 : G) * (v1 : G)) * (v2 : G)⁻¹ := by rw [← hG]
        _ = (v1 : G) * (v2 : G)⁻¹ := by group
    have hmem : (u1 : G)⁻¹ * (u2 : G) ∈ U ⊓ V :=
      ⟨U.mul_mem (U.inv_mem u1.2) u2.2,
        by rw [key]; exact V.mul_mem v1.2 (V.inv_mem v2.2)⟩
    have hone : (u1 : G)⁻¹ * (u2 : G) = 1 := by
      have h := hmem
      rw [hUV] at h
      simpa using h
    have h1 : (u1 : G) = (u2 : G) := by
      calc (u1 : G) = (u1 : G) * ((u1 : G)⁻¹ * (u2 : G)) := by rw [hone, mul_one]
        _ = (u2 : G) := by group
    have h2 : (v1 : G) = (v2 : G) := by
      have h := hG
      rw [h1] at h
      exact mul_left_cancel h
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hcard_le : Nat.card (↥U × ↥V) ≤ Nat.card ↥R := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hcard_le
  have hcardR : Nat.card ↥R = Nat.card ↥U * H.relIndex R := sec64_card_eq R H
  rw [hcardR] at hcard_le
  have hle : Nat.card ↥U * Nat.card ↥U ≤ Nat.card ↥U * H.relIndex R := by
    simpa [hcardV] using hcard_le
  have hpos : 0 < Nat.card ↥U := by
    haveI : Nonempty ↥U := ⟨1⟩
    exact Nat.card_pos
  change Nat.card ↥U ≤ H.relIndex R
  exact Nat.le_of_mul_le_mul_left hle hpos

theorem sec64_ti_not_e4 [Finite G] (hout : Asc82Outside) {T H : Subgroup G} {x y : G}
    (c : Sec64Cfg T H x y) (hcard : 4 ≤ Nat.card ↥(T ⊓ centralizer ({y} : Set G) ⊓ H))
    (hTR : ¬ T ≤ centralizer ({y} : Set G))
    (hQ : QuotEquivTo (T ⊓ centralizer ({y} : Set G)) (T ⊓ centralizer ({y} : Set G) ⊓ H)
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) : False := by
  classical
  let R : Subgroup G := T ⊓ centralizer ({y} : Set G)
  let U : Subgroup G := R ⊓ H
  obtain ⟨s, hsT, hsy⟩ := SetLike.not_le_iff_exists.mp hTR
  have hti := sec64_ti_conj hout c hcard hsT hsy
  let V : Subgroup G := CFSG.conjugate U s
  have hUV : U ⊓ V = ⊥ := hti.1
  have hVR : V ≤ R := hti.2.1
  have hle : Nat.card ↥U ≤ H.relIndex R := sec64_ti_index hout c hcard hTR
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)
  have hF : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := by
    simp [Nat.card_prod, h2]
  obtain ⟨φ, hφsurj, hφker⟩ := hQ
  have hrel4 : H.relIndex R = 4 := by
    rw [← Subgroup.inf_relIndex_left (H := R) (K := H)]
    have hker :
        ((T ⊓ centralizer ({y} : Set G) ⊓ H).subgroupOf (T ⊓ centralizer ({y} : Set G))).index =
          4 := by
      rw [← hφker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφsurj,
        Subgroup.card_top, hF]
    exact hker
  obtain ⟨g, hgU, hg2⟩ := exists_sq_ne_one_of_cyclic_card_ge_four c.hU hcard
  let b : G := s⁻¹ * g * s
  have hbV : b ∈ V := by
    change b ∈ CFSG.conjugate U s
    rw [mem_conjugate_iff']
    show s * b * s⁻¹ ∈ U
    have hsb : s * b * s⁻¹ = g := by
      change s * (s⁻¹ * g * s) * s⁻¹ = g
      group
    rw [hsb]
    exact hgU
  have hbR : b ∈ R := hVR hbV
  have hb2ne : b ^ 2 ≠ 1 := by
    intro h
    apply hg2
    have h' : g ^ 2 = s * b ^ 2 * s⁻¹ := by
      have hb : b = s⁻¹ * g * s := rfl
      rw [hb]
      simp only [pow_two]
      group
    rw [h] at h'
    simpa using h'
  have hsq : ∀ z : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), z ^ 2 = 1 := by decide
  have hker_mem : (⟨b, hbR⟩ : ↥R) ^ 2 ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hsq _
  have hb2U : b ^ 2 ∈ U := by
    have h := hker_mem
    rw [hφker] at h
    have h' := Subgroup.mem_subgroupOf.mp h
    change b ^ 2 ∈ U at h'
    exact h'
  have hb2V : b ^ 2 ∈ V := V.pow_mem hbV 2
  have hbot : b ^ 2 ∈ U ⊓ V := ⟨hb2U, hb2V⟩
  rw [hUV] at hbot
  exact hb2ne (by simpa using hbot)

end CFSG.OddStandard.SmallF3.Omega
