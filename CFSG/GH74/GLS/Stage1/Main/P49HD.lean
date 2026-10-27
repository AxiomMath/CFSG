module

public import CFSG.GH74.GLS.Stage1.Main.P49HCore
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.GLS.IVK.Defs

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.LocalAnalysis.SteinbergBK
open scoped MatrixGroups

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49H

section DLevel

variable {Y : Type} [Group Y] [Finite Y]

theorem pPrimeCore_centralizer_eq_bot {Kb : Subgroup Y} (hKn : Kb.Normal) (hO : pPrimeCore 2 Y = ⊥) :
    pPrimeCore 2 ↥(centralizer (Kb : Set Y)) = ⊥ := by
  have := hKn
  set D := centralizer (Kb : Set Y) with hD
  have : D.Normal := inferInstance
  have hnorm : ((pPrimeCore 2 ↥D).map D.subtype).Normal :=
    map_normal_of_characteristic D.subtype D.subtype_injective
      (by rw [Subgroup.range_subtype]; infer_instance)
  have hcop : Nat.Coprime 2 (Nat.card ↥((pPrimeCore 2 ↥D).map D.subtype)) := by
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact pPrimeCore_coprime_card
  have h1 := (pPrimeCore_eq_bot_iff.1 hO) _ hnorm hcop
  exact (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).1 h1

theorem not_isQuasisimple_of_comm {Q : Type} [Group Q] (h : ∀ a b : Q, a * b = b * a) :
    ¬ IsQuasisimple Q := by
  rintro ⟨-, -, a, b, hab⟩
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h a' b']

omit [Finite Y] in
theorem layer_centralizer_eq_bot {Kb : Subgroup Y} (hKn : Kb.Normal)
    (hcomp : ∀ L : Subgroup Y, IsComponent L → L ≤ Kb) :
    layer ↥(centralizer (Kb : Set Y)) = ⊥ := by
  have := hKn
  set D := centralizer (Kb : Set Y) with hD
  have : D.Normal := inferInstance
  have hempty : {K : Subgroup ↥D | IsComponent K} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun L hL => ?_
    obtain ⟨hq, hsn⟩ := hL
    have hL'q : IsQuasisimple ↥(L.map D.subtype) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (L.equivMapOfInjective D.subtype D.subtype_injective) hq
    have hL'sn : (L.map D.subtype).IsSubnormal :=
      Subgroup.IsSubnormal.trans' hsn (Subgroup.Normal.isSubnormal inferInstance)
    have hle := hcomp _ ⟨hL'q, hL'sn⟩
    refine not_isQuasisimple_of_comm (Q := ↥L) (fun a b => ?_) hq
    have ha : ((a : ↥D) : Y) ∈ Kb := hle ⟨(a : ↥D), a.2, rfl⟩
    have hb := (Subgroup.mem_centralizer_iff.1 (b : ↥D).2) _ ha
    exact Subtype.ext (Subtype.ext hb)
  simp only [CFSG.layer.eq_sSup]
  rw [hempty, sSup_empty]

theorem centralizer_pCore_le {Kb : Subgroup Y} (hKn : Kb.Normal) (hO : pPrimeCore 2 Y = ⊥)
    (hcomp : ∀ L : Subgroup Y, IsComponent L → L ≤ Kb) :
    centralizer (pCore 2 ↥(centralizer (Kb : Set Y)) : Set ↥(centralizer (Kb : Set Y))) ≤
      pCore 2 ↥(centralizer (Kb : Set Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot _ 2
    (pPrimeCore_centralizer_eq_bot hKn hO) (layer_centralizer_eq_bot hKn hcomp)

theorem exists_sylow_quaternion_centralizer {Kb : Subgroup Y} (hKn : Kb.Normal) {T : Subgroup Y}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {n : ℕ}
    (hQ : IVK.IsQuaternionTwoGroup ↥(T ⊓ centralizer (Kb : Set Y)) n) :
    ∃ S : Sylow 2 ↥(centralizer (Kb : Set Y)),
      Nonempty ((S : Subgroup ↥(centralizer (Kb : Set Y))) ≃* QuaternionGroup (2 ^ (n - 2))) := by
  have := hKn
  set D := centralizer (Kb : Set Y) with hD
  have : D.Normal := inferInstance
  have hSD : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ D) D :=
    hT.inf_of_le_normalizer le_top Subgroup.le_normalizer_of_normal
  obtain ⟨S, hS⟩ := hSD
  refine ⟨S, ⟨?_⟩⟩
  exact ((S : Subgroup ↥D).equivMapOfInjective D.subtype D.subtype_injective).trans
    ((MulEquiv.subgroupCongr hS).trans hQ.2.some)

theorem centralizer_structure {Kb : Subgroup Y} (hKn : Kb.Normal) (hO : pPrimeCore 2 Y = ⊥)
    (hcomp : ∀ L : Subgroup Y, IsComponent L → L ≤ Kb) {T : Subgroup Y}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {n : ℕ} (hn : 3 ≤ n)
    (hQ : IVK.IsQuaternionTwoGroup ↥(T ⊓ centralizer (Kb : Set Y)) n)
    (hnot : ¬ IsPGroup 2 ↥(centralizer (Kb : Set Y))) :
    ∃ (t : ↥(centralizer (Kb : Set Y))) (_ : pCore 2 ↥(centralizer (Kb : Set Y)) ≃* QuaternionGroup 2),
      orderOf t = 2 ∧ (∀ u : ↥(centralizer (Kb : Set Y)), orderOf u = 2 → u = t) ∧
      centralizer (pCore 2 ↥(centralizer (Kb : Set Y)) : Set ↥(centralizer (Kb : Set Y))) = zpowers t ∧
      (axisAction (pCore 2 ↥(centralizer (Kb : Set Y)))).ker = pCore 2 ↥(centralizer (Kb : Set Y)) ∧
      (Nat.card ↥(centralizer (Kb : Set Y)) = 24 ∨ Nat.card ↥(centralizer (Kb : Set Y)) = 48) ∧
      (Nat.card ↥(centralizer (Kb : Set Y)) = 24 →
        Nonempty (↥(centralizer (Kb : Set Y)) ≃* SL(2, ZMod 3))) := by
  obtain ⟨S, ⟨eS⟩⟩ := exists_sylow_quaternion_centralizer hKn hT hQ
  exact quaternion_witness_of_cp (pPrimeCore_centralizer_eq_bot hKn hO)
    (centralizer_pCore_le hKn hO hcomp) S hn eS hnot

end DLevel

section Axes

variable {Y : Type} [Group Y]

theorem axisAction_eq_one_of_comm {P' : Subgroup Y} [P'.Normal] {g : Y}
    (hg : ∀ x ∈ P', g * x = x * g) : axisAction P' g = 1 := by
  refine Equiv.ext fun A => Subtype.ext ?_
  rw [axisAction_apply, Equiv.Perm.coe_one, id_eq]
  have hA : (A : Subgroup Y) ≤ P' := A.2.1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := hg y (hA hy)
    have e : (MulAut.conj g).toMonoidHom y = y := by
      change g * y * g⁻¹ = y
      rw [this]; group
    rw [e]; exact hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    have := hg x (hA hx)
    change g * x * g⁻¹ = x
    rw [this]; group

theorem axisAction_eq_one_of_map {D : Subgroup Y} {P : Subgroup ↥D} [P.Normal]
    [(P.map D.subtype).Normal] {d : ↥D} (h : axisAction (P.map D.subtype) (d : Y) = 1) :
    axisAction P d = 1 := by
  refine Equiv.ext fun A => Subtype.ext ?_
  rw [axisAction_apply, Equiv.Perm.coe_one, id_eq]
  obtain ⟨hAP, hcyc, hcard⟩ := A.2
  set A' : Subgroup Y := (A : Subgroup ↥D).map D.subtype with hA'
  have hA'mem : A' ∈ cyclicOrderFourSubgroups (P.map D.subtype) := by
    refine ⟨Subgroup.map_mono hAP, ?_, ?_⟩
    · exact isCyclic_of_surjective
        ((A : Subgroup ↥D).equivMapOfInjective D.subtype D.subtype_injective).toMonoidHom
        ((A : Subgroup ↥D).equivMapOfInjective D.subtype D.subtype_injective).surjective
    · rw [hA', Subgroup.card_map_of_injective D.subtype_injective]; exact hcard
  have h1 := congrArg (fun σ : Equiv.Perm (cyclicOrderFourSubgroups (P.map D.subtype)) =>
    ((σ ⟨A', hA'mem⟩ : cyclicOrderFourSubgroups (P.map D.subtype)) : Subgroup Y)) h
  simp only [axisAction_apply, Equiv.Perm.coe_one, id_eq] at h1
  have h2 : ((A : Subgroup ↥D).map (MulAut.conj d).toMonoidHom).map D.subtype =
      A'.map (MulAut.conj (d : Y)).toMonoidHom := by
    rw [Subgroup.map_map, hA', Subgroup.map_map]
    congr 1
  apply Subgroup.map_injective D.subtype_injective
  rw [h2, h1]

theorem axisAction_sq_eq_one [Finite Y] {P' : Subgroup Y} [P'.Normal]
    (e : ↥P' ≃* QuaternionGroup 2) {s : Y} {f : ℕ} (hs : s ^ (2 ^ f) = 1) :
    (axisAction P' s) ^ 2 = 1 := by
  have h3 := card_cyclicOrderFourSubgroups e
  have hperm : Nat.card (Equiv.Perm (cyclicOrderFourSubgroups P')) = 6 := by
    rw [Nat.card_perm, h3]
    rfl
  set g := axisAction P' s with hg
  have h1 : g ^ 6 = 1 := by rw [← hperm]; exact pow_card_eq_one'
  have h2 : g ^ (2 ^ f) = 1 := by rw [hg, ← map_pow, hs, map_one]
  have h4 : g ^ (Nat.gcd 6 (2 ^ f)) = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  have hcop : Nat.Coprime (Nat.gcd 6 (2 ^ f)) 3 :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right 6 (2 ^ f)) (Nat.Coprime.pow_left f (by norm_num))
  have hdvd : Nat.gcd 6 (2 ^ f) ∣ 2 :=
    hcop.dvd_of_dvd_mul_right (by simpa using Nat.gcd_dvd_left 6 (2 ^ f))
  exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one h4).trans hdvd)

end Axes

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49H
