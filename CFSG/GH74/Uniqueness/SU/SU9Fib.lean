module

public import CFSG.GH74.Uniqueness.SU.SU9Cnt

public section

namespace CFSG.GH74.Uniqueness.SU.SU9

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.Uniqueness.SU.SU7
  CFSG CFSG.ShultStronglyClosedTI.InvolutionCounting

namespace Cnt

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem not_z_mem_zpowers_of_mem_U (hc : Ctx19 S U M V x z A B R) {v w : G} (hvU : v ∈ U)
    (hwT : w ∈ Tsub S U) (hwU : w ∉ U) (hw2 : w * w = 1) : z ∉ zpowers (v * w) := by
  intro h
  have hvv : v * v = 1 := Cfg.U_sq hc v hvU
  have hvw : v * w = w * v := Cfg.U_central hc v hvU w hwT
  have hsq : (v * w) * (v * w) = 1 := by
    calc v * w * (v * w) = v * (w * v) * w := by group
      _ = v * (v * w) * w := by rw [← hvw]
      _ = (v * v) * (w * w) := by group
      _ = 1 := by rw [hvv, hw2]; group
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
  rcases zpow_cases hsq k with h1 | h1
  · exact Cfg.z_ne_one hc (hk.symm.trans h1)
  · have hzvw : z = v * w := hk.symm.trans h1
    apply hwU
    have : w = v * z := by
      calc w = v * (v * w) := by rw [← mul_assoc, hvv, one_mul]
        _ = v * z := by rw [← hzvw]
    rw [this]
    exact U.mul_mem hvU hc.c19.z_mem

theorem fiber_S (h191 : Lemma191Stmt) (h192 : Lemma192Stmt) (h194 : Lemma194Stmt)
    (hc : Ctx19 S U M V x z A B R) {a : G} (hd : Data S U z A B a) {w : G}
    (hwAB : w ∈ A ∨ w ∈ B) (hwU : w ∉ U) :
    {v : G | IsConj z v ∧ z ∈ zpowers (v * w)} =
      {s : G | s ∈ (S : Subgroup G) ∧ s ∉ Tsub S U ∧ s ^ 2 = 1} := by
  have hwT : w ∈ Tsub S U := by
    rcases hwAB with h | h
    · exact hc.c19.A_le h
    · exact hc.c19.B_le h
  have hwS : w ∈ (S : Subgroup G) := Cfg.T_le_S hwT
  have hww : w * w = 1 := by
    rcases hwAB with h | h
    · exact Cfg.A_sq hc w h
    · exact Cfg.B_sq hc w h
  have haw : IsConj a w := (hd.class_a w hwS).2 ⟨hwAB, hwU⟩
  have haa : a * a = 1 := Cfg.A_sq hc a hd.ha
  have hzz : z * z = 1 := Cfg.z_sq hc
  ext v
  constructor
  · rintro ⟨hzv, hzvw⟩
    have hp : (v, w) ∈ thompsonPairs z a z := ⟨hzv, haw, hzvw⟩
    have hvC : v ∈ centralizer ({z} : Set G) :=
      (mem_centralizer_of_mem_thompsonPairs hzz haa hzz hp).1
    have hvR : v ∈ R := mem_R_of_isConj_z h191 h192 h194 hc hd hvC hzv
    have hvS : v ∈ (S : Subgroup G) := hc.c19.R_le hvR
    have hv2 : orderOf v = 2 := orderOf_of_isConj_z hc hzv
    refine ⟨hvS, ?_, by have := pow_orderOf_eq_one v; rwa [hv2] at this⟩
    intro hvT
    rcases (isConj_z_iff h191 hc hd hvS hv2).1 hzv with h | h
    · exact not_z_mem_zpowers_of_mem_U hc h hwT hwU hww hzvw
    · exact h hvT
  · rintro ⟨hvS, hvT, hv2⟩
    have hv1 : v ≠ 1 := fun h => hvT (h ▸ (Tsub S U).one_mem)
    have hvo : orderOf v = 2 := orderOf_eq_prime hv2 hv1
    have hvv : v * v = 1 := by rw [← pow_two]; exact hv2
    exact ⟨(isConj_z_iff h191 hc hd hvS hvo).2 (Or.inr hvT),
      z_mem_zpowers_mul hc hvS hvT hvv hwAB hwU hww⟩

omit [Finite G] in
theorem fiber_conj {c v w : G} (hcz : c * z * c⁻¹ = z)
    (h : IsConj z v ∧ z ∈ zpowers (v * w)) :
    IsConj z (c * v * c⁻¹) ∧ z ∈ zpowers ((c * v * c⁻¹) * (c * w * c⁻¹)) := by
  refine ⟨h.1.trans (isConj_iff.2 ⟨c, rfl⟩), ?_⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h.2
  refine mem_zpowers_iff.2 ⟨k, ?_⟩
  have e : (c * v * c⁻¹) * (c * w * c⁻¹) = c * (v * w) * c⁻¹ := by group
  rw [e, conj_zpow, hk, hcz]

theorem card_fiber (h191 : Lemma191Stmt) (h192 : Lemma192Stmt) (h194 : Lemma194Stmt)
    (hc : Ctx19 S U M V x z A B R) {a : G} (hd : Data S U z A B a) {w : G}
    (hwC : w ∈ centralizer ({z} : Set G)) (haw : IsConj a w) :
    Set.ncard {v : G | IsConj z v ∧ z ∈ zpowers (v * w)} = 8 := by
  have hSC : (S : Subgroup G) ≤ centralizer ({z} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.2 (hc.conf.z_center s hs)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : a * a = 1 := Cfg.A_sq hc a hd.ha
  have hw2 : orderOf w = 2 := by
    obtain ⟨c, hc'⟩ := isConj_iff.1 haw
    rw [← hc', Cfg.orderOf_conj']
    exact orderOf_eq_prime (by rw [pow_two]; exact haa) (fun h => hd.haU (h ▸ U.one_mem))
  have hww : w ^ (2 ^ 1) = 1 := by
    rw [pow_one]; have := pow_orderOf_eq_one w; rwa [hw2] at this
  obtain ⟨c, hcC, hcS⟩ := CFSG.LyonsUnitaryFour.exists_conj_mem_sylow_of_le S hSC hwC ⟨1, hww⟩
  have hcz : c * z * c⁻¹ = z := by
    have := mem_centralizer_singleton_iff.1 hcC
    rw [this]; group
  set w' := c * w * c⁻¹ with hw'
  have haw' : IsConj a w' := haw.trans (isConj_iff.2 ⟨c, rfl⟩)
  obtain ⟨hw'AB, hw'U⟩ := (hd.class_a w' hcS).1 haw'
  have hfib := fiber_S h191 h192 h194 hc hd hw'AB hw'U
  have himg : {v : G | IsConj z v ∧ z ∈ zpowers (v * w')} =
      (fun v => c * v * c⁻¹) '' {v : G | IsConj z v ∧ z ∈ zpowers (v * w)} := by
    ext v'
    constructor
    · intro hv'
      have hcz' : c⁻¹ * z * c⁻¹⁻¹ = z := by
        calc c⁻¹ * z * c⁻¹⁻¹ = c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ := by rw [hcz]
          _ = z := by group
      have h2 := fiber_conj hcz' hv'
      refine ⟨c⁻¹ * v' * c⁻¹⁻¹, ?_, by group⟩
      have e : c⁻¹ * w' * c⁻¹⁻¹ = w := by rw [hw']; group
      rw [e] at h2
      exact h2
    · rintro ⟨v, hv, rfl⟩
      exact fiber_conj hcz hv
  have hinj : Function.Injective (fun v : G => c * v * c⁻¹) := fun v v' h => by
    simpa using h
  rw [← Set.ncard_image_of_injective _ hinj, ← himg, hfib]
  exact (Cfg.j2 hc).card_invol

end Cnt

end CFSG.GH74.Uniqueness.SU.SU9
