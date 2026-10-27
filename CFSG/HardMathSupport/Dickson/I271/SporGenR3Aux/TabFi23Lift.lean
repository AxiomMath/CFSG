module

public import CFSG.Sporadic.Fi23.Centralizer
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiLocal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiTransp
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.Blueprint.Fischer
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

local notation "J22" => CFSG.Sporadic.Fi22.J

theorem cen_iff {G : Type*} [Group G] {t u : G} (h : u ∈ Subgroup.centralizer ({t} : Set G)) :
    u * t = t * u := Subgroup.mem_centralizer_singleton_iff.1 h

theorem cen_iff' {G : Type*} [Group G] {t u : G} (h : u * t = t * u) :
    u ∈ Subgroup.centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 h

theorem cen_mem_iff {G : Type*} [Group G] {t u : G} :
    u ∈ Subgroup.centralizer ({t} : Set G) ↔ u * t = t * u :=
  Subgroup.mem_centralizer_singleton_iff

section Lift


theorem mul_dCd_comm (y : Cd) : y * dCd = dCd * y := Subtype.ext (mem_Cd.1 y.2)

theorem dCd_mul_self : dCd * dCd = 1 := by
  have h := pow_orderOf_eq_one dCd
  rwa [orderOf_dCd, sq] at h

theorem dCd_ne_one : dCd ≠ 1 := by
  intro h
  have := orderOf_dCd
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem rho_eq_one_iff (c : Cd) : rho c = 1 ↔ c = 1 ∨ c = dCd := by
  have h : c ∈ rho.ker ↔ c ∈ Subgroup.zpowers dCd := by rw [ker_rho]
  rw [MonoidHom.mem_ker] at h
  rw [h]
  exact ⟨fun hc => eq_one_or_eq_of_mem_zpowers dCd_mul_self hc, by
    rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _⟩

theorem comm_of_rho_conj {y c : Cd} (hy : y * y * y = 1) (h : rho (c * y * c⁻¹) = rho y) :
    c * y = y * c := by
  have h1 : rho (c * y * c⁻¹ * y⁻¹) = 1 := by rw [map_mul, h, map_inv, mul_inv_cancel]
  rcases (rho_eq_one_iff _).1 h1 with h2 | h2
  · have h4 : c * y * c⁻¹ = y := mul_inv_eq_one.1 h2
    calc c * y = (c * y * c⁻¹) * c := by group
      _ = y * c := by rw [h4]
  · exfalso
    have h3 : c * y * c⁻¹ = dCd * y := by
      calc c * y * c⁻¹ = (c * y * c⁻¹ * y⁻¹) * y := by group
        _ = dCd * y := by rw [h2]
    exact dCd_ne_one (eq_one_of_conj_eq_mul (mul_dCd_comm y).symm dCd_mul_self hy h3)

theorem map_centralizer_cd (y : Cd) :
    (Subgroup.centralizer ({y} : Set Cd)).map Cd.subtype =
      Subgroup.centralizer ({(y : J)} : Set J) ⊓ Cd := by
  ext z
  rw [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h1 := cen_iff hw
    have h2 : ((w * y : Cd) : J) = ((y * w : Cd) : J) := by rw [h1]
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
    exact ⟨cen_iff' h2, w.2⟩
  · rintro ⟨hz, hzC⟩
    have h1 := cen_iff hz
    have h2 : (⟨z, hzC⟩ : Cd) * y = y * ⟨z, hzC⟩ := Subtype.ext h1
    exact ⟨⟨z, hzC⟩, cen_iff' h2, rfl⟩

theorem card_centralizer_lift {y : Cd} (hy : y * y * y = 1) {t : J22} (ht : pi22 t = rho y) :
    Nat.card ↥(Subgroup.centralizer ({y} : Set Cd)) =
      2 * Nat.card ↥(Subgroup.centralizer ({t} : Set J22)) := by
  set S : Subgroup Cd := Subgroup.centralizer ({y} : Set Cd) with hS
  let ψ : ↥S →* Equiv.Perm (Fin 3510) := rho.comp S.subtype
  have hdS : dCd ∈ S := cen_iff' (mul_dCd_comm y).symm
  have hker : ψ.ker = Subgroup.zpowers (⟨dCd, hdS⟩ : ↥S) := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_zpowers_iff]
    constructor
    · intro hc
      have hc' : rho (c : Cd) = 1 := hc
      rcases (rho_eq_one_iff _).1 hc' with h | h
      · exact ⟨0, by apply Subtype.ext; simpa using h.symm⟩
      · exact ⟨1, by apply Subtype.ext; simpa using h.symm⟩
    · rintro ⟨k, rfl⟩
      show rho (((⟨dCd, hdS⟩ : ↥S) ^ k : ↥S) : Cd) = 1
      rw [Subgroup.coe_zpow, map_zpow]
      show rho dCd ^ k = 1
      rw [rho_dCd, one_zpow]
  have hcardker : Nat.card ψ.ker = 2 := by
    rw [hker, Nat.card_zpowers]
    have : orderOf (⟨dCd, hdS⟩ : ↥S) = orderOf dCd :=
      (orderOf_injective S.subtype S.subtype_injective ⟨dCd, hdS⟩).symm
    rw [this, orderOf_dCd]
  have hrange : ψ.range = (Subgroup.centralizer ({t} : Set J22)).map pi22 := by
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      have hcy : (c : Cd) * y = y * c := by
        have h := cen_iff c.2
        exact h
      have hr : rho (c : Cd) ∈ pi22.range := by rw [← range_rho]; exact ⟨c, rfl⟩
      obtain ⟨u, hu⟩ := hr
      refine ⟨u, cen_iff' ?_, hu⟩
      apply pi22_injective
      rw [map_mul, map_mul, hu, ht, ← map_mul, ← map_mul, hcy]
    · rintro ⟨u, hu, rfl⟩
      have hr : pi22 u ∈ rho.range := by rw [range_rho]; exact ⟨u, rfl⟩
      obtain ⟨c, hc⟩ := hr
      have hut : u * t = t * u := by
        have h := cen_iff hu
        exact h
      have hcy : c * y = y * c := by
        refine comm_of_rho_conj hy ?_
        rw [map_mul, map_mul, map_inv, hc, ← ht, ← map_mul, hut, map_mul, mul_inv_cancel_right]
      exact ⟨⟨c, cen_iff' hcy⟩, hc⟩
  have h1 : Nat.card ↥S = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  rw [h1, hcardker, hrange, Subgroup.card_map_of_injective pi22_injective, mul_comm]

@[expose] def conjEquiv {G : Type*} [Group G] (h : G) : G ≃ G where
  toFun g := h⁻¹ * g * h
  invFun g := h * g * h⁻¹
  left_inv g := by group
  right_inv g := by group

theorem conj_comm_iff {G : Type*} [Group G] (h a b : G) :
    (h⁻¹ * a * h) * (h⁻¹ * b * h) = (h⁻¹ * b * h) * (h⁻¹ * a * h) ↔ a * b = b * a := by
  have e1 : (h⁻¹ * a * h) * (h⁻¹ * b * h) = h⁻¹ * (a * b) * h := by group
  have e2 : (h⁻¹ * b * h) * (h⁻¹ * a * h) = h⁻¹ * (b * a) * h := by group
  rw [e1, e2]
  constructor
  · intro H
    exact mul_left_cancel (mul_right_cancel H)
  · intro H
    rw [H]

theorem conj_comm_iff' {G : Type*} [Group G] (h a b : G) :
    (h * a * h⁻¹) * (h * b * h⁻¹) = (h * b * h⁻¹) * (h * a * h⁻¹) ↔ a * b = b * a := by
  have e1 : (h * a * h⁻¹) * (h * b * h⁻¹) = h * (a * b) * h⁻¹ := by group
  have e2 : (h * b * h⁻¹) * (h * a * h⁻¹) = h * (b * a) * h⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro H
    exact mul_left_cancel (mul_right_cancel H)
  · intro H
    rw [H]

theorem conj_eq_iff {G : Type*} [Group G] (h a b : G) : h * a * h⁻¹ = h * b * h⁻¹ ↔ a = b := by
  constructor
  · intro H
    exact mul_left_cancel (mul_right_cancel H)
  · intro H
    rw [H]

theorem rho_fix_iff (y : Cd) (u : Fin 3510) :
    rho y u = u ↔ (y : J) * ((ptE u : star) : J) = ((ptE u : star) : J) * (y : J) := by
  rw [rho_apply, Equiv.symm_apply_eq]
  constructor
  · intro h
    have h2 := congrArg Subtype.val h
    rw [starAction_val] at h2
    calc (y : J) * ((ptE u : star) : J)
        = ((y : J) * ((ptE u : star) : J) * (y : J)⁻¹) * (y : J) := by group
      _ = ((ptE u : star) : J) * (y : J) := by rw [h2]
  · intro h
    apply Subtype.ext
    rw [starAction_val]
    calc (y : J) * ((ptE u : star) : J) * (y : J)⁻¹
        = (((ptE u : star) : J) * (y : J)) * (y : J)⁻¹ := by rw [h]
      _ = ((ptE u : star) : J) := by group

theorem card_fix_rho (y : Cd) :
    Nat.card {u : Fin 3510 // rho y u = u} =
      Nat.card {z : J // z ∈ star ∧ (y : J) * z = z * (y : J)} := by
  refine Nat.card_congr
    { toFun := fun u => ⟨((ptE u.1 : star) : J), (ptE u.1).2, (rho_fix_iff y u.1).1 u.2⟩
      invFun := fun z => ⟨ptE.symm ⟨z.1, z.2.1⟩, ?_⟩
      left_inv := fun u => ?_
      right_inv := fun z => ?_ }
  · rw [rho_fix_iff, Equiv.apply_symm_apply]
    exact z.2.2
  · apply Subtype.ext
    simp
  · apply Subtype.ext
    simp

theorem exists_lift (y : Cd) (hy : orderOf y = 3) :
    ∃ t : J22, orderOf t = 3 ∧ pi22 t = rho y ∧
      Nat.card ↥(Subgroup.centralizer ({(y : J)} : Set J) ⊓ Cd) =
        2 * Nat.card ↥(Subgroup.centralizer ({t} : Set J22)) := by
  have hy3 : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy] at this
  have hy3' : y * y * y = 1 := by rw [← pow_three']; exact hy3
  obtain ⟨t, ht⟩ : rho y ∈ pi22.range := by rw [← range_rho]; exact ⟨y, rfl⟩
  refine ⟨t, ?_, ht, ?_⟩
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · apply pi22_injective
      rw [map_pow, ht, ← map_pow, hy3, map_one, map_one]
    · intro h
      rw [h, map_one] at ht
      rcases (rho_eq_one_iff y).1 ht.symm with h1 | h1
      · rw [h1, orderOf_one] at hy
        exact absurd hy (by norm_num)
      · rw [h1, orderOf_dCd] at hy
        exact absurd hy (by norm_num)
  · have h1 := card_centralizer_lift hy3' ht
    rw [← map_centralizer_cd, Subgroup.card_map_of_injective Cd.subtype_injective]
    exact h1

theorem exists_lift_conj {x e : J} (he : e ∈ D23) (hx : orderOf x = 3) (hxe : x * e = e * x) :
    ∃ t : J22, orderOf t = 3 ∧
      Nat.card ↥(Subgroup.centralizer ({x} : Set J) ⊓ Subgroup.centralizer ({e} : Set J)) =
        2 * Nat.card ↥(Subgroup.centralizer ({t} : Set J22)) ∧
      Nat.card {u : Fin 3510 // pi22 t u = u} =
        Nat.card {z : J // z ∈ D23 ∧ z ≠ e ∧ z * e = e * z ∧ z * x = x * z} := by
  obtain ⟨h, hh⟩ := isConj_iff.1 he
  obtain ⟨x', hx'⟩ : ∃ x' : J, x' = h⁻¹ * x * h := ⟨_, rfl⟩
  have hd : d = h⁻¹ * e * h := by rw [← hh]; group
  have hxx : x = h * x' * h⁻¹ := by rw [hx']; group
  have hx'd : x' * d = d * x' := by
    rw [hx', hd]
    exact (conj_comm_iff h x e).2 hxe
  let y : Cd := ⟨x', mem_Cd.2 hx'd⟩
  have hyo : orderOf y = 3 := by
    rw [← orderOf_injective Cd.subtype Subtype.val_injective y]
    show orderOf x' = 3
    have := orderOf_conj h⁻¹ x
    rw [inv_inv, ← hx'] at this
    rw [this]
    exact hx
  obtain ⟨t, ht3, hty, hcard⟩ := exists_lift y hyo
  refine ⟨t, ht3, ?_, ?_⟩
  · rw [← hcard]
    refine Nat.card_congr (Equiv.subtypeEquiv (conjEquiv h) fun g => ?_)
    have e1 := cen_mem_iff (G := J) (t := x) (u := g)
    have e2 := cen_mem_iff (G := J) (t := e) (u := g)
    have e3 := cen_mem_iff (G := J) (t := x') (u := h⁻¹ * g * h)
    have e5 : (h⁻¹ * g * h) ∈ Cd ↔ (h⁻¹ * g * h) * d = d * (h⁻¹ * g * h) := mem_Cd
    have f1 := conj_comm_iff h g x
    have f2 := conj_comm_iff h g e
    rw [← hx'] at f1
    rw [← hd] at f2
    show (g ∈ Subgroup.centralizer ({x} : Set J) ⊓ Subgroup.centralizer ({e} : Set J)) ↔
      (h⁻¹ * g * h ∈ Subgroup.centralizer ({x'} : Set J) ⊓ Cd)
    rw [Subgroup.mem_inf, Subgroup.mem_inf, e1, e2, e5, e3, f1, f2]
  · rw [hty, card_fix_rho y]
    refine Nat.card_congr (Equiv.subtypeEquiv (conjEquiv h).symm fun z => ?_)
    show (z ∈ star ∧ x' * z = z * x') ↔
      ((h * z * h⁻¹) ∈ D23 ∧ h * z * h⁻¹ ≠ e ∧ (h * z * h⁻¹) * e = e * (h * z * h⁻¹) ∧
        (h * z * h⁻¹) * x = x * (h * z * h⁻¹))
    have hconj : IsConj z (h * z * h⁻¹) := isConj_iff.2 ⟨h, rfl⟩
    have hee : e = h * d * h⁻¹ := hh.symm
    have g1 := conj_comm_iff' h z d
    have g2 := conj_comm_iff' h z x'
    have g3 := conj_eq_iff h z d
    rw [← hee] at g1 g3
    rw [← hxx] at g2
    have hD : z ∈ D23 ↔ (h * z * h⁻¹) ∈ D23 :=
      ⟨fun hz => IsConj.trans hz hconj, fun hz => IsConj.trans hz hconj.symm⟩
    show ((z ∈ D23 ∧ z ≠ d ∧ z * d = d * z) ∧ x' * z = z * x') ↔ _
    rw [hD, ne_eq, ne_eq, g3, g1, g2]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, h2, h3, h4.symm⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2, h3⟩, h4.symm⟩

end Lift

end CFSG.HardMathSupport.Dickson.I271.TabFi23
