module

public import CFSG.GH74.GLS.C3.Layer2.L5B11
public import CFSG.GH74.GLS.C3.Layer2.L5B12

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

section Mg1

variable {h : IsAConfig 5 x K T Q S a} {c : Coord5 h}

theorem psi_X0b
    (hc : Case47 h c) {ψ : ↥S →* Perm (Fin 9)}
    (hψT : ∀ (t : G) (ht : t ∈ T), ψ ⟨t, h.T_lt_S.le ht⟩ = emb 5 (c.rco t))
    (hψnT : ∀ (s : G) (hs : s ∈ S), s ∉ T → ∀ m ∈ T5, ψ ⟨s, hs⟩ ≠ emb 5 m) {s : G} (hs : s ∈ S)
    (hX : X0b (ψ ⟨s, hs⟩) = true) : IsConj s x := by
  obtain ⟨p, hp, hp1, hpe⟩ := X0b_iff.1 hX
  have hpT5 : p ∈ T5 := by
    rcases List.mem_append.1 hp with hP | hQ
    · exact Pm_le_T5 (mem_Pm.2 hP)
    · exact Qm_le_T5 (mem_Qm.2 hQ)
  have hsT : s ∈ T := by
    by_contra hsT
    exact hψnT s hs hsT p hpT5 hpe.symm
  have hrco : c.rco s = p := emb_injective 5 ((hψT s hsT).symm.trans hpe.symm)
  have hs1 : s ≠ 1 := by
    intro e
    apply hp1
    rw [← hrco, e, Coord5.rco_one]
  rcases List.mem_append.1 hp with hP | hQ
  · have hsP : s ∈ T ⊓ K := by
      rw [Coord5.P_eq_lift (c := c)]
      exact (Coord5.mem_lift_rco c).2 ⟨h.T_le_C hsT, by rw [hrco]; exact mem_Pm.2 hP⟩
    exact isConj_x_of_PQ hc (Or.inl hsP) hs1
  · have hsQ : s ∈ Q := by
      rw [Coord5.Q_eq_lift (c := c)]
      exact (Coord5.mem_lift_rco c).2 ⟨h.T_le_C hsT, by rw [hrco]; exact mem_Qm.2 hQ⟩
    exact isConj_x_of_PQ hc (Or.inr hsQ) hs1

theorem Mg1
    (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hc : Case47 h c)
    (haa : a * a = 1) {t : G} (ht : t ∈ T) (htR : t ∉ c.lift Rm) (htt : t * t = 1) :
    IsConj t x := by
  by_contra hnx
  have hTS : T ≤ S := h.T_lt_S.le
  have haS : a ∈ S := h.a_mem.1
  have haT : a ∉ T := h.a_mem.2.2.1
  have hvT := L4.v_mem_T h
  have hvS : L4.vElt x a ∈ S := hTS hvT
  have hvsq := L4.v_mul_self h
  have hv1 := L4.v_ne_one h
  have haR : a * a ∈ c.lift Rm := by rw [haa]; exact one_mem _
  have ht1 : t ≠ 1 := fun e => htR (e ▸ (c.lift Rm).one_mem)
  have htv : IsConj t (L4.vElt x a) :=
    (invol_conj_x_or_v hsimple hnab hc haa t htt ht1).resolve_left hnx
  have hJv : ∀ t' ∈ T, t' ∉ c.lift Rm → t' * t' = 1 → IsConj t' (L4.vElt x a) := by
    intro t' ht' ht'R ht'2
    obtain ⟨r, _, hr⟩ := JR_conj_G c ht htR htt ht' ht'R ht'2
    exact (isConj_iff.2 ⟨r, hr⟩ : IsConj t t').symm.trans htv
  obtain ⟨ψ, hinj, hS0, -, hψT, hψnT⟩ := exists_psi hc haR
  have hAsq : ψ ⟨a, haS⟩ * ψ ⟨a, haS⟩ = 1 := by
    rw [← map_mul]
    have : (⟨a, haS⟩ : ↥S) * ⟨a, haS⟩ = 1 := Subtype.ext haa
    rw [this, map_one]
  obtain ⟨t₀, ht₀, hAeq⟩ : ∃ t₀ ∈ T5, ψ ⟨a, haS⟩ = emb 5 t₀ * a0perm 5 := by
    rcases mem_S0.1 (hS0 ⟨a, haS⟩) with hA | hA
    · exfalso
      obtain ⟨m, hm, hme⟩ := mem_R5.1 hA
      exact hψnT a haS haT m hm hme.symm
    · obtain ⟨m, hm, hme⟩ := mem_R5.1 hA
      refine ⟨m, hm, ?_⟩
      calc ψ ⟨a, haS⟩ = ψ ⟨a, haS⟩ * a0perm 5 * a0perm 5 := by rw [mul_assoc, a0_sq, mul_one]
        _ = emb 5 m * a0perm 5 := by rw [← hme]
  obtain ⟨mY, hmY, mE, hmE, hY2, hYR, hEmix, hYA, hEA, hYE⟩ :=
    exists_yE ht₀ (by rw [← hAeq]; exact hAsq)
  obtain ⟨y, hyT, hry⟩ := c.exists_T_rco hmY
  obtain ⟨e, heR, hre⟩ := Coord5.exists_lift_rco c Rm_le_Fgrp hmE
  have heT : e ∈ T := Coord5.Rg_le_T (c := c) heR
  have hyS : y ∈ S := hTS hyT
  have heS : e ∈ S := hTS heT
  have hyy : y * y = 1 := by
    apply c.rco_T_inj (T.mul_mem hyT hyT) T.one_mem
    rw [c.rco_T_mul hyT hyT, hry, hY2, Coord5.rco_one]
  have hyR : y ∉ c.lift Rm := fun hh => hYR (by rw [← hry]; exact Coord5.rco_mem c hh)
  have hee : e * e = 1 := R_sq_G c heR
  have hψy : ψ ⟨y, hyS⟩ = emb 5 mY := by rw [hψT y hyT, hry]
  have hψe : ψ ⟨e, heS⟩ = emb 5 mE := by rw [hψT e heT, hre]
  have hψv : ψ ⟨L4.vElt x a, hvS⟩ = vS0 := by
    rw [hψT _ hvT, Coord5.rco_v hc, map_mul]
    rfl
  have hay : a * y = y * a := by
    have : (⟨a, haS⟩ : ↥S) * ⟨y, hyS⟩ = ⟨y, hyS⟩ * ⟨a, haS⟩ := by
      apply hinj
      rw [map_mul, map_mul, hψy, hAeq]
      exact hYA.symm
    exact congrArg Subtype.val this
  have hae : a * e = e * a := by
    have : (⟨a, haS⟩ : ↥S) * ⟨e, heS⟩ = ⟨e, heS⟩ * ⟨a, haS⟩ := by
      apply hinj
      rw [map_mul, map_mul, hψe, hAeq]
      exact hEA.symm
    exact congrArg Subtype.val this
  have hyev : (y * e) * (y * e) = L4.vElt x a := by
    have : (⟨y, hyS⟩ * ⟨e, heS⟩ : ↥S) * (⟨y, hyS⟩ * ⟨e, heS⟩) = ⟨L4.vElt x a, hvS⟩ := by
      apply hinj
      simp only [map_mul, hψy, hψe, hψv]
      have := hYE
      rw [pow_two] at this
      exact this
    exact congrArg Subtype.val this
  have hyv : IsConj y (L4.vElt x a) := hJv y hyT hyR hyy
  have hMe : Mixm (c.rco e) := by rw [hre]; exact hEmix
  have hev : IsConj e (L4.vElt x a) := isConj_v_of_Mixm hc heT hMe
  have hayinv : (a * y) * (a * y) = 1 := by
    calc (a * y) * (a * y) = a * (y * a) * y := by group
      _ = a * (a * y) * y := by rw [hay]
      _ = (a * a) * (y * y) := by group
      _ = 1 := by rw [haa, hyy, one_mul]
  have haeinv : (a * e) * (a * e) = 1 := by
    calc (a * e) * (a * e) = a * (e * a) * e := by group
      _ = a * (a * e) * e := by rw [hae]
      _ = (a * a) * (e * e) := by group
      _ = 1 := by rw [haa, hee, one_mul]
  have hayS : a * y ∈ S := S.mul_mem haS hyS
  have haeS : a * e ∈ S := S.mul_mem haS heS
  have hayT : a * y ∉ T := fun hh => haT (by
    have := T.mul_mem hh (T.inv_mem hyT)
    simpa using this)
  have haeT : a * e ∉ T := fun hh => haT (by
    have := T.mul_mem hh (T.inv_mem heT)
    simpa using this)
  have hayv : IsConj (a * y) (L4.vElt x a) := Mg2 hsimple hnab hc haa hayS hayT hayinv
  have haev : IsConj (a * e) (L4.vElt x a) := Mg2 hsimple hnab hc haa haeS haeT haeinv
  have hav : IsConj a (L4.vElt x a) := Mg2 hsimple hnab hc haa haS haT haa
  obtain ⟨g, hg1, hg2⟩ := scp_v hc hav
  have hy'S : g * y * g⁻¹ ∈ S := hg2 y hyS hay.symm
  have he'S : g * e * g⁻¹ ∈ S := hg2 e heS hae.symm
  have hvy : L4.vElt x a * (g * y * g⁻¹) = g * (a * y) * g⁻¹ := by
    rw [← hg1]; group
  have hve : L4.vElt x a * (g * e * g⁻¹) = g * (a * e) * g⁻¹ := by
    rw [← hg1]; group
  have hvyS : L4.vElt x a * (g * y * g⁻¹) ∈ S := S.mul_mem hvS hy'S
  have hveS : L4.vElt x a * (g * e * g⁻¹) ∈ S := S.mul_mem hvS he'S
  have hy'y' : (g * y * g⁻¹) * (g * y * g⁻¹) = 1 := by
    calc (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [hyy]; group
  have he'e' : (g * e * g⁻¹) * (g * e * g⁻¹) = 1 := by
    calc (g * e * g⁻¹) * (g * e * g⁻¹) = g * (e * e) * g⁻¹ := by group
      _ = 1 := by rw [hee]; group
  have hm : ((g * y * g⁻¹) * (g * e * g⁻¹)) * ((g * y * g⁻¹) * (g * e * g⁻¹)) =
      g * L4.vElt x a * g⁻¹ := by
    calc ((g * y * g⁻¹) * (g * e * g⁻¹)) * ((g * y * g⁻¹) * (g * e * g⁻¹))
        = g * ((y * e) * (y * e)) * g⁻¹ := by group
      _ = g * L4.vElt x a * g⁻¹ := by rw [hyev]
  have hmS : g * L4.vElt x a * g⁻¹ ∈ S := by
    rw [← hm]
    exact S.mul_mem (S.mul_mem hy'S he'S) (S.mul_mem hy'S he'S)
  set Y : Perm (Fin 9) := ψ ⟨g * y * g⁻¹, hy'S⟩ with hY
  set E : Perm (Fin 9) := ψ ⟨g * e * g⁻¹, he'S⟩ with hE
  have hYE2 : (Y * E) ^ 2 = ψ ⟨g * L4.vElt x a * g⁻¹, hmS⟩ := by
    rw [pow_two, hY, hE, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hm
  have hmne : (⟨g * L4.vElt x a * g⁻¹, hmS⟩ : ↥S) ≠ 1 := by
    intro e'
    apply hv1
    have := congrArg Subtype.val e'
    simp only [Subgroup.coe_one] at this
    calc L4.vElt x a = g⁻¹ * (g * L4.vElt x a * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group
  have hmv : (⟨g * L4.vElt x a * g⁻¹, hmS⟩ : ↥S) ≠ ⟨L4.vElt x a, hvS⟩ := by
    intro e'
    have h1 := congrArg Subtype.val e'
    simp only at h1
    have h2 : g * L4.vElt x a * g⁻¹ = g * a * g⁻¹ := by rw [h1, hg1]
    have h3 : L4.vElt x a = a := mul_left_cancel (mul_right_cancel h2)
    exact haT (h3 ▸ hvT)
  have hY2' : Y * Y = 1 := by
    rw [hY, ← map_mul]
    have : (⟨g * y * g⁻¹, hy'S⟩ : ↥S) * ⟨g * y * g⁻¹, hy'S⟩ = 1 := Subtype.ext hy'y'
    rw [this, map_one]
  have hE2' : E * E = 1 := by
    rw [hE, ← map_mul]
    have : (⟨g * e * g⁻¹, he'S⟩ : ↥S) * ⟨g * e * g⁻¹, he'S⟩ = 1 := Subtype.ext he'e'
    rw [this, map_one]
  have h4 : (Y * E) ^ 4 = 1 := by
    have : (Y * E) ^ 4 = ((Y * E) ^ 2) * ((Y * E) ^ 2) := by group
    rw [this, hYE2, ← map_mul]
    have : (⟨g * L4.vElt x a * g⁻¹, hmS⟩ : ↥S) * ⟨g * L4.vElt x a * g⁻¹, hmS⟩ = 1 := by
      apply Subtype.ext
      calc g * L4.vElt x a * g⁻¹ * (g * L4.vElt x a * g⁻¹) = g * (L4.vElt x a * L4.vElt x a) * g⁻¹ := by
            group
        _ = 1 := by rw [hvsq]; group
    rw [this, map_one]
  have h2 : (Y * E) ^ 2 ≠ 1 := by
    rw [hYE2]
    intro e'
    exact hmne (hinj (e'.trans (map_one ψ).symm))
  have hv : (Y * E) ^ 2 ≠ vS0 := by
    rw [hYE2, ← hψv]
    intro e'
    exact hmv (hinj e')
  rcases mg1_cert (hS0 _) (hS0 _) hY2' hE2' h4 h2 hv with hX | hX | hX | hX
  ·
    have := psi_X0b hc hψT hψnT hy'S hX
    exact x_not_conj_v hc (this.symm.trans ((isConj_conj g y).symm.trans hyv))
  ·
    have hX' : X0b (ψ ⟨L4.vElt x a * (g * y * g⁻¹), hvyS⟩) = true := by
      rw [show (⟨L4.vElt x a * (g * y * g⁻¹), hvyS⟩ : ↥S) =
          ⟨L4.vElt x a, hvS⟩ * ⟨g * y * g⁻¹, hy'S⟩ from rfl, map_mul, hψv]
      exact hX
    have := psi_X0b hc hψT hψnT hvyS hX'
    rw [hvy] at this
    exact x_not_conj_v hc (this.symm.trans ((isConj_conj g (a * y)).symm.trans hayv))
  ·
    have := psi_X0b hc hψT hψnT he'S hX
    exact x_not_conj_v hc (this.symm.trans ((isConj_conj g e).symm.trans hev))
  ·
    have hX' : X0b (ψ ⟨L4.vElt x a * (g * e * g⁻¹), hveS⟩) = true := by
      rw [show (⟨L4.vElt x a * (g * e * g⁻¹), hveS⟩ : ↥S) =
          ⟨L4.vElt x a, hvS⟩ * ⟨g * e * g⁻¹, he'S⟩ from rfl, map_mul, hψv]
      exact hX
    have := psi_X0b hc hψT hψnT hveS hX'
    rw [hve] at this
    exact x_not_conj_v hc (this.symm.trans ((isConj_conj g (a * e)).symm.trans haev))

end Mg1

end CFSG.GH74.GLS.C3.Layer2.L5
