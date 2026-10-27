module

public import CFSG.CGT.Timmesfeld75.Sec57Basic
public import CFSG.CGT.Timmesfeld75.Sec5FiveEngHelp

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

section Alg

variable {G : Type} [Group G]

theorem card_sup_eq_mul_of_commute [Finite G] {P Q : Subgroup G}
    (hc : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (h : P ⊓ Q = ⊥) :
    Nat.card ↥(P ⊔ Q) = Nat.card P * Nat.card Q := by
  let φ : P × Q → ↥(P ⊔ Q) := fun p =>
    ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective φ := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ he
    have h1 : (p : G) * q = p' * q' := congrArg Subtype.val he
    have h2 : (p' : G)⁻¹ * p = q' * (q : G)⁻¹ := by
      calc (p' : G)⁻¹ * p = (p' : G)⁻¹ * (p * q) * (q : G)⁻¹ := by group
        _ = q' * (q : G)⁻¹ := by rw [h1]; group
    have hmem : (p' : G)⁻¹ * p ∈ P ⊓ Q :=
      ⟨P.mul_mem (P.inv_mem p'.2) p.2, by rw [h2]; exact Q.mul_mem q'.2 (Q.inv_mem q.2)⟩
    rw [h, Subgroup.mem_bot] at hmem
    have hp : p' = p := Subtype.ext (inv_mul_eq_one.1 hmem)
    have hq : q' = q := Subtype.ext (mul_inv_eq_one.1 (h2 ▸ hmem))
    rw [hp, hq]
  have hPN : P ≤ Subgroup.normalizer (Q : Set G) := fun p hp => by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hz : ∀ q ∈ Q, p * q * p⁻¹ = q := fun q hq => by rw [hc p hp q hq]; group
    constructor
    · intro hzQ
      rw [hz z hzQ]
      exact hzQ
    · intro hzQ
      have h5 : p⁻¹ * (p * z * p⁻¹) * p = p * z * p⁻¹ := by
        have := hc p⁻¹ (P.inv_mem hp) _ hzQ
        calc p⁻¹ * (p * z * p⁻¹) * p = ((p * z * p⁻¹) * p⁻¹) * p := by rw [← this]
          _ = p * z * p⁻¹ := by group
      have e : z = p * z * p⁻¹ := by
        calc z = p⁻¹ * (p * z * p⁻¹) * p := by group
          _ = p * z * p⁻¹ := h5
      rw [e]
      exact hzQ
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ ((P : Set G) * (Q : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right P Q hPN]
      exact hz
    obtain ⟨p, hp, q, hq, rfl⟩ := hz'
    exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm

end Alg

section SecA

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem secA_le_secR₁ (hP : MaxPair T T₁) (hS : Sec3Global T) (hI : Sec3IsoGlobal T) :
    secA T T₁ ≤ secR₁ T T₁ := by
  obtain ⟨x₀, hx₀⟩ := hP.conj
  have hsec3 := hP.sec3 hS
  have hx₀ne : conjSubgroup x₀ T ≠ T := by rw [← hx₀]; exact hP.ne
  have hL₁ne : normIn (conjSubgroup x₀ T) T ≠ ⊥ := by rw [← hx₀]; exact hsec3.cfg.ne₁
  have hx₀u : IsUIdx T T₁ x₀ := isUIdx_of_conj hP hS hx₀
  have hA₁R : conjSubgroup x₀ (secA T T₁) ≤ secR₁ T T₁ := by
    unfold secR₁
    exact le_iSup₂ (f := fun (h : G) (_ : IsUIdx T T₁ h) => conjSubgroup h (secA T T₁)) x₀ hx₀u
  have hA₁L : conjSubgroup x₀ (secA T T₁) ≤ normIn T₁ T := by
    have := conjSubgroup_secA_le_normIn hP hS hx₀ne hL₁ne
    rwa [← hx₀] at this
  obtain ⟨t, htT, htL⟩ : ∃ t ∈ T, t ∉ normIn T T₁ := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show T ≤ normIn T T₁ from hcon)
    have h2 := two_mul_card_normIn_le_of_maxPair hP
    have h3 : 0 < Nat.card ↥(normIn T T₁) := Nat.card_pos
    omega
  have htM : t ∉ cfgM T T₁ := fun hM => htL (by
    rw [← hsec3.cfg.inf_cfgM]
    exact ⟨htT, hM⟩)
  have hcomm := commutator_conj_secA_le_of_ne hP hS hI hx₀ne hL₁ne
  let χ : conjSubgroup x₀ (secA T T₁) → secA T T₁ := fun w =>
    ⟨⁅(w : G), t⁆, hcomm w w.2 t htT⟩
  have hinj : Function.Injective χ := by
    intro w w' he
    have h1 : ⁅(w : G), t⁆ = ⁅(w' : G), t⁆ := congrArg Subtype.val he
    have hm : (w' : G)⁻¹ * w ∈ conjSubgroup x₀ (secA T T₁) :=
      (conjSubgroup x₀ (secA T T₁)).mul_mem ((conjSubgroup x₀ (secA T T₁)).inv_mem w'.2) w.2
    have hcm : (w' : G)⁻¹ * w ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [commutatorElement_def, commutatorElement_def] at h1
      calc (w' : G)⁻¹ * w * t = (w' : G)⁻¹ * (w * t * (w : G)⁻¹ * t⁻¹) * t * w := by group
        _ = (w' : G)⁻¹ * (w' * t * (w' : G)⁻¹ * t⁻¹) * t * w := by rw [h1]
        _ = t * ((w' : G)⁻¹ * w) := by group
    have hmM : (w' : G)⁻¹ * w ∈ cfgM T T₁ :=
      Cfg.normIn_le_cfgM_right T T₁ (hA₁L hm)
    have hmL : (w' : G)⁻¹ * w ∈ normIn T T₁ := by
      rw [← hsec3.cfg.cfgM_inf_centralizer htT htM]
      exact ⟨hmM, hcm⟩
    have hmT₁ : (w' : G)⁻¹ * w ∈ T₁ := normIn_le _ _ (hA₁L hm)
    have hm1 : (w' : G)⁻¹ * w ∈ T ⊓ T₁ := ⟨normIn_le _ _ hmL, hmT₁⟩
    rw [hsec3.cfg.inf, Subgroup.mem_bot] at hm1
    exact Subtype.ext (inv_mul_eq_one.1 hm1).symm
  have hcard : Nat.card (secA T T₁) ≤ Nat.card (conjSubgroup x₀ (secA T T₁)) := by
    rw [card_conjSubgroup]
  have hbij := hinj.bijective_of_nat_card_le hcard
  intro u hu
  obtain ⟨w, hw⟩ := hbij.2 ⟨u, hu⟩
  have hwu : ⁅(w : G), t⁆ = u := congrArg Subtype.val hw
  have htN : t ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer htT
  have hw' : t * (w : G) * t⁻¹ ∈ secR₁ T T₁ := by
    have := conj_mem_conjSubgroup t (hA₁R w.2)
    rwa [conjSubgroup_secR₁ htN] at this
  have e : u = (w : G) * (t * (w : G) * t⁻¹)⁻¹ := by
    rw [← hwu, commutatorElement_def]
    group
  rw [e]
  exact (secR₁ T T₁).mul_mem (hA₁R w.2) ((secR₁ T T₁).inv_mem hw')

end SecA

end CFSG.CGT.Timmesfeld75
