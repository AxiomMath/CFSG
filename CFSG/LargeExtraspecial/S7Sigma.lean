module

public import CFSG.LargeExtraspecial.S7Perm
public import CFSG.LargeExtraspecial.S4SevenA

public section

namespace CFSG.LargeExtraspecial.S7

open Subgroup Equiv
open scoped Pointwise

variable {X : Type*} [Group X] [Finite X] {M D : Subgroup X} {t : X}

section Sigma

variable (hDM : D ≤ M) (hD3 : Nat.card D = 3) (hconj : ∀ x ∈ M, ∀ y ∈ D, x * y * x⁻¹ ∈ D)
  (htM : t ∈ M) (htt : t * t = 1) (ht1 : t ≠ 1) (hcomm : ∀ x ∈ M, x * t * x⁻¹ * t⁻¹ ∈ D)
  (hnc : ∃ x ∈ M, x * t * x⁻¹ ≠ t)

omit [Finite X] in
include hD3 in
theorem eq_one_of_mem_of_mul_self {c : X} (hc : c ∈ D) (hcc : c * c = 1) : c = 1 := by
  have h1 : orderOf (⟨c, hc⟩ : D) ∣ 3 := hD3 ▸ orderOf_dvd_natCard _
  have h2 : orderOf (⟨c, hc⟩ : D) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [pow_two]; exact hcc))
  have h3 : orderOf (⟨c, hc⟩ : D) = 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [show Nat.gcd 3 2 = 1 by norm_num, Nat.dvd_one] at this
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h3)

omit [Finite X] in
include hD3 htt hcomm hnc in
theorem exists_not_comm_t : ∃ y ∈ D, t * y ≠ y * t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, hxt⟩ := hnc
  apply hxt
  obtain ⟨c, hc⟩ : ∃ c, c = x * t * x⁻¹ * t⁻¹ := ⟨_, rfl⟩
  have hcD : c ∈ D := hc ▸ hcomm x hx
  have hu : x * t * x⁻¹ = c * t := by rw [hc]; group
  have huu : x * t * x⁻¹ * (x * t * x⁻¹) = 1 := by
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  have hcc : c * c = 1 := by
    have e : c * t * (c * t) = c * c * (t * t) := by
      calc c * t * (c * t) = c * (t * c) * t := by group
        _ = c * (c * t) * t := by rw [hcon c hcD]
        _ = c * c * (t * t) := by group
    rw [← hu, huu, htt, mul_one] at e
    exact e.symm
  rw [hu, eq_one_of_mem_of_mul_self hD3 hcD hcc, one_mul]

include hconj htM in
theorem zpowers_le_normalizer : zpowers t ≤ normalizer (D : Set X) :=
  zpowers_le.mpr (S4.mem_normalizer_of_conj_le fun y hy => hconj t htM y hy)

omit [Finite X] in
theorem card_zpowers_of_mul_self (htt : t * t = 1) (ht1 : t ≠ 1) : Nat.card (zpowers t) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact htt) ht1

include hD3 hconj htM htt ht1 in
theorem card_sigma : Nat.card (D ⊔ zpowers t : Subgroup X) = 6 := by
  have h2 := card_zpowers_of_mul_self htt ht1
  have hset : ((D ⊔ zpowers t : Subgroup X) : Set X) = (zpowers t : Set X) * (D : Set X) := by
    rw [sup_comm]
    exact coe_mul_of_left_le_normalizer_right _ _ (zpowers_le_normalizer hconj htM)
  have hle : Nat.card (D ⊔ zpowers t : Subgroup X) ≤ 6 := by
    have := Set.natCard_mul_le (s := (zpowers t : Set X)) (t := (D : Set X))
    rw [← hset] at this
    calc Nat.card (D ⊔ zpowers t : Subgroup X)
        ≤ Nat.card (zpowers t : Set X) * Nat.card (D : Set X) := this
      _ = 6 := by
        change Nat.card (zpowers t) * Nat.card D = 6
        rw [h2, hD3]
  have h3 : 3 ∣ Nat.card (D ⊔ zpowers t : Subgroup X) := hD3 ▸ card_dvd_of_le le_sup_left
  have h2' : 2 ∣ Nat.card (D ⊔ zpowers t : Subgroup X) := h2 ▸ card_dvd_of_le le_sup_right
  have hpos : 0 < Nat.card (D ⊔ zpowers t : Subgroup X) := Nat.card_pos
  have h6 : 6 ∣ Nat.card (D ⊔ zpowers t : Subgroup X) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h2'
  obtain ⟨k, hk⟩ := h6
  rcases k with _ | _ | k
  · omega
  · omega
  · nlinarith

include hD3 hconj htM htt ht1 hcomm hnc in
theorem nonempty_sigma_mulEquiv : Nonempty ((D ⊔ zpowers t : Subgroup X) ≃* Perm (Fin 3)) := by
  have htS : t ∈ D ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  refine nonempty_mulEquiv_perm_three (card_sigma hD3 hconj htM htt ht1)
    (T := (zpowers t).subgroupOf (D ⊔ zpowers t)) ?_ ?_
  · rw [Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : zpowers t ≤ D ⊔ zpowers t)).toEquiv]
    exact card_zpowers_of_mul_self htt ht1
  · intro hT
    obtain ⟨y, hyD, hyt⟩ := exists_not_comm_t hD3 htt hcomm hnc
    apply hyt
    have hyS : y ∈ D ⊔ zpowers t := mem_sup_left hyD
    have h1 := hT.conj_mem ⟨t, htS⟩ (mem_subgroupOf.mpr (mem_zpowers t)) ⟨y, hyS⟩
    rw [mem_subgroupOf] at h1
    have h2 : y * t * y⁻¹ ∈ zpowers t := h1
    rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp h2 with h | h
    · exfalso
      apply ht1
      have := congrArg (fun z => y⁻¹ * z * y) h
      simpa [mul_assoc] using this
    · calc t * y = y * t * y⁻¹ * y := by rw [h]
        _ = y * t := by group

omit [Finite X] in
include hDM htM in
theorem sigma_le : D ⊔ zpowers t ≤ M := sup_le hDM (zpowers_le.mpr htM)

include hD3 hconj htM htt ht1 hcomm hnc in
theorem sigma_inf_cent :
    (D ⊔ zpowers t) ⊓ (M ⊓ centralizer ((D ⊔ zpowers t : Subgroup X) : Set X)) = ⊥ := by
  obtain ⟨φ⟩ := nonempty_sigma_mulEquiv hD3 hconj htM htt ht1 hcomm hnc
  rw [eq_bot_iff]
  rintro s ⟨hsS, -, hsC⟩
  rw [mem_bot]
  have h1 : φ ⟨s, hsS⟩ = 1 := perm_three_eq_one_of_comm _ fun τ => by
    obtain ⟨y, rfl⟩ := φ.surjective τ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp hsC y y.2).symm
  have h2 := φ.injective (h1.trans (map_one φ).symm)
  exact congrArg Subtype.val h2

include hDM hD3 hconj htM htt ht1 hcomm hnc in
theorem exists_sigma_mul_cent {x : X} (hx : x ∈ M) :
    ∃ s ∈ D ⊔ zpowers t, ∃ c ∈ M ⊓ centralizer ((D ⊔ zpowers t : Subgroup X) : Set X),
      x = s * c := by
  obtain ⟨φ⟩ := nonempty_sigma_mulEquiv hD3 hconj htM htt ht1 hcomm hnc
  set Sg := D ⊔ zpowers t with hSg
  have hxS : ∀ y ∈ Sg, x * y * x⁻¹ ∈ Sg := by
    have hle : Sg ≤ Sg.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun y hy => mem_sup_left (hconj x hx y hy)) (zpowers_le.mpr ?_)
      change x * t * x⁻¹ ∈ Sg
      have e : x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
      rw [e]
      exact mul_mem (mem_sup_left (hcomm x hx)) (mem_sup_right (mem_zpowers t))
    exact fun y hy => hle hy
  let κ : Sg →* Sg :=
    ((MulAut.conj x).toMonoidHom.comp Sg.subtype).codRestrict Sg fun y => hxS y y.2
  have hκ : ∀ y : Sg, ((κ y : Sg) : X) = x * y * x⁻¹ := fun y => rfl
  have hκinj : Function.Injective κ := by
    intro y z h
    have h1 : x * (y : X) * x⁻¹ = x * z * x⁻¹ := by rw [← hκ, ← hκ, h]
    exact Subtype.ext (by simpa using h1)
  let f : Perm (Fin 3) →* Perm (Fin 3) := φ.toMonoidHom.comp (κ.comp φ.symm.toMonoidHom)
  have hf : Function.Injective f := φ.injective.comp (hκinj.comp φ.symm.injective)
  obtain ⟨τ, hτ⟩ := perm_three_exists_conj f hf
  set s : Sg := φ.symm τ with hs
  refine ⟨s, s.2, (s : X)⁻¹ * x,
    Subgroup.mem_inf.mpr ⟨M.mul_mem (M.inv_mem (sigma_le hDM htM s.2)) hx, ?_⟩, by group⟩
  rw [mem_centralizer_iff]
  intro y hy
  have h1 : κ ⟨y, hy⟩ = s * ⟨y, hy⟩ * s⁻¹ := by
    apply φ.injective
    have := hτ (φ ⟨y, hy⟩)
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      at this
    rw [this, map_mul, map_mul, map_inv, hs, MulEquiv.apply_symm_apply]
  have h2 : x * y * x⁻¹ = s * y * (s : X)⁻¹ := by
    have := congrArg Subtype.val h1
    rw [hκ] at this
    simpa using this
  calc y * ((s : X)⁻¹ * x) = (s : X)⁻¹ * (s * y * (s : X)⁻¹) * x := by group
    _ = (s : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h2]
    _ = (s : X)⁻¹ * x * y := by group

include hDM hD3 hconj htM htt ht1 hcomm hnc in
theorem nonempty_mulEquiv_sigma_prod :
    Nonempty (M ≃* Perm (Fin 3) × (M ⊓ centralizer ((D ⊔ zpowers t : Subgroup X) : Set X) :
      Subgroup X)) := by
  obtain ⟨φ⟩ := nonempty_sigma_mulEquiv hD3 hconj htM htt ht1 hcomm hnc
  obtain ⟨e⟩ := nonempty_mulEquiv_prod (sigma_le hDM htM) inf_le_left
    (fun s hs c hc => (mem_centralizer_iff.mp hc.2 s hs))
    (sigma_inf_cent hD3 hconj htM htt ht1 hcomm hnc)
    (fun x hx => exists_sigma_mul_cent hDM hD3 hconj htM htt ht1 hcomm hnc hx)
  exact ⟨e.trans (MulEquiv.prodCongr φ (MulEquiv.refl _))⟩

include hDM hD3 hconj htM htt ht1 hcomm hnc in
theorem mem_cent_of_comm_t {x : X} (hx : x ∈ M) (hxt : x * t = t * x) :
    x ∈ M ⊓ centralizer ((D ⊔ zpowers t : Subgroup X) : Set X) ∨
      t * x ∈ M ⊓ centralizer ((D ⊔ zpowers t : Subgroup X) : Set X) := by
  obtain ⟨φ⟩ := nonempty_sigma_mulEquiv hD3 hconj htM htt ht1 hcomm hnc
  obtain ⟨s, hs, c, hc, rfl⟩ := exists_sigma_mul_cent hDM hD3 hconj htM htt ht1 hcomm hnc hx
  have htS : t ∈ D ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hct : t * c = c * t := mem_centralizer_iff.mp hc.2 t htS
  have hst : s * t = t * s := by
    have e : s * c * t = t * (s * c) := hxt
    have e2 : s * t * c = t * s * c := by
      calc s * t * c = s * (t * c) := by group
        _ = s * (c * t) := by rw [hct]
        _ = s * c * t := by group
        _ = t * (s * c) := e
        _ = t * s * c := by group
    exact mul_right_cancel e2
  have hφ : φ ⟨s, hs⟩ * φ ⟨t, htS⟩ = φ ⟨t, htS⟩ * φ ⟨s, hs⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hst
  have htt' : φ ⟨t, htS⟩ * φ ⟨t, htS⟩ = 1 := by
    rw [← map_mul, ← map_one φ]
    congr 1
    exact Subtype.ext htt
  have ht1' : φ ⟨t, htS⟩ ≠ 1 := fun h =>
    ht1 (congrArg Subtype.val (φ.injective (h.trans (map_one φ).symm)))
  rcases perm_three_eq_of_comm_inv _ _ htt' ht1' hφ with h | h
  · left
    have : s = 1 := congrArg Subtype.val (φ.injective (h.trans (map_one φ).symm))
    rw [this, one_mul]
    exact hc
  · right
    have : s = t := congrArg Subtype.val (φ.injective h)
    rw [this, ← mul_assoc, htt, one_mul]
    exact hc

end Sigma

end CFSG.LargeExtraspecial.S7
