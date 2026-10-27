module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5N18Aut
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5N18Fin
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5N18SC
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5KStruct
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Dich16

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalAnalysis.EvenBN.Tits.N CFSG.LocalAnalysis.EvenBN.Tits.N.P4

section Setup

variable {X : Type*} [Group X] [Finite X] {U : Subgroup X} {x v t : X}

theorem n18_mem_normalizer_of_conj_mem {Q : Subgroup X} {g : X} (h : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) :
    g ∈ normalizer (Q : Set X) := by
  have hle : Q.map (MulAut.conj g).toMonoidHom ≤ Q := by
    rintro _ ⟨q, hq, rfl⟩
    exact h q hq
  have heq : Q.map (MulAut.conj g).toMonoidHom = Q :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

theorem n18_normalizes_U0 (htt : t * t = 1) (htU : ∀ u ∈ U, t * u = u * t) {p : X}
    (hpU : p ∈ normalizer (U : Set X)) (hpt : p * t = t * p) :
    p ∈ normalizer ((U ⊔ zpowers t : Subgroup X) : Set X) := by
  refine n18_mem_normalizer_of_conj_mem fun y hy => ?_
  rw [mem_sup_zpowers_iff_of_comm_invol htt htU] at hy ⊢
  have hpU' : ∀ u ∈ U, p * u * p⁻¹ ∈ U := fun u hu => (Subgroup.mem_normalizer_iff.1 hpU u).1 hu
  rcases hy with hy | hy
  · exact Or.inl (hpU' y hy)
  · refine Or.inr ?_
    have e : t * (p * y * p⁻¹) = p * (t * y) * p⁻¹ := by
      calc t * (p * y * p⁻¹) = (t * p) * y * p⁻¹ := by group
        _ = (p * t) * y * p⁻¹ := by rw [hpt]
        _ = p * (t * y) * p⁻¹ := by group
    rw [e]
    exact hpU' _ hy

theorem n18_isElemAbelian (hF : IsF20 U x v) : IsElemAbelian 2 U :=
  ⟨⟨⟨fun a b => Subtype.ext (hF.comm a a.2 b b.2)⟩⟩, fun a ha => by
    rw [pow_two]
    exact hF.sq a ha⟩

theorem n18_U0_data (hF : IsF20 U x v) (htt : t * t = 1) (htU : ∀ u ∈ U, t * u = u * t)
    (htnU : t ∉ U) :
    IsElemAbelian 2 (U ⊔ zpowers t) ∧ Nat.card ↥(U ⊔ zpowers t : Subgroup X) = 32 := by
  refine ⟨?_, card_U0 hF htt htU htnU⟩
  refine IsElemAbelian.sup_of_commute (n18_isElemAbelian hF)
    (isElemAbelian_zpowers (by rw [pow_two]; exact htt)) ?_
  rintro a ha b ⟨n, rfl⟩
  exact (Commute.zpow_right (show Commute a t from (htU a ha).symm) n).eq

theorem n18_Pgrp_le_normalizer (hF : IsF20 U x v) :
    IsF20.Pgrp U x v ≤ normalizer (U : Set X) :=
  sup_le Subgroup.le_normalizer
    (sup_le (Subgroup.zpowers_le.2 hF.x_norm) (Subgroup.zpowers_le.2 hF.v_norm))

theorem n18_Pgrp_le_K (hF : IsF20 U x v) (htt : t * t = 1) (htU : ∀ u ∈ U, t * u = u * t)
    (hcomm : ∀ p ∈ IsF20.Pgrp U x v, t * p = p * t) :
    IsF20.Pgrp U x v ≤ normalizer ((U ⊔ zpowers t : Subgroup X) : Set X) :=
  fun _ hp => n18_normalizes_U0 htt htU (n18_Pgrp_le_normalizer hF hp) (hcomm _ hp).symm

theorem n18_mem_K_of_conj (hF : IsF20 U x v) (htt : t * t = 1) (htnU : t ∉ U)
    (hcomm : ∀ p ∈ IsF20.Pgrp U x v, t * p = p * t) (hinf : zpowers t ⊓ IsF20.Pgrp U x v = ⊥)
    (hCt : ∀ g : X, g * t = t * g → g ∈ zpowers t ⊔ IsF20.Pgrp U x v) {u g : X} (hu : u ∈ U)
    (hg : g * t * g⁻¹ = t * u) : g ∈ normalizer ((U ⊔ zpowers t : Subgroup X) : Set X) := by
  have htU : ∀ u ∈ U, t * u = u * t := fun u hu => hcomm u (IsF20.U_le_Pgrp U x v hu)
  obtain ⟨hab, hcard⟩ := n18_U0_data hF htt htU htnU
  have htU0 : t ∈ U ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hua : t * u ∈ U ⊔ zpowers t := mul_mem htU0 (mem_sup_left hu)
  have hDC : (U ⊔ zpowers t : Subgroup X).map (MulAut.conj g⁻¹).toMonoidHom ≤
      zpowers t ⊔ IsF20.Pgrp U x v := by
    rintro _ ⟨y, hy, rfl⟩
    apply hCt
    have hya : y * (t * u) = (t * u) * y := hab.comm hy hua
    show g⁻¹ * y * g⁻¹⁻¹ * t = t * (g⁻¹ * y * g⁻¹⁻¹)
    calc g⁻¹ * y * g⁻¹⁻¹ * t = g⁻¹ * (y * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (y * (t * u)) * g := by rw [hg]
      _ = g⁻¹ * ((t * u) * y) * g := by rw [hya]
      _ = g⁻¹ * ((g * t * g⁻¹) * y) * g := by rw [hg]
      _ = t * (g⁻¹ * y * g⁻¹⁻¹) := by group
  have hDab : IsElemAbelian 2 ((U ⊔ zpowers t : Subgroup X).map (MulAut.conj g⁻¹).toMonoidHom) :=
    hab.map _
  have hDcard : Nat.card ↥((U ⊔ zpowers t : Subgroup X).map (MulAut.conj g⁻¹).toMonoidHom) = 32 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  have hZP : ∀ a ∈ zpowers t, ∀ p ∈ IsF20.Pgrp U x v, a * p = p * a := by
    intro a ha p hp
    obtain ⟨n, rfl⟩ := ha
    exact (Commute.zpow_left (show Commute t p from hcomm p hp) n).eq
  have h2 : Nat.card ↥(zpowers t) = 2 := card_zpowers_invol htt htnU
  obtain ⟨hle, heq⟩ := IsF20.card_elemAb_le_sup hF hZP hinf hDC
    (fun a ha b hb => hDab.comm ha hb) (fun a ha => hDab.mul_self_eq_one ha)
  rw [h2] at hle heq
  have hDU0 : (U ⊔ zpowers t : Subgroup X).map (MulAut.conj g⁻¹).toMonoidHom = U ⊔ zpowers t := by
    rw [heq (by rw [hDcard])]
    exact sup_comm _ _
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  constructor
  · intro hy
    have h1 : g⁻¹ * y * g ∈ (U ⊔ zpowers t : Subgroup X).map (MulAut.conj g⁻¹).toMonoidHom :=
      ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rw [hDU0] at h1
    exact h1
  · intro hy
    have h1 : g⁻¹ * y * g ∈ (U ⊔ zpowers t : Subgroup X).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [hDU0]
      exact hy
    obtain ⟨u', hu', hux⟩ := h1
    have : u' = y := by
      have h2 : g⁻¹ * u' * g = g⁻¹ * y * g := by simpa [MulAut.conj_apply] using hux
      simpa using h2
    rw [← this]
    exact hu'

theorem n18_exists_ne_one (hU : Nat.card U = 16) : ∃ u ∈ U, u ≠ 1 := by
  by_contra h
  push Not at h
  have : Nat.card U = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩, ⟨1⟩⟩
  omega

end Setup

section Main


theorem delta_surj (hTop : TopStatement) {X : Type} [Group X] [Finite X] {U : Subgroup X}
    {x v t : X} (rk : X → ℕ) (hF : IsF20 U x v) (htt : t * t = 1) (htnU : t ∉ U)
    (hcomm : ∀ p ∈ IsF20.Pgrp U x v, t * p = p * t) (hinf : zpowers t ⊓ IsF20.Pgrp U x v = ⊥)
    (hCt : ∀ g : X, g * t = t * g → g ∈ zpowers t ⊔ IsF20.Pgrp U x v)
    (hnotU : ∀ g : X, g * t * g⁻¹ ∉ U) (h66 : ∃ u ∈ U, u ≠ 1 ∧ ∃ g : X, g * t * g⁻¹ = t * u)
    (h67 : ∃ w g : X, w ∈ normalizer (U : Set X) ∧ w * t = t * w ∧ w * x * w⁻¹ = x⁻¹ ∧
      g * t * g⁻¹ = t * w)
    (hrk_conj : ∀ g y : X, rk (g * y * g⁻¹) = rk y) (hrk3 : ∃ u ∈ U, u ≠ 1 ∧ rk u ≤ 8)
    (hrk4 : ∀ y g : X, y * y = 1 → y * (g * x * g⁻¹) * y⁻¹ = (g * x * g⁻¹)⁻¹ → 16 ≤ rk y) :
    ∀ u ∈ U, ∃ g : X, g * t * g⁻¹ = t * u := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨u₀, hu₀U, hu₀⟩ := hcon
  have htU : ∀ u ∈ U, t * u = u * t := fun u hu => hcomm u (IsF20.U_le_Pgrp U x v hu)
  have htx : t * x = x * t := hcomm x (mem_sup_right (mem_sup_left (mem_zpowers x)))
  have htv : t * v = v * t := hcomm v (mem_sup_right (mem_sup_right (mem_zpowers v)))
  obtain ⟨hU0ab, hU0card⟩ := n18_U0_data hF htt htU htnU
  have htU0 : t ∈ U ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have htK : t ∈ normalizer ((U ⊔ zpowers t : Subgroup X) : Set X) :=
    Subgroup.le_normalizer htU0
  have hCK : zpowers t ⊔ IsF20.Pgrp U x v ≤ normalizer ((U ⊔ zpowers t : Subgroup X) : Set X) :=
    sup_le (Subgroup.zpowers_le.2 htK) (n18_Pgrp_le_K hF htt htU hcomm)
  have hΔ : ∀ k ∈ normalizer ((U ⊔ zpowers t : Subgroup X) : Set X), ∃ u ∈ U,
      k * t * k⁻¹ = t * u := by
    intro k hk
    have hkt : k * t * k⁻¹ ∈ U ⊔ zpowers t := (Subgroup.mem_normalizer_iff.1 hk t).1 htU0
    rcases (mem_sup_zpowers_iff_of_comm_invol htt htU).1 hkt with h | h
    · exact absurd h (hnotU k)
    · refine ⟨t * (k * t * k⁻¹), h, ?_⟩
      rw [← mul_assoc, htt, one_mul]
  have hne : ∃ u ∈ U, ∀ k ∈ normalizer ((U ⊔ zpowers t : Subgroup X) : Set X),
      k * t * k⁻¹ ≠ t * u := ⟨u₀, hu₀U, fun k _ => hu₀ k⟩
  have h7 : ∃ u ∈ U, u ≠ 1 ∧ ∃ k ∈ normalizer ((U ⊔ zpowers t : Subgroup X) : Set X),
      k * t * k⁻¹ = t * u := by
    obtain ⟨u, hu, hu1, g, hg⟩ := h66
    exact ⟨u, hu, hu1, g, n18_mem_K_of_conj hF htt htnU hcomm hinf hCt hu hg, hg⟩
  obtain ⟨hKU, hmax, hcommK, hklein, h5, htrans⟩ :=
    kstruct (K := normalizer ((U ⊔ zpowers t : Subgroup X) : Set X)) hF htt htnU htU htx htv hCK
      le_rfl (fun k _ hk => hCt k hk) hΔ hne h7
  have hKF : KFacts (normalizer ((U ⊔ zpowers t : Subgroup X) : Set X)) U x t rk :=
    { htt := htt, htnU := htnU, htU := htU, hU0ab := hU0ab, hU0card := hU0card,
      hNK := fun _ => Iff.rfl, hUK := hKU, hmax := hmax, hcomm := hcommK, hklein := hklein,
      htrans := htrans, hrk_conj := hrk_conj, hrk3 := hrk3, hrk4 := hrk4 }
  obtain ⟨S, hUS, hSK, hcl⟩ := strong_closure hKF
  have hUab := n18_isElemAbelian hF
  have hKN : normalizer ((U ⊔ zpowers t : Subgroup X) : Set X) ≤ normalizer (U : Set X) :=
    fun k hk => n18_mem_normalizer_of_conj_mem (hKU k hk)
  have hxK : x ∈ normalizer ((U ⊔ zpowers t : Subgroup X) : Set X) :=
    hCK (mem_sup_right (mem_sup_right (mem_sup_left (mem_zpowers x))))
  rcases Gold.layer_dichotomy16 hTop S hUS hUab hF.card hcl hF.x_norm hF.x5 hF.fpf with
    hbot | ⟨B₀, hB₀, hBn, hodd, htr⟩
  · have hN := (Gold.normal_of_layer_bot hTop S hUS hUab.1 hcl hbot).2.2
    obtain ⟨w, g, hwN, hwt, hwx, hg⟩ := h67
    exact contra_of_normal (goldschmidtOddCore_normal X)
      (SStarTransport.odd_card_goldschmidtOddCore X) hUab hN (n18_exists_ne_one hF.card) htU hwt
      (fun u hu => (Subgroup.mem_normalizer_iff.1 hwN u).1 hu)
      (fun u hu => (Subgroup.mem_normalizer_iff.1 hF.x_norm u).1 hu) hF.x5 hF.fpf hwx hg
  · exact no_odd_normal hUab hF.card hF.x_norm hF.x5 hF.fpf hKN hxK h5 hB₀ hBn hodd htr

end Main

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
