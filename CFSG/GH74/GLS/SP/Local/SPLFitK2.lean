module

public import CFSG.GH74.GLS.SP.Local.SPLCt0

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section FitK2

theorem fitK2_le_pPrimeCoreOf {H : Type*} [Group H] {X W : Subgroup H}
    (hWX : W ≤ X) (hnorm : ∀ c ∈ X, ∀ w ∈ W, c * w * c⁻¹ ∈ W) (hodd : Odd (Nat.card ↥W)) :
    W ≤ pPrimeCoreOf 2 X := by
  have hN : (W.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  have hodd' : Odd (Nat.card ↥(W.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv]
    exact hodd
  have hle : W.subgroupOf X ≤ pPrimeCore 2 ↥X :=
    le_sSup ⟨hN, Nat.coprime_two_left.mpr hodd'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hWX]
  exact Subgroup.map_mono hle

theorem fitK2_side₂ {G : Type} [Group G] {t : G} (htt : t * t = 1) {K₁ K₂ : Subgroup G}
    (hK₁ : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₂) (hK₂ : ∀ x ∈ K₂, t * x * t⁻¹ ∈ K₁) {y : G}
    (hy : ∃ k ∈ K₁, ∀ x ∈ K₁, (t * y * t⁻¹) * x * (t * y * t⁻¹)⁻¹ = k * x * k⁻¹) :
    ∃ k₂ ∈ K₂, ∀ x ∈ K₂, y * x * y⁻¹ = k₂ * x * k₂⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨k', hk', hk'x⟩ := hy
  refine ⟨t * k' * t⁻¹, hK₁ k' hk', fun x hx => ?_⟩
  have h1 := hk'x _ (hK₂ x hx)
  calc y * x * y⁻¹
      = t⁻¹ * ((t * y * t⁻¹) * (t * x * t⁻¹) * (t * y * t⁻¹)⁻¹) * t := by group
    _ = t⁻¹ * (k' * (t * x * t⁻¹) * k'⁻¹) * t := by rw [h1]
    _ = (t⁻¹ * k' * t) * x * (t⁻¹ * k' * t)⁻¹ := by group
    _ = (t * k' * t⁻¹) * x * (t * k' * t⁻¹)⁻¹ := by rw [htinv]

theorem fitK2_cen {G : Type} [Group G] {K₁ K₂ : Subgroup G}
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) {y k k₂ : G} (hk : k ∈ K₁) (hk₂ : k₂ ∈ K₂)
    (h₁ : ∀ x ∈ K₁, y * x * y⁻¹ = k * x * k⁻¹) (h₂ : ∀ x ∈ K₂, y * x * y⁻¹ = k₂ * x * k₂⁻¹) :
    ∀ x ∈ K₁ ⊔ K₂, ((k * k₂)⁻¹ * y) * x = x * ((k * k₂)⁻¹ * y) := by
  have hX : K₁ ⊔ K₂ ≤ centralizer ({(k * k₂)⁻¹ * y} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_centralizer_singleton_iff]
      have e1 : y * x = k * x * k⁻¹ * y := by
        calc y * x = (y * x * y⁻¹) * y := by group
          _ = (k * x * k⁻¹) * y := by rw [h₁ x hx]
      have e2 : k₂⁻¹ * x = x * k₂⁻¹ := by
        have h := hcomm x hx k₂ hk₂
        calc k₂⁻¹ * x = k₂⁻¹ * (x * k₂) * k₂⁻¹ := by group
          _ = k₂⁻¹ * (k₂ * x) * k₂⁻¹ := by rw [h]
          _ = x * k₂⁻¹ := by group
      calc x * ((k * k₂)⁻¹ * y) = (x * k₂⁻¹) * (k⁻¹ * y) := by group
        _ = (k₂⁻¹ * x) * (k⁻¹ * y) := by rw [e2]
        _ = k₂⁻¹ * k⁻¹ * (k * x * k⁻¹ * y) := by group
        _ = k₂⁻¹ * k⁻¹ * (y * x) := by rw [e1]
        _ = ((k * k₂)⁻¹ * y) * x := by group
    · rw [mem_centralizer_singleton_iff]
      have e1 : y * x = k₂ * x * k₂⁻¹ * y := by
        calc y * x = (y * x * y⁻¹) * y := by group
          _ = (k₂ * x * k₂⁻¹) * y := by rw [h₂ x hx]
      have hw : k₂ * x * k₂⁻¹ ∈ K₂ := K₂.mul_mem (K₂.mul_mem hk₂ hx) (K₂.inv_mem hk₂)
      have e2 : k⁻¹ * (k₂ * x * k₂⁻¹) = (k₂ * x * k₂⁻¹) * k⁻¹ := by
        have h := hcomm k hk _ hw
        calc k⁻¹ * (k₂ * x * k₂⁻¹) = k⁻¹ * ((k₂ * x * k₂⁻¹) * k) * k⁻¹ := by group
          _ = k⁻¹ * (k * (k₂ * x * k₂⁻¹)) * k⁻¹ := by rw [h]
          _ = (k₂ * x * k₂⁻¹) * k⁻¹ := by group
      calc x * ((k * k₂)⁻¹ * y) = k₂⁻¹ * ((k₂ * x * k₂⁻¹) * k⁻¹) * y := by group
        _ = k₂⁻¹ * (k⁻¹ * (k₂ * x * k₂⁻¹)) * y := by rw [e2]
        _ = k₂⁻¹ * k⁻¹ * (k₂ * x * k₂⁻¹ * y) := by group
        _ = k₂⁻¹ * k⁻¹ * (y * x) := by rw [e1]
        _ = ((k * k₂)⁻¹ * y) * x := by group
  intro x hx
  exact (mem_centralizer_singleton_iff.mp (hX hx)).symm

theorem fit_of_K1_side {G : Type} [Group G] [Finite G] (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0) {u : G}
    (hut : D.t * u = u * D.t)
    (Y : Subgroup G) (hYle : Y ≤ D.C ⊓ centralizer ({u} : Set G))
    (hYnorm : ∀ c ∈ D.C ⊓ centralizer ({u} : Set G), ∀ y ∈ Y, c * y * c⁻¹ ∈ Y)
    (hYodd : Odd (Nat.card ↥Y))
    (hside : ∀ y ∈ Y, ∃ k ∈ D.K₁, ∀ x ∈ D.K₁, y * x * y⁻¹ = k * x * k⁻¹) :
    Y ≤ D.Eu u := by
  have ht_mem : D.t ∈ D.C ⊓ centralizer ({u} : Set G) :=
    ⟨mem_centralizer_singleton_iff.mpr (z_comm_t' D hs).symm, mem_centralizer_singleton_iff.mpr hut⟩
  have hKC : D.K ≤ D.C := K_le_C D.ext3 hs
  have hyK : ∀ y ∈ Y, y ∈ D.K := by
    intro y hy
    obtain ⟨k, hk, hk₁⟩ := hside y hy
    obtain ⟨k₂, hk₂, hk₂'⟩ := fitK2_side₂ (t_mul_t' D hs) (t_conj_K₁' D hs) (t_conj_K₂' D hs)
      (hside _ (hYnorm D.t ht_mem y hy))
    have hcen := fitK2_cen hs.comps.comm hk hk₂ hk₁ hk₂'
    have hkK : k ∈ D.K := Subgroup.mem_sup_left hk
    have hk₂K : k₂ ∈ D.K := Subgroup.mem_sup_right hk₂
    have hgC : (k * k₂)⁻¹ * y ∈ D.C :=
      D.C.mul_mem (D.C.inv_mem (D.C.mul_mem (hKC hkK) (hKC hk₂K))) (hYle hy).1
    have hgz : (k * k₂)⁻¹ * y ∈ zpowers D.z := cen_C_K hs hgC hcen
    have hgK : (k * k₂)⁻¹ * y ∈ D.K := (zpowers_le.mpr (z_mem_K' D hs)) hgz
    have hy_eq : y = (k * k₂) * ((k * k₂)⁻¹ * y) := by group
    rw [hy_eq]
    exact D.K.mul_mem (D.K.mul_mem hkK hk₂K) hgK
  exact fitK2_le_pPrimeCoreOf (X := D.K ⊓ centralizer ({u} : Set G))
    (fun y hy => ⟨hyK y hy, (hYle hy).2⟩)
    (fun c hc w hw => hYnorm c ⟨hKC hc.1, hc.2⟩ w hw) hYodd

end FitK2

end CFSG.GH74.GLS.SP.Local
