module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Pins.Counting
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Pins.Duad
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Normalizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Glue1

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open Subgroup CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin (pairVec)
open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

structure NormCocode (G : Type) [Group G] (E : Subgroup G) (t : G) (i j : Fin 24) where
  e : ↥E ≃* W11
  ext : CocodeExtension ↥(normalizer (E : Set G)) (E.subgroupOf (normalizer (E : Set G)))
    ((subgroupOfNormalizerEquiv E).trans e)
  t_mem : t ∈ E
  e_t : e ⟨t, t_mem⟩ = cocodeCoords.κ (pairVec i j)

variable {G : Type} [Group G] {L E : Subgroup G} {t : G}

theorem nonempty_normCocode
    (hm : M24Out G E t) {i j : Fin 24} (hij : i ≠ j) :
    Nonempty (NormCocode G E t i j) := by
  letI := commGroupOfM24Out hm
  obtain ⟨z, hz⟩ := exists_isZ_of_m24Out hm
  obtain ⟨e₁, he₁, -, het₁⟩ := exists_equiv_std hm hz
  obtain ⟨p, hp, hp0, hp1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two (1 : Fin 24) 3 (by decide)
  obtain ⟨q, hq, hq0, hq1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two i j hij
  let σ : ↥AutPerm := ⟨q * p⁻¹, mul_mem hq (inv_mem hp)⟩
  have hpi1 : p⁻¹ 1 = 0 := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hp0.symm
  have hpi3 : p⁻¹ 3 = 1 := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hp1.symm
  have hσ1 : ((σ : ↥AutPerm) : Equiv.Perm (Fin 24)) 1 = i := by
    show (q * p⁻¹) 1 = i
    rw [Equiv.Perm.mul_apply, hpi1, hq0]
  have hσ3 : ((σ : ↥AutPerm) : Equiv.Perm (Fin 24)) 3 = j := by
    show (q * p⁻¹) 3 = j
    rw [Equiv.Perm.mul_apply, hpi3, hq1]
  let e : ↥E ≃* W11 := e₁.trans (rho11 AutPerm le_rfl σ)
  have hX : (S44.XE E).map (CFSG.Quasithin.H.congrHom e) = img11 AutPerm :=
    map_congrHom_trans_of_mem he₁ (CFSG.Quasithin.H.Coc24.rho11_mem_img11 σ)
  have het : e ⟨t, hm.t_mem⟩ = cocodeCoords.κ (pairVec i j) := by
    show rho11 AutPerm le_rfl σ (e₁ ⟨t, hm.t_mem⟩) = _
    rw [het₁, t0_eq_kappa_pairVec, rho11_kappa_pairVec, hσ1, hσ3]
  exact ⟨⟨e, CocodeExtension.of_normalizer hm.centralizer_eq e hX, hm.t_mem, het⟩⟩

theorem NormCocode.mem_centralizer_iff_mem_Bhat
    {i j : Fin 24} (D : NormCocode G E t i j) (hij : i ≠ j) (n : ↥(normalizer (E : Set G))) :
    (n : G) ∈ centralizer ({t} : Set G) ↔ n ∈ D.ext.Bhat i j := by
  have ht : t ∈ normalizer (E : Set G) := le_normalizer D.t_mem
  let x : ↥(E.subgroupOf (normalizer (E : Set G))) := ⟨⟨t, ht⟩, mem_subgroupOf.2 D.t_mem⟩
  have hx : ((subgroupOfNormalizerEquiv E).trans D.e) x = cocodeCoords.κ (pairVec i j) := D.e_t
  rw [← D.ext.conj_eq_iff_mem_Bhat hij hx n, mem_centralizer_singleton_iff]
  constructor
  · intro hc
    apply Subtype.ext
    show (n : G) * t * (n : G)⁻¹ = t
    rw [mul_inv_eq_iff_eq_mul]
    exact hc
  · intro hc
    have h1 : (n : G) * t * (n : G)⁻¹ = t := congrArg Subtype.val hc
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1

theorem Std.mem_iff_mem_Bduad
    [Finite G] {i j : Fin 24} (h : Std G L E t)
    (hr : L.relIndex (centralizer ({t} : Set G)) = 2)
    (D : NormCocode G E t i j) (hij : i ≠ j) (n : ↥(normalizer (E : Set G))) :
    (n : G) ∈ L ↔ n ∈ D.ext.Bduad i j := by
  set N := normalizer (E : Set G) with hN
  have hle : L.subgroupOf N ≤ D.ext.Bduad i j := by
    intro n hn
    have hnL : (n : G) ∈ L := mem_subgroupOf.1 hn
    have hgen := h.facts.gen ⟨n.2, hnL⟩
    have hB : E ⊔ closure {y | y ∈ N ⊓ L ∧ Odd (orderOf y)} ≤
        (D.ext.Bduad i j).map N.subtype := by
      refine sup_le ?_ ((closure_le _).2 ?_)
      · intro x hx
        exact ⟨⟨x, le_normalizer hx⟩, D.ext.le_Bduad i j (mem_subgroupOf.2 hx), rfl⟩
      · rintro y ⟨⟨hyN, hyL⟩, hodd⟩
        have hyC : ((⟨y, hyN⟩ : ↥N) : G) ∈ centralizer ({t} : Set G) := h.facts.le_centralizer hyL
        have hyH := (D.mem_centralizer_iff_mem_Bhat hij ⟨y, hyN⟩).1 hyC
        have hy' : (⟨y, hyN⟩ : ↥N) ∈ D.ext.Bduad i j :=
          D.ext.mem_Bduad_of_mem_Bhat_of_odd hij hyH (by rwa [Subgroup.orderOf_mk])
        exact ⟨⟨y, hyN⟩, hy', rfl⟩
    obtain ⟨m, hm, hmn⟩ := hB hgen
    have hmn' : m = n := Subtype.ext hmn
    exact hmn' ▸ hm
  have hH : D.ext.Bhat i j = (centralizer ({t} : Set G)).subgroupOf N := by
    ext n
    rw [mem_subgroupOf, D.mem_centralizer_iff_mem_Bhat hij n]
  have hcard : Nat.card ↥(D.ext.Bhat i j) = 2 * Nat.card ↥(L.subgroupOf N) := by
    rw [hH, card_subgroupOf_eq_card_inf, card_subgroupOf_eq_card_inf]
    exact S44.card_normalizer_inf_centralizer h.facts hr
  have heq : L.subgroupOf N = D.ext.Bduad i j :=
    eq_of_le_of_card_eq_two_mul hle (D.ext.Bduad_le_Bhat i j)
      (D.ext.exists_mem_Bhat_not_mem_Bduad hij) hcard
  constructor
  · intro hnL
    exact hle (mem_subgroupOf.2 hnL)
  · intro hn
    rw [← heq] at hn
    exact mem_subgroupOf.1 hn

theorem Std.card_normalizer_inf_eq_mul_card_duadStab
    [Finite G] {i j : Fin 24} (h : Std G L E t)
    (hr : L.relIndex (centralizer ({t} : Set G)) = 2) (D : NormCocode G E t i j) (hij : i ≠ j) :
    Nat.card ↥(normalizer (E : Set G) ⊓ L) = 2 ^ 11 * Nat.card ↥(duadStab i j) := by
  have hB : L.subgroupOf (normalizer (E : Set G)) = D.ext.Bduad i j := by
    ext n
    exact (mem_subgroupOf).trans (Std.mem_iff_mem_Bduad h hr D hij n)
  have hE : Nat.card ↥(E.subgroupOf (normalizer (E : Set G))) = 2 ^ 11 := by
    rw [Nat.card_congr (subgroupOfNormalizerEquiv E).toEquiv]
    exact h.facts.card_E
  rw [← card_subgroupOf_eq_card_inf, hB, D.ext.card_Bduad i j, hE]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
