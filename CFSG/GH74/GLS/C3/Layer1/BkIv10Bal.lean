module

public import CFSG.GH74.GLS.C3.Layer1.BkIv10Aux
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.GH74.GLS.C3.Layer1.BkIv81Core

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCoreOf_centralizer_le_normalizer {x y : G} {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hy2 : orderOf y = 2)
    (hyN : y ∈ normalizer (K : Set G))
    (hZ : ∀ c ∈ K, orderOf c = 2 → ¬ ∀ l ∈ K, ⁅c, l⁆ ∈ pPrimeCoreOf 2 K) :
    pPrimeCoreOf 2 (centralizer ({x, y} : Set G)) ≤ normalizer (K : Set G) := by
  intro w hwW
  by_contra hwN
  set X : Subgroup G := centralizer ({x} : Set G) with hXdef
  set Z : Subgroup G := centralizer ({x, y} : Set G) with hZdef
  have hZmem : ∀ z, z ∈ Z ↔ z * x = x * z ∧ z * y = y * z := by
    intro z
    simp only [hZdef, Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
  have hZX : Z ≤ X := fun z hz => by
    rw [hXdef, mem_centralizer_singleton_iff]
    exact ((hZmem z).1 hz).1
  have hwZ : w ∈ Z := TwoThin.pPrimeCoreOf_le Z hwW
  have hwX : w ∈ X := hZX hwZ
  obtain ⟨c, hcK, hc2, hcy⟩ := exists_involution_comm hy2 hyN (even_card_of_isPCompIn hK)
  have hcX : c ∈ X := hK.1 hcK
  have hcx : c * x = x * c := mem_centralizer_singleton_iff.1 hcX
  have hcZ : c ∈ Z := (hZmem c).2 ⟨hcx, hcy⟩
  have hcc : c * c = 1 := by rw [← pow_two, ← hc2, pow_orderOf_eq_one]
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  set K' : Subgroup G := cmap w K with hK'def
  have hcX' : cmap w X = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer hwX)
  have hK'c : IsPCompIn 2 X K' := by
    have := isPCompIn_cmap hK w
    rwa [hcX'] at this
  have hne : K' ≠ K := by
    intro h
    exact hwN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have h1 : K ≤ cSec K' := le_cSec_of_ne hK hK'c hne.symm
  have h2 : K' ≤ cSec K := le_cSec_of_ne hK'c hK hne
  have hc'K' : w * c * w⁻¹ ∈ K' := by
    refine mem_cmap.2 ?_
    have e : w⁻¹ * (w * c * w⁻¹) * w = c := by group
    rw [e]
    exact hcK
  obtain ⟨-, -, hcomm1⟩ := h1 hcK
  have ht : ⁅w * c * w⁻¹, c⁆ ∈ pPrimeCoreOf 2 K' := hcomm1 _ hc'K'
  have hWn : c * w⁻¹ * c⁻¹ ∈ pPrimeCoreOf 2 Z :=
    TwoThin.pPrimeCoreOf_normalized Z hcZ ((pPrimeCoreOf 2 Z).inv_mem hwW)
  have hg : (w * c * w⁻¹) * c ∈ pPrimeCoreOf 2 Z := by
    have e : (w * c * w⁻¹) * c = w * (c * w⁻¹ * c⁻¹) := by rw [hcinv]; group
    rw [e]
    exact (pPrimeCoreOf 2 Z).mul_mem hwW hWn
  have hc'sq : (w * c * w⁻¹) * (w * c * w⁻¹) = 1 := by
    have e : (w * c * w⁻¹) * (w * c * w⁻¹) = w * (c * c) * w⁻¹ := by group
    rw [e, hcc]
    group
  have hc'inv : (w * c * w⁻¹)⁻¹ = w * c * w⁻¹ := inv_eq_of_mul_eq_one_right hc'sq
  have hcomm : ⁅w * c * w⁻¹, c⁆ = ((w * c * w⁻¹) * c) ^ 2 := by
    rw [commutatorElement_def, hc'inv, hcinv, pow_two]
    group
  have hg2 : ((w * c * w⁻¹) * c) ^ 2 ∈ pPrimeCoreOf 2 K' := by rw [← hcomm]; exact ht
  have hodd : Odd (orderOf ((w * c * w⁻¹) * c)) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd Z) (Subgroup.orderOf_dvd_natCard _ hg)
  obtain ⟨m, hm⟩ := hodd
  have hgO : (w * c * w⁻¹) * c ∈ pPrimeCoreOf 2 K' := by
    have h1' : ((w * c * w⁻¹) * c) ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
    have e : (w * c * w⁻¹) * c = (((w * c * w⁻¹) * c) ^ 2) ^ (m + 1) := by
      rw [← pow_mul]
      have : ((w * c * w⁻¹) * c) ^ (2 * (m + 1)) =
          ((w * c * w⁻¹) * c) ^ (2 * m + 1) * ((w * c * w⁻¹) * c) := by
        rw [← pow_succ]; congr 1
      rw [this, h1', one_mul]
    rw [e]
    exact pow_mem hg2 _
  have hcK' : c ∈ K' := by
    have e : c = (w * c * w⁻¹) * ((w * c * w⁻¹) * c) := by
      rw [← mul_assoc, hc'sq, one_mul]
    rw [e]
    exact K'.mul_mem hc'K' (TwoThin.pPrimeCoreOf_le K' hgO)
  obtain ⟨-, -, hcomm2⟩ := h2 hcK'
  refine hZ c hcK hc2 fun l hl => ?_
  have := (pPrimeCoreOf 2 K).inv_mem (hcomm2 l hl)
  rwa [commutatorElement_inv] at this

end CFSG.GH74.GLS.C3.Layer1.Bk
