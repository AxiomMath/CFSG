module

public import CFSG.GH74.GLS.IVK.Lifted.Lem31c
public import CFSG.GH74.GLS.IVK.Lifted.GroupAux

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

section Frattini

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_centralizing (K : Subgroup G) {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzK : z ∈ K)
    {y : G} (hy : y ∈ cSec K) :
    ∃ o ∈ pPrimeCoreOf 2 K, o⁻¹ * y ∈ centralizer ({z} : Set G) := by
  classical
  set O := pPrimeCoreOf 2 K with hO
  have hzN : z ∈ normalizer (O : Set G) :=
    CFSG.GH74.GLS.TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hzK)
  obtain ⟨-, -, hycomm⟩ := hy
  have hco : ⁅z, y⁆ ∈ O := hycomm z hzK
  set o₂ : G := (⁅z, y⁆)⁻¹ with ho₂
  have ho₂O : o₂ ∈ O := O.inv_mem hco
  set u : G := y * z * y⁻¹ with hu
  have hu_eq : u = o₂ * z := by
    rw [hu, ho₂, commutatorElement_def]
    group
  have hu2 : u * u = 1 := by
    calc u * u = y * (z * z) * y⁻¹ := by rw [hu]; group
      _ = 1 := by rw [hz2]; group
  have hu1 : u ≠ 1 := by
    intro h
    apply hz1
    have : y * z * y⁻¹ = 1 := h
    calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
      _ = 1 := by rw [this]; group
  have hnorm : ∀ n ∈ O, u * n * u⁻¹ ∈ O := by
    intro n hn
    have h1 : z * n * z⁻¹ ∈ O := TwoThin.pPrimeCoreOf_normalized K hzK hn
    have h2 : u * n * u⁻¹ = o₂ * (z * n * z⁻¹) * o₂⁻¹ := by rw [hu_eq]; group
    rw [h2]
    exact O.mul_mem (O.mul_mem ho₂O h1) (O.inv_mem ho₂O)
  have hxO : z * u⁻¹ ∈ O := by
    have : z * u⁻¹ = o₂⁻¹ := by rw [hu_eq]; group
    rw [this]
    exact O.inv_mem ho₂O
  obtain ⟨g, hg, hgz⟩ := exists_conj_of_mul_mem_odd (TwoThin.card_pPrimeCoreOf_odd K) hz2 hu2 hz1 hu1
    hnorm hxO
  have huS : u ∈ O ⊔ zpowers z := by
    rw [hu_eq]
    exact mul_mem (mem_sup_left ho₂O) (mem_sup_right (mem_zpowers z))
  have hzS : z ∈ O ⊔ zpowers u := by
    have : z = o₂⁻¹ * u := by rw [hu_eq]; group
    rw [this]
    exact mul_mem (mem_sup_left (O.inv_mem ho₂O)) (mem_sup_right (mem_zpowers u))
  have hsup : O ⊔ zpowers u ≤ O ⊔ zpowers z := sup_le le_sup_left (zpowers_le.2 huS)
  obtain ⟨o, hoO, i, rfl⟩ := exists_mul_zpow_of_mem_sup hzN (hsup hg)
  have hconj : u = o * z * o⁻¹ := by
    rw [← hgz]
    group
  refine ⟨o, hoO, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have : y * z * y⁻¹ = o * z * o⁻¹ := hconj
  calc o⁻¹ * y * z = o⁻¹ * (y * z * y⁻¹) * y := by group
    _ = o⁻¹ * (o * z * o⁻¹) * y := by rw [this]
    _ = z * (o⁻¹ * y) := by group

omit [Finite G] in
theorem pPrimeCoreOf_le_cSec (K : Subgroup G) : pPrimeCoreOf 2 K ≤ cSec K := by
  intro o ho
  have hoK : o ∈ K := TwoThin.pPrimeCoreOf_le K ho
  refine ⟨Subgroup.le_normalizer hoK,
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hoK), ?_⟩
  intro k hk
  rw [commutatorElement_def]
  exact (pPrimeCoreOf 2 K).mul_mem (TwoThin.pPrimeCoreOf_normalized K hk ho)
    ((pPrimeCoreOf 2 K).inv_mem ho)

theorem relIndex_centralizer_odd (K : Subgroup G) {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzK : z ∈ K) :
    Odd ((cSec K ⊓ centralizer ({z} : Set G)).relIndex (cSec K)) := by
  classical
  set O := pPrimeCoreOf 2 K with hO
  set Y := cSec K with hY
  set Y₀ := Y ⊓ centralizer ({z} : Set G) with hY₀
  have hOY : O ≤ Y := pPrimeCoreOf_le_cSec K
  have hYN : Y ≤ normalizer (O : Set G) := fun y hy => hy.2.1
  have : (O.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).2 hYN
  have hsup : O.subgroupOf Y ⊔ Y₀.subgroupOf Y = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨o, ho, hc⟩ := exists_odd_centralizing K hz2 hz1 hzK hy
    have h1 : (⟨o, hOY ho⟩ : ↥Y) ∈ O.subgroupOf Y := Subgroup.mem_subgroupOf.2 ho
    have h2 : (⟨o⁻¹ * y, Y.mul_mem (Y.inv_mem (hOY ho)) hy⟩ : ↥Y) ∈ Y₀.subgroupOf Y :=
      Subgroup.mem_subgroupOf.2 ⟨Y.mul_mem (Y.inv_mem (hOY ho)) hy, hc⟩
    have h3 := Subgroup.mul_mem_sup h1 h2
    have h4 : (⟨o, hOY ho⟩ : ↥Y) * ⟨o⁻¹ * y, Y.mul_mem (Y.inv_mem (hOY ho)) hy⟩ = ⟨y, hy⟩ :=
      Subtype.ext (by simp)
    rwa [h4] at h3
  have hrel := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (O.subgroupOf Y)
    (Y₀.subgroupOf Y)
  rw [hsup, Subgroup.relIndex_top_right] at hrel
  have hdvd : (Y₀.subgroupOf Y).relIndex (O.subgroupOf Y) ∣ Nat.card ↥(O.subgroupOf Y) :=
    Subgroup.index_dvd_card _
  have hcardN : Nat.card ↥(O.subgroupOf Y) = Nat.card ↥O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOY).toEquiv
  have hodd : Odd (Nat.card ↥(O.subgroupOf Y)) := by
    rw [hcardN]
    exact TwoThin.card_pPrimeCoreOf_odd K
  have : Odd ((Y₀.subgroupOf Y).index) := by
    rw [hrel]
    exact Odd.of_dvd_nat hodd hdvd
  exact this

end Frattini

end CFSG.GH74.GLS.IVK.Lifted
