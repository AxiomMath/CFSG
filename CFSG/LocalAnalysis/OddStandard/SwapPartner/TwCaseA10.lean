module

import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLAltSetup
import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLPermSimple
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLShape

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open Equiv

open scoped commutatorElement

theorem false_of_alternating_ten_of_conj {X : Type*} [Group X] [Finite X] {t : X}
    {Sg V K : Subgroup X} [K.Normal] (h : SwapShape t Sg V) (hKq : CFSG.IsQuasisimple K)
    (hA : ⁅Sg, Sg⁆ ≤ K) (hne : ⁅Sg, Sg⁆ ≠ K)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 10)) {y a : X}
    (ha : a ∈ (⁅Sg, Sg⁆ : Subgroup X)) (ha1 : a ≠ 1) (hy2 : y * y = 1)
    (hy : y * t * y⁻¹ = t * a) : False := by
  classical
  have hK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKq.1
  have ht : t * t = 1 := by
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h.order_eq])
  obtain ⟨π, hπ2, hπ⟩ := exists_perm_intertwining ht (by norm_num) (by norm_num) e
  obtain ⟨σ, hσ2, hσ⟩ := exists_perm_intertwining hy2 (by norm_num) (by norm_num) e
  have hπ1 : π ≠ 1 := pi_ne_one h hK hne hA e hπ
  obtain ⟨hf, hk2, hAeq⟩ := card_fixed_eq_eight hπ2 hπ1
    (imageAbar_le h e hπ) (card_imageAbar h hA e) (isSimpleGroup_imageAbar h hA e)
    (card_alt_inf_centralizer_le h e hπ)
  let a' : K := ⟨a, hA ha⟩
  let ε : Perm (Fin 10) := toPerm e a'
  have ha'_mem : a' ∈ ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K : Set K) :=
    Subgroup.mem_subgroupOf.mpr ha
  have hεimg : ε ∈ imageAbar Sg K e := by
    show toPerm e a' ∈ ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K).map (toPerm e)
    exact Subgroup.mem_map.mpr ⟨a', ha'_mem, rfl⟩
  have hεmem : ε ∈ altFixingMoved π := hAeq ▸ hεimg
  have hεfix : ∀ x, π x ≠ x → ε x = x := (mem_altFixingMoved.mp hεmem).2
  have heps_ne : ε ≠ 1 := by
    intro hε1
    have hinj := injOn_toPerm_commutator h hA e
    have haeq1 : a' = 1 := hinj ha'_mem (Subgroup.one_mem _) (by rw [map_one]; exact hε1)
    exact ha1 (congrArg Subtype.val haeq1)
  have hσ_inv : ∀ k : K, toPerm e (MulAut.conjNormal y⁻¹ k) =
      σ⁻¹ * toPerm e k * σ := by
    intro k
    have h1 : MulAut.conjNormal y (MulAut.conjNormal y⁻¹ k) = k := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have h := hσ (MulAut.conjNormal y⁻¹ k)
    rw [h1] at h
    have h2 : σ⁻¹ * toPerm e k * σ = toPerm e (MulAut.conjNormal y⁻¹ k) := by
      rw [h]; group
    exact h2.symm
  have ha_conj : ∀ k : K, toPerm e (MulAut.conjNormal a k) =
      ε * toPerm e k * ε⁻¹ := by
    intro k
    have hconj_eq : MulAut.conjNormal a k = a' * k * a'⁻¹ := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv, a']
    rw [hconj_eq, map_mul, map_mul, map_inv]
  have ha_eq : ∀ k : K, toPerm e (MulAut.conjNormal (y * t * y⁻¹) k) =
      (σ * π * σ⁻¹) * toPerm e k * (σ * π * σ⁻¹)⁻¹ := by
    intro k
    have hφ : MulAut.conjNormal (H := K) (y * t * y⁻¹) =
        MulAut.conjNormal (H := K) y * MulAut.conjNormal (H := K) t *
          MulAut.conjNormal (H := K) y⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hφ, MulAut.mul_apply, MulAut.mul_apply]
    rw [hσ (MulAut.conjNormal t (MulAut.conjNormal y⁻¹ k)),
      hπ (MulAut.conjNormal y⁻¹ k), hσ_inv k]
    group
  have hb_eq : ∀ k : K, toPerm e (MulAut.conjNormal (y * t * y⁻¹) k) =
      (π * ε) * toPerm e k * (π * ε)⁻¹ := by
    intro k
    rw [hy, map_mul, MulAut.mul_apply, hπ (MulAut.conjNormal a k), ha_conj k]
    group
  let u : Perm (Fin 10) := (π * ε)⁻¹ * (σ * π * σ⁻¹)
  have hcomm : ∀ k : K, u * toPerm e k * u⁻¹ = toPerm e k := by
    intro k
    have h1 : (σ * π * σ⁻¹) * toPerm e k * (σ * π * σ⁻¹)⁻¹ =
        (π * ε) * toPerm e k * (π * ε)⁻¹ := (ha_eq k).symm.trans (hb_eq k)
    calc u * toPerm e k * u⁻¹
        = (π * ε)⁻¹ * ((σ * π * σ⁻¹) * toPerm e k * (σ * π * σ⁻¹)⁻¹) *
            (π * ε) := by simp only [u]; group
      _ = (π * ε)⁻¹ * ((π * ε) * toPerm e k * (π * ε)⁻¹) * (π * ε) := by rw [h1]
      _ = toPerm e k := by group
  have hmem : u ∈ Subgroup.centralizer
      ((alternatingGroup (Fin 10) : Subgroup (Perm (Fin 10))) : Set (Perm (Fin 10))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [← range_toPerm (e := e)] at hz
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hz
    have h := hcomm k
    have h' : toPerm e k * u = u * toPerm e k := by
      have h1 : u * toPerm e k = toPerm e k * u := by
        calc u * toPerm e k = (u * toPerm e k * u⁻¹) * u := by group
          _ = toPerm e k * u := by rw [h]
      exact h1.symm
    exact h'
  have hu1 : u = 1 := by
    apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 10
      (by norm_num)
    rw [map_one]
    ext ⟨z, hz⟩
    rw [MulAut.one_apply, MulAut.conjNormal_apply]
    have hzu : z * u = u * z := (Subgroup.mem_centralizer_iff.mp hmem) z hz
    rw [hzu.symm]
    group
  have hrel : σ * π * σ⁻¹ = π * ε := by
    have h1 : (π * ε)⁻¹ * (σ * π * σ⁻¹) = 1 := hu1
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  let ρ : Perm (Fin 10) := π * ε
  have hρeq : ρ = σ * π * σ⁻¹ := hrel.symm
  have hcardρ : Fintype.card {x : Fin 10 // ρ x = x} = 8 := by
    have hcard : Fintype.card {x : Fin 10 // π x = x} =
        Fintype.card {x : Fin 10 // ρ x = x} := by
      have key : ∀ b, ρ (σ b) = σ (π b) := by
        intro b; rw [hρeq]; simp [Perm.mul_apply]
      refine Fintype.card_congr (Equiv.subtypeEquiv σ (fun a => ?_))
      rw [key]
      exact ⟨fun h => by rw [h], fun h => σ.injective h⟩
    rw [hcard.symm, hf]
  have hlt : Fintype.card {x : Fin 10 // ρ x = x} <
      Fintype.card {x : Fin 10 // π x = x} := by
    let Fπ : Finset (Fin 10) := Finset.univ.filter (fun x => π x = x)
    let Fρ : Finset (Fin 10) := Finset.univ.filter (fun x => ρ x = x)
    have hcardπ : Fπ.card = Fintype.card {x : Fin 10 // π x = x} := by
      rw [Fintype.card_subtype]
    have hcardρ' : Fρ.card = Fintype.card {x : Fin 10 // ρ x = x} := by
      rw [Fintype.card_subtype]
    have hsub : Fρ ⊆ Fπ := by
      intro x hx
      simp only [Fρ, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Fπ, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hxπ
      have hεx : ε x = x := hεfix x hxπ
      have hπx : π (ε x) = x := by simpa [ρ, Perm.mul_apply] using hx
      rw [hεx] at hπx
      exact hxπ hπx
    have hex : ∃ x, ε x ≠ x := by
      by_contra h
      rw [not_exists] at h
      exact heps_ne (Equiv.ext fun x => not_not.mp (h x))
    obtain ⟨x, hxε⟩ := hex
    have hxπ : π x = x := by
      by_contra hx
      exact hxε (hεfix x hx)
    have hxρ : ρ x ≠ x := by
      intro hρx
      have h1 : π (ε x) = x := by simpa [ρ, Perm.mul_apply] using hρx
      have h2 : π (ε x) = ε x := by
        by_contra hne
        exact hxε (ε.injective (hεfix (ε x) hne))
      exact hxε (h2.symm.trans h1)
    have hne : Fρ ≠ Fπ := by
      intro heq
      have hxmem : x ∈ Fπ := by
        simp only [Fπ, Finset.mem_filter, Finset.mem_univ, true_and]; exact hxπ
      have hxρ' : x ∈ Fρ := by rw [heq]; exact hxmem
      simp only [Fρ, Finset.mem_filter, Finset.mem_univ, true_and] at hxρ'
      exact hxρ hxρ'
    have hssub : Fρ ⊂ Fπ := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    have := Finset.card_lt_card hssub
    rw [hcardρ', hcardπ] at this
    exact this
  rw [hcardρ, hf] at hlt
  exact absurd hlt (lt_irrefl 8)

end CFSG.OddStandard.AltStdSec.SwapPartner
