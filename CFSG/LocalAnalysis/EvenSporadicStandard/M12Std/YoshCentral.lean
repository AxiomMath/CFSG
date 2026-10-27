module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshSwap
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModel

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open CFSG.EvenSporadicStandard.Fin76b.AutETable

section SwapAut

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)

set_option linter.unusedSectionVars false

@[expose, irreducible] noncomputable def sG : G := ιH e₀ ⟨sP, sP_mem_M12⟩

theorem sG_def : sG e₀ = ιH e₀ ⟨sP, sP_mem_M12⟩ := by unfold sG; rfl

theorem sG_mem_centralizer : sG e₀ ∈ centralizer ({e} : Set G) := by
  rw [sG_def]; exact (LG_le_centralizer e₀) ⟨_, rfl⟩

theorem e_mem_Hc : e ∈ HcG e₀ :=
  ⟨e_mem_centralizer, mem_centralizer_iff.2 fun y hy => by
    rw [Set.mem_singleton_iff] at hy; rw [hy]; exact cG_comm_e e₀⟩

theorem cG_mem_Hc : cG e₀ ∈ HcG e₀ :=
  ⟨cG_mem_centralizer e₀, mem_centralizer_iff.2 fun y hy => by
    rw [Set.mem_singleton_iff] at hy; rw [hy]⟩

theorem sG_mem_Hc : sG e₀ ∈ HcG e₀ := by
  refine ⟨sG_mem_centralizer e₀, mem_centralizer_iff.2 fun y hy => ?_⟩
  rw [Set.mem_singleton_iff] at hy
  rw [hy, cG_def, sG_def, ← map_mul, ← map_mul]
  exact congrArg (ιH e₀) (Subtype.ext sP_comm_bfJ.symm)

theorem ΘE_coe (y : ↥(HcG e₀)) :
    (ΘE e₀ y : Equiv.Perm (Fin 14)) = ρH e₀ ⟨y.1, y.2.1⟩ := rfl

theorem ΘE_e (he2 : orderOf e = 2) : ΘE e₀ ⟨e, e_mem_Hc e₀⟩ = Spec.eK := by
  apply Subtype.ext
  rw [ΘE_coe, eK_coe, ρH_apply]
  have h := e₀_e e₀ he2
  simp only [h]
  simp [kapP_apply, tauPow_ofAdd_one]

theorem e₀_sG : e₀ ⟨sG e₀, sG_mem_centralizer e₀⟩ = (1, ⟨sP, sP_mem_M12⟩) := by
  have : (⟨sG e₀, sG_mem_centralizer e₀⟩ : centralizer ({e} : Set G)) =
      e₀.symm (1, ⟨sP, sP_mem_M12⟩) := Subtype.ext (sG_def e₀)
  rw [this, MulEquiv.apply_symm_apply]

theorem ΘE_c : ΘE e₀ ⟨cG e₀, cG_mem_Hc e₀⟩ = Spec.cK := by
  apply Subtype.ext
  rw [ΘE_coe, cK_coe, ρH_apply, e₀_cG e₀]
  simp [kapP_apply, tauPow_one]
  rfl

theorem ΘE_s : ΘE e₀ ⟨sG e₀, sG_mem_Hc e₀⟩ = Spec.sK := by
  apply Subtype.ext
  rw [ΘE_coe, sK_coe, ρH_apply, e₀_sG e₀]
  simp [kapP_apply, tauPow_one]

end SwapAut

section Swap

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)

set_option linter.unusedSectionVars false

@[expose] def IsSwap (x : G) : Prop := x * e * x⁻¹ = e * cG e₀ ∧ x * cG e₀ * x⁻¹ = cG e₀

variable {e₀}

theorem IsSwap.inv {x : G} (hx : IsSwap e₀ x) : IsSwap e₀ x⁻¹ := by
  obtain ⟨h1, h2⟩ := hx
  have hcc := cG_sq e₀
  have hc : x⁻¹ * cG e₀ * x = cG e₀ := by
    calc x⁻¹ * cG e₀ * x = x⁻¹ * (x * cG e₀ * x⁻¹) * x := by rw [h2]
      _ = cG e₀ := by group
  refine ⟨?_, by simpa using hc⟩
  have h3 : x * (e * cG e₀) * x⁻¹ = e := by
    calc x * (e * cG e₀) * x⁻¹ = (x * e * x⁻¹) * (x * cG e₀ * x⁻¹) := by group
      _ = e * cG e₀ * cG e₀ := by rw [h1, h2]
      _ = e := by rw [mul_assoc, hcc, mul_one]
  calc x⁻¹ * e * x⁻¹⁻¹ = x⁻¹ * (x * (e * cG e₀) * x⁻¹) * x := by rw [h3]; group
    _ = e * cG e₀ := by group

theorem IsSwap.conj_mem {x : G} (hx : IsSwap e₀ x) {y : G} (hy : y ∈ HcG e₀) :
    x * y * x⁻¹ ∈ HcG e₀ := by
  obtain ⟨hye, hyc⟩ := hy
  have hye' := mem_centralizer_iff.1 hye e (Set.mem_singleton e)
  have hyc' := mem_centralizer_iff.1 hyc (cG e₀) (Set.mem_singleton _)
  have hcc := cG_sq e₀
  have h1 : (e * cG e₀) * (x * y * x⁻¹) = (x * y * x⁻¹) * (e * cG e₀) := by
    rw [← hx.1]
    calc x * e * x⁻¹ * (x * y * x⁻¹) = x * (e * y) * x⁻¹ := by group
      _ = x * (y * e) * x⁻¹ := by rw [hye']
      _ = (x * y * x⁻¹) * (x * e * x⁻¹) := by group
  have h2 : cG e₀ * (x * y * x⁻¹) = (x * y * x⁻¹) * cG e₀ := by
    rw [← hx.2]
    calc x * cG e₀ * x⁻¹ * (x * y * x⁻¹) = x * (cG e₀ * y) * x⁻¹ := by group
      _ = x * (y * cG e₀) * x⁻¹ := by rw [hyc']
      _ = (x * y * x⁻¹) * (x * cG e₀ * x⁻¹) := by group
  have h3 : e * (x * y * x⁻¹) = (x * y * x⁻¹) * e := by
    have hee : e * cG e₀ * cG e₀ = e := by rw [mul_assoc, hcc, mul_one]
    have hA : Commute (e * cG e₀) (x * y * x⁻¹) := h1
    have hB : Commute (cG e₀) (x * y * x⁻¹) := h2
    have := (hA.mul_left hB).eq
    rwa [hee] at this
  exact ⟨mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff] at hh; rw [hh]; exact h3,
    mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff] at hh; rw [hh]; exact h2⟩

theorem IsSwap.map_eq {x : G} (hx : IsSwap e₀ x) :
    (HcG e₀).map (MulAut.conj x).toMonoidHom = HcG e₀ := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hx.conj_mem hy
  · intro z hz
    refine ⟨x⁻¹ * z * x⁻¹⁻¹, hx.inv.conj_mem hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

@[expose] noncomputable def conjHc {x : G} (hx : IsSwap e₀ x) : ↥(HcG e₀) ≃* ↥(HcG e₀) :=
  ((MulAut.conj x).subgroupMap (HcG e₀)).trans (MulEquiv.subgroupCongr hx.map_eq)

theorem conjHc_coe {x : G} (hx : IsSwap e₀ x) (y : ↥(HcG e₀)) :
    (conjHc hx y : G) = x * y * x⁻¹ := rfl

@[expose] noncomputable def swapAut {x : G} (hx : IsSwap e₀ x) : MulAut ↥yK :=
  (ΘE e₀).symm.trans ((conjHc hx).trans (ΘE e₀))

theorem swapAut_apply {x : G} (hx : IsSwap e₀ x) (y : ↥(HcG e₀)) :
    swapAut hx (ΘE e₀ y) = ΘE e₀ (conjHc hx y) := by
  simp [swapAut]

theorem swapAut_symm_apply {x : G} (hx : IsSwap e₀ x) (z : ↥yK) :
    (ΘE e₀).symm (swapAut hx z) = conjHc hx ((ΘE e₀).symm z) := by
  simp [swapAut]

theorem IsSwap.sq_mem {x : G} (hx : IsSwap e₀ x) : x * x ∈ HcG e₀ := by
  have hcc := cG_sq e₀
  have h1 : x * x * e * (x * x)⁻¹ = e := by
    calc x * x * e * (x * x)⁻¹ = x * (x * e * x⁻¹) * x⁻¹ := by group
      _ = x * (e * cG e₀) * x⁻¹ := by rw [hx.1]
      _ = (x * e * x⁻¹) * (x * cG e₀ * x⁻¹) := by group
      _ = e * cG e₀ * cG e₀ := by rw [hx.1, hx.2]
      _ = e := by rw [mul_assoc, hcc, mul_one]
  have h2 : x * x * cG e₀ * (x * x)⁻¹ = cG e₀ := by
    calc x * x * cG e₀ * (x * x)⁻¹ = x * (x * cG e₀ * x⁻¹) * x⁻¹ := by group
      _ = cG e₀ := by rw [hx.2, hx.2]
  refine ⟨mem_centralizer_iff.2 fun h hh => ?_, mem_centralizer_iff.2 fun h hh => ?_⟩
  · rw [Set.mem_singleton_iff] at hh; rw [hh]
    calc e * (x * x) = (x * x * e * (x * x)⁻¹) * (x * x) := by rw [h1]
      _ = (x * x) * e := by group
  · rw [Set.mem_singleton_iff] at hh; rw [hh]
    calc cG e₀ * (x * x) = (x * x * cG e₀ * (x * x)⁻¹) * (x * x) := by rw [h2]
      _ = (x * x) * cG e₀ := by group

theorem exists_d (he2 : orderOf e = 2) {x : G} (hx : IsSwap e₀ x) :
    ∃ d : G, IsSwap e₀ d ∧ d * d = 1 ∧ d * sG e₀ * d⁻¹ = sG e₀ ∧ ∃ h ∈ HcG e₀, d = h * x := by
  set ψ := swapAut hx with hψ
  have heH : ΘE e₀ ⟨e, e_mem_Hc e₀⟩ = Spec.eK := ΘE_e e₀ he2
  have hcH : ΘE e₀ ⟨cG e₀, cG_mem_Hc e₀⟩ = Spec.cK := ΘE_c e₀
  have hsH : ΘE e₀ ⟨sG e₀, sG_mem_Hc e₀⟩ = Spec.sK := ΘE_s e₀
  have hψe : ψ Spec.eK = Spec.eK * Spec.cK := by
    rw [← heH, ← hcH, ← map_mul, hψ, swapAut_apply]
    congr 1
    exact Subtype.ext hx.1
  have hψc : ψ Spec.cK = Spec.cK := by
    rw [← hcH, hψ, swapAut_apply]
    congr 1
    exact Subtype.ext hx.2
  set wH : ↥(HcG e₀) := ⟨x * x, hx.sq_mem⟩ with hwH
  have hψw : ψ (ΘE e₀ wH) = ΘE e₀ wH := by
    rw [hψ, swapAut_apply]
    congr 1
    exact Subtype.ext (by simp [conjHc_coe, hwH]; group)
  have hψ2 : ∀ y : ↥yK, ψ (ψ y) * ΘE e₀ wH = ΘE e₀ wH * y := by
    intro y
    obtain ⟨y', rfl⟩ := (ΘE e₀).surjective y
    rw [hψ, swapAut_apply, swapAut_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [conjHc_coe, hwH, Subgroup.coe_mul]
    group
  obtain ⟨h, hh1, hh2⟩ := yFacts.norm ψ hψe hψc (ΘE e₀ wH) hψw hψ2
  set h' : ↥(HcG e₀) := (ΘE e₀).symm h with hh'
  refine ⟨(h' : G) * x, ?_, ?_, ?_, h', h'.2, rfl⟩
  ·
    have hhe := mem_centralizer_iff.1 h'.2.1 e (Set.mem_singleton e)
    have hhc := mem_centralizer_iff.1 h'.2.2 (cG e₀) (Set.mem_singleton _)
    constructor
    · calc (h' : G) * x * e * ((h' : G) * x)⁻¹ = (h' : G) * (x * e * x⁻¹) * (h' : G)⁻¹ := by group
        _ = (h' : G) * (e * cG e₀) * (h' : G)⁻¹ := by rw [hx.1]
        _ = e * cG e₀ := by
          calc (h' : G) * (e * cG e₀) * (h' : G)⁻¹ = ((h' : G) * e * (h' : G)⁻¹) *
                ((h' : G) * cG e₀ * (h' : G)⁻¹) := by group
            _ = e * cG e₀ := by
              rw [show (h' : G) * e * (h' : G)⁻¹ = e by rw [← hhe]; group,
                show (h' : G) * cG e₀ * (h' : G)⁻¹ = cG e₀ by rw [← hhc]; group]
    · calc (h' : G) * x * cG e₀ * ((h' : G) * x)⁻¹ = (h' : G) * (x * cG e₀ * x⁻¹) * (h' : G)⁻¹ := by
            group
        _ = (h' : G) * cG e₀ * (h' : G)⁻¹ := by rw [hx.2]
        _ = cG e₀ := by rw [← hhc]; group
  ·
    have h3 := congrArg (ΘE e₀).symm hh2
    rw [map_mul, map_mul, map_one, swapAut_symm_apply] at h3
    have h4 : (ΘE e₀).symm (ΘE e₀ wH) = wH := MulEquiv.symm_apply_apply _ _
    rw [h4] at h3
    have h5 := congrArg (fun z : ↥(HcG e₀) => (z : G)) h3
    simp only [Subgroup.coe_mul, conjHc_coe, hwH, Subgroup.coe_one] at h5
    calc (h' : G) * x * ((h' : G) * x) = (h' : G) * (x * (h' : G) * x⁻¹) * (x * x) := by group
      _ = 1 := h5
  ·
    have h3 := congrArg (ΘE e₀).symm hh1
    rw [map_mul, map_mul, swapAut_symm_apply, ← hsH, MulEquiv.symm_apply_apply] at h3
    have h5 := congrArg (fun z : ↥(HcG e₀) => (z : G)) h3
    simp only [Subgroup.coe_mul, conjHc_coe] at h5
    calc (h' : G) * x * sG e₀ * ((h' : G) * x)⁻¹ = ((h' : G) * (x * sG e₀ * x⁻¹)) * (h' : G)⁻¹ := by
          group
      _ = (sG e₀ * (h' : G)) * (h' : G)⁻¹ := by rw [h5]
      _ = sG e₀ := by group

end Swap

section Central

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)

set_option linter.unusedSectionVars false

structure CentralSwap (α : ℕ) (d : G) : Prop where
  sq : d * d = 1
  conj_e : d * e * d⁻¹ = e * cG e₀
  conj_c : d * cG e₀ * d⁻¹ = cG e₀
  conj_s : d * sG e₀ * d⁻¹ = sG e₀
  conj_jH : ∀ (a : Multiplicative (ZMod 2)) (σ : G12), σ * Jelt = Jelt * σ →
    d * jH e₀ (a, σ) * d⁻¹ =
      jH e₀ (a, σ) * cG e₀ ^ ((Multiplicative.toAdd a).val + α * lamP σ.1)

theorem jH_mem_Hc (a : Multiplicative (ZMod 2)) (σ : G12) (hσ : σ * Jelt = Jelt * σ) :
    jH e₀ (a, σ) ∈ HcG e₀ := by
  have hmem : jH e₀ (a, σ) ∈ centralizer ({e} : Set G) := (mem_range_jH e₀).1 ⟨_, rfl⟩
  have hcomm : jH e₀ (a, σ) * cG e₀ = cG e₀ * jH e₀ (a, σ) := by
    rw [cG_def, ιH, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    apply congrArg
    exact Prod.ext (by simp) hσ
  exact ⟨hmem, mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hcomm.symm⟩

theorem e₀_jH (a : Multiplicative (ZMod 2)) (σ : G12) :
    e₀ ⟨jH e₀ (a, σ), (mem_range_jH e₀).1 ⟨_, rfl⟩⟩ = (a, σ) := by
  have : (⟨jH e₀ (a, σ), (mem_range_jH e₀).1 ⟨_, rfl⟩⟩ : centralizer ({e} : Set G)) =
      e₀.symm (a, σ) := Subtype.ext rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem centralSwap_of_cases {α : ℕ} {d : G} (hd : IsSwap e₀ d) (hdd : d * d = 1)
    (hds : d * sG e₀ * d⁻¹ = sG e₀)
    (hcase : ∀ y : ↥yK, swapAut hd y = y * Spec.cK ^ (Spec.epsY y + α * Spec.lamY y)) :
    CentralSwap e₀ α d := by
  refine ⟨hdd, hd.1, hd.2, hds, fun a σ hσ => ?_⟩
  set Y : ↥(HcG e₀) := ⟨jH e₀ (a, σ), jH_mem_Hc e₀ a σ hσ⟩ with hY
  have hperm : (ΘE e₀ Y : Equiv.Perm (Fin 14)) = kapP (a, σ.1) := by
    rw [ΘE_coe, ρH_apply, e₀_jH e₀ a σ]
  have key : ∀ v b L : ℕ, (v + b * L) % 2 = (v + b * (L % 2)) % 2 := by
    intro v b L
    conv_lhs => rw [← Nat.mod_add_div L 2, mul_add, ← add_assoc, mul_left_comm,
      Nat.add_mul_mod_self_left]
  have hmod : (Spec.epsY (ΘE e₀ Y : Equiv.Perm (Fin 14)) +
      α * Spec.lamY (ΘE e₀ Y : Equiv.Perm (Fin 14))) % 2 =
      ((Multiplicative.toAdd a).val + α * lamP σ.1) % 2 := by
    rw [hperm, epsY_kapP, key, lamY_kapP]
  have hpow : Spec.cK ^ (Spec.epsY (ΘE e₀ Y : Equiv.Perm (Fin 14)) +
      α * Spec.lamY (ΘE e₀ Y : Equiv.Perm (Fin 14))) =
      Spec.cK ^ ((Multiplicative.toAdd a).val + α * lamP σ.1) := by
    rw [pow_eq_pow_mod _ yFacts.c_sq, hmod, ← pow_eq_pow_mod _ yFacts.c_sq]
  have h1 := hcase (ΘE e₀ Y)
  rw [hpow, swapAut_apply] at h1
  have hc : ΘE e₀ ⟨cG e₀, cG_mem_Hc e₀⟩ = Spec.cK := ΘE_c e₀
  rw [← hc, ← map_pow, ← map_mul] at h1
  have h2 := (ΘE e₀).injective h1
  have h3 := congrArg (fun z : ↥(HcG e₀) => (z : G)) h2
  simpa [conjHc_coe, hY] using h3

theorem swapAut_e (he2 : orderOf e = 2) {d : G} (hd : IsSwap e₀ d) :
    swapAut hd Spec.eK = Spec.eK * Spec.cK := by
  rw [← ΘE_e e₀ he2, ← ΘE_c e₀, ← map_mul, swapAut_apply]
  congr 1
  exact Subtype.ext hd.1

theorem swapAut_c {d : G} (hd : IsSwap e₀ d) : swapAut hd Spec.cK = Spec.cK := by
  rw [← ΘE_c e₀, swapAut_apply]
  congr 1
  exact Subtype.ext hd.2

theorem swapAut_s {d : G} (hd : IsSwap e₀ d) (hds : d * sG e₀ * d⁻¹ = sG e₀) :
    swapAut hd Spec.sK = Spec.sK := by
  rw [← ΘE_s e₀, swapAut_apply]
  congr 1
  exact Subtype.ext hds

theorem swapAut_inv {d : G} (hd : IsSwap e₀ d) (hdd : d * d = 1) (y : ↥yK) :
    swapAut hd (swapAut hd y) = y := by
  obtain ⟨y', rfl⟩ := (ΘE e₀).surjective y
  rw [swapAut_apply, swapAut_apply]
  congr 1
  apply Subtype.ext
  simp only [conjHc_coe]
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  rw [hdi]
  calc d * (d * (y' : G) * d) * d = (d * d) * (y' : G) * (d * d) := by group
    _ = y' := by rw [hdd]; group

theorem exists_centralSwap_or_bad [Finite G] [IsSimpleGroup G] (he2 : orderOf e = 2) :
    (∃ d, CentralSwap e₀ 0 d) ∨ (∃ d, CentralSwap e₀ 1 d) ∨
    ∃ (d : G) (hd : IsSwap e₀ d), d * d = 1 ∧ d * sG e₀ * d⁻¹ = sG e₀ ∧
      ∀ u : ↥yK, (u : Equiv.Perm (Fin 14)) =
          CFSG.Sporadic.SmallOddCore.tp 14 tauT * CFSG.Sporadic.SmallOddCore.tp 14 u1T →
        Spec.SwapType (swapAut hd) u := by
  obtain ⟨x, hx1, hx2⟩ := exists_swap_pinned e₀ he2
  obtain ⟨d, hd, hdd, hds, -⟩ := exists_d he2 (x := x) ⟨hx1, hx2⟩
  rcases yFacts.classify (swapAut hd) ⟨swapAut_e e₀ he2 hd, swapAut_c e₀ hd,
    swapAut_s e₀ hd hds, swapAut_inv e₀ hd hdd⟩ with h0 | h1 | hb
  · exact Or.inl ⟨d, centralSwap_of_cases e₀ hd hdd hds (α := 0) (fun y => by
      simpa using h0 y)⟩
  · exact Or.inr (Or.inl ⟨d, centralSwap_of_cases e₀ hd hdd hds (α := 1) (fun y => by
      simpa using h1 y)⟩)
  · exact Or.inr (Or.inr ⟨d, hd, hdd, hds, hb⟩)

end Central

end CFSG.EvenSporadicStandard.M12Std.Yosh
