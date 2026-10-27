module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5LAInd
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5LAModel
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTInd
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Tab5Cov

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec5la_centralizes_of_mem_normalizer {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hS : Asc82SchurU43) (hL : IsOm6Z2 L) {z : G} (hz : IsI4PlusIn L z) {w : G}
    (hwN : w ∈ normalizer (L : Set G)) (hwz : w ∈ centralizer ({z} : Set G))
    (hw6 : Nat.Coprime (orderOf w) 6) : w ∈ centralizer (L : Set G) := by
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, hφ⟩ := t5_exists_cover hS hL
  letI := i1
  letI := i2
  letI := i3
  obtain ⟨e, he⟩ := t5_exists_model hL hφ
  have hzL : z ∈ L := by
    obtain ⟨_, K, hzK, hKle, _⟩ := hz
    exact (Subgroup.mem_inf.mp (hKle hzK)).1
  let ρ : ↥L →* omegaProj hQ := (omegaToProj hQ).comp φ
  have hρsurj : Function.Surjective ρ := (omegaToProj_surjective hQ).comp hφ.surjective
  have hρker : ρ.ker = Subgroup.center ↥L := by
    ext l
    rw [MonoidHom.mem_ker]
    change omegaToProj hQ (φ l) = 1 ↔ l ∈ Subgroup.center ↥L
    rw [← he l, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  let nw : normalizer (L : Set G) := ⟨w, hwN⟩
  let σ : MulAut ↥L := L.normalizerMonoidHom nw
  have hnw : orderOf nw = orderOf w := Subgroup.orderOf_mk w hwN
  have hσn : σ ^ orderOf w = 1 := by
    change (L.normalizerMonoidHom nw) ^ orderOf w = 1
    rw [← map_pow, show nw ^ orderOf w = 1 from by
      rw [← hnw]; exact pow_orderOf_eq_one nw, map_one]
  have hcenter : ∀ l : ↥L, l ∈ Subgroup.center ↥L ↔ σ l ∈ Subgroup.center ↥L := by
    have hfwd : ∀ (τ : MulAut ↥L) (a : ↥L),
        a ∈ Subgroup.center ↥L → τ a ∈ Subgroup.center ↥L := by
      intro τ a ha
      rw [Subgroup.mem_center_iff] at ha ⊢
      intro y
      obtain ⟨y', rfl⟩ := τ.surjective y
      rw [← map_mul, ← map_mul, ha y']
    intro l
    constructor
    · exact hfwd σ l
    · intro hl
      have h := hfwd σ.symm (σ l) hl
      simpa using h
  have hker : ∀ l : ↥L, l ∈ ρ.ker ↔ σ l ∈ ρ.ker := by
    intro l
    rw [hρker]
    exact hcenter l
  obtain ⟨ᾱ, hᾱ, hᾱn⟩ := sec5la_exists_induced_aut hρsurj σ hker
  let u : omegaGroup hQ := φ ⟨z, hzL⟩
  have huu : (u : OGroup Q) * u = 1 := by
    have hzsq : z * z = 1 := t5_mul_self_eq_one_of_orderOf_eq_two hz.1
    change ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) *
      ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) = 1
    rw [← Subgroup.coe_mul, ← map_mul,
      show (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 from Subtype.ext hzsq, map_one]
    rfl
  have hty : invType (u : OGroup Q) = (4, 1) := t5_phi_pocket_invType hφ hL hz hzL
  have hzw : z * w = w * z := (Subgroup.mem_centralizer_iff.mp hwz) z (Set.mem_singleton z)
  have hσz : σ ⟨z, hzL⟩ = ⟨z, hzL⟩ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change w * z * w⁻¹ = z
    rw [show w * z = z * w from hzw.symm]
    group
  have hfix : ᾱ (omegaToProj hQ u) = omegaToProj hQ u := by
    have h1 : ρ (σ ⟨z, hzL⟩) = ρ ⟨z, hzL⟩ := by rw [hσz]
    have h2 := hᾱ ⟨z, hzL⟩
    rw [h1] at h2
    exact h2.symm
  have hαn : ᾱ ^ orderOf w = 1 := hᾱn (orderOf w) hσn
  have hαeq : ᾱ = 1 :=
    sec5la_mulAut_omegaProj_eq_one hQ hφ.finrank_eq hφ.quadSign_eq huu hty hw6 hαn hfix
  have hσ1 : σ = 1 :=
    sec63PT_eq_one_of_induced_eq_one (le_of_eq hρker) hL.1.1.commutator_eq_top (fun a => by
      rw [hᾱ a, hαeq, MulAut.one_apply])
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hconj : w * x * w⁻¹ = x := by
    have h3 : ((σ ⟨x, hx⟩ : ↥L) : G) = x := by
      rw [hσ1, MulAut.one_apply]
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
    change w * x * w⁻¹ = x at h3
    exact h3
  calc x * w = (w * x * w⁻¹) * w := by rw [hconj]
    _ = w * x := by group

end CFSG.OddStandard.SmallF3.Omega
