module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Simp

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {A : Type} [Group A] [Finite A] {H : Subgroup A} {𝒮 : Set (Subgroup A)} {x : A}

private theorem mem_conjugate_mul_conj {S : Subgroup A} {d : A} (hx : x * x = 1) (hd : d ∈ S) :
    x * d * x⁻¹ ∈ CFSG.conjugate S x := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have e : (x⁻¹)⁻¹ * (x * d * x⁻¹) * x⁻¹ = d := by
    calc (x⁻¹)⁻¹ * (x * d * x⁻¹) * x⁻¹ = (x * x) * d * (x * x)⁻¹ := by group
      _ = d := by rw [hx]; group
  rw [e]; exact hd

theorem L34GFac.ne_bot (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮) : S ≠ ⊥ := by
  haveI : Nontrivial ↥S := (l34g_simple_of_simpleFStar (hF.simple S hS)).1.toNontrivial
  exact (Subgroup.nontrivial_iff_ne_bot S).mp inferInstance

theorem L34GFac.center_eq_bot (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮) :
    center ↥S = ⊥ :=
  (l34g_simple_of_simpleFStar (hF.simple S hS)).2

theorem L34GFac.inf_eq_bot (hF : L34GFac H 𝒮 x) {S T : Subgroup A} (hS : S ∈ 𝒮) (hT : T ∈ 𝒮)
    (hne : S ≠ T) : S ⊓ T = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzS, hzT⟩
  have hmem : (⟨z, hzS⟩ : ↥S) ∈ center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hF.comm S hS T hT hne (s : A) s.2 z hzT)
  rw [L34GFac.center_eq_bot hF hS] at hmem
  exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem)

theorem L34GFac.eq_one_of_centralizes (hF : L34GFac H 𝒮 x) {z : A}
    (hz : ∀ S ∈ 𝒮, ∀ s ∈ S, z * s = s * z) : z = 1 := by
  have hH : H ≤ Subgroup.centralizer ({z} : Set A) := by
    rw [← hF.sup_eq]
    refine sSup_le fun S hS s hs => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hz S hS s hs).symm
  have hzH : z ∈ Subgroup.centralizer (H : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hH hh)
  rw [hF.cent] at hzH
  simpa using hzH

theorem L34GFac.comm_conj (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hne : CFSG.conjugate S x ≠ S) : ∀ a ∈ S, ∀ b ∈ CFSG.conjugate S x, a * b = b * a := by
  intro a ha b hb
  exact hF.comm S hS (CFSG.conjugate S x) (hF.perm S hS) hne.symm a ha b hb

theorem L34GFac.diag_mul (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hne : CFSG.conjugate S x ≠ S) {d e : A} (hd : d ∈ S) (he : e ∈ S) :
    (d * e) * (x * (d * e) * x⁻¹) = (d * (x * d * x⁻¹)) * (e * (x * e * x⁻¹)) := by
  have hcomm := hF.comm_conj hS hne e he (x * d * x⁻¹) (mem_conjugate_mul_conj hF.invol hd)
  calc (d * e) * (x * (d * e) * x⁻¹)
      = d * (e * (x * d * x⁻¹) * (x * e * x⁻¹)) := by group
    _ = d * ((x * d * x⁻¹) * e * (x * e * x⁻¹)) := by rw [hcomm]
    _ = (d * (x * d * x⁻¹)) * (e * (x * e * x⁻¹)) := by group

theorem L34GFac.diag_eq_one (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hne : CFSG.conjugate S x ≠ S) {d : A} (hd : d ∈ S) (h : d * (x * d * x⁻¹) = 1) : d = 1 := by
  have hd' : x * d * x⁻¹ = d⁻¹ := by
    calc x * d * x⁻¹ = d⁻¹ * (d * (x * d * x⁻¹)) := by group
      _ = d⁻¹ * 1 := by rw [h]
      _ = d⁻¹ := by group
  have hmem : x * d * x⁻¹ ∈ S ⊓ CFSG.conjugate S x :=
    ⟨by rw [hd']; exact S.inv_mem hd, mem_conjugate_mul_conj hF.invol hd⟩
  rw [L34GFac.inf_eq_bot hF hS (hF.perm S hS) hne.symm] at hmem
  have h1 : x * d * x⁻¹ = 1 := Subgroup.mem_bot.mp hmem
  rw [h1, mul_one] at h
  exact h

theorem L34GFac.diag_mem (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hne : CFSG.conjugate S x ≠ S) {d : A} (hd : d ∈ S) :
    d * (x * d * x⁻¹) ∈ H ⊓ centralizer ({x} : Set A) := by
  have hb : x * d * x⁻¹ ∈ CFSG.conjugate S x := mem_conjugate_mul_conj hF.invol hd
  have hcomm := hF.comm_conj hS hne d hd (x * d * x⁻¹) hb
  constructor
  · exact H.mul_mem (hF.le S hS hd) (hF.le (CFSG.conjugate S x) (hF.perm S hS) hb)
  · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc (d * (x * d * x⁻¹)) * x
        = d * x * d := by group
      _ = x * ((x * d * x⁻¹) * d) := by
            rw [show x⁻¹ = x from inv_eq_of_mul_eq_one_right hF.invol]
            exact (by
              calc d * x * d = (x * x) * d * x * d := by rw [hF.invol]; group
                _ = x * ((x * d * x) * d) := by group)
      _ = x * (d * (x * d * x⁻¹)) := by rw [hcomm]

theorem L34GFac.diag_unique (hF : L34GFac H 𝒮 x) {S : Subgroup A} (hS : S ∈ 𝒮)
    (hne : CFSG.conjugate S x ≠ S) {d e : A} (hd : d ∈ S) (he : e ∈ S)
    (h : d * (x * d * x⁻¹) = e * (x * e * x⁻¹)) : d = e := by
  have hmul := hF.diag_mul hS hne hd (S.inv_mem he)
  have hee : (e * (x * e * x⁻¹)) * (e⁻¹ * (x * e⁻¹ * x⁻¹)) = 1 := by
    have h0 := hF.diag_mul hS hne he (S.inv_mem he)
    simpa using h0.symm
  have hinv : e⁻¹ * (x * e⁻¹ * x⁻¹) = (e * (x * e * x⁻¹))⁻¹ :=
    eq_inv_of_mul_eq_one_right hee
  have hδ : (d * (x * d * x⁻¹)) * (e⁻¹ * (x * e⁻¹ * x⁻¹)) = 1 := by
    rw [hinv, h]
    exact mul_inv_cancel (e * (x * e * x⁻¹))
  have hde : (d * e⁻¹) * (x * (d * e⁻¹) * x⁻¹) = 1 := by
    rw [hmul]; exact hδ
  have h1 : d * e⁻¹ = 1 := hF.diag_eq_one hS hne (S.mul_mem hd (S.inv_mem he)) hde
  simpa using (mul_eq_one_iff_eq_inv.mp h1)

end CFSG.OddStandard.SmallF3.Omega
