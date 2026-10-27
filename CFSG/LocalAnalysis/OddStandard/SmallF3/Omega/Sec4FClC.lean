module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FClType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4FCl_w_mem_conjugate [Finite G] (h43 : Asc82Lemma43) (hf43c : Asc82Fact43Class)
    {t : G} {L S : Subgroup G} {z : G} (hctx : Sec4Ctx G t L S z) {g : G}
    (hgc : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hg6 : InducesTypeSome L (g⁻¹ * t * g) 7 1 6 1) {w : G} (hwL : w ∈ L)
    (hws : w ∈ centralizer ({g⁻¹ * t * g} : Set G)) (hw4 : IsI4PlusIn L w) :
    w ∈ CFSG.conjugate L g := by
  let s : G := g⁻¹ * t * g
  let L' : Subgroup G := CFSG.conjugate L g
  let z' : G := g⁻¹ * z * g
  have hctx' : Sec4Ctx G s L' (CFSG.conjugate S g) z' := hctx.conjugate g
  have hL : IsOmega7Group L := sec4_isOmega7Group hctx.toSec4Setting
  have hz : IsI4PlusIn L z := hctx.pocket
  have hz' : IsI4PlusIn L' z' := hctx'.pocket
  have hz'L' : z' ∈ L' := IsI4PlusIn.mem hz'
  have hs_cent : s ∈ centralizer (L' : Set G) := sec4_t_mem_centralizer hctx'.toSec3Setting
  have ht_cent : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer hctx.toSec3Setting
  have hs_ord : orderOf s = 2 := by
    show orderOf (g⁻¹ * t * g) = 2
    rw [orderOf_conjugate_eq, hctx.involution]
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hs_ord, pow_two] at h
  obtain ⟨l, -, hlw⟩ := hf43c G L hL z w hz hw4
  have hh : (g⁻¹ * l⁻¹)⁻¹ * z' * (g⁻¹ * l⁻¹) = w := by
    rw [hlw]
    simp only [z']
    group
  have hh_cent : (g⁻¹ * l⁻¹)⁻¹ * z' * (g⁻¹ * l⁻¹) ∈ centralizer ({s} : Set G) := by
    rw [hh]
    exact hws
  have hcase := h43 G s L' (CFSG.conjugate S g) z' hctx' (g⁻¹ * l⁻¹) hh_cent
  rw [hh] at hcase
  rcases hcase with h1 | h2
  · obtain ⟨l', hl', hl'w⟩ := h1
    rw [hl'w]
    exact mul_mem (mul_mem hl' hz'L') (inv_mem hl')
  ·
    obtain ⟨l', hl', hl'w⟩ := h2
    have hsl' : s * l' = l' * s :=
      (Subgroup.mem_centralizer_iff.mp hs_cent l' hl').symm
    have hsw : s * w = l' * z' * l'⁻¹ := by
      rw [hl'w]
      calc s * (l' * (s * z') * l'⁻¹)
          = (s * l') * (s * z') * l'⁻¹ := by group
        _ = (l' * s) * (s * z') * l'⁻¹ := by rw [hsl']
        _ = l' * (s * s) * z' * l'⁻¹ := by group
        _ = l' * z' * l'⁻¹ := by rw [hss]; group
    have hh' : (g * l'⁻¹)⁻¹ * z * (g * l'⁻¹) = s * w := by
      rw [hsw]
      simp only [z']
      group
    have hh'_cent : (g * l'⁻¹)⁻¹ * z * (g * l'⁻¹) ∈ centralizer ({t} : Set G) := by
      rw [hh', Subgroup.mem_centralizer_singleton_iff]
      have hts : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp hgc
      have htw : w * t = t * w := Subgroup.mem_centralizer_iff.mp ht_cent w hwL
      calc (s * w) * t = s * (w * t) := by group
        _ = s * (t * w) := by rw [htw]
        _ = (s * t) * w := by group
        _ = (t * s) * w := by rw [hts]
        _ = t * (s * w) := by group
    have hcase2 := h43 G t L S z hctx (g * l'⁻¹) hh'_cent
    rw [hh'] at hcase2
    rcases hcase2 with h2a | h2b
    · obtain ⟨m, hm, hmw⟩ := h2a
      have hy0L : s * w ∈ L := by
        rw [hmw]
        exact mul_mem (mul_mem hm (IsI4PlusIn.mem hz)) (inv_mem hm)
      have hsL : s ∈ L := by
        have h : s = (s * w) * w⁻¹ := by group
        rw [h]
        exact mul_mem hy0L (inv_mem hwL)
      exact absurd (by simp : s = s * 1)
        (sec4FCl_not_inner6 hL hg6 hsL (Subgroup.one_mem _))
    · obtain ⟨m, hm, hmw⟩ := h2b
      have htm : m * t = t * m := Subgroup.mem_centralizer_iff.mp ht_cent m hm
      have hy0 : s * w = t * (m * z * m⁻¹) := by
        calc s * w = m * (t * z) * m⁻¹ := hmw
          _ = (m * t) * z * m⁻¹ := by group
          _ = (t * m) * z * m⁻¹ := by rw [htm]
          _ = t * (m * z * m⁻¹) := by group
      have humL : m * z * m⁻¹ ∈ L :=
        mul_mem (mul_mem hm (IsI4PlusIn.mem hz)) (inv_mem hm)
      have hcomm : t * ((m * z * m⁻¹) * w⁻¹) = ((m * z * m⁻¹) * w⁻¹) * t :=
        (Subgroup.mem_centralizer_iff.mp ht_cent ((m * z * m⁻¹) * w⁻¹)
          (mul_mem humL (inv_mem hwL))).symm
      have hs_eq : s = ((m * z * m⁻¹) * w⁻¹) * t := by
        calc s = (s * w) * w⁻¹ := by group
          _ = (t * (m * z * m⁻¹)) * w⁻¹ := by rw [hy0]
          _ = t * ((m * z * m⁻¹) * w⁻¹) := by group
          _ = ((m * z * m⁻¹) * w⁻¹) * t := hcomm
      exact absurd hs_eq
        (sec4FCl_not_inner6 hL hg6 (mul_mem humL (inv_mem hwL)) ht_cent)

end CFSG.OddStandard.SmallF3.Omega
