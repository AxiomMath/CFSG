module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov1
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] {L : Subgroup G}

theorem CoverSetting.isM22Cover {t : G} (hc : CoverSetting L t)
    (hq : IsSporadic (L ⧸ center L) .M22) : IsM22Cover L ⟨t, hc.t_mem⟩ where
  orderOf_t := by
    rw [Subgroup.orderOf_mk]
    exact hc.orderOf_t
  center_eq := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hc.map_center, MonoidHom.map_zpowers]
    rfl
  quotient := hq

variable [Finite G]

theorem false_of_inner_cover
    (h : StdHyp G L) {t : G} (hc : CoverSetting L t) (hq : IsSporadic (L ⧸ center L) .M22)
    (hH : centralizer ({t} : Set G) = L) : False := by
  have := h.simple
  have hcov := hc.isM22Cover hq
  have : Group.IsPerfect L := Group.isPerfect_def.2 h.standard.1.1
  obtain ⟨g, hne, hcomm⟩ := exists_fused_commuting_involution h.nonabelian hc.orderOf_t
  set t' : G := g * t * g⁻¹ with ht'
  have ht'2 : orderOf t' = 2 := by
    rw [ht', show g * t * g⁻¹ = MulAut.conj g t from rfl, MulEquiv.orderOf_eq, hc.orderOf_t]
  have ht'sq : t' * t' = 1 := by rw [← sq, ← ht'2, pow_orderOf_eq_one]
  have ht'1 : t' ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ht'2
    exact absurd ht'2 (by decide)
  have ht'H : t' ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hcomm
  have ht'L : t' ∈ L := hH ▸ ht'H
  let u : L := ⟨t', ht'L⟩
  have hu2 : u * u = 1 := Subtype.ext ht'sq
  have hu1 : u ≠ ⟨t, hc.t_mem⟩ := fun e => hne (congrArg Subtype.val e)
  have hu0 : u ≠ 1 := fun e => ht'1 (congrArg Subtype.val e)
  have hbar : orderOf (u : L ⧸ center L) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← QuotientGroup.mk_mul, hu2, QuotientGroup.mk_one]
    · intro h1
      have hmem : u ∈ center L := (QuotientGroup.eq_one_iff u).1 h1
      rw [hcov.center_eq] at hmem
      rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hcov.orderOf_t hmem with e | e
      · exact hu0 e
      · exact hu1 e
  obtain ⟨w, hw⟩ := hcov.exists_sq_of_lift u hbar
  have hwt : (w : G) * w = t' := congrArg Subtype.val hw
  set w' : G := g⁻¹ * (w : G) * g with hw'def
  have hw' : w' * w' = t := by
    calc w' * w' = g⁻¹ * ((w : G) * w) * g := by rw [hw'def]; group
      _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hwt]
      _ = t := by group
  have hw'H : w' ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc w' * t = w' * (w' * w') := by rw [hw']
      _ = t * w' := by rw [← mul_assoc, hw']
  have hw'L : w' ∈ L := hH ▸ hw'H
  exact hcov.not_sq_t ⟨w', hw'L⟩ (Subtype.ext hw')

end CFSG.EvenSporadicStandard.M22Std
