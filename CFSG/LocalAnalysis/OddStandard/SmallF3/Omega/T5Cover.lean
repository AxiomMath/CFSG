module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj
import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

structure IsCoverMap (L : Subgroup G) (φ : ↥L →* omegaGroup hQ) : Prop where
  surjective : Function.Surjective φ
  ker_eq : φ.ker = oddCore ↥L
  finrank_eq : Module.finrank (ZMod 3) V = 6
  quadSign_eq : quadSign Q = -1

private lemma eq_of_ne_one_of_card_two {H : Type*} [Group H] (h2 : Nat.card H = 2)
    {a b : H} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  classical
  by_contra hab
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [h2]; norm_num)
  letI := Fintype.ofFinite H
  have hcard : Fintype.card H = 2 := by rw [← Nat.card_eq_fintype_card, h2]
  have h3 : ({1, a, b} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => ha h.symm, fun h => hb h.symm⟩),
        Finset.card_insert_of_notMem (by simpa using hab),
        Finset.card_singleton]
  have hle := Finset.card_le_univ ({1, a, b} : Finset H)
  rw [h3, hcard] at hle
  omega

theorem t5_center_omegaGroup_eq_one_or_pi (hQ : Q.Nondegenerate)
    (hZ : Nat.card (Subgroup.center (omegaGroup hQ)) = 2)
    (hπ : piOrth Q ∈ omegaGroup hQ) (hπ_ne : piOrth Q ≠ 1)
    {x : omegaGroup hQ} (hx : x ∈ Subgroup.center (omegaGroup hQ)) :
    x = 1 ∨ (x : OGroup Q) = piOrth Q := by
  by_cases h1 : x = 1
  · exact Or.inl h1
  · right
    have hπΩ_cent : (⟨piOrth Q, hπ⟩ : omegaGroup hQ) ∈
        Subgroup.center (omegaGroup hQ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp piOrth_mem_center (y : OGroup Q)
    have hπΩ_ne : (⟨piOrth Q, hπ⟩ : omegaGroup hQ) ≠ 1 :=
      fun hh => hπ_ne (Subtype.ext_iff.mp hh)
    have hx_ne : (⟨x, hx⟩ : Subgroup.center (omegaGroup hQ)) ≠ 1 :=
      fun hh => h1 (Subtype.ext_iff.mp hh)
    have hy_ne : (⟨⟨piOrth Q, hπ⟩, hπΩ_cent⟩ :
        Subgroup.center (omegaGroup hQ)) ≠ 1 :=
      fun hh => hπΩ_ne (Subtype.ext_iff.mp hh)
    have heq := eq_of_ne_one_of_card_two hZ hx_ne hy_ne
    have heq2 : x = (⟨piOrth Q, hπ⟩ : omegaGroup hQ) := congrArg Subtype.val heq
    exact congrArg Subtype.val heq2

theorem t5_center_omegaGroup_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) {x : omegaGroup hQ}
    (hx : x ∈ Subgroup.center (omegaGroup hQ)) : x = 1 ∨ (x : OGroup Q) = piOrth Q :=
  t5_center_omegaGroup_eq_one_or_pi hQ (natCard_center_omegaGroup_six_minus hQ hdim hs)
    ((piOrth_mem_omegaGroup_iff hQ).mpr
      ⟨by rw [hdim]; decide, by rw [hs, hdim]; decide⟩)
    (piOrth_ne_one (by rw [hdim]; norm_num)) hx

private theorem oddCentralCover_of_isCoverMap {φ : ↥L →* omegaGroup hQ}
    (h : IsCoverMap L φ) (hL : IsOm6Z2 L) : OddCentralCover φ := by
  have hcen : oddCore ↥L ≤ Subgroup.center ↥L :=
    CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple
      (⟨hL.1.1.commutator_eq_top, hL.1.2.1⟩ : CFSG.Open.IsQuasisimple ↥L)
  refine ⟨h.surjective, ?_, ?_⟩
  · rw [h.ker_eq]; exact hcen
  · rw [h.ker_eq]
    exact CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.odd_card_oddCore

theorem t5_exists_cover (hS : Asc82SchurU43) (hL : IsOm6Z2 L) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate) (φ : ↥L →* omegaGroup hQ),
      IsCoverMap L φ := by
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hs, ⟨f⟩⟩ :=
    isOmegaCover_oddCore_quotient hS hL.1 hL.2
  letI := i1
  letI := i2
  letI := i3
  refine ⟨V, i1, i2, i3, Q, hQ, f.toMonoidHom.comp (QuotientGroup.mk' (oddCore ↥L)), ?_⟩
  refine ⟨f.surjective.comp (QuotientGroup.mk'_surjective _), ?_, hdim, hs⟩
  ext x
  rw [MonoidHom.mem_ker]
  change f (QuotientGroup.mk x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem t5_exists_model (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (h : IsCoverMap L φ) :
    ∃ e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ,
      ∀ l : ↥L, e (QuotientGroup.mk l) = omegaToProj hQ (φ l) := by
  let ψ : ↥L →* omegaProj hQ := (omegaToProj hQ).comp φ
  have hψ : Function.Surjective ψ := (omegaToProj_surjective hQ).comp h.surjective
  have hcen : oddCore ↥L ≤ Subgroup.center ↥L :=
    CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple
      (⟨hL.1.1.commutator_eq_top, hL.1.2.1⟩ : CFSG.Open.IsQuasisimple ↥L)
  have hπ_mem : piOrth Q ∈ omegaGroup hQ :=
    (piOrth_mem_omegaGroup_iff hQ).mpr
      ⟨by rw [h.finrank_eq]; decide, by rw [h.quadSign_eq, h.finrank_eq]; decide⟩
  have hπ_ne : piOrth Q ≠ 1 := piOrth_ne_one (by rw [h.finrank_eq]; norm_num)
  have hZ : Nat.card (Subgroup.center (omegaGroup hQ)) = 2 :=
    natCard_center_omegaGroup_six_minus hQ h.finrank_eq h.quadSign_eq
  have hker : ψ.ker = Subgroup.center ↥L := by
    apply le_antisymm
    · intro l hl
      rw [MonoidHom.mem_ker] at hl
      have hφl_pi : (φ l : OGroup Q) = 1 ∨ (φ l : OGroup Q) = piOrth Q :=
        (omegaToProj_eq_one_iff hQ (φ l)).mp hl
      have hφl_cent : φ l ∈ Subgroup.center (omegaGroup hQ) := by
        rcases hφl_pi with h1 | h1
        · rw [Subgroup.mem_center_iff]
          intro y
          simp [show φ l = 1 from Subtype.ext h1]
        · rw [Subgroup.mem_center_iff]
          intro y
          apply Subtype.ext
          show (y : OGroup Q) * (φ l : OGroup Q) = (φ l : OGroup Q) * (y : OGroup Q)
          rw [h1]
          exact Subgroup.mem_center_iff.mp piOrth_mem_center (y : OGroup Q)
      have hcomm : ∀ m : ↥L, ⁅l, m⁆ ∈ Subgroup.center ↥L := by
        intro m
        apply hcen
        rw [← h.ker_eq, MonoidHom.mem_ker, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hφl_cent (φ m)).symm
      have hmk_center : (QuotientGroup.mk' (Subgroup.center ↥L)) l ∈
        Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) y
        have h1 : ⁅(QuotientGroup.mk' (Subgroup.center ↥L)) l,
            (QuotientGroup.mk' (Subgroup.center ↥L)) m⁆ = 1 := by
          rw [← map_commutatorElement]
          exact (QuotientGroup.eq_one_iff _).mpr (hcomm m)
        exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
      haveI : Group.IsPerfect ↥L := hL.1.1
      have hbot : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
        Group.IsPerfect.center_quotient_center_eq_bot ↥L
      have hmk_one : (QuotientGroup.mk' (Subgroup.center ↥L)) l = 1 := by
        have hmem : (QuotientGroup.mk' (Subgroup.center ↥L)) l ∈
            (⊥ : Subgroup (↥L ⧸ Subgroup.center ↥L)) := by
          rw [← hbot]; exact hmk_center
        simpa using hmem
      exact (QuotientGroup.eq_one_iff l).mp hmk_one
    · intro l hl
      rw [MonoidHom.mem_ker]
      have hφl_cent : φ l ∈ Subgroup.center (omegaGroup hQ) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨x, rfl⟩ := h.surjective y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hl x]
      rcases t5_center_omegaGroup_eq_one_or_pi hQ hZ hπ_mem hπ_ne hφl_cent with h1 | h1
      · change omegaToProj hQ (φ l) = 1
        rw [h1, map_one]
      · change omegaToProj hQ (φ l) = 1
        exact (omegaToProj_eq_one_iff hQ (φ l)).mpr (Or.inr h1)
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ), ?_⟩
  intro l
  change (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    ((QuotientGroup.quotientMulEquivOfEq hker).symm (QuotientGroup.mk l)) = ψ l
  have hA : (QuotientGroup.quotientMulEquivOfEq hker).symm
      (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk l := by
    have h := (QuotientGroup.quotientMulEquivOfEq hker).symm_apply_apply
      (QuotientGroup.mk l : ↥L ⧸ ψ.ker)
    rwa [QuotientGroup.quotientMulEquivOfEq_mk hker l] at h
  rw [hA]
  change (QuotientGroup.kerLift ψ) (QuotientGroup.mk l) = ψ l
  exact QuotientGroup.kerLift_mk ψ l

theorem IsCoverMap.map_central {φ : ↥L →* omegaGroup hQ} (h : IsCoverMap L φ)
    (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2) (ht' : t ∈ L) :
    ((φ ⟨t, ht'⟩ : omegaGroup hQ) : OGroup Q) = piOrth Q := by
  have hw_center : (⟨t, ht'⟩ : ↥L) ∈ Subgroup.center ↥L := by
    obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp ht
    have hxw : x = (⟨t, ht'⟩ : ↥L) := Subtype.ext hxval
    rw [← hxw]
    exact hx
  have hw2 : orderOf (⟨t, ht'⟩ : ↥L) = 2 := by
    rw [Subgroup.orderOf_mk, ht2]
  have hw_sq : (⟨t, ht'⟩ : ↥L) * ⟨t, ht'⟩ = 1 := by
    rw [← pow_two, ← hw2]
    exact pow_orderOf_eq_one _
  have hoc : OddCentralCover φ := oddCentralCover_of_isCoverMap h hL
  have hφw_ne : φ (⟨t, ht'⟩ : ↥L) ≠ 1 := by
    intro h1
    have h1' : (⟨t, ht'⟩ : ↥L) = 1 :=
      hoc.eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr h1) hw_sq
    rw [h1', orderOf_one] at hw2
    exact absurd hw2 (by decide)
  have hφw_cent : φ (⟨t, ht'⟩ : ↥L) ∈ Subgroup.center (omegaGroup hQ) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := h.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw_center x]
  have hπ_mem : piOrth Q ∈ omegaGroup hQ :=
    (piOrth_mem_omegaGroup_iff hQ).mpr
      ⟨by rw [h.finrank_eq]; decide, by rw [h.quadSign_eq, h.finrank_eq]; decide⟩
  have hπ_ne : piOrth Q ≠ 1 := piOrth_ne_one (by rw [h.finrank_eq]; norm_num)
  have hZ : Nat.card (Subgroup.center (omegaGroup hQ)) = 2 :=
    natCard_center_omegaGroup_six_minus hQ h.finrank_eq h.quadSign_eq
  rcases t5_center_omegaGroup_eq_one_or_pi hQ hZ hπ_mem hπ_ne hφw_cent with h1 | h1
  · exact absurd h1 hφw_ne
  · exact h1

theorem IsCoverMap.oddCentralCover {φ : ↥L →* omegaGroup hQ} (h : IsCoverMap L φ)
    (hL : IsOm6Z2 L) : OddCentralCover φ :=
  oddCentralCover_of_isCoverMap h hL

end CFSG.OddStandard.SmallF3.Omega
