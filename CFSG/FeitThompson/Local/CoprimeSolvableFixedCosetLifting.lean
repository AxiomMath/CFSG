module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise SemidirectProduct

variable {A V : Type*} [Group A] [Group V] {ρ : A →* MulAut V} {N : Subgroup V}

def IsInvariantSubgroup.twistedInr (hN : IsInvariantSubgroup ρ N) {v : V}
    (hv : ∀ b : A, v⁻¹ * ρ b v ∈ N) : A →* (↥N ⋊[hN.restrictAut] A) where
  toFun b := ⟨⟨v⁻¹ * ρ b v, hv b⟩, b⟩
  map_one' := by
    refine SemidirectProduct.ext ?_ rfl
    ext
    simp
  map_mul' b c := by
    refine SemidirectProduct.ext ?_ rfl
    ext
    simp only [SemidirectProduct.mul_left, Subgroup.coe_mul, hN.coe_restrictAut_apply, map_mul,
      MulAut.mul_apply, map_inv]
    group

@[simp]
theorem IsInvariantSubgroup.coe_twistedInr_left (hN : IsInvariantSubgroup ρ N) {v : V}
    (hv : ∀ b : A, v⁻¹ * ρ b v ∈ N) (b : A) :
    ((hN.twistedInr hv b).left : V) = v⁻¹ * ρ b v := (rfl)

@[simp]
theorem IsInvariantSubgroup.twistedInr_right (hN : IsInvariantSubgroup ρ N) {v : V}
    (hv : ∀ b : A, v⁻¹ * ρ b v ∈ N) (b : A) : (hN.twistedInr hv b).right = b := (rfl)

theorem IsInvariantSubgroup.twistedInr_injective (hN : IsInvariantSubgroup ρ N) {v : V}
    (hv : ∀ b : A, v⁻¹ * ρ b v ∈ N) : Function.Injective (hN.twistedInr hv) := fun b c h => by
  simpa using congrArg SemidirectProduct.right h

theorem IsInvariantSubgroup.mem_twistedInr_range_iff (hN : IsInvariantSubgroup ρ N) {v : V}
    (hv : ∀ b : A, v⁻¹ * ρ b v ∈ N) (x : ↥N ⋊[hN.restrictAut] A) :
    x ∈ (hN.twistedInr hv).range ↔ ((x.left : V) = v⁻¹ * ρ x.right v) := by
  refine ⟨fun ⟨b, hb⟩ => by rw [← hb]; simp, fun h => ⟨x.right, ?_⟩⟩
  refine SemidirectProduct.ext ?_ rfl
  exact Subtype.ext (by rw [hN.coe_twistedInr_left hv, h])

section Hall

variable (hN : IsInvariantSubgroup ρ N) [Finite A] [Finite V]

instance instFiniteSemidirectProductRestrictAut : Finite (↥N ⋊[hN.restrictAut] A) :=
  Finite.of_equiv _ equivProd.symm

omit [Finite V] in
theorem isHallSubgroup_of_natCard_eq {S : Subgroup (↥N ⋊[hN.restrictAut] A)}
    (hcop : (Nat.card A).Coprime (Nat.card ↥N)) (hS : Nat.card ↥S = Nat.card A) :
    IsHallSubgroup ((Nat.card A).primeFactors : Set ℕ) S := by
  have hidx : S.index = Nat.card ↥N := by
    have h := Subgroup.card_mul_index S
    rw [hS, SemidirectProduct.card, mul_comm (Nat.card ↥N)] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  refine ⟨isPiNumber_iff.2 fun p hp => by rwa [hS] at hp, isPiNumber_iff.2 fun p hp hp' => ?_⟩
  rw [hidx] at hp
  rw [Finset.mem_coe] at hp'
  exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne'
    (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp')
      (Nat.dvd_of_mem_primeFactors hp)))

end Hall

section Main

variable [Finite A] [Finite V] [Group.IsSolvable A]

theorem exists_mem_forall_apply_mul_eq [Group.IsSolvable ↥N] (hN : IsInvariantSubgroup ρ N)
    (hcop : (Nat.card A).Coprime (Nat.card V)) {v : V}
    (hv : ∀ b : A, v⁻¹ * ρ b v ∈ N) : ∃ n ∈ N, ∀ b : A, ρ b (v * n) = v * n := by
  have hcopN : (Nat.card A).Coprime (Nat.card ↥N) :=
    hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card N)
  set X := ↥N ⋊[hN.restrictAut] A with hX
  have hXsolv : Group.IsSolvable X :=
    Group.isSolvable_of_ker_le_range (inl : ↥N →* X) (rightHom : X →* A)
      (le_of_eq range_inl_eq_ker_rightHom.symm)
  set S : Subgroup X := (hN.twistedInr hv).range with hS
  set T : Subgroup X := (inr : A →* X).range with hT
  have hScard : Nat.card ↥S = Nat.card A :=
    Nat.card_congr (MonoidHom.ofInjective (hN.twistedInr_injective hv)).toEquiv.symm
  have hTcard : Nat.card ↥T = Nat.card A :=
    Nat.card_congr (MonoidHom.ofInjective (inr_injective (φ := hN.restrictAut))).toEquiv.symm
  obtain ⟨g, hg⟩ := exists_conj_smul_eq_of_isHallSubgroup
    (isHallSubgroup_of_natCard_eq hN hcopN hTcard)
    (isHallSubgroup_of_natCard_eq hN hcopN hScard)
  refine ⟨(g.left : V), g.left.2, fun b => ?_⟩
  set c : A := g.right⁻¹ * b * g.right with hc
  set y : X := g * inr c * g⁻¹ with hy
  have hyS : y ∈ S := by
    rw [← hg, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
      hy]
    rw [show g⁻¹ * (g * inr c * g⁻¹) * g = inr c by group]
    exact ⟨c, rfl⟩
  have hyright : y.right = b := by
    rw [hy, SemidirectProduct.mul_right, SemidirectProduct.mul_right, right_inr, inv_right, hc]
    group
  have hyleft : (y.left : V) = (g.left : V) * (ρ b (g.left : V))⁻¹ := by
    rw [hy, SemidirectProduct.mul_left, SemidirectProduct.mul_left, left_inr,
      SemidirectProduct.mul_right, right_inr, inv_left, Subgroup.coe_mul, Subgroup.coe_mul,
      hN.coe_restrictAut_apply, hN.coe_restrictAut_apply, hN.coe_restrictAut_apply,
      OneMemClass.coe_one, map_one, mul_one, ← MulAut.mul_apply, ← map_mul, hc,
      show g.right * (g.right⁻¹ * b * g.right) * g.right⁻¹ = b by group, InvMemClass.coe_inv,
      map_inv]
  rw [hS, hN.mem_twistedInr_range_iff hv, hyright, hyleft] at hyS
  have h3 : v * (g.left : V) * (ρ b (g.left : V))⁻¹ = v * (v⁻¹ * ρ b v) := by
    rw [mul_assoc, hyS]
  have h2 : ρ b v = v * (g.left : V) * (ρ b (g.left : V))⁻¹ := by rw [h3]; group
  rw [map_mul, h2]
  group

variable [N.Normal]

theorem fixedPoints_quotientAut_range_of_isSolvable_subgroup [Group.IsSolvable ↥N]
    (hN : IsInvariantSubgroup ρ N) (hcop : (Nat.card A).Coprime (Nat.card V)) :
    FixedPoints.subgroup hN.quotientAut.range (V ⧸ N)
      = (FixedPoints.subgroup ρ.range V).map (QuotientGroup.mk' N) := by
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [mem_fixedPoints_range_iff] at hx
    induction x using QuotientGroup.induction_on with
    | H v =>
      have hv : ∀ b : A, v⁻¹ * ρ b v ∈ N := by
        intro b
        have h := hx b
        rw [hN.quotientAut_mk] at h
        exact QuotientGroup.eq.1 h.symm
      obtain ⟨n, hnN, hfix⟩ := exists_mem_forall_apply_mul_eq hN hcop hv
      refine ⟨v * n, (mem_fixedPoints_range_iff ρ).2 hfix, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
      simpa using N.inv_mem hnN
  · rw [Subgroup.map_le_iff_le_comap]
    intro v hv
    rw [mem_fixedPoints_range_iff ρ] at hv
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, mem_fixedPoints_range_iff]
    intro b
    rw [hN.quotientAut_mk, hv b]

theorem fixedPoints_quotientAut_range [Group.IsSolvable V] (hN : IsInvariantSubgroup ρ N)
    (hcop : (Nat.card A).Coprime (Nat.card V)) :
    FixedPoints.subgroup hN.quotientAut.range (V ⧸ N)
      = (FixedPoints.subgroup ρ.range V).map (QuotientGroup.mk' N) :=
  fixedPoints_quotientAut_range_of_isSolvable_subgroup hN hcop

theorem fixedPoints_quotientAut_range_eq_map_sup [Group.IsSolvable V]
    (hN : IsInvariantSubgroup ρ N) (hcop : (Nat.card A).Coprime (Nat.card V)) :
    FixedPoints.subgroup hN.quotientAut.range (V ⧸ N)
      = (FixedPoints.subgroup ρ.range V ⊔ N).map (QuotientGroup.mk' N) := by
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
    fixedPoints_quotientAut_range hN hcop]

theorem exists_mem_fixedPoints_range_mk_eq [Group.IsSolvable V] (hN : IsInvariantSubgroup ρ N)
    (hcop : (Nat.card A).Coprime (Nat.card V)) {x : V ⧸ N}
    (hx : ∀ b : A, hN.quotientAut b x = x) :
    ∃ v ∈ FixedPoints.subgroup ρ.range V, (v : V ⧸ N) = x := by
  have h : x ∈ (FixedPoints.subgroup ρ.range V).map (QuotientGroup.mk' N) := by
    rw [← fixedPoints_quotientAut_range hN hcop, mem_fixedPoints_range_iff]
    exact hx
  obtain ⟨v, hv, hvx⟩ := h
  exact ⟨v, hv, hvx⟩

end Main

end CFSG.FeitThompson
