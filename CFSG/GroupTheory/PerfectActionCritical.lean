module

public import CFSG.Quasithin.Background.SmithD37Fix
public import CFSG.RankThree.PartTwo.Sec3.SectionModuleBound
public import CFSG.LocalAnalysis.SteinbergCCCyclicNormalCommutatorCentralizes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128ClPerf

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {H A Q : Type*}

theorem map_eq_bot_of_isPerfect_of_isCyclicTarget [Group H] [Group A] [IsCyclic A]
    (φ : H →* MulAut A) {P : Subgroup H} (hP : ⁅P, P⁆ = P) : P.map φ = ⊥ :=
  (Subgroup.map_eq_bot_iff _).mpr
    (CFSG.OddStandard.SmallF3.Omega.sec128_perfect_le_ker
      (fun a b => (IsCyclic.mulAutMulEquiv (G := A)).injective (by simp [mul_comm])) P hP φ)

theorem map_eq_bot_of_isPerfect_of_le_fixingSubgroup [Group H] [Group Q] [Finite Q]
    {q : ℕ} [Fact q.Prime] (φ : H →* MulAut Q) (D : Subgroup Q)
    (hfix : IsPGroup q (fixingSubgroup (MulAut Q) (D : Set Q)))
    {P : Subgroup H} (hP : ⁅P, P⁆ = P)
    (hPD : P.map φ ≤ fixingSubgroup (MulAut Q) (D : Set Q)) : P.map φ = ⊥ := by
  have : Group.IsPerfect ↥(P.map φ) := isPerfect_iff.mpr (by rw [← map_commutator, hP])
  have : Group.IsNilpotent ↥(P.map φ) := (hfix.to_le hPD).isNilpotent
  by_contra hne
  have : Nontrivial ↥(P.map φ) := (nontrivial_iff_ne_bot _).2 hne
  exact Group.IsPerfect.not_isNilpotent ↥(P.map φ) ‹_›

theorem le_centralizer_of_isPerfect_of_card_eq_sq [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    {P C W : Subgroup Q} [C.Normal] [hWn : W.Normal] (hP : ⁅P, P⁆ = P)
    (hC : Nat.card C = q ^ 2) (hWC : W ≤ C) (hW : Nat.card W = q) :
    P ≤ centralizer (C : Set Q) := by
  haveI : IsCyclic W := isCyclic_of_prime_card hW
  let Wq : Subgroup C := W.subgroupOf C
  haveI hWqnormal : Wq.Normal := hWn.subgroupOf C
  have hquotcard : Nat.card (C ⧸ Wq) = q := by
    have h := card_eq_card_quotient_mul_card_subgroup Wq
    rw [hC, Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv, hW] at h
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : q.Prime).pos (by rw [← h]; ring)
  haveI : IsCyclic (C ⧸ Wq) := isCyclic_of_prime_card hquotcard
  letI : CommGroup C := IsPGroup.commGroupOfCardEqPrimeSq hC
  let φ : Q →* MulAut C := MulAut.conjNormal (H := C)
  haveI : Group.IsPerfect ↥(P.map φ) := isPerfect_iff.mpr (by rw [← map_commutator, hP])
  have hWcent : P ≤ centralizer (W : Set Q) :=
    CFSG.LocalAnalysis.CyclicNormalConj.le_centralizer_of_perfect inferInstance hP
  have hfixW : Wq ≤ CFSG.Quasithin.fixV (P.map φ) := by
    intro w hw
    rw [CFSG.Quasithin.mem_fixV]
    rintro _ ⟨x, hx, rfl⟩
    apply Subtype.ext
    change (((MulAut.conjNormal (H := C) x) w : C) : Q) = (w : Q)
    rw [MulAut.conjNormal_apply,
      ← mem_centralizer_iff.mp (hWcent hx) _ (mem_subgroupOf.mp hw), mul_inv_cancel_right]
  have hdisp : ∀ l ∈ P.map φ, ∀ u : C, l u * u⁻¹ ∈ Wq := by
    rintro _ ⟨x, hx, rfl⟩ u
    let ψ : Q →* MulAut (C ⧸ Wq) := CFSG.RankThree.PartTwo.Sec3.sectionAction C W
    have h1 : ψ x = 1 := by
      have hmem : ψ x ∈ P.map ψ := mem_map_of_mem ψ hx
      rwa [map_eq_bot_of_isPerfect_of_isCyclicTarget ψ hP] at hmem
    have h2 := congrArg (fun e : MulAut (C ⧸ Wq) => e (QuotientGroup.mk u)) h1
    rw [CFSG.RankThree.PartTwo.Sec3.sectionAction_mk] at h2
    have h3 : ((MulAut.conjNormal (H := C) x) u)⁻¹ * u ∈ Wq := (QuotientGroup.eq).1 h2
    have h4 : u⁻¹ * ((MulAut.conjNormal (H := C) x) u) ∈ Wq := by
      simpa [mul_inv_rev, inv_inv] using Wq.inv_mem h3
    simpa [mul_assoc] using
      hWqnormal.conj_mem (u⁻¹ * ((MulAut.conjNormal (H := C) x) u)) h4
        ((MulAut.conjNormal (H := C) x) u)
  have htriv := CFSG.Quasithin.SmithD37.trivial_of_perfect (L := P.map φ) (C := Wq) hfixW hdisp
  intro x hx
  rw [mem_centralizer_iff]
  intro c hc
  have h : x * c * x⁻¹ = c := by
    have h0 := congrArg Subtype.val (htriv (φ x) (mem_map_of_mem φ hx) ⟨c, hc⟩)
    rwa [MulAut.conjNormal_apply] at h0
  calc c * x = x * c * x⁻¹ * x := by rw [h]
    _ = x * c := by group

end CFSG.GroupTheory
