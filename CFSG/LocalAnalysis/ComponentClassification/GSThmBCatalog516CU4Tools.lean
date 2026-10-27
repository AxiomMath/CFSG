module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4U4Cover
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CL4Diag
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowSupport

public section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open CFSG.ComponentClassification.CatFactsL4U4

variable {Y : Type} [Group Y] {p f : ℕ} {K : Type} [Field K]

theorem barAut_fixed_of_congr {P : Type*} [Group P] (e : Y ⧸ center Y ≃* P) (α : MulAut Y)
    {β : MulAut P} (hα' : MulAut.congr e (barAut α) = β) {y : P} (hy : β y = y) :
    barAut α (e.symm y) = e.symm y := by
  have h := congrArg (fun φ : MulAut P => φ y) hα'
  simp only [MulAut.congr_apply, MulEquiv.trans_apply] at h
  rw [hy] at h
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  exact h

theorem congr_conj {P : Type*} [Group P] (e : Y ⧸ center Y ≃* P) (x : Y ⧸ center Y) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem outer_of_congr {P : Type*} [Group P] (e : Y ⧸ center Y ≃* P) (α : MulAut Y)
    {β : MulAut P} (hα' : MulAut.congr e (barAut α) = β) (hout : ∀ y, β ≠ MulAut.conj y) :
    ∀ x, barAut α ≠ MulAut.conj x := fun x hx =>
  hout (e x) (by rw [← hα', hx, congr_conj])

theorem four_dvd_range {G H : Type*} [Group G] [Group H] [Finite H] {ρ : G →* H} {q : ℕ}
    (hgood : Group.IsPerfect G ∨
      (q = 3 ∧ ∃ S : Set G, closure S = ⊤ ∧ ∀ s ∈ S, Odd (orderOf s)))
    (h2 : 2 ∣ Nat.card ρ.range) : 4 ∣ Nat.card ρ.range := by
  rcases hgood with hP | ⟨-, S, hS, hSo⟩
  · exact four_dvd_card_of_perfect (range_perfect ρ) h2
  · have hr : ρ.range = closure (ρ '' S) := by
      rw [MonoidHom.range_eq_map, ← hS, MonoidHom.map_closure]
    rw [hr] at h2 ⊢
    refine four_dvd_card_closure_odd ?_ h2
    rintro _ ⟨s, hs, rfl⟩
    exact Odd.of_dvd_nat (hSo s hs) (orderOf_map_dvd ρ s)

theorem two_dvd_range {G H : Type*} [Group G] [Group H] [Finite H] (ρ : G →* H) {x : G}
    {n : ℕ} (hx : orderOf (ρ x) = n) (hn : 2 ∣ n) : 2 ∣ Nat.card ρ.range := by
  have hmem : ρ x ∈ ρ.range := ⟨x, rfl⟩
  have := orderOf_dvd_natCard (⟨_, hmem⟩ : ρ.range)
  rw [Subgroup.orderOf_mk, hx] at this
  exact hn.trans this

theorem exists_cover_U4 [Finite Y] [Group.IsPerfect Y] (hZ : Nat.card (center Y) = 2)
    (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    (e₀ : Y ⧸ center Y ≃* Assembly.LowTwoRank.StatedProj
      (Assembly.LowTwoRank.StatedSU 4 (p ^ f) K))
    {R : Matrix (Fin (2 * 2 + 0)) (HypIndex 2 0) K} (hR : IsHypTransport h R) :
    ∃ σ : hypSU h 2 0 →* Y, Function.Injective σ ∧ ∀ g,
      piZ (σ g) = (e₀.trans (hypPSUEquivStatedProj h hR (Nat.le_of_ble_eq_true rfl)).symm).symm
        (hypProj h 2 0 g) := by
  have hZ2 : IsPGroup 2 (center Y) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have hZ1 : center Y ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hZ
    exact absurd hZ (by norm_num)
  obtain ⟨ψ, hψ⟩ := exists_equiv_statedSU_four hZ2 hZ1 h hp2 hq e₀
  refine ⟨ψ.symm.toMonoidHom.comp (hypTransport h hR).toMonoidHom,
    ψ.symm.injective.comp (hypTransport h hR).injective, fun g => ?_⟩
  rw [MulEquiv.symm_trans_apply, MulEquiv.symm_symm, hypPSUEquivStatedProj_hypProj]
  apply e₀.injective
  rw [MulEquiv.apply_symm_apply]
  change e₀ (QuotientGroup.mk (ψ.symm (hypTransport h hR g))) = _
  rw [hψ, MulEquiv.apply_symm_apply]

theorem perfect_SU3 (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    Group.IsPerfect (unitarySU p f K 3) :=
  (GH74.Generic.S45.isPerfect_and_center_unitarySU' h hp2 le_rfl).1

theorem perfect_SL2_sq (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    Group.IsPerfect (SpecialLinearGroup (Fin 2) K) := by
  have := h.finite
  have h3 : p ^ (2 * f) ≠ 3 := by
    intro h3
    have hq : (p ^ f) ^ 2 = 3 := by rw [← pow_mul, mul_comm, h3]
    have h1 : 1 < p ^ f := Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt
    nlinarith
  exact LinearGroups.special_linear_dimension_two_perfect
    (exists_finset_four h.prime hp2 h.card h3)

end CFSG.ComponentClassification.GSThmB.Cent516
