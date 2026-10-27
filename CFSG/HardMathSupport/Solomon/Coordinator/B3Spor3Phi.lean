module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporExact
public import CFSG.CharacterTheory.Burnside

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.Proving
open scoped commutatorElement

@[expose] def B3Phi (p : ℕ) {G : Type*} [Group G] (C : Subgroup G) : Prop :=
  ⁅GLAPLayer p C, GLAPPrimeCoreOf p C⁆ = ⊥

variable {G G' : Type*} [Group G] [Group G'] {p : ℕ} {C : Subgroup G}

theorem b3Phi_of_comm (h : ∀ J : Subgroup G, GLAPComponent p C J →
    ∀ g ∈ J, ∀ o ∈ GLAPPrimeCoreOf p C, o * g = g * o) : B3Phi p C :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.2
    (sSup_le fun J hJ g hg => Subgroup.mem_centralizer_iff.2 fun o ho => h J hJ g hg o ho)

theorem comm_of_b3Phi (h : B3Phi p C) {J : Subgroup G} (hJ : GLAPComponent p C J) :
    ∀ g ∈ J, ∀ o ∈ GLAPPrimeCoreOf p C, o * g = g * o := by
  intro g hg o ho
  have hgL : g ∈ GLAPLayer p C := (le_sSup hJ : J ≤ GLAPLayer p C) hg
  have h1 : ⁅g, o⁆ ∈ (⊥ : Subgroup G) := h ▸ Subgroup.commutator_mem_commutator hgL ho
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem b3Phi_of_oPrime (h : GLAPPrimeCoreOf p C = ⊥) : B3Phi p C := by
  unfold B3Phi
  rw [h]
  exact Subgroup.commutator_bot_right _

theorem b3Phi_of_solvable [Finite G] (hp : p.Prime) (hC : Group.IsSolvable ↥C) : B3Phi p C := by
  unfold B3Phi
  have hL : GLAPLayer p C = ⊥ := by
    refine le_bot_iff.1 (sSup_le fun J hJ => ?_)
    exfalso
    have hone := hom_eq_one_of_solvable hp hJ (MonoidHom.id ↥C)
    have hJbot : J.subgroupOf C = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have := hone x (Subgroup.mem_subgroupOf.1 hx)
      exact (Subgroup.mem_bot.2 (by simpa using this))
    have hbar : barX p C J ≠ ⊥ := by
      intro h
      have hq : CFSG.Open.IsQuasisimple ↥(barX p C J) := hJ.2.2.1.2.2
      rw [h] at hq
      exact not_isQuasisimple_bot hq
    exact hbar (by rw [barX, hJbot, Subgroup.map_bot])
  rw [hL]
  exact Subgroup.commutator_bot_left _

theorem b3Phi_map_iff [Finite G] [Finite G'] (hp : p.Prime) (φ : G →* G')
    (hφ : Function.Injective φ) : B3Phi p (C.map φ) ↔ B3Phi p C := by
  have hc : ∀ y ∈ C ⊓ φ.ker, ∀ x ∈ C, x * y = y * x := by
    intro y hy x _
    have : y = 1 := hφ ((MonoidHom.mem_ker.1 hy.2).trans (map_one φ).symm)
    rw [this, mul_one, one_mul]
  have hO := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p φ hφ C
  constructor
  · intro h
    refine b3Phi_of_comm fun J hJ g hg o ho => ?_
    have hJ' : GLAPComponent p (C.map φ) (J.map φ) := glaPComponent_map_central hp φ hc hJ
    have := comm_of_b3Phi h hJ' (φ g) ⟨g, hg, rfl⟩ (φ o) (hO ▸ ⟨o, ho, rfl⟩)
    exact hφ (by rw [map_mul, map_mul]; exact this)
  · intro h
    refine b3Phi_of_comm fun J' hJ' g' hg' o' ho' => ?_
    obtain ⟨J, hJ, rfl⟩ := exists_glaPComponent_map_central hp φ hc hJ'
    obtain ⟨g, hg, rfl⟩ := hg'
    obtain ⟨o, ho, rfl⟩ : o' ∈ (GLAPPrimeCoreOf p C).map φ := hO ▸ ho'
    have := comm_of_b3Phi h hJ g hg o ho
    rw [← map_mul, ← map_mul, this]

theorem gLAPPrimeCoreOf_three_eq_bot_of_conj_product [Finite G]
    (h : ∀ w ∈ C, (orderOf w).Prime → orderOf w ≠ 3 →
      ∃ u ∈ C, 3 ∣ orderOf (w * (u * w * u⁻¹))) : GLAPPrimeCoreOf 3 C = ⊥ := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  by_contra hL
  set O := GLAPPrimeCoreOf 3 C with hO
  have hOC : O ≤ C := GLAPPrimeCoreOf_le C
  have hcop : Nat.Coprime 3 (Nat.card O) := coprime_card_GLAPPrimeCoreOf hp3 C
  have hne : Nat.card O ≠ 1 := fun h1 => hL (Subgroup.card_eq_one.1 h1)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  have hq3 : q ≠ 3 := by
    rintro rfl
    exact (Nat.Prime.coprime_iff_not_dvd hp3).1 hcop hqd
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := O) q hqd
  have hxo : orderOf (x : G) = q := by rw [Subgroup.orderOf_coe, hx]
  have hxO : (x : G) ∈ O := x.2
  obtain ⟨u, huC, hu3⟩ := h (x : G) (hOC hxO) (hxo ▸ hq) (hxo ▸ hq3)
  have hconj : u * (x : G) * u⁻¹ ∈ O := GLAPPrimeCoreOf_conj_mem u huC (x : G) hxO
  have hprod : (x : G) * (u * (x : G) * u⁻¹) ∈ O := O.mul_mem hxO hconj
  have hdvd : orderOf ((x : G) * (u * (x : G) * u⁻¹)) ∣ Nat.card O :=
    Subgroup.orderOf_dvd_natCard _ hprod
  exact (Nat.Prime.coprime_iff_not_dvd hp3).1 hcop (hu3.trans hdvd)

theorem b3Phi_of_card_two_primes [Finite G] (hp : p.Prime) {a q b : ℕ} (hq : q.Prime)
    (hpq : p ≠ q) (hcard : Nat.card ↥C = p ^ a * q ^ b) : B3Phi p C := by
  have : Fintype ↥C := Fintype.ofFinite _
  refine b3Phi_of_solvable hp ?_
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)

end CFSG.HardMathSupport.Solomon.Coordinator
