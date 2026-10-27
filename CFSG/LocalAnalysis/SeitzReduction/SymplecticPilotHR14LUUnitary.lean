module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPart
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_centralizer_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (x : X) :
    Nat.card (centralizer ({φ x} : Set Y)) = Nat.card (centralizer ({x} : Set X)) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun z => ?_)).symm
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  change z * x = x * z ↔ φ z * φ x = φ x * φ z
  rw [← map_mul, ← map_mul, φ.injective.eq_iff]

section Unitary

variable {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K')

theorem le_factorization_card_centralizer_primeFormP_one {N : ℕ}
    (y : primeFormP h ((1 : GL (Fin N) K') : Matrix (Fin N) (Fin N) K')) (hy : orderOf y = 2) :
    f * (N / 2 * (N / 2 + 2 * (N % 2))) ≤ (Nat.card (centralizer ({y} : Set
      (primeFormP h ((1 : GL (Fin N) K') : Matrix (Fin N) (Fin N) K'))))).factorization 2 := by
  set ψ := CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv h N
  have h1 := UnitaryPilot.unitaryInnerInvolutionTwoPart_holds h N (ψ y)
    (by rw [MulEquiv.orderOf_eq, hy])
  rwa [card_centralizer_map_mulEquiv] at h1

theorem exists_fieldBar_normal_form_of_factorization_le {N B : ℕ} (hN : 3 ≤ N)
    (hq : ¬(N = 3 ∧ 2 ^ f = 2))
    (hinner : ∀ y : primeFormP h ((1 : GL (Fin N) K') : Matrix (Fin N) (Fin N) K'),
      orderOf y = 2 → B < (Nat.card (centralizer ({y} : Set
        (primeFormP h ((1 : GL (Fin N) K') : Matrix (Fin N) (Fin N) K'))))).factorization 2)
    (hy0 : ∃ y : primeFormP h ((1 : GL (Fin N) K') : Matrix (Fin N) (Fin N) K'), orderOf y = 2)
    {α : MulAut (primeFormP h ((1 : GL (Fin N) K') : Matrix (Fin N) (Fin N) K'))}
    (hαα : α * α = 1) (hle : (Nat.card (fixedSubgroup α)).factorization 2 ≤ B) :
    ∃ (C₀ : GL (Fin N) K') (hC₀ : IsPrimeFormGram C₀),
      ((C₀ : Matrix (Fin N) (Fin N) K') = 1 ∨
        ∃ r, N = 2 * r ∧ (C₀ : Matrix (Fin N) (Fin N) K') = blockSwapJ N r) ∧
      ∃ θ : primeFormP h (C₀ : Matrix (Fin N) (Fin N) K') ≃*
          primeFormP h ((1 : GL (Fin N) K') : Matrix (Fin N) (Fin N) K'),
        α = MulAut.congr θ (primeFormFieldHom h hC₀ (UnitaryPilot.barRingEquiv h)) := by
  have : Finite K' := h.finite
  have : Finite (primeFormP h ((1 : GL (Fin N) K') : Matrix (Fin N) (Fin N) K')) := by
    infer_instance
  have hC : IsPrimeFormGram (1 : GL (Fin N) K') := isPrimeFormGram_one
  by_cases hα1 : α = 1
  · exfalso
    subst hα1
    obtain ⟨y₀, hy₀⟩ := hy0
    have h1 := hinner y₀ hy₀
    have htop : fixedSubgroup (1 : MulAut (primeFormP h
        ((1 : GL (Fin N) K') : Matrix (Fin N) (Fin N) K'))) = ⊤ :=
      eq_top_iff.2 fun y _ => rfl
    rw [htop] at hle
    have h2 := LinearPilot.factorization_two_le_of_dvd
      (Subgroup.card_dvd_of_le (le_top : centralizer ({y₀} : Set _) ≤ ⊤)) Nat.card_pos.ne'
    omega
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hαα) hα1
  obtain ⟨hcases, hinn, -, -⟩ := even_unitary_involution_matrix_lifts h hC hN hq α hα2
  rcases hcases with hid | hbar
  · exfalso
    obtain ⟨s, -, hss, hαs⟩ := hinn hid
    rw [primeFormConjHom_eq_conj] at hαs
    set y : primeFormP h ((1 : GL (Fin N) K') : Matrix (Fin N) (Fin N) K') :=
      QuotientGroup.mk s with hy
    have hy1 : y ≠ 1 := fun h1 => hα1 (by rw [hαs, h1, map_one])
    have hyy : y * y = 1 := by
      rw [hy, ← QuotientGroup.mk_mul]
      have hs1 : s * s = 1 := Subtype.ext hss
      rw [hs1, QuotientGroup.mk_one]
    have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hyy) hy1
    rw [hαs, LinearPilot.fixedSubgroup_mulAut_conj_eq] at hle
    have := hinner y hy2
    omega
  · obtain ⟨-, -, C₀, hC₀, hcase₀, -, -, -, -, ⟨θ, -, hθα⟩, -⟩ :=
      even_unitary_antiunitary_involution_descent h hC hN hq α hα2 hbar
    have hφ : primeFormFieldFactor h hC hN hq α = UnitaryPilot.barRingEquiv h :=
      RingEquiv.ext fun x => by rw [hbar, UnitaryPilot.barRingEquiv_apply]
    refine ⟨C₀, hC₀, hcase₀, θ, MulEquiv.ext fun x => ?_⟩
    rw [hθα x, hφ]
    rfl

end Unitary

end CFSG.SeitzReduction.SymplecticPilot
