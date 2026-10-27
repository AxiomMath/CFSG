module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SympKill
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SympL4Frame
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Cases
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Kill

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank

@[expose] def Surv4Orth {F : Type} [Field F] (α : MulAut (projectiveSL 4 F)) : Prop :=
  (∃ B : GL (Fin 4) F, B * B = 1 ∧ Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 2 ∧
      α = conjAut 4 F B) ∨
    (∃ (A : GL (Fin 4) F) (c : Fˣ), A * A = GeneralLinearGroup.scalar (Fin 4) c ∧
      ¬ IsSquare (c : F) ∧ α = conjAut 4 F A) ∨
    (∃ A : GL (Fin 4) F, α = conjAut 4 F A * dualAut 4 F ∧
      (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A)

theorem genericKill_of_symp_graph_L4 {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (h2 : (2 : F) ≠ 0) (A : GL (Fin 4) F)
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A) :
    GenericKill (projectiveSL 4 F) (conjAut 4 F A * dualAut 4 F) := by
  obtain ⟨ϖ, hfix, hker⟩ := exists_sp4_hom_of_alt_L4 h2 A hA
  exact genericKill_of_sp4_hom _ hp hf hp2 hF ϖ hfix hker

theorem genericKill_or_surv_of_FL4_orth {Y : Type} [Group Y] (hF : FL4 Y) (α : MulAut Y)
    (hα : α * α = 1) :
    GenericKill Y α ∨ ∃ (p f : ℕ) (F : Type) (_ : Field F) (_ : Finite F),
      (p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Odd f ∧ p ^ f % 8 ≠ 1 ∧ Nat.card F = p ^ f) ∧
      ∃ (e : Y ≃* projectiveSL 4 F) (α' : MulAut (projectiveSL 4 F)),
        (∀ x, e (α x) = α' (e x)) ∧ Surv4Orth α' := by
  obtain ⟨p, f, hp, hf, hp2, hq8, hL⟩ := hF
  obtain ⟨F, iF, fF, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hK2 : ringChar F ≠ 2 := by rwa [ringChar.eq F p]
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hfodd : Odd f := by
    by_contra hnot
    obtain ⟨m, rfl⟩ := Nat.not_odd_iff_even.mp hnot
    have hsq : p ^ (m + m) = (p ^ m) ^ 2 := by ring
    rw [hsq] at hq8
    have hm : p ^ m % 2 = 1 := by
      rw [Nat.pow_mod, hpodd]
      simp
    have h8 : ∀ a : ℕ, a % 2 = 1 → a ^ 2 % 8 = 1 := by
      intro a ha
      have := Nat.mod_lt a (by norm_num : 8 > 0)
      interval_cases h : a % 8 <;> simp [Nat.pow_mod, h] <;> omega
    exact hq8 (h8 _ hm)
  have hFodd : Odd (Nat.card F) := by
    rw [hcard, Nat.odd_iff]
    exact Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  have h3 : 3 ≤ Nat.card F := by
    rw [hcard]
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have := Nat.odd_iff.mp hFodd
    omega
  set α' : MulAut (projectiveSL 4 F) := e.symm.trans (α.trans e) with hα'
  have hcomm : ∀ x, e (α x) = α' (e x) := fun x => by simp [hα']
  have hα'2 : α' ^ 2 = 1 := by
    ext s
    obtain ⟨x, rfl⟩ := e.surjective s
    rw [sq, MulAut.mul_apply, ← hcomm, ← hcomm]
    have : α (α x) = x := by
      have := congrArg (fun a : MulAut Y => a x) hα
      simpa using this
    rw [this]
    rfl
  have hdata : p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Odd f ∧ p ^ f % 8 ≠ 1 ∧ Nat.card F = p ^ f :=
    ⟨hp, hp2, hf, hfodd, hq8, hcard⟩
  rcases linear4_involution_cases hp hf hcard hfodd hK2 α' hα'2 with ⟨ρ, hρ, hfix⟩ | hS
  · exact Or.inl (genericKill_of_mulEquiv e α α' hcomm
      (genericKill_of_sl3_block hp2 hFodd h3 α' ρ hρ hfix))
  · rcases hS with hS | hS | ⟨A, hαA, hAt | hAt⟩
    · exact Or.inr ⟨p, f, F, iF, fF, hdata, e, α', hcomm, Or.inl hS⟩
    · exact Or.inr ⟨p, f, F, iF, fF, hdata, e, α', hcomm, Or.inr (Or.inl hS)⟩
    · exact Or.inr ⟨p, f, F, iF, fF, hdata, e, α', hcomm, Or.inr (Or.inr ⟨A, hαA, hAt⟩)⟩
    · rw [hαA] at hcomm
      exact Or.inl (genericKill_of_mulEquiv e α _ hcomm
        (genericKill_of_symp_graph_L4 hp hf hp2 hcard (Ring.two_ne_zero hK2) A hAt))

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
