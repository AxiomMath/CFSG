module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FPair
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three

@[expose] def sgnB (b : D4Idx → Bool) (v : D4Vec) : Bool :=
  decide ((∑ i : D4Idx, if b i then (v i).natAbs else 0) % 2 = 1)

@[expose] def orbRep (v : D4Vec) : Prop := v 0 ≥ v 1 ∧ v 1 ≥ v 3

instance (v : D4Vec) : Decidable (orbRep v) := by unfold orbRep; infer_instance

theorem simple_of_height_one :
    ∀ v ∈ d4RootsFrom 1, height v = 1 → ∃ i : D4Idx, v = rA i := by decide +kernel

theorem decomp_of_height_gt_one :
    ∀ b : D4Idx → Bool, ∀ v ∈ d4RootsFrom 1, 1 < height v →
      ∃ i : D4Idx, v - rA i ∈ d4RootsFrom 1 ∧ sgnB b v = xor (sgnB b (v - rA i)) (b i) := by
  decide +kernel

theorem sgnB_rA : ∀ (b : D4Idx → Bool) (i : D4Idx), sgnB b (rA i) = b i := by decide +kernel

theorem sgn_count_le :
    ∀ b : D4Idx → Bool, (∃ i, b i = true) →
      ((d4RootsFrom 1).filter fun v => sgnB b v = false).card ≤ 6 := by decide +kernel

theorem sgn_orbit_count_le :
    ∀ b : D4Idx → Bool, (∃ i, b i = true) → b 0 = b 1 → b 1 = b 3 →
      ((d4RootsFrom 1).filter fun v => orbRep v ∧ sgnB b v = false).card ≤ 2 := by
  decide +kernel

theorem orbRep_meets :
    ∀ v ∈ d4RootsFrom 1, ∀ m ∈ ({2, 4} : Finset ℕ), orbRep v ∨ orbRep (permLattice (d4Rho ^ m) v) ∨
      orbRep (permLattice (d4Rho ^ m) (permLattice (d4Rho ^ m) v)) := by decide +kernel

section Table

variable {K : Type} [Field K]


structure SignData (s : D4Vec → K) : Prop where
  sq : ∀ v ∈ d4RootsFrom 1, s v * s v = 1
  add : ∀ γ ∈ d4RootsFrom 1, ∀ δ ∈ d4RootsFrom 1, γ + δ ∈ d4RootsFrom 1 → s (γ + δ) = s γ * s δ

theorem signData_table (hK : (-1 : K) ≠ 1) {s : D4Vec → K} (hs : SignData s) :
    ∃ b : D4Idx → Bool, ∀ v ∈ d4RootsFrom 1, s v = if sgnB b v then -1 else 1 := by
  classical
  have hpm : ∀ v ∈ d4RootsFrom 1, s v = 1 ∨ s v = -1 := by
    intro v hv
    have h := hs.sq v hv
    have : (s v - 1) * (s v + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · exact Or.inl (sub_eq_zero.1 h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
  have hsimple : ∀ i : D4Idx, rA i ∈ d4RootsFrom 1 := by decide +kernel
  set b : D4Idx → Bool := fun i => decide (s (rA i) = -1) with hb
  have hbs : ∀ i : D4Idx, s (rA i) = if b i then -1 else 1 := by
    intro i
    rcases hpm _ (hsimple i) with h | h
    · have : b i = false := by simp [hb, h, hK.symm]
      simp [this, h]
    · have : b i = true := by simp [hb, h]
      simp [this, h]
  refine ⟨b, ?_⟩
  have key : ∀ n : ℕ, ∀ v ∈ d4RootsFrom 1, (height v).toNat = n →
      s v = if sgnB b v then -1 else 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv hn
      have hpos : 0 < height v := (mem_d4RootsFrom.1 hv).2.1
      by_cases h1 : height v = 1
      · obtain ⟨i, rfl⟩ := simple_of_height_one v hv h1
        rw [hbs i, sgnB_rA]
      · have h2 : 1 < height v := by omega
        obtain ⟨i, hvi, hx⟩ := decomp_of_height_gt_one b v hv h2
        have hlt : (height (v - rA i)).toNat < n := by
          have hh : height (v - rA i) = height v - 1 := by
            have : height v = height (v - rA i) + height (rA i) := by
              rw [← d4_height_add]; simp
            have h3 : height (rA i) = 1 := height_rA i
            omega
          rw [hh]; omega
        have ih' := ih _ hlt (v - rA i) hvi rfl
        have hadd := hs.add (v - rA i) hvi (rA i) (hsimple i) (by rw [sub_add_cancel]; exact hv)
        have e : v - rA i + rA i = v := by simp
        rw [e] at hadd
        rw [hadd, ih', hbs i, hx]
        cases sgnB b (v - rA i) <;> cases b i <;> simp
  exact fun v hv => key _ v hv rfl

end Table

end CFSG.LocalAnalysis.GLTheoremA
