module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Concl

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6

@[expose] def E6Model165At (m : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n p q : ℕ), Nat.card F = 2 ^ n → 2 ≤ n →
    p.Prime → p ≠ 2 → rk2Ord p n = m → q.Prime → q ≠ 2 → q ≠ p →
    (q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3) →
    letI : Finite ↥(e6Data_valid.minGroup F) :=
      CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
    ∀ Ã : Subgroup ↥(e6Data_valid.minGroup F), IsElemAbelian p Ã →
      (∀ g ∈ Subgroup.centralizer (Ã : Set ↥(e6Data_valid.minGroup F)),
        orderOf g = p → g ∈ Ã) →
      CFSG.Open.pRank p (⊤ : Subgroup ↥(e6Data_valid.minGroup F)) ≤ CFSG.Open.pRank p Ã →
      3 ≤ CFSG.Open.pRank p Ã →
      Concl165Avoid ↥(e6Data_valid.minGroup F) p q Ã
        (Subgroup.center ↥(e6Data_valid.minGroup F))

@[expose] def TwE6Model165At (m : ℕ) : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] (n p q : ℕ) (θ : k →+* k),
    Nat.card k = (2 ^ n) ^ 2 → (∀ c, θ c = c ^ (2 ^ n)) → 2 ≤ n →
    p.Prime → p ≠ 2 → rk2Ord p n = m → q.Prime → q ≠ 2 → q ≠ p → q ∣ 2 ^ n + 1 →
    letI : Finite ↥(e6Data_valid.minGroup k) :=
      CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid k
    ∀ Ã : Subgroup ↥(fixedGroup k θ), IsElemAbelian p Ã →
      (∀ g ∈ Subgroup.centralizer (Ã : Set ↥(fixedGroup k θ)), orderOf g = p → g ∈ Ã) →
      CFSG.Open.pRank p (⊤ : Subgroup ↥(fixedGroup k θ)) ≤ CFSG.Open.pRank p Ã →
      3 ≤ CFSG.Open.pRank p Ã →
      Concl165Avoid ↥(fixedGroup k θ) p q Ã (Subgroup.center ↥(fixedGroup k θ))

@[expose] def E7Model165At (m : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n p q : ℕ), Nat.card F = 2 ^ n → 1 ≤ n →
    p.Prime → p ≠ 2 → rk2Ord p n = m → q.Prime → q ≠ 2 → q ≠ p →
    (q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3) →
    ∀ Ã : Subgroup ↥(adjointGroup Tag.E7 F), IsElemAbelian p Ã →
      (∀ g ∈ Subgroup.centralizer (Ã : Set ↥(adjointGroup Tag.E7 F)),
        orderOf g = p → g ∈ Ã) →
      CFSG.Open.pRank p (⊤ : Subgroup ↥(adjointGroup Tag.E7 F)) ≤ CFSG.Open.pRank p Ã →
      3 ≤ CFSG.Open.pRank p Ã → Concl165 ↥(adjointGroup Tag.E7 F) p q Ã

@[expose] def E8Model165At (m : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n p q : ℕ), Nat.card F = 2 ^ n → 1 ≤ n →
    p.Prime → p ≠ 2 → rk2Ord p n = m → q.Prime → q ≠ 2 → q ≠ p →
    (q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3) →
    ∀ Ã : Subgroup ↥(adjointGroup Tag.E8 F), IsElemAbelian p Ã →
      (∀ g ∈ Subgroup.centralizer (Ã : Set ↥(adjointGroup Tag.E8 F)),
        orderOf g = p → g ∈ Ã) →
      CFSG.Open.pRank p (⊤ : Subgroup ↥(adjointGroup Tag.E8 F)) ≤ CFSG.Open.pRank p Ã →
      3 ≤ CFSG.Open.pRank p Ã → Concl165 ↥(adjointGroup Tag.E8 F) p q Ã

end CFSG.LocalAnalysis.GLTheoremA.Y10F
