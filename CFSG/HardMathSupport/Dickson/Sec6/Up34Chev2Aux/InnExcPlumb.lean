module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyE
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace Up34Exc

section Residual


@[expose] def Char2Hrat (τ : Tag) (k : TwistKind) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      twistKind S.ρ (rootCharHom a) i = k →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
      ∃ z : ModGL τ L, z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        (∀ g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, g * z = z * g) ∧
        z ^ 3 = 1 ∧ z ≠ 1

end Residual

section Assembly

set_option linter.unusedSectionVars false


theorem noL34Layer_exc_inner_untw_two {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hI : Char2Hrat τ .inner) (hS : Char2Hrat τ .suN) (hD : Char2Hrat τ .twoD)
    (hE : Char2Hrat τ .exc)
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (β : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup τ (AlgebraicClosure K))
    (hβ : ∀ c, (β c : ModGL τ K) = h * c * h⁻¹) (hp1 : h ^ 3 = 1) (hh1 : h ≠ 1) :
    Up34Chev2.NoL34Layer β := by
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hτ'' : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hτ''' : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := single_edge_perfect τ K hτ''
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have h5K : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    intro h5
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5)
    omega
  have hmon : MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ''' Nat.prime_three
      (by norm_num)
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ' Nat.prime_three h3K Nat.prime_five h5K
      (Or.inl le_rfl) hmon hperf β h hhL hβ hp1 hh1
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure Nat.prime_three h3K
  refine noL34Layer_of_langSetup S Nat.prime_three ι hinj hrange β hconj hT hap h1
    (langSetup_hTame_of_prime S Nat.prime_three h3L (fun h' => absurd h' (by rcases hτ with h | h | h | h <;> simp [h])) hT hap h1) ?_
  intro i hq hL34
  cases hk : twistKind S.ρ (rootCharHom a) i with
  | inner => exact hI _ _ S a hT hap h1 i hk hq hL34
  | suN => exact hS _ _ S a hT hap h1 i hk hq hL34
  | twoD => exact hD _ _ S a hT hap h1 i hk hq hL34
  | exc => exact hE _ _ S a hT hap h1 i hk hq hL34

end Assembly

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
