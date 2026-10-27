module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1Res
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1E7
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1TwE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1D4

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.E1

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.Foote5.OddLieCore (oddFixed)

theorem e7_innerDiag_exists_component
    (K : Type) [Field K] [Finite K] (hK : Odd (Nat.card K))
    (α : MulAut (adjointGroup .E7 K)) (hα : α ^ 2 = 1)
    (hdiag : ∃ (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ), ∀ h : adjointGroup .E7 K,
      (α h : ModGL .E7 K) = (g : ModGL .E7 K) * rootDiagUnit .E7 a * h *
        (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 K)⁻¹) :
    ∃ X : Subgroup (adjointGroup .E7 K), GorensteinWalter.IsComponentOf X (oddFixed α) := by
  have := Fintype.ofFinite K
  obtain ⟨p, hpc, n, hp, hcard⟩ := FiniteField.card' K
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hK'] at hK
    exact (Nat.not_even_iff_odd.2 hK) ((Nat.even_pow' n.ne_zero).2 even_two)
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  obtain ⟨g, a, hαg⟩ := hdiag
  obtain ⟨D', J', w, h, -⟩ := SR.E1.e7_innerDiag_orbit_component hp2 n.pos hK' hαg hα
  exact ⟨_, h⟩

theorem twisted_inner_exists_component
    (t : TwistTag) (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ t.order)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (x : graphFixedRootGroup t K σ.toRingHom) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ X : Subgroup (graphFixedRootGroup t K σ.toRingHom),
      GorensteinWalter.IsComponentOf X (oddFixed (MulAut.conj x)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hKm : Nat.card K = p ^ (f * t.order) := by rw [hK, ← pow_mul]
  have hord : 1 ≤ t.order := by cases t <;> decide
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) hKm
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  cases t with
  | E6 =>
    obtain ⟨D', J', w, h, -⟩ := SR.E1.twistedE6_orbit_component hp2 hf hK σ hσ hx2
    exact ⟨_, h⟩
  | D4 =>
    have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
    have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := fun c => by
      have := Fintype.ofFinite K
      change σ (σ (σ c)) = c
      rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, show p ^ f * (p ^ f * p ^ f) = (p ^ f) ^ 3 by ring,
        ← hK3, Nat.card_eq_fintype_card, FiniteField.pow_card]
    have hx : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    obtain ⟨c, ψ, -, -, h⟩ := SR.E1.triality_slB_component hp hp2 hf hK3 σ hσ hσ3 hx
    exact ⟨_, h⟩

theorem chevOddInnerInput_holds
    : ChevOddInnerInput := by
  refine ⟨fun K _ _ hK α hα _ hdiag => ?_, fun t p f hp hp2 hf K _ _ hK σ hσ x hx2 hx1 => ?_⟩
  · obtain ⟨X, hX⟩ := e7_innerDiag_exists_component K hK α hα hdiag
    obtain ⟨hXF, hXp, h2⟩ := SR.E1.perfect_even_of_isComponentOf hX
    exact ⟨X, hXF, hXp, h2⟩
  · obtain ⟨X, hX⟩ := twisted_inner_exists_component t p f hp hp2 hf K hK σ hσ x hx2 hx1
    have : Finite (ModGL t.tag K) := finite_modGL
    obtain ⟨hXF, hXp, h2⟩ := SR.E1.perfect_even_of_isComponentOf hX
    exact ⟨X, hXF, hXp, h2⟩

end CFSG.ComponentClassification.HarrisLit.L33.E1
