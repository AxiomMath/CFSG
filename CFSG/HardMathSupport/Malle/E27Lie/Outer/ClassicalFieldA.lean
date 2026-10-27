module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
public import CFSG.Quasithin.EmptyFaithful.S146zMListCl
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnFieldAut

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne

theorem exists_fixed_perfect_three_of_semilinear {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (ζ : MulAut (LinearFlag.projectiveSL n K)) (hζ3 : ζ ^ 3 = 1)
    (hζ : ζ ∈ LinearFlag.semilinearAutGroup n K) (hζD : ζ ∉ LinearFlag.linearAutGroup n K) :
    ∃ D : Subgroup (LinearFlag.projectiveSL n K), (∀ x ∈ D, ζ x = x) ∧ ⁅D, D⁆ = D ∧
      3 ∣ Nat.card D := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hζ1 : ζ ≠ 1 := fun h1 => hζD (h1 ▸ one_mem _)
  have hord : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  obtain ⟨-, σ, -, ⟨h, hh, hζeq⟩, -⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      hℓ hf hn hK Nat.prime_three ζ hζ hζD hord
  obtain ⟨H, rfl⟩ := LinearFlag.mem_linearAutGroup_iff.mp hh
  let j := linearSubfieldInclusion n (semilinearFixedSubfield σ)
  have hσfix : ∀ c ∈ semilinearFixedSubfield σ, σ c = c := fun c hc =>
    RingHom.mem_eqLocusField.mp hc
  have hmem : ∀ x : LinearFlag.projectiveSL n (semilinearFixedSubfield σ),
      ζ ((LinearFlag.conjAut n K H) (j x)) = (LinearFlag.conjAut n K H) (j x) := by
    intro x
    rw [hζeq]
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    exact congrArg _ (fieldAut_linearSubfieldInclusion hσfix x)
  let φ : LinearFlag.projectiveSL n (semilinearFixedSubfield σ) →* LinearFlag.projectiveSL n K :=
    (LinearFlag.conjAut n K H).toMonoidHom.comp j
  have hφinj : Function.Injective φ := fun a b hab =>
    linearSubfieldInclusion_injective (by omega) _ ((LinearFlag.conjAut n K H).injective hab)
  have := KCLinearSubfield.isSimpleGroup_projectiveSL (n := n)
    (K := semilinearFixedSubfield σ) hn
  have hnc := KCLinearSubfield.not_commutative_projectiveSL (n := n)
    (K := semilinearFixedSubfield σ) hn
  let eD : LinearFlag.projectiveSL n (semilinearFixedSubfield σ) ≃* φ.range :=
    MonoidHom.ofInjective hφinj
  have hDsimple : IsSimpleGroup φ.range := eD.symm.isSimpleGroup
  have hDnc : ¬ ∀ x y : φ.range, x * y = y * x := fun h => hnc fun x y =>
    eD.injective (by rw [map_mul, map_mul]; exact h _ _)
  refine ⟨φ.range, ?_,
    CFSG.GH74.GLS.Stage2.Bender.Thm1.commutator_eq_self_of_simple _ hDsimple hDnc, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hmem x
  · rw [← Nat.card_congr eD.toEquiv]
    have h3 := CFSG.Quasithin.three_dvd_card_psl (K := semilinearFixedSubfield σ) (by omega : 2 ≤ n)
    rwa [← Nat.card_congr (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj n
      (semilinearFixedSubfield σ)).toEquiv] at h3

end CFSG.HardMathSupport.Malle.E27Lie
