module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootDefs
public import CFSG.LieType.SeitzGeneration.HyperEx
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoLongRoot
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoLevi

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcWideThree


theorem hyperGen_of_levi_cube (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hr : ringChar K ≠ 3) (hq2 : q ≠ 2)
    {E₀ : Subgroup (twistedE6RootGroup K σ)} (hE₀ : IsElemAbelian 3 E₀)
    (hcard : Nat.card E₀ = 3 ^ 3)
    {X Xm : Subgroup (twistedE6RootGroup K σ)} (hpair : IsTwE6LongRootPair K σ X Xm)
    (hSH : twE6LongRootSL2 X Xm ≤ hyperClosure 3 ⊤ E₀)
    {R : Subgroup (twistedE6RootGroup K σ)} (hRQ : R ≤ twE6LongRootRadical X)
    (hRH : R ≤ hyperClosure 3 ⊤ E₀) (hRX : ¬ R ≤ X)
    (φ : E₀ →* twistedE6RootGroup K σ) (hφ : Function.Injective φ)
    (hφJ : ∀ x, φ x ∈ twE6LongRootLevi X Xm)
    (hφc : ∀ x : E₀, ∀ j ∈ twE6LongRootLevi X Xm,
      (x : twistedE6RootGroup K σ) * j * (x : twistedE6RootGroup K σ)⁻¹ = φ x * j * (φ x)⁻¹) :
    HyperGen 3 ⊤ E₀ := by
  classical
  haveI := hE₀.1
  have hEJ : φ.range ≤ twE6LongRootLevi X Xm := by
    rintro _ ⟨x, rfl⟩
    exact hφJ x
  have hEab : IsElemAbelian 3 φ.range := by
    refine ⟨Subgroup.range_isMulCommutative φ, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h3 : x ^ 3 = 1 := Subtype.ext (by simpa using hE₀.2 _ x.2)
    rw [← map_pow, h3, map_one]
  have hEcard : Nat.card φ.range = 3 ^ 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm.trans hcard
  have hJgen := hyperGen_twE6LongRootLevi K σ q hK hσ hr hq2 hpair hEJ hEab hEcard
  have hcl : hyperClosure 3 (twE6LongRootLevi X Xm) φ.range ≤ hyperClosure 3 ⊤ E₀ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro k ⟨hkJ, F', -, hF'i, hF'c⟩
    refine Subgroup.subset_closure ⟨Subgroup.mem_top k, (F'.comap φ).map E₀.subtype,
      Subgroup.map_subtype_le _, ?_, ?_⟩
    · rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective E₀.subtype_injective, Subgroup.index_comap]
      exact hF'i
    · rintro _ ⟨y, hy, rfl⟩
      have h1 : φ y * k = k * φ y := hF'c (φ y) hy
      have h2 : (y : twistedE6RootGroup K σ) * k * (y : twistedE6RootGroup K σ)⁻¹ = k := by
        rw [hφc y k hkJ, h1, mul_inv_cancel_right]
      change (y : twistedE6RootGroup K σ) * k = k * (y : twistedE6RootGroup K σ)
      calc (y : twistedE6RootGroup K σ) * k
          = (y : twistedE6RootGroup K σ) * k * (y : twistedE6RootGroup K σ)⁻¹ *
              (y : twistedE6RootGroup K σ) := by group
        _ = k * (y : twistedE6RootGroup K σ) := by rw [h2]
  have hJH : twE6LongRootLevi X Xm ≤ hyperClosure 3 ⊤ E₀ :=
    (hyperGen_iff_le.1 hJgen).trans hcl
  exact hyperGen_iff_le.2
    (top_le_iff.2 (eq_top_of_longRoot_le hr hσ hK hpair hSH hJH hRQ hRH hRX))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
