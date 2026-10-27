module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

variable {X : Type} [Group X]

namespace SwapP2

theorem pPrimeCore_map_le_of_isSubnormal [Finite X] {C J : Subgroup X} (hJC : J ≤ C)
    (hsub : (J.subgroupOf C).IsSubnormal) :
    (pPrimeCore 2 J).map J.subtype ≤ (pPrimeCore 2 C).map C.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 (J.subgroupOf C) hsub
  let φ : J.subgroupOf C ≃* J := subgroupOfEquivOfLe hJC
  rw [← pPrimeCore_map_iso 2 φ, h1]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨(x : C), hx, rfl⟩

theorem false_of_le_coreActionKernel [Finite X] {L P : Subgroup X} (hPperf : ⁅P, P⁆ = P)
    (hPq : Nontrivial (↥P ⧸ pPrimeCore 2 ↥P)) (hPL : P ≤ L)
    (hPK : P ≤ UnbalancedLayer.coreActionKernel L) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPO : P ≤ (pPrimeCore 2 ↥L).map L.subtype := by
    rw [← hPperf, commutator_le]
    intro x hx y hy
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem (hPK hy))).2 x⁻¹
      (inv_mem (hPL hx))
    rw [inv_inv, inv_inv] at h1
    rw [commutatorElement_def]
    exact h1
  have hodd : Nat.Coprime 2 (Nat.card P) := by
    refine Nat.Coprime.coprime_dvd_right (card_dvd_of_le hPO) ?_
    rw [card_map_of_injective L.subtype_injective]
    exact pPrimeCore_coprime_card
  have htop : pPrimeCore 2 ↥P = ⊤ :=
    eq_top_iff.mpr (le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩)
  have : Subsingleton (↥P ⧸ pPrimeCore 2 ↥P) := QuotientGroup.subsingleton_iff.mpr htop
  exact false_of_nontrivial_of_subsingleton (↥P ⧸ pPrimeCore 2 ↥P)

theorem map_conj_eq_of_le_centralizer {P : Subgroup X} {g : X}
    (hP : P ≤ centralizer ({g} : Set X)) : P.map (MulAut.conj g).toMonoidHom = P := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g * y * g⁻¹ ∈ P
    rw [show g * y = y * g from (mem_centralizer_singleton_iff.mp (hP hy)).symm,
      mul_inv_cancel_right]
    exact hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    change g * x * g⁻¹ = x
    rw [show g * x = x * g from (mem_centralizer_singleton_iff.mp (hP hx)).symm,
      mul_inv_cancel_right]

end SwapP2

end CFSG.ComponentClassification.SolMax
