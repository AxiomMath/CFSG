module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerOrth
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerUnitaryFamily

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  QuadraticMap CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Generic

theorem OddPCoreInClosure.of_inf_of_conj_mem {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (U N : Subgroup G) (hN : ∀ u ∈ U, ∀ n ∈ N, u * n * u⁻¹ ∈ N)
    (h : OddPCoreInClosure p ↥U) : OddPCoreInClosure p ↥(U ⊓ N) := by
  have heq : (U ⊓ N).subgroupOf U = N.subgroupOf U := by
    ext g
    simp [Subgroup.mem_subgroupOf]
  haveI hNn : ((U ⊓ N).subgroupOf U).Normal := by
    rw [heq]
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hN g g.2 n hn
  exact OddPCoreInClosure.of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_left)
    (OddPCoreInClosure.of_normal hp ((U ⊓ N).subgroupOf U) h)

theorem conj_mem_commutator_of_mem {G : Type*} [Group G] (O : Subgroup G) {u : G} (hu : u ∈ O)
    {n : G} (hn : n ∈ ⁅O, O⁆) : u * n * u⁻¹ ∈ ⁅O, O⁆ := by
  refine Subgroup.closure_induction (p := fun n _ => u * n * u⁻¹ ∈ ⁅O, O⁆) ?_ ?_ ?_ ?_ hn
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    have e : u * ⁅a, b⁆ * u⁻¹ = ⁅u * a * u⁻¹, u * b * u⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (O.mul_mem (O.mul_mem hu ha) (O.inv_mem hu))
      (O.mul_mem (O.mul_mem hu hb) (O.inv_mem hu))
  · simp
  · intro x y _ _ hx hy
    have e : u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have e : u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

end Generic

section Orth

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem pClosureOdd_orthDerived (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : PClosureOdd p ↥(orthDerived Q) := by
  intro x hx1 hxp
  haveI : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hpl : p ≠ ringChar K := by
    rw [ringChar.eq K 2]
    exact hp2
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxord
  have hC := oddPCoreInClosure_isometryCentralizer hx hp hp2
  have hO : ∀ u ∈ isometryCentralizer Q (x : V ≃ₗ[K] V), ∀ n ∈ orthDerived Q,
      u * n * u⁻¹ ∈ orthDerived Q :=
    fun u hu n hn => conj_mem_commutator_of_mem _ (Subgroup.mem_inf.1 hu).1 hn
  have hCN := OddPCoreInClosure.of_inf_of_conj_mem hp _ _ hO hC
  have heq : orthDerived Q ⊓ Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) =
      isometryCentralizer Q (x : V ≃ₗ[K] V) ⊓ orthDerived Q := by
    ext g
    simp only [Subgroup.mem_inf, isometryCentralizer]
    constructor
    · rintro ⟨hΩ, hc⟩
      exact ⟨⟨orthDerived_le_orthogonalGroup hΩ, hc⟩, hΩ⟩
    · rintro ⟨⟨-, hc⟩, hΩ⟩
      exact ⟨hΩ, hc⟩
  exact OddPCoreInClosure.of_mulEquiv
    ((centralizerSubtypeEquiv (orthDerived Q) x).trans (MulEquiv.subgroupCongr heq)).symm hCN

end Orth

section Models

open CFSG.LieType.Universal.Spin CFSG.AGLEmbedding.ToralCensus

theorem pClosureOdd_of_model_pomegaPlus {X : Type} [Group X] {r f p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : StatedClassicalModel X .POmegaPlus r 2 f) : PClosureOdd p X := by
  obtain ⟨⟨-, -, hr⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have : Nonempty (Fin r ⊕ Fin r) := ⟨.inl ⟨0, by omega⟩⟩
  exact PClosureOdd.of_mulEquiv
    (e.trans (statedProjOmegaEquivDerivedCharTwo (coe_quadPlus r K)
      (nondegenerate_polarBilin_quadPlus r K))).symm
    (pClosureOdd_orthDerived (nondegenerate_polarBilin_quadPlus r K) hp hp2)

theorem pClosureOdd_of_model_pomegaMinus {X : Type} [Group X] {r f p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : StatedClassicalModel X .POmegaMinus r 2 f) : PClosureOdd p X := by
  obtain ⟨⟨-, -, hr⟩, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := h
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have : Nonempty (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) := ⟨.inr (.inr 0)⟩
  exact PClosureOdd.of_mulEquiv
    (e.trans (statedProjOmegaEquivDerivedCharTwo (coe_quadMinus r K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite r K hbc))).symm
    (pClosureOdd_orthDerived (nondegenerate_polarBilin_quadMinus_of_finite r K hbc) hp hp2)

end Models

section Family

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

theorem chevTwoPClosureOddFamily_orthogonal : ChevTwoPClosureOddFamily LieFamilyOrthogonal := by
  intro p hp hp2 L _ _ hs hnab hrk hSE ⟨dd, hv⟩ hF hdi he
  cases dd with
  | D r q =>
    obtain ⟨e⟩ := he
    have hdi' : q.p = 2 := hdi
    obtain ⟨hadm, hmod | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_D r q hv e
    · have hmod' : StatedClassicalModel L .POmegaPlus r 2 q.exponent := by
        rw [hdi'] at hmod
        exact hmod
      exact pClosureOdd_of_model_pomegaPlus hp hp2 hmod'
    · exfalso
      have : 4 ≤ r := hadm.2.2
      omega
  | twistedD r q =>
    obtain ⟨e⟩ := he
    have hdi' : q.p = 2 := hdi
    obtain ⟨hadm, hmod | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_twistedD r q hv e
    · have hmod' : StatedClassicalModel L .POmegaMinus r 2 q.exponent := by
        rw [hdi'] at hmod
        exact hmod
      exact pClosureOdd_of_model_pomegaMinus hp hp2 hmod'
    · exfalso
      have : 4 ≤ r := hadm.2.2
      omega
  | _ => exact absurd hF (by simp [LieFamilyOrthogonal])

end Family

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
