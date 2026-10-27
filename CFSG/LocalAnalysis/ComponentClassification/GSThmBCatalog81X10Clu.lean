module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10Clt
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerB

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4

namespace X10

@[expose] def IsSL2Comp (K : Type) [Field K] {G : Type*} [Group G] (t : G) (E : Subgroup G) :
    Prop :=
  E ≤ centralizer {t} ∧ IsPComponent 2 (E.subgroupOf (centralizer {t})) ∧ t ∈ E ∧
    pPrimeCore 2 E = ⊥ ∧ Nonempty (E ≃* Matrix.SpecialLinearGroup (Fin 2) K)

theorem isSL2Comp_map {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K)
    {G : Type*} [Group G] (ψ : StatedProj (StatedSp 2 K) ≃* G) {E : Subgroup (StatedProj
      (StatedSp 2 K))} (hE : E = E1 K ∨ E = E2 K) :
    IsSL2Comp K (ψ (u1 K)) (E.map ψ.toMonoidHom) := by
  have hC := map_centralizer_singleton ψ (u1 K)
  have hEC : E ≤ centralizer {u1 K} := by
    rcases hE with rfl | rfl
    exacts [E1_le_centralizer_u1 h2, E2_le_centralizer_u1 h2]
  have hEp : IsPComponent 2 (E.subgroupOf (centralizer {u1 K})) := by
    rcases hE with rfl | rfl
    exacts [isPComponent_E1 h2 h4, isPComponent_E2 h2 h4]
  have hu : u1 K ∈ E := by
    rcases hE with rfl | rfl
    exacts [u1_mem_E1, u1_mem_E2]
  have hO : pPrimeCore 2 E = ⊥ := by
    rcases hE with rfl | rfl
    exacts [pPrimeCore_E1 h2 h4, pPrimeCore_E2 h2 h4]
  obtain ⟨eE⟩ : Nonempty (E ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
    rcases hE with rfl | rfl
    exacts [⟨(E1Equiv h2).symm⟩, ⟨(E2Equiv h2).symm⟩]
  let φ : E ≃* E.map ψ.toMonoidHom := E.equivMapOfInjective ψ.toMonoidHom ψ.injective
  refine ⟨hC ▸ map_mono hEC, ?_, mem_map_of_mem _ hu, ?_, ⟨φ.symm.trans eE⟩⟩
  · have h := isPComponent_map_subgroupOf 2 ψ hEC hEp
    rwa [hC] at h
  · rw [← pPrimeCore_map_iso 2 φ, hO, Subgroup.map_bot]

theorem tauZ_twoComponents {K₀ : Type} [Group K₀] [Finite K₀] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) (hK₀ : Blueprint.LieModel K₀ .PSp 2 p f)
    (c : Cat8.QConf K₀ (p ^ f)) (hc : c.Props) {tτ tz : K₀} (hτ : MulAut.conj tτ = c.tau)
    (hz : MulAut.conj tz = c.z) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (E₁ E₂ : Subgroup K₀), Nat.card K = p ^ f ∧
      E₁ ≠ E₂ ∧ IsSL2Comp K (tτ * tz) E₁ ∧ IsSL2Comp K (tτ * tz) E₂ := by
  obtain ⟨K, _, _, φ, hK, hφ⟩ := tauZ_equiv_u1 hp hp2 hf hK₀ c hc hτ hz
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card (odd_card_of_card_eq hp hp2 hK)
  have h4 : 4 ≤ Nat.card K := by omega
  have ht : φ.symm (u1 K) = tτ * tz := by rw [← hφ, MulEquiv.symm_apply_apply]
  refine ⟨K, inferInstance, inferInstance, (E1 K).map φ.symm.toMonoidHom,
    (E2 K).map φ.symm.toMonoidHom, hK, ?_, ?_, ?_⟩
  · intro h
    exact E1_ne_E2 (map_injective φ.symm.injective h)
  · rw [← ht]
    exact isSL2Comp_map h2 h4 φ.symm (Or.inl rfl)
  · rw [← ht]
    exact isSL2Comp_map h2 h4 φ.symm (Or.inr rfl)

end X10

end CFSG.ComponentClassification.GSThmB
