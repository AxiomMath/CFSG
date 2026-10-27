module

public import CFSG.RankThree.PartOne.KC.OrthogonalHypCoordinates
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDetOrders
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaStepOneOdd
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap Module Subgroup CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail (pairsPerp mem_pairsPerp finrank_pairsPerp
  finrank_le_of_totSing_tail)
open CFSG.RankThree.PartOne.KCOrthogonal (hypCoordIsometry hypCoordSplitIsometry)
open CFSG.Assembly.LowTwoRank

section Transport

variable {F V V' : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']
  {Q : QuadraticForm F V} {Q' : QuadraticForm F V'}

@[expose] def lagIsoConj (ι : V ≃ₗ[F] V') : (V ≃ₗ[F] V) ≃* (V' ≃ₗ[F] V') where
  toFun g := ι.symm.trans (g.trans ι)
  invFun g := ι.trans (g.trans ι.symm)
  left_inv g := by ext v; simp
  right_inv g := by ext v; simp
  map_mul' g h := by ext v; simp

theorem map_orthogonalGroup_lagIsoConj (ι : Q.IsometryEquiv Q') :
    (TauCeti.QuadraticMap.orthogonalGroup Q).map (lagIsoConj ι.toLinearEquiv).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q' := by
  ext g'
  rw [Subgroup.mem_map, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩ v
    have hg' := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
    change Q' (ι (g (ι.symm v))) = Q' v
    rw [ι.map_app, hg', ι.symm.map_app]
  · intro hg'
    refine ⟨(lagIsoConj ι.toLinearEquiv).symm g', ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    change Q (ι.symm (g' (ι v))) = Q v
    rw [ι.symm.map_app, hg', ι.map_app]

@[expose] noncomputable def lagOmegaCongr (ι : Q.IsometryEquiv Q') :
    ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≃*
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q', TauCeti.QuadraticMap.orthogonalGroup Q'⁆ :=
  ((lagIsoConj ι.toLinearEquiv).subgroupMap _).trans (MulEquiv.subgroupCongr (by
    rw [Subgroup.map_commutator]
    congr 1 <;> exact map_orthogonalGroup_lagIsoConj ι))

end Transport

theorem lieModel_plus_of_isometry {G : Type} [Group G] {F V : Type} [Field F] [Finite F]
    [CharP F 2] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {m k : ℕ} (hm : 4 ≤ m)
    (hk : 1 ≤ k) (hcard : Nat.card F = 2 ^ k)
    (ι : Q.IsometryEquiv (CFSG.LieType.Universal.Spin.quadPlus m F))
    (φ : G ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    CFSG.Blueprint.LieModel G .POmegaPlus m 2 k := by
  have : Nontrivial (Fin m ⊕ Fin m → F) := by
    have : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    infer_instance
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m F
  have hQ := CFSG.LieType.Universal.Spin.coe_quadPlus m F
  have hne : ∃ v, StatedQuadPlus m F v ≠ 0 := by
    obtain ⟨a, ha⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hnd
    exact ⟨a, by rwa [← hQ]⟩
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, hk, hm⟩, F, inferInstance, inferInstance, hcard,
    ⟨φ.trans ((lagOmegaCongr ι).trans
      ((statedProjOmegaEquiv hQ hne).trans (statedOmegaEquivOmega hQ)).symm)⟩⟩

theorem exists_le_finrank_eq_three {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {W : Submodule F V} (h3 : 3 ≤ finrank F W) :
    ∃ T : Submodule F V, finrank F T = 3 ∧ T ≤ W := by
  set b := Module.finBasis F W
  set v : Fin 3 → V := fun i => (b (Fin.castLE h3 i) : V) with hv
  have hli : LinearIndependent F v :=
    (b.linearIndependent.comp (Fin.castLE h3) (Fin.castLE_injective h3)).map' W.subtype
      (Submodule.ker_subtype W)
  refine ⟨Submodule.span F (Set.range v), ?_, ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b _).2

theorem spOmegaLagrangianATwoInput_omegaMinus : SpOmegaLagrangianATwoInput .omegaMinus := by
  intro G _ _ L hset n f K _ _ _ hn _ hKc hf e t ht hKt hroot hglob F _ _ _ V _ _ _ Q φ hF4 hnd
    hdim g hw ⟨hlag, hQW⟩
  set W := omegaInvSpace ((φ ⟨g⁻¹ * t * g, hw⟩ : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
    TauCeti.QuadraticMap.orthogonalGroup Q⁆) : V ≃ₗ[F] V) with hW
  have hWdim : finrank F W = n + 1 := by omega
  obtain ⟨T, hT3, hTW⟩ := exists_le_finrank_eq_three (W := W) (by omega)
  obtain ⟨P, r, hr, hP, hani, htail⟩ :=
    CFSG.RankThree.Classical.exists_hypPair_tail_decomposition hnd
      ⟨T, hT3, fun x hx => hQW x (hTW hx)⟩
  set P' : Fin r → HypPair Q := fun i => P i with hP'def
  have hP' : ∀ i j, i ≠ j → (P' i).Orth (P' j) := fun i j hij =>
    hP i j i.2 j.2 fun h => hij (Fin.ext h)
  have hperp : pairsPerp P' = CFSG.ClassicalGroups.Orthogonal.tailSpace P r := by
    ext x
    rw [mem_pairsPerp, CFSG.ClassicalGroups.Orthogonal.mem_tailSpace]
    constructor
    · intro h i hi
      exact HypPair.mem_perp.1 (h ⟨i, hi⟩)
    · intro h i
      exact HypPair.mem_perp.2 (h i i.2)
  have hdimV := finrank_pairsPerp hP' hnd
  rw [hperp] at hdimV
  rcases htail with h0 | h2
  ·
    have hU : pairsPerp P' = ⊥ := by
      rw [hperp]
      exact Submodule.finrank_eq_zero.1 h0
    have hrN : r = n + 1 := by omega
    have := Fintype.ofFinite F
    obtain ⟨k, -, hk⟩ := FiniteField.card F 2
    have hcard : Nat.card F = 2 ^ (k : ℕ) := by rw [Nat.card_eq_fintype_card, hk]
    have hplus : CFSG.Blueprint.LieModel (spGlobal e) .POmegaPlus r 2 k :=
      lieModel_plus_of_isometry (by omega) k.pos hcard (hypCoordSplitIsometry hP' hU) φ
    have hminus : CFSG.Blueprint.LieModel (spGlobal e) .POmegaMinus (n + 1) 2 f := hglob.1
    have c1 := F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hplus
    have c2 := F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hminus
    rw [c1] at c2
    exact OmegaPilot.ordTwistedD_ne_ordD (by omega) (by omega) (by omega) k.pos c2.symm
  ·
    have hrn : r = n := by omega
    set ι := hypCoordIsometry hP' with hι
    have haniA : (Q.comp (pairsPerp P').subtype).Anisotropic := by
      intro x hx
      apply Subtype.ext
      have hxt : (x : V) ∈ CFSG.ClassicalGroups.Orthogonal.tailSpace P r := hperp ▸ x.2
      exact hani x hxt hx
    have hT' : ∀ y ∈ W.map ι.toLinearEquiv.toLinearMap,
        CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.quadTail r
          (Q.comp (pairsPerp P').subtype) y = 0 := by
      rintro _ ⟨w, hw', rfl⟩
      rw [LinearEquiv.coe_coe, QuadraticMap.IsometryEquiv.coe_toLinearEquiv, ι.map_app]
      exact hQW w hw'
    have hle := finrank_le_of_totSing_tail haniA hT'
    rw [LinearEquiv.finrank_map_eq] at hle
    omega

end CFSG.SeitzReduction.SymplecticPilot
