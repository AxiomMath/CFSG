module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterRows

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap Module Subgroup CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail (pairsPerp mem_pairsPerp finrank_pairsPerp
  finrank_le_of_totSing_tail)
open CFSG.RankThree.PartOne.KCOrthogonal (hypCoordIsometry hypCoordSplitIsometry)
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_eq_of_lagrangian_omegaPlus {G : Type} [Group G] {L : Subgroup G} {n f : ℕ}
    {K : Type} [Field K] [Finite K] (hn : 4 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {e : L ≃* StatedSp n K} {t : G} (hglob : SpOmegaRowGlobal e t f .omegaPlus) {F : Type}
    [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V}
    (φ : spGlobal e ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hnd : (polarBilin Q).Nondegenerate) (hdim : finrank F V = 2 * (n + 1))
    {W : Submodule F V} (hWdim : finrank F W = n + 1) (hQW : ∀ w ∈ W, Q w = 0) :
    Nat.card F = Nat.card K := by
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
  · have hU : pairsPerp P' = ⊥ := by
      rw [hperp]
      exact Submodule.finrank_eq_zero.1 h0
    have hrN : r = n + 1 := by omega
    have := Fintype.ofFinite F
    obtain ⟨k, -, hk⟩ := FiniteField.card F 2
    have hcard : Nat.card F = 2 ^ (k : ℕ) := by rw [Nat.card_eq_fintype_card, hk]
    have hplus : CFSG.Blueprint.LieModel (spGlobal e) .POmegaPlus r 2 k :=
      lieModel_plus_of_isometry (by omega) k.pos hcard (hypCoordSplitIsometry hP' hU) φ
    have hplus' : CFSG.Blueprint.LieModel (spGlobal e) .POmegaPlus (n + 1) 2 f := hglob.1
    have c1 := F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hplus
    have c2 := F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hplus'
    rw [c1] at c2
    obtain ⟨-, hkf⟩ := OmegaPilot.ordD_eq_ordD (by omega) k.pos (by omega) (by omega) c2
    rw [hcard, hKc, hkf]
  · exfalso
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

@[expose] def OmegaLagrangianATwoModelInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V), 4 ≤ Nat.card F →
    (polarBilin Q).Nondegenerate → ∀ N : ℕ, N % 4 = 2 → 5 ≤ N → finrank F V = 2 * N →
    ∀ s : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      s * s = 1 → 2 * finrank F (omegaInvSpace (s : V ≃ₗ[F] V)) = finrank F V →
      (∀ w ∈ omegaInvSpace (s : V ≃ₗ[F] V), Q w = 0) →
      ∃ P : Subgroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆,
        commutator P = ⊤ ∧ (∀ p ∈ P, p * s = s * p) ∧
        ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card F →
          ∀ ψ : P →* StatedSp (N - 1) K, ¬ Function.Injective ψ

theorem spOmegaLagrangianATwoInput_omegaPlus_of_model (hM : OmegaLagrangianATwoModelInput) :
    SpOmegaLagrangianATwoInput .omegaPlus := by
  intro G _ _ L hset n f K _ _ _ hn hmod hKc hf e t ht hKt hroot hglob F _ _ _ V _ _ _ Q φ hF4
    hnd hdim g hw ⟨hlag, hQW⟩
  set s := φ ⟨g⁻¹ * t * g, hw⟩ with hs
  have hFK : Nat.card F = Nat.card K :=
    card_eq_of_lagrangian_omegaPlus hn hKc hf hglob φ hnd hdim
      (W := omegaInvSpace (s : V ≃ₗ[F] V)) (by omega) hQW
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hss : s * s = 1 := by
    rw [hs, ← map_mul, ← map_one φ]
    congr 1
    apply Subtype.ext
    show (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt]; group
  obtain ⟨P, hPc, hPs, hPne⟩ := hM F V Q hF4 hnd (n + 1) hmod (by omega) hdim s hss hlag hQW
  set eP : P ≃* P.map φ.symm.toMonoidHom :=
    P.equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective with heP
  have hP'c : commutator (P.map φ.symm.toMonoidHom) = ⊤ := commutator_top_transfer eP hPc
  have hwN : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) := Subgroup.le_normalizer hw
  have hP'F : P.map φ.symm.toMonoidHom ≤
      fixedSubgroup ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hwN⟩) := by
    rintro _ ⟨p, hp, rfl⟩
    have hc : φ.symm p * ⟨g⁻¹ * t * g, hw⟩ = ⟨g⁻¹ * t * g, hw⟩ * φ.symm p := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hs]
      exact hPs p hp
    have hc' := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at hc'
    show ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hwN⟩) (φ.symm p) = φ.symm p
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    show (g⁻¹ * t * g) * ((φ.symm p : spGlobal e) : G) * (g⁻¹ * t * g)⁻¹ = _
    rw [← hc', mul_inv_cancel_right]
  obtain ⟨ψ, hψ⟩ := exists_injective_of_perfect_le_fixedSubgroup_conj hset (by omega) e ht hKt
    hwN (P.map φ.symm.toMonoidHom) hP'c hP'F
  exact hPne K hFK.symm (ψ.comp eP.toMonoidHom) (hψ.comp eP.injective)

end CFSG.SeitzReduction.SymplecticPilot
