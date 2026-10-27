module

public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.E6Three
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.SeitzGeneration.ExcParabolicUntw
public import CFSG.LieType.SeitzGeneration.UnitaryHyperDiag
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3
public import CFSG.HardMathSupport.Malle.SeitzCube.E7High
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

open CFSG.Open CFSG.LieType.SeitzGeneration
open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem hyperGen_of_radicals {Y : Type*} [Group Y] {p : ℕ} [Fact p.Prime]
    {N E A Q Q' : Subgroup Y} [Finite A] [Finite Q] [Finite Q'] (hA : IsElemAbelian p A)
    (hA1 : A ≠ ⊥) (hN : N ≤ Q ⊔ Q') (hQ : ¬ p ∣ Nat.card Q) (hQ' : ¬ p ∣ Nat.card Q')
    (hAQ : A ≤ Subgroup.normalizer (Q : Set Y)) (hAQ' : A ≤ Subgroup.normalizer (Q' : Set Y))
    (hlQ : ∀ B : Subgroup Y, B ≤ A → B.relIndex A = p →
      Q ⊓ Subgroup.centralizer (B : Set Y) ≤ hyperClosure p N E)
    (hlQ' : ∀ B : Subgroup Y, B ≤ A → B.relIndex A = p →
      Q' ⊓ Subgroup.centralizer (B : Set Y) ≤ hyperClosure p N E) :
    HyperGen p N E := by
  have : IsElementaryAbelian p A := isElementaryAbelian_of_isElemAbelian hA
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 hA1
  have h1 := CFSG.LieType.Chevalley.le_iSup_hyper_of_coprime (C := Q) hQ hAQ le_rfl
  have h2 := CFSG.LieType.Chevalley.le_iSup_hyper_of_coprime (C := Q') hQ' hAQ' le_rfl
  have hQle : Q ≤ hyperClosure p N E :=
    h1.trans (iSup₂_le fun B hB => iSup_le fun hBi => hlQ B hB hBi)
  have hQ'le : Q' ≤ hyperClosure p N E :=
    h2.trans (iSup₂_le fun B hB => iSup_le fun hBi => hlQ' B hB hBi)
  exact hyperGen_iff_le.2 (hN.trans (sup_le hQle hQ'le))

@[expose] def E6ThreeRadicalAdj (K : Type) [Field K] (r : ℕ) [CharP K r]
    (ψ : Fin 3 → Matrix.SpecialLinearGroup (Fin 3) K →* ↥(adjointGroup Tag.E6 K)) : Prop :=
  ∀ (p : ℕ) (g : Matrix.SpecialLinearGroup (Fin 3) K), p.Prime → p ≠ 3 → p ≠ r →
    orderOf ((Nat.card K : ℕ) : ZMod p) = 3 → orderOf g = p →
    ∃ Q Q' : Subgroup ↥(adjointGroup Tag.E6 K), IsPGroup r Q ∧ IsPGroup r Q' ∧
      (⊤ : Subgroup ↥(adjointGroup Tag.E6 K)) ≤ Q ⊔ Q' ∧
      plane ψ g ≤ Subgroup.normalizer (Q : Set ↥(adjointGroup Tag.E6 K)) ∧
      plane ψ g ≤ Subgroup.normalizer (Q' : Set ↥(adjointGroup Tag.E6 K)) ∧
      (∀ B : Subgroup ↥(adjointGroup Tag.E6 K), B ≤ plane ψ g → B.relIndex (plane ψ g) = p →
        Q ⊓ Subgroup.centralizer (B : Set ↥(adjointGroup Tag.E6 K)) ≤
          hyperClosure p ⊤ (cube ψ g)) ∧
      (∀ B : Subgroup ↥(adjointGroup Tag.E6 K), B ≤ plane ψ g → B.relIndex (plane ψ g) = p →
        Q' ⊓ Subgroup.centralizer (B : Set ↥(adjointGroup Tag.E6 K)) ≤
          hyperClosure p ⊤ (cube ψ g))

theorem excCubeHighAt_E6_three_of_radicalAdj
    (h : ∀ (K : Type) [Field K] [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r],
      ∃ ψ : Fin 3 → Matrix.SpecialLinearGroup (Fin 3) K →* ↥(adjointGroup Tag.E6 K),
        (∀ i, Function.Injective (ψ i)) ∧ (∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) ∧
          E6ThreeRadicalAdj K r ψ) :
    CFSG.HardMathSupport.Malle.SeitzCube.ExcCubeHighAt TauCeti.LieTypeIndex.E6 3 := by
  intro q hv p hp _ hpq _ _ hord _
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Finite (ModGL Tag.E6 K) := CFSG.LieType.Chevalley.finite_modGL
  obtain ⟨ψ, hinj, hcomm, hrad⟩ := h K q.p
  obtain ⟨hdvd, hp3⟩ := dvd_sq_add_add_one_of_orderOf_eq_three hp hord
  have hdvdK : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := by rw [hK]; exact hdvd
  obtain ⟨g, hg⟩ := exists_sl3_orderOf (K := K) hp hp3 hdvdK
  have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 3 := by rw [hK]; exact hord
  have hrp : q.p ≠ p := fun h' => hpq h'.symm
  obtain ⟨Q, Q', hQr, hQ'r, htop, hnQ, hnQ', hlQ, hlQ'⟩ := hrad p g hp hp3 hpq hordK hg
  obtain ⟨hA, hA1⟩ := plane_spec hinj hcomm hp hp3 hg
  have hHG : HyperGen p ⊤ (cube ψ g) :=
    hyperGen_of_radicals hA hA1 htop
      (CFSG.LieType.Chevalley.not_dvd_card_of_isPGroup hrp hQr)
      (CFSG.LieType.Chevalley.not_dvd_card_of_isPGroup hrp hQ'r) hnQ hnQ' hlQ hlQ'
  refine ⟨(cube ψ g).map e.symm.toMonoidHom, ?_, ?_, Or.inr (hyperGen_map_symm e hHG)⟩
  · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
      (isElemAbelian_cube hinj hcomm hp hp3 hg) e.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact card_cube hinj hcomm hp hp3 hg

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
