module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrthPc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOForm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eDefs
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOSign
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
import CFSG.GH74.GLS.Classes
import CFSG.GH74.Generic.Shapes
import CFSG.GH74.Statements
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOData
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e.Orth

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof.X10Sp (CentralModel centralModel_SL
  CentralModel.of_mulEquiv)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {d : ℕ}

omit [Finite K] in
theorem exists_lift_sq (h2 : (2 : K) ≠ 0) (hd : 0 < d) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {t : StatedProj (matrixDerived (oQ R))}
    (ht2 : t * t = 1) :
    ∃ (T : GL (Fin d) K) (hT : T ∈ matrixDerived (oQ R)), t = projH _ ⟨T, hT⟩ ∧
      ((T : Matrix (Fin d) (Fin d) K) * T = 1 ∨ (T : Matrix (Fin d) (Fin d) K) * T = -1) :=
  CFSG.ComponentClassification.GSThmB.QPUCl.exists_lift_sq h2 hd hR ht2

theorem comp_types_of_model (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime)
    (hKc : Nat.card K = p ^ f) (hd : 7 ≤ d) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {z : StatedProj (matrixDerived (oQ R))}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {L : Subgroup (StatedProj (matrixDerived (oQ R)))}
    (hLH : L ≤ centralizer {z}) (hL : IsPComponent 2 (L.subgroupOf (centralizer {z}))) :
    (∃ (w : Fin d → K) (hw : ∀ i, w i ≠ 0) (I : Finset (Fin d)), Iᶜ.Nonempty ∧ BlockNF w I ∧
        Nonempty (L ≃* blockP K hw I)) ∨ (Nat.card K ≠ 3 ∧ Nonempty (L ≃* SL(2, K))) ∨
      ∃ m, d = 2 * m ∧ (CentralModel p .PSL m f L ∨ CentralModel p .PSU m f L) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨T, hT, rfl, hT2 | hT2⟩ := exists_lift_sq h2 (by omega) hR hz2
  · rcases sign_comp_cases_of_model hK hR hT hT2 hz1 hLH hL with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (pc_comp_centralModel_of_model hK hp hKc hd hR hT hT2 hLH hL))

theorem comp_N_of_model {N : ℕ → (L : Type) → [Group L] → Prop}
    (hN : ∀ {p : ℕ} {L M : Type} [Group L] [Group M], (L ≃* M) → N p M → N p L)
    (hT1 : ∀ {L : Type} [Group L] {t : StatedLieTag} {n p f : ℕ}, p ≠ 2 →
      StatedLieAdmissible t n p f → Blueprint.LieModel (L ⧸ center L) t n p f →
      ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3) → N p L)
    (hT1b : ∀ {K : Type} [Field K] [Finite K], ringChar K ≠ 2 → ∀ {p f : ℕ}, p.Prime →
      Nat.card K = p ^ f → ∀ {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
      {I : Finset (Fin d)}, Iᶜ.Nonempty → BlockNF w I → N p ↥(blockP K hw I))
    (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hKc : Nat.card K = p ^ f)
    (hd : 7 ≤ d) {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    {z : StatedProj (matrixDerived (oQ R))} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    {L : Subgroup (StatedProj (matrixDerived (oQ R)))}
    (hLH : L ≤ centralizer {z}) (hL : IsPComponent 2 (L.subgroupOf (centralizer {z}))) :
    N p L := by
  have hne : ∀ {t : StatedLieTag} {n : ℕ}, (t = .PSL ∨ t = .PSU) →
      ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3) := by
    rintro t n (rfl | rfl) ⟨h | h, -⟩ <;> exact absurd h (by decide)
  rcases comp_types_of_model hK hp hKc hd hR hz2 hz1 hLH hL with
    ⟨w, hw, I, hIc, hNF, ⟨e⟩⟩ | ⟨hK3, ⟨e⟩⟩ | ⟨m, -, h | h⟩
  · exact hN e (hT1b hK hp hKc hw hIc hNF)
  · have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hadm : StatedLieAdmissible .PSL 2 p f :=
      ⟨hp, one_le_of_card_eq hKc, le_rfl, fun h => by
        have := (Prod.mk.inj h).2
        rw [this] at hodd
        exact (by decide : ¬ Odd 2) hodd, fun h => hK3 (by rw [hKc]; exact (Prod.mk.inj h).2)⟩
    have hc := (centralModel_SL hadm hKc).of_mulEquiv e
    exact hT1 hp2 hc.1 hc.2 (hne (Or.inl rfl))
  · exact hT1 hp2 h.1 h.2 (hne (Or.inl rfl))
  · exact hT1 hp2 h.1 h.2 (hne (Or.inr rfl))

theorem fam_N_of_model {N : ℕ → (L : Type) → [Group L] → Prop}
    (hN : ∀ {p : ℕ} {L M : Type} [Group L] [Group M], (L ≃* M) → N p M → N p L)
    (hT1 : ∀ {L : Type} [Group L] {t : StatedLieTag} {n p f : ℕ}, p ≠ 2 →
      StatedLieAdmissible t n p f → Blueprint.LieModel (L ⧸ center L) t n p f →
      ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3) → N p L)
    (hT1b : ∀ {K : Type} [Field K] [Finite K], ringChar K ≠ 2 → ∀ {p f : ℕ}, p.Prime →
      Nat.card K = p ^ f → ∀ {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
      {I : Finset (Fin d)}, Iᶜ.Nonempty → BlockNF w I → N p ↥(blockP K hw I))
    (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hKc : Nat.card K = p ^ f)
    (hd : 7 ≤ d) {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    {X : Type} [Group X] [IsSimpleGroup X] (θ : X ≃* StatedProj (matrixDerived (oQ R))) {g : X}
    (hg : orderOf (MulAut.conj g) = 2) {L : Subgroup (fixedSubgroup (MulAut.conj g))}
    (hL : IsComponent L) : N p L := by
  have : Finite X := Finite.of_equiv _ θ.symm.toEquiv
  obtain ⟨hg2, hg1⟩ := Comp.mul_self_eq_one_of_orderOf_conj
    (Comp.center_eq_bot_of_orderOf_conj hg) hg
  obtain ⟨L', hL'H, hL'c, ⟨eL⟩⟩ := Comp.exists_comp_of_isComponent θ g hL
  have hz2 : θ g * θ g = 1 := by rw [← map_mul, hg2, map_one]
  have hz1 : θ g ≠ 1 := fun h => hg1 (θ.injective (by rw [h, map_one]))
  exact hN eL (comp_N_of_model (N := N) hN hT1 hT1b hK hp hp2 hKc hd hR hz2 hz1 hL'H hL'c)

theorem fam_pomegaOdd_of {N : ℕ → (L : Type) → [Group L] → Prop}
    (hN : ∀ {p : ℕ} {L M : Type} [Group L] [Group M], (L ≃* M) → N p M → N p L)
    (hT1 : ∀ {L : Type} [Group L] {t : StatedLieTag} {n p f : ℕ}, p ≠ 2 →
      StatedLieAdmissible t n p f → Blueprint.LieModel (L ⧸ center L) t n p f →
      ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3) → N p L)
    (hT1b : ∀ {K : Type} [Field K] [Finite K], ringChar K ≠ 2 → ∀ {p f : ℕ}, p.Prime →
      Nat.card K = p ^ f → ∀ {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
      {I : Finset (Fin d)}, Iᶜ.Nonempty → BlockNF w I → N p ↥(blockP K hw I))
    (X : Type) [Group X] (n p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : Blueprint.LieModel X .POmegaOdd n p f) (g : X) (hg : orderOf (MulAut.conj g) = 2)
    (L : Subgroup (fixedSubgroup (MulAut.conj g))) (hL : IsComponent L) : N p L := by
  have hmod := Comp.statedClassicalModel_of_lieModel (by decide) hX
  have := (ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaOdd X n p f
    hmod).2
  obtain ⟨⟨-, -, hn, -⟩, F, _, _, hFc, ⟨e⟩⟩ := hmod
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n F)
    (regular_coordinateQuadOdd n F h2 hn).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) F) : Matrix _ _ F) *ᵥ v) =
      ((1 : Fˣ) : F) * coordinateQuadOdd n F v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  exact fam_N_of_model (N := N) hN hT1 hT1b hF hp hp2 hFc (by omega) hR
    ((coordinateOddWitnessEquiv F e).trans (oTransport 1 1 hS₁)) hg hL

theorem fam_pomegaMinus_of {N : ℕ → (L : Type) → [Group L] → Prop}
    (hN : ∀ {p : ℕ} {L M : Type} [Group L] [Group M], (L ≃* M) → N p M → N p L)
    (hT1 : ∀ {L : Type} [Group L] {t : StatedLieTag} {n p f : ℕ}, p ≠ 2 →
      StatedLieAdmissible t n p f → Blueprint.LieModel (L ⧸ center L) t n p f →
      ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3) → N p L)
    (hT1b : ∀ {K : Type} [Field K] [Finite K], ringChar K ≠ 2 → ∀ {p f : ℕ}, p.Prime →
      Nat.card K = p ^ f → ∀ {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
      {I : Finset (Fin d)}, Iᶜ.Nonempty → BlockNF w I → N p ↥(blockP K hw I))
    (X : Type) [Group X] (n p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : Blueprint.LieModel X .POmegaMinus n p f) (g : X) (hg : orderOf (MulAut.conj g) = 2)
    (L : Subgroup (fixedSubgroup (MulAut.conj g))) (hL : IsComponent L) : N p L := by
  have hmod := Comp.statedClassicalModel_of_lieModel (by decide) hX
  have := (ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus X n p f
    hmod).2
  obtain ⟨⟨-, -, hn⟩, F, _, _, hFc, b, c, hirr, ⟨e⟩⟩ := hmod
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hn1 : 1 ≤ n := by omega
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadMinus n F hn1 b c)
    (regular_coordinateQuadMinus n F b c hn hirr).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
      ((1 : Fˣ) : F) * coordinateQuadMinus n F hn1 b c v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  exact fam_N_of_model (N := N) hN hT1 hT1b hF hp hp2 hFc (by omega) hR
    ((coordinateMinusWitnessEquiv F hn1 b c e).trans (oTransport 1 1 hS₁)) hg hL

theorem fam_pomegaPlus_of {N : ℕ → (L : Type) → [Group L] → Prop}
    (hN : ∀ {p : ℕ} {L M : Type} [Group L] [Group M], (L ≃* M) → N p M → N p L)
    (hT1 : ∀ {L : Type} [Group L] {t : StatedLieTag} {n p f : ℕ}, p ≠ 2 →
      StatedLieAdmissible t n p f → Blueprint.LieModel (L ⧸ center L) t n p f →
      ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3) → N p L)
    (hT1b : ∀ {K : Type} [Field K] [Finite K], ringChar K ≠ 2 → ∀ {p f : ℕ}, p.Prime →
      Nat.card K = p ^ f → ∀ {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
      {I : Finset (Fin d)}, Iᶜ.Nonempty → BlockNF w I → N p ↥(blockP K hw I))
    (X : Type) [Group X] (n p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : Blueprint.LieModel X .POmegaPlus n p f) (g : X) (hg : orderOf (MulAut.conj g) = 2)
    (L : Subgroup (fixedSubgroup (MulAut.conj g))) (hL : IsComponent L) : N p L := by
  have hmod := Comp.statedClassicalModel_of_lieModel (by decide) hX
  have := (ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus X n p f
    hmod).2
  obtain ⟨⟨-, -, hn⟩, F, _, _, hFc, ⟨e⟩⟩ := hmod
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n F)
    (regular_coordinateQuadPlus n F (by omega)).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
      ((1 : Fˣ) : F) * coordinateQuadPlus n F v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  exact fam_N_of_model (N := N) hN hT1 hT1b hF hp hp2 hFc (by omega) hR
    ((coordinatePlusWitnessEquiv F e).trans (oTransport 1 1 hS₁)) hg hL

theorem famNoSpin7_pomegaOdd
    (hT1 : ∀ {L : Type} [Group L] {t : StatedLieTag} {n p f : ℕ}, p ≠ 2 →
      StatedLieAdmissible t n p f → Blueprint.LieModel (L ⧸ center L) t n p f →
      ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3) → NoSpin7 p L)
    (hT1b : ∀ {K : Type} [Field K] [Finite K], ringChar K ≠ 2 → ∀ {p f : ℕ}, p.Prime →
      Nat.card K = p ^ f → ∀ {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
      {I : Finset (Fin d)}, Iᶜ.Nonempty → BlockNF w I → NoSpin7 p ↥(blockP K hw I)) :
    FamNoSpin7 .POmegaOdd :=
  fun X _ n p f hp hp2 _ hX g hg L hL => fam_pomegaOdd_of (N := NoSpin7)
    (fun e h => NoSpin7.of_mulEquiv e h) hT1 hT1b X n p f hp hp2 hX g hg L hL

theorem famNoSpin7_pomegaPlus
    (hT1 : ∀ {L : Type} [Group L] {t : StatedLieTag} {n p f : ℕ}, p ≠ 2 →
      StatedLieAdmissible t n p f → Blueprint.LieModel (L ⧸ center L) t n p f →
      ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3) → NoSpin7 p L)
    (hT1b : ∀ {K : Type} [Field K] [Finite K], ringChar K ≠ 2 → ∀ {p f : ℕ}, p.Prime →
      Nat.card K = p ^ f → ∀ {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
      {I : Finset (Fin d)}, Iᶜ.Nonempty → BlockNF w I → NoSpin7 p ↥(blockP K hw I)) :
    FamNoSpin7 .POmegaPlus :=
  fun X _ n p f hp hp2 _ hX g hg L hL => fam_pomegaPlus_of (N := NoSpin7)
    (fun e h => NoSpin7.of_mulEquiv e h) hT1 hT1b X n p f hp hp2 hX g hg L hL

theorem famNoSpin7_pomegaMinus
    (hT1 : ∀ {L : Type} [Group L] {t : StatedLieTag} {n p f : ℕ}, p ≠ 2 →
      StatedLieAdmissible t n p f → Blueprint.LieModel (L ⧸ center L) t n p f →
      ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3) → NoSpin7 p L)
    (hT1b : ∀ {K : Type} [Field K] [Finite K], ringChar K ≠ 2 → ∀ {p f : ℕ}, p.Prime →
      Nat.card K = p ^ f → ∀ {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
      {I : Finset (Fin d)}, Iᶜ.Nonempty → BlockNF w I → NoSpin7 p ↥(blockP K hw I)) :
    FamNoSpin7 .POmegaMinus :=
  fun X _ n p f hp hp2 _ hX g hg L hL => fam_pomegaMinus_of (N := NoSpin7)
    (fun e h => NoSpin7.of_mulEquiv e h) hT1 hT1b X n p f hp hp2 hX g hg L hL

end CFSG.ComponentClassification.HarrisLit.T1.P51e.Orth
