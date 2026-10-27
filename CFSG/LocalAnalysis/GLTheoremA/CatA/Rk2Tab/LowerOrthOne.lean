module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalElementary
public import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.D4Centre
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootData
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootGen
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryBasic
public import CFSG.HardMathSupport.Lang.E27Lie.MinusToralCore
public import CFSG.Walter.ReeOrder.JT.Section4H
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.StandardType CFSG.Assembly CFSG.Blueprint.Multiplier
open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

variable {F : Type} [Field F]

section BlockFour

@[expose] def quadFour (w : Fin 4 → F) : F := w 0 * w 2 + w 1 * w 3

@[expose] def orthBlockUnitOfCube (M : Matrix (Fin 4) (Fin 4) F) (h : M * (M * M) = 1) :
    GL (Fin 4) F :=
  ⟨M, M * M, h, (mul_assoc M M M).trans h⟩

@[expose] def orthBlockUnitOfSq (M : Matrix (Fin 4) (Fin 4) F) (h : M * M = 1) : GL (Fin 4) F :=
  ⟨M, M, h, h⟩

@[expose] def orthBlockLgMat : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 1, 0;
     1, 0, 0, 1]

@[expose] def orthBlockRgMat : Matrix (Fin 4) (Fin 4) F :=
  !![0, 1, 0, 0;
     1, 1, 0, 0;
     0, 0, 1, 1;
     0, 0, 1, 0]

@[expose] def orthBlockRtMat : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0;
     1, 1, 0, 0;
     0, 0, 1, 1;
     0, 0, 0, 1]

variable [CharP F 2]

@[expose] def orthBlockLg : GL (Fin 4) F :=
  orthBlockUnitOfCube orthBlockLgMat (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [orthBlockLgMat, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero])

@[expose] def orthBlockRg : GL (Fin 4) F :=
  orthBlockUnitOfCube orthBlockRgMat (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [orthBlockRgMat, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero])

@[expose] def orthBlockRt : GL (Fin 4) F :=
  orthBlockUnitOfSq orthBlockRtMat (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [orthBlockRtMat, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero])

end BlockFour

section BlockFourRelations

variable [CharP F 2]

@[expose] def quadFourCoord : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun
    | Sum.inl 0 => 0
    | Sum.inl 1 => 1
    | Sum.inr 0 => 2
    | Sum.inr 1 => 3
  invFun
    | 0 => Sum.inl 0
    | 1 => Sum.inl 1
    | 2 => Sum.inr 0
    | 3 => Sum.inr 1
  left_inv := by
    rintro (i | i) <;> fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem orthBlockLg_pow_three : orthBlockLg (F := F) ^ 3 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [orthBlockLg, orthBlockUnitOfCube, orthBlockLgMat, Units.val_pow_eq_pow_val,
      Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero, pow_succ, pow_two]

theorem orthBlockRg_pow_three : orthBlockRg (F := F) ^ 3 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [orthBlockRg, orthBlockUnitOfCube, orthBlockRgMat, Units.val_pow_eq_pow_val,
      Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero, pow_succ, pow_two]

theorem orthBlockLg_comm_orthBlockRg :
    orthBlockLg (F := F) * orthBlockRg = orthBlockRg * orthBlockLg := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [orthBlockLg, orthBlockRg, orthBlockUnitOfCube, orthBlockLgMat, orthBlockRgMat,
      Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero, pow_succ, pow_two]

theorem orthBlockLg_ne_one : orthBlockLg (F := F) ≠ 1 := by
  intro h
  have h' : (orthBlockLg (F := F) : Matrix (Fin 4) (Fin 4) F) = 1 := by rw [h]; rfl
  rw [show (orthBlockLg (F := F) : Matrix (Fin 4) (Fin 4) F) = orthBlockLgMat from rfl] at h'
  have := congrFun (congrFun h' 0) 0
  simp [orthBlockLgMat] at this

theorem orthBlockRg_ne_one : orthBlockRg (F := F) ≠ 1 := by
  intro h
  have h' : (orthBlockRg (F := F) : Matrix (Fin 4) (Fin 4) F) = 1 := by rw [h]; rfl
  rw [show (orthBlockRg (F := F) : Matrix (Fin 4) (Fin 4) F) = orthBlockRgMat from rfl] at h'
  have := congrFun (congrFun h' 0) 0
  simp [orthBlockRgMat] at this

end BlockFourRelations

section AddBlock

variable [CharP F 2]

@[expose] def sumCommMiddle (A B : Type*) : (A ⊕ B) ⊕ (A ⊕ B) ≃ (A ⊕ A) ⊕ (B ⊕ B) where
  toFun x :=
    match x with
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
    | Sum.inr (Sum.inl a) => Sum.inl (Sum.inr a)
    | Sum.inr (Sum.inr b) => Sum.inr (Sum.inr b)
  invFun x :=
    match x with
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr a) => Sum.inr (Sum.inl a)
    | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
    | Sum.inr (Sum.inr b) => Sum.inr (Sum.inr b)
  left_inv := by rintro ((a | b) | (a | b)) <;> rfl
  right_inv := by rintro ((a | a') | (b | b')) <;> rfl

@[expose] noncomputable def sumArrowProd (A B : Type*) : ((A ⊕ B) → F) ≃ₗ[F] (A → F) × (B → F) where
  toFun f := (fun a => f (Sum.inl a), fun b => f (Sum.inr b))
  invFun p := Sum.elim p.1 p.2
  left_inv f := by funext x; rcases x with a | b <;> rfl
  right_inv p := by ext <;> rfl
  map_add' f g := by ext <;> rfl
  map_smul' c f := by ext <;> rfl

@[expose] def quadSuccIdx (m : ℕ) : Fin (m + 2) ≃ Fin m ⊕ Fin 2 := finSumFinEquiv.symm

@[expose] def quadAddCoord (m : ℕ) :
    Fin (m + 2) ⊕ Fin (m + 2) ≃ (Fin m ⊕ Fin m) ⊕ (Fin 2 ⊕ Fin 2) :=
  (Equiv.sumCongr (quadSuccIdx m) (quadSuccIdx m)).trans (sumCommMiddle (Fin m) (Fin 2))

@[expose] noncomputable def quadAddBlockEquiv (m : ℕ) :
    (Fin (m + 2) ⊕ Fin (m + 2) → F) ≃ₗ[F]
      ((Fin m ⊕ Fin m → F) × (Fin 2 ⊕ Fin 2 → F)) :=
  (LinearEquiv.funCongrLeft F F (quadAddCoord m).symm).trans
    (sumArrowProd (Fin m ⊕ Fin m) (Fin 2 ⊕ Fin 2))

theorem quadAddBlockEquiv_apply (m : ℕ) (v : Fin (m + 2) ⊕ Fin (m + 2) → F) :
    quadAddBlockEquiv (F := F) m v =
      (fun a => v ((quadAddCoord m).symm (Sum.inl a)),
       fun k => v ((quadAddCoord m).symm (Sum.inr k))) := rfl

theorem quadPlus_add_two (m : ℕ) (v : Fin (m + 2) ⊕ Fin (m + 2) → F) :
    quadPlus (m + 2) F v =
      quadPlus m F (quadAddBlockEquiv (F := F) m v).1 +
        quadPlus 2 F (quadAddBlockEquiv (F := F) m v).2 := by
  rw [quadPlus_apply, quadPlus_apply, quadPlus_apply]
  rw [Fin.sum_univ_add (f := fun i => v (Sum.inl i) * v (Sum.inr i))]
  have h1 : ∀ j : Fin m,
      v (Sum.inl (Fin.castAdd 2 j)) * v (Sum.inr (Fin.castAdd 2 j)) =
        (quadAddBlockEquiv (F := F) m v).1 (Sum.inl j) *
          (quadAddBlockEquiv (F := F) m v).1 (Sum.inr j) := by
    intro j
    simp [quadAddBlockEquiv_apply, quadAddCoord, sumCommMiddle, quadSuccIdx, finSumFinEquiv]
  have h2 : ∀ r : Fin 2,
      v (Sum.inl (Fin.natAdd m r)) * v (Sum.inr (Fin.natAdd m r)) =
        (quadAddBlockEquiv (F := F) m v).2 (Sum.inl r) *
          (quadAddBlockEquiv (F := F) m v).2 (Sum.inr r) := by
    intro r
    fin_cases r <;>
      simp [quadAddBlockEquiv_apply, quadAddCoord, sumCommMiddle, quadSuccIdx, finSumFinEquiv]
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_congr rfl fun r _ => h2 r]

end AddBlock

section BlockTwo

variable [CharP F 2]

@[expose] noncomputable def quadFourReindex : (Fin 4 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F) :=
  LinearEquiv.funCongrLeft F F quadFourCoord

@[expose] noncomputable def quadFourConj (g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) :
    (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F) :=
  quadFourReindex.symm.trans (g.trans quadFourReindex)

theorem quadFourConj_one : quadFourConj (F := F) 1 = 1 := by
  ext v
  simp [quadFourConj]

theorem quadFourConj_mul (g h : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) :
    quadFourConj (g * h) = quadFourConj g * quadFourConj h := by
  ext v
  simp [quadFourConj, LinearEquiv.mul_apply]

@[expose] noncomputable def quadFourConjHom :
    ((Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) →* ((Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)) where
  toFun := quadFourConj
  map_one' := quadFourConj_one
  map_mul' := quadFourConj_mul

theorem quadFourConj_leftInverse (e : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) :
    quadFourReindex.trans ((quadFourConj e).trans quadFourReindex.symm) = e := by
  ext v
  simp [quadFourConj]

theorem quadFourConj_injective : Function.Injective (quadFourConj (F := F)) := by
  intro g h gh
  have := congrArg (fun e => quadFourReindex.trans (e.trans quadFourReindex.symm)) gh
  rwa [quadFourConj_leftInverse, quadFourConj_leftInverse] at this

@[expose] noncomputable def blockLg (F : Type) [Field F] [CharP F 2] :
    (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F) :=
  quadFourConj (toLinEquiv (Fin 4) F orthBlockLg)

@[expose] noncomputable def blockRg (F : Type) [Field F] [CharP F 2] :
    (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F) :=
  quadFourConj (toLinEquiv (Fin 4) F orthBlockRg)

@[expose] noncomputable def blockRt (F : Type) [Field F] [CharP F 2] :
    (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F) :=
  quadFourConj (toLinEquiv (Fin 4) F orthBlockRt)

theorem blockLg_ne_one : blockLg F ≠ 1 := by
  intro h
  have h1 : quadFourConj (toLinEquiv (Fin 4) F orthBlockLg) =
      quadFourConj (1 : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) := by
    rw [quadFourConj_one]
    simpa [blockLg] using h
  have h2 := quadFourConj_injective (F := F) h1
  exact orthBlockLg_ne_one (F := F) ((toLinEquiv (Fin 4) F).injective (by simpa using h2))

theorem blockRg_ne_one : blockRg F ≠ 1 := by
  intro h
  have h1 : quadFourConj (toLinEquiv (Fin 4) F orthBlockRg) =
      quadFourConj (1 : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) := by
    rw [quadFourConj_one]
    simpa [blockRg] using h
  have h2 := quadFourConj_injective (F := F) h1
  exact orthBlockRg_ne_one (F := F) ((toLinEquiv (Fin 4) F).injective (by simpa using h2))

theorem orthBlockRt_ne_one : orthBlockRt (F := F) ≠ 1 := by
  intro h
  have h' : (orthBlockRt (F := F) : Matrix (Fin 4) (Fin 4) F) = 1 := by rw [h]; rfl
  rw [show (orthBlockRt (F := F) : Matrix (Fin 4) (Fin 4) F) = orthBlockRtMat from rfl] at h'
  have := congrFun (congrFun h' 1) 0
  simp [orthBlockRtMat] at this

theorem blockRt_ne_one : blockRt F ≠ 1 := by
  intro h
  have h1 : quadFourConj (toLinEquiv (Fin 4) F orthBlockRt) =
      quadFourConj (1 : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) := by
    rw [quadFourConj_one]
    simpa [blockRt] using h
  have h2 := quadFourConj_injective (F := F) h1
  exact orthBlockRt_ne_one (F := F) ((toLinEquiv (Fin 4) F).injective (by simpa using h2))

end BlockTwo

section BlockEichler

variable [CharP F 2]

private abbrev qbe₀ : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 0) 1

private abbrev qbe₁ : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 1) 1

private abbrev qbf₀ : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inr 0) 1

private abbrev qbf₁ : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inr 1) 1

private theorem quadPlus_two_qbe₀ : (quadPlus 2 F) qbe₀ = 0 := by
  rw [quadPlus_apply]; simp [qbe₀]

private theorem quadPlus_two_qbe₁ : (quadPlus 2 F) qbe₁ = 0 := by
  rw [quadPlus_apply]; simp [qbe₁]

private theorem quadPlus_two_qbf₀ : (quadPlus 2 F) qbf₀ = 0 := by
  rw [quadPlus_apply]; simp [qbf₀]

private theorem polar_qbe₀_qbe₁ : polar (quadPlus 2 F) qbe₀ qbe₁ = 0 := by
  rw [polar_quadPlus]; simp [qbe₀, qbe₁]

private theorem polar_qbe₀_qbf₁ : polar (quadPlus 2 F) qbe₀ qbf₁ = 0 := by
  rw [polar_quadPlus]; simp [qbe₀, qbf₁]

private theorem polar_qbf₀_qbe₁ : polar (quadPlus 2 F) qbf₀ qbe₁ = 0 := by
  rw [polar_quadPlus]; simp [qbf₀, qbe₁]

private theorem polar_qbf₀_qbf₁ : polar (quadPlus 2 F) qbf₀ qbf₁ = 0 := by
  rw [polar_quadPlus]; simp [qbf₀, qbf₁]

private theorem polar_qbe₁_qbf₀ : polar (quadPlus 2 F) qbe₁ qbf₀ = 0 := by
  rw [polar_quadPlus]; simp [qbe₁, qbf₀]

private theorem blockRt_apply_basis (c : Fin 2 ⊕ Fin 2) :
    blockRt F (Pi.single c 1) = eichler (quadPlus 2 F) qbf₀ qbe₁ (Pi.single c 1) := by
  rw [eichler_apply quadPlus_two_qbf₀ polar_qbf₀_qbe₁]
  funext i
  rcases c with c | c <;> fin_cases c <;> rcases i with i | i <;> fin_cases i <;>
    simp [blockRt, quadFourConj, quadFourReindex, LinearEquiv.funCongrLeft, LinearMap.funLeft_apply,
      quadFourCoord, quadFour, polar_quadPlus, Fin.sum_univ_two, Pi.single_apply,
      orthBlockRt, orthBlockUnitOfSq, orthBlockRtMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      quadPlus_apply, CharTwo.two_eq_zero, CharTwo.neg_eq, CharTwo.sub_eq_add,
      CharTwo.add_self_eq_zero, qbe₀, qbe₁, qbf₀, qbf₁]

private theorem blockLg_apply_basis (c : Fin 2 ⊕ Fin 2) :
    blockLg F (Pi.single c 1) =
      (eichler (quadPlus 2 F) qbe₀ qbe₁ * eichler (quadPlus 2 F) qbf₀ qbf₁) (Pi.single c 1) := by
  rw [LinearEquiv.mul_apply, eichler_apply quadPlus_two_qbf₀ polar_qbf₀_qbf₁,
    eichler_apply quadPlus_two_qbe₀ polar_qbe₀_qbe₁]
  funext i
  rcases c with c | c <;> fin_cases c <;> rcases i with i | i <;> fin_cases i <;>
    simp [blockLg, quadFourConj, quadFourReindex, LinearEquiv.funCongrLeft, LinearMap.funLeft_apply,
      quadFourCoord, quadFour, polar_quadPlus, Fin.sum_univ_two, Pi.single_apply,
      orthBlockLg, orthBlockUnitOfCube, orthBlockLgMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      quadPlus_apply, CharTwo.two_eq_zero, CharTwo.neg_eq, CharTwo.sub_eq_add,
      CharTwo.add_self_eq_zero, qbe₀, qbe₁, qbf₀, qbf₁]

private theorem blockRg_apply_basis (c : Fin 2 ⊕ Fin 2) :
    blockRg F (Pi.single c 1) =
      (eichler (quadPlus 2 F) qbe₀ qbf₁ * eichler (quadPlus 2 F) qbe₁ qbf₀) (Pi.single c 1) := by
  rw [LinearEquiv.mul_apply, eichler_apply quadPlus_two_qbe₁ polar_qbe₁_qbf₀,
    eichler_apply quadPlus_two_qbe₀ polar_qbe₀_qbf₁]
  funext i
  rcases c with c | c <;> fin_cases c <;> rcases i with i | i <;> fin_cases i <;>
    simp [blockRg, quadFourConj, quadFourReindex, LinearEquiv.funCongrLeft, LinearMap.funLeft_apply,
      quadFourCoord, quadFour, polar_quadPlus, Fin.sum_univ_two, Pi.single_apply,
      orthBlockRg, orthBlockUnitOfCube, orthBlockRgMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      quadPlus_apply, CharTwo.two_eq_zero, CharTwo.neg_eq, CharTwo.sub_eq_add,
      CharTwo.add_self_eq_zero, qbe₀, qbe₁, qbf₀, qbf₁]

private theorem blockRt_eq_eichler :
    blockRt F = eichler (quadPlus 2 F) qbf₀ qbe₁ := by
  have h : (blockRt F).toLinearMap = (eichler (quadPlus 2 F) qbf₀ qbe₁).toLinearMap := by
    refine (Pi.basisFun F (Fin 2 ⊕ Fin 2)).ext ?_
    intro c
    simpa [Pi.basisFun_apply] using blockRt_apply_basis (F := F) c
  exact LinearEquiv.ext fun x => LinearMap.congr_fun h x

private theorem blockLg_eq_eichler :
    blockLg F = eichler (quadPlus 2 F) qbe₀ qbe₁ * eichler (quadPlus 2 F) qbf₀ qbf₁ := by
  have h : (blockLg F).toLinearMap =
      (eichler (quadPlus 2 F) qbe₀ qbe₁ * eichler (quadPlus 2 F) qbf₀ qbf₁).toLinearMap := by
    refine (Pi.basisFun F (Fin 2 ⊕ Fin 2)).ext ?_
    intro c
    simpa [Pi.basisFun_apply] using blockLg_apply_basis (F := F) c
  exact LinearEquiv.ext fun x => LinearMap.congr_fun h x

private theorem blockRg_eq_eichler :
    blockRg F = eichler (quadPlus 2 F) qbe₀ qbf₁ * eichler (quadPlus 2 F) qbe₁ qbf₀ := by
  have h : (blockRg F).toLinearMap =
      (eichler (quadPlus 2 F) qbe₀ qbf₁ * eichler (quadPlus 2 F) qbe₁ qbf₀).toLinearMap := by
    refine (Pi.basisFun F (Fin 2 ⊕ Fin 2)).ext ?_
    intro c
    simpa [Pi.basisFun_apply] using blockRg_apply_basis (F := F) c
  exact LinearEquiv.ext fun x => LinearMap.congr_fun h x

private theorem blockLg_mem_elementaryGroup :
    blockLg F ∈ orthElementaryGroup (quadPlus 2 F) := by
  rw [blockLg_eq_eichler, orthElementaryGroup]
  exact mul_mem (eichler_mem_elementaryGroup _ _ _) (eichler_mem_elementaryGroup _ _ _)

private theorem blockRg_mem_elementaryGroup :
    blockRg F ∈ orthElementaryGroup (quadPlus 2 F) := by
  rw [blockRg_eq_eichler, orthElementaryGroup]
  exact mul_mem (eichler_mem_elementaryGroup _ _ _) (eichler_mem_elementaryGroup _ _ _)

private theorem blockRt_mem_elementaryGroup :
    blockRt F ∈ orthElementaryGroup (quadPlus 2 F) := by
  rw [blockRt_eq_eichler, orthElementaryGroup]
  exact eichler_mem_elementaryGroup _ _ _

private theorem blockRt_sq : blockRt F ^ 2 = 1 := by
  rw [blockRt_eq_eichler, pow_two, eichler_mul polar_qbf₀_qbe₁ polar_qbf₀_qbe₁,
    CharTwo.add_self_eq_zero, eichler_zero_right]

private theorem blockLg_pow_three : blockLg F ^ 3 = 1 := by
  have h1 : ((toLinEquiv (Fin 4) F) (orthBlockLg (F := F))) ^ 3 = 1 := by
    rw [← map_pow, orthBlockLg_pow_three, map_one]
  change (quadFourConjHom ((toLinEquiv (Fin 4) F) (orthBlockLg (F := F)))) ^ 3 = 1
  rw [← map_pow, h1, map_one]

private theorem blockRg_pow_three : blockRg F ^ 3 = 1 := by
  have h1 : ((toLinEquiv (Fin 4) F) (orthBlockRg (F := F))) ^ 3 = 1 := by
    rw [← map_pow, orthBlockRg_pow_three, map_one]
  change (quadFourConjHom ((toLinEquiv (Fin 4) F) (orthBlockRg (F := F)))) ^ 3 = 1
  rw [← map_pow, h1, map_one]

private theorem orthBlockLg_comm_orthBlockRt :
    orthBlockLg (F := F) * orthBlockRt = orthBlockRt * orthBlockLg := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [orthBlockLg, orthBlockRt, orthBlockUnitOfCube, orthBlockUnitOfSq, orthBlockLgMat,
      orthBlockRtMat, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero, pow_succ,
      pow_two]

private theorem blockLg_comm_blockRt : blockLg F * blockRt F = blockRt F * blockLg F := by
  have h := orthBlockLg_comm_orthBlockRt (F := F)
  change quadFourConj ((toLinEquiv (Fin 4) F) (orthBlockLg (F := F))) *
      quadFourConj ((toLinEquiv (Fin 4) F) (orthBlockRt (F := F))) =
    quadFourConj ((toLinEquiv (Fin 4) F) (orthBlockRt (F := F))) *
      quadFourConj ((toLinEquiv (Fin 4) F) (orthBlockLg (F := F)))
  rw [← quadFourConj_mul, ← quadFourConj_mul, ← map_mul, ← map_mul, h]

private theorem blockLg_comm_blockRg : blockLg F * blockRg F = blockRg F * blockLg F := by
  have h := orthBlockLg_comm_orthBlockRg (F := F)
  change quadFourConj ((toLinEquiv (Fin 4) F) (orthBlockLg (F := F))) *
      quadFourConj ((toLinEquiv (Fin 4) F) (orthBlockRg (F := F))) =
    quadFourConj ((toLinEquiv (Fin 4) F) (orthBlockRg (F := F))) *
      quadFourConj ((toLinEquiv (Fin 4) F) (orthBlockLg (F := F)))
  rw [← quadFourConj_mul, ← quadFourConj_mul, ← map_mul, ← map_mul, h]

private theorem orthBlockRg_ne_orthBlockLg : orthBlockRg (F := F) ≠ orthBlockLg := by
  intro h
  have h' : (orthBlockRg (F := F) : Matrix (Fin 4) (Fin 4) F) = orthBlockLgMat := by
    rw [h]; rfl
  rw [show (orthBlockRg (F := F) : Matrix (Fin 4) (Fin 4) F) = orthBlockRgMat from rfl] at h'
  have := congrFun (congrFun h' 0) 1
  simp [orthBlockRgMat, orthBlockLgMat] at this

private theorem orthBlockRg_ne_orthBlockLg_sq : orthBlockRg (F := F) ≠ orthBlockLg ^ 2 := by
  intro h
  have h' : (orthBlockRg (F := F) : Matrix (Fin 4) (Fin 4) F) =
      (orthBlockLgMat : Matrix (Fin 4) (Fin 4) F) ^ 2 := by
    rw [h, Units.val_pow_eq_pow_val]
    rfl
  rw [show (orthBlockRg (F := F) : Matrix (Fin 4) (Fin 4) F) = orthBlockRgMat from rfl] at h'
  have := congrFun (congrFun h' 0) 0
  simp [orthBlockRgMat, orthBlockLgMat, pow_two, Matrix.mul_apply, Fin.sum_univ_four,
    CharTwo.add_self_eq_zero] at this

private theorem blockRg_ne_blockLg : blockRg F ≠ blockLg F := by
  intro h
  apply orthBlockRg_ne_orthBlockLg (F := F)
  have h1 : quadFourConj (toLinEquiv (Fin 4) F (orthBlockRg (F := F))) =
      quadFourConj (toLinEquiv (Fin 4) F (orthBlockLg (F := F))) := by
    simpa [blockRg, blockLg] using h
  exact (toLinEquiv (Fin 4) F).injective (quadFourConj_injective (F := F) h1)

private theorem blockRg_ne_blockLg_sq : blockRg F ≠ blockLg F ^ 2 := by
  intro h
  have hL : blockLg F ^ 2 =
      quadFourConj ((toLinEquiv (Fin 4) F (orthBlockLg (F := F))) ^ 2) := by
    change (quadFourConjHom ((toLinEquiv (Fin 4) F) (orthBlockLg (F := F)))) ^ 2 = _
    rw [← map_pow]
    rfl
  rw [hL] at h
  have h' : (toLinEquiv (Fin 4) F) (orthBlockRg (F := F)) =
      (toLinEquiv (Fin 4) F) (orthBlockLg ^ 2) := by
    rw [map_pow]
    exact quadFourConj_injective (F := F) (by simpa [blockRg] using h)
  exact orthBlockRg_ne_orthBlockLg_sq (F := F) ((toLinEquiv (Fin 4) F).injective h')

end BlockEichler

section WitnessDef

variable [CharP F 2]

def QuadWitness (V : Type*) [AddCommGroup V] [Module F V] (Q : QuadraticForm F V) (k : ℕ) : Prop :=
  ∃ E U : Subgroup (CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup Q),
    IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k ∧
      U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set (CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup Q))

theorem QuadWitness.of_isometryEquiv {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {Q : QuadraticForm F V} {R : QuadraticForm F W}
    (e : Q.IsometryEquiv R) {k : ℕ} (h : QuadWitness W R k) : QuadWitness V Q k := by
  obtain ⟨E, U, hE, hEcard, hU, hU2, hEN⟩ := h
  let ψ : ↥(orthElementaryGroup R) →* ↥(orthElementaryGroup Q) :=
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.elementaryIsometryEquiv
      e).symm.toMonoidHom
  have hinj : Function.Injective ψ :=
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.elementaryIsometryEquiv
      e).symm.injective
  refine ⟨E.map ψ, U.map ψ, hE.map ψ, ?_, ?_, hU2.map ψ, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hEcard]
  · exact fun hbot => hU ((Subgroup.map_eq_bot_iff_of_injective U hinj).mp hbot)
  · rw [Subgroup.le_normalizer_iff] at hEN ⊢
    intro x hx y hy
    rw [Subgroup.mem_map] at hx hy ⊢
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hconj : ψ x' * ψ y' * (ψ x')⁻¹ = ψ (x' * y' * (x')⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [hconj]
    exact Subgroup.mem_map_of_mem ψ (hEN x' hx' y' hy')

private theorem isElemAbelian_prod {G H : Type*} [Group G] [Group H] {p : ℕ}
    {E : Subgroup G} {B : Subgroup H} (hE : IsElemAbelian p E) (hB : IsElemAbelian p B) :
    IsElemAbelian p (E.prod B) := by
  haveI := hE.1
  haveI := hB.1
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · exact congrArg Subtype.val (mul_comm' (⟨x.1.1, (Subgroup.mem_prod.mp x.2).1⟩ : E)
        (⟨y.1.1, (Subgroup.mem_prod.mp y.2).1⟩ : E))
    · exact congrArg Subtype.val (mul_comm' (⟨x.1.2, (Subgroup.mem_prod.mp x.2).2⟩ : B)
        (⟨y.1.2, (Subgroup.mem_prod.mp y.2).2⟩ : B))
  · refine Prod.ext ?_ ?_
    · exact hE.2 x.1 (Subgroup.mem_prod.mp hx).1
    · exact hB.2 x.2 (Subgroup.mem_prod.mp hx).2

private theorem isPGroup_prod_bot {G H : Type*} [Group G] [Group H] {p : ℕ} {U : Subgroup G}
    (h : IsPGroup p U) : IsPGroup p (U.prod (⊥ : Subgroup H)) := by
  intro x
  obtain ⟨n, hn⟩ := h ⟨x.1.1, (Subgroup.mem_prod.mp x.2).1⟩
  refine ⟨n, ?_⟩
  refine Subtype.ext (Prod.ext ?_ ?_)
  · simpa using congrArg Subtype.val hn
  · have hx2 : x.1.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp x.2).2
    simp [hx2]

private theorem prod_le_normalizer_prod_bot {G H : Type*} [Group G] [Group H]
    {E U : Subgroup G} {B : Subgroup H} (h : E ≤ Subgroup.normalizer (U : Set G)) :
    E.prod B ≤ Subgroup.normalizer ((U.prod (⊥ : Subgroup H) : Subgroup (G × H)) :
      Set (G × H)) := by
  rw [Subgroup.le_normalizer_iff] at h ⊢
  intro x hx y hy
  rw [Subgroup.mem_prod] at hx hy ⊢
  obtain ⟨hxE, -⟩ := hx
  obtain ⟨hyU, hyB⟩ := hy
  refine ⟨?_, ?_⟩
  · simpa using h x.1 hxE y.1 hyU
  · rw [Subgroup.mem_bot] at hyB ⊢
    simp [hyB]

end WitnessDef

section WitnessBase

variable [CharP F 2] [Finite F]

private theorem finite_quadPlus_two :
    Finite ((Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (Fin 2 ⊕ Fin 2 → F) := inferInstance
  exact Finite.of_injective
    (fun e : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F) => (e : _ → _))
    DFunLike.coe_injective

private theorem exist_witness_quadPlus_two :
    QuadWitness (F := F) (Fin 2 ⊕ Fin 2 → F) (quadPlus 2 F) 1 := by
  haveI : Finite ((Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)) := finite_quadPlus_two
  let g : orthElementaryGroup (quadPlus 2 F) := ⟨blockLg F, blockLg_mem_elementaryGroup⟩
  let u : orthElementaryGroup (quadPlus 2 F) := ⟨blockRt F, blockRt_mem_elementaryGroup⟩
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa [g] using blockLg_pow_three (F := F))
  have hg1 : g ≠ 1 := fun hh => blockLg_ne_one (F := F) (by simpa [g] using congrArg Subtype.val hh)
  have hu2 : u ^ 2 = 1 := Subtype.ext (by simpa [u] using blockRt_sq (F := F))
  have hu1 : u ≠ 1 := fun hh => blockRt_ne_one (F := F) (by simpa [u] using congrArg Subtype.val hh)
  have hcomm : g * u = u * g := Subtype.ext (by simpa [g, u] using blockLg_comm_blockRt (F := F))
  have hcommem : ∀ x ∈ Subgroup.zpowers g, ∀ y ∈ Subgroup.zpowers u, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute g u from hcomm) m n).eq
  refine ⟨Subgroup.zpowers g, Subgroup.zpowers u, ?_, ?_, ?_, ?_, ?_⟩
  · exact isElemAbelian_zpowers (p := 3) hg3
  · rw [Nat.card_zpowers, orderOf_eq_prime hg3 hg1, pow_one]
  · rw [Ne, Subgroup.zpowers_eq_bot]
    exact hu1
  · exact (isElemAbelian_zpowers (p := 2) hu2).isPGroup
  · rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have hxy : x * y * x⁻¹ = y := by rw [hcommem x hx y hy]; group
    rw [hxy]
    exact hy

private theorem exist_blockNine_quadPlus_two :
    ∃ B : Subgroup (orthElementaryGroup (quadPlus 2 F)), IsElemAbelian 3 B ∧ Nat.card B = 9 := by
  haveI : Finite ((Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)) := finite_quadPlus_two
  let g : orthElementaryGroup (quadPlus 2 F) := ⟨blockLg F, blockLg_mem_elementaryGroup⟩
  let h : orthElementaryGroup (quadPlus 2 F) := ⟨blockRg F, blockRg_mem_elementaryGroup⟩
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa [g] using blockLg_pow_three (F := F))
  have hg1 : g ≠ 1 := fun hh => blockLg_ne_one (F := F) (by simpa [g] using congrArg Subtype.val hh)
  have hh3 : h ^ 3 = 1 := Subtype.ext (by simpa [h] using blockRg_pow_three (F := F))
  have hh1 : h ≠ 1 := fun hh' => blockRg_ne_one (F := F) (by simpa [h] using congrArg Subtype.val hh')
  have hhl : h ≠ g := fun hh' =>
    blockRg_ne_blockLg (F := F) (by simpa [g, h] using congrArg Subtype.val hh')
  have hhl2 : h ≠ g ^ 2 := fun hh' =>
    blockRg_ne_blockLg_sq (F := F) (by simpa [g, h] using congrArg Subtype.val hh')
  have hc : g * h = h * g := Subtype.ext (by simpa [g, h] using blockLg_comm_blockRg (F := F))
  have hmem : h ∉ Subgroup.zpowers g := by
    rw [CFSG.Walter.JT.mem_zpowers_iff_of_orderOf_three (z := g) (orderOf_eq_prime hg3 hg1)]
    simp only [not_or, not_not]
    exact ⟨hh1, hhl, hhl2⟩
  refine ⟨Subgroup.zpowers g ⊔ Subgroup.zpowers h,
    ?_, CFSG.HardMathSupport.Lang.E27Lie.card_zpowers_sup_zpowers_of_order_three hc hg3 hg1 hh3 hmem⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CFSG.IsElementaryAbelian 3 ↥(Subgroup.zpowers g) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (p := 3) hg3
  haveI : CFSG.IsElementaryAbelian 3 ↥(Subgroup.zpowers h) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (p := 3) hh3
  have hle : Subgroup.zpowers h ≤ Subgroup.centralizer (Subgroup.zpowers g : Set _) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hn]
    exact (Commute.zpow_left (show Commute g h from hc) n).eq
  exact CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
    (CFSG.IsElementaryAbelian.sup_of_le_centralizer hle)

end WitnessBase

section TailModel

variable [CharP F 2]

theorem eichler_prod_snd {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (Q : QuadraticForm K V) (R : QuadraticForm K W) (u w : W) :
    eichler (Q.prod R) ((0, u) : V × W) ((0, w) : V × W) =
      (LinearEquiv.refl K V).prodCongr (eichler R u w) := by
  by_cases h : R u = 0 ∧ polar R u w = 0
  · have hu : (Q.prod R) ((0, u) : V × W) = 0 := by
      rw [QuadraticMap.prod_apply, QuadraticMap.map_zero, zero_add]; exact h.1
    have hw : polar (Q.prod R) ((0, u) : V × W) ((0, w) : V × W) = 0 := by
      rw [polar_prod, polar_zero_left, zero_add]; exact h.2
    refine LinearEquiv.ext fun x => ?_
    rw [eichler_apply hu hw, LinearEquiv.prodCongr_apply, eichler_apply h.1 h.2]
    ext <;> simp [polar_prod]
  · have h' : ¬((Q.prod R) ((0, u) : V × W) = 0 ∧
        polar (Q.prod R) ((0, u) : V × W) ((0, w) : V × W) = 0) := by
      rwa [QuadraticMap.prod_apply, QuadraticMap.map_zero, zero_add, polar_prod, polar_zero_left,
        zero_add]
    rw [eichler_of_not h', eichler_of_not h]
    exact LinearEquiv.ext fun x => by simp

theorem orthElementaryGroup_map_prodHom_le
    {F : Type} [Field F] {A : Type} [AddCommGroup A] [Module F A] {r : ℕ}
    (qA : QuadraticForm F A) :
    (orthElementaryGroup (quadPlus r F)).map (prodHom (K := F) (r := r) A) ≤
      orthElementaryGroup (quadTail r qA) := by
  rw [orthElementaryGroup, orthElementaryGroup, Subgroup.map_le_iff_le_comap]
  refine elementaryGroup_le_of_eichler_mem ?_
  intro u w hu hw
  rw [Subgroup.mem_comap]
  change prodHom A (eichler (quadPlus r F) u w) ∈ elementaryGroup (quadTail r qA)
  rw [prodHom_apply, ← eichler_prod_fst]
  exact eichler_mem_elementaryGroup _ _ _

theorem prodHom_apply_injective
    {F : Type} [Field F] {A : Type} [AddCommGroup A] [Module F A] {r : ℕ} :
    Function.Injective (prodHom (K := F) (r := r) A) := by
  intro g h hgh
  apply LinearEquiv.ext
  intro v
  have h' := congrArg
    (fun e : ((Fin r ⊕ Fin r → F) × A) ≃ₗ[F] ((Fin r ⊕ Fin r → F) × A) => e (v, 0)) hgh
  rw [prodHom_apply, prodHom_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.prodCongr_apply] at h'
  exact (Prod.ext_iff.1 h').1

@[expose] noncomputable def orthElementaryGroupProdHom
    {F : Type} [Field F] {A : Type} [AddCommGroup A] [Module F A] {r : ℕ}
    (qA : QuadraticForm F A) :
    orthElementaryGroup (quadPlus r F) →* orthElementaryGroup (quadTail r qA) :=
  ((prodHom (K := F) (r := r) A).comp (orthElementaryGroup (quadPlus r F)).subtype).codRestrict _
    (fun g : orthElementaryGroup (quadPlus r F) =>
      orthElementaryGroup_map_prodHom_le (r := r) (qA := qA)
        (Subgroup.mem_map_of_mem (prodHom (K := F) (r := r) A) g.2))

theorem orthElementaryGroupProdHom_apply
    {F : Type} [Field F] {A : Type} [AddCommGroup A] [Module F A] {r : ℕ}
    (qA : QuadraticForm F A) (g : orthElementaryGroup (quadPlus r F)) :
    ((orthElementaryGroupProdHom (r := r) qA g : orthElementaryGroup (quadTail r qA)) :
      ((Fin r ⊕ Fin r → F) × A) ≃ₗ[F] ((Fin r ⊕ Fin r → F) × A)) =
      (g : (Fin r ⊕ Fin r → F) ≃ₗ[F] (Fin r ⊕ Fin r → F)).prodCongr
        (LinearEquiv.refl F A) :=
  rfl

theorem orthElementaryGroupProdHom_injective
    {F : Type} [Field F] {A : Type} [AddCommGroup A] [Module F A] {r : ℕ}
    (qA : QuadraticForm F A) : Function.Injective (orthElementaryGroupProdHom (r := r) qA) := by
  intro x y hxy
  have h : prodHom (K := F) (r := r) A
        (x : (Fin r ⊕ Fin r → F) ≃ₗ[F] (Fin r ⊕ Fin r → F)) =
      prodHom (K := F) (r := r) A
        (y : (Fin r ⊕ Fin r → F) ≃ₗ[F] (Fin r ⊕ Fin r → F)) := by
    simpa only [orthElementaryGroupProdHom, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype] using congrArg
        (fun z : orthElementaryGroup (quadTail r qA) =>
          (z : ((Fin r ⊕ Fin r → F) × A) ≃ₗ[F] ((Fin r ⊕ Fin r → F) × A))) hxy
  exact Subtype.ext (prodHom_apply_injective (A := A) (r := r) h)

@[expose] noncomputable def prodCongrSndHom (m : ℕ) :
    ((Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)) →*
      (((Fin m ⊕ Fin m → F) × (Fin 2 ⊕ Fin 2 → F)) ≃ₗ[F]
        ((Fin m ⊕ Fin m → F) × (Fin 2 ⊕ Fin 2 → F))) where
  toFun b := (LinearEquiv.refl F (Fin m ⊕ Fin m → F)).prodCongr b
  map_one' := by ext x <;> rfl
  map_mul' p q := by ext x <;> rfl

theorem prodCongrSndHom_apply (m : ℕ) (b : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)) :
    prodCongrSndHom (F := F) m b =
      (LinearEquiv.refl F (Fin m ⊕ Fin m → F)).prodCongr b :=
  rfl

theorem map_orthElementaryGroup_prodCongrSnd_le (m : ℕ) :
    (orthElementaryGroup (quadPlus 2 F)).map (prodCongrSndHom (F := F) m) ≤
      orthElementaryGroup (quadTail m (quadPlus 2 F)) := by
  rw [orthElementaryGroup, Subgroup.map_le_iff_le_comap]
  refine elementaryGroup_le_of_eichler_mem ?_
  intro u w hu hw
  rw [Subgroup.mem_comap]
  change prodCongrSndHom (F := F) m (eichler (quadPlus 2 F) u w) ∈
    elementaryGroup (quadTail m (quadPlus 2 F))
  rw [prodCongrSndHom_apply, ← eichler_prod_snd]
  exact eichler_mem_elementaryGroup _ _ _

@[expose] noncomputable def quadAddTailIsometry (m : ℕ) :
    (quadPlus (m + 2) F).IsometryEquiv (quadTail m (quadPlus 2 F)) where
  toLinearEquiv := quadAddBlockEquiv (F := F) m
  map_app' v := by
    rw [quadTail_apply]
    exact (quadPlus_add_two (F := F) m v).symm

theorem prodCongr_mem (m : ℕ) {g : (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F)}
    (hg : g ∈ orthElementaryGroup (quadPlus m F))
    {b : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)}
    (hb : b ∈ orthElementaryGroup (quadPlus 2 F)) :
    g.prodCongr b ∈ orthElementaryGroup (quadTail m (quadPlus 2 F)) := by
  have h1 : g.prodCongr (LinearEquiv.refl F (Fin 2 ⊕ Fin 2 → F)) ∈
      orthElementaryGroup (quadTail m (quadPlus 2 F)) := by
    have h := orthElementaryGroup_map_prodHom_le (F := F) (r := m)
      (A := Fin 2 ⊕ Fin 2 → F) (quadPlus 2 F)
      (Subgroup.mem_map_of_mem (prodHom (K := F) (r := m) (Fin 2 ⊕ Fin 2 → F)) hg)
    rwa [prodHom_apply] at h
  have h2 : (LinearEquiv.refl F (Fin m ⊕ Fin m → F)).prodCongr b ∈
      orthElementaryGroup (quadTail m (quadPlus 2 F)) := by
    have h := map_orthElementaryGroup_prodCongrSnd_le (F := F) m
      (Subgroup.mem_map_of_mem (prodCongrSndHom (F := F) m) hb)
    rwa [prodCongrSndHom_apply] at h
  have hmul : g.prodCongr b = (g.prodCongr (LinearEquiv.refl F (Fin 2 ⊕ Fin 2 → F))) *
      ((LinearEquiv.refl F (Fin m ⊕ Fin m → F)).prodCongr b) :=
    LinearEquiv.ext fun x => Prod.ext rfl rfl
  rw [hmul]
  exact mul_mem h1 h2

@[expose] noncomputable def tailProdHom (m : ℕ) :
    orthElementaryGroup (quadPlus m F) × orthElementaryGroup (quadPlus 2 F) →*
      orthElementaryGroup (quadTail m (quadPlus 2 F)) where
  toFun p := ⟨(p.1 : (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F)).prodCongr
      (p.2 : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)),
    prodCongr_mem (F := F) m p.1.2 p.2.2⟩
  map_one' := by
    refine Subtype.ext (LinearEquiv.ext fun x => Prod.ext rfl rfl)
  map_mul' p q := by
    refine Subtype.ext (LinearEquiv.ext fun x => Prod.ext rfl rfl)

theorem tailProdHom_injective (m : ℕ) : Function.Injective (tailProdHom (F := F) m) := by
  intro p q hpq
  have h : ((p.1 : (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F)).prodCongr
        (p.2 : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F))) =
      ((q.1 : (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F)).prodCongr
        (q.2 : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F))) := by
    have h' := congrArg (fun z : orthElementaryGroup (quadTail m (quadPlus 2 F)) =>
      (z : ((Fin m ⊕ Fin m → F) × (Fin 2 ⊕ Fin 2 → F)) ≃ₗ[F]
        ((Fin m ⊕ Fin m → F) × (Fin 2 ⊕ Fin 2 → F)))) hpq
    simpa [tailProdHom] using h'
  refine Prod.ext ?_ ?_
  · exact Subtype.ext (LinearEquiv.ext fun v => by
      have h' := congrArg (fun e => (e (v, 0)).1) h
      simpa using h')
  · exact Subtype.ext (LinearEquiv.ext fun w => by
      have h' := congrArg (fun e => (e (0, w)).2) h
      simpa using h')

@[expose] noncomputable def quadAddBlockHom (m : ℕ) :
    orthElementaryGroup (quadPlus m F) × orthElementaryGroup (quadPlus 2 F) →*
      orthElementaryGroup (quadPlus (m + 2) F) :=
  ((CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.elementaryIsometryEquiv
      (quadAddTailIsometry (F := F) m)).symm.toMonoidHom).comp (tailProdHom (F := F) m)

theorem quadAddBlockHom_injective (m : ℕ) : Function.Injective (quadAddBlockHom (F := F) m) := by
  intro x y hxy
  exact tailProdHom_injective (F := F) m
    ((CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.elementaryIsometryEquiv
      (quadAddTailIsometry (F := F) m)).symm.injective hxy)

end TailModel

section WitnessProof

variable [CharP F 2] [Finite F]

private theorem quadWitness_add_two (m : ℕ) (hm : 1 ≤ m)
    (h : QuadWitness (F := F) (Fin m ⊕ Fin m → F) (quadPlus m F) (m - 1)) :
    QuadWitness (F := F) (Fin (m + 2) ⊕ Fin (m + 2) → F) (quadPlus (m + 2) F) (m + 1) := by
  obtain ⟨E, U, hE, hEcard, hU, hU2, hEN⟩ := h
  obtain ⟨B, hB, hBcard⟩ := exist_blockNine_quadPlus_two (F := F)
  have hφ : Function.Injective (quadAddBlockHom (F := F) m) := quadAddBlockHom_injective m
  refine ⟨(E.prod B).map (quadAddBlockHom (F := F) m),
    (U.prod ⊥).map (quadAddBlockHom (F := F) m), (isElemAbelian_prod hE hB).map _,
    ?_, ?_, (isPGroup_prod_bot hU2).map _, ?_⟩
  · rw [Subgroup.card_map_of_injective hφ,
      Nat.card_congr (Subgroup.prodEquiv E B).toEquiv, Nat.card_prod, hEcard, hBcard]
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9, ← pow_add]
    congr 1
    omega
  · refine fun hbot => hU ?_
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have hmem : ((u, (1 : orthElementaryGroup (quadPlus 2 F))) :
        orthElementaryGroup (quadPlus m F) × orthElementaryGroup (quadPlus 2 F)) ∈ U.prod ⊥ := by
      rw [Subgroup.mem_prod]
      exact ⟨hu, Subgroup.one_mem _⟩
    rw [(Subgroup.map_eq_bot_iff_of_injective (U.prod ⊥) hφ).mp hbot] at hmem
    simpa using hmem
  · exact (Subgroup.map_mono (prod_le_normalizer_prod_bot hEN)).trans
      (Subgroup.le_normalizer_map (quadAddBlockHom (F := F) m))

private theorem exist_witness_quadPlus_three :
    QuadWitness (F := F) (Fin 3 ⊕ Fin 3 → F) (quadPlus 3 F) 2 := by
  have htail : QuadWitness (F := F) ((Fin 2 ⊕ Fin 2 → F) × (Fin 1 ⊕ Fin 1 → F))
      (quadTail 2 (quadPlus 1 F)) 2 := by
    set A := Fin 1 ⊕ Fin 1 → F
    set W := (Fin 2 ⊕ Fin 2 → F) × A
    set e : A := Pi.single (Sum.inl 0) 1 with he
    set u : W := (0, e) with hu
    set w₀ : W := (Pi.single (Sum.inl 0) 1, 0) with hw₀
    have hqu : (quadTail 2 (quadPlus 1 F)) u = 0 := by
      rw [quadTail_apply]
      simp [u, hu, e, quadPlus_apply]
    have huw₀ : polar (quadTail 2 (quadPlus 1 F)) u w₀ = 0 := by
      rw [polar_quadTail]
      simp [u, hu, w₀, hw₀, e]
    have hy₀_ne : eichler (quadTail 2 (quadPlus 1 F)) u w₀ ≠ 1 := by
      intro h1
      have h2 : eichler (quadTail 2 (quadPlus 1 F)) u w₀
          (0, (Pi.single (Sum.inr 0) 1 : A)) = (0, (Pi.single (Sum.inr 0) 1 : A)) := by
        rw [h1]
        exact LinearEquiv.refl_apply (0, (Pi.single (Sum.inr 0) 1 : A))
      rw [eichler_apply hqu huw₀] at h2
      simp [u, hu, w₀, hw₀, e, polar_quadTail, polar_quadPlus, quadPlus_apply, Pi.single_apply,
        Prod.ext_iff] at h2
    obtain ⟨B, hB, hBcard⟩ := exist_blockNine_quadPlus_two (F := F)
    let U : Subgroup (orthElementaryGroup (quadTail 2 (quadPlus 1 F))) :=
      (rootGroup (quadTail 2 (quadPlus 1 F)) u).subgroupOf
        (orthElementaryGroup (quadTail 2 (quadPlus 1 F)))
    have hmemE : eichler (quadTail 2 (quadPlus 1 F)) u w₀ ∈
        orthElementaryGroup (quadTail 2 (quadPlus 1 F)) :=
      rootGroup_le_elementaryGroup _ _ (eichler_mem_rootGroup huw₀)
    refine ⟨B.map (orthElementaryGroupProdHom (r := 2) (quadPlus 1 F)), U, hB.map _, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective
        (orthElementaryGroupProdHom_injective (quadPlus 1 F)), hBcard]
      norm_num
    · intro hbot
      have hmem : (⟨eichler (quadTail 2 (quadPlus 1 F)) u w₀, hmemE⟩ :
          orthElementaryGroup (quadTail 2 (quadPlus 1 F))) ∈ U := by
        rw [Subgroup.mem_subgroupOf]
        exact eichler_mem_rootGroup huw₀
      rw [hbot] at hmem
      have hone : (⟨eichler (quadTail 2 (quadPlus 1 F)) u w₀, hmemE⟩ :
          orthElementaryGroup (quadTail 2 (quadPlus 1 F))) = 1 := by simpa using hmem
      exact hy₀_ne (congrArg Subtype.val hone)
    · have hroot : ∀ w : W ≃ₗ[F] W, w ∈ rootGroup (quadTail 2 (quadPlus 1 F)) u → w ^ 2 = 1 := by
        intro w hw
        obtain ⟨v, hv, hz⟩ := mem_rootGroup.mp hw
        rw [← hz, pow_two, eichler_mul hv hv, CharTwo.add_self_eq_zero, eichler_zero_right]
      intro z
      refine ⟨1, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [show (2 : ℕ) ^ 1 = 2 from rfl]
      exact hroot _ (Subgroup.mem_subgroupOf.mp z.2)
    · rw [Subgroup.le_normalizer_iff]
      intro x hx y hy
      rw [Subgroup.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      rw [mem_rootGroup] at hy ⊢
      obtain ⟨v, hv, hz⟩ := hy
      have hbiso : ((orthElementaryGroupProdHom (r := 2) (quadPlus 1 F) b :
            orthElementaryGroup (quadTail 2 (quadPlus 1 F))) : W ≃ₗ[F] W) ∈
          TauCeti.QuadraticMap.orthogonalGroup (quadTail 2 (quadPlus 1 F)) :=
        orthElementaryGroup_le (quadTail 2 (quadPlus 1 F)) (Subtype.mem _)
      have hgu : ((orthElementaryGroupProdHom (r := 2) (quadPlus 1 F) b :
            orthElementaryGroup (quadTail 2 (quadPlus 1 F))) : W ≃ₗ[F] W) u = u := by
        rw [orthElementaryGroupProdHom_apply]
        simp [u, hu]
      refine ⟨((orthElementaryGroupProdHom (r := 2) (quadPlus 1 F) b :
          orthElementaryGroup (quadTail 2 (quadPlus 1 F))) : W ≃ₗ[F] W) v, ?_, ?_⟩
      · rw [← hgu, polar_map_of_mem hbiso, hv]
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [show ((y : orthElementaryGroup (quadTail 2 (quadPlus 1 F))) : W ≃ₗ[F] W) =
          eichler (quadTail 2 (quadPlus 1 F)) u v from hz.symm]
        rw [eichler_conj hbiso u v, hgu]
  exact htail.of_isometryEquiv ((quadAddTailIsometry (F := F) 1).trans
    (QuadraticMap.IsometryEquiv.prodComm (quadPlus 1 F) (quadPlus 2 F)))

theorem quadPlusWitness (F : Type) [Field F] [Finite F] [CharP F 2] {m : ℕ} (hm : 2 ≤ m) :
    ∃ E U : Subgroup (CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup (quadPlus m F)),
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ (m - 1) ∧
        U ≠ ⊥ ∧ IsPGroup 2 U ∧
        E ≤ Subgroup.normalizer (U : Set (CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup (quadPlus m F))) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have key : ∀ n : ℕ, QuadWitness (F := F) (Fin (n + 2) ⊕ Fin (n + 2) → F)
      (quadPlus (n + 2) F) (n + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n with
      | 0 => simpa using exist_witness_quadPlus_two (F := F)
      | 1 => simpa using exist_witness_quadPlus_three (F := F)
      | (m + 2) =>
        exact quadWitness_add_two (F := F) (m := m + 2) (by omega) (ih m (by omega))
  exact key n

end WitnessProof

section ClauseD

theorem le_evenRank_of_quadPlusWitness {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .D) (hn : lab.n = 1) (hℓ : 4 ≤ lab.rank) :
    lab.rank - 1 ≤ evenRank K := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have htag3 : lab.rank ≠ 3 := by omega
  have ht : markTag lab = .POmegaPlus := by
    simp [CFSG.StandardType.markTag, htag, if_neg htag3]
  have hrk : markRank lab = lab.rank := by
    simp [CFSG.StandardType.markRank, htag, if_neg htag3]
  have hch : markChar lab = 2 := by simp [CFSG.StandardType.markChar, htag]
  have hdg : markDeg lab = lab.n := by simp [CFSG.StandardType.markDeg, htag]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hrk, hch, hdg] at hM'
  obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hcard2 : Nat.card F = 2 := by rw [hcard, hn]; norm_num
  have hcard' : Fintype.card F = 2 ^ 1 := by
    rw [← Nat.card_eq_fintype_card]; exact hcard2
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hv : ∃ v : Fin lab.rank ⊕ Fin lab.rank → F, quadPlus lab.rank F v ≠ 0 := by
    let i0 : Fin lab.rank := ⟨0, by omega⟩
    let v : Fin lab.rank ⊕ Fin lab.rank → F :=
      Pi.single (Sum.inl i0) (1 : F) + Pi.single (Sum.inr i0) (1 : F)
    refine ⟨v, ?_⟩
    rw [quadPlus_apply]
    have hv1 : v (Sum.inl i0) = 1 := by simp [v]
    have hv2 : v (Sum.inr i0) = 1 := by simp [v]
    have hterm : ∀ i : Fin lab.rank, v (Sum.inl i) * v (Sum.inr i) =
        if i = i0 then 1 else 0 := by
      intro i
      by_cases hi : i = i0
      · subst hi; rw [hv1, hv2, if_pos rfl, one_mul]
      · rw [if_neg hi]
        have h1 : v (Sum.inl i) = 0 := by
          simp [v, hi]
        rw [h1, zero_mul]
    simp only [hterm]
    rw [Finset.sum_ite_eq']
    simp
  have hbot : (StatedScalars (Fin lab.rank ⊕ Fin lab.rank) F).subgroupOf
      (StatedOmega (StatedQuadPlus lab.rank F)) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadPlus lab.rank F) (Q₀ := StatedQuadPlus lab.rank F) (coe_quadPlus lab.rank F) hv
  let φ₁ : StatedProj (StatedOmega (StatedQuadPlus lab.rank F)) ≃*
      StatedOmega (StatedQuadPlus lab.rank F) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot)
  let φ₂ : StatedOmega (StatedQuadPlus lab.rank F) ≃*
      orthElementaryGroup (quadPlus lab.rank F) :=
    CFSG.ClassicalGroups.Orthogonal.statedOmegaEquiv (coe_quadPlus lab.rank F)
      (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus (by omega))
  have hSC1 : StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaPlus lab.rank 2 1 :=
    ⟨by simpa [hn] using hadm, F, hfield, hfinite, by simpa [hn] using hcard, ⟨e⟩⟩
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) := by
    intro hdiv
    have hdvdZ : Nat.card (Subgroup.center K) ∣
        Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
      _root_.CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_hopf hQ
        (MulEquiv.refl _)
    rcases eq_or_lt_of_le hℓ with h4 | h5
    ·
      rw [← h4] at e
      have hQ' : CFSG.Open.IsQuasisimple K := ⟨hQ.1.commutator_eq_top, hQ.2.1⟩
      exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.noThreeCover_omegaPlus_four F
        K hQ' ⟨e⟩ hdiv
    ·
      have h4 : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) ∣ 4 :=
        card_griess_pomegaPlus_dvd_four hSC1 (Or.inr h5)
      have h34 : 3 ∣ 4 := hdiv.trans (hdvdZ.trans h4)
      omega
  obtain ⟨E, U, hE, hEcard, hU, hU2, hEN⟩ := quadPlusWitness (F := F) (m := lab.rank) (by omega)
  exact le_evenRank_of_center_quotient (e.trans (φ₁.trans φ₂)) Nat.prime_three (by norm_num) hZ
    hU hU2 hE hEcard hEN

theorem rk2_low_d_one {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .D) (hn : lab.n = 1) (hℓ : 4 ≤ lab.rank) :
    lab.rank - 1 ≤ evenRank K :=
  le_evenRank_of_quadPlusWitness hK htag hn hℓ

end ClauseD

end CFSG.LocalAnalysis.GLTheoremA
