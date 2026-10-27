module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighType
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterCartan
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.RankThree.Lattice

open Matrix


def twoDFourNegWord : List (Fin 4) := [0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 1, 3]

private def d4ReflectHom (i : Fin 4) : (Fin 4 → ℤ) →+ (Fin 4 → ℤ) where
  toFun x := coordReflect (CFSG.LieType.Universal.Spin.cartanD 4) i x
  map_zero' := by
    funext k
    simp [coordReflect]
  map_add' x y := by
    funext k
    simp only [coordReflect, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, mul_add, Pi.single_apply]
    split_ifs <;> ring

private def d4NegHom : (Fin 4 → ℤ) →+ (Fin 4 → ℤ) :=
  twoDFourNegWord.foldr (fun i g => (d4ReflectHom i).comp g) (AddMonoidHom.id _)

private theorem d4NegHom_apply_aux :
    ∀ (l : List (Fin 4)) (x : Fin 4 → ℤ),
      (l.foldr (fun i g => (d4ReflectHom i).comp g) (AddMonoidHom.id _)) x =
        l.foldr (fun i x => coordReflect (CFSG.LieType.Universal.Spin.cartanD 4) i x) x := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons i l ih =>
      intro x
      rw [List.foldr_cons, AddMonoidHom.comp_apply, ih x]
      rfl

private theorem d4NegHom_apply (x : Fin 4 → ℤ) :
    d4NegHom x = twoDFourNegWord.foldr
      (fun i x => coordReflect (CFSG.LieType.Universal.Spin.cartanD 4) i x) x :=
  d4NegHom_apply_aux twoDFourNegWord x

private theorem d4NegHom_single : ∀ j : Fin 4,
    d4NegHom (Pi.single j 1) = -Pi.single j 1 := by
  decide +kernel

private theorem d4NegCoord_eq_neg (x : Fin 4 → ℤ) :
    twoDFourNegWord.foldr
      (fun i x => coordReflect (CFSG.LieType.Universal.Spin.cartanD 4) i x) x = -x := by
  have hx : x = ∑ j, x j • (Pi.single j 1 : Fin 4 → ℤ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  have h1 : d4NegHom x = ∑ j, x j • (-(Pi.single j 1 : Fin 4 → ℤ)) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, d4NegHom_single]
  have h2 : twoDFourNegWord.foldr
      (fun i x => coordReflect (CFSG.LieType.Universal.Spin.cartanD 4) i x) x = d4NegHom x :=
    (d4NegHom_apply x).symm
  rw [h2, h1]
  simp only [smul_neg, Finset.sum_neg_distrib]
  rw [← hx]

theorem exists_neg_mem_of_cartanD {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (e : simpleRoots Ψ ≃ Fin 4)
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      CFSG.LieType.Universal.Spin.cartanD 4 (e β) (e γ)) :
    ∃ w ∈ componentWeylGroup Ψ, ∀ γ ∈ Ψ, w • γ = -γ := by
  classical
  refine ⟨(twoDFourNegWord.map (fun i => rootReflection (e.symm i : Fin τ.rank → ℤ))).prod, ?_, ?_⟩
  · clear he
    induction twoDFourNegWord with
    | nil => simpa using one_mem _
    | cons i l ih =>
        rw [List.map_cons, List.prod_cons]
        exact mul_mem (rootReflection_mem_componentWeylGroup (e.symm i).2) ih
  · intro γ hγ
    have hfold : ∀ (l : List (Fin 4)) (x : Fin 4 → ℤ),
        rootLift e (l.foldr
            (fun i x => coordReflect (CFSG.LieType.Universal.Spin.cartanD 4) i x) x) =
          (l.map (fun i => rootReflection (e.symm i : Fin τ.rank → ℤ))).prod •
            rootLift e x := by
      intro l
      induction l with
      | nil => intro x; simp
      | cons i l ih =>
          intro x
          rw [List.foldr_cons, List.map_cons, List.prod_cons, mul_smul,
            rootLift_coordReflect e he i, ih]
    rw [← image_rootLift_orbit hΨ e he] at hγ
    obtain ⟨x, -, rfl⟩ := hγ
    have hcoord := d4NegCoord_eq_neg x
    have h1 : rootLift e (-x) =
        (twoDFourNegWord.map (fun i => rootReflection (e.symm i : Fin τ.rank → ℤ))).prod •
          rootLift e x := by
      rw [← hcoord]
      exact hfold twoDFourNegWord x
    rw [← h1]
    rw [rootLift_eq_sum, rootLift_eq_sum]
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

theorem exists_neg_mem_of_twistKind_twoD_rank_four {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h4 : compRank (componentRoots (rootCharHom a) i) = 4) :
    ∃ w ∈ componentWeylGroup (componentRoots (rootCharHom a) i),
      ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ = -γ := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  obtain ⟨h4le, hcard⟩ := shape_of_twistKind_twoD hkind
  obtain ⟨-, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  have hiso := outer_isIsometry_rho S hs
  have hni := not_twistInner_of_twistKind_twoD_exc (Or.inl hkind)
  obtain ⟨r, -, e, he⟩ := exists_cartanD_of_nonInner hΨ
    ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ Ψ])
    hiso.bijOn hiso.iform_eq hiso.neg hni h4le hcard
  have hcardΔ : (simpleRoots Ψ).card = r := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hr4 : r = 4 := by
    have hcomp := compRank_eq_card hΨ
    omega
  subst hr4
  exact exists_neg_mem_of_cartanD hΨ e he

theorem twoDFourWord_spec {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (e : simpleRoots Ψ ≃ Fin 4)
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      CFSG.LieType.Universal.Spin.cartanD 4 (e β) (e γ)) :
    (twoDFourNegWord.map (fun i => rootReflection (e.symm i : Fin τ.rank → ℤ))).prod ∈
        componentWeylGroup Ψ ∧
      ∀ γ ∈ Ψ,
        ((twoDFourNegWord.map (fun i =>
          rootReflection (e.symm i : Fin τ.rank → ℤ))).prod) • γ = -γ := by
  classical
  constructor
  · clear he
    induction twoDFourNegWord with
    | nil => simpa using one_mem _
    | cons i l ih =>
        rw [List.map_cons, List.prod_cons]
        exact mul_mem (rootReflection_mem_componentWeylGroup (e.symm i).2) ih
  · intro γ hγ
    have hfold : ∀ (l : List (Fin 4)) (x : Fin 4 → ℤ),
        rootLift e (l.foldr
            (fun i x => coordReflect (CFSG.LieType.Universal.Spin.cartanD 4) i x) x) =
          (l.map (fun i => rootReflection (e.symm i : Fin τ.rank → ℤ))).prod •
            rootLift e x := by
      intro l
      induction l with
      | nil => intro x; simp
      | cons i l ih =>
          intro x
          rw [List.foldr_cons, List.map_cons, List.prod_cons, mul_smul,
            rootLift_coordReflect e he i, ih]
    rw [← image_rootLift_orbit hΨ e he] at hγ
    obtain ⟨x, -, rfl⟩ := hγ
    have hcoord := d4NegCoord_eq_neg x
    have h1 : rootLift e (-x) =
        (twoDFourNegWord.map (fun i =>
          rootReflection (e.symm i : Fin τ.rank → ℤ))).prod • rootLift e x := by
      rw [← hcoord]
      exact hfold twoDFourNegWord x
    rw [← h1]
    rw [rootLift_eq_sum, rootLift_eq_sum]
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

theorem exists_zsmul_eq_sum_of_basis {n : ℕ} (b : Fin n → (Fin n → ℤ))
    (hb : LinearIndependent ℚ (fun j => fun i => (b j i : ℚ))) :
    ∀ γ : Fin n → ℤ, ∃ (m : ℤ) (_ : m ≠ 0) (c : Fin n → ℤ), m • γ = ∑ j, c j • b j := by
  classical
  intro γ
  let B : Matrix (Fin n) (Fin n) ℤ := fun i j => b j i
  have hcol : LinearIndependent ℚ (B.map (Int.cast : ℤ → ℚ)).col := by
    change LinearIndependent ℚ (fun j => fun i => (b j i : ℚ))
    exact hb
  have hBq : (B.map (Int.cast : ℤ → ℚ)).det ≠ 0 :=
    Matrix.nonsingular_iff_det_ne_zero.1 (Matrix.linearIndependent_col_iff.1 hcol)
  have hdet : B.det ≠ 0 := by
    intro h0
    refine hBq ?_
    rw [← Int.cast_det (R := ℚ) B, h0]
    simp
  refine ⟨B.det, hdet, fun j => (B.adjugate *ᵥ γ) j, ?_⟩
  have hmul : B * B.adjugate = B.det • (1 : Matrix (Fin n) (Fin n) ℤ) := Matrix.mul_adjugate B
  have hmain : B *ᵥ (B.adjugate *ᵥ γ) = B.det • γ := by
    rw [Matrix.mulVec_mulVec, hmul, Matrix.smul_mulVec, Matrix.one_mulVec]
  funext i
  have hi := congrFun hmain i
  have hi' : ∑ j, b j i * (B.adjugate *ᵥ γ) j = B.det * γ i := by
    simpa [B, Matrix.mulVec, dotProduct, Finset.sum_apply, smul_eq_mul] using hi
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hi']
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem smul_eq_neg_of_basis {τ : Tag} {w : WeylGroup τ}
    (b : Fin τ.rank → (Fin τ.rank → ℤ))
    (hbasis : LinearIndependent ℚ (fun j => fun i => (b j i : ℚ)))
    (hneg : ∀ j, w • b j = -b j) :
    ∀ γ : Fin τ.rank → ℤ, w • γ = -γ := by
  intro γ
  obtain ⟨m, hm, c, hc⟩ := exists_zsmul_eq_sum_of_basis b hbasis γ
  have h2 : w • (m • γ) = -(m • γ) := by
    rw [hc, Finset.smul_sum]
    simp only [smul_comm w, hneg, smul_neg]
    rw [← Finset.sum_neg_distrib]
  have h5 : m • (w • γ) = m • (-γ) := by
    rw [← smul_comm w m γ, h2, smul_neg]
  have h6 : m • (w • γ - -γ) = 0 := by
    rw [smul_sub, h5, sub_self]
  have h7 : w • γ - -γ = 0 := (smul_eq_zero.1 h6).resolve_left hm
  have h8 : w • γ + γ = 0 := by simpa using h7
  exact eq_neg_iff_add_eq_zero.2 h8

theorem smul_eq_neg_of_basis' {τ : Tag} {ι : Type} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = τ.rank) {w : WeylGroup τ}
    (b : ι → (Fin τ.rank → ℤ))
    (hbasis : LinearIndependent ℚ (fun j => fun i => (b j i : ℚ)))
    (hneg : ∀ j, w • b j = -b j) :
    ∀ γ : Fin τ.rank → ℤ, w • γ = -γ := by
  classical
  let e : ι ≃ Fin τ.rank := Fintype.equivFinOfCardEq hcard
  have hb' : LinearIndependent ℚ (fun i : Fin τ.rank =>
      fun k => (b (e.symm i) k : ℚ)) := by
    have h := hbasis.comp e.symm e.symm.injective
    exact h
  intro γ
  exact smul_eq_neg_of_basis (fun i => b (e.symm i)) hb' (fun i => hneg (e.symm i)) γ

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
