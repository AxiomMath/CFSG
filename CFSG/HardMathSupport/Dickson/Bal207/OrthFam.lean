module

public import CFSG.HardMathSupport.Dickson.Bal207.CompShapeOn
public import CFSG.HardMathSupport.Dickson.Bal207.OrthShapeIdx
public import CFSG.HardMathSupport.Dickson.Bal207.Glue
public import CFSG.HardMathSupport.Dickson.Bal207.D4Semilin
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthD4
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import all CFSG.HardMathSupport.Dickson.Bal207.CompShapeW
import CFSG.HardMathSupport.Dickson.Bal207.FamD4Eight
import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerField
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaPlus
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Neg
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessTransport

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFix

open Module QuadraticMap CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Dickson.I271
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalAut
open CFSG.GroupTheory.WeirSylow (IsPlusType)
open CFSG.RankThree.Classical.SteinbergBY
  (orthogonal_large_prime_semilinear_field_and_diagonal_gates)
open CFSG.ComponentClassification.CatFC (omegaPlus_isPlusType)
open CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8 (not_isPlusType_coordinateQuadMinus)

@[expose] def OrthInnerShapeInput : Prop :=
  ∀ {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ} {Q : QuadraticForm F (Fin d → F)},
    (Nat.card F = 2 ∨ Nat.card F = 8) → ∀ hd : 0 < d, (polarBilin Q).Nondegenerate →
    (∃ U : Submodule F (Fin d → F), finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0) →
    ∀ {n : ℕ}, d = 2 * n → 4 ≤ n → (IsPlusType Q ↔ Even n) →
    ∀ {t : ProjOrthDerived Q}, orderOf t = 3 →
      CompShapeOn 3 OrthCompType
        ((matrixProjectiveImage Q).comap (MulAut.congr (coordBridge Q hd).symm).toMonoidHom)
        (MulAut.conj t)

@[expose] def OrthInnerUniqueTwo : Prop :=
  ∀ {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ} {Q : QuadraticForm F (Fin d → F)},
    Nat.card F = 2 → (polarBilin Q).Nondegenerate →
    (∃ U : Submodule F (Fin d → F), finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0) →
    ∀ {n : ℕ}, d = 2 * n → n = 4 → (IsPlusType Q ↔ Even n) →
    ∀ {t : ProjOrthDerived Q}, orderOf t = 3 → ∀ {L L' : Subgroup (ProjOrthDerived Q)},
      IsComponentOf L (Solomon.Coordinator.fixSubgroup (MulAut.conj t)) →
      IsComponentOf L' (Solomon.Coordinator.fixSubgroup (MulAut.conj t)) → L = L'

@[expose] def OrthD4EightComp : Prop :=
  ∀ (G : ∀ (S : Type) [Group S], MulAut S → Prop) (X : Type) [Group X] [Finite X]
    (K B A : Subgroup X), Bal207PlusCtx G 3 K B A → IsLieQuot ↥K (FamOrth 3) →
      Nat.Coprime 3 (Nat.card (Subgroup.center ↥K)) →
      ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
        GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) → IsLieQuot ↥J IsD4EightIdx →
          NoTrialityOn NonSemilinD4Eight (B.subgroupOf (Subgroup.centralizer ({a} : Set X)))
            (J.subgroupOf (Subgroup.centralizer ({a} : Set X)))

theorem mulAut_congr_conj {S S' : Type*} [Group S] [Group S'] (e : S ≃* S') (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem compShape_of_unique {T : ∀ (Q : Type) [Group Q], Prop} {S : Type} [Group S]
    {β : MulAut S} (hl : PerfectInLayer β)
    (hT : ∀ L : Subgroup S, IsComponentOf L (Solomon.Coordinator.fixSubgroup β) →
      T (↥L ⧸ Subgroup.center ↥L))
    (hu : ∀ L L' : Subgroup S, IsComponentOf L (Solomon.Coordinator.fixSubgroup β) →
      IsComponentOf L' (Solomon.Coordinator.fixSubgroup β) → L = L') : CompShape T β :=
  ⟨hl, hT, fun _ hω L hL => hu _ _ (isComponentOf_map_of_commute_w hω hL) hL⟩

theorem exists_coords_of_model {S : Type} [Group S] {t : StatedLieTag} {n f : ℕ}
    (hcase : (t = .POmegaPlus ∧ Even n ∧ (6 ≤ n ∨ (n = 4 ∧ f = 1))) ∨
      (t = .POmegaMinus ∧ Odd n ∧ 5 ≤ n))
    (hM : StatedClassicalModel S t n 2 f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (Q : QuadraticForm F (Fin (2 * n) → F)) (_ : S ≃* ProjOrthDerived Q),
      Nat.card F = 2 ^ f ∧ (polarBilin Q).Nondegenerate ∧
      (∃ U : Submodule F (Fin (2 * n) → F), finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
      (IsPlusType Q ↔ Even n) ∧ (5 ≤ n → matrixProjectiveImage Q = ⊤) ∧
      ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
        g.val.right = 1 ∧
          ∃ a : Fˣ, g.val.left = Matrix.GeneralLinearGroup.scalar (Fin (2 * n)) a := by
  have hd : 0 < 2 * n := by rcases hcase with ⟨-, -, h | ⟨h, -⟩⟩ | ⟨-, -, h⟩ <;> omega
  have hchar : ∀ {F : Type} [Field F] [Finite F], Nat.card F = 2 ^ f → CharP F 2 := by
    intro F _ _ hF
    haveI := Fintype.ofFinite F
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hF])
  rcases hcase with ⟨rfl, hev, h6⟩ | ⟨rfl, hodd, h5⟩
  · obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hM.2
    haveI := hchar hF
    have hreg := regular_coordinateQuadPlus n F (by rcases h6 with h | ⟨h, -⟩ <;> omega)
    refine ⟨F, inferInstance, inferInstance, inferInstance, coordinateQuadPlus n F,
      (coordinatePlusWitnessEquiv F e₀).trans (coordBridge (coordinateQuadPlus n F) hd), hF,
      hreg.1, hreg.2, iff_of_true (omegaPlus_isPlusType n F) hev,
      fun h5 => matrixProjectiveImage_eq_top_plus F n h5, fun g => ?_⟩
    exact ((orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus
      (Or.inr (Or.inl rfl)) n 2 f hM F hF e₀).1 g).mp
  · have hn1 : 1 ≤ n := by omega
    obtain ⟨F, _, _, hF, b, c, hirr, ⟨e₀⟩⟩ := hM.2
    haveI := hchar hF
    have hreg := regular_coordinateQuadMinus n F b c (by omega : 4 ≤ n) hirr
    refine ⟨F, inferInstance, inferInstance, inferInstance, coordinateQuadMinus n F hn1 b c,
      (coordinateMinusWitnessEquiv F hn1 b c e₀).trans (coordBridge _ hd), hF, hreg.1, hreg.2,
      iff_of_false (not_isPlusType_coordinateQuadMinus n hn1 hirr) (Nat.not_even_iff_odd.mpr hodd),
      fun _ => matrixProjectiveImage_eq_top_minus F n (by omega) b c hirr, fun g => ?_⟩
    exact ((orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n 2 f hM hn1 F hF b c hirr e₀).1 g).mp

section Shape


theorem compShapeOn_top_of_model (hInner : OrthInnerShapeInput) (hU2 : OrthInnerUniqueTwo)
    (hTri : D42TrialityShape) {S : Type} [Group S] [Finite S] {t : StatedLieTag} {n f : ℕ}
    (hf : f = 1 ∨ f = 3)
    (hcase : (t = .POmegaPlus ∧ Even n ∧ (6 ≤ n ∨ (n = 4 ∧ f = 1))) ∨
      (t = .POmegaMinus ∧ Odd n ∧ 5 ≤ n))
    (hM : StatedClassicalModel S t n 2 f) {β : MulAut S} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    CompShapeOn 3 OrthCompType ⊤ β := by
  by_cases hin : ∃ s : S, MulAut.conj s = β
  · obtain ⟨s, rfl⟩ := hin
    obtain ⟨F, _, _, _, Q, e, hF, hQ, hT, hV, htop, -⟩ := exists_coords_of_model hcase hM
    have hd : 0 < 2 * n := by rcases hcase with ⟨-, -, h | ⟨h, -⟩⟩ | ⟨-, -, h⟩ <;> omega
    have hn4 : 4 ≤ n := by rcases hcase with ⟨-, -, h | ⟨h, -⟩⟩ | ⟨-, -, h⟩ <;> omega
    have hF' : Nat.card F = 2 ∨ Nat.card F = 8 := by
      rcases hf with rfl | rfl
      · exact Or.inl (by rw [hF]; norm_num)
      · exact Or.inr (by rw [hF]; norm_num)
    have hes : MulAut.conj (e s) = MulAut.congr e (MulAut.conj s) := (mulAut_congr_conj e s).symm
    have h1 : MulAut.conj (e s) ≠ 1 := by
      rw [hes]
      intro h
      apply hβ1
      apply (MulAut.congr e).injective
      rw [h, map_one]
    have ht3 : orderOf (e s) = 3 :=
      orderOf_eq_three_of_conj (CFSG.RankThree.PartOne.KCOrthogonalD4.center_projOrthDerived_eq_bot
        Q hQ hT) h1 (by rw [hes, ← map_pow, hβ3, map_one])
    have hsh := hInner hF' hd hQ hT rfl hn4 hV ht3
    rw [hes] at hsh
    by_cases h5 : 5 ≤ n
    · rw [htop h5, Subgroup.comap_top] at hsh
      have h := CompShapeOn.of_congr isoInvariant_orthCompType e hsh
      rwa [Subgroup.comap_top] at h
    · have h41 : n = 4 ∧ f = 1 := by
        rcases hcase with ⟨-, -, h | h⟩ | ⟨-, -, h⟩
        · omega
        · exact h
        · omega
      have hF2 : Nat.card F = 2 := by rw [hF, h41.2]; norm_num
      have hc : CompShape OrthCompType (MulAut.congr e (MulAut.conj s)) :=
        compShape_of_unique hsh.layer hsh.type fun L L' hL hL' => by
          rw [← hes] at hL hL'
          exact hU2 hF2 hQ hT rfl h41.1 hV ht3 hL hL'
      have h := CompShapeOn.of_congr isoInvariant_orthCompType e (hc.compShapeOn 3 ⊤)
      rwa [Subgroup.comap_top] at h
  · push Not at hin
    rcases hcase with ⟨rfl, hev, h6 | ⟨rfl, rfl⟩⟩ | ⟨rfl, hodd, h5⟩
    · rcases hf with rfl | rfl
      · obtain ⟨s, hs⟩ := orthTwo_inner (Or.inl rfl) (by omega) hM hβ3
        exact absurd hs (hin s)
      · obtain ⟨hl, J, hJ, hZJ, hMJ⟩ := orthField_comps (Or.inl rfl) (by omega) hM hβ3 hin
        refine (compShape_of_unique hl (fun L hL => ?_) fun L L' hL hL' =>
          (hJ L hL).trans (hJ L' hL').symm).compShapeOn 3 ⊤
        obtain rfl := hJ L hL
        exact isoInvariant_orthCompType _ _
          ((QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot).symm
          (orthCompType_of_model_plus hMJ (Or.inl rfl) hev)
    · obtain ⟨hu, hty⟩ := hTri S hM β hβ3 hin
      exact (compShape_of_unique
        (LieSemisimple.perfectInLayer_omega_D4_three hM (by norm_num) β hβ3)
        (fun L hL => orthCompType_of_u33 (hty L hL)) hu).compShapeOn 3 ⊤
    · rcases hf with rfl | rfl
      · obtain ⟨s, hs⟩ := orthTwo_inner (Or.inr rfl) h5 hM hβ3
        exact absurd hs (hin s)
      · obtain ⟨hl, J, hJ, hZJ, hMJ⟩ := orthField_comps (Or.inr rfl) h5 hM hβ3 hin
        refine (compShape_of_unique hl (fun L hL => ?_) fun L L' hL hL' =>
          (hJ L hL).trans (hJ L' hL').symm).compShapeOn 3 ⊤
        obtain rfl := hJ L hL
        exact isoInvariant_orthCompType _ _
          ((QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot).symm
          (orthCompType_of_model_minus hMJ (Or.inl rfl) hodd h5)

theorem bal207PlusFamOrth_of_inputs (hGA : GriessAllModelsStatement)
    (hInner : OrthInnerShapeInput) (hU2 : OrthInnerUniqueTwo) (hTri : D42TrialityShape)
    (hD8 : OrthD4EightComp) (hFC : Bal207OrthFirstClaim NonSemilinD4Eight) :
    Bal207PlusFamOrth NonSemilinD4Eight := by
  intro X _ _ hKG p K B A ctx hK hIH
  have hp3 : p = 3 := by
    obtain ⟨⟨d, hv⟩, ⟨hi, ho⟩, -⟩ := hK
    cases d with
    | D r q => exact hi.1
    | twistedD r q => exact hi.1
    | _ => exact ho.elim
  subst hp3
  have hZ := famOrth_coprime_center hGA ctx.comp.2.2 hK
  obtain ⟨t, n, f, hf, hcase, hM⟩ := exists_model_of_famOrth hK
  have hB : ∀ b ∈ B, b ^ 3 = 1 := fun b hb => ctx.scp.2.1.2 b hb
  refine bal207PlusFamClauses_of_compShapeOn_b2 ctx isoInvariant_orthCompType le_top
    (fun β hβ hβ1 => ?_) ?_ ?_
  · have hβ3 : β ^ 3 = 1 := by
      obtain ⟨b, hbN, hbB, rfl⟩ := mem_autImage.1 hβ
      have hb3 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hB b hbB)
      rw [← map_pow, hb3, map_one]
    exact compShapeOn_top_of_model hInner hU2 hTri hf hcase hM hβ3 hβ1
  · exact fun h => (by norm_num : (3 : ℕ) ≠ 1) (Nat.Coprime.eq_one_of_dvd hZ h)
  · intro a haA ha1 J hJ hcomp hTJ hsmall hBJ
    obtain ⟨d, hd, hJd⟩ := hTJ
    rcases orthCompIdx_cases hd with hi | hi | hi | hi | hi
    · exact Glue.stronglyLocallyOneBalanced_of_ih ctx hIH haA ha1 hJ hcomp.2.2 hBJ
        (Glue.bal207PlusHyp_of_isLieQuot
          (Glue.isLieQuot_subgroupOf (hJ.1.trans inf_le_right) ⟨d, hi, hJd⟩))
    · exact Glue.stronglyLocallyOneBalanced_of_ih ctx hIH haA ha1 hJ hcomp.2.2 hBJ
        (Glue.bal207PlusHyp_of_d4Eight
          (Glue.isLieQuot_subgroupOf (hJ.1.trans inf_le_right) ⟨d, hi, hJd⟩)
          (hD8 _ X K B A ctx hK hZ a haA ha1 J hJ hBJ ⟨d, hi, hJd⟩))
    · exact absurd (Or.inr (Or.inl ⟨d, hi, hJd⟩)) hsmall
    · exact absurd (Or.inr (Or.inr ⟨d, hi, hJd⟩)) hsmall
    · exact hFC X hKG K B A ctx hK hIH a haA ha1 J hJ hcomp hBJ ⟨d, hi, hJd⟩

end Shape

end CFSG.HardMathSupport.Dickson.Bal207.OrthFix

end
