module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthFCCases
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaPlus
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Neg
public import CFSG.HardMathSupport.Dickson.Bal207.OrthShapeIdx

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFC

open Polynomial Module QuadraticMap CFSG.Open CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.HardMathSupport.Dickson.Bal207.Uni
  CFSG.HardMathSupport.Dickson.I271 CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8 CFSG.ComponentClassification.CatFC Matrix

theorem not_two_pow_dvd_ordD_four_two : ¬ 2 ^ 15 ∣ ordD 4 (2 ^ 1) := by
  unfold ordD
  decide

theorem false_of_d4_two {Y : Type} [Group Y] {K J : Subgroup Y}
    (hM : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .POmegaPlus 4 2 1) (hJK : J ≤ K)
    (hJFC : IsLieQuot ↥J IsSpFirstClaimIdx) : False := by
  obtain ⟨dd, hdd, ⟨eJ⟩⟩ := hJFC
  have h15 := FirstClaim.two_pow_dvd_card_of_isSpFirstClaimIdx dd hdd
  rw [← Nat.card_congr eJ.toEquiv] at h15
  have h1 := FirstClaim.card_centerQuot_dvd_card_image
    (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) hJK
  have h2 : Nat.card ((J.comap K.subtype).map (uniMap (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)))) ∣
      Nat.card (↥K ⧸ Subgroup.center ↥K) := Subgroup.card_subgroup_dvd_card _
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hM).2.2.2.1 rfl] at h2
  exact not_two_pow_dvd_ordD_four_two (h15.trans (h1.trans h2))

theorem orthFC_inner_model (hC : OrthInnerCases) (hD : OrthBlockFrame)
    {G : ∀ (S : Type) [Group S], MulAut S → Prop} {Y : Type} [Group Y] [Finite Y]
    {K B A : Subgroup Y} (ctx : Bal207PlusCtx G 3 K B A) (hIH : Bal207PlusIH G A)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K)))
    {t : StatedLieTag} {n f : ℕ} (hf : f = 1 ∨ f = 3) (hn : 5 ≤ n)
    (hP : (t = .POmegaPlus ∧ Even n) ∨ (t = .POmegaMinus ∧ Odd n))
    (hM : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) t n 2 f)
    {a : Y} (haA : a ∈ A) (ha1 : a ≠ 1) {s : ↥K ⧸ Subgroup.center ↥K}
    (hs : actHom K ⟨a, ctx.norm (ctx.le haA)⟩ = MulAut.conj s)
    {J : Subgroup Y} (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set Y)) J)
    (hcomp : CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({a} : Set Y)))
    (hBJ : B ≤ Subgroup.normalizer (J : Set Y)) (hJFC : IsLieQuot ↥J IsSpFirstClaimIdx) :
    IsStronglyLocallyOneBalanced 3 B a J := by
  rcases hP with ⟨rfl, hev⟩ | ⟨rfl, hodd⟩
  · have hlayS : ∀ s : ↥K ⧸ Subgroup.center ↥K, s ^ 3 = 1 → PerfectInLayer (MulAut.conj s) :=
      fun s hs3 => LieSemisimple.perfectInLayer_conj_omega (Or.inr (Or.inl rfl)) hM
        Nat.prime_three (by norm_num) (by norm_num) s hs3
    obtain ⟨-, F, _, _, hFc, ⟨e₀⟩⟩ := id hM
    haveI : Fintype F := Fintype.ofFinite F
    haveI : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hFc])
    obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus hM F hFc e₀
    have htop := matrixProjectiveImage_eq_top_plus F n hn
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus
      (Or.inr (Or.inl rfl)) n 2 f hM F hFc e₀
    have hF : Nat.card F = 2 ∨ Nat.card F = 8 := by
      rcases hf with rfl | rfl
      · exact Or.inl (by rw [hFc]; norm_num)
      · exact Or.inr (by rw [hFc]; norm_num)
    exact orthFC_inner hC hD ctx hIH hZ hF (d := 2 * n) (by omega) hnd hT rfl (by omega)
      (iff_of_true (omegaPlus_isPlusType n F) hev)
      (fun g hg => (hgates.1 g).1 hg) htop
      ((coordinatePlusWitnessEquiv F e₀).trans (coordBridge _ (by omega))) hlayS haA ha1 hs hJ
      hcomp hBJ hJFC
  · have hlayS : ∀ s : ↥K ⧸ Subgroup.center ↥K, s ^ 3 = 1 → PerfectInLayer (MulAut.conj s) :=
      fun s hs3 => LieSemisimple.perfectInLayer_conj_omega (Or.inr (Or.inr rfl)) hM
        Nat.prime_three (by norm_num) (by norm_num) s hs3
    have hn1 : 1 ≤ n := by omega
    obtain ⟨-, F, _, _, hFc, b, c, hirr, ⟨e₀⟩⟩ := id hM
    haveI : Fintype F := Fintype.ofFinite F
    haveI : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hFc])
    obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus hM F hFc b c hirr e₀
    have htop := matrixProjectiveImage_eq_top_minus F n (by omega) b c hirr
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n 2 f hM hn1 F hFc b c hirr e₀
    have hF : Nat.card F = 2 ∨ Nat.card F = 8 := by
      rcases hf with rfl | rfl
      · exact Or.inl (by rw [hFc]; norm_num)
      · exact Or.inr (by rw [hFc]; norm_num)
    exact orthFC_inner hC hD ctx hIH hZ hF (d := 2 * n) (by omega) hnd hT rfl (by omega)
      (iff_of_false (not_isPlusType_coordinateQuadMinus (K := F) n hn1 hirr)
        (Nat.not_even_iff_odd.mpr hodd))
      (fun g hg => (hgates.1 g).1 hg) htop
      ((coordinateMinusWitnessEquiv F hn1 b c e₀).trans (coordBridge _ (by omega))) hlayS haA ha1
      hs hJ hcomp hBJ hJFC

theorem bal207OrthFirstClaim_of_cases (hGA : GriessAllModelsStatement) (hC : OrthInnerCases)
    (hD : OrthBlockFrame) (hField : OrthFieldComps) (hTwo : OrthTwoInner)
    (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Bal207OrthFirstClaim G := by
  intro Y _ _ _ K B A ctx hK hIH a haA ha1 J hJ hcomp hBJ hJFC
  have hKq : CFSG.Open.IsQuasisimple ↥K := ctx.comp.2.2
  have hZ := famOrth_coprime_center hGA hKq hK
  have haB : a ∈ B := ctx.le haA
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  obtain ⟨t, n, f, hf, hshape, hM⟩ := exists_model_of_famOrth hK
  by_cases hn5 : 5 ≤ n
  · have ht : t = .POmegaPlus ∨ t = .POmegaMinus := by
      rcases hshape with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    have hP : (t = .POmegaPlus ∧ Even n) ∨ (t = .POmegaMinus ∧ Odd n) := by
      rcases hshape with ⟨h, he, -⟩ | ⟨h, ho, -⟩
      · exact Or.inl ⟨h, he⟩
      · exact Or.inr ⟨h, ho⟩
    by_cases hinner : ∃ s : ↥K ⧸ Subgroup.center ↥K,
        actHom K ⟨a, ctx.norm haB⟩ = MulAut.conj s
    · obtain ⟨s, hs⟩ := hinner
      exact orthFC_inner_model hC hD ctx hIH hZ hf hn5 hP hM haA ha1 hs hJ hcomp hBJ hJFC
    · push Not at hinner
      rcases hf with rfl | rfl
      · exfalso
        have hβ3 := uniAut_pow_three ctx.scp ctx.norm (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) haB
        obtain ⟨s, hs⟩ := hTwo (↥K ⧸ Subgroup.center ↥K) t n ht hn5 hM
          (actHom K ⟨a, ctx.norm haB⟩) (by rw [← uniAut_refl]; exact hβ3)
        exact hinner s hs.symm
      · exact orthFC_outer hField ctx hIH hZ (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) ht hn5 hP
          hM haA (fun s h => hinner s (h.trans (uniAut_refl _)).symm) hJ hcomp hBJ ha1
  · exfalso
    rcases hshape with ⟨rfl, -, h6 | ⟨rfl, rfl⟩⟩ | ⟨-, -, h5⟩
    · omega
    · exact false_of_d4_two hM hJK hJFC
    · exact hn5 h5

end CFSG.HardMathSupport.Dickson.Bal207.OrthFC

end
