module

public import CFSG.HardMathSupport.Dickson.Bal207.SU38Frame
public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Image
import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerField
import CFSG.HardMathSupport.Dickson.Bal207.OrthShapeIdx
import CFSG.HardMathSupport.Dickson.Bal207.SpFCCases
import CFSG.HardMathSupport.Dickson.Bal207.UniOrder
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.LargeExtraspecial.A2ModOrd
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFix

open Polynomial QuadraticMap CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Dickson.Bal207.Uni
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical.SteinbergBY
  (orthogonal_large_prime_semilinear_field_and_diagonal_gates)

@[expose] def OrthSU38ToralInput : Prop :=
  ∀ {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ} {Q : QuadraticForm F (Fin d → F)}
    {G : Type} [Group G] {K B J : Subgroup G} [Finite G], IsSCp 3 ⊤ B →
    ∀ hBK : B ≤ Subgroup.normalizer (K : Set G), Nat.Coprime 3 (Nat.card (Subgroup.center ↥K)) →
    Nat.card F = 8 → ∀ hd : 0 < d, (polarBilin Q).Nondegenerate →
    (∃ U : Submodule F (Fin d → F), Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0) →
    (∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Fˣ, g.val.left = Matrix.GeneralLinearGroup.scalar (Fin d) a) →
    ∀ e : (↥K ⧸ Subgroup.center ↥K) ≃* ProjOrthDerived Q,
    (∀ b : ↥B, MulAut.congr (coordBridge Q hd).symm (uniAut e ⟨b, hBK b.2⟩) ∈
      matrixProjectiveImage Q) →
    CFSG.Open.IsQuasisimple ↥J → J ≤ K → B ≤ Subgroup.normalizer (J : Set G) →
    ∀ x : orthDerived Q, orderOf x = 3 →
    (X ^ 2 + X + 1 : F[X]) ∈ primaryFactors (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap →
    primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap (X ^ 2 + X + 1) = 3 →
    (J.comap K.subtype).map (uniMap e) =
      componentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1) →
    (∀ b : ↥B, uniAut e ⟨b, hBK b.2⟩ (piOrth Q x) = piOrth Q x) → SU38Toral B J

@[expose] def OrthUniAutFixInput : Prop :=
  ∀ {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ} {Q : QuadraticForm F (Fin d → F)}
    {G : Type} [Group G] {K B : Subgroup G}, IsSCp 3 ⊤ B →
    ∀ hBK : B ≤ Subgroup.normalizer (K : Set G), 0 < d → (polarBilin Q).Nondegenerate →
    (∃ U : Submodule F (Fin d → F), Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0) →
    ∀ (e : (↥K ⧸ Subgroup.center ↥K) ≃* ProjOrthDerived Q) {a : G} (haB : a ∈ B)
      {t : ProjOrthDerived Q}, uniAut e ⟨a, hBK haB⟩ = MulAut.conj t →
      ∀ b : ↥B, uniAut e ⟨b, hBK b.2⟩ t = t

theorem two_pow_dvd_card_of_orthTwo {S : Type} [Group S] {t : StatedLieTag} {n : ℕ}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (hn : 1 ≤ n)
    (hS : StatedClassicalModel S t n 2 1) : 2 ^ (n * (n - 1)) ∣ Nat.card S := by
  rcases ht with rfl | rfl
  · rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hS).2.2.2.1 rfl, pow_one,
      CFSG.LargeExtraspecial.A2Mod.Ord.ordD_two_eq hn, mul_assoc]
    exact dvd_mul_right _ _
  · rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hS).2.2.2.2 rfl, pow_one,
      CFSG.LargeExtraspecial.A2Mod.Ord.ordTwistedD_two_eq hn, mul_assoc]
    exact dvd_mul_right _ _

theorem su38Toral_of_projOrth (hTor : OrthSU38ToralInput) (hFix : OrthUniAutFixInput)
    {G : ∀ (S : Type) [Group S], MulAut S → Prop} {Y : Type} [Group Y] [Finite Y]
    {K B A : Subgroup Y} (ctx : Bal207PlusCtx G 3 K B A)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K))) {F : Type} [Field F] [Finite F]
    [CharP F 2] {d : ℕ} {Q : QuadraticForm F (Fin d → F)} (hF : Nat.card F = 2 ∨ Nat.card F = 8)
    (hd : 0 < d) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule F (Fin d → F), Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hker : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Fˣ, g.val.left = Matrix.GeneralLinearGroup.scalar (Fin d) a)
    (htop : matrixProjectiveImage Q = ⊤) {t : StatedLieTag} {n f : ℕ}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (hn : 5 ≤ n) (hf : f = 1 ∨ f = 3)
    (hM : StatedClassicalModel (ProjOrthDerived Q) t n 2 f)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ProjOrthDerived Q) {a : Y} (haA : a ∈ A) (ha1 : a ≠ 1)
    {J : Subgroup Y} (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set Y)) J)
    (hJU : IsSU38Comp J) (hBJ : B ≤ Subgroup.normalizer (J : Set Y)) : SU38Toral B J := by
  have haB : a ∈ B := ctx.le haA
  have hBK : B ≤ Subgroup.normalizer (K : Set Y) := ctx.norm
  have hKq : CFSG.Open.IsQuasisimple ↥K := ctx.comp.2.2
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hβ3 : uniAut e ⟨a, hBK haB⟩ ^ 3 = 1 := by
    have h3 : (⟨a, hBK haB⟩ : ↥(Subgroup.normalizer (K : Set Y))) ^ 3 = 1 :=
      Subtype.ext (ctx.scp.2.1.2 a haB)
    rw [← map_pow, h3, map_one]
  have hβ1 : uniAut e ⟨a, hBK haB⟩ ≠ 1 := fun h1 =>
    not_mem_centralizer_of_inf_eq_bot ctx.disj haA ha1
      (mem_centralizer_of_uniAut_eq_one e hKq.1 (hBK haB) h1)
  by_cases hin : ∃ s : ProjOrthDerived Q, MulAut.conj s = uniAut e ⟨a, hBK haB⟩
  · obtain ⟨s, hs⟩ := hin
    have hZT := CFSG.RankThree.PartOne.KCOrthogonalD4.center_projOrthDerived_eq_bot Q hQ hT
    have hs3 : s ^ 3 = 1 := by
      have h1 : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, hs, hβ3]
      have hc : s ^ 3 ∈ Subgroup.center (ProjOrthDerived Q) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h2 := congrArg (fun φ : MulAut (ProjOrthDerived Q) => φ g) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h2
        calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [h2]
          _ = s ^ 3 * g := by group
      rw [hZT, Subgroup.mem_bot] at hc
      exact hc
    have hs1 : s ≠ 1 := fun h => hβ1 (by rw [← hs, h, map_one])
    have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
    haveI : Nontrivial (Fin d → F) := by
      obtain ⟨U, hU3, -⟩ := hT
      exact Module.nontrivial_of_finrank_pos (R := F)
        (lt_of_lt_of_le (by norm_num : 0 < 3) (hU3 ▸ Submodule.finrank_le U))
    obtain ⟨x, hxs, hx3⟩ := exists_lift_orderOf_three hQ hso
    have hax : uniAut e ⟨a, hBK haB⟩ = MulAut.conj (piOrth Q x) := by rw [hxs, hs]
    have hlay : PerfectInLayer (MulAut.conj (piOrth Q x)) :=
      LieSemisimple.perfectInLayer_conj_omega (Or.inr ht) hM Nat.prime_three (by norm_num)
        (by norm_num) _ (by rw [hxs, hs3])
    obtain ⟨hcomp, h8, hΦ, hm, hJx⟩ :=
      su38_image_eq_componentImage hF hQ hKq hZ e (hBK haB) x hx3 hax hlay hJ hJU
    exact hTor ctx.scp hBK hZ h8 hd hQ hT hker e
      (fun b => by rw [htop]; exact Subgroup.mem_top _) hcomp.2.2 hJK hBJ x hx3 hΦ hm hJx
      (hFix ctx.scp hBK hd hQ hT e haB hax)
  · push Not at hin
    exfalso
    rcases hf with rfl | rfl
    · obtain ⟨s, hs⟩ := orthTwo_inner ht hn hM hβ3
      exact hin s hs
    · obtain ⟨hl, J₀, hJ₀, hZ₀, hM₀⟩ := orthField_comps ht hn hM hβ3 hin
      obtain ⟨hcomp, hJc, -⟩ := uni_component e Nat.prime_three hKq hZ (hBK haB) hl hJ
      have hψ := hJ₀ _ hJc
      obtain ⟨eq⟩ := FirstClaim.nonempty_centerQuot_of_image e hJK hcomp.2.2.1
        (MulEquiv.subgroupCongr hψ)
      have hc : Nat.card ↥J₀ = 5515776 := by
        rw [← uni_card_su38 hJU, Nat.card_congr eq.toEquiv,
          Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ₀).trans
            QuotientGroup.quotientBot).toEquiv]
      have h20 : 2 ^ 20 ∣ Nat.card ↥J₀ :=
        (pow_dvd_pow 2 (le_trans (by norm_num) (Nat.mul_le_mul hn (by omega : 4 ≤ n - 1)))).trans
          (two_pow_dvd_card_of_orthTwo ht (by omega) hM₀)
      rw [hc] at h20
      norm_num at h20

theorem su38FrameOrth_of_torus (hTor : OrthSU38ToralInput) (hFix : OrthUniAutFixInput)
    (hGA : GriessAllModelsStatement) (G : ∀ (S : Type) [Group S], MulAut S → Prop) :
    SU38FrameOrth G := by
  intro Y _ _ _ K B A ctx hK _ a haA ha1 J hJ hJU hBJ
  obtain ⟨t, n, f, hf, hcase, hM⟩ := exists_model_of_famOrth hK
  have hKq : CFSG.Open.IsQuasisimple ↥K := ctx.comp.2.2
  have hZ := famOrth_coprime_center hGA hKq hK
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hcardF : ∀ {F : Type} [Field F] [Finite F], Nat.card F = 2 ^ f →
      Nat.card F = 2 ∨ Nat.card F = 8 := fun hF =>
    hf.imp (fun h => by rw [hF, h]; norm_num) (fun h => by rw [hF, h]; norm_num)
  have hchar : ∀ {F : Type} [Field F] [Finite F], Nat.card F = 2 ^ f → CharP F 2 := by
    intro F _ _ hF
    haveI := Fintype.ofFinite F
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hF])
  rcases hcase with ⟨rfl, -, h6 | ⟨rfl, rfl⟩⟩ | ⟨rfl, -, h5⟩
  · obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hM.2
    haveI := hchar hF
    have hd : 0 < 2 * n := by omega
    have hreg := regular_coordinateQuadPlus n F (by omega : 3 ≤ n)
    let e := (coordinatePlusWitnessEquiv F e₀).trans (coordBridge (coordinateQuadPlus n F) hd)
    have hker := fun g => ((orthogonal_large_prime_semilinear_field_and_diagonal_gates _
      .POmegaPlus (Or.inr (Or.inl rfl)) n 2 f hM F hF e₀).1 g).mp
    exact Or.inr (su38Toral_of_projOrth hTor hFix ctx hZ (hcardF hF) hd hreg.1 hreg.2 hker
      (matrixProjectiveImage_eq_top_plus F n (by omega)) (Or.inl rfl) (by omega) hf
      ⟨hM.1, F, inferInstance, inferInstance, hF, ⟨e.symm.trans e₀⟩⟩ e haA ha1 hJ hJU hBJ)
  · exfalso
    have hdvd := (FirstClaim.card_centerQuot_dvd_card_image
      (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) hJK).trans (Subgroup.card_subgroup_dvd_card _)
    rw [uni_card_su38 hJU, (CFSG.Timmesfeld.card_statedClassicalModel_two hM).2.2.2.1 rfl] at hdvd
    exact (by unfold ordD; decide : ¬ 5515776 ∣ ordD 4 (2 ^ 1)) hdvd
  · obtain ⟨F, _, _, hF, b, c, hirr, ⟨e₀⟩⟩ := hM.2
    haveI := hchar hF
    have hn1 : 1 ≤ n := by omega
    have hd : 0 < 2 * n := by omega
    have hreg := regular_coordinateQuadMinus n F b c (by omega : 4 ≤ n) hirr
    let e := (coordinateMinusWitnessEquiv F hn1 b c e₀).trans
      (coordBridge (coordinateQuadMinus n F hn1 b c) hd)
    have hker := fun g => ((orthogonal_large_prime_semilinear_field_and_diagonal_gates _
      .POmegaMinus (Or.inr (Or.inr rfl)) n 2 f hM hn1 F hF b c hirr e₀).1 g).mp
    exact Or.inr (su38Toral_of_projOrth hTor hFix ctx hZ (hcardF hF) hd hreg.1 hreg.2 hker
      (matrixProjectiveImage_eq_top_minus F n (by omega) b c hirr) (Or.inr rfl) h5 hf
      ⟨hM.1, F, inferInstance, inferInstance, hF, b, c, hirr, ⟨e.symm.trans e₀⟩⟩ e haA ha1 hJ
      hJU hBJ)

end CFSG.HardMathSupport.Dickson.Bal207.OrthFix

end
