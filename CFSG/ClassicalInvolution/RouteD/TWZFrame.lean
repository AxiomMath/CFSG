module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Aut
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

section Neg

theorem polar_apply_apply {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (a b : V) : polar Q (g a) (g b) = polar Q a b :=
  polar_map_of_mem hg a b

theorem coords_apply_of_neg (fr : OFrame Q) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hneg : ∀ x ∈ fr.span, g x = -x) (x : V) :
    fr.coords (g x) = -fr.coords x := by
  have key : ∀ s ∈ fr.span, polar Q (g x) s = -polar Q x s := by
    intro s hs
    have hgs : g (-s) = s := by
      rw [map_neg, hneg s hs, neg_neg]
    have h1 := polar_apply_apply hg x (-s)
    rw [hgs] at h1
    rw [h1, polar_neg_right]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Frame.coords_apply, key _ fr.e₁_mem_span, key _ fr.f₁_mem_span,
      key _ fr.e₂_mem_span, key _ fr.f₂_mem_span]

theorem La_comm_of_neg_on_span (fr : OFrame Q) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hneg : ∀ x ∈ fr.span, g x = -x)
    (A : SL(2, F)) : g * fr.La A = fr.La A * g := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Frame.La_apply, Frame.La_apply, map_add,
    hneg _ ⟨_, rfl⟩, coords_apply_of_neg fr hg hneg x]
  simp only [mul_neg, map_sub, map_neg]
  abel

theorem neg_on_span_of_basis (fr : OFrame Q) (T : V ≃ₗ[F] V) (h1 : T fr.e₁ = -fr.e₁)
    (h2 : T fr.f₁ = -fr.f₁) (h3 : T fr.e₂ = -fr.e₂) (h4 : T fr.f₂ = -fr.f₂) :
    ∀ x ∈ fr.span, T x = -x := by
  rintro _ ⟨Y, rfl⟩
  rw [Frame.incl_apply, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1,
    h2, h3, h4]
  module

end Neg

section Link

variable [Finite F] [FiniteDimensional F V]

theorem exists_linked_frame (hodd : Odd (Nat.card F)) (fr₂ : OFrame Q) {y : V ≃ₗ[F] V}
    (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hy₂ : ∀ x ∈ fr₂.span, y x = x)
    {a₁ a₂ : V} (ha₁ : a₁ ∈ minusSp y) (ha₂ : a₂ ∈ minusSp y) (ha₁₂ : polar Q a₁ a₂ = 0)
    (hQ₁ : Q a₁ ≠ 0) (hQ₂ : Q a₂ ≠ 0) :
    ∃ fr' : OFrame Q, (∀ x ∈ fr'.span, (y * fr₂.La (-1)) x = -x) ∧
      ¬ ∀ A : SL(2, F), y * fr'.La A = fr'.La A * y := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hP : (Q.restrict fr₂.span).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_restrict (Frame.polarNondegOn_span fr₂))
  obtain ⟨l, hlen, hlorth, hlne, hlspan, -⟩ := exists_orthogonal_list_restrict Q fr₂.span hP
  rw [Frame.finrank_span] at hlen
  rcases l with _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨b₄, _ | ⟨b₅, rest⟩⟩⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  swap
  · simp at hlen
  have hb₁ : Q b₁ ≠ 0 := hlne b₁ (by simp)
  have hb₂ : Q b₂ ≠ 0 := hlne b₂ (by simp)
  have hb₃ : Q b₃ ≠ 0 := hlne b₃ (by simp)
  have hb₄ : Q b₄ ≠ 0 := hlne b₄ (by simp)
  have hmem : ∀ b ∈ [b₁, b₂, b₃, b₄], b ∈ fr₂.span := fun b hb =>
    hlspan ▸ Submodule.subset_span hb
  have hm₁ : b₁ ∈ fr₂.span := hmem b₁ (by simp)
  have hm₂ : b₂ ∈ fr₂.span := hmem b₂ (by simp)
  have hm₃ : b₃ ∈ fr₂.span := hmem b₃ (by simp)
  have hm₄ : b₄ ∈ fr₂.span := hmem b₄ (by simp)
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true] at hlorth
  obtain ⟨⟨o₁₂, o₁₃, o₁₄⟩, ⟨o₂₃, o₂₄⟩, o₃₄, -⟩ := hlorth
  have p₁₂ := o₁₂.polar_eq_zero
  have p₁₃ := o₁₃.polar_eq_zero
  have p₁₄ := o₁₄.polar_eq_zero
  have p₂₃ := o₂₃.polar_eq_zero
  have p₂₄ := o₂₄.polar_eq_zero
  have p₃₄ := o₃₄.polar_eq_zero
  have := Fintype.ofFinite F
  have hK' : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  obtain ⟨s₁, t₁, hst₁⟩ := CFSG.RankThree.Classical.exists_mul_sq_add_mul_sq_eq hK' hb₁ hb₂
    (-Q a₁)
  obtain ⟨s₂, t₂, hst₂⟩ := CFSG.RankThree.Classical.exists_mul_sq_add_mul_sq_eq hK' hb₃ hb₄
    (-Q a₂)
  set c₁ : V := s₁ • b₁ + t₁ • b₂ with hc₁
  set c₂ : V := s₂ • b₃ + t₂ • b₄ with hc₂
  have hQc₁ : Q c₁ = -Q a₁ := by
    rw [hc₁, CFSG.RankThree.Classical.quad_smul_add_smul Q p₁₂]
    linear_combination hst₁
  have hQc₂ : Q c₂ = -Q a₂ := by
    rw [hc₂, CFSG.RankThree.Classical.quad_smul_add_smul Q p₃₄]
    linear_combination hst₂
  have hcm₁ : c₁ ∈ fr₂.span := fr₂.span.add_mem (fr₂.span.smul_mem _ hm₁) (fr₂.span.smul_mem _ hm₂)
  have hcm₂ : c₂ ∈ fr₂.span := fr₂.span.add_mem (fr₂.span.smul_mem _ hm₃) (fr₂.span.smul_mem _ hm₄)
  have hc₁₂ : polar Q c₁ c₂ = 0 := by
    simp only [hc₁, hc₂, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
      p₁₃, p₁₄, p₂₃, p₂₄]
    simp
  have hac₁₁ : polar Q a₁ c₁ = 0 := polar_minusSp_span fr₂ h2 hyO hy₂ ha₁ hcm₁
  have hac₁₂ : polar Q a₁ c₂ = 0 := polar_minusSp_span fr₂ h2 hyO hy₂ ha₁ hcm₂
  have hac₂₁ : polar Q a₂ c₁ = 0 := polar_minusSp_span fr₂ h2 hyO hy₂ ha₂ hcm₁
  have hac₂₂ : polar Q a₂ c₂ = 0 := polar_minusSp_span fr₂ h2 hyO hy₂ ha₂ hcm₂
  have hya₁ : y a₁ = -a₁ := mem_minusSp.mp ha₁
  have hya₂ : y a₂ = -a₂ := mem_minusSp.mp ha₂
  have hyc₁ : y c₁ = c₁ := hy₂ c₁ hcm₁
  have hyc₂ : y c₂ = c₂ := hy₂ c₂ hcm₂
  have hκ₁ : (4 : F) * Q a₁ ≠ 0 := mul_ne_zero h4 hQ₁
  have hκ₂ : (4 : F) * Q a₂ ≠ 0 := mul_ne_zero h4 hQ₂
  have hQsum : ∀ {a c : V}, polar Q a c = 0 → Q (a + c) = Q a + Q c := fun h => by
    rw [QuadraticMap.map_add Q, h, add_zero]
  have hQdiff : ∀ {a c : V}, polar Q a c = 0 → Q (a - c) = Q a + Q c := fun h => by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right, h,
      neg_zero, add_zero]
  have hpolar_self : ∀ a : V, polar Q a a = 2 * Q a := fun a => by
    rw [QuadraticMap.polar_self, two_nsmul, two_mul]
  have hQe₁ : Q (a₁ + c₁) = 0 := by rw [hQsum hac₁₁, hQc₁]; ring
  have hQf₁ : Q ((4 * Q a₁)⁻¹ • (a₁ - c₁)) = 0 := by
    rw [QuadraticMap.map_smul, hQdiff hac₁₁, hQc₁]; ring
  have hef₁ : polar Q (a₁ + c₁) ((4 * Q a₁)⁻¹ • (a₁ - c₁)) = 1 := by
    rw [polar_smul_right, polar_add_left, polar_sub_right, polar_sub_right,
      polar_comm Q c₁ a₁, hac₁₁, hpolar_self, hpolar_self, hQc₁, smul_eq_mul]
    field_simp
    ring
  have hQe₂ : Q (a₂ + c₂) = 0 := by rw [hQsum hac₂₂, hQc₂]; ring
  have hQf₂ : Q ((4 * Q a₂)⁻¹ • (a₂ - c₂)) = 0 := by
    rw [QuadraticMap.map_smul, hQdiff hac₂₂, hQc₂]; ring
  have hef₂ : polar Q (a₂ + c₂) ((4 * Q a₂)⁻¹ • (a₂ - c₂)) = 1 := by
    rw [polar_smul_right, polar_add_left, polar_sub_right, polar_sub_right,
      polar_comm Q c₂ a₂, hac₂₂, hpolar_self, hpolar_self, hQc₂, smul_eq_mul]
    field_simp
    ring
  let P₁ : HypPair Q := ⟨a₁ + c₁, (4 * Q a₁)⁻¹ • (a₁ - c₁), hQe₁, hQf₁, hef₁⟩
  let P₂ : HypPair Q := ⟨a₂ + c₂, (4 * Q a₂)⁻¹ • (a₂ - c₂), hQe₂, hQf₂, hef₂⟩
  have hca₂₁ : polar Q c₁ a₂ = 0 := by rw [polar_comm]; exact hac₂₁
  have horth : P₁.Orth P₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [P₁, P₂, polar_add_left, polar_add_right, polar_sub_left, polar_sub_right,
        polar_smul_left, polar_smul_right, ha₁₂, hac₁₂, hca₂₁, hc₁₂]
      simp
  obtain ⟨fr', he₁, hf₁, he₂, hf₂⟩ : ∃ fr' : OFrame Q, fr'.e₁ = a₁ + c₁ ∧
      fr'.f₁ = (4 * Q a₁)⁻¹ • (a₁ - c₁) ∧ fr'.e₂ = a₂ + c₂ ∧
      fr'.f₂ = (4 * Q a₂)⁻¹ • (a₂ - c₂) := ⟨⟨P₁, P₂, horth⟩, rfl, rfl, rfl, rfl⟩
  have hperp₁ : a₁ ∈ fr₂.perp := minusSp_le_perp fr₂ h2 hyO hy₂ ha₁
  have hperp₂ : a₂ ∈ fr₂.perp := minusSp_le_perp fr₂ h2 hyO hy₂ ha₂
  have hLa₁ : fr₂.La (-1) a₁ = a₁ := (Frame.mem_perp_iff_fix fr₂ h2).mp hperp₁
  have hLa₂ : fr₂.La (-1) a₂ = a₂ := (Frame.mem_perp_iff_fix fr₂ h2).mp hperp₂
  have hLc₁ : fr₂.La (-1) c₁ = -c₁ := (Frame.mem_span_iff_inv fr₂ h2).mp hcm₁
  have hLc₂ : fr₂.La (-1) c₂ = -c₂ := (Frame.mem_span_iff_inv fr₂ h2).mp hcm₂
  have hτ : ∀ a c : V, y a = -a → y c = c → fr₂.La (-1) a = a → fr₂.La (-1) c = -c →
      (y * fr₂.La (-1)) (a + c) = -(a + c) ∧ (y * fr₂.La (-1)) (a - c) = -(a - c) := by
    intro a c hya hyc hLa hLc
    constructor
    · simp only [LinearEquiv.mul_apply, map_add, map_neg, hLa, hLc, hya, hyc]
      abel
    · simp only [LinearEquiv.mul_apply, map_sub, map_neg, hLa, hLc, hya, hyc]
      abel
  have τ₁ := hτ a₁ c₁ hya₁ hyc₁ hLa₁ hLc₁
  have τ₂ := hτ a₂ c₂ hya₂ hyc₂ hLa₂ hLc₂
  have hτe₁ : (y * fr₂.La (-1)) fr'.e₁ = -fr'.e₁ := by rw [he₁]; exact τ₁.1
  have hτf₁ : (y * fr₂.La (-1)) fr'.f₁ = -fr'.f₁ := by
    rw [hf₁, map_smul, τ₁.2, smul_neg]
  have hτe₂ : (y * fr₂.La (-1)) fr'.e₂ = -fr'.e₂ := by rw [he₂]; exact τ₂.1
  have hτf₂ : (y * fr₂.La (-1)) fr'.f₂ = -fr'.f₂ := by
    rw [hf₂, map_smul, τ₂.2, smul_neg]
  refine ⟨fr', neg_on_span_of_basis fr' (y * fr₂.La (-1)) hτe₁ hτf₁ hτe₂ hτf₂, fun hall => ?_⟩
  set A₀ : SL(2, F) :=
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1 with hA₀
  have hA := LinearEquiv.congr_fun (hall A₀) fr'.f₁
  have hf₁i : fr'.f₁ = fr'.incl !![0, 0; 0, 1] := Frame.f₁_eq_incl fr'
  have he₁i : fr'.e₁ = fr'.incl !![1, 0; 0, 0] := Frame.e₁_eq_incl fr'
  have hLf₁ : fr'.La A₀ fr'.f₁ = fr'.f₁ - fr'.e₂ := by
    have h := Frame.La_apply_incl fr' A₀ !![0, 0; 0, 1]
    rw [← hf₁i, hA₀, Frame.coe_transvection_zero_one, Matrix.mul_fin_two] at h
    rw [h, Frame.incl_apply]
    simp [sub_eq_add_neg]
  have hLe₁ : fr'.La A₀ fr'.e₁ = fr'.e₁ := by
    have h := Frame.La_apply_incl fr' A₀ !![1, 0; 0, 0]
    rw [← he₁i, hA₀, Frame.coe_transvection_zero_one, Matrix.mul_fin_two] at h
    rw [h, he₁i]
    simp
  have hyf₁ : y fr'.f₁ = -((4 * Q a₁)⁻¹ • fr'.e₁) := by
    rw [hf₁, he₁, map_smul, map_sub, hya₁, hyc₁, ← smul_neg]
    congr 1
    abel
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hLf₁, hyf₁, map_neg, map_smul, hLe₁,
    map_sub, hyf₁] at hA
  have hye₂ : y fr'.e₂ = 0 := sub_eq_self.mp hA
  have he₂0 : fr'.e₂ = 0 := (LinearEquiv.map_eq_zero_iff y).mp hye₂
  have h1 := fr'.polar_e₂_f₂
  rw [he₂0, polar_zero_left] at h1
  exact zero_ne_one h1

end Link

section Sign

theorem eq_mul_right_of_commute_left (T : Matrix (Fin 2) (Fin 2) F →ₗ[F] Matrix (Fin 2) (Fin 2) F)
    (hL₁ : ∀ X, T (!![0, 1; 0, 0] * X) = !![0, 1; 0, 0] * T X)
    (hL₂ : ∀ X, T (!![0, 0; 1, 0] * X) = !![0, 0; 1, 0] * T X) (X : Matrix (Fin 2) (Fin 2) F) :
    T X = X * T 1 := by
  set C := T 1 with hC
  have hdec : ∀ X : Matrix (Fin 2) (Fin 2) F, X = X 0 0 • !![1, 0; 0, 0] + X 0 1 • !![0, 1; 0, 0] +
      X 1 0 • !![0, 0; 1, 0] + X 1 1 • !![0, 0; 0, 1] := by
    intro X
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have t12 : T !![0, 1; 0, 0] = !![0, 1; 0, 0] * C := by
    have := hL₁ 1
    rwa [mul_one] at this
  have t21 : T !![0, 0; 1, 0] = !![0, 0; 1, 0] * C := by
    have := hL₂ 1
    rwa [mul_one] at this
  have t11 : T !![1, 0; 0, 0] = !![1, 0; 0, 0] * C := by
    have e : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 0, 0] * !![0, 0; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [e, hL₁, t21, ← mul_assoc]
  have t22 : T !![0, 0; 0, 1] = !![0, 0; 0, 1] * C := by
    have e : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) = !![0, 0; 1, 0] * !![0, 1; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [e, hL₂, t12, ← mul_assoc]
  conv_lhs => rw [hdec X]
  simp only [map_add, map_smul, t11, t12, t21, t22]
  conv_rhs => rw [hdec X]
  simp only [add_mul, smul_mul_assoc]

theorem matrix_eq_one_or_neg_one (h2 : (2 : F) ≠ 0) {C : Matrix (Fin 2) (Fin 2) F}
    (hdet : C.det = 1) (hsq : C * C = 1) : C = 1 ∨ C = -1 := by
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  have e11 := congrFun (congrFun hsq 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  by_cases htr : C 0 0 + C 1 1 = 0
  · exfalso
    apply h2
    linear_combination (-1 : F) * hdet + (-1 : F) * e00 + C 0 0 * htr
  · have hb : C 0 1 = 0 := by
      have : C 0 1 * (C 0 0 + C 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right htr
    have hc : C 1 0 = 0 := by
      have : C 1 0 * (C 0 0 + C 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right htr
    rw [hb, hc] at e00 e11 hdet
    have ha : C 0 0 = C 1 1 := by
      have h1 : C 0 0 * C 1 1 = 1 := by linear_combination hdet
      have h3 : C 0 0 * (C 0 0 - C 1 1) = 0 := by linear_combination e00 - h1
      rcases mul_eq_zero.mp h3 with h | h
      · rw [h] at h1
        simp at h1
      · exact sub_eq_zero.mp h
    have ha2 : (C 0 0 - 1) * (C 0 0 + 1) = 0 := by linear_combination e00
    rcases mul_eq_zero.mp ha2 with h | h
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, ← ha, sub_eq_zero.mp h]
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, ← ha, eq_neg_of_add_eq_zero_left h]

theorem sign_on_span (h2 : (2 : F) ≠ 0) (fr : OFrame Q) {y : V ≃ₗ[F] V}
    (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hyy : y * y = 1)
    (hcomm : ∀ A : SL(2, F), y * fr.La A = fr.La A * y) :
    (∀ x ∈ fr.span, y x = x) ∨ (∀ x ∈ fr.span, y x = -x) := by
  have hz : ∀ x, y (fr.La (-1) x) = fr.La (-1) (y x) := fun x => by
    have := congrArg (fun g : V ≃ₗ[F] V => g x) (hcomm (-1))
    simpa using this
  have hspan : ∀ x ∈ fr.span, y x ∈ fr.span := by
    intro x hx
    rw [Frame.mem_span_iff_inv fr h2]
    rw [← hz, (Frame.mem_span_iff_inv fr h2).mp hx, map_neg]
  have hT : ∀ X, y (fr.incl X) = fr.incl (fr.coords (y (fr.incl X))) := fun X =>
    (Frame.mem_span_iff fr).mp (hspan _ ⟨X, rfl⟩)
  let T : Matrix (Fin 2) (Fin 2) F →ₗ[F] Matrix (Fin 2) (Fin 2) F :=
    fr.coords ∘ₗ (y : V →ₗ[F] V) ∘ₗ fr.incl
  have hTy : ∀ X, y (fr.incl X) = fr.incl (T X) := hT
  have hinj : ∀ X Y, fr.incl X = fr.incl Y → X = Y := fun X Y h => by
    have := congrArg fr.coords h
    rwa [Frame.coords_incl, Frame.coords_incl] at this
  have hL : ∀ (A : SL(2, F)) X, T ((A : Matrix (Fin 2) (Fin 2) F) * X) =
      (A : Matrix (Fin 2) (Fin 2) F) * T X := by
    intro A X
    apply hinj
    have h := congrArg (fun g : V ≃ₗ[F] V => g (fr.incl X)) (hcomm A)
    simp only [LinearEquiv.mul_apply] at h
    rw [Frame.La_apply_incl, hTy, hTy, Frame.La_apply_incl] at h
    exact h
  have e12 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) = 1 + !![0, 1; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have e21 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) = 1 + !![0, 0; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hL₁ : ∀ X, T (!![0, 1; 0, 0] * X) = !![0, 1; 0, 0] * T X := by
    intro X
    have h := hL (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1) X
    rw [Frame.coe_transvection_zero_one, e12, add_mul, add_mul, one_mul, one_mul, map_add] at h
    exact add_left_cancel h
  have hL₂ : ∀ X, T (!![0, 0; 1, 0] * X) = !![0, 0; 1, 0] * T X := by
    intro X
    have h := hL (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1) X
    rw [Frame.coe_transvection_one_zero, e21, add_mul, add_mul, one_mul, one_mul, map_add] at h
    exact add_left_cancel h
  have hTX := eq_mul_right_of_commute_left T hL₁ hL₂
  set C := T 1 with hC
  have hdet : C.det = 1 := by
    have h1 : Q (y (fr.incl 1)) = Q (fr.incl 1) :=
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hyO) _
    rw [hTy, Frame.Q_incl, Frame.Q_incl] at h1
    simpa [hTX 1] using h1
  have hsq : C * C = 1 := by
    have h1 : y (y (fr.incl 1)) = fr.incl 1 := by
      have := congrArg (fun g : V ≃ₗ[F] V => g (fr.incl 1)) hyy
      simpa using this
    rw [hTy, hTy] at h1
    have h2' := hinj _ _ h1
    rw [hTX (T 1), hTX 1] at h2'
    simpa using h2'
  have hy : ∀ X, y (fr.incl X) = fr.incl (X * C) := fun X => by rw [hTy, hTX X]
  rcases matrix_eq_one_or_neg_one h2 hdet hsq with h | h
  · left
    rintro _ ⟨X, rfl⟩
    rw [hy, h, mul_one]
  · right
    rintro _ ⟨X, rfl⟩
    rw [hy, h, mul_neg, mul_one, map_neg]

end Sign

end CFSG.ClassicalInvolution.RouteD.TWZ
