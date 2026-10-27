module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcRoot
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalGroup
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Perfect
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.RankThree.PartOne.S11d.OutLinear
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
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.Exc

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement MatrixGroups

section General

variable {A C : Type*} [Group A] [Group C] (f : A →* C)

theorem pow_conj_eq_of_mem_center {a h : A} (hz : a * h * a⁻¹ * h⁻¹ ∈ center A) (n : ℕ) :
    a ^ n * h * (a ^ n)⁻¹ = (a * h * a⁻¹ * h⁻¹) ^ n * h := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzn := Subgroup.pow_mem _ hz n
    calc a ^ (n + 1) * h * (a ^ (n + 1))⁻¹ = a * (a ^ n * h * (a ^ n)⁻¹) * a⁻¹ := by group
      _ = a * ((a * h * a⁻¹ * h⁻¹) ^ n * h) * a⁻¹ := by rw [ih]
      _ = (a * h * a⁻¹ * h⁻¹) ^ n * (a * h * a⁻¹) := by
        rw [show a * ((a * h * a⁻¹ * h⁻¹) ^ n * h) * a⁻¹ =
          (a * (a * h * a⁻¹ * h⁻¹) ^ n) * h * a⁻¹ by group, (mem_center_iff.1 hzn a)]
        group
      _ = (a * h * a⁻¹ * h⁻¹) ^ (n + 1) * h := by rw [pow_succ]; group

theorem mem_map_centralizer_of_pow (hfs : Function.Surjective f) (hker : f.ker ≤ center A)
    (hodd : Odd (Nat.card f.ker)) (H : Subgroup A) {c : C}
    (hc : c ∈ centralizer ((H.map f : Subgroup C) : Set C)) {k : ℕ} (hck : c ^ 2 ^ k = 1) :
    c ∈ (centralizer (H : Set A)).map f := by
  obtain ⟨a, rfl⟩ := hfs c
  refine ⟨a, mem_centralizer_iff.2 fun h hh => ?_, rfl⟩
  have hfh := mem_centralizer_iff.1 hc (f h) ⟨h, hh, rfl⟩
  have hzk : a * h * a⁻¹ * h⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hfh]
    group
  have hzc := hker hzk
  have ha : a ^ 2 ^ k ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow, hck]
  have h1 := pow_conj_eq_of_mem_center hzc (2 ^ k)
  rw [← mem_center_iff.1 (hker ha) h, mul_inv_cancel_right] at h1
  have hz2 : (a * h * a⁻¹ * h⁻¹) ^ 2 ^ k = 1 := by
    have := congrArg (· * h⁻¹) h1
    simpa using this.symm
  have hzo : Odd (orderOf (a * h * a⁻¹ * h⁻¹)) :=
    CFSG.ComponentClassification.RankTwoL3Even.odd_orderOf_of_mem hodd hzk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hz2)
  have hi0 : i = 0 := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exact h0
    · exfalso
      rw [hi] at hzo
      exact (Nat.not_even_iff_odd.2 hzo) ((Nat.even_pow' h0.ne').2 even_two)
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  exact (calc a * h = (a * h * a⁻¹ * h⁻¹) * (h * a) := by group
    _ = h * a := by rw [hi, one_mul]).symm

theorem le_normalizer_map_centralizer (hfs : Function.Surjective f) (hker : f.ker ≤ center A)
    (H : Subgroup A) :
    centralizer ((H.map f : Subgroup C) : Set C) ≤
      normalizer (((centralizer (H : Set A)).map f : Subgroup C) : Set C) :=
  CFSG.LieType.Chevalley.EvenOddRadical.le_normalizer_of_conj_mem fun c hc y hy => by
    obtain ⟨a, rfl⟩ := hfs c
    obtain ⟨d, hd, rfl⟩ := hy
    refine ⟨a * d * a⁻¹, mem_centralizer_iff.2 fun h hh => ?_, by simp only [map_mul, map_inv]⟩
    have hfh := mem_centralizer_iff.1 (inv_mem hc) (f h) ⟨h, hh, rfl⟩
    have hzk : a⁻¹ * h * a * h⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [show (f a)⁻¹ * f h = f h * (f a)⁻¹ from hfh.symm]
      group
    have hzc := mem_center_iff.1 (hker hzk)
    have e1 : a⁻¹ * h * a = (a⁻¹ * h * a * h⁻¹) * h := by group
    have hdh : h * d = d * h := mem_centralizer_iff.1 hd h hh
    have hzd : (a⁻¹ * h * a * h⁻¹) * d = d * (a⁻¹ * h * a * h⁻¹) := (hzc d).symm
    calc h * (a * d * a⁻¹) = a * (a⁻¹ * h * a) * d * a⁻¹ := by group
      _ = a * ((a⁻¹ * h * a * h⁻¹) * (h * d)) * a⁻¹ := by rw [e1]; group
      _ = a * (((a⁻¹ * h * a * h⁻¹) * d) * h) * a⁻¹ := by rw [hdh]; group
      _ = a * (d * ((a⁻¹ * h * a * h⁻¹) * h)) * a⁻¹ := by rw [hzd]; group
      _ = a * d * a⁻¹ * h := by rw [← e1]; group

end General

section Root

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {C : Type} [Group C]
  {ψ : normalizer (A : Set G) →* MulAut C}
  (hZC : center C = ⊥) (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
include hZC hψ

omit hZC in
theorem exists_mem_of_card_eq_of_actsIn [Finite C] (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h34 : Asc08Lemma34) (hc : Sec3 A R T g) {U : Subgroup C} (hT : ActsIn ψ T U)
    (hTU : Nat.card T = Nat.card U) {w : C} (hw : w ∈ U) :
    ∃ s ∈ T, ∃ hsN : s ∈ normalizer (A : Set G), ψ ⟨s, hsN⟩ = MulAut.conj w := by
  have key : ∀ s : T, ∃ c : U, ψ ⟨s, hc.le_normalizer s.2⟩ = MulAut.conj (c : C) := by
    intro s
    obtain ⟨c, hc'⟩ := exists_conj_of_mem hψ hc h32 h4 h34 s.2 (hc.le_normalizer s.2)
    exact ⟨⟨c, (actsIn_iff.1 hT) s s.2 _ c hc'⟩, hc'⟩
  choose F hF using key
  have hFinj : Function.Injective F := fun s s' h => by
    have hsN := hc.le_normalizer s.2
    have hs'N := hc.le_normalizer s'.2
    have h1 : ψ ⟨(s : G)⁻¹ * s', mul_mem (inv_mem hsN) hs'N⟩ = 1 := by
      rw [psi_mul (inv_mem hsN) hs'N, psi_inv hsN, hF s, hF s', h, inv_mul_cancel]
    have h2 := (hψ.eq_one_iff _).1 h1
    by_contra hne
    refine not_mem_centralizer hc h32 (mul_mem (inv_mem s.2) s'.2) ?_ h2
    intro h3
    exact hne (Subtype.ext (inv_mul_eq_one.1 h3))
  have hFbij := hFinj.bijective_of_nat_card_le hTU.ge
  obtain ⟨s, hs⟩ := hFbij.2 ⟨w, hw⟩
  refine ⟨s, s.2, hc.le_normalizer s.2, ?_⟩
  rw [hF s, hs]

theorem not_le_normalizer_qLift_of_oTwo_of_inf [Finite C] (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h34 : Asc08Lemma34) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) {reps : List C} (hcover : ClassesCover reps)
    (hR₁A : rightConjugate R g⁻¹ ⊓ A = ⊥) (hchar : ∀ y ∈ reps, CharTwo y)
    (hO2 : ∀ S : Subgroup C, Odd (Nat.card S) → ∀ N : Subgroup C,
      N ≤ centralizer (S : Set C) → (N.subgroupOf (centralizer (S : Set C))).Normal →
        IsPGroup 2 N → N = ⊥)
    {Ql : Subgroup C} (hQodd : Odd (Nat.card Ql)) :
    ¬ centralizer (qLift ψ T Ql : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G) := by
  intro hle
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hsw := hc.swap
  set R₁ := rightConjugate R g⁻¹ with hR₁
  have hX : CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) = rightConjugate
      (CFSG.Quasithin.perfectCore (A ⊓ centralizer (R₁ : Set G))) g := by
    rw [hc.perfectCore_eq h32 h4 h34 hOut, RankTwoClassical.rightConjugate_perfectCore,
      RankTwoClassical.rightConjugate_inf, ← AS76b.centralizer_rightConjugate,
      RankTwoClassical.rightConjugate_inv_rightConjugate]
  have hM₁ : ∀ w ∈ qLift ψ T Ql, g * w * g⁻¹ ∈ A ⊓ centralizer (R₁ : Set G) := by
    intro w hw
    have h1 : w ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) := (mem_inf.1 hw).1
    rw [hX, mem_rightConjugate_iff] at h1
    exact CFSG.Quasithin.perfectCore_le _ h1
  obtain ⟨⟨r₀, hr₀⟩, hr₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hsw.T_ne_bot
  have hr₀1' : r₀ ≠ 1 := fun h => hr₀1 (Subtype.ext h)
  have hr₀N := hsw.le_normalizer hr₀
  obtain ⟨x', hx'⟩ := exists_conj_of_mem hψ hsw h32 h4 h34 hr₀ hr₀N
  obtain ⟨hx'2, hx'1⟩ := involution_of_conj hZC hψ hsw h32 hr₀ hr₀N hx'
  have hr₀2 : r₀ ^ 2 = 1 := (hsw.elemT h32).2 r₀ hr₀
  set Q₁ := rightConjugate (qLift ψ T Ql) g⁻¹ with hQ₁
  have hQ₁mem : ∀ v, v ∈ Q₁ ↔ g⁻¹ * v * g ∈ qLift ψ T Ql := by
    intro v
    rw [hQ₁, mem_rightConjugate_iff, inv_inv]
  have hQ₁R : ∀ v ∈ Q₁, v ∈ A ⊓ centralizer (R₁ : Set G) := by
    intro v hv
    have h1 := hM₁ _ ((hQ₁mem v).1 hv)
    rwa [show g * (g⁻¹ * v * g) * g⁻¹ = v by group] at h1
  have hQ₁A : Q₁ ≤ A := fun v hv => (mem_inf.1 (hQ₁R v hv)).1
  have hQ₁le : Q₁ ≤ A ⊓ centralizer ({r₀} : Set G) := fun v hv =>
    mem_inf.2 ⟨hQ₁A hv, mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 (mem_inf.1 (hQ₁R v hv)).2 r₀ hr₀).symm⟩
  have hSle : img ψ Q₁ ≤ cent x' := by
    rw [← img_centralizer_eq hZC hψ hZA hr₀N hr₀2 hx']
    exact img_mono hQ₁le
  have hSodd : Odd (Nat.card (img ψ Q₁)) := by
    refine AS76b.Lemma22.odd_card_of_forall_orderOf_ne_two fun c hc' h2 => ?_
    obtain ⟨v, hv, hvN, hvc⟩ := mem_img.1 hc'
    have hvo : Odd (orderOf v) := by
      have h1 := odd_orderOf_of_mem_qLift hψ hZA hQodd ((hQ₁mem v).1 hv)
      have e : g⁻¹ * v * g = MulAut.conj g⁻¹ v := by simp
      rwa [e, MulEquiv.orderOf_eq] at h1
    have h3 : orderOf c ∣ orderOf v := by
      have h4 := orderOf_map_dvd ψ ⟨v, hvN⟩
      rwa [hvc, orderOf_injective _ hinj, Subgroup.orderOf_mk] at h4
    rw [h2] at h3
    exact (Nat.not_even_iff_odd.2 hvo) (even_iff_two_dvd.2 h3)
  have hdN : ∀ d ∈ A ⊓ centralizer (Q₁ : Set G), d ∈ normalizer (R₁ : Set G) := by
    intro d hd
    have hdA : d ∈ A := (mem_inf.1 hd).1
    have h1 : g⁻¹ * d * g ∈ centralizer (qLift ψ T Ql : Set G) ⊓ centralizer (T : Set G) := by
      refine mem_inf.2 ⟨mem_centralizer_iff.2 fun w hw => ?_, mem_centralizer_iff.2 fun t ht => ?_⟩
      · have hv : g * w * g⁻¹ ∈ Q₁ := by
          rw [hQ₁mem]
          simpa [mul_assoc] using hw
        have h2 : g * w * g⁻¹ * d = d * (g * w * g⁻¹) :=
          mem_centralizer_iff.1 (mem_inf.1 hd).2 _ hv
        calc w * (g⁻¹ * d * g) = g⁻¹ * (g * w * g⁻¹ * d) * g := by group
          _ = g⁻¹ * (d * (g * w * g⁻¹)) * g := by rw [h2]
          _ = g⁻¹ * d * g * w := by group
      · have hgt : g * t * g⁻¹ ∈ centralizer (A : Set G) :=
          hsw.sylowR.le (conj_mem_rightConjugate_inv ht g)
        have h2 : g * t * g⁻¹ * d = d * (g * t * g⁻¹) := (mem_centralizer_iff.1 hgt d hdA).symm
        calc t * (g⁻¹ * d * g) = g⁻¹ * (g * t * g⁻¹ * d) * g := by group
          _ = g⁻¹ * (d * (g * t * g⁻¹)) * g := by rw [h2]
          _ = g⁻¹ * d * g * t := by group
    rw [hR₁, AS76b.mem_normalizer_rightConjugate_iff, inv_inv]
    exact hle h1
  have hdR : ∀ d ∈ A ⊓ centralizer (Q₁ : Set G), ∀ r ∈ R₁, d * r = r * d := by
    intro d hd r hr
    have hdA : d ∈ A := (mem_inf.1 hd).1
    have h1 : d * r * d⁻¹ * r⁻¹ ∈ R₁ :=
      mul_mem ((mem_normalizer_iff.1 (hdN d hd) r).1 hr) (inv_mem hr)
    have h2 : d * r * d⁻¹ * r⁻¹ ∈ A := by
      have h3 : r * d⁻¹ * r⁻¹ ∈ A :=
        (mem_normalizer_iff.1 (hsw.le_normalizer hr) _).1 (inv_mem hdA)
      have he : d * r * d⁻¹ * r⁻¹ = d * (r * d⁻¹ * r⁻¹) := by group
      rw [he]
      exact mul_mem hdA h3
    have h5 : d * r * d⁻¹ * r⁻¹ ∈ R₁ ⊓ A := mem_inf.2 ⟨h1, h2⟩
    rw [hR₁A, mem_bot] at h5
    calc d * r = d * r * d⁻¹ * r⁻¹ * (r * d) := by group
      _ = r * d := by rw [h5, one_mul]
  have hcomm : ∀ {u v : G} (huN : u ∈ normalizer (A : Set G)) (hvN : v ∈ normalizer (A : Set G))
      {a b : C}, ψ ⟨u, huN⟩ = MulAut.conj a → ψ ⟨v, hvN⟩ = MulAut.conj b → u * v = v * u →
        a * b = b * a := by
    intro u v huN hvN a b hua hvb huv
    have h1 := congrArg ψ (Subtype.ext huv :
      (⟨u * v, mul_mem huN hvN⟩ : normalizer (A : Set G)) = ⟨v * u, mul_mem hvN huN⟩)
    rw [psi_mul huN hvN, psi_mul hvN huN, hua, hvb, ← map_mul, ← map_mul] at h1
    exact hinj h1
  have hWS : img ψ R₁ ≤ centralizer (img ψ Q₁ : Set C) := fun w hw =>
    mem_centralizer_iff.2 fun s hs => by
      obtain ⟨r, hr, hrN, hrw⟩ := mem_img.1 hw
      obtain ⟨v, hv, hvN, hvs⟩ := mem_img.1 hs
      exact hcomm hvN hrN hvs hrw (mem_centralizer_iff.1 (mem_inf.1 (hQ₁R v hv)).2 r hr).symm
  have hWM : img ψ R₁ ≤ centralizer (img ψ (A ⊓ centralizer (Q₁ : Set G)) : Set C) := fun w hw =>
    mem_centralizer_iff.2 fun m hm => by
      obtain ⟨r, hr, hrN, hrw⟩ := mem_img.1 hw
      obtain ⟨d, hd, hdN', hdm⟩ := mem_img.1 hm
      exact hcomm hdN' hrN hdm hrw (hdR d hd r hr)
  have hMS : img ψ (A ⊓ centralizer (Q₁ : Set G)) ≤ centralizer (img ψ Q₁ : Set C) := fun m hm =>
    mem_centralizer_iff.2 fun s hs => by
      obtain ⟨d, hd, hdN', hdm⟩ := mem_img.1 hm
      obtain ⟨v, hv, hvN, hvs⟩ := mem_img.1 hs
      exact hcomm hvN hdN' hvs hdm (mem_centralizer_iff.1 (mem_inf.1 hd).2 v hv)
  have hWzx : img ψ R₁ ≤ zx x' :=
    actsIn_zx hZC hψ h4 h32 h34 hsw hZA hR₁A (fun t ht ht1 htN x hx =>
      charTwo_of_reps hcover hchar (involution_of_conj hZC hψ hsw h32 ht htN hx).1
        ((involution_of_conj hZC hψ hsw h32 ht htN hx).2 ht1)) hr₀ hr₀1' hr₀N hx'
  have hW2 : IsPGroup 2 (img ψ R₁) := fun w =>
    ⟨1, Subtype.ext (by
      rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
      exact (hWzx w.2).2.2)⟩
  have hWbot : img ψ R₁ ≠ ⊥ := by
    intro h
    have h1 : x' ∈ img ψ R₁ := mem_img.2 ⟨r₀, hr₀, hr₀N, hx'⟩
    rw [h, mem_bot] at h1
    exact hx'1 hr₀1' h1
  set f := toC hZC hψ with hfdef
  have hfs := toC_surjective hZC hψ
  have hker : f.ker ≤ center ↥A := fun a ha => mem_center_iff.2 fun b =>
    Subtype.ext (mem_centralizer_iff.1 ((mem_ker_toC hZC hψ).1 ha) b b.2)
  have hkodd : Odd (Nat.card f.ker) := by rw [card_ker_toC]; exact hZA
  have hS : img ψ Q₁ = (Q₁.subgroupOf A).map f := img_eq_map hZC hψ hQ₁A
  have hM : img ψ (A ⊓ centralizer (Q₁ : Set G)) =
      (centralizer ((Q₁.subgroupOf A : Subgroup ↥A) : Set ↥A)).map f := by
    rw [img_eq_map hZC hψ inf_le_left]
    congr 1
    ext a
    rw [mem_subgroupOf, mem_inf, mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · rintro ⟨-, ha⟩ h hh
      exact Subtype.ext (ha h (mem_subgroupOf.1 hh))
    · intro ha
      refine ⟨a.2, fun v hv => ?_⟩
      exact congrArg Subtype.val (ha ⟨v, hQ₁A hv⟩ (mem_subgroupOf.2 hv))
  have hWM' : img ψ R₁ ≤ img ψ (A ⊓ centralizer (Q₁ : Set G)) := fun w hw => by
    rw [hM]
    refine mem_map_centralizer_of_pow f hfs hker hkodd _ (by rw [← hS]; exact hWS hw) (k := 1) ?_
    rw [pow_one, sq]
    exact (hWzx hw).2.2
  have hMN : centralizer (img ψ Q₁ : Set C) ≤
      normalizer (img ψ (A ⊓ centralizer (Q₁ : Set G)) : Set C) := by
    rw [hS, hM]
    exact le_normalizer_map_centralizer f hfs hker _
  set Mb := img ψ (A ⊓ centralizer (Q₁ : Set G)) with hMb
  have hWZ : img ψ R₁ ≤ Mb ⊓ centralizer (Mb : Set C) := le_inf hWM' hWM
  have hSZ : centralizer (img ψ Q₁ : Set C) ≤
      normalizer ((Mb ⊓ centralizer (Mb : Set C) : Subgroup C) : Set C) :=
    CFSG.LieType.Chevalley.EvenOddRadical.le_normalizer_of_conj_mem fun c hc z hz => by
      refine mem_inf.2 ⟨(mem_normalizer_iff.1 (hMN hc) z).1 (mem_inf.1 hz).1,
        mem_centralizer_iff.2 fun m hm => ?_⟩
      have hm' : c⁻¹ * m * c⁻¹⁻¹ ∈ Mb := (mem_normalizer_iff.1 (hMN (inv_mem hc)) m).1 hm
      rw [inv_inv] at hm'
      have h1 := mem_centralizer_iff.1 (mem_inf.1 hz).2 _ hm'
      calc m * (c * z * c⁻¹) = c * ((c⁻¹ * m * c) * z) * c⁻¹ := by group
        _ = c * (z * (c⁻¹ * m * c)) * c⁻¹ := by rw [h1]
        _ = c * z * c⁻¹ * m := by group
  have hZW : Mb ⊓ centralizer (Mb : Set C) ≤ normalizer (img ψ R₁ : Set C) :=
    CFSG.LieType.Chevalley.EvenOddRadical.le_normalizer_of_conj_mem fun z hz w hw => by
      have h1 := mem_centralizer_iff.1 (mem_inf.1 hz).2 w (hWM' hw)
      rw [show z * w * z⁻¹ = w by rw [← h1]; group]
      exact hw
  obtain ⟨R', hR'Z, -, hR'S, hR'2, hR'⟩ :=
    CFSG.LieType.Chevalley.EvenOddRadical.exists_invariant_isPGroup hSZ hWZ hZW hW2 hWbot
  have hR'C : R' ≤ centralizer (img ψ Q₁ : Set C) := hR'Z.trans (inf_le_left.trans hMS)
  exact hR' (hO2 _ hSodd R' hR'C
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hR'C).2 hR'S) hR'2)

theorem config814_of_pinned_of_oTwo_of_inf [Finite C] (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h34 : Asc08Lemma34) (D : ExcModel A) (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A)))
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) (hq2 : 2 < D.q)
    {reps : List C} (hcover : ClassesCover reps) (hTA : T ⊓ A = ⊥)
    (hRA : rightConjugate R g⁻¹ ⊓ A = ⊥)
    (hnc : ∀ (L₀ : Subgroup G) (n : ℕ), D.LeviType L₀ →
      Nonempty (↥L₀ ≃* SL(2, GaloisField 2 n)) → ∀ c : G, ¬ R.map (MulAut.conj c).toMonoidHom ≤ A)
    (hchar : ∀ y ∈ reps, CharTwo y)
    (hO2 : ∀ S : Subgroup C, Odd (Nat.card S) → ∀ N : Subgroup C,
      N ≤ centralizer (S : Set C) → (N.subgroupOf (centralizer (S : Set C))).Normal →
        IsPGroup 2 N → N = ⊥)
    {y₀ : C} (hT : ActsIn ψ T (zx y₀)) {Dl Ql Hl Ll : Subgroup C}
    (hLC : LeviClassData D (zx y₀) Dl Ql Hl Ll)
    (h3 : D.IsTrialityFour → Nat.Coprime 3 (Nat.card (center ↥A))) :
    Config814 D g R T (qLift ψ T Ql) := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hlevi' := hLC.levi
  have hLlp := commutator_eq_of_isQuasisimple hlevi'.quasisimple
  have hQodd := hlevi'.odd_Q
  have hlay := layerCentralizer_qLift hZC hψ h4 h32 h34 hc hT hlevi'
  refine
    { not_mem := hc.not_mem
      sylowR := hc.sylowR
      sylowT := hc.sylowT
      le_normalizer := hc.le_normalizer
      commute := commutator_eq_bot_iff_le_centralizer.2 hc.le_centralizer
      two_lt_q := hq2
      le := qLift_le
      ne_bot := ?_
      quasisimple := ?_
      odd_center := ?_
      levi := ?_
      sylow_inf := ?_
      le_sup := ?_
      inf_eq_bot := ?_
      not_le := not_le_normalizer_qLift_of_oTwo_of_inf hZC hψ h4 h32 h34 hc hOut hZA hcover hRA
        hchar hO2 hQodd
      noConj := ?_
      diag := ?_ }
  ·
    obtain ⟨⟨q₁, hq₁⟩, hq₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hlevi'.Q_ne_bot
    obtain ⟨w, hw, hwψ⟩ := exists_mem_qLift hψ h4 h32 h34 hc hT hlevi'.D_le hlevi'.D_perfect
      hlevi'.Q_le hq₁
    intro hbot
    have hw1 : w = 1 := by
      have := hw
      rw [hbot, mem_bot] at this
      exact this
    subst hw1
    apply hq₁1
    refine Subtype.ext (hinj ?_)
    rw [← hwψ]
    show ψ 1 = MulAut.conj (1 : C)
    rw [map_one, map_one]
  · rw [hlay]
    exact isQuasisimple_leviLift_inn hZC hψ hLlp hlevi'.quasisimple
  · rw [hlay]
    exact odd_card_center_leviLift hZC hψ hZA hLlp hlevi'.odd_center
  · rw [hlay]
    exact hLC.type _ ⟨quotEquiv_leviLift hZC hψ hLlp⟩
  · rw [hlay]
    refine isSylowOf_of_autFix hZC hψ hc.hyp hc.sylowR hLC.autFix qLift_le leviLift_le
      (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨w, hw, hwψ⟩ := exists_mem_qLift hψ h4 h32 h34 hc hT hlevi'.D_le hlevi'.D_perfect
        hlevi'.Q_le hy
      exact ⟨w, hw, _, hwψ⟩
    · obtain ⟨l, hl, hlψ⟩ := exists_mem_leviLift hψ (inn_le_range Ll) (commutator_inn hLlp)
        (conj_mem_inn hy)
      exact ⟨l, hl, _, hlψ⟩
  · rw [hlay]
    exact le_sup_leviLift_inn hψ h4 h32 h34 hc hZA hT hLlp hlevi'.Z_le
  · rw [hlay, eq_bot_iff, ← hTA]
    exact inf_le_inf_left T leviLift_le
  · intro n _ hiso c hle
    have hlev : D.LeviType (AS76b.layerCentralizer A (qLift ψ T Ql)) := by
      rw [hlay]
      exact hLC.type _ ⟨quotEquiv_leviLift hZC hψ hLlp⟩
    rw [hlay] at hle
    exact hnc _ n hlev hiso c (hle.trans leviLift_le)
  · intro hD hL3
    rw [hlay] at hL3 ⊢
    obtain ⟨y, hy, hy3, hyL⟩ :=
      hLC.diag hD (statedPSL_of_mulEquiv (quotEquiv_leviLift hZC hψ hLlp).symm hL3)
    exact exists_diag hZC hψ (h3 hD) qLift_le (fun w hw => exists_of_mem_qLift hw) hLlp hy hy3
      hyL

end Root

section Assembly

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem inf_eq_bot_rightConjugate_of_mem {T : Subgroup G} {a : G} (ha : a ∈ A)
    (h : T ⊓ A = ⊥) : rightConjugate T a ⊓ A = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxT, hxA⟩ := mem_inf.1 hx
  have h1 : a * x * a⁻¹ ∈ T ⊓ A :=
    mem_inf.2 ⟨(mem_rightConjugate_iff T a x).1 hxT, mul_mem (mul_mem ha hxA) (inv_mem ha)⟩
  rw [h, mem_bot] at h1
  rw [mem_bot]
  calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
    _ = 1 := by rw [h1]; group

omit [Finite G] in
theorem rightConjugate_mul_inv_inv_of_le {R : Subgroup G} (hR : R ≤ centralizer (A : Set G))
    {a : G} (ha : a ∈ A) (g : G) : rightConjugate R (g * a⁻¹)⁻¹ = rightConjugate R g⁻¹ := by
  have haR : rightConjugate R a = R := (rightConjugate_eq_self_iff R a).2
    (mem_normalizer_iff.2 fun r => by
      constructor
      · intro hr
        rw [mem_centralizer_iff.1 (hR hr) a ha, mul_inv_cancel_right]
        exact hr
      · intro hr
        have hc := mem_centralizer_iff.1 (hR hr) a ha
        have e : r = a⁻¹ * ((a * r * a⁻¹) * a) := by group
        rw [e, ← hc, inv_mul_cancel_left]
        exact hr)
  rw [mul_inv_rev, inv_inv, ← rightConjugate_mul, haR]

theorem exists_config814_of_torus_of_sec3 (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) (D : ExcModel A) (hZA : Odd (Nat.card (center A)))
    {C : Type} [Group C] [Finite C] (hZC : center C = ⊥) (e : rankTwoQuot A ≃* C)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) (q : ℕ) (hq : D.q = q)
    (hq2 : 2 ≤ q) {reps : List C} (hcover : ClassesCover reps) (hchar : ∀ x ∈ reps, CharTwo x)
    (hz2 : q = 2 → ∀ x ∈ reps, Nat.card (zx x) < 4 ∨ (Nat.card (zx x) ≤ 4 ∧
      ∃ w ∈ zx x, w ≠ 1 ∧ ∃ y ∈ reps, IsConj y w ∧ Nat.card (zx y) < 4))
    (hlevi : 2 < q → ∀ x ∈ reps, ∃ Dl Ql Hl Ll : Subgroup C,
      LeviClassData D (zx x) Dl Ql Hl Ll)
    (hO2 : 2 < q → ∀ S : Subgroup C, Odd (Nat.card S) → ∀ N : Subgroup C,
      N ≤ centralizer (S : Set C) → (N.subgroupOf (centralizer (S : Set C))).Normal →
        IsPGroup 2 N → N = ⊥)
    (h3 : D.IsTrialityFour → Nat.Coprime 3 (Nat.card (center ↥A)))
    {R T₀ : Subgroup G} {g₀ : G} (hc₀ : Sec3 A R T₀ g₀) (hTA₀ : T₀ ⊓ A = ⊥)
    (hRA₀ : rightConjugate R g₀⁻¹ ⊓ A = ⊥)
    (hnc : ∀ (L₀ : Subgroup G) (n : ℕ), D.LeviType L₀ →
      Nonempty (↥L₀ ≃* SL(2, GaloisField 2 n)) → ∀ c : G, ¬ R.map (MulAut.conj c).toMonoidHom ≤ A) :
    ∃ (g : G) (R T Q : Subgroup G), Config814 D g R T Q := by
  classical
  have hAp : commutator ↥A = ⊤ := hc₀.hyp.standard.1.1
  obtain ⟨ψ, hψ⟩ := exists_isActionHom (RankTwoHypIIY.autModel_mulAut hZC) hAp e
  have hcharT : ∀ {R' T' : Subgroup G} {g' : G}, Sec3 A R' T' g' → ∀ t ∈ T', t ≠ 1 →
      ∀ (htN : t ∈ normalizer (A : Set G)) (x : C), ψ ⟨t, htN⟩ = MulAut.conj x → CharTwo x :=
    fun hc' _ ht ht1 htN _ hx => charTwo_of_reps hcover hchar
      (involution_of_conj hZC hψ hc' h32 ht htN hx).1
      ((involution_of_conj hZC hψ hc' h32 ht htN hx).2 ht1)
  obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hc₀.T_ne_bot
  have ht₀1' : t₀ ≠ 1 := fun h => ht₀1 (Subtype.ext h)
  have ht₀N := hc₀.le_normalizer ht₀
  obtain ⟨x₀, hx₀⟩ := exists_conj_of_mem hψ hc₀ h32 h4 h34 ht₀ ht₀N
  obtain ⟨hx₀2, hx₀1⟩ := involution_of_conj hZC hψ hc₀ h32 ht₀ ht₀N hx₀
  obtain ⟨y₀, hy₀, hy₀x⟩ := hcover x₀ hx₀2 (hx₀1 ht₀1')
  obtain ⟨a₀, ha₀, hc, ht₁T, ht₁N, hψt₁⟩ := exists_pin hψ hc₀ ht₀ ht₀N hx₀ hy₀x
  have ht₁1 : a₀ * t₀ * a₀⁻¹ ≠ 1 := fun h => ht₀1' (by
    rw [show t₀ = a₀⁻¹ * (a₀ * t₀ * a₀⁻¹) * a₀ by group, h]; group)
  set T := rightConjugate T₀ a₀⁻¹ with hTdef
  set g := g₀ * a₀⁻¹ with hgdef
  have hTA : T ⊓ A = ⊥ := inf_eq_bot_rightConjugate_of_mem (inv_mem ha₀) hTA₀
  have hRA : rightConjugate R g⁻¹ ⊓ A = ⊥ := by
    rw [hgdef, rightConjugate_mul_inv_inv_of_le hc₀.sylowR.le ha₀]
    exact hRA₀
  have hT : ActsIn ψ T (zx y₀) :=
    actsIn_zx hZC hψ h4 h32 h34 hc hZA hTA (hcharT hc) ht₁T ht₁1 ht₁N hψt₁
  have hq2' : 2 < q := by
    have h1 := card_le_of_actsIn hZC hψ h4 h32 h34 hc hT
    have h2 : 4 ≤ Nat.card T := by rw [hc.card_eq]; exact hc.four_le
    by_contra hle
    rcases hz2 (by omega) y₀ hy₀ with h5 | ⟨h5, w, hw, hw1, y, hy, hyw, h6⟩
    · omega
    ·
      obtain ⟨s, hsT, hsN, hsw⟩ :=
        exists_mem_of_card_eq_of_actsIn hψ h4 h32 h34 hc hT (by omega) hw
      have hs1 : s ≠ 1 := by
        rintro rfl
        apply hw1
        refine RankTwoHypIIY.conj_injective_of_center_eq_bot hZC ?_
        rw [← hsw, map_one]
        exact map_one ψ
      obtain ⟨a, ha, hc', hsT', hsN', hsy⟩ := exists_pin hψ hc hsT hsN hsw hyw
      have has1 : a * s * a⁻¹ ≠ 1 := fun h => hs1 (by
        rw [show s = a⁻¹ * (a * s * a⁻¹) * a by group, h]; group)
      have hT' := actsIn_zx hZC hψ h4 h32 h34 hc' hZA
        (inf_eq_bot_rightConjugate_of_mem (inv_mem ha) hTA) (hcharT hc') hsT' has1 hsN' hsy
      have h7 := card_le_of_actsIn hZC hψ h4 h32 h34 hc' hT'
      have h8 : 4 ≤ Nat.card (rightConjugate T a⁻¹) := by rw [hc'.card_eq]; exact hc'.four_le
      omega
  obtain ⟨Dl, Ql, Hl, Ll, hLC⟩ := hlevi hq2' y₀ hy₀
  exact ⟨g, R, T, _, config814_of_pinned_of_oTwo_of_inf hZC hψ h4 h32 h34 D hc hZA hOut
    (by rw [hq]; exact hq2') hcover hTA hRA hnc hchar (hO2 hq2') hT hLC h3⟩

theorem exists_config814_of_torus (h32 : Lemma32) (h33 : Lemma33Three) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) (D : ExcModel A) (hA : Hyp31 A) (hZA : Odd (Nat.card (center A)))
    {C : Type} [Group C] [Finite C] (hZC : center C = ⊥) (e : rankTwoQuot A ≃* C)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) (q : ℕ) (hq : D.q = q)
    (hq2 : 2 ≤ q) {reps : List C} (hcover : ClassesCover reps)
    (hres : ∀ x ∈ reps, ResidualMem x) (hchar : ∀ x ∈ reps, CharTwo x)
    (hz2 : q = 2 → ∀ x ∈ reps, Nat.card (zx x) < 4 ∨ (Nat.card (zx x) ≤ 4 ∧
      ∃ w ∈ zx x, w ≠ 1 ∧ ∃ y ∈ reps, IsConj y w ∧ Nat.card (zx y) < 4))
    (hlevi : 2 < q → ∀ x ∈ reps, ∃ Dl Ql Hl Ll : Subgroup C,
      LeviClassData D (zx x) Dl Ql Hl Ll)
    (hO2 : 2 < q → ∀ S : Subgroup C, Odd (Nat.card S) → ∀ N : Subgroup C,
      N ≤ centralizer (S : Set C) → (N.subgroupOf (centralizer (S : Set C))).Normal →
        IsPGroup 2 N → N = ⊥)
    (h3 : D.IsTrialityFour → Nat.Coprime 3 (Nat.card (center ↥A))) :
    ∃ (g : G) (R T Q : Subgroup G), Config814 D g R T Q := by
  classical
  have hAp : commutator ↥A = ⊤ := hA.standard.1.1
  obtain ⟨ψ, hψ⟩ := exists_isActionHom (RankTwoHypIIY.autModel_mulAut hZC) hAp e
  obtain ⟨g₀, hg₀, R, T₀, hR, hT₀, -, -, hTR, -, -⟩ := section3Config_of h32 h33 h4 h34 G A hA
  have hc₀ : Sec3 A R T₀ g₀ := ⟨hA, hR, hg₀, hT₀, commutator_eq_bot_iff_le_centralizer.mp hTR⟩
  exact exists_config814_of_torus_of_sec3 h32 h4 h34 D hZA hZC e hOut q hq hq2 hcover hchar hz2
    hlevi hO2 h3 hc₀ (inf_eq_bot_of_reps hZC hψ h4 h32 h34 hc₀ hOut hZA hcover hres)
    (inf_eq_bot_of_reps hZC hψ h4 h32 h34 hc₀.swap hOut hZA hcover hres)
    (fun _ _ _ _ c => not_conj_le hZC hψ h4 h32 h34 hc₀ hOut hZA hcover hres c)

end Assembly

end CFSG.ComponentClassification.RankTwoExceptional.Exc
