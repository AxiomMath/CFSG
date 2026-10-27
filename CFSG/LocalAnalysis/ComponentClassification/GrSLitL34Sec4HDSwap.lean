module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma412Inner
public import CFSG.GroupTheory.InvolutionFixedCentralSylow
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Ly
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyCert
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidtBasic
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEndPair
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSporadic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Walter.Bender1970.S3.Setup
public import CFSG.Walter.J1
public import CFSG.Walter.JRFacts
public import Certificates.Certificate3085Base
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8052

public section

namespace CFSG.ComponentClassification.GrSLit.HeDiag

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem commutator_mem_of_mem_sup {M J A B : Subgroup X} (hJM : J ≤ M) (hAM : A ≤ M)
    (hBM : B ≤ M) (hA : ∀ x ∈ A, ∀ j ∈ J, ⁅j, x⁆ ∈ oddIn M)
    (hB : ∀ x ∈ B, ∀ j ∈ J, ⁅j, x⁆ ∈ oddIn M) {x : X} (hx : x ∈ A ⊔ B ⊔ oddIn M) :
    x ∈ M ∧ ∀ j ∈ J, ⁅j, x⁆ ∈ oddIn M := by
  have hOMN : M ≤ normalizer ((oddIn M : Subgroup X) : Set X) := GrS4.self_le_normalizer_oddIn M
  let Z : Subgroup X :=
    { carrier := {x | x ∈ M ∧ ∀ j ∈ J, ⁅j, x⁆ ∈ oddIn M}
      one_mem' := ⟨one_mem _, fun j _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
      mul_mem' := by
        rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
        refine ⟨mul_mem hxM hyM, fun j hj => ?_⟩
        rw [show ⁅j, x * y⁆ = ⁅j, x⁆ * (x * ⁅j, y⁆ * x⁻¹) by
          simp only [commutatorElement_def]; group]
        exact mul_mem (hx j hj) ((mem_normalizer_iff.mp (hOMN hxM) _).mp (hy j hj))
      inv_mem' := by
        rintro x ⟨hxM, hx⟩
        refine ⟨inv_mem hxM, fun j hj => ?_⟩
        rw [show ⁅j, x⁻¹⁆ = x⁻¹ * ⁅j, x⁆⁻¹ * x⁻¹⁻¹ by simp only [commutatorElement_def]; group]
        exact (mem_normalizer_iff.mp (hOMN (inv_mem hxM)) _).mp (inv_mem (hx j hj)) }
  have hOZ : oddIn M ≤ Z := fun o ho => ⟨map_subtype_le _ ho, fun j hj => by
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp (hOMN (hJM hj)) o).mp ho) (inv_mem ho)⟩
  exact (sup_le (sup_le (fun x hx => ⟨hAM hx, hA x hx⟩) (fun x hx => ⟨hBM hx, hB x hx⟩)) hOZ) hx

theorem eq_or_eq_of_isPComponent {M K K₂ : Subgroup X} {a : X} (ha : orderOf a = 2)
    (haM : a ∈ M) (hKM : K ≤ M) (hKc : IsPComponent 2 (K.subgroupOf M))
    (hno : ∀ r : X, orderOf r = 2 → a * r = r * a → r ∈ M → r ∈ normalizer (K : Set X) →
      r ∈ normalizer (conjugate K a : Set X) → (∀ k ∈ K, k⁻¹ * r⁻¹ * k * r ∈ oddIn M) →
      (∀ k ∈ conjugate K a, k⁻¹ * r⁻¹ * k * r ∈ oddIn M) → False)
    (hK₂M : K₂ ≤ M) (hK₂c : IsPComponent 2 (K₂.subgroupOf M)) : K₂ = K ∨ K₂ = conjugate K a := by
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  set K' := conjugate K a with hK'def
  set K₃ := conjugate K₂ a with hK₃def
  have hK'M : K' ≤ M := conjugate_le_of_mem hKM haM
  have hK'c : IsPComponent 2 (K'.subgroupOf M) := isPComponent_conjugate_subgroupOf haM hKc
  have hK₃M : K₃ ≤ M := conjugate_le_of_mem hK₂M haM
  have hK₃c : IsPComponent 2 (K₃.subgroupOf M) := isPComponent_conjugate_subgroupOf haM hK₂c
  have hcc : ∀ H : Subgroup X, conjugate (conjugate H a) a = H := fun H => by
    rw [conjugate_conjugate, haa, conjugate_one]
  have h3 : K₃ ≠ K := fun h => h2 (by rw [← hcc K₂, ← hK₃def, h])
  have h4 : K₃ ≠ K' := fun h => h1 (by rw [← hcc K₂, ← hK₃def, h, hK'def, hcc])
  have hcomm : ∀ {A B : Subgroup X}, A ≤ M → IsPComponent 2 (A.subgroupOf M) → B ≤ M →
      IsPComponent 2 (B.subgroupOf M) → A ≠ B →
      (∀ x ∈ B, ∀ j ∈ A, ⁅j, x⁆ ∈ oddIn M) ∧ B ≤ normalizer (A : Set X) := by
    intro A B hAM hA hBM hB hAB
    obtain ⟨hc, hN⟩ := GrS5.commutator_le_of_ne hAM hBM hA hB hAB
    exact ⟨fun x hx j hj => hc (commutator_mem_commutator hj hx), hN⟩
  set P := K₂ ⊔ K₃ ⊔ oddIn M with hP
  have hPK := fun {x} (hx : x ∈ P) => commutator_mem_of_mem_sup hKM hK₂M hK₃M
    (hcomm hKM hKc hK₂M hK₂c (Ne.symm h1)).1 (hcomm hKM hKc hK₃M hK₃c (Ne.symm h3)).1 hx
  have hPK' := fun {x} (hx : x ∈ P) => commutator_mem_of_mem_sup hK'M hK₂M hK₃M
    (hcomm hK'M hK'c hK₂M hK₂c (Ne.symm h2)).1 (hcomm hK'M hK'c hK₃M hK₃c (Ne.symm h4)).1 hx
  have hPNK : P ≤ normalizer (K : Set X) := sup_le (sup_le
    (hcomm hKM hKc hK₂M hK₂c (Ne.symm h1)).2 (hcomm hKM hKc hK₃M hK₃c (Ne.symm h3)).2)
    (GrS4.oddIn_le_normalizer_of_isPComponent hKM hKc)
  have hPNK' : P ≤ normalizer (K' : Set X) := sup_le (sup_le
    (hcomm hK'M hK'c hK₂M hK₂c (Ne.symm h2)).2 (hcomm hK'M hK'c hK₃M hK₃c (Ne.symm h4)).2)
    (GrS4.oddIn_le_normalizer_of_isPComponent hK'M hK'c)
  have haP : ∀ x ∈ P, a * x * a⁻¹ ∈ P := by
    have hle : P ≤ P.comap (MulAut.conj a).toMonoidHom := by
      refine sup_le (sup_le (fun x hx => ?_) (fun x hx => ?_)) (fun x hx => ?_)
      · refine mem_sup_left (mem_sup_right ?_)
        show a * x * a⁻¹ ∈ conjugate K₂ a
        rw [mem_conjugate_iff, hai, show a * (a * x * a) * a = (a * a) * x * (a * a) by group,
          haa, one_mul, mul_one]
        exact hx
      · refine mem_sup_left (mem_sup_left ?_)
        exact mem_conjugate_iff.mp hx
      · exact mem_sup_right ((mem_normalizer_iff.mp (GrS4.self_le_normalizer_oddIn M haM) x).mp hx)
    exact fun x hx => hle hx
  have haNP : a ∈ normalizer (P : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨haP x, fun hx => ?_⟩
    have h5 := haP _ hx
    rwa [hai, show a * (a * x * a) * a = (a * a) * x * (a * a) by group, haa, one_mul,
      mul_one] at h5
  have hPeven : Even (Nat.card P) := by
    have h5 := GrS4.not_odd_card_of_isPComponent hK₂M hK₂c
    rw [Nat.not_odd_iff_even] at h5
    exact (even_iff_two_dvd.mp h5).trans (card_dvd_of_le (le_sup_left.trans le_sup_left)) |>
      even_iff_two_dvd.mpr
  have hza : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨r, hrP, hr2, hra⟩ := CFSG.GroupTheory.exists_involution_commute_of_isPGroup_le_normalizer
    hza (zpowers_le.mpr haNP) hPeven
  have hrM : r ∈ M := (hPK hrP).1
  refine hno r hr2 (hra a (mem_zpowers a)) hrM (hPNK hrP) (hPNK' hrP) (fun k hk => ?_)
    (fun k hk => ?_)
  · have h5 := (hPK (inv_mem hrP)).2 _ (inv_mem hk)
    rwa [commutatorElement_def, inv_inv, inv_inv] at h5
  · have h5 := (hPK' (inv_mem hrP)).2 _ (inv_mem hk)
    rwa [commutatorElement_def, inv_inv, inv_inv] at h5

omit [Finite X] in
theorem mem_normalizer_iff_conjugate_eq {K : Subgroup X} {x : X} :
    x ∈ normalizer (K : Set X) ↔ conjugate K x = K :=
  ⟨conjugate_eq_of_mem_normalizer, fun h => by
    have h1 : x⁻¹ ∈ normalizer (K : Set X) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
    simpa using inv_mem h1⟩

omit [Finite X] in
theorem conj_not_mem_normalizer {M K : Subgroup X} {a : X} (ha : orderOf a = 2)
    (hKM : K ≤ M) (hKc : IsPComponent 2 (K.subgroupOf M)) (hKa : conjugate K a ≠ K)
    (honly : ∀ K₂ : Subgroup X, K₂ ≤ M → IsPComponent 2 (K₂.subgroupOf M) →
      K₂ = K ∨ K₂ = conjugate K a) {m : X} (hm : m ∈ M) :
    m⁻¹ * a * m ∉ normalizer (K : Set X) := by
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  intro h
  have hK₂M : conjugate K m⁻¹ ≤ M := conjugate_le_of_mem hKM (inv_mem hm)
  have hK₂c := isPComponent_conjugate_subgroupOf (inv_mem hm) hKc
  have haN : a ∈ normalizer ((conjugate K m⁻¹ : Subgroup X) : Set X) := by
    rw [mem_normalizer_iff_conjugate_eq, conjugate_conjugate,
      show m⁻¹ * a = (m⁻¹ * a * m) * m⁻¹ by group, ← conjugate_conjugate,
      conjugate_eq_of_mem_normalizer h]
  rcases honly _ hK₂M hK₂c with h1 | h1
  · rw [h1] at haN
    exact hKa (conjugate_eq_of_mem_normalizer haN)
  · rw [h1] at haN
    have h2 := conjugate_eq_of_mem_normalizer haN
    rw [conjugate_conjugate, haa, conjugate_one] at h2
    exact hKa h2.symm

omit [Finite X] in
theorem relIndex_inf_normalizer {M K T : Subgroup X} {a : X} (ha : orderOf a = 2)
    (hKM : K ≤ M) (hKc : IsPComponent 2 (K.subgroupOf M)) (hKa : conjugate K a ≠ K)
    (honly : ∀ K₂ : Subgroup X, K₂ ≤ M → IsPComponent 2 (K₂.subgroupOf M) →
      K₂ = K ∨ K₂ = conjugate K a) (hTM : T ≤ M) (haT : a ∈ T) :
    (T ⊓ normalizer (K : Set X)).relIndex T = 2 := by
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  rw [relIndex_eq_two_iff]
  refine ⟨a, haT, fun b hb => ?_⟩
  have hb2 := honly _ (conjugate_le_of_mem hKM (hTM hb)) (isPComponent_conjugate_subgroupOf
    (hTM hb) hKc)
  have hba : conjugate K (b * a) = conjugate (conjugate K b) a := (conjugate_conjugate K b a).symm
  simp only [mem_inf, hb, mul_mem hb haT, true_and, mem_normalizer_iff_conjugate_eq, hba]
  rcases hb2 with h | h
  · rw [h]
    exact Or.inr ⟨rfl, hKa⟩
  · rw [h, conjugate_conjugate, haa, conjugate_one]
    exact Or.inl ⟨rfl, hKa⟩

theorem inf_coreActionKernel_eq_bot {M K T : Subgroup X} {a : X} (haM : a ∈ M) (hKM : K ≤ M)
    (hKc : IsPComponent 2 (K.subgroupOf M))
    (honly : ∀ K₂ : Subgroup X, K₂ ≤ M → IsPComponent 2 (K₂.subgroupOf M) →
      K₂ = K ∨ K₂ = conjugate K a)
    (hno : ∀ r : X, orderOf r = 2 → a * r = r * a → r ∈ M → r ∈ normalizer (K : Set X) →
      r ∈ normalizer (conjugate K a : Set X) → (∀ k ∈ K, k⁻¹ * r⁻¹ * k * r ∈ oddIn M) →
      (∀ k ∈ conjugate K a, k⁻¹ * r⁻¹ * k * r ∈ oddIn M) → False)
    (hT2 : IsPGroup 2 T) (hTM : T ≤ M) (haT : a ∈ T) :
    T ⊓ coreActionKernel K ⊓ coreActionKernel (conjugate K a) = ⊥ := by
  have hK'M : conjugate K a ≤ M := conjugate_le_of_mem hKM haM
  have hK'c := isPComponent_conjugate_subgroupOf haM hKc
  have hinv : ∀ {x : X} (t : X), t ∈ T → x ∈ coreActionKernel K ⊓ coreActionKernel (conjugate K a)
      → t * x * t⁻¹ ∈ coreActionKernel K ⊓ coreActionKernel (conjugate K a) := by
    intro x t ht hx
    obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
    have hmem : ∀ J : Subgroup X, J = K ∨ J = conjugate K a → x ∈ coreActionKernel J := by
      rintro J (rfl | rfl)
      · exact hx1
      · exact hx2
    refine mem_inf.mpr ⟨FooteLit.mem_coreActionKernel_conjugate_iff.mp ?_,
      FooteLit.mem_coreActionKernel_conjugate_iff.mp ?_⟩
    · exact hmem _ (honly _ (conjugate_le_of_mem hKM (hTM ht))
        (isPComponent_conjugate_subgroupOf (hTM ht) hKc))
    · exact hmem _ (honly _ (conjugate_le_of_mem hK'M (hTM ht))
        (isPComponent_conjugate_subgroupOf (hTM ht) hK'c))
  by_contra hne
  have hTQ : T ≤ normalizer ((T ⊓ coreActionKernel K ⊓ coreActionKernel (conjugate K a) :
      Subgroup X) : Set X) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [inf_assoc] at hx ⊢
      obtain ⟨hxT, hxk⟩ := mem_inf.mp hx
      exact mem_inf.mpr ⟨mul_mem (mul_mem ht hxT) (inv_mem ht), hinv t ht hxk⟩
    · intro hx
      rw [inf_assoc] at hx ⊢
      obtain ⟨hxT, hxk⟩ := mem_inf.mp hx
      have h1 := hinv t⁻¹ (inv_mem ht) hxk
      rw [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at h1
      refine mem_inf.mpr ⟨?_, h1⟩
      have h2 := mul_mem (mul_mem (inv_mem ht) hxT) ht
      rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at h2
  obtain ⟨r, hrQ, hr2, hrc⟩ := exists_central_involution hT2 (inf_le_left.trans inf_le_left) hTQ hne
  obtain ⟨⟨hrT, hrK⟩, hrK'⟩ := mem_inf.mp hrQ
  refine hno r hr2 (hrc a haT) (hTM hrT) (mem_coreActionKernel.mp hrK).1
    (mem_coreActionKernel.mp hrK').1 (fun k hk => ?_) (fun k hk => ?_)
  · exact GSLit.map_pPrimeCore_le_of_isPComponent hKM hKc ((mem_coreActionKernel.mp hrK).2 k hk)
  · exact GSLit.map_pPrimeCore_le_of_isPComponent hK'M hK'c
      ((mem_coreActionKernel.mp hrK').2 k hk)

end CFSG.ComponentClassification.GrSLit.HeDiag
