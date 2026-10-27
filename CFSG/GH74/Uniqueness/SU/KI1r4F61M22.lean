module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public import CFSG.GH74.Uniqueness.SU.KI1r4F61Sp
public import CFSG.GH74.Uniqueness.SU.KI1r4F61Mod
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public import Certificates.Certificate2195
public import Certificates.Certificate2202
public import Certificates.Certificate2203
public import Certificates.Certificate3029
public import Certificates.Certificate3157
public import Certificates.Certificate5139
public import CFSG.Foundations
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Uniqueness.SU.KI1r3FamBender
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
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
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.MathieuOddCore
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Walter.J1
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open CFSG CFSG.Certificates CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.GH74.Uniqueness.SU.K.R3

theorem e4_search (Q : RawSchreierDatum 22) (hQ : ValidSchreier Q)
    (h : ((enumeration Q).any fun u => (enumeration Q).any fun v =>
      decide (u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * u = 1 ∧ v * v = 1 ∧ u * v = v * u)) = true) :
    ∃ u v : Equiv.Perm (Fin 22), u ∈ Q.originalSubgroup ∧ v ∈ Q.originalSubgroup ∧ u ≠ 1 ∧
      v ≠ 1 ∧ u ≠ v ∧ u * u = 1 ∧ v * v = 1 ∧ u * v = v * u := by
  obtain ⟨u, hu, h1⟩ := List.any_eq_true.1 h
  obtain ⟨v, hv, h2⟩ := List.any_eq_true.1 h1
  simp only [decide_eq_true_eq] at h2
  exact ⟨u, v, (mem_enumeration_iff Q hQ u).1 hu, (mem_enumeration_iff Q hQ v).1 hv, h2⟩

theorem m22_e4_1_check : ((enumeration m22OutCentQ1).any fun u => (enumeration m22OutCentQ1).any fun v =>
      decide (u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * u = 1 ∧ v * v = 1 ∧ u * v = v * u)) = true :=
  Certificates.certificate5139.1

theorem m22_e4_1 :
    ∃ u v : Equiv.Perm (Fin 22), u ∈ m22OutCentQ1.originalSubgroup ∧
    v ∈ m22OutCentQ1.originalSubgroup ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * u = 1 ∧ v * v = 1 ∧
      u * v = v * u :=
  e4_search m22OutCentQ1 m22_outer_cent1.1 m22_e4_1_check

theorem m22_e4_2_check : ((enumeration m22OutCentQ2).any fun u => (enumeration m22OutCentQ2).any fun v =>
      decide (u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * u = 1 ∧ v * v = 1 ∧ u * v = v * u)) = true :=
  Certificates.certificate5139.2

theorem m22_e4_2 :
    ∃ u v : Equiv.Perm (Fin 22), u ∈ m22OutCentQ2.originalSubgroup ∧
    v ∈ m22OutCentQ2.originalSubgroup ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * u = 1 ∧ v * v = 1 ∧
      u * v = v * u :=
  e4_search m22OutCentQ2 m22_outer_cent2.1 m22_e4_2_check

theorem exists_four_of_commuting {M : Type*} [Group M] [Finite M] (C : Subgroup M) {u v : M}
    (hu : u ∈ C) (hv : v ∈ C) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hu2 : u * u = 1)
    (hv2 : v * v = 1) (hc : u * v = v * u) :
    ∃ V : Subgroup M, V ≤ C ∧ Open.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  have hu2' : u ^ 2 = 1 := by rw [pow_two]; exact hu2
  have hv2' : v ^ 2 = 1 := by rw [pow_two]; exact hv2
  have hvu : v ∉ Subgroup.zpowers u := by
    intro hmem
    rcases eq_one_or_eq_of_mem_zpowers_sq hu2' hmem with h | h
    · exact hv1 h
    · exact huv h.symm
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := u) (y := v)
    hu2' hv2' hu1 hvu hc
  refine ⟨Subgroup.zpowers u ⊔ Subgroup.zpowers v, sup_le (Subgroup.zpowers_le.2 hu)
    (Subgroup.zpowers_le.2 hv), hel, by rw [hcard]; norm_num⟩

theorem m22_four_reps :
    ∀ r ∈ [m22OutRep1, m22OutRep2], ∃ V : Subgroup (Equiv.Perm (Fin 22)),
    V ≤ centralizerIn m22Certificate.originalSubgroup r ∧ Open.IsElemAbelian 2 V ∧
      Nat.card V = 4 := by
  intro r hr
  obtain ⟨-, -, hK1, -, -⟩ := m22_out_rep_data1
  obtain ⟨-, -, hK2, -, -⟩ := m22_out_rep_data2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · obtain ⟨u, v, hu, hv, hu1, hv1, huv, hu2, hv2, hc⟩ := m22_e4_1
    exact exists_four_of_commuting _ (hK1 hu) (hK1 hv) hu1 hv1 huv hu2 hv2 hc
  · obtain ⟨u, v, hu, hv, hu1, hv1, huv, hu2, hv2, hc⟩ := m22_e4_2
    exact exists_four_of_commuting _ (hK2 hu) (hK2 hv) hu1 hv1 huv hu2 hv2 hc

theorem m22_outer_four :
    ∀ u, m22Delta⁻¹ * u ∈ NativeSporadic.M22 → orderOf u = 2 →
    ∃ V : Subgroup (Equiv.Perm (Fin 22)), V ≤ centralizerIn NativeSporadic.M22 u ∧
      Open.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, -, -⟩ := m22_outer_cover
  obtain ⟨hr1, hro1, -, -, -⟩ := m22_out_rep_data1
  obtain ⟨hr2, hro2, -, -, -⟩ := m22_out_rep_data2
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22OutReps_eq] at hok
  have hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
      m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
    rw [m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK hn m22Certificate hQ (pairTables_spec hn hA hB)
    m22Delta hg₀ (by norm_num) [m22OutRep1, m22OutRep2] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨hr1, hro1⟩
      · exact ⟨hr2, hro2⟩) 2000 hok
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u hu ho
  obtain ⟨V, hV, hVel, hVc⟩ := m22_four_reps r hr
  refine ⟨V.map (MulAut.conj c).toMonoidHom, ?_, ?_, ?_⟩
  · rw [centralizerIn_conj _ hc]
    exact Subgroup.map_mono hV
  · exact isElemAbelian_map_conj hVel c
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hVc

theorem fixed_four_of_cent {M : Type*} [Group M] {N : Subgroup M} {u : M} {α : MulAut N}
    (hαg : ∀ h : N, (α h : M) = u * h * u⁻¹) (V : Subgroup M) (hV : V ≤ centralizerIn N u)
    (hel : Open.IsElemAbelian 2 V) (hcard : Nat.card V = 4) :
    ∃ W : Subgroup N, (∀ w ∈ W, α w = w) ∧ Open.IsElemAbelian 2 W ∧ Nat.card W = 4 := by
  have hVN : V ≤ N := fun v hv => (Subgroup.mem_inf.1 (hV hv)).1
  have hmap : (V.subgroupOf N).map N.subtype = V := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hVN]
  refine ⟨V.subgroupOf N, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : (w : M) ∈ V := hw
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hV hw')).2
    apply Subtype.ext
    rw [hαg]
    calc u * (w : M) * u⁻¹ = (w : M) * u * u⁻¹ := by rw [← hc]
      _ = w := by group
  · rw [SU1.isElemAbelian_iff] at hel ⊢
    obtain ⟨hc, hp⟩ := hel
    refine ⟨fun a ha b hb => Subtype.ext (hc a ha b hb), fun a ha => Subtype.ext ?_⟩
    simpa using hp a ha
  · rw [← Subgroup.card_map_of_injective N.subtype_injective (K := V.subgroupOf N), hmap]
    exact hcard

theorem strictFix_M22 :
    StrictFix ↥NativeSporadic.M22 := by
  have : IsSimpleGroup NativeSporadic.M22 := fam_m22_simplicity.2.2
  have hnab : ∃ a b : NativeSporadic.M22, a * b ≠ b * a := ⟨_, _, m22_gens_not_comm⟩
  intro α hα
  by_cases hin : α ∈ inner NativeSporadic.M22
  · obtain ⟨g, rfl⟩ := hin
    exact four_group_fixed_of_inner hnab g hα
  · have hα2 : α * α = 1 := by rw [← pow_two]; exact hα
    obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer NativeSporadic.M22 m22Delta
      m22_delta_normalizes m22_delta_sq m22_center_eq_bot' m22_delta_outer m22_mulAut_card α hin
    set u := g * m22Delta with hu
    have hδ' := inv_conj_mem NativeSporadic.M22 m22_delta_normalizes m22_delta_sq
    have huN : m22Delta⁻¹ * u ∈ NativeSporadic.M22 := by
      simpa [u, mul_assoc] using hδ' g hg
    have hu2N : u * u ∈ NativeSporadic.M22 := by
      have : u * u = g * (m22Delta * g * m22Delta⁻¹) * (m22Delta * m22Delta) := by
        simp only [u]
        group
      rw [this]
      exact NativeSporadic.M22.mul_mem (NativeSporadic.M22.mul_mem hg
        (m22_delta_normalizes g hg)) m22_delta_sq
    have hu2 : u * u = 1 := by
      have hc : (⟨u * u, hu2N⟩ : NativeSporadic.M22) ∈ Subgroup.center NativeSporadic.M22 := by
        rw [Subgroup.mem_center_iff]
        intro z
        have hz := congrArg (fun φ : MulAut NativeSporadic.M22 => (φ z : Equiv.Perm (Fin 22))) hα2
        simp only [MulAut.mul_apply, MulAut.one_apply] at hz
        rw [hαg, hαg] at hz
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        calc (z : Equiv.Perm (Fin 22)) * (u * u) =
              u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
          _ = u * u * z := by group
      rw [m22_center_eq_bot', Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc
    have hu1 : u ≠ 1 := by
      intro h1
      apply hin
      refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
      rw [hαg, h1]
      simp
    have ho : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
    obtain ⟨V, hV, hVel, hVc⟩ := m22_outer_four u huN ho
    exact fixed_four_of_cent hαg V hV hVel hVc

theorem strictSp_M22 :
    StrictFamSp .M22 := by
  intro K _ _ ⟨e⟩
  exact StrictFix.of_mulEquiv (K := NativeSporadic.M22) (e.symm : NativeSporadic.M22 ≃* K)
    strictFix_M22

end CFSG.GH74.Uniqueness.SU.K.R4
