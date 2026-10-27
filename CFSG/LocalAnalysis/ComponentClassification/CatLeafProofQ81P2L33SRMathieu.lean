module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRBase
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Card
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import Certificates.Certificate2191
public import Certificates.Certificate2192
public import Certificates.Certificate2193
public import Certificates.Certificate2194
public import Certificates.Certificate2195
public import Certificates.Certificate2196
public import Certificates.Certificate2197
public import Certificates.Certificate2198
public import Certificates.Certificate2199
public import Certificates.Certificate2200
public import Certificates.Certificate2201
public import Certificates.Certificate2202
public import Certificates.Certificate2203
public import Certificates.Certificate2204
public import Certificates.Certificate2205
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3046
public import Certificates.Certificate3086
public import Certificates.Certificate3120
public import Certificates.Certificate3157
public import CFSG.Sporadic.Schreier.M23Check
public import CFSG.Sporadic.Schreier.M24Check
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Leaf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC311a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitCor441
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Count
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Fbar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitProperComplete
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import Certificates.Certificate3085Base

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
open CFSG.ComponentClassification.OuterAutomorphisms

section Checked

variable {n : ℕ}

theorem not_isPGroup_centralizerIn_of_repsOK (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (g₀ : Equiv.Perm (Fin n))
    (hg₀ : ∀ h ∈ Q.originalSubgroup, g₀⁻¹ * h * g₀ ∈ Q.originalSubgroup)
    (reps : List (Equiv.Perm (Fin n)))
    (hreps : ∀ r ∈ reps, g₀⁻¹ * r ∈ Q.originalSubgroup ∧ orderOf r = 2) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) (reps.map toTable) cap = true)
    (hK : ∀ r ∈ reps, ¬ IsPGroup 2 ↥(centralizerIn Q.originalSubgroup r)) :
    ∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = 2 →
      ¬ IsPGroup 2 ↥(centralizerIn Q.originalSubgroup u) := by
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK hn Q hQ hg g₀ hg₀ (by norm_num) reps hreps cap hok
  intro u hu ho
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u hu ho
  exact not_isPGroup_inf_centralizer_conj hc (hK r hr)

end Checked

section Model

variable {M : Type} [Group M]

theorem not_isPGroup_fixedPoints_of_mem_inner (N : Subgroup M) (hZ : center N = ⊥)
    (hC : ∀ u ∈ N, orderOf u = 2 → ¬ IsPGroup 2 ↥(centralizerIn N u)) {α : MulAut N}
    (hα : α ∈ inner N) (ho : orderOf α = 2) : ¬ IsPGroup 2 ↥(fixedPoints α) := by
  obtain ⟨t, rfl⟩ := hα
  refine not_isPGroup_fixedPoints_conj hZ (fun t ht hP => ?_) ho
  apply hC t t.2 (by rw [Subgroup.orderOf_coe]; exact ht)
  rw [← map_centralizer_subtype]
  exact hP.of_equiv (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective)

theorem not_isPGroup_fixedPoints_of_outer (N : Subgroup M) [Finite N] (δ : M)
    (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N) (hcenter : center N = ⊥)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut N) ≤ 2 * Nat.card N)
    (hw : ∀ u, δ⁻¹ * u ∈ N → orderOf u = 2 → ¬ IsPGroup 2 ↥(centralizerIn N u))
    {α : MulAut N} (hα2 : α * α = 1) (hα : α ∉ inner N) : ¬ IsPGroup 2 ↥(fixedPoints α) := by
  have hδ' := inv_conj_mem N hδ hδ2
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer N δ hδ hδ2 hcenter houter hcard α hα
  set u := g * δ
  have hu : δ⁻¹ * u ∈ N := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ N := by
    have : u * u = g * (δ * g * δ⁻¹) * (δ * δ) := by simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem hg (hδ g hg)) hδ2
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : N) ∈ center N := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut N => (φ z : M)) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : M) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hαg, h1]
    simp
  have ho : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  exact not_isPGroup_fixedPoints_of_conj hαg (hw u hu ho)

theorem congr_not_mem_inner {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) {α : MulAut G}
    (hα : α ∉ inner G) : MulAut.congr ψ α ∉ inner H := by
  rw [← inner_map_congr ψ]
  rintro ⟨β, hβ, hβα⟩
  exact hα ((MulAut.congr ψ).injective hβα ▸ hβ)

theorem mul_self_eq_one_of_orderOf {G : Type*} [Group G] {α : G} (hα : orderOf α = 2) :
    α * α = 1 := by
  have h := pow_orderOf_eq_one α
  rwa [hα, pow_two] at h

end Model

theorem m11_centralizerIn_not_isPGroup :
    ∀ u ∈ NativeSporadic.M11, orderOf u = 2 →
      ¬ IsPGroup 2 ↥(centralizerIn NativeSporadic.M11 u) := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m11Certificate := m11Certificate_check.1
  obtain ⟨hok, -, -⟩ := m11_oddcore_cover
  obtain ⟨hr, hro, hK, hKc, -⟩ := m11_rep_data
  have hA : m11gA ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11a.2
  have hB : m11gB ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11b.2
  rw [← m11Certificate_originalSubgroup]
  intro u hu ho
  refine not_isPGroup_centralizerIn_of_repsOK hn m11Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) m11InvReps ?_ 400 hok ?_ u (by simpa using hu) ho
  · intro r hr'
    simp only [m11InvReps, m11InvRepWords, List.map_cons, List.map_nil,
      List.mem_singleton] at hr'
    subst hr'
    exact ⟨by simpa using hr, hro⟩
  · intro r hr'
    simp only [m11InvReps, m11InvRepWords, List.map_cons, List.map_nil,
      List.mem_singleton] at hr'
    subst hr'
    exact not_isPGroup_of_le hK (not_isPGroup_of_three_dvd (by rw [hKc]; norm_num))

theorem sporNoTwoFix_M11 :
    SporNoTwoFix .M11 := by
  refine sporNoTwoFix_of_mulEquiv (P := ↥NativeSporadic.M11) (MulEquiv.refl _) fun α hα => ?_
  have htop : inner NativeSporadic.M11 = ⊤ :=
    inner_eq_top_of_card_le m11_center_eq_bot' m11_mulAut_card
  exact not_isPGroup_fixedPoints_of_mem_inner _ m11_center_eq_bot'
    m11_centralizerIn_not_isPGroup (htop ▸ Subgroup.mem_top α) hα

theorem m12_centralizerIn_not_isPGroup :
    ∀ u ∈ NativeSporadic.M12, orderOf u = 2 →
      ¬ IsPGroup 2 ↥(centralizerIn NativeSporadic.M12 u) := by
  intro u hu ho
  apply not_isPGroup_of_three_dvd
  rcases m12_card_centralizerIn_involution hu ho with h | h <;> rw [h] <;> norm_num

theorem m12D_sigma_centralizerIn_not_isPGroup :
    ∀ u, m12Sigma⁻¹ * u ∈ m12D.originalSubgroup → orderOf u = 2 →
      ¬ IsPGroup 2 ↥(centralizerIn m12D.originalSubgroup u) := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, hord⟩ := m12_sigma_cover
  obtain ⟨hc, ho, hcomm, -⟩ := m12_sigma_cent
  have hA : m12A1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  have hB : m12B1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  have hK : m12SigmaCentQ.originalSubgroup ≤ centralizerIn m12D.originalSubgroup m12Sigma := by
    rw [m12SigmaCentQ, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m12_gens_memD w) hcomm
  have hKc : Nat.card m12SigmaCentQ.originalSubgroup = 120 := by
    rw [← m12SigmaCentQ.orderCertificate_eq_card hc, ho]
  refine not_isPGroup_centralizerIn_of_repsOK hn m12D m12D_check.1 (pairTables_spec hn hA hB)
    m12Sigma (inv_conj_mem _ m12D_sigma_normalizes m12D_sigma_sq) [m12Sigma] ?_ 1000 hok ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨by simp, (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hord⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact not_isPGroup_of_le hK (not_isPGroup_of_three_dvd (by rw [hKc]; norm_num))

theorem sporNoTwoFix_M12 :
    SporNoTwoFix .M12 := by
  refine sporNoTwoFix_of_mulEquiv (P := ↥NativeSporadic.M12) (MulEquiv.refl _) fun α hα => ?_
  by_cases hin : α ∈ inner NativeSporadic.M12
  · exact not_isPGroup_fixedPoints_of_mem_inner _ m12_center_eq_bot'
      m12_centralizerIn_not_isPGroup hin hα
  · have hα2 := mul_self_eq_one_of_orderOf hα
    have hα2' : MulAut.congr m12EquivD α * MulAut.congr m12EquivD α = 1 := by
      rw [← map_mul, hα2, map_one]
    intro hP
    exact not_isPGroup_fixedPoints_of_outer _ m12Sigma m12D_sigma_normalizes m12D_sigma_sq
      m12D_center m12D_sigma_outer m12D_mulAut_card m12D_sigma_centralizerIn_not_isPGroup
      hα2' (congr_not_mem_inner m12EquivD hin) (isPGroup_fixedPoints_map m12EquivD α hP)

theorem m22_centralizerIn_not_isPGroup :
    ∀ u ∈ NativeSporadic.M22, orderOf u = 2 →
      ¬ IsPGroup 2 ↥(centralizerIn NativeSporadic.M22 u) := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, -, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  refine not_isPGroup_centralizerIn_of_repsOK hn m22Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) [m22Rep1] ?_ 2000 hok ?_ u (by simpa using hu) ho
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨by simpa using hr1, hro1⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact not_isPGroup_of_le hK1 (not_isPGroup_of_three_dvd (by rw [hKc1]; norm_num))

theorem m22_outer_centralizerIn_not_isPGroup :
    ∀ u, m22Delta⁻¹ * u ∈ NativeSporadic.M22 → orderOf u = 2 →
      ¬ IsPGroup 2 ↥(centralizerIn NativeSporadic.M22 u) := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, -, -⟩ := m22_outer_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_out_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m22_out_rep_data2
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22OutReps_eq] at hok
  have hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
      m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
    rw [m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq
  rw [← m22Certificate_originalSubgroup]
  refine not_isPGroup_centralizerIn_of_repsOK hn m22Certificate hQ (pairTables_spec hn hA hB)
    m22Delta hg₀ [m22OutRep1, m22OutRep2] ?_ 2000 hok ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨hr1, hro1⟩
    · exact ⟨hr2, hro2⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact not_isPGroup_of_le hK1
        (not_isPGroup_of_prime_dvd Nat.prime_five (by norm_num) (by rw [hKc1]; norm_num))
    · exact not_isPGroup_of_le hK2 (not_isPGroup_of_three_dvd (by rw [hKc2]; norm_num))

theorem sporNoTwoFix_M22 :
    SporNoTwoFix .M22 := by
  refine sporNoTwoFix_of_mulEquiv (P := ↥NativeSporadic.M22) (MulEquiv.refl _) fun α hα => ?_
  by_cases hin : α ∈ inner NativeSporadic.M22
  · exact not_isPGroup_fixedPoints_of_mem_inner _ m22_center_eq_bot'
      m22_centralizerIn_not_isPGroup hin hα
  · exact not_isPGroup_fixedPoints_of_outer _ m22Delta m22_delta_normalizes m22_delta_sq
      m22_center_eq_bot' m22_delta_outer m22_mulAut_card m22_outer_centralizerIn_not_isPGroup
      (mul_self_eq_one_of_orderOf hα) hin

theorem m23_centralizerIn_not_isPGroup :
    ∀ u ∈ NativeSporadic.M23, orderOf u = 2 →
      ¬ IsPGroup 2 ↥(centralizerIn NativeSporadic.M23 u) := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, -, -⟩ := m23_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23InvReps_eq] at hok
  rw [← m23Certificate_originalSubgroup]
  intro u hu ho
  refine not_isPGroup_centralizerIn_of_repsOK hn m23Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) [m23Rep1] ?_ 4000 hok ?_ u (by simpa using hu) ho
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨by simpa using hr1, hro1⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact not_isPGroup_of_le hK1 (not_isPGroup_of_three_dvd (by rw [hKc1]; norm_num))

theorem sporNoTwoFix_M23 :
    SporNoTwoFix .M23 := by
  refine sporNoTwoFix_of_mulEquiv (P := ↥NativeSporadic.M23) (MulEquiv.refl _) fun α hα => ?_
  have htop : inner NativeSporadic.M23 = ⊤ :=
    inner_eq_top_of_card_le m23_center_eq_bot' m23_mulAut_card
  exact not_isPGroup_fixedPoints_of_mem_inner _ m23_center_eq_bot'
    m23_centralizerIn_not_isPGroup (htop ▸ Subgroup.mem_top α) hα

theorem m24_centralizerIn_not_isPGroup :
    ∀ u ∈ NativeSporadic.M24, orderOf u = 2 →
      ¬ IsPGroup 2 ↥(centralizerIn NativeSporadic.M24 u) := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m24Certificate := m24Certificate_check
  obtain ⟨hok, -, -⟩ := m24_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m24_rep_data2
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  rw [m24InvReps_eq] at hok
  rw [← m24Certificate_originalSubgroup]
  intro u hu ho
  refine not_isPGroup_centralizerIn_of_repsOK hn m24Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) [m24Rep1, m24Rep2] ?_ 40000 hok ?_ u (by simpa using hu) ho
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨by simpa using hr1, hro1⟩
    · exact ⟨by simpa using hr2, hro2⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact not_isPGroup_of_le hK1 (not_isPGroup_of_three_dvd (by rw [hKc1]; norm_num))
    · exact not_isPGroup_of_le hK2 (not_isPGroup_of_three_dvd (by rw [hKc2]; norm_num))

theorem sporNoTwoFix_M24 :
    SporNoTwoFix .M24 := by
  refine sporNoTwoFix_of_mulEquiv (P := ↥NativeSporadic.M24) (MulEquiv.refl _) fun α hα => ?_
  have htop : inner NativeSporadic.M24 = ⊤ :=
    inner_eq_top_of_card_le m24_center_eq_bot' m24_mulAut_card
  exact not_isPGroup_fixedPoints_of_mem_inner _ m24_center_eq_bot'
    m24_centralizerIn_not_isPGroup (htop ▸ Subgroup.mem_top α) hα

end CFSG.ComponentClassification.HarrisLit.L33.SR
