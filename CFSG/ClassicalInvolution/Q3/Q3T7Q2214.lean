module

public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge
public import CFSG.ClassicalInvolution.Q3.Q3T8Defs
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Base
public import CFSG.ClassicalInvolution.Q3.Q3T7EApp
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A02
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A02
public import CFSG.ClassicalInvolution.Q3.Q3T7P25B00
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Exact
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22RLayer
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Res
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Sect
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2201
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2202
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2203
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2204
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2205
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2206
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2207
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2208
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2209
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2210
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2211
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2212
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2213
public import CFSG.ClassicalInvolution.Asc77.AscExactDTwin
public import CFSG.ClassicalInvolution.Asc77.WP3Layer
public import CFSG.ClassicalInvolution.Asc77.AscExactDCover
public import CFSG.ClassicalInvolution.Asc77.WP3LayerPair
public import CFSG.ClassicalInvolution.Asc77.AscC22P1
public import CFSG.ClassicalInvolution.Asc77.AscExactDMain
public import CFSG.ClassicalInvolution.Asc77.AscT7Y2
public import CFSG.ClassicalInvolution.Asc77.AscT7Z1
public import CFSG.ClassicalInvolution.Asc77.AscC22P2
public import CFSG.ClassicalInvolution.Asc77.AscT7Z16
public import CFSG.ClassicalInvolution.Asc77.AscT7Z23
public import CFSG.ClassicalInvolution.Asc77.AscC22P3
public import CFSG.ClassicalInvolution.Asc77.AscR31Phan
public import CFSG.ClassicalInvolution.Asc77.AscC22P5
public import CFSG.ClassicalInvolution.Asc77.AscC22N1
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Asc77.AscC22G16
public import CFSG.ClassicalInvolution.Asc77.AscC25W13
public import CFSG.ClassicalInvolution.Asc77.AscC25W17
public import CFSG.ClassicalInvolution.Asc77.AscCX8A
public import CFSG.ClassicalInvolution.Asc77.AscS22B
public import CFSG.ClassicalInvolution.Asc77.AscS24Alpha
public import CFSG.ClassicalInvolution.Asc77.AscT7XFin
public import CFSG.ClassicalInvolution.Q3.Q3MTShapeA
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A09
public import CFSG.ClassicalInvolution.Q3.Q3T7P24H01
public import CFSG.ClassicalInvolution.Q3.Q3T8E274B
public import CFSG.ClassicalInvolution.Q3.Q3TLKLink
public import CFSG.ClassicalInvolution.SmallCases.NDBH5
public import CFSG.Foundations
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.Timmesfeld.Moufang.Three

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

abbrev _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.ExactD
    :=
  @CFSG.ClassicalInvolution.Asc77.ExactD

section

open scoped commutatorElement MatrixGroups Pointwise
namespace Asc77.ExactD
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.ExactD
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

structure TwinPair {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K K' : Subgroup G) (z : G) : Prop where
  hyp : Q3T8.Asc77.HypOmegaMod Ω
  mem : K ∈ Ω
  mem' : K' ∈ Ω
  ne : K ≠ K'
  hz : IsUniqueInvolution K z
  hz' : IsUniqueInvolution K' z
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem TwinPair.of_twinSet
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω)
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K ≠ K') :
    Q3T8.Asc77.ExactD.TwinPair Ω K K' z := by
  obtain ⟨hK'Ω, z', hz'K, hz'K'⟩ := hK'
  have hzz : z' = z := hz'K.eq hz
  subst hzz
  exact ⟨hΩ, hK, hK'Ω, hne, hz, hz'K'⟩

theorem TwinPair.symm
    (d : Q3T8.Asc77.ExactD.TwinPair Ω K K' z) : Q3T8.Asc77.ExactD.TwinPair Ω K' K
    z :=
  ⟨d.hyp, d.mem', d.mem, d.ne.symm, d.hz', d.hz⟩
section Twin
namespace TwinPair
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.ExactD
open CFSG.ClassicalInvolution.Asc77.ExactD.TwinPair
variable [Finite G] (d : Q3T8.Asc77.ExactD.TwinPair Ω K K' z)
include d

theorem comm_le
    : ⁅K, K'⁆ ≤ oddCoreOf K ⊓ oddCoreOf K' :=
  d.hyp.comm_le_oddCore_of_twin d.mem d.mem' d.ne d.hz d.hz'

theorem K_le
    : K ≤ Subgroup.normalizer (K' : Set G) :=
  d.hyp.le_normalizer_of_twin d.mem d.mem' d.ne d.hz d.hz'

theorem K'_le
    : K' ≤ Subgroup.normalizer (K : Set G) :=
  d.symm.K_le

theorem sup_le_normalizer_left
    : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) :=
  sup_le Subgroup.le_normalizer d.K'_le

theorem sup_le_normalizer_right
    : K ⊔ K' ≤ Subgroup.normalizer (K' : Set G) :=
  sup_le d.K_le Subgroup.le_normalizer

theorem sup_le_normalizer_oddCore_left
    : K ⊔ K' ≤ Subgroup.normalizer (oddCoreOf K : Set G) :=
  fun _ hg => mem_normalizer_oddCore_of_mem_normalizer (d.sup_le_normalizer_left hg)

theorem sup_le_normalizer_oddCore_right
    : K ⊔ K' ≤ Subgroup.normalizer (oddCoreOf K' : Set G) :=
  fun _ hg => mem_normalizer_oddCore_of_mem_normalizer (d.sup_le_normalizer_right hg)

theorem sup_le_normalizer_oddProd
    : K ⊔ K' ≤ Subgroup.normalizer (oddProd K K' : Set G) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_sup (oddCoreOf K) (oddCoreOf K')
    ⟨d.sup_le_normalizer_oddCore_left hg, d.sup_le_normalizer_oddCore_right hg⟩

theorem oddCoreOf_le_oddCoreOf_sup
    : oddCoreOf K ≤ oddCoreOf (K ⊔ K') :=
  Balance.le_oddCoreIn_of_normalizes ((oddCoreOf_le_self K).trans le_sup_left)
    d.sup_le_normalizer_oddCore_left (oddCoreOf_odd_natCard K)

theorem oddCoreOf_le_oddCoreOf_sup'
    : oddCoreOf K' ≤ oddCoreOf (K ⊔ K') :=
  Balance.le_oddCoreIn_of_normalizes ((oddCoreOf_le_self K').trans le_sup_right)
    d.sup_le_normalizer_oddCore_right (oddCoreOf_odd_natCard K')

theorem odd_oddProd
    : Odd (Nat.card (oddProd K K')) := by
  have hle : oddProd K K' ≤ oddCoreOf (K ⊔ K') :=
    sup_le d.oddCoreOf_le_oddCoreOf_sup d.oddCoreOf_le_oddCoreOf_sup'
  exact (oddCoreOf_odd_natCard (K ⊔ K')).of_dvd_nat (Subgroup.card_dvd_of_le hle)
end TwinPair
end Twin
section Chart
namespace TwinPair
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.ExactD
open CFSG.ClassicalInvolution.Asc77.ExactD.TwinPair
variable [Finite G] (d : Q3T8.Asc77.ExactD.TwinPair Ω K K' z)
include d
end TwinPair
end Chart
end Asc77.ExactD

end

section

namespace Asc77.ExactLayer
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement MatrixGroups
section Layer
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
  {K : Subgroup G}
end Layer
section Lie
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
  {K : Subgroup G} {z : G}
end Lie
section Compare
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
  {K : Subgroup G}

theorem centMembers_subset_exactFamily
    (hcls : ∀ K ∈ Ω, ∃ z, Q3T8.Generic.IsClassicalMember K z) :
    centMembers Ω c ⊆ Q3T8.Asc77.ExactLayer.exactFamily Ω c := by
  rintro K ⟨hKΩ, hKc⟩
  have hcom : ∀ x ∈ K, c * x = x * c := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKc hx)).symm
  have hcK : c ∈ trivialOnQuot K := by
    refine ⟨Subgroup.centralizer_le_normalizer (K : Set G) ?_, fun x hx => ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hcom h hh).symm
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcom x hx)]
      exact Subgroup.one_mem _
  exact ⟨K, ⟨hKΩ, hcK⟩, (inf_eq_left.mpr hKc).symm⟩
end Compare
end Asc77.ExactLayer

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace C22P
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22P
set_option linter.unusedSectionVars false
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem fuseFrame_S
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃)
    (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) :
    ∃ a a' : G, a ∈ K ∧ a' ∈ K' ∧ orderOf a = 4 ∧ orderOf a' = 4 ∧ a * a' = a' * a ∧
      ∃ (R R' : Subgroup G) (b b' y : G), IsSylow2In R K₃ ∧ IsSylow2In R' K₄ ∧ Commutes R R' ∧
        R ≤ Subgroup.centralizer ({a * a'} : Set G) ∧
        R' ≤ Subgroup.centralizer ({a * a'} : Set G) ∧ b ∈ R ∧ b' ∈ R' ∧ orderOf b = 4 ∧
        orderOf b' = 4 ∧ b * b = z ∧ b' * b' = z ∧ y ∈ rLayer Ω (a * a') ∧
        y * z * y⁻¹ = b * b' * (a * a') ∧ b * b' * (a * a') ≠ z ∧
        z * (b * b' * (a * a')) = (b * b' * (a * a')) * z := by
  classical
  have hs := h
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃ : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := hs.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  obtain ⟨R₁, R₂, R₃, R₄, h1, h2, h3, h4, hu₁, hu₂, c12, c13, c23, c14, c24, c34⟩ :=
    Q3T8.Asc77.C22P.exists_sylow_quad_S h hK₄ h41 h42 h43
  
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes c12.symm)
  have hP123 : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) :=
    hP12.to_sup_of_normal_right' h3.2.1 (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  have hP : IsPGroup 2 ↥(((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄) :=
    hP123.to_sup_of_normal_right' h4.2.1 (sup_le (sup_le
      (T7A.le_normalizer_of_commutes c14.symm) (T7A.le_normalizer_of_commutes c24.symm))
      (T7A.le_normalizer_of_commutes c34.symm))
  obtain ⟨W, hW, hWD⟩ := Q3T8.Asc77.exists_W_of_isPGroup (Q3T7.modU_toGen3 hΩ) hP
  have hD₁ : R₁ ∈ DSet Ω W := hWD R₁ (mem_RSet_of_isSylow2In hK h1)
    (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hD₂ : R₂ ∈ DSet Ω W := hWD R₂ (mem_RSet_of_isSylow2In hK' h2)
    (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hD₃ : R₃ ∈ DSet Ω W := hWD R₃ (mem_RSet_of_isSylow2In hK₃ h3)
    (le_sup_right.trans le_sup_left)
  have hD₄ : R₄ ∈ DSet Ω W := hWD R₄ (mem_RSet_of_isSylow2In hK₄Ω h4) le_sup_right
  obtain ⟨ρ₀, hρ₀K, hρ₀R⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK h1 hD₁
  obtain ⟨ρ₁, hρ₁K, hρ₁R⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK' h2 hD₂
  obtain ⟨ρ₂, hρ₂K, hρ₂R⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK₃ h3 hD₃
  obtain ⟨ρ₃, hρ₃K, hρ₃R⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK₄Ω h4
      hD₄
  let ρ : Fin 4 → Rep Ω W := ![ρ₀, ρ₁, ρ₂, ρ₃]
  have hρK : ∀ i, (ρ i).K = ![K, K', K₃, K₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀K, hρ₁K, hρ₂K, hρ₃K]
  have hρR : ∀ i, (ρ i).R = ![R₁, R₂, R₃, R₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀R, hρ₁R, hρ₂R, hρ₃R]
  have hTw : ∀ i, ![K, K', K₃, K₄] i ∈ twinSet Ω K := by
    intro i
    fin_cases i
    · exact mem_twinSet_self hK hz
    · exact hs.hK'
    · exact hs.hK₃
    · exact hK₄
  have hzρ : ∀ i, IsUniqueInvolution (ρ i).K z := by
    intro i
    rw [hρK i]
    fin_cases i
    · exact hz
    · exact hz'
    · exact hz₃
    · exact hz₄
  have hKK' : K ≠ K' := hs.hne.symm
  have hKK₃ : K ≠ K₃ := hs.hK₃K.symm
  have hKK₄ : K ≠ K₄ := h41.symm
  have hK'K₃ : K' ≠ K₃ := hs.hK₃K'.symm
  have hK'K₄ : K' ≠ K₄ := h42.symm
  have hK₃K₄ : K₃ ≠ K₄ := h43.symm
  have hneK : ∀ i j : Fin 4, i ≠ j → ![K, K', K₃, K₄] i ≠ ![K, K', K₃, K₄] j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hKK', hKK'.symm, hKK₃, hKK₃.symm, hKK₄, hKK₄.symm,
      hK'K₃, hK'K₃.symm, hK'K₄, hK'K₄.symm, hK₃K₄, hK₃K₄.symm] at hij ⊢
  have hneρ : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact hneK i j hij
  have hnbrρ : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact Q3T8.Asc77.T7V.adj_of_twins hs (hTw i) (hTw j) (hneK j i (Ne.symm hij))
  have hnc : ¬ DbarConnected Ω W :=
    Q3T8.Asc77.T7V.not_dbarConnected_of_wyl hs hW ρ₀ hρ₀K (hμ W hW)
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand hs.stand hW
  obtain ⟨σ, t, g, ht, hfar, hg, hrel, hR⟩ := c.fuse_frame h.stand.cls hnc ρ hzρ hneρ hnbrρ
  have hρ0K : (ρ 0).K = K := hρ₀K
  have hρ1K : (ρ 1).K = K' := hρ₁K
  have hρ2K : (ρ 2).K = K₃ := hρ₂K
  have hρ3K : (ρ 3).K = K₄ := hρ₃K
  have hρ0R : (ρ 0).R = R₁ := hρ₀R
  have hρ1R : (ρ 1).R = R₂ := hρ₁R
  have hρ2R : (ρ 2).R = R₃ := hρ₂R
  have hρ3R : (ρ 3).R = R₄ := hρ₃R
  have hgW : ∀ i, g i ∈ W := fun i => (hg i).1.2
  have hgR : ∀ i, g i ∈ (ρ i).R := by
    intro i
    have h1 := (Q3CL.Thompson.inf_W_of_mem_D hΩ hW (ρ i).hR (ρ i).hK (ρ i).hRK).1
    have hmem : g i ∈ (ρ i).R ⊓ W := by rw [h1]; exact (hg i).1
    exact hmem.1
  have hgsq : ∀ i, g i * g i = z := fun i =>
    sq_eq_involution_of_orderOf_four (hzρ i) (hg i).1.1 (hg i).2
  have hzW : z ∈ W := c.mem_W_of_isUniqueInvolution (ρ 0) (hzρ 0)
  have htW : t ∈ W := c.mem_W_of_isUniqueInvolution σ ht
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => c.comm_W x hx y hy
  have hu0W : g 0 * g 1 ∈ W := W.mul_mem (hgW 0) (hgW 1)
  have hu2 : (g 0 * g 1) * (g 0 * g 1) = 1 := by
    calc (g 0 * g 1) * (g 0 * g 1) = (g 0 * g 0) * (g 1 * g 1) := by
          rw [mul_assoc, ← mul_assoc (g 1), ← hcomm _ (hgW 0) _ (hgW 1)]; group
      _ = 1 := by rw [hgsq 0, hgsq 1]; exact (hzρ 0).sq
  have hc2 : IsPGroup 2 (Subgroup.zpowers (g 0 * g 1)) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hu2
  have hg0R₁ : g 0 ∈ R₁ := by simpa [hρ0R] using hgR 0
  have hg1R₂ : g 1 ∈ R₂ := by simpa [hρ1R] using hgR 1
  have hR₃C : R₃ ≤ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g 0 * g 1) = (x * g 0) * g 1 := by group
      _ = (g 0 * x) * g 1 := by rw [c13 (g 0) hg0R₁ x hx]
      _ = g 0 * (x * g 1) := by group
      _ = g 0 * (g 1 * x) := by rw [c23 (g 1) hg1R₂ x hx]
      _ = (g 0 * g 1) * x := by group
  have hR₄C : R₄ ≤ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g 0 * g 1) = (x * g 0) * g 1 := by group
      _ = (g 0 * x) * g 1 := by rw [c14 (g 0) hg0R₁ x hx]
      _ = g 0 * (x * g 1) := by group
      _ = g 0 * (g 1 * x) := by rw [c24 (g 1) hg1R₂ x hx]
      _ = (g 0 * g 1) * x := by group
  have hcK₃ : g 0 * g 1 ∈ trivialOnQuot K₃ :=
    (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hc2 hK₃).mpr ⟨R₃, h3, hR₃C⟩
  have hcK₄ : g 0 * g 1 ∈ trivialOnQuot K₄ :=
    (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hc2 hK₄Ω).mpr ⟨R₄, h4, hR₄C⟩
  have hex₃ : IsSylow2In R₃ (Q3T8.Asc77.ExactLayer.exactCore (g 0 * g 1) K₃) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hc2 hK₃ hcK₃).mpr ⟨h3, hR₃C⟩
  have hex₄ : IsSylow2In R₄ (Q3T8.Asc77.ExactLayer.exactCore (g 0 * g 1) K₄) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hc2 hK₄Ω hcK₄).mpr ⟨h4, hR₄C⟩
  have hg2R₃ : g 2 ∈ R₃ := by simpa [hρ2R] using hgR 2
  have hg3R₄ : g 3 ∈ R₄ := by simpa [hρ3R] using hgR 3
  
  obtain ⟨y, hy⟩ : ∃ y : G, y = (ρ 2).r * σ.r * (ρ 2).r⁻¹ := ⟨_, rfl⟩
  have hr₂R : (ρ 2).r ∈ R₃ := by simpa [hρ2R] using (ρ 2).hr
  have hyC : y ∈ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hR₃C hr₂R) (hR σ.hr))
      (Subgroup.inv_mem _ (hR₃C hr₂R))
  have hyN : y ∈ Subgroup.normalizer (W : Set G) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ρ 2).r_mem_normalizer σ.r_mem_normalizer)
      (Subgroup.inv_mem _ (ρ 2).r_mem_normalizer)
  have hbr := c.conjRep_braid h.stand.cls (ρ 2) σ (Ne.symm (hfar 2)) (hy ▸ hyN)
  have hKy : conjSub y K₃ = σ.K := by
    have h1 := c.K_eq_of_img_eq (Q3T8.Asc77.T7D.conjRep c.hΩ (hy ▸ hyN) (ρ 2)) σ hbr
    rw [hy, ← hρ2K]
    exact h1
  have hyz : y * z * y⁻¹ = t := by
    have h1 : IsUniqueInvolution (conjSub y K₃) (y * z * y⁻¹) := hz₃.conj y
    rw [hKy] at h1
    exact h1.eq ht
  have htz : t ≠ z := by
    intro h'
    have hσK : σ.K ∈ twinSet Ω K := ⟨σ.hK, z, hz, h' ▸ ht⟩
    have hperp : σ.K ∈ KPerp Ω K := by rw [hs.perp]; exact hσK
    rcases hperp with h'' | h''
    · exact hfar 0 (by rw [c.img_eq_of_K_eq σ (ρ 0) (h''.trans hρ0K.symm)])
    · exact hfar 0 (c.comm_of_omega (ρ 0) σ (by rw [hρ0K]; exact h'')).symm
  have hperm : g 0 * g 1 * g 2 * g 3 = g 2 * g 3 * (g 0 * g 1) := by
    calc g 0 * g 1 * g 2 * g 3 = (g 0 * g 1) * (g 2 * g 3) := by group
      _ = (g 2 * g 3) * (g 0 * g 1) := hcomm _ hu0W _ (W.mul_mem (hgW 2) (hgW 3))
  have hRL₃ : R₃ ≤ rLayer Ω (g 0 * g 1) :=
    le_iSup₂_of_le R₃ (mem_RSet_of_isSylow2In hK₃ h3) (le_iSup_of_le hR₃C le_rfl)
  have hRLσ : σ.R ≤ rLayer Ω (g 0 * g 1) :=
    le_iSup₂_of_le σ.R σ.hR.1 (le_iSup_of_le hR le_rfl)
  have hyL : y ∈ rLayer Ω (g 0 * g 1) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hRL₃ hr₂R) (hRLσ σ.hr))
      (Subgroup.inv_mem _ (hRL₃ hr₂R))
  refine ⟨g 0, g 1, by simpa [hρ0K] using (hg 0).1.1, by simpa [hρ1K] using (hg 1).1.1,
    (hg 0).2, (hg 1).2, hcomm _ (hgW 0) _ (hgW 1), ?_⟩
  refine ⟨R₃, R₄, g 2, g 3, y, h3, h4, c34, hR₃C, hR₄C, hg2R₃, hg3R₄, (hg 2).2, (hg 3).2,
    hgsq 2, hgsq 3, hyL, ?_, ?_, ?_⟩
  · rw [hyz, hrel, hperm]
  · rw [← hperm, ← hrel]
    exact htz
  · exact hcomm _ hzW _ (W.mul_mem (W.mul_mem (hgW 2) (hgW 3)) hu0W)
end C22P
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace T7Y
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7Y
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z u e g : G}
section Basic
omit [IsSimpleGroup G] in

theorem mem_normalizer_exactLayer
    {c h : G} (hΩ : ConjInvariant Ω)
    (hh : h ∈ Subgroup.centralizer ({c} : Set G)) :
    h ∈ Subgroup.normalizer (Q3T8.Asc77.ExactLayer.exactLayer Ω c : Set G) :=
  mem_normalizer_iff_conjSub_eq.mpr (Q3T8.Asc77.ExactLayer.conjSub_exactLayer hΩ hh)
end Basic
end T7Y
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.ExactLayer
namespace T7Z
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7Z
variable {G : Type} [Group G] [Finite G]

theorem exactLayer_eq_omegaGen
    (Ω : Set (Subgroup G)) (c : G) :
    Q3T8.Asc77.ExactLayer.exactLayer Ω c = omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω c) :=
  Q3T8.Asc77.ExactLayer.exactLayer_eq_iSup Ω c

theorem exists_omegaLie_of_layerOrth
    {Ω : Set (Subgroup G)} {c : G} {d : ℕ} {ε : Bool}
    (hO : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c) = ⊥) (h :
        Q3T8.Asc77.LayerOrthType Ω c d ε) :
    ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsOrthTag d ε t n ∧
      ∃ D : Q3T8.Asc77.OmegaLie (Q3T8.Asc77.ExactLayer.exactFamily Ω c), D.card = 1 ∧
        ∃ i : Fin D.card, D.tag i = t ∧ D.rank i = n := by
  obtain ⟨t, n, ht, hS⟩ := h
  refine ⟨t, n, ht, ?_⟩
  rw [Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen] at hO hS
  exact exists_omegaLie_of_sectionLieType hO hS
end T7Z
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace C22P
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22P
set_option linter.unusedSectionVars false
section Frame
variable {G : Type} [Group G] [Finite G]

@[expose] def FrameS
    (Ω : Set (Subgroup G)) (K₃ K₄ : Subgroup G) (z c : G) : Prop :=
  ∃ (R R' : Subgroup G) (b b' y : G), IsSylow2In R K₃ ∧ IsSylow2In R' K₄ ∧ Commutes R R' ∧
    R ≤ Subgroup.centralizer ({c} : Set G) ∧ R' ≤ Subgroup.centralizer ({c} : Set G) ∧
    b ∈ R ∧ b' ∈ R' ∧ orderOf b = 4 ∧ orderOf b' = 4 ∧ b * b = z ∧ b' * b' = z ∧
    y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω c ∧ y * z * y⁻¹ = b * b' * c ∧ b * b' * c ≠ z ∧
    z * (b * b' * c) = (b * b' * c) * z

theorem FrameS.conj
    {Ω : Set (Subgroup G)} {K₃ K₄ : Subgroup G} {z c : G}
    (hΩ : ConjInvariant Ω) (hF : Q3T8.Asc77.C22P.FrameS Ω K₃ K₄ z c) {n : G} (hn₃ : conjSub n K₃ =
        K₃)
    (hn₄ : conjSub n K₄ = K₄) (hnz : n * z * n⁻¹ = z) : Q3T8.Asc77.C22P.FrameS Ω K₃ K₄ z (n * c *
        n⁻¹) := by
  obtain ⟨R, R', b, b', y, hR, hR', hRR', hRc, hR'c, hbR, hb'R', hb4, hb'4, hbz, hb'z, hy, hyz,
    hne, hcomm⟩ := hF
  have hnz' : n⁻¹ * z * n = z := by
    have := congrArg (fun x => n⁻¹ * x * n) hnz
    simpa [mul_assoc] using this.symm
  have ho : ∀ x : G, orderOf (n * x * n⁻¹) = orderOf x := fun x =>
    orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective x
  refine ⟨conjSub n R, conjSub n R', n * b * n⁻¹, n * b' * n⁻¹, n * y * n⁻¹, ?_, ?_,
    hRR'.conjSub n, conjSub_le_centralizer_conj n hRc, conjSub_le_centralizer_conj n hR'c,
    conj_mem_conjSub hbR, conj_mem_conjSub hb'R', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hn₃]; exact hR.conj n
  · rw [← hn₄]; exact hR'.conj n
  · rw [ho, hb4]
  · rw [ho, hb'4]
  · calc n * b * n⁻¹ * (n * b * n⁻¹) = n * (b * b) * n⁻¹ := by group
      _ = z := by rw [hbz, hnz]
  · calc n * b' * n⁻¹ * (n * b' * n⁻¹) = n * (b' * b') * n⁻¹ := by group
      _ = z := by rw [hb'z, hnz]
  · rw [Q3T8.Asc77.ExactLayer.exactLayer_conj hΩ n c]
    exact conj_mem_conjSub hy
  · calc n * y * n⁻¹ * z * (n * y * n⁻¹)⁻¹ = n * y * (n⁻¹ * z * n) * y⁻¹ * n⁻¹ := by group
      _ = n * (y * z * y⁻¹) * n⁻¹ := by rw [hnz']; group
      _ = n * (b * b' * c) * n⁻¹ := by rw [hyz]
      _ = n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹) := by group
  · intro h
    apply hne
    have h2 : b * b' * c = n⁻¹ * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) * n := by group
    rw [h2, h, hnz']
  · calc z * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) =
        n * (z * (b * b' * c)) * n⁻¹ := by
          calc z * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹))
              = (n * z * n⁻¹) * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) := by rw [hnz]
            _ = n * (z * (b * b' * c)) * n⁻¹ := by group
      _ = n * ((b * b' * c) * z) * n⁻¹ := by rw [hcomm]
      _ = (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) * z := by
          calc n * ((b * b' * c) * z) * n⁻¹
              = (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) * (n * z * n⁻¹) := by group
            _ = _ := by rw [hnz]
end Frame
section Setting
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem frame_at
    (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃) (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) :
    Q3T8.Asc77.C22P.FrameS Ω K₃ K₄ z (u₁ * u₂) := by
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃ : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := hs.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  obtain ⟨a, a', ha, ha', ha4, ha'4, haa', R, R', b, b', y, hR, hR', hRR', hRc, hR'c, hbR, hb'R',
    hb4, hb'4, hbz, hb'z, hy, hyz, htz, hzt⟩ := Q3T8.Asc77.C22P.fuseFrame_S hs hK₄ h41 h42 h43 hμ
  have haz : a * a = z := sq_eq_involution_of_orderOf_four hz ha ha4
  have ha'z : a' * a' = z := sq_eq_involution_of_orderOf_four hz' ha' ha'4
  have haa2 : (a * a') * (a * a') = 1 := by
    calc (a * a') * (a * a') = (a * a) * (a' * a') := by
          rw [mul_assoc, ← mul_assoc a' a a', ← haa']; group
      _ = 1 := by rw [haz, ha'z]; exact hz.sq
  have hy' : y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω (a * a') := by
    exact Q3T8.Asc77.rLayer_le_exactLayer hΩ haa2 hy
  have hF : Q3T8.Asc77.C22P.FrameS Ω K₃ K₄ z (a * a') :=
    ⟨R, R', b, b', y, hR, hR', hRR', hRc, hR'c, hbR, hb'R', hb4, hb'4, hbz, hb'z, hy', hyz, htz,
      hzt⟩
  have hKK' : K ≤ trivialOnQuot K' := Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK hK' hs.hne.symm hz
      hz'
  have hK'K : K' ≤ trivialOnQuot K := Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK' hK hs.hne hz' hz
  obtain ⟨c, hc, hconj⟩ := Q3T8.Asc77.T7V.exists_conj_pair hΩ hK hK' hs.hne.symm hz hz' hKK' hK'K
      ha ha'
    hs.hu₁.1 hs.hu₂.1 ha4 ha'4 hs.hu₁.2 hs.hu₂.2 haa' hs.comm₁₂
  have nK₃ : K ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₃ hs.hK₃K.symm hz hz₃
  have nK₃' : K' ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₃ hs.hK₃K'.symm hz' hz₃
  have nK₄ : K ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₄Ω h41.symm hz hz₄
  have nK₄' : K' ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₄Ω h42.symm hz' hz₄
  have hc₃ : conjSub c K₃ = K₃ := mem_normalizer_iff_conjSub_eq.mp (sup_le nK₃ nK₃' hc)
  have hc₄ : conjSub c K₄ = K₄ := mem_normalizer_iff_conjSub_eq.mp (sup_le nK₄ nK₄' hc)
  have hcz : c * z * c⁻¹ = z := by
    have hle : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hz.commute_of_mem hx).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hz'.commute_of_mem hx).symm
    have h1 : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp (hle hc)
    rw [h1]
    group
  have := hF.conj hΩ.conjInvariant hc₃ hc₄ hcz
  rw [hconj] at this
  exact this
end Setting
end C22P
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace T7Z
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7Z
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}
section Perfect
end Perfect
section Alpha

theorem oddCore_commutes_of_alphaOf
    [Finite G] (hΩ : ConjInvariant Ω) {c t : G} (hc1 : c ≠ 1)
    {A : Subgroup G} (hcA : c ∈ A) (htA : t ∈ A) (hα : alphaOf A = ⊥) {n : G}
    (hn : n ∈ oddCoreOf (Q3T8.Asc77.ExactLayer.exactLayer Ω c)) : n * t = t * n := by
  have hBN : ∀ b ∈ Subgroup.centralizer ({c} : Set G),
      b ∈ Subgroup.normalizer (oddCoreOf (Q3T8.Asc77.ExactLayer.exactLayer Ω c) : Set G) := fun b
          hb =>
    T7L.mem_normalizer_oddCoreOf (Q3T8.Asc77.T7Y.mem_normalizer_exactLayer hΩ hb)
  have hOY : oddCoreOf (Q3T8.Asc77.ExactLayer.exactLayer Ω c) ≤ oddCoreOf (Subgroup.centralizer
      ({c} : Set G)) :=
    le_oddCoreIn_of_normalizes ((oddCoreIn_le _).trans
        (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω c)) hBN
      (oddCoreOf_odd_natCard _)
  exact T7Y.commute_of_alphaOf_eq_bot hcA hc1 hα (hOY hn) htA
variable [IsSimpleGroup G]
end Alpha
section ZStarE
variable [IsSimpleGroup G]
end ZStarE
section Layer
end Layer
section Final
variable [IsSimpleGroup G]
end Final
end T7Z
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace C22P
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22P
set_option linter.unusedSectionVars false
section ZStar
variable {G : Type} [Group G] [Finite G]
end ZStar
section Layer
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
end Layer
section Exact
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem exactMembers_S (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥)
    (hOc : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂)) = ⊥) {d : ℕ}
        {ε : Bool}
    (hY : Q3T8.Asc77.LayerOrthType Ω (u₁ * u₂) d ε) : ExactMembers Ω := by
  classical
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hc2 : (u₁ * u₂) * (u₁ * u₂) = 1 := hs.sq_12
  have hc2' : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  have hJtq : K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂) :=
    Q3T8.Asc77.C22P.mem_tqMembers_of_twin hs hs.hK₃ hs.hK₃K hs.hK₃K'
  have hzJ : IsUniqueInvolution K₃ z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK₃
  obtain ⟨z', hz'⟩ := hΩ.classical K₃ hs.hK₃.1
  have hz'z : z' = z := by
    have hsq : z' * z' = 1 := by
      have h2 := pow_orderOf_eq_one z'
      rw [hz'.orderOf_eq_two] at h2
      simpa [sq] using h2
    rcases hzJ.unique z' hz'.mem hsq with h | h
    · exfalso
      have h2 := hz'.orderOf_eq_two
      rw [h, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · exact h
  subst hz'z
  have hzA : z' ∈ Subgroup.closure ({u₁ * u₂, z'} : Set G) := Subgroup.subset_closure (by simp)
  have huA : u₁ * u₂ ∈ Subgroup.closure ({u₁ * u₂, z'} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hcomm :=
    CFSG.ClassicalInvolution.Asc77.ExactD.commutator_oddCore_centralizer_le_alphaOf hzJ.ne_one
      (Subgroup.closure ({u₁ * u₂, z'} : Set G)) hzA
  rw [hα] at hcomm
  have hOJ : ∀ n ∈ oddCoreOf K₃, n * (u₁ * u₂) = (u₁ * u₂) * n := by
    intro n hn
    have hn' : n ∈ oddCoreOf (Subgroup.centralizer ({z'} : Set G)) :=
      CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal hz'.subnormal hn
    have h1 : ⁅n, u₁ * u₂⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({z'} : Set G)),
        Subgroup.closure ({u₁ * u₂, z'} : Set G)⁆ := Subgroup.commutator_mem_commutator hn' huA
    have h2 : ⁅n, u₁ * u₂⁆ = 1 := Subgroup.mem_bot.mp (hcomm h1)
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  have hOe := Q3T8.Asc77.T7Z.oddCore_exactCore_eq_bot hΩ hc2 hOc hY hJtq
  have hK3 : Q3.IsClassicalMember3 K₃ z' := hz'.toQ3 (by norm_num)
  have hO0 : oddCoreOf K₃ = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxc : x ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hOJ x hx
    have hxK : x ∈ Q3T8.Asc77.ExactLayer.exactCore (u₁ * u₂) K₃ :=
      ⟨CFSG.ClassicalInvolution.Balance.oddCoreIn_le K₃ hx, hxc⟩
    have hx' : x ∈ Q3T8.Asc77.ExactLayer.exactCore (u₁ * u₂) K₃ ⊓ oddCoreIn K₃ := ⟨hxK, hx⟩
    rw [← Q3NL.oddCoreIn_exactCore3 hK3 hc2' hJtq.2] at hx'
    have h2 : oddCoreIn (Q3T8.Asc77.ExactLayer.exactCore (u₁ * u₂) K₃) = ⊥ := by
      show (classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactCore (u₁ * u₂) K₃)).map
        (Q3T8.Asc77.ExactLayer.exactCore (u₁ * u₂) K₃).subtype = ⊥
      rw [hOe, Subgroup.map_bot]
    rw [h2] at hx'
    exact hx'
  have hO : classicalInvolutionOddCore ↥K₃ = ⊥ := by
    have h3 : (classicalInvolutionOddCore ↥K₃).map K₃.subtype = ⊥ := hO0
    exact (Subgroup.map_eq_bot_iff_of_injective _ K₃.subtype_injective).mp h3
  exact exactMembers_of_oddCore_eq_bot
    ⟨K, hst.mem, fun L hL => by
      obtain ⟨g, hg⟩ := hst.trans L hL
      exact ⟨g, hg.symm⟩⟩ hs.hK₃.1 hO

theorem commutes_of_twins (hst : Q3T8.Asc77.AscStand Ω K) {z : G} (hz : IsUniqueInvolution K z)
    {M₁ M₂ : Subgroup G} (hM₁ : M₁ ∈ twinSet Ω K) (hM₂ : M₂ ∈ twinSet Ω K) (hne : M₁ ≠ M₂)
    (hex : ExactMembers Ω) : Commutes M₁ M₂ := by
  have hz₁ : IsUniqueInvolution M₁ z := isUniqueInvolution_of_mem_twinSet hz hM₁
  have hM₂' : M₂ ∈ twinSet Ω M₁ := by
    rw [twinSet_eq_of_mem_twinSet hz hM₁]
    exact hM₂
  have d := Q3T8.Asc77.ExactD.TwinPair.of_twinSet hst.hyp hM₁.1 hz₁ hM₂' hne
  have h := d.comm_le
  rw [oddCoreOf_eq_bot_of_exact hex hM₁.1, bot_inf_eq, le_bot_iff] at h
  intro x hx y hy
  have : ⁅x, y⁆ ∈ ⁅M₁, M₂⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this
end Exact
end C22P
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace R31
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.R31
set_option linter.unusedSectionVars false
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.Assembly.LowTwoRank
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

@[expose] def C22_phanChainNeg
    : Prop :=
  3 % 4 = 3 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) →
        (Q3T8.Asc77.LayerOrthType Ω (u₁ * u₂) 6 (piSign 3 1) ∧
          (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤) →
          ∃ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) ∧
            (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) ∧
            (∀ i j : Fin 4, edgeD 4 i j →
              ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (U i) (U j)) ∧
            ⨆ k, U k = ⊤ ∧ ¬ 3 ∣ Nat.card (Subgroup.center ↥(U 0 ⊔ U 1 ⊔ U 2))
end R31
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped commutatorElement MatrixGroups
namespace C22P
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22P
set_option linter.unusedSectionVars false
section Basic
variable {G : Type} [Group G] [Finite G]

theorem FrameS.exists_data
    {Ω : Set (Subgroup G)} {K₃ K₄ : Subgroup G} {z c : G}
    (h : Q3T8.Asc77.C22P.FrameS Ω K₃ K₄ z c) :
    ∃ (R R' : Subgroup G) (b b' y : G), Q3T8.Asc77.C22P.FrameData Ω K₃ K₄ z c R R' b b' y := by
  obtain ⟨R, R', b, b', y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨R, R', b, b', y, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩⟩
end Basic
section Layer
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem not_commutes_of_involution_S (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    {M L : Subgroup G} {t : G} (hM : M ∈ twinSet Ω K) (hLΩ : L ∈ Ω)
    (htL : IsUniqueInvolution L t) (htz : t ≠ z) : M ≠ L ∧ ¬ Commutes M L := by
  have hzM : IsUniqueInvolution M z := isUniqueInvolution_of_mem_twinSet hs.hz hM
  have hne : M ≠ L := by
    rintro rfl
    exact htz (htL.eq hzM)
  refine ⟨hne, fun h => ?_⟩
  have hmem : L ∈ omegaNbr Ω M := MuTab.mem_omegaNbr_of_commutes hLΩ hne.symm h
  have hperp : L ∈ KPerp Ω M := Or.inr hmem
  rw [Q3T8.Asc77.T7S22.perp_of_twin hs hM, twinSet_eq_of_mem_twinSet hs.hz hM] at hperp
  exact htz (htL.eq (isUniqueInvolution_of_mem_twinSet hs.hz hperp))
end Layer
end C22P
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement MatrixGroups
namespace C22N
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22N
set_option linter.unusedSectionVars false
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem nonempty_psuLayer_of_layerOrth {c : G}
    (hOc : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c) = ⊥)
    (hL : Q3T8.Asc77.LayerOrthType Ω c 6 false) :
    Nonempty (C22G.PSULayer 3 1 (Q3T8.Asc77.ExactLayer.exactFamily Ω c)) := by
  obtain ⟨t', n', ht', D, hcard, i, hit, hir⟩ := Q3T8.Asc77.T7Z.exists_omegaLie_of_layerOrth hOc hL
  have htn : t' = .PSU ∧ n' = 4 := by
    rcases ht' with h | h | h | h | h | h <;> simp_all
  have hie : D.exp i = 1 := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · exact absurd (hit.symm.trans h) (by rw [htn.1]; decide)
  exact nonempty_psuLayer_of_omegaLie D hcard i (hit.trans htn.1) (hir.trans htn.2) hie

theorem oddCore_layer_eq_bot_neg [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.OddCoreLayerNeg3]
    [IsSimpleGroup G] {K K' K₃ : Subgroup G} {z₀ u₁ u₂ u₃ : G}
    (h22 : Q3T8.Asc77.Hyp22 Ω K K' K₃ z₀ u₁ u₂ u₃) {c z : G} (hc1 : c ≠ 1)
    (hα : alphaOf (Subgroup.closure ({c, z} : Set G)) = ⊥)
    (hL : Q3T8.Asc77.LayerOrthType Ω c 6 false) (hzY : z ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω c)
        (hz2 : z * z = 1)
    (hmove : ¬ ∀ y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω c, y * z = z * y) :
    classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c) = ⊥ := by
  have h : Q3T8.Asc77.OddCoreLayerNeg3 := @Fact.out _ inferInstance
  exact h G Ω K K' K₃ z₀ u₁ u₂ u₃ h22 c z hc1 hα hL hzY hz2 hmove
end C22N
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
