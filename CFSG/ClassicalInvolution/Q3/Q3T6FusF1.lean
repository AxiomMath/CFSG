module

public import CFSG.ClassicalInvolution.Q3.Q3T6FusMain
public import CFSG.ClassicalInvolution.AschTight.S19QSec2
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open CFSG.Blueprint

section F1

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem exists_conj_eq_of_cStar3 (hK : Q3.IsClassicalMember3 K z)
    (hΩ : HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K))
    (hDE : DEdgeless (CoreAssembly.conjClass K))
    (hN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hnab : ∃ a b : G, a * b ≠ b * a) {n : ℕ} (hIH : CITBelowT (.sl2 3 1) n)
    (hn : Nat.card G ≤ n) (hM : Q3.M11Facts)
    (hOut : ∀ φ : MulAut ↥NativeSporadic.M11, ∃ g, φ = MulAut.conj g) {x : G}
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hx1 : x ≠ 1) (hxK : x ∈ centralizerModOdd ⊤ K)
    (hzx : z ∈ Subgroup.centralizer ({x} : Set G))
    (hex : ∃ c₀ : G, c₀ * x = x * c₀ ∧ c₀ * z * c₀⁻¹ ≠ z ∧
      c₀ * z * c₀⁻¹ * z = z * (c₀ * z * c₀⁻¹))
    (hL3 : (SectionLieTypeU 3 1 (conjFamily (secL K (Subgroup.centralizer ({x} : Set G))))
        (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) .PSL 3 ∨
      SectionLieTypeU 3 1 (conjFamily (secL K (Subgroup.centralizer ({x} : Set G))))
        (conjGen (secL K (Subgroup.centralizer ({x} : Set G)))) .PSU 3) →
      FusResidualL3 K z (Subgroup.centralizer ({x} : Set G)))
    {g : G} (hg : g * z * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G)) :
    ∃ c ∈ Subgroup.centralizer ({x} : Set G), c * z * c⁻¹ = g * z * g⁻¹ := by
  have h : FusSec3 K z (Subgroup.centralizer ({x} : Set G)) :=
    FusSec3.of_cStar_element hK hΩ hDE hN hx2 hxK hzx
  obtain ⟨c₀, hc₀x, hne, hcomm⟩ := hex
  have hc₀C : c₀ ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc₀x
  have hTop := top_not_mem_sectionFamily_sec h.zC h.memberC
    (⟨c₀, hc₀C⟩ : ↥(Subgroup.centralizer ({x} : Set G))) hne hcomm
  have hcard : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) < Nat.card G :=
    S19Q.card_centralizer_lt_of_ne_one hnab hx1
  have hsec := sectionThm6U hIH (hcard.trans_le hn) h.hypC
    ⟨secL K (Subgroup.centralizer ({x} : Set G)), ⟨1, conjSub_one _⟩⟩ h.edgelessC hTop
  obtain ⟨c, hc⟩ := h.fusion_of_sectionType3 hM hOut hsec hL3 ⟨g * z * g⁻¹, hg⟩ ⟨g, rfl⟩
  exact ⟨c, c.2, (congrArg Subtype.val hc).symm⟩

end F1

end CFSG.ClassicalInvolution.Q3.Q3T6
