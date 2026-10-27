module

public import CFSG.ClassicalInvolution.RouteD.TWDConfig
public import CFSG.ClassicalInvolution.RouteD.TwinYR2Rows
public import CFSG.ClassicalInvolution.RouteD.TwinYExistsD
public import CFSG.ClassicalInvolution.RouteD.TwinYExistsB
public import CFSG.ClassicalInvolution.RouteD.TwinYExistsTD
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TwinY

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Assembly

variable {p f : ℕ} [Fact p.Prime]

theorem twinY_exists_on {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {P : StatedLieTag → ℕ → Prop} {t : StatedLieTag} {n : ℕ} (hrow : TwinRow t n) (hP : P t n)
    {Pat : ∀ {G : Type} [Group G], Set (Subgroup G) → Subgroup G → Subgroup G → G → Prop}
    (hY1 : TwinYP1On p f P) (hY2 : TwinYTypeOn p f P) (hY3 : TwinYPartnerOn p f P)
    (hY4 : TwinYPatternAt p f t n Pat) (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G}
    {z : G} (S : RouteDSetup p f K z) (hshape : LocalShapeT p f 2 t n (𝒞 K) z) :
    ∃ β ∈ 𝒞 K, ∃ s : G, IsClassicalMember p f β s ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧ Pat (𝒞 K) K β s := by
  obtain ⟨T, e, J, J', w, e', β, s, hcfg⟩ := hY3 G hnab K z S t n hrow hP hshape
  have hP1 := hY1 G hnab K z S t n hrow hP hshape T hcfg.twin hcfg.clsT e
  have hty := hY2 G hnab K z S t n hrow hP hshape T hcfg.twin hcfg.clsT e hP1
  have hJΩ : J ∈ 𝒞 K := hcfg.mem_J.1
  have SJ : RouteDSetup p f J w := S.of_mem_conjClass hJΩ hcfg.clsJ
  have hcl : 𝒞 J = 𝒞 K := conjClass_eq_of_mem hJΩ
  have hshapeJ : LocalShapeT p f 2 t n (𝒞 J) w := by
    rw [hcl]
    exact localShapeT_at_member S hJΩ hcfg.clsJ hshape
  have htwinJ : IsTwinAt (𝒞 J) J J' w := by
    rw [hcl]
    exact hcfg.twinJ
  have hP1' := hY1 G hnab J w SJ t n hrow hP hshapeJ J' htwinJ hcfg.clsJ' e'
  have hty' := hY2 G hnab J w SJ t n hrow hP hshapeJ J' htwinJ hcfg.clsJ' e' hP1'
  rw [hcl] at hP1' hty'
  exact ⟨β, hcfg.memβ.1, s, hcfg.clsβ, hcfg.linear,
    hY4 G hnab K z S hshape T e J J' w e' β s hcfg hP1 hP1' hty hty'⟩

theorem twinDExistsCase_of_Y {m : ℕ} (hm : 4 ≤ m) {P : StatedLieTag → ℕ → Prop}
    (hP : P .POmegaPlus m) (hY1 : TwinYP1On p f P) (hY2 : TwinYTypeOn p f P)
    (hY3 : TwinYPartnerOn p f P)
    (hY4 : TwinYPatternAt p f .POmegaPlus m (@PartnerPatternD p f m _)) :
    TwinDExistsCase p f m := by
  intro G _ _ _ hnab K z S k hk hshape
  subst hk
  exact twinY_exists_on (t := .POmegaPlus) (n := k) (Or.inl ⟨rfl, rfl, hm⟩) hP hY1 hY2 hY3 hY4
    hnab S hshape

end Assembly

end CFSG.ClassicalInvolution.RouteD.TWE
