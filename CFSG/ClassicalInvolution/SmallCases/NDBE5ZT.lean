module

public import CFSG.ClassicalInvolution.SmallCases.NDBE0Stmt
import CFSG.ClassicalInvolution.Asc77.WP3CFCZT
import CFSG.ClassicalInvolution.Asc77.AscT8Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.WP3SCVPart
import CFSG.ClassicalInvolution.SmallCases.DSplitEdge
import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyFrames
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
import CFSG.ClassicalInvolution.Asc77.AscE187Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscT8Setup
import CFSG.ClassicalInvolution.Asc77.AscThmABasic
import CFSG.ClassicalInvolution.Asc77.WP2Thm7c
import CFSG.ClassicalInvolution.Asc77.WP3ChainVGen3
import CFSG.ClassicalInvolution.Asc77.WP3S28WTag

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

namespace Exotic

omit [Finite G] [IsSimpleGroup G] in
theorem noTwins {K : Subgroup G} {z : G} (hΩ : Asc77.HypOmegaMod p f (𝒞 K))
    (hKz : IsUniqueInvolution K z) (hnoT : ¬ HasTwin p f K z) :
    ∀ M ∈ 𝒞 K, ∀ M' ∈ Asc77.twinSet (𝒞 K) M, M' = M := by
  intro M hM
  refine Asc77.T8.noTwins_of_mem hΩ.conjInvariant (fun M hM => hM) (fun K' hK' => ?_) hM
  obtain ⟨hK'Ω, w, hKw, hK'w⟩ := hK'
  have hwz : w = z := hKw.eq hKz
  subst hwz
  by_contra hne
  exact hnoT ⟨K', hK'Ω, hne, Asc77.isClassicalMember_of_twin hΩ hK'Ω hK'w⟩

theorem involution_eq_of_noFuzzy (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G))
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) {J : Subgroup G} {t : G}
    (hJ : J ∈ 𝒞 K) (ht : IsClassicalMember p f J t) (htz : t ≠ z)
    (hzJ : z ∈ Bootstrap.trivialOnQuot J) {N : Subgroup G} (hN : N ∈ 𝒞 K) {w : G}
    (hw : IsClassicalMember p f N w) (hzN : z ∈ Bootstrap.trivialOnQuot N)
    (htN : t ∈ Bootstrap.trivialOnQuot N) (hwz : w ≠ z) (hwt : w ≠ t) : w = z * t := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hne : ∀ {L : Subgroup G} {a b : G}, IsClassicalMember p f L a →
      IsClassicalMember p f L b → b ≠ a → False :=
    fun ha hb hba => hba (ha.eq_of_isCentralInvolution hp2 hf hb.isCentralInvolution)
  have hJK : J ≠ K := by
    rintro rfl
    exact hne hz ht htz
  have hNK : N ≠ K := by
    rintro rfl
    exact hne hz hw hwz
  have hNJ : N ≠ J := by
    rintro rfl
    exact hne ht hw hwt
  obtain ⟨D⟩ := Cover.nonempty_lieSystem hnab hp2 hq hz hBelow
  have htK : t ∈ Bootstrap.trivialOnQuot K :=
    Cover.mem_trivialOnQuot_K (Cover.toXCtx hnab hp2 hq hz hBelow D) ⟨hJ, hzJ⟩ ht hJK
  have hwK : w ∈ Bootstrap.trivialOnQuot K :=
    Cover.mem_trivialOnQuot_K (Cover.toXCtx hnab hp2 hq hz hBelow D) ⟨hN, hzN⟩ hw hNK
  have e := Cover.conjClass_eq_of_mem hJ
  obtain ⟨D'⟩ := Cover.nonempty_lieSystem hnab hp2 hq ht hBelow
  have hwJ : w ∈ Bootstrap.trivialOnQuot J :=
    Cover.mem_trivialOnQuot_K (Cover.toXCtx hnab hp2 hq ht hBelow D') ⟨e ▸ hN, htN⟩ hw hNJ
  have hUt := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq ht
  have hUw := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hw
  have hcomm : ∀ {a b : G} {L : Subgroup G}, IsUniqueInvolution L b →
      a ∈ Bootstrap.trivialOnQuot L → a * b = b * a := by
    intro a b L hb ha
    have h := Asc77.SCV.conj_eq_of_isUniqueInvolution hb ha.1
    calc a * b = (a * b * a⁻¹) * a := by group
      _ = b * a := by rw [h]
  by_contra hwzt
  have hT : Bootstrap.AxisTriangle p f K J N z t w :=
    { cls₁ := hz
      cls₂ := ht
      cls₃ := hw
      comm₁₂ := hcomm hUt hzJ
      comm₁₃ := hcomm hUw hzN
      comm₂₃ := hcomm hUw htN
      tq₁₂ := htK
      tq₁₃ := hwK
      tq₂₁ := hzJ
      tq₂₃ := hwJ
      tq₃₁ := hzN
      tq₃₂ := htN }
  exact hnoF _ (Bootstrap.fuzzyFrameOn_of_axisTriangle hT (mem_conjClass_self K) hJ hN htz.symm
    hwz.symm hwt.symm (fun h => hwzt h.symm))

theorem thirdZT {K J K' : Subgroup G} {z t z' : G} (hS : ExoticBase p f K z)
    (hnoT : ¬ HasTwin p f K z) (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (hfr : Asc77.ChainFrameData (𝒞 K) K J K' z t z') :
    ∀ N ∈ 𝒞 K, N ≠ K → N ≠ J → z ∈ Bootstrap.trivialOnQuot N →
      t ∈ Bootstrap.trivialOnQuot N → IsUniqueInvolution N (z * t) := by
  intro N hN hNK hNJ hzN htN
  have hp2 := hS.odd
  have hq := hS.five
  have hΩ := Cover.hypOmegaMod hS.nonabelian hp2 hq hS.member hS.below
  have hTw := noTwins hΩ hfr.hz hnoT
  have hJΩ : J ∈ 𝒞 K := hfr.hJ.1
  have ht : IsClassicalMember p f J t := Asc77.isClassicalMember_of_twin hΩ hJΩ hfr.ht
  obtain ⟨w, hw⟩ := hΩ.classical N hN
  have hUw := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hw
  obtain ⟨a, ha, hJa⟩ := Disconnected.tq_of_mem_omegaNbr hp2 hq hΩ.classical hfr.mem hfr.hJ
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have haz : z = a := ha.eq_of_isCentralInvolution hp2 hf hS.member.isCentralInvolution
  rw [← haz] at hJa
  have hzJ : z ∈ Bootstrap.trivialOnQuot J :=
    Bootstrap.mem_trivialOnQuot_iff_actsTrivOnQuot.mpr hJa
  have htz : t ≠ z := by
    intro h
    refine hfr.hJ.2.1 (hTw K hfr.mem J ⟨hJΩ, z, hfr.hz, ?_⟩)
    rw [← h]
    exact hfr.ht
  have hwz : w ≠ z := by
    intro h
    rw [h] at hUw
    exact hNK (hTw K hfr.mem N ⟨hN, z, hfr.hz, hUw⟩)
  have hwt : w ≠ t := by
    intro h
    rw [h] at hUw
    exact hNJ (hTw J hJΩ N ⟨hN, t, hfr.ht, hUw⟩)
  have h := involution_eq_of_noFuzzy hS.nonabelian hp2 hq hS.member hS.below hnoF hJΩ ht htz hzJ
    hN hw hzN htN hwz hwt
  rw [← h]
  exact hUw

end Exotic

variable (p f) in
theorem exoticHyp51ZT_proved : ExoticHyp51ZT p f := by
  intro G _ _ _ K J K' z t z' hS hnoT hnoF _ hfr
  have hΩ := Cover.hypOmegaMod hS.nonabelian hS.odd hS.five hS.member hS.below
  have hcore : Asc77.ChainFrameCore p f (𝒞 K) K J K' z t z' :=
    ⟨hS.odd, hS.five, hΩ, Exotic.noTwins hΩ hfr.hz hnoT, hS.below, hfr⟩
  exact Asc77.CFC.hyp51At_zt_of_third hcore (Exotic.thirdZT hS hnoT hnoF hfr)

end CFSG.ClassicalInvolution.NDB
