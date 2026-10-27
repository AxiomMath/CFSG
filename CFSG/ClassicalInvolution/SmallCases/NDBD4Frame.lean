module

public import CFSG.ClassicalInvolution.SmallCases.NDBD4Defs
public import CFSG.ClassicalInvolution.Asc77.WP3FrameStarE
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.RouteD.LocalTwin
import CFSG.ClassicalInvolution.SmallCases.NDBD4Shape
import CFSG.ClassicalInvolution.SmallCases.NDBC3
import CFSG.ClassicalInvolution.SmallCases.DSplitBridge
import CFSG.ClassicalInvolution.Asc77.WP3L52Main
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

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]

@[expose] def D4FivePred : Asc77.ShapePred := fun G _ _ K z =>
  (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) ∧
    ∃ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∃ i : Fin D.card,
      (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∧ D.card = 5

@[expose] def ExoticD4FourFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      RouteD.LocalShapeT p f 4 .POmegaPlus 4 (𝒞 K) z → False

variable {p f}

theorem d4FiveCore_of_frame (hfr : Asc77.FrameExistsOnE p f (D4FivePred p f))
    (hF : ExoticD4FourFalse p f) : D4FiveCore p f := by
  intro G _ _ _ K z hnab hp2 hq hz hBelow hD hnoF D i hi h5
  obtain ⟨L₀, z₀, A, S, a, hfrm, hA⟩ :=
    hfr G hnab hp2 hq K z hz hBelow hD ⟨hnoF, D, i, hi, h5⟩
  have hΩ : InClass p f (𝒞 K) := inClass_conjugates hz
  obtain ⟨hex, hP1⟩ := Asc77.exactMembers_and_localOddCentral_of_fuzzyFrameStarE hnab hp2 hq hΩ
    (exists_single_class K) (localLieSystems_of_citBelowU hΩ hBelow) hD hfrm
    (Asc77.lemma52 G A hA)
  have hP1z := hP1 K (mem_conjClass_self K) z hz
  have hconn := Disconnected.routeD_deltaConnected_of_dConnected_of_exact hnab hp2 hq hz hBelow hD
    hex hP1z
  have hS : RouteDSetup p f K z := mk_routeDSetup hp2 hq hz hBelow hconn hex hP1z
  let C := Cover.toXCtx hnab hp2 hq hz hBelow D
  have hQ : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2) := fun h => by
    have h1 : D.tag i = .PSL := h.1
    rw [hi.1] at h1
    exact absurd h1 (by decide)
  have hrest : ∀ j, j ≠ i → D.tag j = .PSL ∧ D.rank j = 2 := fun j hj => by
    by_contra h
    exact Cover.false_of_two_nonA1 C hnoF hj h hQ
  exact hF G hnab K z hS
    (D4.localShapeT_of_exact hex hΩ.classical D (by omega) hi.1 hi.2 hrest)

end CFSG.ClassicalInvolution.NDB
