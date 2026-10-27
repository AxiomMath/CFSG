module

public import CFSG.ClassicalInvolution.SmallCases.NDBS1Plus
public import CFSG.ClassicalInvolution.SmallCases.NDBStmt
import CFSG.ClassicalInvolution.Asc77.AscIH8Small
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
import CFSG.ClassicalInvolution.Asc77.TwinLookup

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem pspShape_of_card_two {K : Subgroup G} {z : G} (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G))
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) (hcard : D.card = 2) (i : Fin D.card)
    (ht : D.tag i = .PSp) (hn : D.rank i = 2) : PSpShape p f (𝒞 K) z := by
  set C := Cover.toXCtx hnab hp2 hq hz hBelow D with hC
  have htrans : ∀ M ∈ 𝒞 K, ∃ g : G, conjSub g C.K = M := fun M hM => hM
  have hQ : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2) := fun h =>
    absurd (ht.symm.trans h.1) (by decide)
  have hG2 : C.D.tag i ≠ .G2 := fun h => absurd (ht.symm.trans h) (by decide)
  have hD4 : C.D.tag i ≠ .trialityD4 := fun h => absurd (ht.symm.trans h) (by decide)
  have hq' : 5 ≤ p ^ D.exp i := by
    rw [show D.exp i = f from C.exp_eq i hD4]
    exact hq
  obtain ⟨i₀, hi₀, hK₀⟩ := C.exists_A1_of_K
  have hi₀i : i₀ ≠ i := fun h => hQ (h ▸ hi₀)
  obtain ⟨R₁, hR₁, R₂, hR₂, hne, hc⟩ := Asc77.ih8SmallEdge p (D.tag i) (D.rank i) (D.exp i)
    (D.admissible i) hp2 hq' (Or.inr (Or.inr (Or.inl ⟨ht, hn⟩)))
  obtain ⟨b, hb⟩ := Cover.zbar_mem_of_pair C htrans hnoF (S1.noTwin_of_card_two C hcard hQ) hQ
    hG2 hD4 hR₁ hR₂ hne hc
  have hzK : oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ ∈ (C.psi i₀).range := by
    rw [← hK₀, C.exactCore_K]
    exact oddQuotMk_mem_modOdd C.K_cl.mem _
  obtain ⟨a, ha⟩ := hzK
  have hab : D.hom i₀ a = D.hom i b :=
    Bootstrap.sectionQuotientHom_injective C.hs.normalizes (ha.trans hb.symm)
  refine ⟨D, hcard, i₀, i, hi₀i, hi₀.1, hi₀.2, ht, hn, D.hom i₀ a, fun h1 => ?_, ⟨a, rfl⟩,
    ⟨b, hab.symm⟩⟩
  have h2 : oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ = 1 := by
    rw [← ha]
    show Bootstrap.sectionQuotientHom C.hs.normalizes (D.hom i₀ a) = 1
    rw [h1]
    exact map_one _
  exact C.hKz.ne_one (congrArg Subtype.val
    (eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) h2))

end CFSG.ClassicalInvolution.NDB
