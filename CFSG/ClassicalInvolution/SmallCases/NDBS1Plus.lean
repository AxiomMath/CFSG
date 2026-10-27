module

public import CFSG.ClassicalInvolution.SmallCases.NDBC7
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

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

namespace S1

theorem noTwin_of_card_two {Ω : Set (Subgroup G)} {z : G} (C : Asc77.XCtx p f Ω z)
    (hcard : C.D.card = 2) {i : Fin C.D.card} (hQ : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2)) :
    ¬ ∃ T ∈ Ω, T ≠ C.K ∧ IsClassicalMember p f T z := by
  rintro ⟨T, hTΩ, hTK, hTz⟩
  obtain ⟨j₀, hj₀, hK₀⟩ := C.exists_A1_of_K
  obtain ⟨j₂, hj₂, hT₂⟩ := C.exists_A1_of_member hTΩ hTz
  have h0 : j₀.val ≠ i.val := fun h => hQ (Fin.ext h ▸ hj₀)
  have h2 : j₂.val ≠ i.val := fun h => hQ (Fin.ext h ▸ hj₂)
  have h02 : j₀.val ≠ j₂.val := by
    intro h
    apply hTK
    refine (Cover.eq_of_modOdd_eq C.K_cl hTz ?_).symm
    rw [← C.exactCore_K, hK₀, Fin.ext h, hT₂]
  have hj₀c := j₀.2
  have hj₂c := j₂.2
  have hic := i.2
  omega

end S1

variable [IsSimpleGroup G] in
theorem noSpinPlusSingle_of_card_two {K : Subgroup G} {z : G} (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G))
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) (hcard : D.card = 2) (i : Fin D.card) :
    ¬ (D.tag i = .POmegaPlus ∧ D.rank i = 4) := by
  rintro ⟨ht, hn⟩
  set C := Cover.toXCtx hnab hp2 hq hz hBelow D with hC
  have htrans : ∀ M ∈ 𝒞 K, ∃ g : G, conjSub g C.K = M := fun M hM => hM
  have hQ : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2) := fun h =>
    absurd (ht.symm.trans h.1) (by decide)
  have hG2 : C.D.tag i ≠ .G2 := fun h => absurd (ht.symm.trans h) (by decide)
  have hD4 : C.D.tag i ≠ .trialityD4 := fun h => absurd (ht.symm.trans h) (by decide)
  have hq' : 5 ≤ p ^ D.exp i := by
    rw [show D.exp i = f from C.exp_eq i hD4]
    exact hq
  obtain ⟨R, hR, -⟩ := Cover.exists_member_of_meets C i
  obtain ⟨R₂, hR₂, R₃, hR₃, n12, n13, n23, c12, c13, c23⟩ :=
    Cover.exists_triangle_plus hp2 hq' ht hn (D.admissible i) hR
  exact Cover.false_of_triangle C htrans hnoF (S1.noTwin_of_card_two C hcard hQ) hQ hG2 hD4 hR
    hR₂ hR₃ n12 n13 n23 c12 c13 c23

end CFSG.ClassicalInvolution.NDB
