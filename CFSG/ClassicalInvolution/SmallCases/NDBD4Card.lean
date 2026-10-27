module

public import CFSG.ClassicalInvolution.SmallCases.NDBC0
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootCtx
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

namespace CFSG.ClassicalInvolution.NDB.D4

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77.ExactLayer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem four_le_card (C : Asc77.XCtx p f Ω z) {T₁ T₂ : Subgroup G} (h₁ : T₁ ∈ Ω) (h₂ : T₂ ∈ Ω)
    (h1K : T₁ ≠ C.K) (h2K : T₂ ≠ C.K) (h12 : T₁ ≠ T₂) (h1z : IsClassicalMember p f T₁ z)
    (h2z : IsClassicalMember p f T₂ z) {i : Fin C.D.card}
    (hi : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2)) : 4 ≤ C.D.card := by
  classical
  obtain ⟨j₀, hj₀, hK₀⟩ := C.exists_A1_of_K
  rw [C.exactCore_K] at hK₀
  obtain ⟨j₁, hj₁, hT₁⟩ := C.exists_A1_of_member h₁ h1z
  obtain ⟨j₂, hj₂, hT₂⟩ := C.exists_A1_of_member h₂ h2z
  have n01 : j₀ ≠ j₁ := fun h => h1K (Cover.eq_of_modOdd_eq h1z C.K_cl (by rw [hT₁, hK₀, h]))
  have n02 : j₀ ≠ j₂ := fun h => h2K (Cover.eq_of_modOdd_eq h2z C.K_cl (by rw [hT₂, hK₀, h]))
  have n12 : j₁ ≠ j₂ := fun h => h12 (Cover.eq_of_modOdd_eq h1z h2z (by rw [hT₁, hT₂, h]))
  have ni0 : i ≠ j₀ := fun h => hi (h ▸ hj₀)
  have ni1 : i ≠ j₁ := fun h => hi (h ▸ hj₁)
  have ni2 : i ≠ j₂ := fun h => hi (h ▸ hj₂)
  have hcard : ({i, j₀, j₁, j₂} : Finset (Fin C.D.card)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [ni0, ni1, ni2]),
      Finset.card_insert_of_notMem (by simp [n01, n02]), Finset.card_pair n12]
  calc 4 = ({i, j₀, j₁, j₂} : Finset (Fin C.D.card)).card := hcard.symm
    _ ≤ Finset.univ.card := Finset.card_le_univ _
    _ = C.D.card := by rw [Finset.card_univ, Fintype.card_fin]

end CFSG.ClassicalInvolution.NDB.D4
