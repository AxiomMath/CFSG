module

public import CFSG.ClassicalInvolution.SmallCases.NDBS1Exo
public import CFSG.ClassicalInvolution.SmallCases.NDBC9
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
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace Cover

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G}

theorem shape_of_noTwinX {K : Subgroup G} (hS : Setting p f K z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) (hnoT : ¬ HasTwin p f K z)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) {i₁ : Fin D.card}
    (hQ : ¬ (D.tag i₁ = .PSL ∧ D.rank i₁ = 2))
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) :
    Asc77.ChainShape p f (𝒞 K) z ∨ PSpShape p f (𝒞 K) z ∨ ExoticNoTwin p f K z := by
  by_cases hX : ExoticTag (D.tag i₁) (D.rank i₁)
  · exact Or.inr (Or.inr ⟨hnoT, hnoF, D, i₁, hX⟩)
  refine Or.imp_right Or.inl ?_
  set C := toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D with hC
  have htrans : ∀ M ∈ 𝒞 K, ∃ g : G, conjSub g C.K = M := fun M hM => hM
  have hnoT' : ¬ ∃ T ∈ 𝒞 K, T ≠ C.K ∧ IsClassicalMember p f T z := hnoT
  obtain ⟨i₀, hi₀, hK₀⟩ := C.exists_A1_of_K
  have hi₀₁ : i₀ ≠ i₁ := fun h => hQ (h ▸ hi₀)
  have hcases : ∀ i, i = i₀ ∨ i = i₁ := by
    intro i
    by_cases h1 : i = i₁
    · exact Or.inr h1
    by_cases h0 : i = i₀
    · exact Or.inl h0
    obtain ⟨T, hT, hTK, hTz, -⟩ := A1_member_twin C hnoF hQ hi₀ hK₀ (hrest i h1) h0
    exact (hnoT ⟨T, hT, hTK, hTz⟩).elim
  have hcard : D.card = 2 := card_eq_two_of hi₀₁ hcases
  have hG2 : D.tag i₁ ≠ .G2 := fun h => hX (Or.inl h)
  have hD4 : D.tag i₁ ≠ .trialityD4 := fun h => hX (Or.inr (Or.inl h))
  have hq' : 5 ≤ p ^ D.exp i₁ := by
    rw [show D.exp i₁ = f from C.exp_eq i₁ hD4]
    exact hS.five
  have hadm := D.admissible i₁
  rcases small_of_noFrame C hnoF hQ hG2 hD4 with
    ⟨ht, hn⟩ | ⟨ht, hn⟩ | ⟨ht, hn⟩ | ⟨ht, hn⟩ | ⟨ht, hn⟩ | ⟨ht, hn⟩
  · have h2 := two_le_of_psl hadm ht
    have hne : D.rank i₁ ≠ 2 := fun h => hQ ⟨ht, h⟩
    have hn' : D.rank i₁ ≤ 4 := hn
    exact Or.inl ⟨D, hcard, i₀, i₁, hi₀₁, hi₀.1, hi₀.2, Or.inl ht, by omega⟩
  · have h3 := three_le_of_psu hadm ht
    have hn' : D.rank i₁ ≤ 4 := hn
    exact Or.inl ⟨D, hcard, i₀, i₁, hi₀₁, hi₀.1, hi₀.2, Or.inr ht, by omega⟩
  · right
    obtain ⟨R₁, hR₁, R₂, hR₂, hne, hc⟩ := Asc77.ih8SmallEdge p (D.tag i₁) (D.rank i₁)
      (D.exp i₁) hadm hS.odd hq' (Or.inr (Or.inr (Or.inl ⟨ht, hn⟩)))
    obtain ⟨b, hb⟩ := zbar_mem_of_pair C htrans hnoF hnoT' hQ hG2 hD4 hR₁ hR₂ hne hc
    have hzK : oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ ∈ (C.psi i₀).range := by
      rw [← hK₀, C.exactCore_K]
      exact oddQuotMk_mem_modOdd C.K_cl.mem _
    obtain ⟨a, ha⟩ := hzK
    have hab : D.hom i₀ a = D.hom i₁ b :=
      Bootstrap.sectionQuotientHom_injective C.hs.normalizes (ha.trans hb.symm)
    refine ⟨D, hcard, i₀, i₁, hi₀₁, hi₀.1, hi₀.2, ht, hn, D.hom i₀ a, fun h1 => ?_, ⟨a, rfl⟩,
      ⟨b, hab.symm⟩⟩
    have h2 : oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ = 1 := by
      rw [← ha]
      show Bootstrap.sectionQuotientHom C.hs.normalizes (D.hom i₀ a) = 1
      rw [h1]
      exact map_one _
    exact C.hKz.ne_one (congrArg Subtype.val
      (eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) h2))
  · exact (hX (Or.inr (Or.inr (Or.inl ⟨ht, hn⟩)))).elim
  · exfalso
    obtain ⟨R, hR, -⟩ := exists_member_of_meets C i₁
    obtain ⟨R₂, hR₂, R₃, hR₃, n12, n13, n23, c12, c13, c23⟩ :=
      exists_triangle_plus hS.odd hq' ht hn hadm hR
    exact false_of_triangle C htrans hnoF hnoT' hQ hG2 hD4 hR hR₂ hR₃ n12 n13 n23 c12 c13 c23
  · exact (hX (Or.inr (Or.inr (Or.inr ⟨ht, hn⟩)))).elim

theorem shape_of_settingX (hA : NoAllA1 p f) (hB' : NoG2D4Twin p f) (hC : NoD4Twins p f)
    {K : Subgroup G} (hS : Setting p f K z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) :
    Asc77.ChainShape p f (𝒞 K) z ∨ TwinShapeWeak p f K z ∨ PSpShape p f (𝒞 K) z ∨
      ExoticNoTwin p f K z := by
  obtain ⟨D⟩ := nonempty_lieSystem hS.nonabelian hS.odd hS.five hS.member hS.below
  set C := toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D with hC'
  obtain ⟨i₁, hQ⟩ : ∃ i₁ : Fin D.card, ¬ (D.tag i₁ = .PSL ∧ D.rank i₁ = 2) := by
    by_contra h
    push Not at h
    exact hA G K z hS D fun i => ⟨(h i).1, (h i).2⟩
  have hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2 := by
    intro i hi
    by_contra h
    exact false_of_two_nonA1 C hnoF hi h hQ
  by_cases hT : HasTwin p f K z
  · exact Or.inr (Or.inl (shape_of_twin hB' hC hS hnoF hT D hQ hrest))
  · rcases shape_of_noTwinX hS hnoF hT D hQ hrest with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

end Cover

variable (p f : ℕ) [Fact p.Prime]

@[expose] def NoDataShapeCoverX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      Disconnected.DConnected (𝒞 K) → ¬ BootData p f (𝒞 K) →
        (∃ A : Subgroup G, Theorem5.FuzzyFrameOn p f (𝒞 K) A) ∨
          Asc77.ChainShape p f (𝒞 K) z ∨ TwinShapeWeak p f K z ∨ PSpShape p f (𝒞 K) z ∨
            ExoticNoTwin p f K z

variable {p f}

theorem noDataShapeCoverX_of_residuals (hA : NoAllA1 p f) (hB' : NoG2D4Twin p f)
    (hC : NoD4Twins p f) : NoDataShapeCoverX p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow h3 h4 hD hB
  have hS : Setting p f K z := ⟨hnab, hp2, hq, hz, hBelow, h3, h4, hD, hB⟩
  by_cases hF : ∃ A : Subgroup G, Theorem5.FuzzyFrameOn p f (𝒞 K) A
  · exact Or.inl hF
  · exact Or.inr (Cover.shape_of_settingX hA hB' hC hS fun A hA' => hF ⟨A, hA'⟩)

end CFSG.ClassicalInvolution.NDB
