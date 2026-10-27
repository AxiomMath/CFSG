module

public import CFSG.ClassicalInvolution.SmallCases.NDBC7
import CFSG.ClassicalInvolution.Asc77.WP3SCSModel
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

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace Cover

theorem listedTwin_of {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (h1 : Asc77.TwinShape t n) (h2 : Asc77.SmallModel t n) : Asc77.ListedTwin t n := by
  unfold Asc77.TwinShape at h1
  unfold Asc77.SmallModel at h2
  unfold Asc77.ListedTwin
  rcases h1 with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp_all

section Twin

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem ne_z_of_le_nonA1 (C : Asc77.XCtx p f Ω z) {j : Fin C.D.card}
    (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2)) {N : Subgroup G} (hN : N ∈ tqMembers Ω z)
    {n : G} (hn : IsClassicalMember p f N n) {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D)
    (hNR : modOdd z (exactCore z N) = R.map (C.psi j)) : n ≠ z := by
  intro hnz
  have hx : oddQuotMk z ⟨n, C.involution_mem_centralizer hN hn⟩ ∈ R.map (C.psi j) :=
    hNR ▸ oddQuotMk_mem_modOdd (C.involution_mem_exactCore hN hn) _
  obtain ⟨y, -, hy⟩ := exists_not_commute C hj hR hx (C.isUniqueInvolution_modOdd hN hn).ne_one
  apply hy
  have e : (⟨n, C.involution_mem_centralizer hN hn⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
      ⟨z, Asc77.XCtx.hzC z⟩ := Subtype.ext hnz
  rw [e]
  exact zbar_comm y

variable [IsSimpleGroup G] in
theorem exists_twins_in_Q {K : Subgroup G} (hS : Setting p f K z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) {i₁ : Fin D.card}
    (hQ : ¬ (D.tag i₁ = .PSL ∧ D.rank i₁ = 2))
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) :
    ∃ g : G, g * z * g⁻¹ ≠ z ∧ ∀ T ∈ 𝒞 K, IsClassicalMember p f T z →
      conjSub g T ∈ tqMembers (𝒞 K) z ∧ IsClassicalMember p f (conjSub g T) (g * z * g⁻¹) ∧
        modOdd z (exactCore z (conjSub g T)) ≤
          ((toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D).psi i₁).range := by
  set C := toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D with hC
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; have := hS.five; simp at this)
  obtain ⟨R, hR, J, hJ, hJR⟩ := exists_member_of_meets C i₁
  obtain ⟨t, ht⟩ := C.hΩ.classical J hJ.1
  have htz : t ≠ z := ne_z_of_le_nonA1 C hQ hJ ht hR hJR
  obtain ⟨g, hg⟩ : ∃ g : G, conjSub g K = J := hJ.1
  have hgz : g * z * g⁻¹ = t := by
    have h := hS.member.conj g
    rw [hg] at h
    exact (h.eq_of_isCentralInvolution hS.odd hf ht.isCentralInvolution).symm
  refine ⟨g, hgz ▸ htz, fun T hT hTz => ?_⟩
  have hTt : IsClassicalMember p f (conjSub g T) t := hgz ▸ hTz.conj g
  have hTΩ : conjSub g T ∈ 𝒞 K := C.hΩ.conjInvariant g T hT
  have hmem : conjSub g T ∈ tqMembers (𝒞 K) z :=
    twin_mem_tq hS.nonabelian hS.odd hS.five hS.member hS.below hJ ht htz hTΩ hTt
  refine ⟨hmem, hTz.conj g, ?_⟩
  obtain ⟨j, R', -, hR'⟩ := C.exists_fund_of_mem hmem
  by_cases hj : j = i₁
  · subst hj
    rw [← hR']
    exact Subgroup.map_le_range _ _
  · exfalso
    refine htz (eq_z_of_le_A1 C hnoF hQ hmem hTt (hrest j hj) ?_)
    rw [← hR']
    exact Subgroup.map_le_range _ _

variable [IsSimpleGroup G] in
theorem shape_of_twin (hB' : NoG2D4Twin p f) (hC : NoD4Twins p f) {K : Subgroup G}
    (hS : Setting p f K z) (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (hT : HasTwin p f K z) (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) {i₁ : Fin D.card}
    (hQ : ¬ (D.tag i₁ = .PSL ∧ D.rank i₁ = 2))
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) : TwinShapeWeak p f K z := by
  refine ⟨⟨D, ?_⟩, hT⟩
  set C := toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D with hC'
  have hG2 : D.tag i₁ ≠ .G2 := fun h => hB' G K z hS hT D i₁ (Or.inl h)
  have hD4 : D.tag i₁ ≠ .trialityD4 := fun h => hB' G K z hS hT D i₁ (Or.inr h)
  obtain ⟨g, -, hconj⟩ := exists_twins_in_Q hS hnoF D hQ hrest
  obtain ⟨i₀, hi₀, hK₀⟩ := C.exists_A1_of_K
  obtain ⟨T, hTΩ, hTK, hTz⟩ := hT
  have eK := hconj K (mem_conjClass_self K) hS.member
  have eT := hconj T hTΩ hTz
  have hne : conjSub g T ≠ conjSub g K := fun h => hTK (conjSub_injective g h)
  obtain ⟨hshape, -⟩ :=
    twinShape_of_twins C eK.1 eT.1 eK.2.1 eT.2.1 hne eK.2.2 eT.2.2 hG2 hD4
  have hlist : Asc77.ListedTwin (D.tag i₁) (D.rank i₁) :=
    listedTwin_of hshape (small_of_noFrame C hnoF hQ hG2 hD4)
  obtain ⟨i₂, hi₂, hT₂⟩ := C.exists_A1_of_member hTΩ hTz
  have hzT : oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ ∈ (C.psi i₂).range := by
    rw [← hT₂]
    exact oddQuotMk_mem_modOdd hTz.mem _
  have hi₀₁ : i₀ ≠ i₁ := fun h => hQ (h ▸ hi₀)
  have hi₁₂ : i₁ ≠ i₂ := fun h => hQ (h ▸ hi₂)
  have hi₀₂ : i₀ ≠ i₂ := by
    intro h
    apply hTK
    refine (eq_of_modOdd_eq C.K_cl hTz ?_).symm
    rw [← C.exactCore_K, hK₀, h, hT₂]
  by_cases hTT : HasTwoTwins p f K z
  · exfalso
    obtain ⟨T₁, h₁, T₂, h₂, h1K, h2K, h12, h1z, h2z⟩ := hTT
    have e1 := hconj T₁ h₁ h1z
    have e2 := hconj T₂ h₂ h2z
    have n1 : conjSub g T₁ ≠ conjSub g K := fun h => h1K (conjSub_injective g h)
    have n2 : conjSub g T₂ ≠ conjSub g K := fun h => h2K (conjSub_injective g h)
    have n12 : conjSub g T₂ ≠ conjSub g T₁ := fun h => h12 (conjSub_injective g h).symm
    have hns := not_small_of_three_twins C eK.1 e1.1 e2.1 eK.2.1 e1.2.1 e2.2.1 n1 n2 n12 eK.2.2
      e1.2.2 e2.2.2 hG2 hD4
    rcases hlist with h | h | h | h | h | h
    · exact hns (Or.inl h)
    · exact hns (Or.inr (Or.inl h))
    · exact hns (Or.inr (Or.inr (Or.inl h)))
    · exact hns (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact hC G K z hS ⟨T₁, h₁, T₂, h₂, h1K, h2K, h12, h1z, h2z⟩ D i₁ h
    · exact hns (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · have hcover : ∀ i, i = i₀ ∨ i = i₁ ∨ i = i₂ := by
      intro i
      by_cases h1 : i = i₁
      · exact Or.inr (Or.inl h1)
      by_cases h0 : i = i₀
      · exact Or.inl h0
      right
      right
      obtain ⟨T', hT', hT'K, hT'z, hT'r⟩ := A1_member_twin C hnoF hQ hi₀ hK₀ (hrest i h1) h0
      by_cases hTT' : T' = T
      · have hr : (C.psi i).range = (C.psi i₂).range := by rw [← hT'r, hTT', hT₂]
        by_contra h2
        exact ne_range_of_A1 C h2 (hrest i h1) (hr ▸ hzT) hr
      · exact (hTT ⟨T, hTΩ, T', hT', hTK, hT'K, fun h => hTT' h.symm, hTz, hT'z⟩).elim
    exact ⟨card_eq_three_of hi₀₁ hi₀₂ hi₁₂ hcover, i₀, i₁, i₂, hi₀₁, hi₁₂, hi₀₂, hi₀.1, hi₀.2,
      hi₂.1, hi₂.2, hlist⟩

end Twin

end Cover

end CFSG.ClassicalInvolution.NDB
