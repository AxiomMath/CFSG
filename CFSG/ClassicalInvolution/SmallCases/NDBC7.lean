module

public import CFSG.ClassicalInvolution.SmallCases.NDBC6
import CFSG.ClassicalInvolution.Asc77.AscIH8Small
import CFSG.ClassicalInvolution.Asc77.AscMuTabD4
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
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace Cover

section Counting

theorem card_eq_two_of {n : ℕ} {a b : Fin n} (hab : a ≠ b) (h : ∀ i : Fin n, i = a ∨ i = b) :
    n = 2 := by
  have ha := a.2
  have hb := b.2
  have hne : a.val ≠ b.val := fun e => hab (Fin.ext e)
  by_contra hn
  have h3 : 3 ≤ n := by omega
  obtain ⟨k, hk, hka, hkb⟩ : ∃ k, k < 3 ∧ k ≠ a.val ∧ k ≠ b.val := by
    by_cases h0 : a.val = 0 ∨ b.val = 0
    · by_cases h1 : a.val = 1 ∨ b.val = 1
      · exact ⟨2, by omega, by omega, by omega⟩
      · exact ⟨1, by omega, by omega, by omega⟩
    · exact ⟨0, by omega, by omega, by omega⟩
  rcases h ⟨k, by omega⟩ with e | e
  · exact hka (congrArg Fin.val e)
  · exact hkb (congrArg Fin.val e)

theorem card_eq_three_of {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : ∀ i : Fin n, i = a ∨ i = b ∨ i = c) : n = 3 := by
  have ha := a.2
  have hb := b.2
  have hc := c.2
  have h1 : a.val ≠ b.val := fun e => hab (Fin.ext e)
  have h2 : a.val ≠ c.val := fun e => hac (Fin.ext e)
  have h3 : b.val ≠ c.val := fun e => hbc (Fin.ext e)
  by_contra hn
  have h4 : 4 ≤ n := by omega
  obtain ⟨k, hk, hka, hkb, hkc⟩ : ∃ k, k < 4 ∧ k ≠ a.val ∧ k ≠ b.val ∧ k ≠ c.val := by
    by_cases e0 : a.val = 0 ∨ b.val = 0 ∨ c.val = 0
    · by_cases e1 : a.val = 1 ∨ b.val = 1 ∨ c.val = 1
      · by_cases e2 : a.val = 2 ∨ b.val = 2 ∨ c.val = 2
        · exact ⟨3, by omega, by omega, by omega, by omega⟩
        · exact ⟨2, by omega, by omega, by omega, by omega⟩
      · exact ⟨1, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, by omega, by omega, by omega, by omega⟩
  rcases h ⟨k, by omega⟩ with e | e | e
  · exact hka (congrArg Fin.val e)
  · exact hkb (congrArg Fin.val e)
  · exact hkc (congrArg Fin.val e)

theorem two_le_of_psl {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (ht : t = .PSL) : 2 ≤ n := by
  subst ht
  exact hadm.2.2.1

theorem three_le_of_psu {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (ht : t = .PSU) : 3 ≤ n := by
  subst ht
  exact hadm.2.2.1

end Counting

section Shape

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem A1_member_twin (C : Asc77.XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A) {i₁ : Fin C.D.card}
    (hQ : ¬ (C.D.tag i₁ = .PSL ∧ C.D.rank i₁ = 2)) {i₀ : Fin C.D.card}
    (hi₀ : C.D.tag i₀ = .PSL ∧ C.D.rank i₀ = 2)
    (hK₀ : modOdd z (exactCore z C.K) = (C.psi i₀).range) {i : Fin C.D.card}
    (hi : C.D.tag i = .PSL ∧ C.D.rank i = 2) (hii₀ : i ≠ i₀) :
    ∃ T ∈ Ω, T ≠ C.K ∧ IsClassicalMember p f T z ∧ modOdd z T = (C.psi i).range := by
  obtain ⟨R, hR, N, hN, hNR⟩ := exists_member_of_meets C i
  rw [C.fund_eq_top i hi hR, Subgroup.map_top] at hNR
  obtain ⟨n, hn⟩ := C.hΩ.classical N hN.1
  have hnz : n = z := eq_z_of_le_A1 C hnoF hQ hN hn hi (le_of_eq hNR)
  rw [hnz] at hn
  have hNe : exactCore z N = N := exactCore_eq_self hn.perfect (isSubnormal_le hn.subnormal)
  refine ⟨N, hN.1, fun h => ?_, hn, by rw [← hNe, hNR]⟩
  have hz₀ : oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ ∈ (C.psi i₀).range := by
    rw [← hK₀, C.exactCore_K]
    exact oddQuotMk_mem_modOdd C.K_cl.mem _
  apply ne_range_of_A1 C (Ne.symm hii₀) hi₀ hz₀
  rw [← hK₀, ← hNR, h]

theorem exists_triangle_plus {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ e) (ht : t = .POmegaPlus) (hn : n = 4) (hadm : StatedLieAdmissible t n p e)
    {R : Subgroup (modelUniv t n p e Fact.out).K} (hR : R ∈ RouteD.ModelFund p t n e) :
    ∃ R₂ ∈ RouteD.ModelFund p t n e, ∃ R₃ ∈ RouteD.ModelFund p t n e, R ≠ R₂ ∧ R ≠ R₃ ∧
      R₂ ≠ R₃ ∧ Commutes R R₂ ∧ Commutes R R₃ ∧ Commutes R₂ R₃ := by
  subst ht hn
  obtain ⟨R₂, h₂, R₃, h₃, -, -, n12, n13, -, n23, -, -, c12, c13, -, c23, -⟩ :=
    Asc77.MuTab.clique_plus hp2 hq hadm hR
  exact ⟨R₂, h₂, R₃, h₃, n12, n13, n23, c12, c13, c23⟩

variable [IsSimpleGroup G] in
theorem shape_of_noTwin (hB : NoExoticSingle p f) {K : Subgroup G} (hS : Setting p f K z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) (hnoT : ¬ HasTwin p f K z)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) {i₁ : Fin D.card}
    (hQ : ¬ (D.tag i₁ = .PSL ∧ D.rank i₁ = 2))
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) :
    Asc77.ChainShape p f (𝒞 K) z ∨ PSpShape p f (𝒞 K) z := by
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
  have hG2 : D.tag i₁ ≠ .G2 := fun h => hB G K z hS hnoT D i₁ (Or.inl h)
  have hD4 : D.tag i₁ ≠ .trialityD4 := fun h => hB G K z hS hnoT D i₁ (Or.inr (Or.inl h))
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
  · exact (hB G K z hS hnoT D i₁ (Or.inr (Or.inr (Or.inl ⟨ht, hn⟩)))).elim
  · exfalso
    obtain ⟨R, hR, -⟩ := exists_member_of_meets C i₁
    obtain ⟨R₂, hR₂, R₃, hR₃, n12, n13, n23, c12, c13, c23⟩ :=
      exists_triangle_plus hS.odd hq' ht hn hadm hR
    exact false_of_triangle C htrans hnoF hnoT' hQ hG2 hD4 hR hR₂ hR₃ n12 n13 n23 c12 c13 c23
  · exact (hB G K z hS hnoT D i₁ (Or.inr (Or.inr (Or.inr ⟨ht, hn⟩)))).elim

end Shape

end Cover

end CFSG.ClassicalInvolution.NDB
