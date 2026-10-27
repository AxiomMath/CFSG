module

public import CFSG.ClassicalInvolution.SmallCases.NDBC5
public import CFSG.ClassicalInvolution.ModelFacts.Orth15LieTwin
import CFSG.ClassicalInvolution.ModelFacts.Orth15VertexTwin
import CFSG.ClassicalInvolution.Asc77.AscIHSectE
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
public import CFSG.ClassicalInvolution.Asc77.AscE189Basic
public import CFSG.ClassicalInvolution.Asc77.WP2Interface
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinModel
public import CFSG.ClassicalInvolution.SmallCases.NDBC4

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace Cover

section Twins

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem ne_range_of_A1 (C : Asc77.XCtx p f Ω z) {i i' : Fin C.D.card} (hii' : i ≠ i')
    (hi : C.D.tag i = .PSL ∧ C.D.rank i = 2)
    (hz : oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ ∈ (C.psi i).range) :
    (C.psi i).range ≠ (C.psi i').range := by
  intro h
  refine C.range_not_comm_of_A1 i hi hz ?_
  intro a ha b hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', hb'⟩ : b ∈ (C.psi i').range := h ▸ hb
  rw [← hb']
  exact C.psi_commute hii' a' b'

variable [IsSimpleGroup G] in
theorem twin_mem_tq (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    {J : Subgroup G} {t : G} (hJ : J ∈ tqMembers (𝒞 K) z) (ht : IsClassicalMember p f J t)
    (htz : t ≠ z) {T : Subgroup G} (hT : T ∈ 𝒞 K) (hTt : IsClassicalMember p f T t) :
    T ∈ tqMembers (𝒞 K) z := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hJK : J ≠ K := by
    rintro rfl
    exact htz (hz.eq_of_isCentralInvolution hp2 hf ht.isCentralInvolution)
  have hTK : K ≠ T := by
    rintro rfl
    exact htz (hz.eq_of_isCentralInvolution hp2 hf hTt.isCentralInvolution)
  obtain ⟨D⟩ := nonempty_lieSystem hnab hp2 hq hz hBelow
  have htK : t ∈ Bootstrap.trivialOnQuot K :=
    mem_trivialOnQuot_K (toXCtx hnab hp2 hq hz hBelow D) hJ ht hJK
  have e := conjClass_eq_of_mem hT
  obtain ⟨D'⟩ := nonempty_lieSystem hnab hp2 hq hTt hBelow
  have hKt : K ∈ tqMembers (𝒞 T) t := ⟨e ▸ mem_conjClass_self K, htK⟩
  exact ⟨hT, mem_trivialOnQuot_K (toXCtx hnab hp2 hq hTt hBelow D') hKt hz hTK⟩

theorem twinShape_of_twins (C : Asc77.XCtx p f Ω z) {M M' : Subgroup G} (hM : M ∈ tqMembers Ω z)
    (hM' : M' ∈ tqMembers Ω z) {b : G} (hMb : IsClassicalMember p f M b)
    (hM'b : IsClassicalMember p f M' b) (hne : M' ≠ M) {j : Fin C.D.card}
    (hMj : modOdd z (exactCore z M) ≤ (C.psi j).range)
    (hM'j : modOdd z (exactCore z M') ≤ (C.psi j).range) (hG2 : C.D.tag j ≠ .G2)
    (hD4 : C.D.tag j ≠ .trialityD4) :
    Asc77.TwinShape (C.D.tag j) (C.D.rank j) ∧
      ∃ R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D,
        ∃ R' ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D, R ≠ R' ∧ Commutes R R' ∧
          R.map (C.psi j) = modOdd z (exactCore z M) ∧
            R'.map (C.psi j) = modOdd z (exactCore z M') := by
  have hmem : ∀ N ∈ tqMembers Ω z, exactCore z N ∈ centMembers (exactFamily Ω z) z :=
    fun N hN => ⟨exactCore_mem_exactFamily hN, exactCore_le_centralizer z N⟩
  obtain ⟨R, hR, hRM⟩ := Bootstrap.exists_fundamental_of_modOdd_le_sec C.hs C.D j (hmem M hM) hMj
  obtain ⟨R', hR', hRM'⟩ :=
    Bootstrap.exists_fundamental_of_modOdd_le_sec C.hs C.D j (hmem M' hM') hM'j
  obtain ⟨hbY, hK, hK', hneK, hzK, hzK'⟩ :=
    Asc77.secFam_twin C.hp C.hq C.hΩ C.hc2 hM hM' hMb hM'b hne
  have hRφ := Asc77.map_hom_eq_modOddIn C.hs C.D j (hmem M hM) hRM
  have hR'φ := Asc77.map_hom_eq_modOddIn C.hs C.D j (hmem M' hM') hRM'
  have hΦ := Asc77.hypOmega_secFam C.hp C.hq C.hΩ C.hc2 C.hs C.D
  have hKR : R.map (C.D.hom j) ∈ Asc77.secFam Ω z := by rw [hRφ]; exact hK
  have hK'R' : R'.map (C.D.hom j) ∈ Asc77.secFam Ω z := by rw [hR'φ]; exact hK'
  have hzKR : IsUniqueInvolution (R.map (C.D.hom j)) (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(centralizingLayer (exactFamily Ω z) {z})) ⟨b, hbY⟩) := by rw [hRφ]; exact hzK
  have hzK'R' : IsUniqueInvolution (R'.map (C.D.hom j))
      (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(centralizingLayer (exactFamily Ω z) {z})) ⟨b, hbY⟩) := by rw [hR'φ]; exact hzK'
  have hneR : R.map (C.D.hom j) ≠ R'.map (C.D.hom j) := by rw [hRφ, hR'φ]; exact hneK
  obtain ⟨hshape, hneR', hcomm, -⟩ := Asc77.twinShape_of_twin C.hp C.hq hΦ
    (Asc77.LieSystemData.toOmegaLie C.D (Asc77.omegaGen_secFam C.hs)) j hG2 hD4 (R := R) (R' := R')
    hR hR' hKR hK'R' hzKR hzK'R' hneR
  exact ⟨hshape, R, hR, R', hR', hneR', hcomm, hRM, hRM'⟩

theorem not_small_of_three_twins (C : Asc77.XCtx p f Ω z) {M₁ M₂ M₃ : Subgroup G}
    (h₁ : M₁ ∈ tqMembers Ω z) (h₂ : M₂ ∈ tqMembers Ω z) (h₃ : M₃ ∈ tqMembers Ω z) {b : G}
    (hb₁ : IsClassicalMember p f M₁ b) (hb₂ : IsClassicalMember p f M₂ b)
    (hb₃ : IsClassicalMember p f M₃ b) (h12 : M₂ ≠ M₁) (h13 : M₃ ≠ M₁) (h23 : M₃ ≠ M₂)
    {j : Fin C.D.card} (hj₁ : modOdd z (exactCore z M₁) ≤ (C.psi j).range)
    (hj₂ : modOdd z (exactCore z M₂) ≤ (C.psi j).range)
    (hj₃ : modOdd z (exactCore z M₃) ≤ (C.psi j).range) (hG2 : C.D.tag j ≠ .G2)
    (hD4 : C.D.tag j ≠ .trialityD4) :
    ¬ ((C.D.tag j = .PSp ∧ C.D.rank j = 2) ∨ (C.D.tag j = .PSL ∧ C.D.rank j = 4) ∨
      (C.D.tag j = .PSU ∧ C.D.rank j = 4) ∨ (C.D.tag j = .POmegaOdd ∧ C.D.rank j = 3) ∨
        (C.D.tag j = .POmegaMinus ∧ C.D.rank j = 4)) := by
  intro hsmall
  obtain ⟨-, R₁, hR₁, R₂, hR₂, hne12, hc12, hR₁M, hR₂M⟩ :=
    twinShape_of_twins C h₁ h₂ hb₁ hb₂ h12 hj₁ hj₂ hG2 hD4
  obtain ⟨-, R₁', hR₁', R₃, hR₃, hne13, hc13, hR₁'M, hR₃M⟩ :=
    twinShape_of_twins C h₁ h₃ hb₁ hb₃ h13 hj₁ hj₃ hG2 hD4
  obtain ⟨-, R₂', hR₂', R₃', hR₃', hne23, hc23, hR₂'M, hR₃'M⟩ :=
    twinShape_of_twins C h₂ h₃ hb₂ hb₃ h23 hj₂ hj₃ hG2 hD4
  have hper : ∀ {R R' : Subgroup (compModel C.D j).K},
      R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D →
      R' ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D →
      R.map (C.psi j) = R'.map (C.psi j) → R = R' := fun hR hR' h =>
    RouteD.eq_of_map_eq_of_perfect (C.psi j) (C.psi_ker j) (C.fund_perfect j hD4 hR).ge
      (C.fund_perfect j hD4 hR').ge h
  have e1 : R₁' = R₁ := hper hR₁' hR₁ (hR₁'M.trans hR₁M.symm)
  have e2 : R₂' = R₂ := hper hR₂' hR₂ (hR₂'M.trans hR₂M.symm)
  have e3 : R₃' = R₃ := hper hR₃' hR₃ (hR₃'M.trans hR₃M.symm)
  rw [e1] at hne13 hc13
  rw [e2, e3] at hne23 hc23
  have hq : 5 ≤ p ^ C.D.exp j := by rw [C.exp_eq j hD4]; exact C.hq
  exact Asc77.smallNoThree (p := p) (C.D.tag j) (C.D.rank j) (C.D.exp j) (C.D.admissible j) C.hp hq
    hsmall R₁ hR₁ R₂ hR₂ R₃ hR₃ hne12 hne13 hne23 hc12 hc13 hc23

end Twins

end Cover

end CFSG.ClassicalInvolution.NDB
