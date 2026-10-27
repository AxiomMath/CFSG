module

public import CFSG.ClassicalInvolution.RouteD.TWT4Vis
public import CFSG.ClassicalInvolution.RouteD.TWYLayer
public import CFSG.ClassicalInvolution.RouteD.TWYArith
public import CFSG.ClassicalInvolution.RouteD.TWYArith2
public import CFSG.ClassicalInvolution.RouteD.TWYBridge
public import CFSG.ClassicalInvolution.RouteD.TWZSmall
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
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWT4

section Arith

variable {p f : ℕ} [Fact p.Prime]

theorem card_o4_eq_framesPlus (hf : f ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      framesPlus (p ^ f) 0 := by
  rw [card_o4 (GaloisField p f), GaloisField.card p f hf]
  rfl

end Arith

section LayerThree

variable {p f : ℕ} [Fact p.Prime]


theorem layerThree_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .POmegaOdd) (he : e = f) (hadm : StatedLieAdmissible t n p e)
    {R₀ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hN : Nat.card {S : Subgroup (modelUniv t n p e Fact.out).K //
      S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D ∧ Commutes S R₀} = 3) :
    False := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  obtain ⟨j, -, hcount⟩ := TWY.layerCount_odd hp2 hq ht he hadm hR₀ hN
  rw [card_o4_eq_framesPlus (p := p) hf] at hcount
  have h1 : TWY.cOdd (p ^ f) j = framesPlus (p ^ f) 0 := by omega
  rcases j with _ | j
  · exact TWY.framesPlus_ne_zero (q := p ^ f) (by omega) 0 (by simpa [TWY.cOdd] using h1.symm)
  · exact TWY.framesOdd_ne_framesPlus Fact.out hp2 (Nat.one_le_iff_ne_zero.mpr hf) rfl hq j 0 h1

theorem layerThree_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .POmegaPlus) (he : e = f) (hadm : StatedLieAdmissible t n p e)
    {R₀ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hN : Nat.card {S : Subgroup (modelUniv t n p e Fact.out).K //
      S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D ∧ Commutes S R₀} = 3) :
    n = 4 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  obtain ⟨j, hn, hcount⟩ := TWY.layerCount_plus hp2 hq ht he hadm hR₀ hN
  rw [card_o4_eq_framesPlus (p := p) hf] at hcount
  have h1 : framesPlus (p ^ f) j = framesPlus (p ^ f) 0 := by omega
  have := TWY.framesPlus_inj Fact.out hp2 (Nat.one_le_iff_ne_zero.mpr hf) rfl hq h1
  omega

theorem layerThree_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .POmegaMinus) (he : e = f) (hadm : StatedLieAdmissible t n p e)
    {R₀ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hN : Nat.card {S : Subgroup (modelUniv t n p e Fact.out).K //
      S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D ∧ Commutes S R₀} = 3) :
    False := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  obtain ⟨j, -, hcount⟩ := TWY.layerCount_minus hp2 hq ht he hadm hR₀ hN
  rw [card_o4_eq_framesPlus (p := p) hf] at hcount
  have h1 : TWY.cMinus (p ^ f) j = framesPlus (p ^ f) 0 := by omega
  rcases j with _ | j
  · exact TWY.framesPlus_ne_zero (q := p ^ f) (by omega) 0 (by simpa [TWY.cMinus] using h1.symm)
  · exact TWY.framesPlus_ne_framesMinus Fact.out hp2 (Nat.one_le_iff_ne_zero.mpr hf) rfl hq 0
      j h1.symm

end LayerThree

section Rank

variable {p f : ℕ} [Fact p.Prime]


theorem twinYRankOn_psu4_of_p1 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hmod : (p ^ f) % 4 = 3)
    (hY1 : TwinYP1On p f fun t n => t = .PSU ∧ n = 4) :
    TwinYRankOn p f fun t n => t = .PSU ∧ n = 4 := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e D hcard i horth'
  obtain ⟨rfl, rfl⟩ := hP
  have hP1 := hY1 G hnab K z S .PSU 4 hrow ⟨rfl, rfl⟩ hshape T hT clsT e
  have hMF : TwinMFGeneration p f .PSU 4 := twinMFGeneration_psu4 S.odd S.five
  have hncs : ∀ L ∈ 𝒞 K, ¬ Commutes L L := fun L hL => not_commutes_self_of_mem S.inClass hL
  obtain ⟨d, ε, -, horth⟩ := horth'
  have hDi : D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    rcases horth with ⟨-, ht, -⟩ | ⟨-, -, ht, -⟩ | ⟨-, -, ht, -⟩ | ⟨-, -, ht, -⟩ |
      ⟨-, -, -, ht, -⟩ | ⟨-, -, -, ht, -⟩ <;> rw [ht] <;> exact ⟨by decide, by decide⟩
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  have hD : ∀ j, D.tag j ≠ .G2 ∧ D.tag j ≠ .trialityD4 := fun j => by
    rw [hsub.elim j i]
    exact hDi
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, -, -, -, -⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  obtain ⟨A⟩ := exists_atT S hrow hshape hT clsT hJ hJK hJT hJt htz
  have hJKc : Commutes J K := (hT.comm_K J hJ hJK).symm
  have hJTc : Commutes J T := (hT.comm_T J hJ hJT).symm
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} := e.mem_centralizingMembers_u hJ.1 hJKc hJTc
  have hJ₂u : A.J₂ ∈ centralizingMembers (𝒞 K) {e.u} :=
    e.mem_centralizingMembers_u A.hJ₂t.1 (hT.comm_K A.J₂ A.hJ₂z A.hJ₂K).symm
      (hT.comm_T A.J₂ A.hJ₂z A.hJ₂T).symm
  obtain ⟨M₁, M₂, hM₁u, hM₂u, hM₁t, hM₂t, hM₁J, hM₁J₂, hM₂J, hM₂J₂, hM₁₂, -, huniq⟩ :=
    exists_visible_three hmod S e A
  have hcomJ : ∀ M ∈ centralizingMembers (𝒞 K) {t}, M ≠ J → Commutes M J := fun M hM hMJ =>
    (A.hJiso M hM hMJ).symm
  have hset : {N : Subgroup G | N ∈ centralizingMembers (𝒞 K) {e.u} ∧ Commutes N J} =
      {A.J₂, M₁, M₂} := by
    ext N
    constructor
    · rintro ⟨hNu, hNJ⟩
      have hNt : N ∈ centralizingMembers (𝒞 K) {t} :=
        ⟨hNu.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
          (hNJ y hy t hJt.mem)⟩
      have hNJne : N ≠ J := fun h => hncs J hJ.1 (by rw [h] at hNJ; exact hNJ)
      by_cases hNJ₂ : N = A.J₂
      · exact Or.inl hNJ₂
      · rcases huniq N hNu hNt hNJne hNJ₂ with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    · intro h
      rcases h with rfl | rfl | rfl
      · exact ⟨hJ₂u, A.hJ₂iso J A.hJt A.hJ₂J.symm⟩
      · exact ⟨hM₁u, hcomJ _ hM₁t hM₁J⟩
      · exact ⟨hM₂u, hcomJ _ hM₂t hM₂J⟩
  have hthree : Set.ncard {N : Subgroup G | N ∈ centralizingMembers (𝒞 K) {e.u} ∧
      Commutes N J} = 3 := by
    rw [hset, Set.ncard_eq_three]
    exact ⟨A.J₂, M₁, M₂, fun h => hM₁J₂ h.symm, fun h => hM₂J₂ h.symm, hM₁₂, rfl⟩
  obtain ⟨R₀, hR₀, -, hN⟩ := TWY.exists_corr_commuting S.odd S.five S.inClass S.exact hP1 D hcard
    i hD hJu
  rw [hthree] at hN
  have hexp : D.exp i = f := (D.exp_eq i).resolve_right fun h => (hD i).2 h.1
  have hmod' : twinYModel (p ^ f) .PSU 4 = (.POmegaPlus, 4) := by simp [twinYModel, hmod]
  show D.tag i = (twinYModel (p ^ f) .PSU 4).1 ∧ D.rank i = (twinYModel (p ^ f) .PSU 4).2
  rw [hmod']
  show D.tag i = .POmegaPlus ∧ D.rank i = 4
  have hadm := D.admissible i
  rcases horth with ⟨-, ht, hr⟩ | ⟨-, -, ht, hr⟩ | ⟨-, -, ht, hr⟩ | ⟨-, -, ht, -⟩ |
    ⟨-, -, -, ht, -⟩ | ⟨-, -, -, ht, -⟩
  · exact (TWZ.false_of_small_component hnab S hrow hshape hT clsT e hMF hP1 D hcard i
      (Or.inl ⟨ht, hr⟩)).elim
  · exact (TWZ.false_of_small_component hnab S hrow hshape hT clsT e hMF hP1 D hcard i
      (Or.inr (Or.inl ⟨ht, hr⟩))).elim
  · exact (TWZ.false_of_small_component hnab S hrow hshape hT clsT e hMF hP1 D hcard i
      (Or.inr (Or.inr ⟨ht, hr⟩))).elim
  · exact (layerThree_odd hp2 hq ht hexp hadm hR₀ hN).elim
  · exact ⟨ht, layerThree_plus hp2 hq ht hexp hadm hR₀ hN⟩
  · exact (layerThree_minus hp2 hq ht hexp hadm hR₀ hN).elim

end Rank

end CFSG.ClassicalInvolution.RouteD.TWT4
