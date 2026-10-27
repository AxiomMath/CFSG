module

public import CFSG.ClassicalInvolution.Asc77.AscAETFinal
public import CFSG.ClassicalInvolution.SmallCases.NDBCRes
import CFSG.ClassicalInvolution.SmallCases.NDBC0
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.ModOApi
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
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
public import CFSG.ClassicalInvolution.Asc77.AscT8Setup
public import CFSG.ClassicalInvolution.AschTight.Sec7L713E
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

section Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem exists_twinShapeCtx_weak (X : XCtx p f Ω z) (hD : TwinShapeData X.D) {T : Subgroup G}
    (hT : T ∈ Ω) (hTz : IsClassicalMember p f T z) (hTK : T ≠ X.K) :
    ∃ C : TwinShapeCtx p f Ω z, Nonempty C.Spec := by
  obtain ⟨hcard, a₀, a₁, a₂, -, -, -, -, -, -, -, hlist⟩ := hD
  have hA₁ : ¬ (X.D.tag a₁ = .PSL ∧ X.D.rank a₁ = 2) := by
    rintro ⟨h1, h2⟩
    rcases hlist with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [h1] at h
      exact absurd h (by decide)
    · omega
    · rw [h1] at h
      exact absurd h (by decide)
    · rw [h1] at h
      exact absurd h (by decide)
    · rw [h1] at h
      exact absurd h (by decide)
    · rw [h1] at h
      exact absurd h (by decide)
  have hzC := XCtx.hzC z
  obtain ⟨j, hj, hjK⟩ := X.exists_A1_of_K
  obtain ⟨j', hj', hjT⟩ := X.exists_A1_of_member hT hTz
  have hzT : oddQuotMk z ⟨z, hzC⟩ ∈ (X.psi j').range := by
    rw [← hjT]
    exact oddQuotMk_mem_modOdd hTz.mem hzC
  have hne : j ≠ j' := by
    intro h
    apply hTK
    refine (Cover.eq_of_modOdd_eq X.K_cl hTz ?_).symm
    rw [← X.exactCore_K, hjK, hjT, h]
  let C : TwinShapeCtx p f Ω z :=
    { toXCtx := X
      i₀ := j
      i₁ := a₁
      i₂ := j'
      ne₀₁ := fun h => hA₁ (by rw [← h]; exact hj)
      ne₁₂ := fun h => hA₁ (by rw [h]; exact hj')
      ne₀₂ := hne
      tag₀ := hj.1
      rank₀ := hj.2
      tag₂ := hj'.1
      rank₂ := hj'.2
      listed := hlist
      extra := extra_of_card_three hcard (fun h => hA₁ (by rw [← h]; exact hj))
        (fun h => hA₁ (by rw [h]; exact hj')) hne }
  exact ⟨C, ⟨⟨hjK, hzT⟩⟩⟩

end Ctx

section AEmpty

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_omegaOfSet_nonempty_of_twinShapeWeak (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} {z : G} (hΩ : HypOmegaMod p f (𝒞 K)) (hz : IsClassicalMember p f K z)
    (hshape : TwinShapeWeak p f K z) :
    ∃ M ∈ 𝒞 K, (omegaOfSet (𝒞 K) (twinSet (𝒞 K) M)).Nonempty := by
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  obtain ⟨⟨D, hD⟩, T, hT, hTK, hTz⟩ := hshape
  let X : XCtx p f (𝒞 K) z :=
    { K := K, hK := CoreAssembly.mem_conjClass_self K, hKz := hKz, hΩ := hΩ, hp := hp2,
      hq := hq, D := D }
  obtain ⟨C, ⟨S⟩⟩ := exists_twinShapeCtx_weak X hD hT hTz hTK
  obtain ⟨L⟩ := C.exists_lift S
  have fd := L.frameData S
  exact ⟨L.K₁, L.hK₁, L.J, fd.hJ⟩

variable (p f) in
@[expose] def AEmptyTwinWeak : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → TwinShapeWeak p f K z →
        ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M

theorem aEmptyTwinWeak_proved (hΩall : HypOmegaModAll p f) : AEmptyTwinWeak p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hshape M hM
  have hΩK : HypOmegaMod p f (𝒞 K) := hΩall G hnab hp2 hq K z hz hBelow
  have hall : ∀ J ∈ 𝒞 K, ∃ g : G, conjSub g K = J := by
    rintro J ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_mul_self_eq_one hKz.sq hKz.ne_one
  have hA : AEmpty (𝒞 K) K := by
    by_contra hn
    obtain ⟨J, zK, zJ, hv⟩ := T3.not_aEmpty_iff.mp hn
    obtain ⟨M₀, hM₀, L₀, hL₀⟩ :=
      exists_omegaOfSet_nonempty_of_twinShapeWeak hp2 hq hΩK hz hshape
    obtain ⟨h, hh⟩ := hall L₀ hL₀.1
    have hKW : K ∈ omegaOfSet (𝒞 K) (twinSet (𝒞 K) (conjSub h⁻¹ M₀)) := by
      have := AscAET.omegaOfSet_conj hΩK.conjInvariant hL₀ h⁻¹
      rwa [← hh, conjSub_inv_conjSub] at this
    have hM'Ω : conjSub h⁻¹ M₀ ∈ 𝒞 K := hΩK.conjInvariant h⁻¹ M₀ hM₀
    obtain ⟨g, hg⟩ := hall _ hM'Ω
    have hv' := hv.conj hΩK.conjInvariant g
    rw [hg] at hv'
    obtain ⟨J', zJ', hv'', hMc, hJc⟩ :=
      AscAET.exists_weak_transfer hp2 hq hΩK hM'Ω hv' hKW hKz
    obtain ⟨D₀, hD₀⟩ := hshape.1
    exact AscAET.false_of_aViol_twinShape hp2 hq hΩK hc2 D₀ hD₀ hM'Ω hv'' hMc hJc
  exact T3.aEmpty_forall_of_transitive' hΩK.conjInvariant hall hA M hM

end AEmpty

end CFSG.ClassicalInvolution.NDB
