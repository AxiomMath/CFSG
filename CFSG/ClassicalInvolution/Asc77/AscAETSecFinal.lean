module

public import CFSG.ClassicalInvolution.Asc77.AscAETSecViol
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinCtx
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedClass
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedQuot
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Section
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscIHSectG
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC5
public import CFSG.ClassicalInvolution.Asc77.AscT7K11
public import CFSG.ClassicalInvolution.Asc77.AscT7L1
public import CFSG.ClassicalInvolution.Asc77.AscThmABasic
public import CFSG.ClassicalInvolution.Asc77.TwinLookup
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Main
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.Models.TwistedPairs

public section

namespace CFSG.ClassicalInvolution.Asc77.AscAET

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.Assembly.LowTwoRank

section Tags

variable {p f : ℕ} [Fact p.Prime]

theorem tag_ne_of_twinShapeData {X : Type} [Group X] {Φ : Set (Subgroup X)}
    {D : LieSystemData p f X Φ} (hD : TwinShapeData D) (i : Fin D.card) :
    D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
  obtain ⟨hcard, i₀, i₁, i₂, h01, h12, h02, ht₀, -, ht₂, -, hL⟩ := hD
  rcases eq_cases_of_card_three hcard h01 h12 h02 i with rfl | rfl | rfl
  · rw [ht₀]
    exact ⟨by decide, by decide⟩
  · rcases hL with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
      exact ⟨by decide, by decide⟩
  · rw [ht₂]
    exact ⟨by decide, by decide⟩

end Tags

section Final

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem false_of_aViol_twinShape (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (D₀ : LocalLieSystemAt p f (exactFamily Ω c) c)
    (hD₀ : TwinShapeData D₀) {M J : Subgroup G} {zM zJ : G} (hM : M ∈ Ω)
    (hv : AViol Ω M J zM zJ) (hMc : c ∈ trivialOnQuot M) (hJc : c ∈ trivialOnQuot J) :
    False := by
  obtain ⟨zK, zL, hv'⟩ := exists_aViol_exactPair hp hq hΩ hc2 hM hv hMc hJc
  have hΛ : HypOmegaMod p f
      (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c)) :=
    hypOmegaMod_restrictFamily_congr (centMembers_exactFamily Ω c).symm rfl
      (hypOmegaMod_exactPair hp hq hΩ hc2)
  have hKt : M ∈ tqMembers Ω c := ⟨hM, hMc⟩
  have hKcm : exactCore c M ∈ centralizingMembers (exactFamily Ω c) {c} :=
    ⟨exactCore_mem_exactFamily hKt, exactCore_le_centralizer c M⟩
  have hKY : exactCore c M ≤ exLayer Ω c := le_centLayer hKcm
  have hK : (exactCore c M).subgroupOf (exLayer Ω c) ∈
      restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c) :=
    subgroupOf_mem_restrictFamily hKcm hKY
  obtain ⟨a, hQ⟩ := T3Typed.quotViol_of_aViol hp hq hΛ hK hv'
  have hs : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨M, hKt⟩
  let D : OmegaLie p f (secFam Ω c) := LieSystemData.toOmegaLie D₀ (omegaGen_secFam hs)
  have hΦ : HypOmegaMod p f (secFam Ω c) := hypOmegaMod_secFam hp hq hΩ hc2
  obtain ⟨i, R, S, hR, hS, hKR, hJS⟩ := T3Typed.QuotViol.exists_components D hQ
  rw [hKR, hJS] at hQ
  exact T3Typed.QuotViol.false_of_classical hp hq hΦ D (tag_ne_of_twinShapeData hD₀ i).1
    (tag_ne_of_twinShapeData hD₀ i).2 hR hS hQ

end Final

end CFSG.ClassicalInvolution.Asc77.AscAET
