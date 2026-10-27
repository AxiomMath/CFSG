module

public import CFSG.GH74.GLS.Stage1.Main.BrG2AsmG
public import CFSG.GH74.GLS.Stage1.Main.BrG2AsmR3
public import CFSG.GH74.GLS.Stage1.Main.BrG2Base

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.IVK.Lifted

open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Main

section Main

theorem g2ShapeBridge_of_facts (hshape : G2SylowShapeFact)
    (hrank : RankG2) : G2ShapeBridge := by
  intro G _ _ z S hcen hT
  obtain ⟨C⟩ := G2Ctx.exists hshape hT
  have hne : RC S z ≠ S := by
    intro h
    have := C.relIndex_RC hcen
    rw [h, Subgroup.relIndex_self] at this
    omega
  have hinv := (baseBridgeG2_of_shape hshape G z S hcen hT).1 hne
  have hrk := hrank G z S hT
  refine ⟨⟨Nat.card C.F₁, Nat.card C.F₂, C.K₁, C.K₂, ?_⟩, C.perfInner hcen⟩
  have hq₁ := C.quat₁ hcen
  have hF₂ : 3 ≤ Nat.card C.F₂ := by
    have h2 : 2 ≤ Nat.card C.F₂ := Finite.one_lt_card
    obtain ⟨r, hr⟩ := C.odd₂
    omega
  by_cases h3 : Nat.card C.F₂ = 3
  · have hq₂ := C.quat₂_three hcen h3
    have hK₁n := C.r3_K₁_normal hcen h3
    have hn₁ : ∀ x ∈ barOf z S, x ∈ normalizer (C.K₁ : Set (CentralizerBar z)) := fun x _ => by
      have := Subgroup.normalizer_eq_top_iff.2 hK₁n
      rw [this]; trivial
    have hn₂ : ∀ x ∈ barOf z S, x ∈ normalizer (C.K₂ : Set (CentralizerBar z)) :=
      fun x hx => C.normalizer_K₂_of hcen (hn₁ x hx)
    refine ⟨C.odd₁, C.odd₂, by have := C.five; omega, ⟨(C.LBar_eq hcen).symm, C.comm, C.inf_card⟩,
      ⟨C.F₁, inferInstance, inferInstance, rfl, ⟨C.e₁⟩⟩, ⟨C.F₂, inferInstance, inferInstance, rfl, ⟨C.e₂⟩⟩,
      C.quat_pair hcen hq₁ hq₂, fun _ => C.r3_clause hcen h3 hq₁, fun h => by omega,
      C.relIndex_RC hcen, C.induced₁ hcen hq₁ hq₂ hn₁ hinv, ?_⟩
    rw [h3]
    exact C.induced₂_three hcen h3 hq₁ hq₂ hn₂ hinv
  · have h5 : 5 ≤ Nat.card C.F₂ := by
      obtain ⟨r, hr⟩ := C.odd₂
      omega
    have hq₂ := C.quat₂ hcen h5
    have hn₁ := C.T_normalizes hcen h5 hq₁ hq₂ hrk hinv
    have hn₂ : ∀ x ∈ barOf z S, x ∈ normalizer (C.K₂ : Set (CentralizerBar z)) :=
      fun x hx => C.normalizer_K₂_of hcen (hn₁ x hx)
    obtain ⟨ζ, hζ₁, hζ₂, hζo, hζT, hT'⟩ := C.exists_zeta hcen
    have hcen' := C.centralizer_K hcen hζ₁ hζ₂ hζo hT'
    have hzeta := C.zbar_eq hcen hT'
    refine ⟨C.odd₁, C.odd₂, by have := C.five; omega, ⟨(C.LBar_eq hcen).symm, C.comm, C.inf_card⟩,
      ⟨C.F₁, inferInstance, inferInstance, rfl, ⟨C.e₁⟩⟩, ⟨C.F₂, inferInstance, inferInstance, rfl, ⟨C.e₂⟩⟩,
      C.quat_pair hcen hq₁ hq₂, fun h => absurd h h3, fun _ => ⟨?_, ?_⟩,
      C.relIndex_RC hcen, C.induced₁ hcen hq₁ hq₂ hn₁ hinv, C.induced₂ hcen h5 hq₁ hq₂ hn₂ hinv⟩
    · exact C.WBar_eq_zpowers hcen h5 hζ₁ hζo hcen' hzeta
    · exact C.generalizedFitting_eq hcen h5 hζ₁ hcen'

end Main

end CFSG.GH74.GLS.Stage1.Main
