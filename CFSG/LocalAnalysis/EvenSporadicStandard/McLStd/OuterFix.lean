module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuter

public section

namespace CFSG.EvenSporadicStandard.McLStd

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd.Spor

theorem card_fixSub_outer_mcl
    {Y : Type} [Group Y] (e : Y ≃* NativeSporadic.McL)
    (α : MulAut Y) (hα2 : α * α = 1) (hα : α ∉ inner Y) : Nat.card (fixSub α) = 7920 := by
  set θ : Y ≃* mclP := e.trans mclPermEquiv
  set β : MulAut mclP := transportAut θ α
  have hβ2 : β * β = 1 := transportAut_mul_self θ hα2
  have hβ : β ∉ inner mclP := transportAut_not_mem_inner θ hα
  obtain ⟨x, hxR, hx⟩ := mcl_autModel.surj β
  have hxP : x ∉ mclP := by
    intro hxP
    apply hβ
    refine ⟨⟨x, hxP⟩, MulEquiv.ext fun p => Subtype.ext ?_⟩
    rw [hx p]
    rfl
  have hx2 : x * x = 1 := by
    apply mcl_autModel.inj (x * x) (mclR.mul_mem hxR hxR)
    intro p hp
    have h := congrArg (fun φ : MulAut mclP => ((φ ⟨p, hp⟩ : mclP) : Equiv.Perm (Fin 275))) hβ2
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    rw [hx, hx] at h
    calc x * x * p = x * (x * p * x⁻¹) * x⁻¹ * (x * x) := by group
      _ = p * (x * x) := by rw [h]
  have hx1 : x ≠ 1 := fun h1 => hxP (h1 ▸ one_mem _)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  obtain ⟨-, -, -, -, hcover, -, -, -⟩ := mcl_involution_centralizers
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover x hxR hxo
  simp only [mclRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hxu : x = g * mclU1 * g⁻¹ := by
    rcases hr with rfl | rfl
    · exfalso
      dsimp only at hxg
      apply hxP
      rw [hxg]
      exact mclP.mul_mem (mclP.mul_mem hg mclT0_facts.1) (mclP.inv_mem hg)
    · dsimp only at hxg
      exact hxg
  have hfix := map_fixSub_conjOn mclP β x hx
  rw [hxu, centralizerIn_conj mclP hg] at hfix
  have eC : ↥(fixSub α) ≃* ↥mclC1 :=
    ((fixSubTransportEquiv θ α).trans ((((fixSub β).equivMapOfInjective mclP.subtype
      mclP.subtype_injective).trans (MulEquiv.subgroupCongr hfix)))).trans
        (conjEquiv mclC1 g).symm
  obtain ⟨-, -, hcard⟩ := mclC1_simple
  rw [Nat.card_congr eC.toEquiv]
  exact hcard

end CFSG.EvenSporadicStandard.McLStd
