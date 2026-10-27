module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinWToolBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinUActsPfCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.GoodLift
public import CFSG.ClassicalInvolution.Q3.Q3T7W21B02
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Mu

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc


section Clique

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)}

theorem mul_four_eq_one_of_twoGroup (hP : Q3CL.PartIHypG Ω) {K₀ : Subgroup Y} (hK₀ : K₀ ∈ Ω)
    (hne : dComp Ω K₀ ≠ dstarComp Ω K₀) {M₁ M₂ M₃ M₄ : Subgroup Y} {z₁ z₂ z₃ z₄ : Y}
    (hM₁ : M₁ ∈ Ω) (hM₂ : M₂ ∈ Ω) (hM₃ : M₃ ∈ Ω) (hM₄ : M₄ ∈ Ω)
    (hz₁ : IsUniqueInvolution M₁ z₁) (hz₂ : IsUniqueInvolution M₂ z₂)
    (hz₃ : IsUniqueInvolution M₃ z₃) (hz₄ : IsUniqueInvolution M₄ z₄)
    (h₁₂ : M₂ ∈ omegaNbr Ω M₁) (h₁₃ : M₃ ∈ omegaNbr Ω M₁) (h₂₃ : M₃ ∈ omegaNbr Ω M₂)
    (h₁₄ : M₄ ∈ omegaNbr Ω M₁) (h₂₄ : M₄ ≠ M₂) (h₃₄ : M₄ ≠ M₃) {B : Subgroup Y}
    (hB : IsPGroup 2 B) (c₁ : 2 < Nat.card ↥(M₁ ⊓ B)) (c₂ : 2 < Nat.card ↥(M₂ ⊓ B))
    (c₃ : 2 < Nat.card ↥(M₃ ⊓ B)) (c₄ : 2 < Nat.card ↥(M₄ ⊓ B)) : z₁ * z₂ * z₃ * z₄ = 1 := by
  have hΩ : HypOmegaGen Ω := hP.hyp
  obtain ⟨S, hBS⟩ := hB.exists_le_sylow
  obtain ⟨η, hη, hηinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hWmem : (⨆ U ∈ η, U : Subgroup Y) ∈ WSet Ω := ⟨η, ⟨S, hη, hηinv⟩, rfl⟩
  have hWS : (⨆ U ∈ η, U : Subgroup Y) ≤ (S : Subgroup Y) :=
    iSup₂_le fun U hU => (hη.1 hU).2
  set W : Subgroup Y := ⨆ U ∈ η, U with hWdef
  have hin : ∀ {M : Subgroup Y} {x : Y}, M ∈ Ω → IsUniqueInvolution M x →
      2 < Nat.card ↥(M ⊓ B) → x ∈ W := by
    intro M x hM hx hc
    have h2 : 2 < Nat.card ↥(M ⊓ (S : Subgroup Y)) :=
      lt_of_lt_of_le hc (Subgroup.card_le_of_le (inf_le_inf_left M hBS))
    have hU := WTool.inf_mem_USet_of_card hΩ hWmem hWS hM h2
    exact (WTool.mem_of_mem_USet_of_le hΩ hx hU inf_le_left).2
  have c := Q3CL.T8.ctxOf hP hWmem
  have hnc := Q3T6.Mu.thompsonGraphAll hP hK₀ hne hWmem
  obtain ⟨ρ₁, hρ₁⟩ := TL4.exists_rep_of_involution_mem_gen c hP.cls hM₁ hz₁ (hin hM₁ hz₁ c₁)
  obtain ⟨ρ₂, hρ₂⟩ := TL4.exists_rep_of_involution_mem_gen c hP.cls hM₂ hz₂ (hin hM₂ hz₂ c₂)
  obtain ⟨ρ₃, hρ₃⟩ := TL4.exists_rep_of_involution_mem_gen c hP.cls hM₃ hz₃ (hin hM₃ hz₃ c₃)
  obtain ⟨ρ₄, hρ₄⟩ := TL4.exists_rep_of_involution_mem_gen c hP.cls hM₄ hz₄ (hin hM₄ hz₄ c₄)
  exact c.mul_four_eq_one hP.cls hnc ρ₁ ρ₂ ρ₃ ρ₄ (by rw [hρ₁, hρ₂]; exact h₁₂)
    (by rw [hρ₁, hρ₃]; exact h₁₃) (by rw [hρ₂, hρ₃]; exact h₂₃) (by rw [hρ₁, hρ₄]; exact h₁₄)
    (by rw [hρ₂, hρ₄]; exact h₂₄) (by rw [hρ₃, hρ₄]; exact h₃₄) (by rw [hρ₁]; exact hz₁)
    (by rw [hρ₂]; exact hz₂) (by rw [hρ₃]; exact hz₃) (by rw [hρ₄]; exact hz₄)

theorem conjSub_mem_omegaOfSet_twin (hΩ : ConjInvariant Ω) {K J : Subgroup Y}
    (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) {m : Y} (hm : conjSub m K = K) :
    conjSub m J ∈ omegaOfSet Ω (twinSet Ω K) := by
  refine ⟨hΩ m J hJ.1, fun L hL => ?_⟩
  have hm' : conjSub m⁻¹ K = K := by
    have := conjSub_inv_conjSub m K
    rwa [hm] at this
  have hL' : conjSub m⁻¹ L ∈ twinSet Ω K := by
    have := twinSet_conj hΩ hL m⁻¹
    rwa [hm'] at this
  have h := omegaNbr_conj hΩ (hJ.2 _ hL') m
  rwa [conjSub_conjSub_inv] at h

theorem not_mem_twinSet_of_mem_omegaOfSet {K J : Subgroup Y} (hK : K ∈ Ω)
    {z : Y} (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) :
    J ∉ twinSet Ω K := fun h => (hJ.2 J h).2.1 rfl

end Clique

end CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15
