module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWAe5Sylow
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7TwoWTr
public import CFSG.ClassicalInvolution.Asc77.AscC25V17

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.Ae5Mod

section Cert


theorem exists_sylow_normW {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g) {c : Y} (hcW : c ∈ W) :
    ∃ T : Subgroup Y, IsSylow2In T (Subgroup.centralizer ({c} : Set Y)) ∧ W ≤ T ∧
      T ≤ Subgroup.normalizer (W : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hPG : Q3CL.PartIHypG (Om R) := hC.partIHypG
  have hd := hc.data
  have htr : ∀ K₁ ∈ Om R, ∀ J ∈ Om R, ∃ a : Y, conjSub a K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  obtain ⟨S₀, hWS₀, hwc, -⟩ := exists_weaklyClosed_conj_of_muIsoS4 hPG htr hd.hW hd.hS4
  have hW2 : IsPGroup 2 W := Asc77.Thompson.isPGroup_of_mem_WSet hd.hW
  have hWc : W ≤ Subgroup.centralizer ({c} : Set Y) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw c hcW)
  obtain ⟨S₂, hS₂, hWS₂⟩ := IsSylow2In.exists_ge hW2 hWc
  obtain ⟨S₁, hSS₁⟩ := hS₂.2.1.exists_le_sylow
  obtain ⟨a, ha⟩ := exists_conjSub_eq_of_sylow S₀ S₁
  have e2 : conjSub a⁻¹ W = W := hwc a⁻¹ (by
    rw [conjSub_le_iff, inv_inv, ha]
    exact hWS₂.trans hSS₁)
  have e3 : conjSub a W = W := by
    conv_lhs => rw [← e2]
    exact conjSub_conjSub_inv a W
  have hS₂N : S₂ ≤ Subgroup.normalizer (W : Set Y) := by
    intro s hs
    have hs₀ : a⁻¹ * s * a ∈ (S₀ : Subgroup Y) := by
      have := hSS₁ hs
      rw [← ha] at this
      exact mem_conjSub_iff.mp this
    have e4 : conjSub (a⁻¹ * s * a) W = W :=
      hwc _ ((conjSub_mono hWS₀).trans (conjSub_eq_self_of_mem hs₀).le)
    have e5 : conjSub s W = W := by
      have : s = a * (a⁻¹ * s * a) * a⁻¹ := by group
      conv_lhs => rw [this]
      rw [conjSub_mul, conjSub_mul, e2, e4, e3]
    exact mem_normalizer_iff_conjSub_eq.mpr e5
  exact ⟨S₂, hS₂, hWS₂, hS₂N⟩

end Cert

theorem exists_mem_inf_of_evenVec {Y : Type} [Group Y] [Finite Y] {C L T : Subgroup Y}
    (hT : IsSylow2In T C) (hLC : L ≤ C) (hn : C ≤ Subgroup.normalizer (L : Set Y))
    (ψ : ↥L →* AEQ 5) {v : Wr 5} (hv : v ∈ evenVec 5) (hvr : mkQ 5 v ∈ ψ.range) :
    ∃ s : ↥L, (s : Y) ∈ T ∧ ψ s = mkQ 5 v := by
  have hS : IsSylow2In (T ⊓ L) L := isSylow2In_inf_of_le_normalizer hT hLC hn
  obtain ⟨s, hs, hsψ⟩ := exists_mem_sylow_evenVec ψ (C25V.sylowOfIsSylow2In hS) hv hvr
  refine ⟨s, ?_, hsψ⟩
  have hs1 : s ∈ (T ⊓ L).subgroupOf L := by
    rw [← C25V.coe_sylowOfIsSylow2In hS]
    exact hs
  exact (Subgroup.mem_subgroupOf.mp hs1).1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam
