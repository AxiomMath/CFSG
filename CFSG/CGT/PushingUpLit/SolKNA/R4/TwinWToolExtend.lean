module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinWToolBasic
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEApply

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace WTool

section Conj

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem centralizersSylowPairsW_conj (hΩ : ConjInvariant Ω) {K W H : Subgroup G}
    (h : CentralizersSylowPairsW Ω K W H) {c : G} (hc : c ∈ H) :
    CentralizersSylowPairsW Ω (conjSub c K) (conjSub c W) H := by
  intro L hL J hJ R₁ R₂ hR₁ hR₁L hR₂ hR₂J hcomm a haR haW ha1 ha2
  have hL' : conjSub c⁻¹ L ∈ twinSet Ω K := by
    have := twinSet_conj hΩ hL c⁻¹
    rwa [conjSub_inv_conjSub] at this
  have hJ' : conjSub c⁻¹ J ∈ KPerp Ω (conjSub c⁻¹ L) := KPerp_conj hΩ hJ c⁻¹
  have hcomm' : Commutes (conjSub c⁻¹ R₁) (conjSub c⁻¹ R₂) ∨ conjSub c⁻¹ R₂ = conjSub c⁻¹ R₁ := by
    rcases hcomm with h1 | h1
    · exact Or.inl (h1.conjSub c⁻¹)
    · exact Or.inr (by rw [h1])
  have haR' : c⁻¹ * a * c ∈ conjSub c⁻¹ R₁ ⊔ conjSub c⁻¹ R₂ := by
    have := conj_mem_conjSub (n := c⁻¹) haR
    rwa [conjSub_sup, inv_inv] at this
  have haW' : c⁻¹ * a * c ∈ W := mem_conjSub_iff.mp haW
  have ha1' : c⁻¹ * a * c ≠ 1 := by
    intro h1
    apply ha1
    have : a = c * (c⁻¹ * a * c) * c⁻¹ := by group
    rw [this, h1]
    group
  have ha2' : (c⁻¹ * a * c) * (c⁻¹ * a * c) = 1 := by
    calc (c⁻¹ * a * c) * (c⁻¹ * a * c) = c⁻¹ * (a * a) * c := by group
      _ = 1 := by rw [ha2]; group
  have hC := h _ hL' _ hJ' (conjSub c⁻¹ R₁) (conjSub c⁻¹ R₂) (RSet.conj hΩ hR₁ c⁻¹)
    (conjSub_mono hR₁L) (RSet.conj hΩ hR₂ c⁻¹) (conjSub_mono hR₂J) hcomm' _ haR' haW' ha1' ha2'
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hx' : c⁻¹ * x * c ∈ Subgroup.centralizer ({c⁻¹ * a * c} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c⁻¹ * x * c * (c⁻¹ * a * c) = c⁻¹ * (x * a) * c := by group
      _ = c⁻¹ * (a * x) * c := by rw [hx]
      _ = c⁻¹ * a * c * (c⁻¹ * x * c) := by group
  have h2 := H.mul_mem (H.mul_mem hc (hC hx')) (H.inv_mem hc)
  simpa [mul_assoc] using h2

theorem centralizersSylowPairsW_congr {K K' W H : Subgroup G} (h : twinSet Ω K' = twinSet Ω K) :
    CentralizersSylowPairsW Ω K' W H ↔ CentralizersSylowPairsW Ω K W H := by
  unfold CentralizersSylowPairsW
  rw [h]

variable [Finite G]

theorem centralizer_le_of_cent (hΩ : HypOmegaGen Ω) {K W H : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) (hKW : K ⊓ W ∈ USet Ω) (h : CentralizersSylowPairsW Ω K W H) :
    Subgroup.centralizer ({z} : Set G) ≤ H := by
  obtain ⟨R, hRΩ, J, hJ, hRJ, hUR, -, -, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hKW
  have hJK : J = K := Sec6Gen.eq_of_mem_USet hΩ hKW hJ hK (hUR.trans hRJ.1) inf_le_left
  rw [hJK] at hRJ
  have hzR : z ∈ R := Sec6Gen.mem_of_isSylow2In hz hRJ
  have hzW : z ∈ W := (mem_of_mem_USet_of_le hΩ hz hKW inf_le_left).2
  exact h K (mem_twinSet_self hK hz) K (Set.mem_insert _ _) R R hRΩ hRJ.1 hRΩ hRJ.1 (Or.inr rfl) z
    (Subgroup.mem_sup_left hzR) hzW hz.ne_one hz.sq

end Conj

end WTool

namespace ThmE

section Extend


theorem extendR_of_four_le {r : ℕ} (hr : 4 ≤ r) (n : ℕ) : ExtendR r n := by
  intro Y _ _ R S t h K H W hK hW hH x _ hKWx
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := h.hyp
  have hKΩ : K ∈ Ω := hK
  obtain ⟨S₀, R₀, hR₀, hR₀S, hWΩ, hWS, -, -⟩ := hW
  have hquat : ∀ L ∈ Ω, ∃ P : Subgroup Y, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
    rintro _ ⟨g', rfl⟩
    refine ⟨conjSub g' ((S : Subgroup R).map R.subtype), h.datum.sylow_core.conj g', ⟨?_⟩⟩
    exact (Subgroup.equivMapOfInjective _ (MulAut.conj g').toMonoidHom
      (MulAut.conj g').injective).symm.trans
      ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans
        h.quat.some)
  have h16 := WTool.sylow16_of_quat hr hΩ hquat
  have hKW : K ⊓ W ∈ USet Ω := by
    refine WTool.inf_mem_USet_of_card hΩ hWΩ hWS hKΩ ?_
    have h1 := Subgroup.card_le_of_le (le_inf hR₀.1 hR₀S)
    have h2 := h16 K hKΩ R₀ hR₀
    omega
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hKΩ
  have hzW : z ∈ W := (WTool.mem_of_mem_USet_of_le hΩ hz hKW inf_le_left).2
  have hzWx : z ∈ conjSub x W := (WTool.mem_of_mem_USet_of_le hΩ hz hKWx inf_le_left).2
  have hWx : conjSub x W ∈ WSet Ω := WSet.conj hΩ.conjInvariant hWΩ x
  obtain ⟨c, hcz, hc⟩ := WTool.exists_conj_of_mem_mem hΩ h16 hWΩ hWx hzW hzWx
  have hcH : c ∈ H := WTool.centralizer_le_of_cent hΩ hKΩ hz hKW hH.cent hcz
  have hcz' : c * z * c⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hcz
    rw [hcz, mul_assoc, mul_inv_cancel, mul_one]
  have hK' : conjSub c K ∈ twinSet Ω K :=
    ⟨hΩ.conjInvariant c K hKΩ, z, hz, by simpa [hcz'] using hz.conj c⟩
  have h1 := WTool.centralizersSylowPairsW_conj hΩ.conjInvariant hH.cent hcH
  rw [hc] at h1
  exact (WTool.centralizersSylowPairsW_congr (twinSet_eq_of_mem_twinSet hz hK')).mp h1

end Extend

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
