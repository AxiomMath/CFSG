module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TFix
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TCases

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10 CFSG.ComponentClassification.GSThmB.P29.A10
open CFSG.ComponentClassification.GSThmB.Eight2

variable {X : Type} [Group X] [Finite X]

private theorem sixtyfour_dvd {n : ℕ} (hn : 10 ≤ n) : 64 ∣ n.factorial / 2 := by
  obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hn
  rw [hk, show (10 : ℕ).factorial = 2 * (64 * 28350) by decide, mul_assoc,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), mul_assoc]
  exact Dvd.intro _ rfl

namespace Ctx.PropBData

variable {c : Ctx X} (d : c.PropBData)

theorem z'_center : orderOf d.z' = 2 ∧ ∀ u ∈ c.s.h.secB0 c.s.y, u * d.z' = d.z' * u := by
  refine ⟨orderOf_eq_prime (by rw [pow_two]; exact d.z'_mul_self) fun h => c.Z.hz1 ?_,
    fun u hu => d.comm_S0 c.Z.z (Set.mem_insert_of_mem _ rfl) u
      (mem_inf.mpr ⟨c.s.h.B_le_S (c.s.h.secB0_le_B c.s.y hu), le_normalizer hu⟩)⟩
  have h1 : c.Z.z = d.g * d.z' * d.g⁻¹ := by
    simp only [PropBData.z']
    group
  rw [h1, h, mul_one, mul_inv_cancel]

theorem false_of_case_ii
    (hcore : EvenPump.EvenAltPumpInput) (hHN : EvenPump.HNPumpInput)
    (hHNfix : HNFixedComponents) (hz : d.z' ∈ c.s.h.secB0 c.s.y) : False := by
  obtain ⟨hz2, hzZ⟩ := d.z'_center
  have hCb : centralizer ((zpowers d.z' : Subgroup X) : Set X) =
      centralizer ({d.z'} : Set X) :=
    UnbalancedLayer.centralizer_zpowers_eq d.z'
  have hFn : c.propMCfg.B₀ ≤ normalizer ((zpowers d.z' : Subgroup X) : Set X) := fun u hu =>
    centralizer_le_normalizer _ (by rw [hCb]; exact mem_centralizer_singleton_iff.mpr (hzZ u hu))
  obtain ⟨M, hMC, hMpc, hLM, -, -, -⟩ :=
    c.propMCfg.exists_unique_component (zpowers_le.mpr hz) hFn
  rw [hCb] at hMC hMpc
  obtain ⟨n, -, hn, ⟨eM⟩⟩ := c.propMCfg.component_alt hcore hHN hHNfix hz hz2 hzZ hMC hMpc hLM
  have hCz : conjugate (centralizer ({d.z'} : Set X)) d.g⁻¹ =
      centralizer ({c.Z.z} : Set X) := by
    rw [conjugate_centralizer_singleton]
    congr 2
    simp only [PropBData.z', inv_inv]
    group
  obtain ⟨hYC, hYpc⟩ := Six.isPComponent_conjugate hMC hMpc d.g⁻¹
  rw [hCz] at hYC hYpc
  let eY : ↥M ≃* ↥(conjugate M d.g⁻¹) :=
    M.equivMapOfInjective (MulAut.conj d.g⁻¹⁻¹).toMonoidHom (MulAut.conj d.g⁻¹⁻¹).injective
  let eYq : ↥(conjugate M d.g⁻¹) ⧸ pPrimeCore 2 ↥(conjugate M d.g⁻¹) ≃*
      alternatingGroup (Fin n) :=
    (QuotientGroup.congr (pPrimeCore 2 ↥M) (pPrimeCore 2 ↥(conjugate M d.g⁻¹)) eY
      (pPrimeCore_map_iso 2 eY)).symm.trans eM
  have hYq := isQuasisimple_of_isPComponent hYC hYpc
  have h64 : 64 ∣ Nat.card (↥(conjugate M d.g⁻¹) ⧸ Open.fusionZStar ↥(conjugate M d.g⁻¹)) := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [EvenPump.fusionZStar_eq_of_alt (by omega) eYq, Nat.card_congr eYq.toEquiv,
      Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    exact sixtyfour_dvd hn
  obtain ⟨Js, hJsC, hJspc, hJ0, hYJs, hx, -⟩ := c.exists_Jstar
    (le_layerIn_of_isPComponent hYC hYpc) (isPerfect_of_isPComponent hYC hYpc) hYq h64
  obtain rfl : Js = conjugate M d.g⁻¹ :=
    eq_of_le_of_le_of_not_isSolvable hJsC hYC hJspc hYpc hYJs le_rfl
      (not_isSolvable_of_isQuasisimple hYq)
  exact Ctx.JstarData.false ⟨_, hJsC, hJspc, hJ0, hx, n, by omega, ⟨eYq⟩⟩

end Ctx.PropBData

end CFSG.ComponentClassification.GSThmB.A10T
