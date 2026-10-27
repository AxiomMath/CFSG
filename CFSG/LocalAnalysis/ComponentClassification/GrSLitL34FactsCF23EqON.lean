module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23Eq
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSpMult
public import CFSG.Sporadic.ONOddCore.Involutions
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23JSide

public section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.CatFactsL4U4.OutInv

theorem exists_conj_of_ON
    {X : Type*} [Group X] (e : X ≃* Blueprint.NativeSporadic.ON) {u v : X}
    (hu : orderOf u = 2) (hv : orderOf v = 2) : ∃ g : X, g * u * g⁻¹ = v := by
  set φ := e.trans ONSchreier.onEquivPv with hφ
  have hu' : orderOf ((φ u : ↥ONSchreier.Pv) : Equiv.Perm (Fin ONSchreier.N)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hu]
  have hv' : orderOf ((φ v : ↥ONSchreier.Pv) : Equiv.Perm (Fin ONSchreier.N)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hv]
  obtain ⟨g₁, hg₁, e₁⟩ := Sporadic.ONOddCore.cti_on_all_involutions_conjugate _ (φ u).2 hu'
  obtain ⟨g₂, hg₂, e₂⟩ := Sporadic.ONOddCore.cti_on_all_involutions_conjugate _ (φ v).2 hv'
  refine ⟨φ.symm ⟨g₂ * g₁⁻¹, mul_mem hg₂ (inv_mem hg₁)⟩, φ.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e₁, e₂]
  group

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

theorem center_eq_bot_of_ON (hSM : SporadicMultTwoPartInput)
    (hON : Nonempty (LK h ≃* Blueprint.NativeSporadic.ON)) : center (OddBar h.K) = ⊥ := by
  have hodd := hSM.2 (OddBar h.K) h.isQuasisimple_K hON
  rw [eq_bot_iff]
  intro c hc
  rw [mem_bot]
  have h1 : orderOf c ∣ Nat.card (center (OddBar h.K)) := by
    rw [← Subgroup.orderOf_mk c hc]
    exact orderOf_dvd_natCard _
  exact CF23Diag.eq_one_of_mem_center_of_odd hc (Odd.of_dvd_nat hodd h1)

theorem fus23ConclW_of_ON
    (hL : Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2) (hSM : SporadicMultTwoPartInput)
    (hαN : phi hKa (abar h) ∈ NL hKa)
    (hON : Nonempty (↥(NL hKa) ≃* Blueprint.NativeSporadic.ON)) : h.Fus23ConclW := by
  obtain ⟨e⟩ := hON
  obtain ⟨eN⟩ := nonempty_NL_equiv hKa
  have hZK : center (OddBar h.K) = ⊥ := center_eq_bot_of_ON hSM ⟨eN.symm.trans e⟩
  obtain ⟨-, -, -, d, -, -, -, hdD, -, hd2, hdx, hdP⟩ := exists_fixed_D h hL
  obtain ⟨hζJ, hζ2, hcomm, hζα⟩ := zeta_facts hKa hZK hdD hd2 hdP
  set ζ := phi hKa (wbarMk h.B ⟨d, K_le_W h (D_le_K hKa hdD)⟩) with hζ
  have hα2 : phi hKa (abar h) * phi hKa (abar h) = 1 := by
    rw [← map_mul, abar_mul_self, map_one]
  have hζN : ζ ∈ NL hKa := Jhat_le_NL hKa hζJ
  have hu : orderOf (⟨phi hKa (abar h), hαN⟩ : ↥(NL hKa)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_phi_abar' hKa
  have hv : orderOf ((⟨phi hKa (abar h), hαN⟩ : ↥(NL hKa)) * ⟨ζ, hζN⟩) = 2 := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact orderOf_mul_eq_two hα2 hζ2 hcomm hζα
  obtain ⟨g, hg⟩ := exists_conj_of_ON e hu hv
  refine fus23ConclW_of_NL hKa hZK hdD hd2 hdx hdP (γ := ((g : ↥(GAut hKa)))⁻¹)
    (inv_mem g.2) ?_
  rw [inv_inv]
  have := congrArg (fun y : ↥(NL hKa) => (y : ↥(GAut hKa))) hg
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this

end CFSG.ComponentClassification.GSThmB.CF23L34
