module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.StdPos
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Straighten

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

open CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
  CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis


section Decomp

variable {L : Type} [Field L]

theorem canonicalRep_mem_sup_of_mem_kernelWeylGroup {u : WeylGroup Tag.E6}
    (hu : u ∈ kernelWeylGroup (triChar stdChar)) :
    canonicalRep (coxeterSystem Tag.E6) L u ∈
      torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support := by
  have hTM : torusGroup Tag.E6 L ≤ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support :=
    le_sup_left
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, i, hα, rfl⟩ := hx
    have hα' := mem_kernelRoots_stdChar.1 hα
    rw [conj_simple_eq_rootReflection]
    have h1 := SmallQ3.canonicalRep_rootReflection_mem (k := L) hα.1
    have hle : rootSpan Tag.E6 L {w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ),
        -(w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))} ≤ subsystemGroup Tag.E6 L d4Support := by
      rw [subsystemGroup_eq_rootSpan]
      refine rootSpan_mono' ?_
      rintro β (rfl | rfl)
      · exact hα'
      · rw [mem_parabolicRoots_d4Support_iff'] at hα' ⊢
        exact ⟨IsRoot.neg hα'.1, by simp [hα'.2.1], by simp [hα'.2.2]⟩
    exact sup_le_sup_left hle _ h1
  | one =>
    rw [canonicalRep_one]
    exact one_mem _
  | mul x y _ _ hx hy =>
    obtain ⟨k, hk, hkxy⟩ := canonicalRep_mul_mem (R := L) x y
    have hQ : canonicalRep (coxeterSystem Tag.E6) L (x * y) =
        k⁻¹ * (canonicalRep (coxeterSystem Tag.E6) L x *
          canonicalRep (coxeterSystem Tag.E6) L y) := by
      rw [hkxy]
      group
    rw [hQ]
    exact mul_mem (inv_mem (hTM hk)) (mul_mem hx hy)
  | inv x _ hx =>
    obtain ⟨k, hk, hkx⟩ := canonicalRep_inv_eq (K := L) x
    have hQ : canonicalRep (coxeterSystem Tag.E6) L x⁻¹ =
        k⁻¹ * (canonicalRep (coxeterSystem Tag.E6) L x)⁻¹ := by
      rw [hkx]
      group
    rw [hQ]
    exact mul_mem (inv_mem (hTM hk)) (inv_mem hx)


theorem mono_decomp {g : ModGL Tag.E6 L} (hg : g ∈ monomialSubgroup Tag.E6 L)
    {w₀ : WeylGroup Tag.E6}
    (hmaps : MapsRootLines g w₀) (hw₀ : w₀ ∈ charStabilizer (triChar stdChar))
    (hsh : triPairing stdChar (e6Shift w₀) ≠ 0) :
    ∃ ε : ℕ, (ε = 1 ∨ ε = 2) ∧ ∃ m ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support,
      g = m * d4TrialityRep L ^ ε := by
  set c : ZMod 3 := triPairing stdChar (e6Shift w₀) / triPairing stdChar (e6Shift wBeta) with hc
  have hc0 : c ≠ 0 := div_ne_zero hsh triPairing_e6Shift_wBeta
  set ε := c.val with hε
  have hε12 : ε = 1 ∨ ε = 2 := by
    have h1 : ε < 3 := ZMod.val_lt c
    have h2 : ε ≠ 0 := fun h => hc0 ((ZMod.val_eq_zero c).1 h)
    omega
  have hwβpow : wBeta ^ ε ∈ charStabilizer (triChar stdChar) :=
    pow_mem mem_charStabilizer_wBeta ε
  have hsh0 : triPairing stdChar (e6Shift (w₀ * (wBeta ^ ε)⁻¹)) = 0 := by
    have h1 := triPairing_e6Shift_mul hw₀ (wBeta ^ ε)⁻¹
    have h2 : triPairing stdChar (e6Shift (wBeta ^ ε)⁻¹) =
        -triPairing stdChar (e6Shift (wBeta ^ ε)) := by
      have := triPairing_e6Shift_mul hwβpow (wBeta ^ ε)⁻¹
      rw [mul_inv_cancel, e6Shift_one, triPairing_zero] at this
      linear_combination (-1 : ZMod 3) * this
    have h3 : triPairing stdChar (e6Shift (wBeta ^ ε)) =
        (ε : ZMod 3) * triPairing stdChar (e6Shift wBeta) :=
      pow_charStab_shift mem_charStabilizer_wBeta ε
    have h4 : (ε : ZMod 3) = c := ZMod.natCast_zmod_val c
    have h5 : c * triPairing stdChar (e6Shift wBeta) = triPairing stdChar (e6Shift w₀) :=
      div_mul_cancel₀ _ triPairing_e6Shift_wBeta
    rw [h1, h2, h3, h4, h5]
    ring
  have hu : w₀ * (wBeta ^ ε)⁻¹ ∈ kernelWeylGroup (triChar stdChar) :=
    e6Shift_mem_kernelWeylGroup stdChar (mul_mem hw₀ (inv_mem hwβpow)) hsh0
  set u := w₀ * (wBeta ^ ε)⁻¹ with hudef
  have hnu := canonicalRep_mem_sup_of_mem_kernelWeylGroup (L := L) hu
  have hβmono : d4TrialityRep L ∈ monomialSubgroup Tag.E6 L :=
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact weylElt_mem_monomialSubgroup i
  have hβmaps : MapsRootLines (d4TrialityRep L) wBeta := mapsRootLines_list_prod d4TrialityWord
  have hg₂mono : canonicalRep (coxeterSystem Tag.E6) L u * d4TrialityRep L ^ ε ∈
      monomialSubgroup Tag.E6 L :=
    mul_mem (canonicalRep_mem_monomialSubgroup' u) (pow_mem hβmono ε)
  have hg₂maps :
      MapsRootLines (canonicalRep (coxeterSystem Tag.E6) L u * d4TrialityRep L ^ ε) w₀ := by
    have := (mapsRootLines_canonicalRep (R := L) u).mul (E8Lift.mapsRootLines_pow hβmaps ε)
    rwa [show u * wBeta ^ ε = w₀ by rw [hudef]; group] at this
  have hq : g * (canonicalRep (coxeterSystem Tag.E6) L u * d4TrialityRep L ^ ε)⁻¹ ∈
      torusGroup Tag.E6 L := by
    refine E8Lift.mem_torusGroup_of_mapsRootLines_one (mul_mem hg (inv_mem hg₂mono)) ?_
    have := hmaps.mul hg₂maps.inv
    rwa [mul_inv_cancel] at this
  refine ⟨ε, hε12, (g * (canonicalRep (coxeterSystem Tag.E6) L u * d4TrialityRep L ^ ε)⁻¹) *
    canonicalRep (coxeterSystem Tag.E6) L u, mul_mem (Subgroup.mem_sup_left hq) hnu, ?_⟩
  group

end Decomp

end CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4
