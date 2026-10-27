module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux11
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux9

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8 CFSG.RankThree.PartOne.KE
open CFSG.ClassicalInvolution.ModelFacts.Levi

set_option linter.unusedSectionVars false


section Generic

variable {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]

theorem Setup.scalClosed_of_torus (S : Setup K L)
    (hd : ∀ a : K, a ≠ 0 → ∃ (d : ModGL Tag.E8 L) (Xbar : Subgroup (ModGL Tag.E8 L)),
      S.XLink Xbar ∧ d ∈ Xbar ∧ d ∈ adjointGroup Tag.E8 L ∧ S.n * Frob S.Fr d * S.n⁻¹ = d ∧
      ∀ q ∈ Qθ Tag.E8 L, d * q * d⁻¹ ∈ Qθ Tag.E8 L ∧
        heisCoord Tag.E8 L (d * q * d⁻¹) = algebraMap K L a • heisCoord Tag.E8 L q) :
    S.ScalClosed := by
  intro a ha
  obtain ⟨d, Xbar, hX, hdX, hdA, hσ, hsc⟩ := hd a ha
  obtain ⟨l₀, hl₀H, hl₀⟩ := ratop_of_sfixed S.Fr S.hFr S.hbij S.hh S.hlang hX hdA hdX hσ
  refine ⟨l₀, hl₀H, fun q hq => ?_⟩
  have hq' : S.h⁻¹ * baseChangeGL (algebraMap K L) q * S.h ∈ Qθ Tag.E8 L := hq
  have e : S.h⁻¹ * baseChangeGL (algebraMap K L) (l₀ * q * l₀⁻¹) * S.h =
      d * (S.h⁻¹ * baseChangeGL (algebraMap K L) q * S.h) * d⁻¹ := by
    rw [map_mul, map_mul, map_inv, hl₀]
    group
  obtain ⟨h1, h2⟩ := hsc _ hq'
  refine ⟨?_, ?_⟩
  · show S.h⁻¹ * baseChangeGL (algebraMap K L) (l₀ * q * l₀⁻¹) * S.h ∈ Qθ Tag.E8 L
    rw [e]
    exact h1
  · unfold Cc
    rw [e, h2]

end Generic

section Torus

variable {L : Type} [Field L]

theorem thetaDiag_pow (θ : Fin Tag.E8.rank → ℤ) (a : Lˣ) {q : ℕ} (ha : a ^ q = a) :
    thetaDiag θ a ^ q = thetaDiag θ a := by
  funext i
  rw [Pi.pow_apply]
  change (a ^ iform θ (Pi.single i 1)) ^ q = a ^ iform θ (Pi.single i 1)
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha]

theorem Frob_dθ (Fr : L →+* L) {q : ℕ} (hF : ∀ c, Fr c = c ^ q) (a : Lˣ) (ha : a ^ q = a) :
    Frob Fr (dθ a) = dθ a := by
  rw [dθ_eq]
  exact (CFSG.RankThree.Chevalley.entrywise_frob_rootDiagUnit Fr hF (thetaDiag _ a)).trans
    (congrArg _ (thetaDiag_pow _ a ha))

theorem conj_Frob_dθ (Fr : L →+* L) {q : ℕ} (hF : ∀ c, Fr c = c ^ q) (a : Lˣ) (ha : a ^ q = a)
    (w : WeylGroup Tag.E8) (hw : w • highRoot Tag.E8 = highRoot Tag.E8) :
    canonicalRep (coxeterSystem Tag.E8) L w * Frob Fr (dθ a) *
      (canonicalRep (coxeterSystem Tag.E8) L w)⁻¹ = dθ a := by
  rw [Frob_dθ Fr hF a ha, dθ_eq]
  refine ((rootDiagUnit_eq_conj_canonicalRep_iff _ _ w).2 fun v => ?_).symm
  rw [rootChar_thetaDiag, rootChar_thetaDiag]
  have := iform_smul w (highRoot Tag.E8) v
  rw [hw] at this
  rw [this]

theorem conj_Frob_dθ_pos2 (Fr : L →+* L) {q : ℕ} (hF : ∀ c, Fr c = c ^ q) (a : Lˣ)
    (ha : a ^ q = a) :
    ((canonicalRep (coxeterSystem Tag.E8) L νW)⁻¹ *
        (canonicalRep (coxeterSystem Tag.E8) L w8 * canonicalRep (coxeterSystem Tag.E8) L νW)) *
      Frob Fr (dθ a) * ((canonicalRep (coxeterSystem Tag.E8) L νW)⁻¹ *
        (canonicalRep (coxeterSystem Tag.E8) L w8 * canonicalRep (coxeterSystem Tag.E8) L νW))⁻¹ =
      dθ a := by
  set c := canonicalRep (coxeterSystem Tag.E8) L νW with hc
  set nw := canonicalRep (coxeterSystem Tag.E8) L w8 with hnw
  have hX : c * dθ a * c⁻¹ = rootDiagUnit Tag.E8 (thetaDiag theta2 a) := by
    rw [dθ_eq]
    refine ((rootDiagUnit_eq_conj_canonicalRep_iff _ _ νW).2 fun v => ?_).symm
    rw [rootChar_thetaDiag, rootChar_thetaDiag]
    have := iform_smul νW (highRoot Tag.E8) v
    rw [νW_theta] at this
    rw [this]
  have hcomm : nw * (c * dθ a * c⁻¹) * nw⁻¹ = c * dθ a * c⁻¹ := by
    rw [hX]
    refine ((rootDiagUnit_eq_conj_canonicalRep_iff _ _ w8).2 fun v => ?_).symm
    rw [rootChar_thetaDiag, rootChar_thetaDiag]
    have hw2 : w8 • theta2 = theta2 := by rw [w_smul, wm_theta2]
    have := iform_smul w8 theta2 v
    rw [hw2] at this
    rw [this]
  rw [Frob_dθ Fr hF a ha]
  calc (c⁻¹ * (nw * c)) * dθ a * (c⁻¹ * (nw * c))⁻¹
      = c⁻¹ * (nw * (c * dθ a * c⁻¹) * nw⁻¹) * c := by group
    _ = c⁻¹ * (c * dθ a * c⁻¹) * c := by rw [hcomm]
    _ = dθ a := by group

end Torus

section Pos

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)
  (H : Subgroup (ModGL Tag.E8 K))

theorem unit_pow_card (a : K) (ha : algebraMap K D.L a ≠ 0) :
    (Units.mk0 (algebraMap K D.L a) ha) ^ Nat.card K = Units.mk0 (algebraMap K D.L a) ha := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val]
  change (algebraMap K D.L a) ^ Nat.card K = algebraMap K D.L a
  rw [← D.hFr]
  exact (toSetup D ⊥).hfix a

theorem scalClosed₁ (hH1 : D.frame TwClass.e8Ten.S₁ ≤ H) : (toSetup D H).ScalClosed := by
  refine Setup.scalClosed_of_torus _ fun a ha => ?_
  have ha' : algebraMap K D.L a ≠ 0 := (map_ne_zero _).2 ha
  refine ⟨dθ (Units.mk0 _ ha'), rootSpan Tag.E8 D.L TwClass.e8Ten.S₁,
    xlink D H _ hH1, ?_, dθ_mem_adj _, ?_, fun q hq => dθ_scal _ hq⟩
  · have hle : Heis.Uθ Tag.E8 D.L ⊔ Heis.Uneg Tag.E8 D.L ≤ rootSpan Tag.E8 D.L TwClass.e8Ten.S₁ :=
      sup_le (rootSubgroup_le_rootSpan_of_mem (TwBasicAux.highRoot_mem_S₁ TwClass.e8Ten))
        (rootSubgroup_le_rootSpan_of_mem (TwBasicAux.neg_highRoot_mem_S₁ TwClass.e8Ten))
    exact hle (dθ_mem _)
  · exact conj_Frob_dθ D.Fr D.hFr _ (unit_pow_card D a ha') w8 (toSetup D H).hθ

theorem scalClosed₂ (hH2 : D.frame TwClass.e8Ten.S₂ ≤ H) : (toSetup2 D H).ScalClosed := by
  refine Setup.scalClosed_of_torus _ fun a ha => ?_
  have ha' : algebraMap K D.L a ≠ 0 := (map_ne_zero _).2 ha
  refine ⟨dθ (Units.mk0 _ ha'), Xc D TwClass.e8Ten.S₂, xlink2 D H _ hH2, ?_, dθ_mem_adj _, ?_,
    fun q hq => dθ_scal _ hq⟩
  · have hle : Heis.Uθ Tag.E8 D.L ⊔ Heis.Uneg Tag.E8 D.L ≤ Xc D TwClass.e8Ten.S₂ :=
      sup_le (fun u hu => Uθ_le_Xc D u hu) (fun u hu => Uneg_le_Xc D u hu)
    exact hle (dθ_mem _)
  · exact conj_Frob_dθ_pos2 D.Fr D.hFr _ (unit_pow_card D a ha')

end Pos

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
