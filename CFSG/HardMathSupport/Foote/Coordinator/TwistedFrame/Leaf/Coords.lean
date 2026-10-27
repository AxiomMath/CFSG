module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CoordsAuxFrame
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CoordsAuxCentral

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


namespace TwCoordsAux

open CoordsAux

theorem rootSubgroup_le_frame {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}
    (D : LangLevi τ K w) {S : Set (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} (hβS : β ∈ S)
    (hg : D.g ∈ Subgroup.normalizer (rootSubgroup τ D.L β : Set (ModGL τ D.L))) :
    rootSubgroup τ K β ≤ D.frame S := by
  intro x hx
  unfold LangLevi.frame
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  refine ⟨rootSubgroup_le_adjointGroup β hx, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  rw [baseChangeGL_pinnedX]
  have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) _).1
    (mem_rootSubgroup.2 ⟨algebraMap K D.L c, rfl⟩ :
      pinnedX τ D.L β (algebraMap K D.L c) ∈ rootSubgroup τ D.L β)
  rw [inv_inv] at h1
  exact Subgroup.mem_iSup_of_mem β (Subgroup.mem_iSup_of_mem hβS h1)

theorem Uθ_le_X₁ (c : TwClass) {K : Type} [Field K] [Finite K] (D : LangLevi c.tag K c.w) :
    Uθ c.tag K ≤ c.X₁ D :=
  rootSubgroup_le_frame D (highRoot_mem_S₁ c)
    (Pθ_le_normalizer_Uθ c.tag D.L (parabolicLevi_le_parabolicSubgroup _ D.g_mem))

theorem Uneg_le_X₁ (c : TwClass) {K : Type} [Field K] [Finite K] (D : LangLevi c.tag K c.w) :
    Heis.Uneg c.tag K ≤ c.X₁ D :=
  rootSubgroup_le_frame D (neg_highRoot_mem_S₁ c) (Lθ_le_normalizer_Uneg c.tag D.L D.g_mem)

variable (c : TwClass) {K : Type} [Field K] [Finite K] (D : LangLevi c.tag K c.w)

theorem κ_one : κ D 1 = 0 := by
  unfold κ Ψ
  rw [map_one]
  have : D.g⁻¹ * 1 * D.g = 1 := by group
  rw [this, heisCoord_one]

theorem κ_inv {q : ModGL c.tag K} (hq : q ∈ Qθ c.tag K) : κ D q⁻¹ = -κ D q := by
  have h := κ_mul D (inv_mem hq) hq
  rw [inv_mul_cancel, κ_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem smul_mem_Bset_iff {β : Fin c.tag.rank → ℤ} (hβ : β ∈ Deg1 c.tag) :
    c.w • β ∈ Bset c ↔ β ∈ Bset c := by
  have hw := w_smul_highRoot c
  have hβr : IsRoot c.tag β := (CoordAux.mem_Deg1.1 hβ).1
  have hwβ : c.w • β ∈ Deg1 c.tag :=
    CoordAux.mem_Deg1.2 ⟨IsRoot.smul hβr c.w, by
      rw [degθ_smul_of_fix hw]
      exact (CoordAux.mem_Deg1.1 hβ).2⟩
  unfold Bset
  simp only [Set.mem_setOf_eq]
  rw [w_smul_mem_S₁_iff c hβr]
  exact ⟨fun h => ⟨hβ, h.2⟩, fun h => ⟨hwβ, h.2⟩⟩

open Classical in
theorem isSig_pB {ε : (Fin c.tag.rank → ℤ) → D.L} {v : (Fin c.tag.rank → ℤ) → D.L}
    (hv : IsSig D ε v) :
    IsSig D ε (fun β => if β ∈ Bset c then v β else 0) := by
  classical
  refine ⟨fun β hβ => ?_, fun β hβ => ?_⟩
  · dsimp only
    rw [if_neg (fun h => hβ h.1)]
  · dsimp only
    by_cases hB : β ∈ Bset c
    · rw [if_pos hB, if_pos ((smul_mem_Bset_iff c hβ).2 hB), hv.2 β hβ]
    · rw [if_neg hB, if_neg (fun h => hB ((smul_mem_Bset_iff c hβ).1 h)), map_zero, mul_zero]

open Classical in
theorem isSig_pM {ε : (Fin c.tag.rank → ℤ) → D.L} {v : (Fin c.tag.rank → ℤ) → D.L}
    (hv : IsSig D ε v) :
    IsSig D ε (fun β => if β ∈ Bset c then 0 else v β) := by
  classical
  refine ⟨fun β hβ => ?_, fun β hβ => ?_⟩
  · dsimp only
    rw [hv.1 β hβ]
    simp
  · dsimp only
    by_cases hB : β ∈ Bset c
    · rw [if_pos hB, if_pos ((smul_mem_Bset_iff c hβ).2 hB), map_zero, mul_zero]
    · rw [if_neg hB, if_neg (fun h => hB ((smul_mem_Bset_iff c hβ).1 h)), hv.2 β hβ]

end TwCoordsAux

theorem twCoords (c : TwClass) (K : Type) [Field K] [Finite K] (hK : c.minQ ≤ Nat.card K)
    (D : LangLevi c.tag K c.w) : TwCoords (c.X₁ D) (c.X₂ D) := by
  classical
  have _ := hK
  open CoordsAux TwCoordsAux in
  have hw := w_smul_highRoot c
  obtain ⟨ε, -, hε⟩ := CoordsAux.exists_monomial (τ := c.tag) (F := D.L) hw
  have hε' : CoordsAux.MonomialProp c.w ε := hε
  set X := c.X₁ D ⊔ c.X₂ D with hX
  have hX₁X : c.X₁ D ≤ X := le_sup_left
  have hUθ : Uθ c.tag K ≤ X := (TwCoordsAux.Uθ_le_X₁ c D).trans hX₁X
  have hsc : ∀ a : K, a ≠ 0 → ∃ t : ModGL c.tag K, t ∈ X ∧ t ∈ Lθ c.tag K ∧
      ∀ q ∈ Qθ c.tag K, t * q * t⁻¹ ∈ Qθ c.tag K ∧
        heisCoord c.tag K (t * q * t⁻¹) = a • heisCoord c.tag K q := by
    intro a ha
    obtain ⟨t, ht, htL, hts⟩ := exists_scalarTorus c.tag K ha
    exact ⟨t, hX₁X (sup_le (TwCoordsAux.Uθ_le_X₁ c D) (TwCoordsAux.Uneg_le_X₁ c D) ht), htL, hts⟩
  have hRsupp : ∀ q ∈ Qθ c.tag K, q ∈ X ↔ ∀ β, κ D q β ≠ 0 → β ∈ CoordsAux.Bset c := fun q hq =>
    ⟨fun h => CoordsAux.support_of_mem_X c D hq h,
      fun hs => hX₁X (CoordsAux.mem_X₁_of_support c D hq hs)⟩
  have hsR : ∀ a : K, a ≠ 0 → ∃ t : ModGL c.tag K, ∀ y ∈ Rθ X, t * y * t⁻¹ ∈ Rθ X ∧
      heisCoord c.tag K (t * y * t⁻¹) = a • heisCoord c.tag K y := by
    intro a ha
    obtain ⟨t, htX, -, hts⟩ := hsc a ha
    exact ⟨t, fun y hy => ⟨⟨X.mul_mem (X.mul_mem htX hy.1) (X.inv_mem htX), (hts y hy.2).1⟩,
      (hts y hy.2).2⟩⟩
  have hsC : ∀ a : K, a ≠ 0 → ∃ t : ModGL c.tag K, ∀ y ∈ CQθ X, t * y * t⁻¹ ∈ CQθ X ∧
      heisCoord c.tag K (t * y * t⁻¹) = a • heisCoord c.tag K y := by
    intro a ha
    obtain ⟨t, htX, htL, hts⟩ := hsc a ha
    refine ⟨t, fun y hy => ?_⟩
    have hcent : t * y * t⁻¹ ∈ Subgroup.centralizer (Rθ X : Set (ModGL c.tag K)) := by
      refine Subgroup.mem_centralizer_iff.2 fun r hr => ?_
      have hr' : t⁻¹ * r * t ∈ Rθ X := by
        refine ⟨X.mul_mem (X.mul_mem (X.inv_mem htX) hr.1) (by simpa using htX), ?_⟩
        have := Lθ_conj_mem_Qθ (inv_mem htL) hr.2
        rwa [inv_inv] at this
      have hc := Subgroup.mem_centralizer_iff.1 hy.2 _ hr'
      calc r * (t * y * t⁻¹) = t * ((t⁻¹ * r * t) * y) * t⁻¹ := by group
        _ = t * (y * (t⁻¹ * r * t)) * t⁻¹ := by rw [hc]
        _ = (t * y * t⁻¹) * r := by group
    exact ⟨⟨(hts y hy.1).1, hcent⟩, (hts y hy.1).2⟩
  refine ⟨fun q hq hqS => ?_, ?_, ?_⟩
  · obtain ⟨r, hr, hrq⟩ := exists_of_mem_span_coord (Rθ X) inf_le_right hsR hqS
    have hU : q * r⁻¹ ∈ Uθ c.tag K := mul_inv_mem_Uθ_of_coord_eq hq hr.2 hrq.symm
    have : q = (q * r⁻¹) * r := by group
    rw [this]
    exact X.mul_mem (hUθ hU) hr.1
  · refine eq_bot_iff.2 fun f hf => ?_
    obtain ⟨hfS, hfM⟩ := hf
    obtain ⟨r, hr, hrf⟩ := exists_of_mem_span_coord (Rθ X) inf_le_right hsR hfS
    obtain ⟨q, hq, hqf⟩ := exists_of_mem_span_coord (CQθ X) inf_le_left hsC hfM
    have hU : q * r⁻¹ ∈ Uθ c.tag K := mul_inv_mem_Uθ_of_coord_eq hq.1 hr.2 (hqf.trans hrf.symm)
    have hqX : q ∈ X := by
      have : q = (q * r⁻¹) * r := by group
      rw [this]
      exact X.mul_mem (hUθ hU) hr.1
    have hqs := (hRsupp q hq.1).1 hqX
    have hκ : κ D q = 0 := by
      refine CoordsAux.eq_zero_of_central c D hε' hq.1 hqs fun r' hr'Q hr's => ?_
      have hr'X : r' ∈ Rθ X := ⟨(hRsupp r' hr'Q).2 hr's, hr'Q⟩
      exact (Subgroup.mem_centralizer_iff.1 hq.2 r' hr'X).symm
    have hqU : q ∈ Uθ c.tag K := (κ_eq_zero_iff D hq.1).1 hκ
    rw [Submodule.mem_bot, ← hqf]
    exact ((heisCoord_spec c.tag K).eq_zero_iff q hq.1).2 hqU
  · refine le_antisymm ?_ ?_
    · refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨q, hq, rfl⟩ β hβ
        exact (heisCoord_spec c.tag K).support q hq.2 β hβ
      · rintro _ ⟨q, hq, rfl⟩ β hβ
        exact (heisCoord_spec c.tag K).support q hq.1 β hβ
    · intro f hf
      obtain ⟨q, hq, rfl⟩ := (heisCoord_spec c.tag K).surj f hf
      have hsig := CoordsAux.κ_isSig D hw hε' hq
      obtain ⟨qS, hqS, hκS⟩ := CoordsAux.exists_lift D hw hε'
        (TwCoordsAux.isSig_pB c D hsig)
      obtain ⟨qM, hqM, hκM⟩ := CoordsAux.exists_lift D hw hε'
        (TwCoordsAux.isSig_pM c D hsig)
      have hqSX : qS ∈ X := (hRsupp qS hqS).2 fun β hβ => by
        by_contra hB
        apply hβ
        rw [hκS]
        simp [hB]
      have hqMC : qM ∈ CQθ X := by
        refine ⟨hqM, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
        refine CoordsAux.commute_of_disjoint_support c D hr.2 hqM
          ((hRsupp r hr.2).1 hr.1) (fun β hβ hB => hβ ?_)
        rw [hκM]
        simp [hB]
      have hsum : κ D (q * (qS * qM)⁻¹) = 0 := by
        have hSM : qS * qM ∈ Qθ c.tag K := mul_mem hqS hqM
        rw [κ_mul D hq (inv_mem hSM), TwCoordsAux.κ_inv c D hSM, κ_mul D hqS hqM, hκS, hκM]
        funext β
        by_cases hB : β ∈ CoordsAux.Bset c <;> simp [hB]
      have hU : q * (qS * qM)⁻¹ ∈ Uθ c.tag K :=
        (κ_eq_zero_iff D (mul_mem hq (inv_mem (mul_mem hqS hqM)))).1 hsum
      have hcoord : heisCoord c.tag K q = heisCoord c.tag K qS + heisCoord c.tag K qM := by
        have h0 := ((heisCoord_spec c.tag K).eq_zero_iff _
          (mul_mem hq (inv_mem (mul_mem hqS hqM)))).2 hU
        rw [(heisCoord_spec c.tag K).mul _ hq _ (inv_mem (mul_mem hqS hqM)),
          heisCoord_inv (mul_mem hqS hqM), (heisCoord_spec c.tag K).mul _ hqS _ hqM] at h0
        have h1 : heisCoord c.tag K q + -(heisCoord c.tag K qS + heisCoord c.tag K qM) = 0 := h0
        exact add_neg_eq_zero.1 h1
      rw [hcoord]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨qS, ⟨hqSX, hqS⟩, rfl⟩)
        (Submodule.subset_span ⟨qM, hqMC, rfl⟩)

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
