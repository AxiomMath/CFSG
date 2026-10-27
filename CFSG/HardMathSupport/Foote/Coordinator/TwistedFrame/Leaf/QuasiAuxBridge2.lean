module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxBridge

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


namespace LangLevi

variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ} (D : LangLevi τ K w)

theorem exists_frame_of_le_perfect {S : Set (Fin τ.rank → ℤ)} {H : Subgroup (ModGL τ D.L)}
    (hle : H ≤ D.fixedRoot S) (hperf : ⁅H, H⁆ = H) {y : ModGL τ D.L} (hy : y ∈ H) :
    ∃ x ∈ D.frame S, D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g = y := by
  set σ : D.L ≃+* D.L := RingEquiv.ofBijective D.Fr D.Fr_bijective with hσ
  have hσfr : (σ : D.L →+* D.L) = D.Fr := RingHom.ext fun _ => rfl
  have hΓ : ∀ q ∈ H, D.g * q * D.g⁻¹ ∈ entrywiseFixedGroup τ σ := by
    intro q hq
    refine ⟨D.conj_mem_adjointGroup (hle hq), ?_⟩
    show Units.map (entrywiseHom (σ : D.L →+* D.L)) (D.g * q * D.g⁻¹) = D.g * q * D.g⁻¹
    rw [hσfr]
    exact D.frobGL_conj_fixedRoot (hle hq)
  have hcomm : ∀ a ∈ entrywiseFixedGroup τ σ, ∀ b ∈ entrywiseFixedGroup τ σ,
      a * b * a⁻¹ * b⁻¹ ∈ fixedFieldImage τ σ := by
    intro a ha b hb
    have h := entrywiseFixedGroup_quotient_comm (τ := τ) (σ := σ)
      (QuotientGroup.mk ⟨a⁻¹, inv_mem ha⟩) (QuotientGroup.mk ⟨b⁻¹, inv_mem hb⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
    have h2 : (a⁻¹ * b⁻¹)⁻¹ * (b⁻¹ * a⁻¹) ∈ fixedFieldImage τ σ := h
    have e : a * b * a⁻¹ * b⁻¹ = ((a⁻¹ * b⁻¹)⁻¹ * (b⁻¹ * a⁻¹))⁻¹ := by group
    rw [e]
    exact inv_mem h2
  set Qg := H.map (MulAut.conj D.g).toMonoidHom with hQg_def
  have hQg : ⁅Qg, Qg⁆ = Qg := by rw [hQg_def, ← Subgroup.map_commutator, hperf]
  have hle' : Qg ≤ fixedFieldImage τ σ := by
    rw [← hQg]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [commutatorElement_def]
    exact hcomm _ (hΓ a' ha') _ (hΓ b' hb')
  have hz : D.g * y * D.g⁻¹ ∈ fixedFieldImage τ σ := hle' ⟨y, hy, rfl⟩
  rw [D.fixedFieldImage_eq_map] at hz
  obtain ⟨x, hx, hxe⟩ := hz
  have hyx : D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g = y := by
    rw [hxe]; group
  exact ⟨x, (D.frame_mem_iff S x).2 ⟨hx, by rw [hyx]; exact (hle hy).1⟩, hyx⟩

@[expose] def frameImage (S : Set (Fin τ.rank → ℤ)) : Subgroup (ModGL τ D.L) :=
  (D.frame S).map ((MulAut.conj D.g⁻¹).toMonoidHom.comp (baseChangeGL (algebraMap K D.L)))

theorem mem_frameImage {S : Set (Fin τ.rank → ℤ)} {y : ModGL τ D.L} :
    y ∈ D.frameImage S ↔ ∃ x ∈ D.frame S,
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g = y := by
  unfold frameImage
  simp only [Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]

theorem frameImage_le_fixedRoot (S : Set (Fin τ.rank → ℤ)) : D.frameImage S ≤ D.fixedRoot S := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (D.mem_frameImage).1 hy
  exact D.conj_mem_fixedRoot hx

theorem frameImage_injective (S : Set (Fin τ.rank → ℤ)) :
    Function.Injective ((MulAut.conj D.g⁻¹).toMonoidHom.comp (baseChangeGL (algebraMap K D.L))) :=
  (MulAut.conj D.g⁻¹).injective.comp (baseChangeGL_injective _)

@[expose] def frameEquivImage (S : Set (Fin τ.rank → ℤ)) : ↥(D.frame S) ≃* ↥(D.frameImage S) :=
  Subgroup.equivMapOfInjective _ _ (D.frameImage_injective S)

theorem le_frameImage_of_perfect {S : Set (Fin τ.rank → ℤ)} {H : Subgroup (ModGL τ D.L)}
    (hle : H ≤ D.fixedRoot S) (hperf : ⁅H, H⁆ = H) : H ≤ D.frameImage S := fun _ hy =>
  D.mem_frameImage.2 (D.exists_frame_of_le_perfect hle hperf hy)

theorem isQuasisimple_frame_of_frameImage_eq {S : Set (Fin τ.rank → ℤ)}
    {P : Subgroup (ModGL τ D.L)} (h : D.frameImage S = P) (hq : CFSG.IsQuasisimple ↥P) :
    CFSG.IsQuasisimple ↥(D.frame S) :=
  CFSG.IsQuasisimple.of_mulEquiv ((D.frameEquivImage S).trans (MulEquiv.subgroupCongr h)) hq

end LangLevi

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
