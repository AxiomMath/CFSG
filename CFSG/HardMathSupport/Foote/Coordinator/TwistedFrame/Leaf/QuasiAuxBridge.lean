module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.RankThree.PartOne.KE.A1Main

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


namespace LangLevi

variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ} (D : LangLevi τ K w)

abbrev frobGL : ModGL τ D.L →* ModGL τ D.L := Units.map (entrywiseHom D.Fr)

abbrev nW : ModGL τ D.L := canonicalRep (coxeterSystem τ) D.L w

@[expose] def fixedRoot (S : Set (Fin τ.rank → ℤ)) : Subgroup (ModGL τ D.L) :=
  rootSpan τ D.L S ⊓ twistedFixedPoints D.nW D.frobGL

theorem mem_fixedRoot {S : Set (Fin τ.rank → ℤ)} {y : ModGL τ D.L} :
    y ∈ D.fixedRoot S ↔ y ∈ rootSpan τ D.L S ∧ D.nW * D.frobGL y * D.nW⁻¹ = y :=
  Iff.rfl

theorem Fr_comp_algebraMap : D.Fr.comp (algebraMap K D.L) = algebraMap K D.L :=
  frobenius_comp_algebraMap D.Fr D.hFr

theorem Fr_bijective : Function.Bijective D.Fr := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  exact frobenius_bijective D.Fr D.hFr

theorem frobGL_baseChangeGL (x : ModGL τ K) :
    D.frobGL (baseChangeGL (algebraMap K D.L) x) = baseChangeGL (algebraMap K D.L) x :=
  units_map_entrywiseHom_baseChangeGL_algebraMap D.Fr D.hFr x

theorem frobGL_g : D.frobGL D.g = D.g * D.nW := D.lang

theorem frame_mem_iff (S : Set (Fin τ.rank → ℤ)) (x : ModGL τ K) :
    x ∈ D.frame S ↔ x ∈ adjointGroup τ K ∧
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g ∈ rootSpan τ D.L S := by
  unfold LangLevi.frame
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]

theorem conj_mem_fixedRoot {S : Set (Fin τ.rank → ℤ)} {x : ModGL τ K} (hx : x ∈ D.frame S) :
    D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g ∈ D.fixedRoot S := by
  obtain ⟨-, h⟩ := (D.frame_mem_iff S x).1 hx
  refine ⟨h, ?_⟩
  show D.nW * D.frobGL (D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g) * D.nW⁻¹ =
    D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g
  rw [map_mul, map_mul, map_inv, D.frobGL_baseChangeGL, D.frobGL_g]
  group

theorem frobGL_conj_fixedRoot {S : Set (Fin τ.rank → ℤ)} {y : ModGL τ D.L}
    (hy : y ∈ D.fixedRoot S) : D.frobGL (D.g * y * D.g⁻¹) = D.g * y * D.g⁻¹ := by
  have h : D.nW * D.frobGL y * D.nW⁻¹ = y := hy.2
  rw [map_mul, map_mul, map_inv, D.frobGL_g]
  calc D.g * D.nW * D.frobGL y * (D.g * D.nW)⁻¹
      = D.g * (D.nW * D.frobGL y * D.nW⁻¹) * D.g⁻¹ := by group
    _ = D.g * y * D.g⁻¹ := by rw [h]

theorem conj_mem_adjointGroup {S : Set (Fin τ.rank → ℤ)} {y : ModGL τ D.L}
    (hy : y ∈ D.fixedRoot S) : D.g * y * D.g⁻¹ ∈ adjointGroup τ D.L := by
  have hg : D.g ∈ adjointGroup τ D.L := parabolicLevi_le_adjointGroup (τ := τ) (K := D.L) (Jθ τ) D.g_mem
  have hy' : y ∈ adjointGroup τ D.L :=
    (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α :
      rootSpan τ D.L S ≤ adjointGroup τ D.L) hy.1
  exact mul_mem (mul_mem hg hy') (inv_mem hg)

theorem fixedFieldImage_eq_map :
    fixedFieldImage τ (RingEquiv.ofBijective D.Fr D.Fr_bijective) =
      (adjointGroup τ K).map (baseChangeGL (algebraMap K D.L)) := by
  rw [fixedFieldImage_eq_closure, map_baseChangeGL_adjointGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨i, c, hc, rfl | rfl⟩
    · obtain ⟨a, rfl⟩ := mem_range_algebraMap_of_pow_card_eq (k := K) (L := D.L)
        (c := c) (by rw [← D.hFr]; exact hc)
      exact ⟨i, a, Or.inl rfl⟩
    · obtain ⟨a, rfl⟩ := mem_range_algebraMap_of_pow_card_eq (k := K) (L := D.L)
        (c := c) (by rw [← D.hFr]; exact hc)
      exact ⟨i, a, Or.inr rfl⟩
  · rintro ⟨i, a, rfl | rfl⟩
    · refine ⟨i, algebraMap K D.L a, ?_, Or.inl rfl⟩
      exact congrArg (fun f => f a) D.Fr_comp_algebraMap
    · refine ⟨i, algebraMap K D.L a, ?_, Or.inr rfl⟩
      exact congrArg (fun f => f a) D.Fr_comp_algebraMap

theorem exists_frame_of_fixedRoot {S : Set (Fin τ.rank → ℤ)}
    (hperf : Group.IsPerfect ↥(D.fixedRoot S)) {y : ModGL τ D.L} (hy : y ∈ D.fixedRoot S) :
    ∃ x ∈ D.frame S, D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g = y := by
  set σ : D.L ≃+* D.L := RingEquiv.ofBijective D.Fr D.Fr_bijective with hσ
  have hσfr : (σ : D.L →+* D.L) = D.Fr := RingHom.ext fun _ => rfl
  have hΓ : ∀ q ∈ D.fixedRoot S, D.g * q * D.g⁻¹ ∈ entrywiseFixedGroup τ σ := by
    intro q hq
    refine ⟨D.conj_mem_adjointGroup hq, ?_⟩
    show Units.map (entrywiseHom (σ : D.L →+* D.L)) (D.g * q * D.g⁻¹) = D.g * q * D.g⁻¹
    rw [hσfr]
    exact D.frobGL_conj_fixedRoot hq
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
  have hQ : ⁅D.fixedRoot S, D.fixedRoot S⁆ = D.fixedRoot S := Subgroup.isPerfect_iff.mp hperf
  set Qg := (D.fixedRoot S).map (MulAut.conj D.g).toMonoidHom with hQg_def
  have hQg : ⁅Qg, Qg⁆ = Qg := by rw [hQg_def, ← Subgroup.map_commutator, hQ]
  have hle : Qg ≤ fixedFieldImage τ σ := by
    rw [← hQg]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [commutatorElement_def]
    exact hcomm _ (hΓ a' ha') _ (hΓ b' hb')
  have hz : D.g * y * D.g⁻¹ ∈ fixedFieldImage τ σ := hle ⟨y, hy, rfl⟩
  rw [D.fixedFieldImage_eq_map] at hz
  obtain ⟨x, hx, hxe⟩ := hz
  have hyx : D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g = y := by
    rw [hxe]; group
  exact ⟨x, (D.frame_mem_iff S x).2 ⟨hx, by rw [hyx]; exact hy.1⟩, hyx⟩

@[expose] def frameToFixedRoot (S : Set (Fin τ.rank → ℤ)) : ↥(D.frame S) →* ↥(D.fixedRoot S) :=
  ((MulAut.conj D.g⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K D.L)).comp (D.frame S).subtype)).codRestrict
    (D.fixedRoot S) fun x => by
      have h := D.conj_mem_fixedRoot x.2
      simpa [MulAut.conj_apply] using h

theorem coe_frameToFixedRoot (S : Set (Fin τ.rank → ℤ)) (x : ↥(D.frame S)) :
    ((D.frameToFixedRoot S x : ↥(D.fixedRoot S)) : ModGL τ D.L) =
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) (x : ModGL τ K) * D.g := by
  simp [frameToFixedRoot, MulAut.conj_apply]

theorem frameToFixedRoot_injective (S : Set (Fin τ.rank → ℤ)) :
    Function.Injective (D.frameToFixedRoot S) := by
  intro x y h
  have h1 := congrArg Subtype.val h
  rw [D.coe_frameToFixedRoot, D.coe_frameToFixedRoot] at h1
  have h2 : baseChangeGL (algebraMap K D.L) (x : ModGL τ K) =
      baseChangeGL (algebraMap K D.L) (y : ModGL τ K) := by
    have := congrArg (fun z => D.g * z * D.g⁻¹) h1
    simpa [mul_assoc] using this
  exact Subtype.ext (baseChangeGL_injective _ h2)

@[expose] def frameEquivFixedRoot {S : Set (Fin τ.rank → ℤ)} (hperf : Group.IsPerfect ↥(D.fixedRoot S)) :
    ↥(D.frame S) ≃* ↥(D.fixedRoot S) :=
  MulEquiv.ofBijective (D.frameToFixedRoot S) ⟨D.frameToFixedRoot_injective S, fun y => by
    obtain ⟨x, hx, hxy⟩ := D.exists_frame_of_fixedRoot hperf y.2
    exact ⟨⟨x, hx⟩, Subtype.ext (by rw [D.coe_frameToFixedRoot]; exact hxy)⟩⟩

theorem isQuasisimple_frame {S : Set (Fin τ.rank → ℤ)}
    (hq : CFSG.IsQuasisimple ↥(D.fixedRoot S)) : CFSG.IsQuasisimple ↥(D.frame S) :=
  CFSG.IsQuasisimple.of_mulEquiv (D.frameEquivFixedRoot hq.1) hq

end LangLevi

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
