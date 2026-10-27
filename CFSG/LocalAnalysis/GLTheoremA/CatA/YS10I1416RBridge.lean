module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Chev2
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def Chev2MarkedConverse : Prop :=
  ∀ (R : Type) [Group R], (∃ lab : CFSG.Assembly.LargeEvenLabel, CFSG.Assembly.LargeEvenInLambda2 lab ∧
    CFSG.StandardType.MarkedModel lab R) → IsChevSimple 2 R

theorem isQuasisimple_of_isChev2 {G : Type} [Group G] {J : Subgroup G} (h : IsChev2 J) :
    CFSG.Open.IsQuasisimple ↥J := by
  obtain ⟨hc, lab, -, hraw⟩ := h
  obtain ⟨R, hR, I, F, hs, -, θ, -⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  haveI := hs
  exact ⟨hc, θ.isSimpleGroup⟩

theorem chev2_quot_equiv {G : Type} [Group G] [Finite G] {p : ℕ} {X J : Subgroup G}
    (hp : p.Prime) (hJ : GLAPComponent p X J) (hq : CFSG.Open.IsQuasisimple ↥J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J) := by
  have hnt : Nontrivial (↥J ⧸ GLAPPrimeCore p ↥J) :=
    isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent hp hJ)
  have hOtop : GLAPPrimeCore p ↥J ≠ ⊤ := by
    intro h
    rw [h] at hnt
    exact not_subsingleton_iff_nontrivial.2 hnt QuotientGroup.subsingleton_quotient_top
  have hOZ : GLAPPrimeCore p ↥J ≤ Subgroup.center ↥J :=
    le_center_of_normal_of_isQuasisimple hq inferInstance hOtop
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hq.2
  haveI := hq.2.toNontrivial
  have hZbot : Subgroup.center (↥J ⧸ Subgroup.center ↥J) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥J ⧸ Subgroup.center ↥J)) with h | h
    · exact h
    · exfalso
      have hall : ∀ a b : ↥J, ⁅a, b⁆ ∈ Subgroup.center ↥J := by
        intro a b
        have ha : (QuotientGroup.mk a⁻¹ : ↥J ⧸ Subgroup.center ↥J) ∈
            Subgroup.center (↥J ⧸ Subgroup.center ↥J) := h ▸ Subgroup.mem_top _
        have hc := Subgroup.mem_center_iff.1 ha (QuotientGroup.mk b⁻¹)
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
        have e : (b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹) = ⁅a, b⁆ := by
          rw [commutatorElement_def]; group
        rwa [e] at hc
      have hle : commutator ↥J ≤ Subgroup.center ↥J :=
        Subgroup.commutator_le.2 fun a _ b _ => hall a b
      rw [hq.1, top_le_iff] at hle
      have hsub : Subsingleton (↥J ⧸ Subgroup.center ↥J) := by
        rw [hle]; exact QuotientGroup.subsingleton_quotient_top
      exact not_subsingleton _ hsub
  let f : ↥J →* PSimple p J :=
    (QuotientGroup.mk' (Subgroup.center (PQuot p J))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥J))
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = Subgroup.center ↥J := by
    ext x
    simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      have hxZ : (QuotientGroup.mk x : ↥J ⧸ Subgroup.center ↥J) ∈
          Subgroup.center (↥J ⧸ Subgroup.center ↥J) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
        have hw := Subgroup.mem_center_iff.1 hx (QuotientGroup.mk w)
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hw
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        exact hOZ hw
      rw [hZbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hxZ
      exact hxZ
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hx w]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

theorem chev2Bridge_of_marked
    (hC : Chev2MarkedConverse) (G : Type) [Group G] [Finite G] : Chev2BridgeAt G := by
  intro p Y J hp hJ hJch
  obtain ⟨e⟩ := chev2_quot_equiv hp hJ (isQuasisimple_of_isChev2 hJch)
  obtain ⟨lab, hlab, hM⟩ := CFSG.StandardType.Canonical.largeEvenMarking_markedModel_centerQuot
    (P := fun _ _ _ _ _ _ => True) hJch
  exact chev_isChevSimple_of_mulEquiv e.symm (hC _ ⟨lab, hlab, hM⟩)

end CFSG.LocalAnalysis.GLTheoremA

end
