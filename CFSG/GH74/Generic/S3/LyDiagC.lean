module

public import CFSG.GH74.Generic.Shapes
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.S1.RSP
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SwappedQuasisimple
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups commutatorElement

section Abstract

variable {H : Type} [Group H] {L : Subgroup H} {t : H}

theorem mem_center_of_swapDiag_central (hL : CFSG.IsQuasisimple ↥L) (hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥)
    {a : ↥L} (ha : ∀ b : ↥L, swapDiag hAB b * swapDiag hAB a = swapDiag hAB a * swapDiag hAB b) :
    a ∈ center ↥L := by
  have hperf : Group.IsPerfect ↥L := hL.1
  have h0 : center (↥L ⧸ center ↥L) = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot ↥L
  have hc : (QuotientGroup.mk a : ↥L ⧸ center ↥L) ∈ center (↥L ⧸ center ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine ker_swapDiag_le_center hAB ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, map_mul, map_mul]
    exact ha b
  rw [h0, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
  exact hc

theorem exists_center_preimage (hL : CFSG.IsQuasisimple ↥L) (hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥) {e : H}
    (he : e ∈ (swapDiag hAB).range) (hc : ∀ d ∈ (swapDiag hAB).range, d * e = e * d) :
    ∃ a : ↥L, a ∈ center ↥L ∧ swapDiag hAB a = e := by
  obtain ⟨a, rfl⟩ := he
  exact ⟨a, mem_center_of_swapDiag_central hL hAB fun b => hc _ ⟨b, rfl⟩, rfl⟩

theorem sq_eq_swapDiag (hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥) (ht : t * t = 1) (a : ↥L) :
    (t * (a : H)) * (t * (a : H)) = swapDiag hAB a := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hc := commute_of_commutator_conj_eq_bot hAB a.2 (conj_mem_conjSub (t := t) a.2)
  rw [ht'] at hc
  rw [swapDiag_apply, ht']
  calc t * (a : H) * (t * (a : H)) = (t * (a : H) * t) * (a : H) := by group
    _ = (a : H) * (t * (a : H) * t) := hc.symm

end Abstract

section Quot

theorem quotCenterEquiv_of_surjective {L Δ : Type*} [Group L] [Group Δ] (ψ : L →* Δ)
    (hψ : Function.Surjective ψ) (hcen : ∀ a, ψ a ∈ center Δ → a ∈ center L) :
    Nonempty (L ⧸ center L ≃* Δ ⧸ center Δ) := by
  let ψ' : L →* Δ ⧸ center Δ := (QuotientGroup.mk' (center Δ)).comp ψ
  have hs : Function.Surjective ψ' := (QuotientGroup.mk'_surjective _).comp hψ
  have hker : ψ'.ker = center L := by
    ext a
    simp only [MonoidHom.mem_ker, ψ', MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · exact hcen a
    · intro ha
      rw [Subgroup.mem_center_iff] at ha ⊢
      intro d
      obtain ⟨b, rfl⟩ := hψ d
      rw [← map_mul, ← map_mul, ha b]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ' hs)⟩

theorem lieModel_psl2_quot {Q : Type} [Group Q] {F : Type} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hcard : Nat.card F = p ^ f)
    (e : Q ≃* StatedSL 2 F) : LieModel (Q ⧸ center Q) .PSL 2 p f := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at h5
    · exact h
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hadm : StatedLieAdmissible .PSL 2 p f := by
    refine ⟨hp, hf, le_rfl, ?_, ?_⟩
    · intro h
      have h2 : p ^ f = 2 := (Prod.mk.inj h).2
      rw [h2] at hodd
      exact absurd hodd (by decide)
    · intro h
      have h3 : p ^ f = 3 := (Prod.mk.inj h).2
      omega
  have hmap : (center Q).map e.toMonoidHom =
      (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) := by
    rw [← center_statedSL_eq 2]
    exact Subgroup.map_center_eq e
  exact Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hcard,
    ⟨QuotientGroup.congr (center Q) _ e hmap⟩⟩

end Quot

section Cover

variable {H : Type} [Group H] [Finite H] {L : Subgroup H} {t : H}

theorem exists_central_involution_diag (hF : GenericKnownFacts) (hL : CFSG.IsQuasisimple ↥L)
    (hZ2 : IsPGroup 2 ↥(center ↥L)) (hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥) {F : Type} [Field F] [Finite F]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hcard : Nat.card F = p ^ f)
    (eΔ : ↥(swapDiag hAB).range ≃* StatedSL 2 F) {e : H} (he : e ∈ (swapDiag hAB).range)
    (he1 : e ≠ 1) (hc : ∀ d ∈ (swapDiag hAB).range, d * e = e * d) :
    ∃ a : ↥L, a ∈ center ↥L ∧ (a : H) * (a : H) = 1 ∧ swapDiag hAB a = e := by
  obtain ⟨a, haC, hae⟩ := exists_center_preimage hL hAB he hc
  let ψ : ↥L →* ↥(swapDiag hAB).range := (swapDiag hAB).rangeRestrict
  have hψ : Function.Surjective ψ := (swapDiag hAB).rangeRestrict_surjective
  have hcen : ∀ b, ψ b ∈ center ↥(swapDiag hAB).range → b ∈ center ↥L := by
    intro b hb
    refine mem_center_of_swapDiag_central hL hAB fun c => ?_
    have := Subgroup.mem_center_iff.1 hb (ψ c)
    exact congrArg Subtype.val this
  obtain ⟨eq⟩ := quotCenterEquiv_of_surjective ψ hψ hcen
  have hmodel : LieModel (↥L ⧸ center ↥L) .PSL 2 p f :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eq.symm
      (lieModel_psl2_quot hp hp2 h5 hcard eΔ)
  rcases hF.psl2_cover p f hp hp2 ↥L hL hZ2 hmodel with hbot | ⟨F', _, _, hF'c, ⟨e'⟩⟩
  · exfalso
    rw [hbot, Subgroup.mem_bot] at haC
    apply he1
    rw [← hae, haC]
    exact map_one _
  · refine ⟨a, haC, ?_, hae⟩
    have hodd' : Odd (Nat.card F') := by
      rw [hF'c]
      exact (hp.odd_of_ne_two hp2).pow
    let e'' : ↥L ≃* SL(2, F') := e'.trans (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 2 F')
    have hcenter : e'' a ∈ Subgroup.center SL(2, F') :=
      (CFSG.ClassicalInvolution.mem_center_iff_of_equiv_sl2 e'' a).1 haC
    have haa : a * a = 1 := by
      apply e''.injective
      rw [map_mul, map_one]
      rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).1 hcenter with h | h
      · rw [h, mul_one]
      · rw [h]
        have h2 := pow_orderOf_eq_one (-1 : SL(2, F'))
        rwa [CFSG.ClassicalInvolution.sl2_orderOf_neg_one hodd', pow_two] at h2
    exact congrArg Subtype.val haa

end Cover

end CFSG.GH74.Generic.S3
