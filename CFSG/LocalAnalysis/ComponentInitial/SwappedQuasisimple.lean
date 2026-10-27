module

public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] {A : Subgroup G} {t : G}

theorem commute_of_commutator_conj_eq_bot (hAB : ⁅A, conjSub t⁻¹ A⁆ = ⊥) {x y : G} (hx : x ∈ A)
    (hy : y ∈ conjSub t⁻¹ A) : x * y = y * x := by
  have := Subgroup.commutator_mem_commutator hx hy
  rw [hAB, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem conj_mem_conjSub {x : G} (hx : x ∈ A) : t⁻¹ * x * t ∈ conjSub t⁻¹ A :=
  ⟨x, hx, by simp⟩

@[expose] def swapDiag (hAB : ⁅A, conjSub t⁻¹ A⁆ = ⊥) : A →* G where
  toFun x := x * (t⁻¹ * x * t)
  map_one' := by simp
  map_mul' x y := by
    simp only [Subgroup.coe_mul]
    have h := commute_of_commutator_conj_eq_bot hAB y.2 (conj_mem_conjSub (t := t) x.2)
    calc (x : G) * y * (t⁻¹ * (x * y) * t) = x * (y * (t⁻¹ * x * t)) * (t⁻¹ * y * t) := by
          group
      _ = x * ((t⁻¹ * x * t) * y) * (t⁻¹ * y * t) := by rw [h]
      _ = x * (t⁻¹ * x * t) * (y * (t⁻¹ * y * t)) := by group

theorem swapDiag_apply (hAB : ⁅A, conjSub t⁻¹ A⁆ = ⊥) (x : A) :
    swapDiag hAB x = x * (t⁻¹ * x * t) := rfl

theorem commutatorElement_mul_mul_of_commute {a b z w : G} (hzb : Commute z b)
    (hzw : Commute z w) (hwa : Commute w a) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ = a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by
        group
    _ = a * (b * z) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzb.eq]
    _ = a * b * (z * w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * b * w * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzw.eq, mul_inv_cancel_right]
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [hwa.inv_right.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_self_of_isQuasisimple {L : Subgroup G} (hL : CFSG.Assembly.IsQuasisimple L) :
    ⁅L, L⁆ = L := by
  have h := congrArg (Subgroup.map L.subtype) hL.1
  rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h

theorem mem_of_mem_conjSub_of_mem_centralizer {z : G} (hz : z ∈ conjSub t⁻¹ A)
    (hzt : z ∈ centralizer ({t} : Set G)) : z ∈ A := by
  obtain ⟨a, ha, rfl⟩ := hz
  have h := mem_centralizer_iff.1 hzt t rfl
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h ⊢
  have h' : a * t = t⁻¹ * a * t * t := by rw [← h]; group
  rw [← mul_right_cancel h']
  exact ha

section Swapped

variable (hAB : ⁅A, conjSub t⁻¹ A⁆ = ⊥)

include hAB in
theorem inf_le_centralizer_sup : A ⊓ conjSub t⁻¹ A ≤
    centralizer ((A ⊔ conjSub t⁻¹ A : Subgroup G) : Set G) := by
  intro z hz
  have hle : A ⊔ conjSub t⁻¹ A ≤ centralizer ({z} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun y hy => ?_)
    · rw [mem_centralizer_iff]; rintro _ rfl
      exact (commute_of_commutator_conj_eq_bot hAB hx hz.2).symm
    · rw [mem_centralizer_iff]; rintro _ rfl
      exact commute_of_commutator_conj_eq_bot hAB hz.1 hy
  rw [mem_centralizer_iff]
  intro w hw
  exact (mem_centralizer_iff.1 (hle hw) z rfl).symm

include hAB in
theorem coe_sup_conjSub : ((A ⊔ conjSub t⁻¹ A : Subgroup G) : Set G) =
    (A : Set G) * (conjSub t⁻¹ A : Set G) := by
  refine Subgroup.coe_mul_of_left_le_normalizer_right _ _ ?_
  refine le_trans ?_ (centralizer_le_normalizer _)
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact (commute_of_commutator_conj_eq_bot hAB hx hy).symm

theorem swapDiag_mem_sup (x : A) : swapDiag hAB x ∈ A ⊔ conjSub t⁻¹ A :=
  mul_mem (mem_sup_left x.2) (mem_sup_right (conj_mem_conjSub x.2))

theorem swapDiag_mem_centralizer (ht : t⁻¹ = t) (x : A) :
    swapDiag hAB x ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_iff]
  intro s hs
  rw [Set.mem_singleton_iff.1 hs, swapDiag_apply]
  have hc := commute_of_commutator_conj_eq_bot hAB x.2 (conj_mem_conjSub (t := t) x.2)
  rw [ht] at hc ⊢
  calc t * (x * (t * x * t)) = t * x * t * x * t := by simp only [mul_assoc]
    _ = x * (t * x * t) * t := by rw [← hc]

theorem mem_inf_of_mem_ker_swapDiag {x : A} (hx : x ∈ (swapDiag hAB).ker) :
    (x : G) ∈ A ⊓ conjSub t⁻¹ A := by
  refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
  rw [MonoidHom.mem_ker, swapDiag_apply, mul_eq_one_iff_eq_inv] at hx
  rw [hx]
  exact inv_mem (conj_mem_conjSub x.2)

theorem ker_swapDiag_le_center : (swapDiag hAB).ker ≤ center A := fun _ hx =>
  mem_center_iff.2 fun y =>
    Subtype.ext (commute_of_commutator_conj_eq_bot hAB y.2 (mem_inf_of_mem_ker_swapDiag hAB hx).2)

theorem isQuasisimple_range_swapDiag (hA : CFSG.Assembly.IsQuasisimple A) :
    CFSG.Assembly.IsQuasisimple (swapDiag hAB).range := by
  rw [AssemblyBPredicates.isQuasisimple_iff_native] at hA ⊢
  have hq := (quasisimple_central_quotient hA (ker_swapDiag_le_center hAB)).1
  exact (isQuasisimple_congr (QuotientGroup.quotientKerEquivRange _)).1 hq

theorem exists_swapDiag_mul (ht : t⁻¹ = t) {c : G} (hc : c ∈ A ⊔ conjSub t⁻¹ A)
    (hct : c ∈ centralizer ({t} : Set G)) :
    ∃ x : A, ∃ z ∈ A ⊓ conjSub t⁻¹ A ⊓ centralizer ({t} : Set G), swapDiag hAB x * z = c := by
  rw [← SetLike.mem_coe, coe_sup_conjSub hAB] at hc
  obtain ⟨x, hx, y, hy, rfl⟩ := hc
  set z := (swapDiag hAB ⟨x, hx⟩)⁻¹ * (x * y) with hz
  have hzt : z ∈ centralizer ({t} : Set G) :=
    mul_mem (inv_mem (swapDiag_mem_centralizer hAB ht _)) hct
  have hzB : z ∈ conjSub t⁻¹ A := by
    have : z = (t⁻¹ * x * t)⁻¹ * y := by rw [hz, swapDiag_apply]; group
    rw [this]
    exact mul_mem (inv_mem (conj_mem_conjSub hx)) hy
  refine ⟨⟨x, hx⟩, z, ⟨⟨mem_of_mem_conjSub_of_mem_centralizer hzB hzt, hzB⟩, hzt⟩, ?_⟩
  rw [hz, mul_inv_cancel_left]

include hAB in
theorem inf_centralizer_le_center :
    A ⊓ conjSub t⁻¹ A ⊓ centralizer ({t} : Set G) ≤
      (center (A ⊔ conjSub t⁻¹ A : Subgroup G)).map (A ⊔ conjSub t⁻¹ A).subtype := by
  intro z hz
  obtain ⟨hzI, -⟩ := Subgroup.mem_inf.1 hz
  rw [Subgroup.mem_map]
  refine ⟨⟨z, mem_sup_left (Subgroup.mem_inf.1 hzI).1⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro w
  exact Subtype.ext (mem_centralizer_iff.1 (inf_le_centralizer_sup hAB hzI) w w.2)

theorem commutator_fixed_eq_range_swapDiag (ht : t⁻¹ = t) (hA : CFSG.Assembly.IsQuasisimple A) :
    ⁅(A ⊔ conjSub t⁻¹ A) ⊓ centralizer ({t} : Set G),
      (A ⊔ conjSub t⁻¹ A) ⊓ centralizer ({t} : Set G)⁆ = (swapDiag hAB).range := by
  have hΔC : (swapDiag hAB).range ≤ (A ⊔ conjSub t⁻¹ A) ⊓ centralizer ({t} : Set G) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨swapDiag_mem_sup hAB x, swapDiag_mem_centralizer hAB ht x⟩
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro c₁ hc₁ c₂ hc₂
    obtain ⟨x₁, z₁, hz₁, rfl⟩ := exists_swapDiag_mul hAB ht hc₁.1 hc₁.2
    obtain ⟨x₂, z₂, hz₂, rfl⟩ := exists_swapDiag_mul hAB ht hc₂.1 hc₂.2
    have hcz₁ := inf_le_centralizer_sup hAB hz₁.1
    have hcz₂ := inf_le_centralizer_sup hAB hz₂.1
    rw [commutatorElement_mul_mul_of_commute
      (mem_centralizer_iff.1 hcz₁ _ (swapDiag_mem_sup hAB x₂)).symm
      (mem_centralizer_iff.1 hcz₁ z₂ (mem_sup_left hz₂.1.1)).symm
      (mem_centralizer_iff.1 hcz₂ _ (swapDiag_mem_sup hAB x₁)).symm]
    exact ⟨⁅x₁, x₂⁆, map_commutatorElement _ _ _⟩
  · calc (swapDiag hAB).range = ⁅(swapDiag hAB).range, (swapDiag hAB).range⁆ :=
          (commutator_self_of_isQuasisimple (isQuasisimple_range_swapDiag hAB hA)).symm
      _ ≤ _ := commutator_mono hΔC hΔC

theorem isComponentOf_fixed_iff [Finite G] (ht : t⁻¹ = t) (hA : CFSG.Assembly.IsQuasisimple A)
    (Q : Subgroup G) :
    CFSG.Assembly.IsComponentOf Q ((A ⊔ conjSub t⁻¹ A) ⊓ centralizer ({t} : Set G)) ↔
      Q = (swapDiag hAB).range := by
  set C := (A ⊔ conjSub t⁻¹ A) ⊓ centralizer ({t} : Set G)
  have hcomm : ⁅C, C⁆ = (swapDiag hAB).range := commutator_fixed_eq_range_swapDiag hAB ht hA
  have hΔC : (swapDiag hAB).range ≤ C := by
    rintro _ ⟨x, rfl⟩
    exact ⟨swapDiag_mem_sup hAB x, swapDiag_mem_centralizer hAB ht x⟩
  have hΔcomp : CFSG.Assembly.IsComponentOf (swapDiag hAB).range C := by
    refine ⟨hΔC, CFSG.Assembly.IsSubnormal.step hΔC ?_ (CFSG.Assembly.IsSubnormal.refl _),
      isQuasisimple_range_swapDiag hAB hA⟩
    rw [normal_subgroupOf_iff hΔC]
    intro d c hd hc
    have : c * d * c⁻¹ = ⁅c, d⁆ * d := by rw [commutatorElement_def]; group
    rw [this]
    refine mul_mem ?_ hd
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator hc (hΔC hd)
  refine ⟨fun hQ => ?_, fun h => h ▸ hΔcomp⟩
  rcases isComponentOf_eq_or_commute hQ hΔcomp with h | h
  · exact h
  · exfalso
    have hQQ := commutator_self_of_isQuasisimple hQ.2.2
    have hQΔ : Q ≤ (swapDiag hAB).range :=
      calc Q = ⁅Q, Q⁆ := hQQ.symm
        _ ≤ ⁅C, C⁆ := commutator_mono hQ.1 hQ.1
        _ = _ := hcomm
    have hbot : Q = ⊥ := eq_bot_iff.2 <|
      calc Q = ⁅Q, Q⁆ := hQQ.symm
        _ ≤ ⁅Q, (swapDiag hAB).range⁆ := commutator_mono le_rfl hQΔ
        _ = ⊥ := h
    exact not_le_centralizer_self_of_isQuasisimple hQ.2.2 (by rw [hbot]; exact bot_le)

end Swapped

theorem swapped_quasisimple_fixed_central_product [Finite G] (ht : orderOf t = 2)
    (hA : CFSG.Assembly.IsQuasisimple A) (hAB : ⁅A, conjSub t⁻¹ A⁆ = ⊥) :
    let B := conjSub t⁻¹ A
    let I := A ⊓ B
    let C := (A ⊔ B) ⊓ centralizer ({t} : Set G)
    let Δ := (swapDiag hAB).range
    (Δ : Set G) = {g | ∃ x ∈ A, x * (t⁻¹ * x * t) = g} ∧ Δ ≤ C ∧
      Function.Surjective (swapDiag hAB).rangeRestrict ∧
      (swapDiag hAB).rangeRestrict.ker ≤ center A ∧
      (swapDiag hAB).rangeRestrict.ker.map A.subtype ≤ I ∧
      CFSG.Assembly.IsQuasisimple Δ ∧
      (C : Set G) = (Δ : Set G) * ((I ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ∧
      I ⊓ centralizer ({t} : Set G) ≤ (center (A ⊔ B : Subgroup G)).map (A ⊔ B).subtype ∧
      ⁅C, C⁆ = Δ ∧
      (∀ Q : Subgroup G, CFSG.Assembly.IsComponentOf Q C ↔ Q = Δ) ∧
      (CFSG.layer C).map C.subtype = Δ ∧
      Nonempty (Δ ⧸ center Δ ≃* A ⧸ center A) := by
  intro B I C Δ
  have ht' : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  have hΔC : Δ ≤ C := by
    rintro _ ⟨x, rfl⟩
    exact ⟨swapDiag_mem_sup hAB x, swapDiag_mem_centralizer hAB ht' x⟩
  have hcomp : ∀ Q : Subgroup G, CFSG.Assembly.IsComponentOf Q C ↔ Q = Δ :=
    isComponentOf_fixed_iff hAB ht' hA
  have hker : (swapDiag hAB).rangeRestrict.ker = (swapDiag hAB).ker :=
    MonoidHom.ker_rangeRestrict _
  refine ⟨?_, hΔC, MonoidHom.rangeRestrict_surjective _, ?_, ?_, isQuasisimple_range_swapDiag hAB hA,
    ?_, inf_centralizer_le_center hAB, commutator_fixed_eq_range_swapDiag hAB ht' hA, hcomp, ?_, ?_⟩
  · ext g
    simp only [Δ, MonoidHom.coe_range, Set.mem_range, Set.mem_ofPred_eq, Subtype.exists,
      swapDiag_apply, exists_prop]
  · rw [hker]; exact ker_swapDiag_le_center hAB
  · rw [hker]
    rintro _ ⟨x, hx, rfl⟩
    exact mem_inf_of_mem_ker_swapDiag hAB hx
  · ext c
    constructor
    · intro hc
      obtain ⟨x, z, hz, rfl⟩ := exists_swapDiag_mul hAB ht' hc.1 hc.2
      exact ⟨_, ⟨x, rfl⟩, z, hz, rfl⟩
    · rintro ⟨d, hd, z, hz, rfl⟩
      exact mul_mem (hΔC hd) ⟨mem_sup_left (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hz).1).1,
        (Subgroup.mem_inf.1 hz).2⟩
  · have hlayer : CFSG.layer C = Δ.subgroupOf C := by
      have hset : {K : Subgroup C | CFSG.IsComponent K} = {Δ.subgroupOf C} := by
        ext K
        rw [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · intro hK
          have hKK : (K.map C.subtype).subgroupOf C = K :=
            Subgroup.comap_map_eq_self_of_injective C.subtype_injective K
          have h1 : CFSG.Assembly.IsComponentOf (K.map C.subtype) C := by
            rw [isComponentOf_iff_isComponent_subgroupOf (map_subtype_le K), hKK]
            exact hK
          rw [← (hcomp _).1 h1, hKK]
        · rintro rfl
          exact (isComponentOf_iff_isComponent_subgroupOf hΔC).1 ((hcomp _).2 rfl)
      rw [CFSG.layer, hset, sSup_singleton]
    rw [hlayer, Subgroup.map_subgroupOf_eq_of_le hΔC]
  · have hK := ker_swapDiag_le_center hAB
    have hAn := (AssemblyBPredicates.isQuasisimple_iff_native A).1 hA
    obtain ⟨-, -, hcen⟩ := quasisimple_central_quotient hAn hK
    let e1 : A ⧸ (swapDiag hAB).ker ≃* Δ := QuotientGroup.quotientKerEquivRange (swapDiag hAB)
    let e2 : Δ ⧸ center Δ ≃* (A ⧸ (swapDiag hAB).ker) ⧸ center (A ⧸ (swapDiag hAB).ker) :=
      QuotientGroup.congr (center Δ) (center (A ⧸ (swapDiag hAB).ker)) e1.symm
        (Subgroup.map_center_eq e1.symm)
    exact ⟨e2.trans ((QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientQuotientEquivQuotient _ _ hK))⟩


end CFSG.LocalAnalysis.ComponentInitial
