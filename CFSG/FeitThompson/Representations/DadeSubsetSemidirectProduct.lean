module

public import CFSG.FeitThompson.Representations.DadeIntersectionAddElement
public import CFSG.FeitThompson.Definitions.PowerOperationOnClassFunctions
import CFSG.FeitThompson.Foundations.ComplementsDifferByCrossedHom
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers
import CFSG.FeitThompson.OddOrder.SemidirectReassociation
import CFSG.FeitThompson.Representations.OddCyclicFactorOrders

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G : Type*} [Group G]

noncomputable def complProj {N K : Subgroup G} [N.Normal] (h : K.IsComplement' N) : G →* K :=
  (h.QuotientMulEquiv : G ⧸ N ≃* K).toMonoidHom.comp (QuotientGroup.mk' N)

theorem complProj_apply_of_mem {N K : Subgroup G} [N.Normal] (h : K.IsComplement' N) {x : G}
    (hx : x ∈ K) : complProj h x = ⟨x, hx⟩ :=
  quotientMulEquiv_mk_coe h ⟨x, hx⟩

theorem ker_complProj {N K : Subgroup G} [N.Normal] (h : K.IsComplement' N) :
    (complProj h).ker = N := by
  rw [complProj, MonoidHom.ker_comp_of_injective _ _ h.QuotientMulEquiv.injective,
    QuotientGroup.ker_mk']

theorem complProj_eq_one_of_mem {N K : Subgroup G} [N.Normal] (h : K.IsComplement' N) {x : G}
    (hx : x ∈ N) : complProj h x = 1 := by
  rw [← MonoidHom.mem_ker, ker_complProj]; exact hx

def dadeStab (L : Subgroup G) (B : Set G) : Subgroup G := L ⊓ Subgroup.normalizer B

def dadeSubsetGroup (H : G → Subgroup G) (L : Subgroup G) (B : Set G) : Subgroup G :=
  dadeInter H B ⊔ dadeStab L B

variable {L : Subgroup G} {A B : Set G} {H : G → Subgroup G} {l : G}

theorem dadeStab_eq_inf (L : Subgroup G) (B : Set G) :
    dadeStab L B = L ⊓ Subgroup.normalizer B := (rfl)

theorem dadeSubsetGroup_eq_sup (H : G → Subgroup G) (L : Subgroup G) (B : Set G) :
    dadeSubsetGroup H L B = dadeInter H B ⊔ dadeStab L B := (rfl)

theorem dadeStab_le_left : dadeStab L B ≤ L := inf_le_left

theorem dadeStab_le_normalizer : dadeStab L B ≤ Subgroup.normalizer B := inf_le_right

theorem mem_dadeStab_iff : l ∈ dadeStab L B ↔ l ∈ L ∧ (fun x => l⁻¹ * x * l) '' B = B := by
  rw [dadeStab, Subgroup.mem_inf]
  refine and_congr_right fun _ => ?_
  rw [← SetLike.mem_coe, ← setOf_conj_eq_self_eq_normalizer B]
  simp

theorem dadeInter_le_dadeSubsetGroup : dadeInter H B ≤ dadeSubsetGroup H L B := le_sup_left

theorem dadeStab_le_dadeSubsetGroup : dadeStab L B ≤ dadeSubsetGroup H L B := le_sup_right

namespace IsDadeData

variable [Finite G]

theorem conj_smul_dadeInter (hD : IsDadeData L A H) (hBA : B ⊆ A) (hl : l ∈ L) :
    MulAut.conj l • dadeInter H B = dadeInter H ((fun x => l * x * l⁻¹) '' B) := by
  ext x
  rw [mem_conj_smul_iff, mem_dadeInter_iff, mem_dadeInter_iff]
  constructor
  · intro hx y hy
    obtain ⟨c, hc, rfl⟩ := hy
    rw [hD.conj_smul_H (hBA hc) hl, mem_conj_smul_iff]
    exact hx c hc
  · intro hx c hc
    have h := hx (l * c * l⁻¹) ⟨c, hc, rfl⟩
    rwa [hD.conj_smul_H (hBA hc) hl, mem_conj_smul_iff] at h

theorem dadeStab_le_normalizer_dadeInter (hD : IsDadeData L A H) (hBA : B ⊆ A) :
    dadeStab L B ≤ Subgroup.normalizer ((dadeInter H B : Subgroup G) : Set G) := by
  rw [Subgroup.le_set_normalizer_iff]
  intro l hl h hh
  have hB' : (fun x => l * x * l⁻¹) '' B = B :=
    Subgroup.mem_normalizer_iff_conj_image_eq.1 (dadeStab_le_normalizer hl)
  have hmem : l * h * l⁻¹ ∈ MulAut.conj l • dadeInter H B := by
    refine mem_conj_smul_iff.2 ?_
    have he : l⁻¹ * (l * h * l⁻¹) * l = h := by group
    rw [he]; exact hh
  rw [hD.conj_smul_dadeInter hBA (dadeStab_le_left hl), hB'] at hmem
  exact hmem

theorem dadeInter_inf_dadeStab_eq_bot (hD : IsDadeData L A H) (hBA : B ⊆ A) (hB : B.Nonempty) :
    dadeInter H B ⊓ dadeStab L B = ⊥ := by
  obtain ⟨b, hb⟩ := hB
  refine le_antisymm ?_ bot_le
  calc dadeInter H B ⊓ dadeStab L B ≤ H b ⊓ L :=
        inf_le_inf (dadeInter_le hb) dadeStab_le_left
    _ = ⊥ := hD.inf_eq_bot_left (hBA hb)

theorem coe_dadeInter_mul_dadeStab (hD : IsDadeData L A H) (hBA : B ⊆ A) :
    ((dadeInter H B : Subgroup G) : Set G) * ((dadeStab L B : Subgroup G) : Set G)
      = ((dadeSubsetGroup H L B : Subgroup G) : Set G) :=
  (Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (hD.dadeStab_le_normalizer_dadeInter hBA)).symm

theorem mem_dadeSubsetGroup_iff (hD : IsDadeData L A H) (hBA : B ⊆ A) {x : G} :
    x ∈ dadeSubsetGroup H L B ↔ ∃ h ∈ dadeInter H B, ∃ u ∈ dadeStab L B, h * u = x := by
  rw [← SetLike.mem_coe, ← hD.coe_dadeInter_mul_dadeStab hBA]
  exact ⟨fun ⟨h, hh, u, hu, hx⟩ => ⟨h, hh, u, hu, hx⟩,
    fun ⟨h, hh, u, hu, hx⟩ => ⟨h, hh, u, hu, hx⟩⟩

theorem normal_subgroupOf_dadeSubsetGroup (hD : IsDadeData L A H) (hBA : B ⊆ A) :
    ((dadeInter H B).subgroupOf (dadeSubsetGroup H L B)).Normal :=
  normal_subgroupOf_sup (hD.dadeStab_le_normalizer_dadeInter hBA)

theorem isComplement'_subgroupOf_dadeSubsetGroup (hD : IsDadeData L A H) (hBA : B ⊆ A)
    (hB : B.Nonempty) :
    ((dadeStab L B).subgroupOf (dadeSubsetGroup H L B)).IsComplement'
      ((dadeInter H B).subgroupOf (dadeSubsetGroup H L B)) :=
  Subgroup.isComplement'_comm.1
    (isComplement'_subgroupOf_sup (hD.dadeStab_le_normalizer_dadeInter hBA)
      (disjoint_iff.2 (hD.dadeInter_inf_dadeStab_eq_bot hBA hB)))

noncomputable def dadeProj (hD : IsDadeData L A H) (hBA : B ⊆ A) (hB : B.Nonempty) :
    dadeSubsetGroup H L B →* dadeStab L B :=
  haveI : ((dadeInter H B).subgroupOf (dadeSubsetGroup H L B)).Normal :=
    hD.normal_subgroupOf_dadeSubsetGroup hBA
  (Subgroup.subgroupOfEquivOfLe (dadeStab_le_dadeSubsetGroup (H := H))).toMonoidHom.comp
    (complProj (hD.isComplement'_subgroupOf_dadeSubsetGroup hBA hB))

theorem dadeProj_apply_of_mem_dadeStab (hD : IsDadeData L A H) (hBA : B ⊆ A) (hB : B.Nonempty)
    {u : G} (hu : u ∈ dadeStab L B) :
    hD.dadeProj hBA hB ⟨u, dadeStab_le_dadeSubsetGroup hu⟩ = ⟨u, hu⟩ := by
  have hnormal : ((dadeInter H B).subgroupOf (dadeSubsetGroup H L B)).Normal :=
    hD.normal_subgroupOf_dadeSubsetGroup hBA
  have hu' : (⟨u, dadeStab_le_dadeSubsetGroup hu⟩ : dadeSubsetGroup H L B) ∈
      (dadeStab L B).subgroupOf (dadeSubsetGroup H L B) := Subgroup.mem_subgroupOf.2 hu
  refine Subtype.ext ?_
  simp only [dadeProj, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    complProj_apply_of_mem _ hu', Subgroup.subgroupOfEquivOfLe_apply_coe]

theorem ker_dadeProj (hD : IsDadeData L A H) (hBA : B ⊆ A) (hB : B.Nonempty) :
    (hD.dadeProj hBA hB).ker = (dadeInter H B).subgroupOf (dadeSubsetGroup H L B) := by
  have hnormal : ((dadeInter H B).subgroupOf (dadeSubsetGroup H L B)).Normal :=
    hD.normal_subgroupOf_dadeSubsetGroup hBA
  rw [dadeProj, MonoidHom.ker_comp_of_injective _ _
    (Subgroup.subgroupOfEquivOfLe (dadeStab_le_dadeSubsetGroup (H := H))).injective,
    ker_complProj]

theorem dadeProj_apply_mul (hD : IsDadeData L A H) (hBA : B ⊆ A) (hB : B.Nonempty)
    {h u : G} (hh : h ∈ dadeInter H B) (hu : u ∈ dadeStab L B) :
    hD.dadeProj hBA hB ⟨h * u, (hD.mem_dadeSubsetGroup_iff hBA).2 ⟨h, hh, u, hu, rfl⟩⟩
      = ⟨u, hu⟩ := by
  have hone : hD.dadeProj hBA hB ⟨h, dadeInter_le_dadeSubsetGroup hh⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hD.ker_dadeProj hBA hB]
    exact Subgroup.mem_subgroupOf.2 hh
  have hsplit : (⟨h * u, (hD.mem_dadeSubsetGroup_iff hBA).2 ⟨h, hh, u, hu, rfl⟩⟩ :
      dadeSubsetGroup H L B)
      = ⟨h, dadeInter_le_dadeSubsetGroup hh⟩ * ⟨u, dadeStab_le_dadeSubsetGroup hu⟩ := rfl
  rw [hsplit, map_mul, hD.dadeProj_apply_of_mem_dadeStab hBA hB hu, hone, one_mul]

end IsDadeData

def dadePullback {M : Type*} {K : Subgroup G} (p : K →* dadeStab L B) (f : L → M) : K → M :=
  fun x => f (Subgroup.inclusion dadeStab_le_left (p x))

theorem dadePullback_apply {M : Type*} {K : Subgroup G} (p : K →* dadeStab L B) (f : L → M)
    (x : K) : dadePullback p f x = f (Subgroup.inclusion dadeStab_le_left (p x)) := (rfl)

theorem isClassFun_dadePullback {M : Type*} {K : Subgroup G} (p : K →* dadeStab L B) {f : L → M}
    (hf : IsClassFun f) : IsClassFun (dadePullback p f) := by
  refine isClassFun_iff.2 fun x g => ?_
  simp only [dadePullback, map_mul, map_inv]
  exact hf.conj _ _

theorem IsDadeData.dadePullback_dadeProj_apply_mul [Finite G] {M : Type*}
    (hD : IsDadeData L A H) (hBA : B ⊆ A) (hB : B.Nonempty) (f : L → M) {h u : G}
    (hh : h ∈ dadeInter H B) (hu : u ∈ dadeStab L B) :
    dadePullback (hD.dadeProj hBA hB) f
        ⟨h * u, (hD.mem_dadeSubsetGroup_iff hBA).2 ⟨h, hh, u, hu, rfl⟩⟩
      = f ⟨u, dadeStab_le_left hu⟩ := by
  rw [dadePullback_apply, hD.dadeProj_apply_mul hBA hB hh hu]
  rfl

end CFSG.FeitThompson
