module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBActionKernel

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup

variable {X₀ W H : Type*} [Group X₀] [Group W] [Group H]

theorem AutModel.bijective_conjNormal {X : Subgroup W} (hW : AutModel X₀ W X) :
    let := hW.normal
    Function.Bijective (MulAut.conjNormal : W →* MulAut ↥X) := by
  let := hW.normal
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_, fun α => ?_⟩
  · rw [eq_bot_iff]
    intro w hw
    rw [mem_bot, ← mem_bot, ← hW.centralizer_eq_bot, mem_centralizer_iff]
    intro x hx
    have h := congrArg (fun σ : MulAut ↥X => ((σ ⟨x, hx⟩ : ↥X) : W)) (MonoidHom.mem_ker.mp hw)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc x * w = w * x * w⁻¹ * w := by rw [h]
      _ = w * x := by group
  · obtain ⟨w, hw⟩ := hW.exists_conj α
    refine ⟨w, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [MulAut.conjNormal_apply, hw]

theorem exists_isActionHom {X : Subgroup W} (hW : AutModel X₀ W X) {B : Subgroup H}
    (hB : commutator B = ⊤) (e : ↥B ⧸ center ↥B ≃* X₀) :
    ∃ ψ : normalizer (B : Set H) →* W, IsActionHom B X ψ := by
  let := hW.normal
  obtain ⟨eX⟩ := hW.nonempty_mulEquiv
  let L : Subgroup (normalizer (B : Set H)) := B.subgroupOf (normalizer (B : Set H))
  let eL : ↥L ≃* ↥B := subgroupOfEquivOfLe le_normalizer
  have hBp : Group.IsPerfect ↥B := (Group.isPerfect_def).2 hB
  have hperf : Group.IsPerfect ↥L :=
    Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  let π : ↥L →* ↥X := eX.symm.toMonoidHom.comp
    (e.toMonoidHom.comp ((QuotientGroup.mk' (center ↥B)).comp eL.toMonoidHom))
  have hπ : Function.Surjective π :=
    eX.symm.surjective.comp (e.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp eL.surjective))
  have hker : π.ker = center ↥L := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [← map_center_eq eL]
    constructor
    · intro h
      obtain ⟨m, hm, hml⟩ := h
      rwa [eL.injective hml] at hm
    · intro h
      exact ⟨l, h, rfl⟩
  let θ := CentralCover.fullAction π hπ hker
  let β : W ≃* MulAut ↥X := MulEquiv.ofBijective _ hW.bijective_conjNormal
  have key : ∀ l : ↥L, β.symm (θ (l : normalizer (B : Set H))) = ((π l : ↥X) : W) := by
    intro l
    rw [MulEquiv.symm_apply_eq]
    change θ (l : normalizer (B : Set H)) = MulAut.conjNormal ((π l : ↥X) : W)
    rw [MulAut.conjNormal_val, CentralCover.fullAction_coe]
  refine ⟨β.symm.toMonoidHom.comp θ, fun a ha => ?_, fun x hx => ?_, fun n => ?_⟩
  ·
    have := key ⟨⟨a, le_normalizer ha⟩, ha⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [this]
    exact (π _).2
  ·
    obtain ⟨l, hl⟩ := hπ ⟨x, hx⟩
    refine ⟨((l : normalizer (B : Set H)) : H), l.2, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [key l, hl]
  ·
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    rw [← MonoidHom.mem_ker, CentralCover.ker_fullAction, mem_centralizer_iff,
      mem_centralizer_iff]
    constructor
    · intro h b hb
      have := h ⟨b, le_normalizer hb⟩ hb
      exact congrArg Subtype.val this
    · intro h m hm
      exact Subtype.ext (h (m : H) hm)

end CFSG.ComponentClassification.RankTwoSporadic
