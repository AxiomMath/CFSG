module

public import CFSG.ClassicalInvolution.Q3.TL3T11

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G]

@[expose] noncomputable def AEIdent.conjXHom {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n)
    (g : G) : ↥(pSpan (conjSub g '' P)) →* AE.AEQ n :=
  I.φ.comp (pSpanConj g P).symm.toMonoidHom

theorem AEIdent.conjXHom_apply {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (g : G)
    (y : ↥(pSpan (conjSub g '' P))) : I.conjXHom g y = I.φ ((pSpanConj g P).symm y) := by
  rw [AEIdent.conjXHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

theorem AEIdent.conjXHom_apply_conj {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (g : G)
    (x : ↥(pSpan P)) : I.conjXHom g (pSpanConj g P x) = I.φ x := by
  rw [AEIdent.conjXHom_apply, MulEquiv.symm_apply_apply]

@[expose] noncomputable def AEIdent.conjX {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (g : G) :
    AEIdent (conjSub g '' P) n where
  φ := I.conjXHom g
  range_eq := by
    rw [← I.range_eq]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(pSpanConj g P).symm y, (I.conjXHom_apply g y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨pSpanConj g P y, I.conjXHom_apply_conj g y⟩
  ker_le := by
    intro x hx
    have hx' : (pSpanConj g P).symm x ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, ← I.conjXHom_apply]; exact hx
    have hc := Subgroup.mem_center_iff.mp (I.ker_le hx')
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (pSpanConj g P) (hc ((pSpanConj g P).symm y))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  label := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    refine ⟨α, h, b, ?_⟩
    rw [← hlab]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(pSpanConj g P).symm y, ?_, (I.conjXHom_apply g y).symm⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, pSpanConj_symm_apply]
      exact mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hy)
    · rintro ⟨w, hw, rfl⟩
      refine ⟨pSpanConj g P w, ?_, I.conjXHom_apply_conj g w⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, pSpanConj_apply]
      exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hw)
  label_surj := by
    intro α h b
    obtain ⟨L, hL, hlab⟩ := I.label_surj α h b
    refine ⟨conjSub g L, ⟨L, hL, rfl⟩, ?_⟩
    rw [← hlab]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(pSpanConj g P).symm y, ?_, (I.conjXHom_apply g y).symm⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, pSpanConj_symm_apply]
      exact mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hy)
    · rintro ⟨w, hw, rfl⟩
      refine ⟨pSpanConj g P w, ?_, I.conjXHom_apply_conj g w⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, pSpanConj_apply]
      exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hw)

theorem AEIdent.conjX_φ_apply {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (g : G)
    (y : ↥(pSpan (conjSub g '' P))) : (I.conjX g).φ y = I.φ ((pSpanConj g P).symm y) :=
  I.conjXHom_apply g y

theorem AEIdent.conjX_ker_eq_bot {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (g : G)
    (hker : I.φ.ker = ⊥) : (I.conjX g).φ.ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : (pSpanConj g P).symm x ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, ← I.conjXHom_apply]; exact hx
  rw [hker, Subgroup.mem_bot] at hx'
  have := (pSpanConj g P).symm.injective (hx'.trans (map_one _).symm)
  exact this

end CFSG.ClassicalInvolution.Q3.TC.Thin
