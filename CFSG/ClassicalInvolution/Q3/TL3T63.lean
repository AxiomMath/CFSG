module

public import CFSG.ClassicalInvolution.Q3.TL3T11

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G]

@[expose] noncomputable def AEIdent.conjE {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n)
    (g : G) : AEIdent (conjSub g '' P) n where
  φ := I.conjHom g
  range_eq := by
    rw [← I.range_eq]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(pSpanConj g P).symm y, (I.conjHom_apply g y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨pSpanConj g P y, I.conjHom_apply_conj g y⟩
  ker_le := by
    intro x hx
    have hx' : (pSpanConj g P).symm x ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, ← I.conjHom_apply]
      exact hx
    have hc := Subgroup.mem_center_iff.mp (I.ker_le hx')
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (pSpanConj g P) (hc ((pSpanConj g P).symm y))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  label := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    exact ⟨α, h, b, (I.map_conj g).trans hlab⟩
  label_surj := by
    intro α h b
    obtain ⟨L, hL, hlab⟩ := I.label_surj α h b
    exact ⟨conjSub g L, ⟨L, hL, rfl⟩, (I.map_conj g).trans hlab⟩

theorem AEIdent.conjE_apply {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (g : G)
    {y : G} (hy : y ∈ pSpan (conjSub g '' P)) (hy' : g⁻¹ * y * g ∈ pSpan P) :
    (I.conjE g).φ ⟨y, hy⟩ = I.φ ⟨g⁻¹ * y * g, hy'⟩ := by
  show I.conjHom g ⟨y, hy⟩ = _
  rw [AEIdent.conjHom_apply]
  congr 1

variable [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

end CFSG.ClassicalInvolution.Q3.TC.Thin
