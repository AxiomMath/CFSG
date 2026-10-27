module

public import CFSG.ClassicalInvolution.Q3.TL3T36

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

@[expose] def Model117At (n : ℕ) : Prop :=
  ∀ β : MulAut ↥(TL4.aeModel n),
    (∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      ∃ (α' : Finset (Fin n)) (h' : α'.card = 4) (b' : Bool),
        ((memBar α h b).subgroupOf (TL4.aeModel n)).map β.toMonoidHom =
          (memBar α' h' b').subgroupOf (TL4.aeModel n)) →
      ∃ x : AEQ n, ∀ g : ↥(TL4.aeModel n), ((β g : ↥(TL4.aeModel n)) : AEQ n) = x * g * x⁻¹

variable {G : Type} [Group G] {Z : Set (Subgroup G)} {j : ℕ}

theorem AEIdent.mem_aeModel (I : AEIdent Z j) (y : ↥(pSpan Z)) : I.φ y ∈ TL4.aeModel j := by
  show I.φ y ∈ (aeSub j).map (mkQ j)
  rw [← I.range_eq]
  exact ⟨y, rfl⟩

theorem AEIdent.ker_eq (hj : 5 ≤ j) (I₁ I₂ : AEIdent Z j) : I₁.φ.ker = I₂.φ.ker :=
  le_antisymm (fun _ hx => AEIdent.center_le_ker hj I₂ (I₁.ker_le hx))
    (fun _ hx => AEIdent.center_le_ker hj I₁ (I₂.ker_le hx))

theorem AEIdent.exists_aut (hj : 5 ≤ j) (I₁ I₂ : AEIdent Z j) :
    ∃ β : MulAut ↥(TL4.aeModel j), ∀ y : ↥(pSpan Z),
      ((β ⟨I₁.φ y, I₁.mem_aeModel y⟩ : ↥(TL4.aeModel j)) : AEQ j) = I₂.φ y := by
  set e₁ := QuotientGroup.quotientKerEquivRange I₁.φ with he₁
  set e₂ := QuotientGroup.quotientKerEquivRange I₂.φ with he₂
  set q := QuotientGroup.quotientMulEquivOfEq (I₁.ker_eq hj I₂) with hq
  set r₁ := MulEquiv.subgroupCongr I₁.range_eq with hr₁
  set r₂ := MulEquiv.subgroupCongr I₂.range_eq with hr₂
  refine ⟨r₁.symm.trans (e₁.symm.trans (q.trans (e₂.trans r₂))), fun y => ?_⟩
  have h1 : r₁.symm ⟨I₁.φ y, I₁.mem_aeModel y⟩ = ⟨I₁.φ y, ⟨y, rfl⟩⟩ := Subtype.ext rfl
  have h2 : e₁.symm ⟨I₁.φ y, ⟨y, rfl⟩⟩ = (y : ↥(pSpan Z) ⧸ I₁.φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  simp only [MulEquiv.trans_apply]
  rw [h1, h2, hq, QuotientGroup.quotientMulEquivOfEq_mk]
  show ((r₂ (e₂ (y : ↥(pSpan Z) ⧸ I₂.φ.ker))) : AEQ j) = I₂.φ y
  rfl

theorem AEIdent.exists_conj_of_model117 (hj : 5 ≤ j) (hM : Model117At j) (I₁ I₂ : AEIdent Z j) :
    ∃ x : AEQ j, ∀ y : ↥(pSpan Z), I₂.φ y = x * I₁.φ y * x⁻¹ := by
  obtain ⟨β, hβ⟩ := I₁.exists_aut hj I₂
  have hperm : ∀ (α : Finset (Fin j)) (h : α.card = 4) (b : Bool),
      ∃ (α' : Finset (Fin j)) (h' : α'.card = 4) (b' : Bool),
        ((memBar α h b).subgroupOf (TL4.aeModel j)).map β.toMonoidHom =
          (memBar α' h' b').subgroupOf (TL4.aeModel j) := by
    intro α h b
    obtain ⟨L, hL, hlab₁⟩ := I₁.label_surj α h b
    obtain ⟨α', h', b', hlab₂⟩ := I₂.label L hL
    refine ⟨α', h', b', ?_⟩
    ext ⟨g, hg⟩
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨⟨g₀, hg₀⟩, hg₀m, he⟩
      rw [Subgroup.mem_subgroupOf] at hg₀m
      change g₀ ∈ memBar α h b at hg₀m
      rw [← hlab₁] at hg₀m
      obtain ⟨y, hy, rfl⟩ := hg₀m
      have e := congrArg Subtype.val he
      rw [MulEquiv.coe_toMonoidHom] at e
      change ((β ⟨I₁.φ y, I₁.mem_aeModel y⟩ : ↥(TL4.aeModel j)) : AEQ j) = g at e
      rw [hβ y] at e
      show g ∈ memBar α' h' b'
      rw [← hlab₂, ← e]
      exact ⟨y, hy, rfl⟩
    · intro hgm
      change g ∈ memBar α' h' b' at hgm
      rw [← hlab₂] at hgm
      obtain ⟨y, hy, rfl⟩ := hgm
      refine ⟨⟨I₁.φ y, I₁.mem_aeModel y⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        show I₁.φ y ∈ memBar α h b
        rw [← hlab₁]
        exact ⟨y, hy, rfl⟩
      · exact Subtype.ext (hβ y)
  obtain ⟨x, hx⟩ := hM β hperm
  exact ⟨x, fun y => by rw [← hβ y, hx]⟩

end CFSG.ClassicalInvolution.Q3.TC.Thin
