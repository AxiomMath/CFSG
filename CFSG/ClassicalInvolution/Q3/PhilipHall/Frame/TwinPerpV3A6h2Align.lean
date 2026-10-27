module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h2Model

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S CFSG.Open CFSG.ClassicalInvolution.Generic

section Shape

variable {Y : Type} [Group Y] {K M L L₂ L₃ : Subgroup Y} {V : Fin 3 → Subgroup Y}

theorem shape_card_M (hS : AE6Shape K M L L₂ L₃ V) : Nat.card M = 12288 := by
  obtain ⟨-, -, -, -, -, h, -⟩ := hS
  exact h

theorem shape_edge (hS : AE6Shape K M L L₂ L₃ V) {k l : Fin 3} (h : k ≠ l) :
    pCoreOf 2 (V k) ≤ V k ⊓ V l ∧ Nat.card ↥(V k ⊓ V l) = 86016 := by
  obtain ⟨-, -, -, -, -, -, h', -⟩ := hS
  exact h' k l h

theorem shape_members (hS : AE6Shape K M L L₂ L₃ V) {k l : Fin 3} (h : k ≠ l) :
    {J | J ∈ ae6ConjIn (V k) K ∧ J ≤ V k ⊓ V l} = ae6ConjIn (V k ⊓ V l) K := by
  obtain ⟨-, -, -, -, -, -, -, h'⟩ := hS
  exact h' k l h

theorem shape_K_le (hS : AE6Shape K M L L₂ L₃ V) (k : Fin 3) : K ≤ V k := by
  obtain ⟨l, hl⟩ : ∃ l : Fin 3, k ≠ l := by revert k; decide
  have hK : K ∈ ae6ConjIn (V k ⊓ V l) K := ⟨1, one_mem _, conjSub_one K⟩
  rw [← shape_members hS hl] at hK
  exact hK.2.trans inf_le_left

theorem shape_le_of_mem (hS : AE6Shape K M L L₂ L₃ V) {k : Fin 3} {J : Subgroup Y}
    (hJ : J ∈ ae6ConjIn (V k) K) : J ≤ V k := by
  obtain ⟨g, hg, rfl⟩ := hJ
  exact conjSub_le_of_mem hg (shape_K_le hS k)

theorem shape_mem_M (hS : AE6Shape K M L L₂ L₃ V) {x : Y} : x ∈ M ↔ ∀ i : Fin 3, x ∈ V i := by
  obtain ⟨-, h01, h02, -, hM, -⟩ := hS
  rw [← hM, Subgroup.mem_inf, ← h01, ← h02, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨h0, h2⟩, -, h1⟩ i
    fin_cases i
    exacts [h0, h1, h2]
  · intro h
    exact ⟨⟨h 0, h 2⟩, h 0, h 1⟩

theorem shape_inf_inf (hS : AE6Shape K M L L₂ L₃ V) {k l m : Fin 3} (hkl : k ≠ l) (hkm : k ≠ m)
    (hlm : l ≠ m) : (V k ⊓ V l) ⊓ (V k ⊓ V m) = M := by
  have hall : ∀ k l m : Fin 3, k ≠ l → k ≠ m → l ≠ m → ∀ i, i = k ∨ i = l ∨ i = m := by decide
  ext x
  rw [shape_mem_M hS, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨hk, hl⟩, -, hm⟩ i
    rcases hall k l m hkl hkm hlm i with rfl | rfl | rfl <;> assumption
  · intro h
    exact ⟨⟨h k, h l⟩, h k, h m⟩

end Shape

section Carries

variable {Z : Type*} [Group Z] [Finite Z]

theorem carries_of_into {W : Subgroup Z} (β : ↥W ≃* ↥W) {P : Set (Subgroup Z)} (hP : ∀ J ∈ P, J ≤ W)
    (h : ∀ J ∈ P, ∃ J' ∈ P, Corr β J J') : Carries β P P := by
  refine ⟨h, ?_⟩
  choose f hfP hf using h
  let g : ↥P → ↥P := fun J => ⟨f J.1 J.2, hfP J.1 J.2⟩
  have hg : Function.Injective g := by
    intro J₁ J₂ hJ
    have h12 : f J₁.1 J₁.2 = f J₂.1 J₂.2 := congrArg Subtype.val hJ
    apply Subtype.ext
    have c1 := (hf J₁.1 J₁.2).symm
    have c2 := (hf J₂.1 J₂.2).symm
    rw [h12] at c1
    exact Corr.unique c1 c2 (hP _ J₁.2) (hP _ J₂.2)
  have hs : Function.Surjective g := Finite.injective_iff_surjective.mp hg
  intro J' hJ'
  obtain ⟨J, hJ⟩ := hs ⟨J', hJ'⟩
  refine ⟨J.1, J.2, ?_⟩
  have := hf J.1 J.2
  rwa [show f J.1 J.2 = J' from congrArg Subtype.val hJ] at this

end Carries

section Align

variable {Y : Type} [Group Y] {K M L L₂ L₃ : Subgroup Y} {V : Fin 3 → Subgroup Y}

theorem align_aux {k l : Fin 3} (ψ : ↥(V k) ≃* ↥(ae6ModelV k)) (β : MulAut ↥(ae6ModelV k))
    (hE : ((ae6ModelE k l).subgroupOf (ae6ModelV k)).map β.toMonoidHom =
      (tr ψ (V k ⊓ V l)).subgroupOf (ae6ModelV k)) :
    ∀ g : ↥(V k), (g : Y) ∈ V l ↔ ((β.symm (ψ g) : ↥(ae6ModelV k)) : AE6Om) ∈ ae6ModelV l := by
  intro g
  have h1 : (g : Y) ∈ V l ↔ (g : Y) ∈ V k ⊓ V l := ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  rw [h1, ← mem_tr_apply ψ g]
  have h2 : ((ψ g : ↥(ae6ModelV k)) : AE6Om) ∈ tr ψ (V k ⊓ V l) ↔
      ψ g ∈ (tr ψ (V k ⊓ V l)).subgroupOf (ae6ModelV k) := Iff.rfl
  rw [h2, ← hE, Subgroup.mem_map_equiv]
  exact ⟨fun h => h.2, fun h => ⟨(β.symm (ψ g)).2, h⟩⟩

theorem exists_aligned (hS : AE6Shape K M L L₂ L₃ V) (hT0 : AE6ModelEdgePairsMem)
    (ψ₀ : ∀ k, ↥(V k) ≃* ↥(ae6ModelV k))
    (hψ₀ : ∀ k, Carries (ψ₀ k) (ae6ConjIn (V k) K) (ae6ConjIn (ae6ModelV k) ae6ModelK)) (k : Fin 3) :
    ∃ ψ : ↥(V k) ≃* ↥(ae6ModelV k),
      Carries ψ (ae6ConjIn (V k) K) (ae6ConjIn (ae6ModelV k) ae6ModelK) ∧
        ∀ l, l ≠ k → ∀ g : ↥(V k), (g : Y) ∈ V l ↔ ((ψ g : ↥(ae6ModelV k)) : AE6Om) ∈ ae6ModelV l := by
  obtain ⟨l, m, hkl, hkm, hlm, hall⟩ : ∃ l m : Fin 3, k ≠ l ∧ k ≠ m ∧ l ≠ m ∧ ∀ i, i ≠ k → i = l ∨ i = m := by
    revert k; decide
  set ψ := ψ₀ k with hψ
  obtain ⟨hpl, hcl⟩ := shape_edge hS hkl
  obtain ⟨hpm, hcm⟩ := shape_edge hS hkm
  obtain ⟨β, hβl, hβm, hβ⟩ := hT0 k l m hkl hkm hlm (tr ψ (V k ⊓ V l)) (tr ψ (V k ⊓ V m))
    (tr_le ψ _) (tr_le ψ _) (pCoreOf_le_tr ψ hpl) (pCoreOf_le_tr ψ hpm)
    ((card_tr ψ inf_le_left).trans hcl) ((card_tr ψ inf_le_left).trans hcm)
    (by
      rw [tr_inf, card_tr ψ (inf_le_left.trans inf_le_left), shape_inf_inf hS hkl hkm hlm]
      exact shape_card_M hS)
  have hβc : Carries β (ae6ConjIn (ae6ModelV k) ae6ModelK) (ae6ConjIn (ae6ModelV k) ae6ModelK) :=
    carries_of_into β (fun J hJ => le_of_mem_conjIn_model hJ) hβ
  refine ⟨ψ.trans β.symm, (hψ₀ k).trans hβc.symm, fun i hi g => ?_⟩
  rcases hall i hi with rfl | rfl
  · exact align_aux ψ β hβl g
  · exact align_aux ψ β hβm g

end Align

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2
