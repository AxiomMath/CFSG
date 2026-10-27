module

import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG

section Aut

theorem card_mulAut_alternatingGroup_five :
    Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (le_refl 5)
    (by norm_num)
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]
  rfl

theorem conjNormal_injective_of_centralizer {G : Type*} [Group G] {S : Subgroup G} [S.Normal]
    (hcent : centralizer (S : Set G) = ⊥) : Function.Injective (MulAut.conjNormal (H := S)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  have hgc : g ∈ centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun f : MulAut ↥S => ((f ⟨x, hx⟩ : ↥S) : G)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  rw [hcent, Subgroup.mem_bot] at hgc
  exact hgc

theorem card_le_card_mulAut {G : Type*} [Group G] [Finite G] {S : Subgroup G} [S.Normal]
    (hcent : centralizer (S : Set G) = ⊥) : Nat.card G ≤ Nat.card (MulAut ↥S) :=
  Nat.card_le_card_of_injective _ (conjNormal_injective_of_centralizer hcent)

theorem centralizer_singleton_ne_top {G : Type*} [Group G] {S : Subgroup G}
    (hcent : centralizer (S : Set G) = ⊥) {t : G} (ht1 : t ≠ 1) :
    centralizer ({t} : Set G) ≠ ⊤ := by
  intro htop
  apply ht1
  have hmem : t ∈ centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x _
    have hx : x ∈ centralizer ({t} : Set G) := htop ▸ Subgroup.mem_top x
    exact mem_centralizer_singleton_iff.1 hx
  rw [hcent, Subgroup.mem_bot] at hmem
  exact hmem

end Aut

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
