module

public import CFSG.LargeExtraspecial.S111BA5End

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}
  {h k k' : G}

namespace Pair111

variable (P : Pair111 S g A h k k')
include P

theorem card_Lbar_eq_four' (hE4 : Nat.card (S.Lbar k) = 4 * Nat.card (Ebar S k k')) :
    Nat.card (S.Lbar k') = 4 * Nat.card (Ebar S k' k) := by
  rw [← P.card_Ebar_eq, P.hy'.cons.card_Lbar, ← P.hy.cons.card_Lbar]
  exact hE4

theorem fixSub_Ebar_eq_Ut' (hE4 : Nat.card (S.Lbar k) = 4 * Nat.card (Ebar S k k'))
    (hU4 : 4 ≤ finrank (ZMod 2) (S9.Ut S k (S.Lbar k ⊔ S.Lbar k'))) :
    fixSub S (Ebar S k k') = S9.Ut S k (S.Lbar k ⊔ S.Lbar k') ∧
      fixSub S (Ebar S k' k) = S9.Ut S k (S.Lbar k ⊔ S.Lbar k') ∧
      finrank (ZMod 2) (S9.Ut S k (S.Lbar k ⊔ S.Lbar k')) = 4 := by
  have hUE : S9.Ut S k (S.Lbar k ⊔ S.Lbar k') ≤ fixSub S (Ebar S k k') := by
    intro u hu
    refine (mem_fixSub S).mpr fun e he => P.fix_Ut_of_mem_O2Sub ?_ hu
    rw [← P.inf_O2Sub_eq] at he
    exact he.2
  have hUF : S9.Ut S k (S.Lbar k ⊔ S.Lbar k') ≤ fixSub S (Ebar S k' k) := by
    intro u hu
    refine (mem_fixSub S).mpr fun f hf => P.fix_Ut_of_mem_O2Sub ?_ hu
    rw [← P.inf_O2Sub_eq'] at hf
    exact hf.2
  have hE4' := finrank_fixSub_le_four_mul (S := S) (L := S.Lbar k) (E := Ebar S k k')
    inf_le_left (fun x hx y hy => Lbar_comm S P.memQ hx hy)
    (fun x hx => mul_self_of_mem_Lbar S P.memQ hx) hE4
  have hF4 := finrank_fixSub_le_four_mul (S := S) (L := S.Lbar k') (E := Ebar S k' k)
    inf_le_left (fun x hx y hy => Lbar_comm S P.memQ' hx hy)
    (fun x hx => mul_self_of_mem_Lbar S P.memQ' hx) (P.card_Lbar_eq_four' hE4)
  rw [P.finrank_fixSub_Lbar] at hE4'
  rw [P.swap.finrank_fixSub_Lbar] at hF4
  have hE := Submodule.eq_of_le_of_finrank_le hUE (by omega)
  have hF := Submodule.eq_of_le_of_finrank_le hUF (by omega)
  refine ⟨hE.symm, hF.symm, ?_⟩
  rw [← hE] at hE4'
  omega

theorem finrank_add_finrank_le' (hE4 : Nat.card (S.Lbar k) = 4 * Nat.card (Ebar S k k'))
    (hU4 : 4 ≤ finrank (ZMod 2) (S9.Ut S k (S.Lbar k ⊔ S.Lbar k'))) :
    finrank (ZMod 2) ↥(S.clSub A ⊓ fixSub S (Ebar S k k')) +
      finrank (ZMod 2) ↥(S.clSub (A.map (MulAut.conj h).toMonoidHom) ⊓ fixSub S (Ebar S k' k))
      ≤ 4 := by
  obtain ⟨hE, hF, h4⟩ := P.fixSub_Ebar_eq_Ut' hE4 hU4
  have hWU : S.clSub A ⊓ fixSub S (Ebar S k k') ≤ S9.Ut S k (S.Lbar k ⊔ S.Lbar k') :=
    hE ▸ inf_le_right
  have hW'U : S.clSub (A.map (MulAut.conj h).toMonoidHom) ⊓ fixSub S (Ebar S k' k) ≤
      S9.Ut S k (S.Lbar k ⊔ S.Lbar k') := hF ▸ inf_le_right
  have hdisj : (S.clSub A ⊓ fixSub S (Ebar S k k')) ⊓
      (S.clSub (A.map (MulAut.conj h).toMonoidHom) ⊓ fixSub S (Ebar S k' k)) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    exact P.eq_zero_of_mem_clSub (Submodule.mem_inf.mp (Submodule.mem_inf.mp hv).1).1
      (Submodule.mem_inf.mp (Submodule.mem_inf.mp hv).2).1
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq
    (S.clSub A ⊓ fixSub S (Ebar S k k'))
    (S.clSub (A.map (MulAut.conj h).toMonoidHom) ⊓ fixSub S (Ebar S k' k))
  rw [hdisj, finrank_bot, add_zero] at h1
  have h2 := Submodule.finrank_mono (sup_le hWU hW'U)
  omega

theorem false_of_finrank_two' (hidx : Nat.card (S.Lbar k) = 4 * Nat.card (Ebar S k k'))
    (hE : Ebar S k k' ≤ ptFix S (S.clSub A)) (hr : finrank (ZMod 2) (S.clSub A) = 2)
    (hmove : ∀ l ∈ S.Lbar k, l ∉ Ebar S k k' → ∃ y ∈ S.Lbar k ⊔ S.Lbar k',
      y ∈ normalizer (S.Lbar k : Set S.O) ∧ l⁻¹ * (y * l * y⁻¹) ∉ Ebar S k k') : False := by
  have hLK := P.card_Lbar_eq_card_Kbar_mul
  rw [hr] at hLK
  have hE0 : 0 < Nat.card (Ebar S k k') := Nat.card_pos
  have hK2 : Nat.card (Kbar S A k) = 2 * Nat.card (Ebar S k k') := by
    norm_num at hLK
    omega
  obtain ⟨k₀, hk₀K, hk₀E⟩ : ∃ x ∈ Kbar S A k, x ∉ Ebar S k k' := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show Kbar S A k ≤ Ebar S k k' from hcon)
    omega
  obtain ⟨y, hyX, hyN, hy⟩ := hmove k₀ hk₀K.1 hk₀E
  exact hy (P.inv_mul_conj_mem_Ebar hE hK2 hyX (P.mem_normalizer_Kbar hyX hyN) hk₀K hk₀E)

theorem false_of_index_four (hE4 : Nat.card (S.Lbar k) = 4 * Nat.card (Ebar S k k'))
    (hU4 : 4 ≤ finrank (ZMod 2) (S9.Ut S k (S.Lbar k ⊔ S.Lbar k')))
    (hmove : ∀ l ∈ S.Lbar k, l ∉ Ebar S k k' → ∃ y ∈ S.Lbar k ⊔ S.Lbar k',
      y ∈ normalizer (S.Lbar k : Set S.O) ∧ l⁻¹ * (y * l * y⁻¹) ∉ Ebar S k k') : False := by
  have hr2 := P.two_le_finrank_clSub
  have hrh := P.finrank_clSub_map
  have hsum := P.finrank_add_finrank_le' hE4 hU4
  have hW := P.finrank_W_eq hE4
  have hW' := P.swap.finrank_W_eq (P.card_Lbar_eq_four' hE4)
  have hWeq : Ebar S k k' ≤ ptFix S (S.clSub A) →
      finrank (ZMod 2) ↥(S.clSub A ⊓ fixSub S (Ebar S k k')) =
        finrank (ZMod 2) (S.clSub A) := fun hE => by
    rw [inf_eq_left.mpr fun v hv => (mem_fixSub S).mpr fun e he => mem_ptFix.mp (hE he) v hv]
  have hW'eq : Ebar S k' k ≤ ptFix S (S.clSub (A.map (MulAut.conj h).toMonoidHom)) →
      finrank (ZMod 2) ↥(S.clSub (A.map (MulAut.conj h).toMonoidHom) ⊓ fixSub S (Ebar S k' k)) =
        finrank (ZMod 2) (S.clSub (A.map (MulAut.conj h).toMonoidHom)) := fun hF => by
    rw [inf_eq_left.mpr fun v hv => (mem_fixSub S).mpr fun f hf => mem_ptFix.mp (hF hf) v hv]
  rcases hW with ⟨h3, -⟩ | hE <;> rcases hW' with ⟨h3', -⟩ | hF
  · omega
  · have := hW'eq hF
    omega
  · have := hWeq hE
    omega
  · have h1 := hWeq hE
    have h2 := hW'eq hF
    exact P.false_of_finrank_two' hE4 hE (by omega) hmove

end Pair111

end CFSG.LargeExtraspecial.S11
