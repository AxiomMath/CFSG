module

public import CFSG.CGT.Timmesfeld75.Sec3GlobalConj
public import CFSG.CGT.Timmesfeld75.Sec3Root

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Global

variable {G : Type} [Group G] [Finite G]

theorem orderOf_mul_cases_of_normIn_ne_bot {T U : Subgroup G} (hG : Sec3Global T) (hT : IsWC T)
    (hTU : T ≤ U)
    (hN : ∀ h ∈ U, ∀ g ∈ U, conjSubgroup h T ≠ conjSubgroup g T →
      normIn (conjSubgroup h T) (conjSubgroup g T) ≠ ⊥)
    {e f : G} (he : e ∈ classDIn U T) (hf : f ∈ classDIn U T) :
    (orderOf (e * f) = 2 ∨ orderOf (e * f) = 4 ∨ Odd (orderOf (e * f))) ∧
      (orderOf (e * f) = 4 → (e * f) ^ 2 ∈ classDIn U T) := by
  obtain ⟨he1, h, hh, heh⟩ := he
  obtain ⟨hf1, g, hg, hfg⟩ := hf
  by_cases hhg : conjSubgroup h T = conjSubgroup g T
  · have hef : e * f ∈ conjSubgroup h T := (conjSubgroup h T).mul_mem heh (hhg ▸ hfg)
    have h2 : (e * f) ^ 2 = 1 := (isElemAbelian_conjSubgroup hT.1 h).2 _ hef
    exact cases_of_sq_mem_conjSubgroup hT.1 hh (by rw [h2]; exact (conjSubgroup h T).one_mem)
  · have hgh : conjSubgroup (g * h⁻¹) (conjSubgroup h T) = conjSubgroup g T := by
      rw [conjSubgroup_conjSubgroup, show g * h⁻¹ * h = g by group]
    have hne : conjSubgroup (g * h⁻¹) (conjSubgroup h T) ≠ conjSubgroup h T := by
      rw [hgh]
      exact fun h' => hhg h'.symm
    have hL : normIn (conjSubgroup h T) (conjSubgroup (g * h⁻¹) (conjSubgroup h T)) ≠ ⊥ := by
      rw [hgh]
      exact hN h hh g hg hhg
    have hS := (hG.conj h) (g * h⁻¹) hne hL
    rw [hgh] at hS
    obtain ⟨-, hroot2, hroot3⟩ := hS.isRootInvolutionSet
    have he' : e ∈ classDIn (conjSubgroup h T ⊔ conjSubgroup g T) (conjSubgroup h T) :=
      ⟨he1, 1, one_mem _, by rwa [conjSubgroup_one]⟩
    have hf' : f ∈ classDIn (conjSubgroup h T ⊔ conjSubgroup g T) (conjSubgroup h T) := by
      obtain ⟨x, hx, hx'⟩ := hS.conj
      exact ⟨hf1, x, hx, by rw [← hx']; exact hfg⟩
    have hXU : conjSubgroup h T ⊔ conjSubgroup g T ≤ U :=
      sup_le (conjSubgroup_le_of_le_of_mem hTU hh) (conjSubgroup_le_of_le_of_mem hTU hg)
    exact ⟨hroot2 e he' f hf', fun h4 =>
      classDIn_conj_subset hXU hh (hroot3 e he' f hf' h4)⟩

theorem isRootInvolutionSet_classDIn_of_normIn_ne_bot {T U : Subgroup G} (hG : Sec3Global T)
    (hT : IsWC T) (hTU : T ≤ U)
    (hN : ∀ h ∈ U, ∀ g ∈ U, conjSubgroup h T ≠ conjSubgroup g T →
      normIn (conjSubgroup h T) (conjSubgroup g T) ≠ ⊥) :
    CFSG.Timmesfeld.IsRootInvolutionSet (classDIn U T) :=
  ⟨fun _ hd => orderOf_eq_two_of_mem_classDIn hT.1 hd,
    fun _ hd _ he => (orderOf_mul_cases_of_normIn_ne_bot hG hT hTU hN hd he).1,
    fun _ hd _ he => (orderOf_mul_cases_of_normIn_ne_bot hG hT hTU hN hd he).2⟩

theorem isRootInvolutionSet_classDIn_of_not_commute_of_global {T U : Subgroup G}
    (hG : Sec3Global T) (hT : IsWC T) (hTU : T ≤ U) (hO : ⁅pCoreOf 2 U, T⁆ ≠ ⊥) :
    CFSG.Timmesfeld.IsRootInvolutionSet (classDIn U T) :=
  isRootInvolutionSet_classDIn_of_normIn_ne_bot hG hT hTU fun _ hh _ hg _ =>
    normIn_conjSubgroup_ne_bot_of_pCoreOf hT hTU hO hh hg

end Global

end CFSG.CGT.Timmesfeld75
