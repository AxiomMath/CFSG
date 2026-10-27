module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.Sporadic.HS.Chain

public section

namespace CFSG.QuasithinUnique.K1.SporadicPerm

open CFSG.Sporadic.SmallF2
open CFSG.Sporadic.SmallF2.Native (VecData)

variable {D : VecData} {c : ℕ}

theorem eq_one_of_fix_base (hF : Facts D c) (g : J D)
    (hg : ∀ i < D.base.size, CFSG.Sporadic.Th.idx D.n g D.base[i]! = D.base[i]!) : g = 1 := by
  have key : ∀ i ≤ D.base.size, g ∈ lvl D i := by
    intro i
    induction i with
    | zero => intro _; rw [lvl_zero hF]; exact Subgroup.mem_top g
    | succ i ih =>
      intro hi
      exact ((chain_facts' hF).2.1 i (by omega) g (ih (by omega))).1 (hg i (by omega))
  have hcard : Nat.card (lvl D D.base.size) = 1 := by
    rw [card_lvl hF le_rfl]; simp
  have hbot : lvl D D.base.size = ⊥ := Subgroup.card_eq_one.mp hcard
  have hg' := key D.base.size le_rfl
  rw [hbot] at hg'
  exact Subgroup.mem_bot.mp hg'

theorem base_lt (hF : Facts D c) : ∀ b ∈ D.base.toList, b < D.n := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have hi' : i < D.base.size := by simpa using hi
  have := ((chain_facts' hF).1 i hi').r_lt
  simpa [getElem!_pos D.base i hi'] using this

theorem base_property (hF : Facts D c) :
    ∀ g : J D, (∀ b ∈ D.base.toList, act D.n g b = b) → g = 1 := by
  intro g hg
  apply eq_one_of_fix_base hF
  intro i hi
  have hb : D.base[i]! < D.n := ((chain_facts' hF).1 i hi).r_lt
  have hmem : D.base[i]! ∈ D.base.toList := by
    rw [getElem!_pos D.base i hi]
    exact Array.getElem_mem_toList hi
  rw [CFSG.Sporadic.Th.idx_of_lt g hb]
  have h1 := hg _ hmem
  have h2 : act D.n g D.base[i]! = (g • (⟨D.base[i]!, hb⟩ : Fin D.n)).val :=
    act_eq g ⟨D.base[i]!, hb⟩
  rw [h2] at h1
  exact h1

end CFSG.QuasithinUnique.K1.SporadicPerm
