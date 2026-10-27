module

public import CFSG.Certificates.Kernel.OrbRow.Sound
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.KC.OrbRow

open Subgroup CFSG.KC.Enum

variable {n : ℕ}

theorem reach_perm {f : ℕ → ℕ → ℕ} {ok : ℕ → Prop} {b : ℕ} (σ : ℕ → Equiv.Perm (Fin n))
    (hσ : ∀ j, ok j → ∀ y (hy : y < n), ((σ j) ⟨y, hy⟩ : ℕ) = f j y) (hb : b < n) {x : ℕ}
    (hx : OrbReach f ok b x) :
    ∃ hxn : x < n, ∃ g ∈ closure (σ '' {j | ok j}), g ⟨b, hb⟩ = ⟨x, hxn⟩ := by
  induction hx with
  | root => exact ⟨hb, 1, one_mem _, rfl⟩
  | @step q j _ hj ih =>
    obtain ⟨hqn, g, hg, hgq⟩ := ih
    have hv := hσ j hj q hqn
    refine ⟨hv ▸ ((σ j) ⟨q, hqn⟩).2, σ j * g,
      mul_mem (subset_closure ⟨j, hj, rfl⟩) hg, ?_⟩
    rw [Equiv.Perm.mul_apply, hgq]
    exact Fin.ext hv

theorem orbit_of_rowsK {w m : ℕ} {S : List ℕ} {k lv D b cnt : ℕ} {R : List ℕ}
    (h : rowsK n w m S k lv D b cnt R = true) (σ : ℕ → Equiv.Perm (Fin n))
    (hσ : ∀ j, lvOk k lv j → ∀ y (hy : y < n), ((σ j) ⟨y, hy⟩ : ℕ) = pg w m (getS S j) y)
    (hb : b < n) :
    ∃ s : Finset (Fin n), s.card = cnt ∧
      ∀ x ∈ s, ∃ g ∈ closure (σ '' {j | lvOk k lv j}), g ⟨b, hb⟩ = x := by
  obtain ⟨s, hs, hsx⟩ := rowsK_sound h
  refine ⟨s.attach.map ⟨fun x => ⟨x.1, (hsx x.1 x.2).1⟩, fun x y he => ?_⟩, ?_, ?_⟩
  · exact Subtype.ext (congrArg Fin.val he)
  · rw [Finset.card_map, Finset.card_attach, hs]
  · intro x hx
    obtain ⟨⟨y, hy⟩, -, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨hyn, g, hg, hgy⟩ := reach_perm σ hσ hb (hsx y hy).2
    exact ⟨g, hg, hgy⟩

theorem fix_of_fixLvK {w m : ℕ} {S : List ℕ} {k lv : ℕ} {B : List ℕ} {i : ℕ}
    (h : fixLvK w m S k lv B i = true) (σ : ℕ → Equiv.Perm (Fin n))
    (hσ : ∀ j, lvOk k lv j → ∀ y (hy : y < n), ((σ j) ⟨y, hy⟩ : ℕ) = pg w m (getS S j) y)
    {j : ℕ} (hj : lvOk k lv j) {t : ℕ} (ht : t < i) (hbt : getS B t < n) :
    σ j ⟨getS B t, hbt⟩ = ⟨getS B t, hbt⟩ :=
  Fin.ext ((hσ j hj _ hbt).trans (fixLvK_sound h hj ht))

end CFSG.KC.OrbRow

end
