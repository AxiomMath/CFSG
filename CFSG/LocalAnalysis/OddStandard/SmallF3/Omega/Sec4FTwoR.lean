module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FTwoSetup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FTwoGrp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FBlock

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B P : Subgroup G}
  {x : G} {φ : (Fin 7 → ZMod 2) → G}

private theorem sec4F_comm_iff_conj_eq {G : Type*} [Group G] (a b : G) :
    a * b = b * a ↔ a * b * a⁻¹ = b := by
  constructor
  · intro h
    rw [h]
    group
  · intro h
    calc a * b = a * b * a⁻¹ * a := by group
      _ = b * a := by rw [h]

private theorem sec4F_swap_ne_self_iff {Ω : Type*} [DecidableEq Ω] {w w' x : Ω} (hw : w ≠ w') :
    (x = w ∨ x = w') ↔ ¬ Equiv.swap w w' x = x := by
  constructor
  · rintro (rfl | rfl)
    · rw [Equiv.swap_apply_left]
      exact fun h => hw h.symm
    · rw [Equiv.swap_apply_right]
      exact hw
  · intro h
    by_contra hx
    push Not at hx
    exact h (Equiv.swap_apply_of_ne_of_ne hx.1 hx.2)

theorem Sec4FSetup.R_left (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x)
    (c : Option (Fin 7)) :
    ∃ u v : Option (Fin 7), u ≠ v ∧ (∀ g, sec4FR t φ x g c ↔ g = u ∨ g = v) ∧
      Sec4MRealizes t φ (sec4FD t φ x c) (Equiv.swap u v) := by
  obtain ⟨u, v, huv, hr⟩ := h.d_swap hT c
  refine ⟨u, v, huv, fun g => ?_, hr⟩
  show ¬ (sec4MPt t φ g * sec4FD t φ x c = sec4FD t φ x c * sec4MPt t φ g) ↔
    g = u ∨ g = v
  have hfix : (sec4MPt t φ g * sec4FD t φ x c = sec4FD t φ x c * sec4MPt t φ g) ↔
      Equiv.swap u v g = g := by
    constructor
    · intro hcomm
      apply h.pt_injective
      rw [← hr g]
      exact (sec4F_comm_iff_conj_eq (sec4FD t φ x c) (sec4MPt t φ g)).mp hcomm.symm
    · intro hσ
      have h1 : sec4FD t φ x c * sec4MPt t φ g * (sec4FD t φ x c)⁻¹ = sec4MPt t φ g := by
        rw [hr g, hσ]
      exact ((sec4F_comm_iff_conj_eq (sec4FD t φ x c) (sec4MPt t φ g)).mpr h1).symm
  rw [hfix, ← sec4F_swap_ne_self_iff huv]

theorem Sec4FSetup.R_right (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x)
    (a : Option (Fin 7)) :
    ∃ u v : Option (Fin 7), u ≠ v ∧ (∀ c, sec4FR t φ x a c ↔ c = u ∨ c = v) ∧
      ∀ c, sec4MPt t φ a * sec4FD t φ x c * (sec4MPt t φ a)⁻¹ =
        sec4FD t φ x (Equiv.swap u v c) := by
  obtain ⟨u, v, huv, hr⟩ := h.pt_d hT a
  refine ⟨u, v, huv, fun c => ?_, hr⟩
  show ¬ (sec4MPt t φ a * sec4FD t φ x c = sec4FD t φ x c * sec4MPt t φ a) ↔
    c = u ∨ c = v
  have hfix : (sec4MPt t φ a * sec4FD t φ x c = sec4FD t φ x c * sec4MPt t φ a) ↔
      Equiv.swap u v c = c := by
    rw [sec4F_comm_iff_conj_eq, hr c]
    exact h.d_inj.eq_iff
  rw [hfix, ← sec4F_swap_ne_self_iff huv]

theorem Sec4FSetup.R_overlap (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x)
    {c c' g : Option (Fin 7)} (hc : sec4FR t φ x g c) (hc' : sec4FR t φ x g c') :
    ∀ g', sec4FR t φ x g' c ↔ sec4FR t φ x g' c' := by
  obtain ⟨u, v, huv, hRl, hr⟩ := h.R_left hT c
  obtain ⟨u', v', huv', hRl', hr'⟩ := h.R_left hT c'
  have hgu : g = u ∨ g = v := (hRl g).mp hc
  have hgu' : g = u' ∨ g = v' := (hRl' g).mp hc'
  have hov : u = u' ∨ u = v' ∨ v = u' ∨ v = v' := by
    rcases hgu with hg | hg <;> rcases hgu' with hg' | hg'
    · exact Or.inl (hg.symm.trans hg')
    · exact Or.inr (Or.inl (hg.symm.trans hg'))
    · exact Or.inr (Or.inr (Or.inl (hg.symm.trans hg')))
    · exact Or.inr (Or.inr (Or.inr (hg.symm.trans hg')))
  have hswap : Equiv.swap u v = Equiv.swap u' v' :=
    h.swap_overlap hT.P2 (h.d_mem_P hT c) (h.d_mem_P hT c') huv huv' hr hr' hov
  intro g'
  rw [hRl g', hRl' g', sec4F_swap_ne_self_iff huv, sec4F_swap_ne_self_iff huv']
  rw [DFunLike.congr_fun hswap g']

theorem Sec4FSetup.blocks (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x)
    (a : Option (Fin 7)) :
    ∃ a' c c' : Option (Fin 7), Sec4FBlock (sec4FR t φ x) a a' c c' := by
  refine sec4F_block_exists (sec4FR t φ x) (fun c => ?_) (fun a => ?_)
    (fun c c' g hc hc' => h.R_overlap hT hc hc') a
  · obtain ⟨u, v, huv, hR, -⟩ := h.R_left hT c
    exact ⟨u, v, huv, hR⟩
  · obtain ⟨u, v, huv, hR, -⟩ := h.R_right hT a
    exact ⟨u, v, huv, hR⟩

end CFSG.OddStandard.SmallF3.Omega
