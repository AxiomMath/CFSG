module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14Ae5Model

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsM

open CFSG.ClassicalInvolution.Q3.AE Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model

theorem zBar_mul_self (c : Fin 5) :
    zBar (miss c) (card_miss c) * zBar (miss c) (card_miss c) = 1 := by
  unfold zBar
  rw [← map_mul]
  have h : zOf (emb (miss c) (card_miss c)) * zOf (emb (miss c) (card_miss c)) = 1 := by
    calc zOf (emb (miss c) (card_miss c)) * zOf (emb (miss c) (card_miss c))
        = zOf (emb (miss c) (card_miss c)) * (zOf (emb (miss c) (card_miss c)))⁻¹ := by
          rw [zOf_inv]
      _ = 1 := mul_inv_cancel _
  rw [h, map_one]

@[expose] def pairVec (c d : Fin 5) : Wr 5 := ⟨fun x => if x = c ∨ x = d then 1 else 0, 1⟩

theorem zBar_mul_zBar {c d : Fin 5} (h : c ≠ d) :
    zBar (miss c) (card_miss c) * zBar (miss d) (card_miss d) = mkQ 5 (pairVec c d) := by
  unfold zBar
  rw [← map_mul]
  congr 1
  refine Wr.ext (funext fun x => ?_) ?_
  · have hmc : ∀ y : Fin 5, y ∈ Set.range (emb (miss c) (card_miss c)) ↔ y ≠ c := by
      intro y
      rw [range_emb]
      simp [miss]
    have hmd : ∀ y : Fin 5, y ∈ Set.range (emb (miss d) (card_miss d)) ↔ y ≠ d := by
      intro y
      rw [range_emb]
      simp [miss]
    have e1 : (1 : Equiv.Perm (Fin 5)).symm x = x := rfl
    rw [mul_vec, zOf_vec_apply, zOf_vec_apply, zOf_perm]
    simp only [hmc, hmd, e1]
    show _ = if x = c ∨ x = d then (1 : ZMod 2) else 0
    by_cases hxc : x = c
    · subst hxc
      have hxd : x ≠ d := h
      simp [hxd]
    · by_cases hxd : x = d
      · subst hxd
        simp [hxc]
      · simp [hxc, hxd]
        decide
  · rw [mul_perm, zOf_perm, zOf_perm]
    rfl

theorem mkQ_embed_w0 (ι : Fin 4 ↪ Fin 5) :
    mkQ 5 (embed ι w0) =
      zBar (miss (ι 0)) (card_miss _) * zBar (miss (ι 1)) (card_miss _) := by
  have h01 : ι 0 ≠ ι 1 := ι.injective.ne (by decide)
  rw [zBar_mul_zBar h01]
  congr 1
  refine Wr.ext (funext fun x => ?_) ?_
  · show (embed ι w0).vec x = if x = ι 0 ∨ x = ι 1 then (1 : ZMod 2) else 0
    have key := embed_w0_vec_eq_one_iff ι x
    by_cases hx : x = ι 0 ∨ x = ι 1
    · rw [if_pos hx]
      exact key.mpr hx
    · rw [if_neg hx]
      have hne : (embed ι w0).vec x ≠ 1 := fun h' => hx (key.mp h')
      generalize (embed ι w0).vec x = a at hne ⊢
      revert a
      decide
  · show (embed ι w0).perm = 1
    rw [embed_perm]
    exact embedPerm_one ι

theorem pair_aux : ∀ c d c' d' : Fin 5, c ≠ d → c' ≠ d' →
    (∀ x : Fin 5, (if x = c ∨ x = d then (1 : ZMod 2) else 0) = if x = c' ∨ x = d' then 1 else 0) →
      (c = c' ∧ d = d') ∨ (c = d' ∧ d = c') := by
  decide

theorem pair_aux' : ∀ c d c' d' : Fin 5, ¬ ∀ x : Fin 5,
    (if x = c ∨ x = d then (1 : ZMod 2) else 0) + (if x = c' ∨ x = d' then 1 else 0) = 1 := by
  decide

theorem eq_pair_of_mul_eq {c d c' d' : Fin 5} (hcd : c ≠ d) (hcd' : c' ≠ d')
    (h : zBar (miss c) (card_miss c) * zBar (miss d) (card_miss d) =
      zBar (miss c') (card_miss c') * zBar (miss d') (card_miss d')) :
    (c = c' ∧ d = d') ∨ (c = d' ∧ d = c') := by
  rw [zBar_mul_zBar hcd, zBar_mul_zBar hcd'] at h
  rcases mkQ_eq_iff.mp h with h1 | h1
  · have h2 : pairVec c d = pairVec c' d' := inv_mul_eq_one.mp h1
    refine pair_aux c d c' d' hcd hcd' fun x => ?_
    exact congrFun (congrArg Wr.vec h2) x
  · exfalso
    refine pair_aux' c d c' d' fun x => ?_
    have h2 := congrFun (congrArg Wr.vec h1) x
    exact h2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsM
