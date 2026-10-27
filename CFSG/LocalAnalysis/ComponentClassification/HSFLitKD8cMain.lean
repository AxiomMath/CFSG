module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cExcl60
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cHS

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

theorem ghRel_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    {z l α₁ α₂ α₃ α₄ x y a : G} (h : GHRel z l α₁ α₂ α₃ α₄ x y a) :
    GHRel (f z) (f l) (f α₁) (f α₂) (f α₃) (f α₄) (f x) (f y) (f a) where
  l_sq := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.l_sq
  α₁_sq := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.α₁_sq
  α₂_sq := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.α₂_sq
  α₃_sq := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.α₃_sq
  α₄_sq := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.α₄_sq
  z_sq := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.z_sq
  x_sq := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.x_sq
  y_sq := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.y_sq
  a_sq := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.a_sq
  c_a1_a3 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_a1_a3
  c_a2_a4 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_a2_a4
  c_x_a1 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_x_a1
  c_x_a2 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_x_a2
  c_y_a2 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_y_a2
  c_a_l := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_a_l
  c_x_a3 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_x_a3
  c_x_a4 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_x_a4
  c_y_a3 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_y_a3
  c_y_a4 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_y_a4
  c_a_a1 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_a_a1
  c_a_a2 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_a_a2
  c_a_a3 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_a_a3
  c_a_a4 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_a_a4
  c_a_y := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.c_a_y
  comm_z_l := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_z_l
  comm_z_a1 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_z_a1
  comm_z_a2 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_z_a2
  comm_z_a3 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_z_a3
  comm_z_a4 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_z_a4
  comm_z_x := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_z_x
  comm_z_y := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_z_y
  comm_z_a := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_z_a
  comm_l_a1 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_l_a1
  comm_l_a2 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_l_a2
  comm_l_a3 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_l_a3
  comm_l_a4 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_l_a4
  comm_l_x := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_l_x
  comm_l_y := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_l_y
  comm_a1_a2 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_a1_a2
  comm_a1_a4 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_a1_a4
  comm_a1_y := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_a1_y
  comm_a2_a3 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_a2_a3
  comm_a3_a4 := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_a3_a4
  comm_x_y := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_x_y
  comm_x_a := by simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h.comm_x_a

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace Conf

namespace T2

namespace Lift

variable {K : Conf S T₁} {T : K.T2}

theorem exists_ghRel (W : T.Lift) (hj : W.j = 0) :
    ∃ z l α₁ α₂ α₃ α₄ x y a : X, GHRel z l α₁ α₂ α₃ α₄ x y a ∧
      closure ({z, l, α₁, α₂, α₃, α₄, x, y, a} : Set X) = T.P := by
  obtain ⟨j, i, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩ := W
  simp only at hj
  subst hj
  let W : T.Lift := ⟨0, i, hj3, hj4, Q, hQ, hs, hQm, hQn, hcs⟩
  let ψ : T22h i →* X := W.ψ
  have hψ : ψ.range = T.P := W.range_ψ
  refine ⟨ψ (gh i 0), ψ (gh i 1), ψ (gh i 2), ψ (gh i 3), ψ (gh i 4), ψ (gh i 5), ψ (gh i 6),
    ψ (gh i 7), ψ (gh i 8), ghRel_map ψ (ghRel_hat i), ?_⟩
  rw [← hψ, MonoidHom.range_eq_map, ← closure_gh i, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]

end Lift

end T2

end Conf

theorem cases_j : ∀ j : Fin 8, ∀ i : Fin 2, j ≠ 3 → j ≠ 4 → j ≠ 0 → (j = 6 ∧ i = 0) ∨
    ((j = 1 ∧ i = 0) ∨ (j = 1 ∧ i = 1) ∨ (j = 2 ∧ i = 0) ∨ (j = 2 ∧ i = 1) ∨
      (j = 7 ∧ i = 0) ∨ (j = 7 ∧ i = 1) ∨ (j = 5 ∧ i = 0) ∨ (j = 5 ∧ i = 1) ∨
      (j = 6 ∧ i = 1)) := by
  decide


theorem fritzKDSection8c : FritzKDSection8c := by
  intro _ X _ _ _ hnonab _ t L A C S T₁ h4 D₁ D₂ hq₁ hq₂
  let K : Conf S T₁ := ⟨h4, D₁, D₂, hq₁, hq₂⟩
  obtain ⟨T⟩ := K.nonempty_T2
  obtain ⟨W⟩ := T.nonempty_lift
  have hj : W.j = 0 := by
    by_contra h0
    rcases cases_j W.j W.i W.hj3 W.hj4 h0 with h | h
    · exact W.false_of_cert60 hnonab h.1 h.2
    · exact W.false_of_cert hnonab h
  obtain ⟨z, l, α₁, α₂, α₃, α₄, x, y, a, hrel, hcl⟩ := W.exists_ghRel hj
  exact ⟨W.sylow, z, l, α₁, α₂, α₃, α₄, x, y, a, hrel, hcl, W.card_P⟩

end KD8c

end CFSG.ComponentClassification.HSFLit
