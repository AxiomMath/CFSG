
module

public import CFSG.CGT.T75JM.N0ModelInputs

@[expose] public section

namespace CFSG.CGT.T75JM

open CFSG.CosetTable CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint

abbrev N0 : Type := PG 6 rels6

def n0 (w : List (Fin 6 × Bool)) : N0 := PresentedGroup.mk _ (FreeGroup.mk w)

theorem n0_nil : n0 [] = 1 := by
  rw [n0]; exact map_one _

theorem n0_append (w w' : List (Fin 6 × Bool)) : n0 (w ++ w') = n0 w * n0 w' := by
  rw [n0, n0, n0, ← map_mul, FreeGroup.mul_mk]

theorem n0_singleton (i : Fin 6) (b : Bool) :
    n0 [(i, b)] = if b then PresentedGroup.of i else (PresentedGroup.of i)⁻¹ := by
  cases b
  · show PresentedGroup.mk _ (FreeGroup.mk [(i, false)]) = _
    rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv]; rfl
  · rfl

theorem rep_m22L6 (hinv : n0InvCheck = true) {z : ℤ} (hz0 : z ≠ 0) (hz : z.natAbs ≤ 6) :
    Rep 22 (m22L z) (m22ImgG z) := by
  have hinv' : ∀ k, k < 6 → invOK 22 (m22T k) (m22V k) = true := by
    intro k hk
    simp only [n0InvCheck, List.all_eq_true, List.mem_range] at hinv
    exact hinv k hk
  have hz' : z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = -1 ∨ z = -2 ∨ z = -3 ∨
      z = -4 ∨ z = -5 ∨ z = -6 := by omega
  rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rep_m22T 0
  · exact rep_m22T 1
  · exact rep_m22T 2
  · exact rep_m22T 3
  · exact rep_m22T 4
  · exact rep_m22T 5
  · exact Rep.inv_of_invOK (rep_m22T 0) (hinv' 0 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m22T 1) (hinv' 1 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m22T 2) (hinv' 2 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m22T 3) (hinv' 3 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m22T 4) (hinv' 4 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m22T 5) (hinv' 5 (by norm_num))

theorem rep_n0Tab (hinv : n0InvCheck = true) (w : List (Fin 6 × Bool)) :
    Rep 22 (n0Tab w) (FreeGroup.lift m22Gen (FreeGroup.mk (liftWord w))) := by
  rw [← wordG_m22ImgG_map_letterZ]
  refine Rep.wordT (by norm_num) _ fun z hz => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
  obtain ⟨⟨i, b⟩, -, rfl⟩ := List.mem_map.1 hl
  have hi := i.isLt
  refine rep_m22L6 hinv ?_ ?_
  · cases b <;> simp [m22LetterZ] <;> omega
  · cases b <;> simp [m22LetterZ] <;> omega

noncomputable def n0Gen (i : Fin 6) : NativeSporadic.M22 := m22Gen i.castSucc

theorem evalWord7_m22Gen (w : List (Fin 6 × Bool)) :
    FreeGroup.lift m22Gen (FreeGroup.mk (liftWord w)) =
      FreeGroup.lift n0Gen (FreeGroup.mk w) := by
  have := evalWord7_liftWord m22Gen w
  rw [evalWord7] at this
  rw [this]
  rfl

theorem lift_n0Gen_eq_one (h1 : n0InvCheck = true) (h2 : n0RelCheck = true) :
    ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ rels6.map FreeGroup.mk},
      FreeGroup.lift n0Gen r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  have h3 : n0Tab w = idT 22 := by
    simp only [n0RelCheck, List.all_eq_true, beq_iff_eq] at h2
    exact h2 w hw
  have hr := rep_n0Tab h1 w
  rw [h3, evalWord7_m22Gen] at hr
  exact eq_of_rep_eq hr (Rep.idT (by norm_num))

theorem n0Tab_size (w : List (Fin 6 × Bool)) : (n0Tab w).size = 22 := wordT_size _ _ _

theorem n0_surj (n : N0) : ∃ w : List (Fin 6 × Bool), n = n0 w := by
  obtain ⟨x, rfl⟩ := PresentedGroup.mk_surjective _ n
  exact ⟨x.toWord, by rw [n0, FreeGroup.mk_toWord]⟩

theorem table_eq_of_rep {T T' : Table} {g : NativeSporadic.M22} (h : Rep 22 T g)
    (h' : Rep 22 T' g) (hs : T.size = 22) (hs' : T'.size = 22) : T = T' := by
  refine Array.ext (by rw [hs, hs']) fun i hi1 hi2 => ?_
  have hi : i < 22 := by rwa [hs] at hi1
  have := (h i hi).trans (h' i hi).symm
  unfold ap at this
  rw [getElem!_pos T i hi1, getElem!_pos T' i hi2] at this
  exact UInt32.toNat_inj.1 this

theorem compT_size (P Q : Table) : (compT 22 P Q).size = 22 := Array.size_ofFn

theorem n0_invWord (w : List (Fin 6 × Bool)) : n0 (invWord w) = (n0 w)⁻¹ := by
  rw [n0, n0, ← map_inv, FreeGroup.inv_mk, FreeGroup.invRev, invWord, List.map_reverse]

end CFSG.CGT.T75JM
