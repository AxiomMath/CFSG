
module

public import CFSG.CGT.T75M23.N7ModelInputs
public import CFSG.CGT.T75M23.N7Group
public import CFSG.CGT.T75JM.Interfaces
public import Certificates.Certificate271010

@[expose] public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint

instance : Finite N7 := Certificates.certificate271010.2.2.1

theorem n7GenT_get (k : ℕ) (hk : k < 6) : n7GenT[k]! = m23T k := by
  interval_cases k <;> rfl

theorem n7GenV_get (k : ℕ) (hk : k < 6) : n7GenV[k]! = m23V k := by
  interval_cases k <;> rfl

theorem n7L_eq {z : ℤ} (hz0 : z ≠ 0) (hz : z.natAbs ≤ 6) : n7L z = m23L z := by
  have hz' : z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = -1 ∨ z = -2 ∨ z = -3 ∨
      z = -4 ∨ z = -5 ∨ z = -6 := by omega
  rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem rep_m23L6 (hinv : n7InvCheck = true) {z : ℤ} (hz0 : z ≠ 0) (hz : z.natAbs ≤ 6) :
    Rep 23 (m23L z) (m23ImgG z) := by
  have hinv' : ∀ k, k < 6 → invOK 23 (m23T k) (m23V k) = true := by
    intro k hk
    simp only [n7InvCheck, List.all_eq_true, List.mem_range] at hinv
    have := hinv k hk
    rwa [n7GenT_get k hk, n7GenV_get k hk] at this
  have hz' : z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = -1 ∨ z = -2 ∨ z = -3 ∨
      z = -4 ∨ z = -5 ∨ z = -6 := by omega
  rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rep_m23T 0
  · exact rep_m23T 1
  · exact rep_m23T 2
  · exact rep_m23T 3
  · exact rep_m23T 4
  · exact rep_m23T 5
  · exact Rep.inv_of_invOK (rep_m23T 0) (hinv' 0 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m23T 1) (hinv' 1 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m23T 2) (hinv' 2 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m23T 3) (hinv' 3 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m23T 4) (hinv' 4 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m23T 5) (hinv' 5 (by norm_num))

theorem rep_n7Tab (hinv : n7InvCheck = true) (w : List (Fin 6 × Bool)) :
    Rep 23 (n7Tab w) (FreeGroup.lift m23Gen (FreeGroup.mk (liftWord7 w))) := by
  rw [← wordG_m23ImgG_map_letterZ]
  refine Rep.wordT (by norm_num) _ fun z hz => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
  obtain ⟨⟨i, b⟩, -, rfl⟩ := List.mem_map.1 hl
  have hi := i.isLt
  have hz0 : m23LetterZ (⟨i, by omega⟩, b) ≠ 0 := by cases b <;> simp [m23LetterZ] <;> omega
  have hz6 : (m23LetterZ ((⟨i, by omega⟩ : Fin 7), b)).natAbs ≤ 6 := by
    cases b <;> simp [m23LetterZ] <;> omega
  have := rep_m23L6 hinv hz0 hz6
  rw [← n7L_eq hz0 hz6] at this
  exact this

@[expose] noncomputable def n7Gen (i : Fin 6) : NativeSporadic.M23 := m23Gen i.castSucc

theorem evalWord7_m23Gen (w : List (Fin 6 × Bool)) :
    FreeGroup.lift m23Gen (FreeGroup.mk (liftWord7 w)) =
      FreeGroup.lift n7Gen (FreeGroup.mk w) := by
  have := CFSG.CGT.T75JM.evalWord7_liftWord m23Gen w
  rw [CFSG.CGT.T75JM.evalWord7] at this
  have h : FreeGroup.lift m23Gen (FreeGroup.mk (liftWord7 w)) =
      FreeGroup.lift m23Gen (FreeGroup.mk (CFSG.CGT.T75JM.liftWord w)) := rfl
  rw [h, this]
  rfl

theorem lift_n7Gen_eq_one (h1 : n7InvCheck = true) (h2 : n7RelCheck = true) :
    ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ rels7.map FreeGroup.mk},
      FreeGroup.lift n7Gen r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  have h3 : n7Tab w = idT 23 := by
    simp only [n7RelCheck, List.all_eq_true, beq_iff_eq] at h2
    exact h2 w hw
  have hr := rep_n7Tab h1 w
  rw [h3, evalWord7_m23Gen] at hr
  exact eq_of_rep_eq hr (Rep.idT (by norm_num))

theorem n7Tab_size (w : List (Fin 6 × Bool)) : (n7Tab w).size = 23 := wordT_size _ _ _

theorem table_eq_of_rep {T T' : Table} {g : NativeSporadic.M23} (h : Rep 23 T g)
    (h' : Rep 23 T' g) (hs : T.size = 23) (hs' : T'.size = 23) : T = T' := by
  refine Array.ext (by rw [hs, hs']) fun i hi1 hi2 => ?_
  have hi : i < 23 := by rwa [hs] at hi1
  have := (h i hi).trans (h' i hi).symm
  unfold ap at this
  rw [getElem!_pos T i hi1, getElem!_pos T' i hi2] at this
  exact UInt32.toNat_inj.1 this

theorem compT_size (P Q : Table) : (compT 23 P Q).size = 23 := Array.size_ofFn

end CFSG.CGT.T75M23
