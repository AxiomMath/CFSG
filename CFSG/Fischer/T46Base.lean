
module

public import CFSG.Fischer.UnitaryPerm
import all CFSG.Fischer.F4
public import Certificates.Data.CFSGNative.Fi22.Local

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Sporadic.Fi22.Native Matrix

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

noncomputable abbrev piGU : GU0 →* Equiv.Perm (Fin 693) := MulAction.toPermHom GU0 (Fin 693)

theorem rep_piGU {T : Table} {g : GU0} (h : Rep 693 T g) : Rep 693 T (piGU g) := by
  intro i hi
  rw [h i hi, idx_of_lt _ hi, idx_of_lt _ hi]
  rfl

theorem tvGens_facts : tvGens.size = 46 ∧ ∀ k < 46, tvGens[k]! ∈ uPts := by
  have h := upts_ok
  unfold uPtsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, Array.contains_iff_mem] at h
  refine ⟨h.1.1.1.2, fun k hk => ?_⟩
  have hk' : k < tvGens.size := by rw [h.1.1.1.2]; exact hk
  rw [getElem!_pos tvGens k hk']
  exact h.2 k hk'

theorem tvGens_get_lt (k : ℕ) : tvGens[k]! < 4096 := by
  by_cases hk : k < 46
  · exact (mem_uPts.1 (tvGens_facts.2 k hk)).1
  · rw [getElem!_neg tvGens k (by rw [tvGens_facts.1]; exact hk)]
    decide

theorem tvGens_get_iso (k : ℕ) :
    hermStd (vecOfCode tvGens[k]!) (vecOfCode tvGens[k]!) = 0 := by
  by_cases hk : k < 46
  · have h := (mem_uPts.1 (tvGens_facts.2 k hk)).2.2.1
    rw [← codeOf_vecOfCode (tvGens_get_lt k), hermC_codeOf] at h
    exact (code_eq_zero_iff _).1 h
  · rw [getElem!_neg tvGens k (by rw [tvGens_facts.1]; exact hk)]
    decide

@[expose] noncomputable def t46G (z : ℤ) : Equiv.Perm (Fin 693) :=
  piGU (tvGU (vecOfCode tvGens[z.natAbs - 1]!) (tvGens_get_iso _))

theorem rep_t46G (z : ℤ) : Rep 693 (t46Gen z) (t46G z) := by
  unfold t46Gen t46G
  have := rep_tvTable (vecOfCode tvGens[z.natAbs - 1]!) (tvGens_get_iso _)
  rw [codeOf_vecOfCode (tvGens_get_lt _)] at this
  exact rep_piGU this

@[expose] noncomputable def t46gs (j : ℕ) : Equiv.Perm (Fin 693) := wordG t46G t46Words[j]!

theorem t46Letters_size : t46Letters.size = 2 * t46Words.size := by
  unfold t46Letters buildLetters; simp

theorem t46Letters_even {j : ℕ} (hj : j < t46Words.size) :
    t46Letters[2 * j]! = wordT 693 t46Gen t46Words[j]! := by
  unfold t46Letters buildLetters
  rw [getElem!_pos _ (2 * j) (by simp; omega), Array.getElem_ofFn]
  simp only
  rw [ite_eq_left (by omega)]
  congr 2
  omega

theorem rep_t46Letters : ∀ j < t46Letters.size / 2, Rep 693 t46Letters[2 * j]! (t46gs j) := by
  intro j hj
  rw [t46Letters_size] at hj
  rw [t46Letters_even (by omega)]
  exact Rep.wordT (by norm_num) _ fun l _ => rep_t46G l

theorem t46Q_get {t : ℕ} (ht : t < 693) : t46Q[t]! = t := by
  unfold t46Q
  rw [getElem!_pos _ t (by simpa using ht), Array.getElem_range]

theorem t46_sep (g : Equiv.Perm (Fin 693))
    (hg : ∀ t < t46Q.size, idx 693 g t46Q[t]! = t46Q[t]!) : g = 1 := by
  ext i
  have h := hg i.val (by unfold t46Q; simp)
  rw [t46Q_get i.2, idx_of_lt _ i.2] at h
  exact h

noncomputable abbrev t46lvl (i : ℕ) : Subgroup (Equiv.Perm (Fin 693)) :=
  levelGroup t46Letters t46Base (pairG t46gs) i

noncomputable abbrev T46 : Subgroup (Equiv.Perm (Fin 693)) := t46lvl 0

theorem t46Base_size : t46Base.size = 5 := rfl

end CFSG.Fischer
