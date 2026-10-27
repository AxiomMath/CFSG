module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherReducedWord
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSubflag

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix SymplecticFlag CFSG.Assembly.LowTwoRank SymplecticTorusWeyl

variable {r : ℕ} {K : Type} [Field K]

variable (K) in
@[expose] def borelCuts (A : Subgroup (StatedSp r K)) : Set ℕ :=
  {i | ∃ k : Fin r, (k : ℕ) + 1 = i ∧ weylRep K k ∉ A}

theorem borelCuts_le (A : Subgroup (StatedSp r K)) : ∀ i ∈ borelCuts K A, 1 ≤ i ∧ i ≤ r := by
  rintro i ⟨k, rfl, -⟩
  exact ⟨by omega, k.2⟩

theorem succ_mem_borelCuts_iff (A : Subgroup (StatedSp r K)) (k : Fin r) :
    (k : ℕ) + 1 ∈ borelCuts K A ↔ weylRep K k ∉ A := by
  constructor
  · rintro ⟨k', hk', hn⟩
    rwa [show k = k' from Fin.ext (by omega)]
  · intro hn
    exact ⟨k, rfl, hn⟩

theorem isLinePerm_prod_weylRep (l : List (Fin r)) :
    IsLinePerm (spWordProd l)
      (((((l.map (weylRep K)).prod : StatedSp r K)) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, Subgroup.coe_one, Units.val_one]
    exact isLinePerm_one
  | cons k l ih =>
    rw [List.map_cons, List.prod_cons, spWordProd_cons, Subgroup.coe_mul, Units.val_mul]
    exact (isLinePerm_weylRep k).mul ih

theorem borel_overgroups (A : Subgroup (StatedSp r K)) (hBA : borelSubgroup r K ≤ A) :
    A = flagStabilizer r K (borelCuts K A) ∧
    ∀ I : Set ℕ, (∀ i ∈ I, 1 ≤ i ∧ i ≤ r) → A = flagStabilizer r K I → I = borelCuts K A := by
  classical
  have hI : ∀ i ∈ borelCuts K A, i ≤ r := fun i hi => (borelCuts_le A i hi).2
  obtain ⟨hgen, hn, -⟩ := subflag_generation (K := K) (borelCuts K A) hI
  have hle : flagStabilizer r K (borelCuts K A) ≤ A := by
    rw [hgen, Subgroup.closure_le]
    rintro g (hg | ⟨k, hk, rfl⟩)
    · exact hBA hg
    · by_contra hn'
      exact hk ((succ_mem_borelCuts_iff A k).mpr hn')
  have heq : A = flagStabilizer r K (borelCuts K A) := by
    refine le_antisymm (fun g hg => ?_) hle
    obtain ⟨w, hw⟩ := (symplectic_bruhat (K := K)).1 g
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hw
    have hwA : dotW K w ∈ A := by
      have := mul_mem (mul_mem (inv_mem (hBA hb₁)) hg) (inv_mem (hBA hb₂))
      convert this using 1
      group
    have hconj : (borelSubgroup r K).map (MulAut.conj (dotW K w)).toMonoidHom ≤ A := by
      rintro _ ⟨b, hb, rfl⟩
      exact mul_mem (mul_mem hwA (hBA hb)) (inv_mem hwA)
    obtain ⟨l, hl, hprod⟩ := exists_word_length_eq _ (w : Equiv.Perm (Fin r ⊕ Fin r)) w.2 rfl
    have hred : IsSpReducedWord (w : Equiv.Perm (Fin r ⊕ Fin r)) l :=
      ⟨hprod, by rw [hl, spLength_eq_invCount w.2]⟩
    have hlA := reduced_word_extraction A hBA l w hconj hred
    have hP : (l.map (weylRep K)).prod ∈ flagStabilizer r K (borelCuts K A) := by
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      refine (hn k).mpr fun hkI => ?_
      exact ((succ_mem_borelCuts_iff A k).mp hkI) (hlA k hk)
    have hlin := isLinePerm_prod_weylRep (K := K) l
    rw [hprod] at hlin
    obtain ⟨t, ht, hPt⟩ := exists_torus_of_isLinePerm hlin
    have hBQ := borelSubgroup_le_flagStabilizer (K := K) hI
    have hdot : dotW K w = (l.map (weylRep K)).prod * t⁻¹ := by
      rw [hPt, mul_inv_cancel_right]
    rw [hdot]
    exact mul_mem (mul_mem (hBQ hb₁) (mul_mem hP (inv_mem (hBQ (torus_le_borelSubgroup ht)))))
      (hBQ hb₂)
  refine ⟨heq, fun I hI' hAI => ?_⟩
  have hn' := (subflag_generation (K := K) I fun i hi => (hI' i hi).2).2.1
  ext i
  constructor
  · intro hi
    obtain ⟨h1, h2⟩ := hI' i hi
    set k : Fin r := ⟨i - 1, by omega⟩
    have hk : (k : ℕ) + 1 = i := by simp [k]; omega
    refine ⟨k, hk, fun hkA => ?_⟩
    rw [hAI] at hkA
    exact (hn' k).mp hkA (hk ▸ hi)
  · rintro ⟨k, rfl, hkA⟩
    by_contra hkI
    exact hkA (hAI ▸ (hn' k).mpr hkI)

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
