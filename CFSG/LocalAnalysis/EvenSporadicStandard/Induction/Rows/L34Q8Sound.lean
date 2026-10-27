module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.QuatPair
public import Certificates.Certificate27213
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificateBase

public section

namespace CFSG.EvenSporadicStandard.L34Q8

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.EvenSporadicStandard.Induction.CoverFix

@[expose] def letterPerm (j : ℕ) : Equiv.Perm (Fin 42) :=
  [g₁, g₂, g₃, g₁⁻¹, g₂⁻¹, g₃⁻¹].getD j 1

theorem letterPerm_mem (j : ℕ) : letterPerm j ∈ S := by
  have h1 : g₁ ∈ S := Subgroup.subset_closure (by simp)
  have h2 : g₂ ∈ S := Subgroup.subset_closure (by simp)
  have h3 : g₃ ∈ S := Subgroup.subset_closure (by simp)
  unfold letterPerm
  rcases j with _ | _ | _ | _ | _ | _ | j
  · exact h1
  · exact h2
  · exact h3
  · exact S.inv_mem h1
  · exact S.inv_mem h2
  · exact S.inv_mem h3
  · simp

theorem letterPerm_inv {k : ℕ} (hk : k < 3) : letterPerm (k + 3) = (letterPerm k)⁻¹ := by
  interval_cases k <;> rfl

theorem letterTabs_zero : letterTabs[0]! = g₁T := rfl

theorem letterTabs_one : letterTabs[1]! = g₂T := rfl

theorem letterTabs_two : letterTabs[2]! = g₃T := rfl

theorem tabRep_letter (hinv : inverseLettersOK = true) {j : ℕ} (hj : j < 6) :
    TabRep letterTabs[j]! (letterPerm j) := by
  have h := hinv
  unfold inverseLettersOK at h
  rw [allBelow_eq_true] at h
  have hsz : ∀ k < 3, letterTabs[k + 3]!.size = 42 ∧
      comp 42 letterTabs[k + 3]! letterTabs[k]! = idTab 42 := by
    intro k hk
    have := h k hk
    simpa only [Bool.and_eq_true, beq_iff_eq] using this
  have hlt : ∀ k < 3, TabRep letterTabs[k]! (letterPerm k) := by
    intro k hk
    interval_cases k
    · rw [letterTabs_zero]
      exact tabRep_g₁
    · rw [letterTabs_one]
      exact tabRep_g₂
    · rw [letterTabs_two]
      exact tabRep_g₃
  by_cases hj3 : j < 3
  · exact hlt j hj3
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
    have hk : k < 3 := by omega
    rw [letterPerm_inv hk]
    exact (hlt k hk).inv (hsz k hk).1 (hsz k hk).2

theorem tabRep_wordT (hinv : inverseLettersOK = true) :
    ∀ w : List ℕ, (∀ j ∈ w, j < 6) → TabRep (wordT w) (w.map letterPerm).prod
  | [], _ => TabRep.idTab
  | j :: w, hw => by
    have h1 := tabRep_letter hinv (hw j (List.mem_cons_self))
    have h2 := tabRep_wordT hinv w fun k hk => hw k (List.mem_cons_of_mem _ hk)
    have e : wordT (j :: w) = comp 42 letterTabs[j]! (wordT w) := rfl
    rw [e, List.map_cons, List.prod_cons]
    exact h1.comp h2

theorem wordProd_mem (w : List ℕ) : (w.map letterPerm).prod ∈ S := by
  refine S.list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact letterPerm_mem j

theorem q8_data :
    ∃ x₁ y₁ x₄ y₄ : Equiv.Perm (Fin 42), x₁ ∈ S ∧ y₁ ∈ S ∧ x₄ ∈ S ∧ y₄ ∈ S ∧
      Q8Rel x₁ y₁ ∧ x₁ * x₁ = r₁ ∧ Q8Rel x₄ y₄ ∧ x₄ * r₄ = r₄ * x₄ ∧ y₄ * r₄ = r₄ * y₄ := by
  have h := Certificates.certificate27213
  simp only [q8OK, class1OK, class4OK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne, and_assoc] at h
  obtain ⟨-, hinv, h11, h12, h13, h14, h41, h42, h43, h44, h45⟩ := h
  have hX1 := tabRep_wordT hinv wX1 (by decide)
  have hY1 := tabRep_wordT hinv wY1 (by decide)
  have hX4 := tabRep_wordT hinv wX4 (by decide)
  have hY4 := tabRep_wordT hinv wY4 (by decide)
  have e11 := ((hX1.comp hX1).eq_iff tabRep_r₁).1 h11
  have e12 := ((hY1.comp hY1).eq_iff tabRep_r₁).1 h12
  have hr1 : r₁ ≠ 1 := fun h => h13 (((tabRep_r₁).eq_iff TabRep.idTab).2 h)
  refine ⟨_, _, _, _, wordProd_mem wX1, wordProd_mem wY1, wordProd_mem wX4, wordProd_mem wY4,
    ⟨e11.trans e12.symm, by rw [e11]; exact hr1,
      (((hX1.comp hY1).comp hX1).eq_iff hY1).1 h14⟩, e11,
    ⟨((hX4.comp hX4).eq_iff (hY4.comp hY4)).1 h41,
      fun h => h42 (((hX4.comp hX4).eq_iff TabRep.idTab).2 h),
      (((hX4.comp hY4).comp hX4).eq_iff hY4).1 h43⟩,
    ((hX4.comp tabRep_r₄).eq_iff (tabRep_r₄.comp hX4)).1 h44,
    ((hY4.comp tabRep_r₄).eq_iff (tabRep_r₄.comp hY4)).1 h45⟩

end CFSG.EvenSporadicStandard.L34Q8
