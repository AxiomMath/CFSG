module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Hyp
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Preimages

public section

open CFSG.Open

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

variable {G : Type} [Group G] {D : Subgroup G}
  {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem map_conj_mul (K : Subgroup G) (a b : G) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem fin_two_cases {i i' : Fin 2} (hii' : i ≠ i') (k : Fin 2) : k = i ∨ k = i' := by
  have h1 := i.isLt
  have h2 := i'.isLt
  have h3 := k.isLt
  have hne : i.val ≠ i'.val := fun h => hii' (Fin.ext h)
  rcases Nat.lt_or_ge k.val 1 with hk | hk
  · rcases Nat.lt_or_ge i.val 1 with hi | hi
    · exact Or.inl (Fin.ext (by omega))
    · exact Or.inr (Fin.ext (by omega))
  · rcases Nat.lt_or_ge i.val 1 with hi | hi
    · exact Or.inr (Fin.ext (by omega))
    · exact Or.inl (Fin.ext (by omega))

variable [Finite G]

theorem sq_map_factor (hyp : Hyp61 G D 2 Abar) {h : G}
    (hh : h ∈ Subgroup.normalizer (D : Set G)) (k : Fin 2) :
    (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj (h * h)).toMonoidHom =
      aschbacherThm5Preimage D (Abar k) := by
  have hinj : ∀ a b : Fin 2, aschbacherThm5Preimage D (Abar a) =
      aschbacherThm5Preimage D (Abar b) → a = b :=
    fun a b hab => hyp.hdistinct (preimage_injective D hab)
  have hmapinj : ∀ X Y : Subgroup G, X.map (MulAut.conj h).toMonoidHom =
      Y.map (MulAut.conj h).toMonoidHom → X = Y :=
    fun X Y hXY => Subgroup.map_injective (MulAut.conj h).injective hXY
  obtain ⟨j₁, h₁⟩ := hyp.hperm h hh k
  obtain ⟨j₂, h₂⟩ := hyp.hperm h hh j₁
  rw [map_conj_mul, h₁, h₂]
  by_cases hj₁ : j₁ = k
  · subst hj₁
    rw [← h₂, h₁]
  · have hj₂ : j₂ ≠ j₁ := by
      rintro rfl
      exact hj₁ (hinj _ _ (hmapinj _ _ (h₂.trans h₁.symm)))
    rcases fin_two_cases hj₁ j₂ with h | h
    · exact absurd h hj₂
    · rw [h]

theorem map_other_of_map (hyp : Hyp61 G D 2 Abar) {h : G}
    (hh : h ∈ Subgroup.normalizer (D : Set G)) {i i' : Fin 2} (hii' : i ≠ i')
    (hi : (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
      aschbacherThm5Preimage D (Abar i)) :
    (aschbacherThm5Preimage D (Abar i')).map (MulAut.conj h).toMonoidHom =
      aschbacherThm5Preimage D (Abar i') := by
  obtain ⟨j, hj⟩ := hyp.hperm h hh i'
  have hji : j ≠ i := by
    rintro rfl
    apply hii'
    apply hyp.hdistinct
    apply preimage_injective D
    exact Subgroup.map_injective (MulAut.conj h).injective (hi.trans hj.symm)
  rcases fin_two_cases hii' j with h | h
  · exact absurd h hji
  · rw [hj, h]

theorem map_eq_other_of_ne (hyp : Hyp61 G D 2 Abar) {h : G}
    (hh : h ∈ Subgroup.normalizer (D : Set G)) {i i' : Fin 2} (hii' : i ≠ i')
    (hi : (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom ≠
      aschbacherThm5Preimage D (Abar i)) :
    (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
      aschbacherThm5Preimage D (Abar i') := by
  obtain ⟨j, hj⟩ := hyp.hperm h hh i
  rcases fin_two_cases hii' j with h | h
  · rw [hj, h] at hi
    exact absurd rfl hi
  · rw [hj, h]

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
