module

public import CFSG.Certificates.Kernel.CoPairSound
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Mathlib.Data.Set.Card

public section

namespace CFSG.KC.CoPair

open CFSG.Monster.Existence.CoPair.Native CFSG.KC.AxisPlane

theorem genXY_zero_eq (v : Nat) : genXY 0 v = actLetters xWordN v := by
  simp [genXY, actXY]

theorem genXY_one_eq (v : Nat) : genXY 1 v = actLetters yWordN v := by
  simp [genXY, actXY]

theorem orbitOf_of_orbOK {seed N : Nat} {D : OrbData} (h : orbOK xWordN yWordN seed N D = true) :
    orbitOf 2 genXY seed ⊆ Set.Iio (2 ^ 24) ∧ (orbitOf 2 genXY seed).ncard = N := by
  obtain ⟨hs, hseed, hmono, hX, hY, hreach⟩ := orbOK_sound h
  let F : Finset Nat := (Finset.range N).image (f24 D.P)
  have hmem : ∀ x, x ∈ F ↔ ∃ i < N, f24 D.P i = x := by simp [F]
  have hsub : ∀ v, Relation.ReflTransGen (fun a b => ∃ g < 2, b = genXY g a) seed v → v ∈ F := by
    intro v hv
    induction hv with
    | refl => exact (hmem seed).2 ⟨D.s, hs, hseed⟩
    | tail _ hab ih =>
      obtain ⟨g, hg, rfl⟩ := hab
      obtain ⟨i, hi, hia⟩ := (hmem _).1 ih
      rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
      · obtain ⟨j, hj, hji⟩ := hX i hi
        exact (hmem _).2 ⟨j, hj, by rw [hji, genXY_zero_eq, hia]⟩
      · obtain ⟨j, hj, hji⟩ := hY i hi
        exact (hmem _).2 ⟨j, hj, by rw [hji, genXY_one_eq, hia]⟩
  have hsup : ∀ x, Reach2 (actLetters xWordN) (actLetters yWordN) seed x →
      Relation.ReflTransGen (fun a b => ∃ g < 2, b = genXY g a) seed x := by
    intro x hx
    induction hx with
    | base => exact Relation.ReflTransGen.refl
    | left _ ih => exact ih.tail ⟨0, by omega, (genXY_zero_eq _).symm⟩
    | right _ ih => exact ih.tail ⟨1, by omega, (genXY_one_eq _).symm⟩
  have heq : orbitOf 2 genXY seed = (F : Set Nat) := by
    apply Set.Subset.antisymm
    · exact fun v hv => hsub v hv
    · intro v hv
      obtain ⟨i, hi, rfl⟩ := (hmem v).1 hv
      exact hsup _ (hreach i hi)
  have hinjP : Set.InjOn (f24 D.P) (Finset.range N : Set Nat) := fun i hi j hj hij => by
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact absurd hij (Nat.ne_of_lt (hmono i j h' hj))
    · exact absurd hij (Nat.ne_of_gt (hmono j i h' hi))
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [heq] at hv
    obtain ⟨i, -, rfl⟩ := (hmem v).1 hv
    exact f24_lt _ _
  · rw [heq, Set.ncard_coe_finset, Finset.card_image_of_injOn hinjP, Finset.card_range]

end CFSG.KC.CoPair

end
