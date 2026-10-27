module

public import CFSG.ClassicalInvolution.Q3.Q3T8Dich

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3
open scoped MatrixGroups

section Dich


variable {ι : Type} {Y : Type} [Group Y] {Φ : Set (Subgroup Y)}

@[expose] def lieSystemDataUOfOne (D : LieSystemData3 ι Y Φ) {i₀ : ι} (hone : ∀ i, i = i₀) :
    LieSystemDataU 3 1 (Fin 1) Y Φ where
  kind := fun _ => D.kind i₀
  valid := fun _ => by
    rcases D.valid i₀ with ⟨t, n, ht, hadm, hc⟩ | hc | hc
    · exact Or.inl ⟨t, n, 1, ht, hadm, Or.inl rfl, hc⟩
    · exact Or.inr ⟨by norm_num, Or.inl hc⟩
    · exact Or.inr ⟨by norm_num, Or.inr hc⟩
  hom := fun _ => D.hom i₀
  ker_le_center := fun _ => D.ker_le_center i₀
  commute := fun i j hij => absurd (Subsingleton.elim i j) hij
  generate := by
    rw [← D.generate]
    refine le_antisymm (iSup_le fun _ => le_iSup (fun j => (D.hom j).range) i₀)
      (iSup_le fun j => ?_)
    rw [hone j]
    exact le_iSup (fun _ : Fin 1 => (D.hom i₀).range) 0
  fundamental := fun L hL => by
    obtain ⟨i, R', hR, e⟩ := D.fundamental L hL
    obtain rfl := hone i
    exact ⟨0, R', hR, e⟩
  meets := fun _ => D.meets i₀
  card_eq := fun _ => D.card_eq

theorem dich_of_lieSystemData3 (D : LieSystemData3 ι Y Φ) {i₀ : ι} (hone : ∀ i, i = i₀)
    (hcase : D.kind i₀ = CompData.model .PSL 3 ∨ D.kind i₀ = CompData.m11)
    {J' : Subgroup Y} (hJ' : J' ∈ Φ) {ū : Y} (hū : ū ∈ J') {n : ℕ} (hn : 1 ≤ n)
    (hord : orderOf ū = 2 ^ (n + 1))
    (hmax : (Nat.card SL(2, GaloisField 3 1)).factorization 2 = n + 2)
    (β : MulAut Y) (hβ : β ū = ū) (hβ2 : β ^ 2 ^ (n + 1) = 1) :
    β ^ 2 ^ n = 1 ∨ β ^ 2 ^ n = MulAut.conj (ū ^ 2 ^ n) := by
  have hcase' : CompIs 3 1 ((lieSystemDataUOfOne D hone).kind 0) .PSL 3 ∨
      (lieSystemDataUOfOne D hone).kind 0 = CompData.m11 := by
    rcases hcase with hc | hc
    · exact Or.inl ⟨1, Or.inl rfl, trivial,
        ⟨Nat.prime_three, le_rfl, by norm_num, by norm_num, by norm_num⟩, hc⟩
    · exact Or.inr hc
  exact Q3T8.s26_dich_of_sysDataU (lieSystemDataUOfOne D hone) hcase' hJ' hū hn hord hmax β hβ hβ2

end Dich

end CFSG.ClassicalInvolution.Q3.Q3AM
