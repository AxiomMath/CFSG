module

public import CFSG.LargeExtraspecial.S111SJRee
public import CFSG.Goldschmidt.Steps.GoldType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.Open
open scoped MatrixGroups

theorem card_le_eight_of_nonBender
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (h : (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (L ≃* PSL(2, GaloisField p f))) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card L = ordRee (3 ^ (2 * m + 1))) ∨ Nonempty (L ≃* goldschmidtJ1))
    (A : Subgroup (MulAut L)) (hA : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 8 := by
  rcases h with ⟨p, f, hp, hpodd, hf, h5, hmod, ⟨e⟩⟩ | hRJ
  ·
    have hKcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
    have hfodd : Odd f :=
      ComponentClassification.AschbacherToolkit.Goldschmidt.odd_of_pow_mod_eight hpodd hmod
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
    set A' : Subgroup (MulAut (CFSG.GorensteinWalter.PSL2 (GaloisField p f))) :=
      A.map (MulAut.congr e).toMonoidHom with hA'
    have hA'sq : ∀ α ∈ A', α * α = 1 := by
      rintro _ ⟨α, hα, rfl⟩
      rw [← map_mul, hA α hα, map_one]
    have h4 := ComponentClassification.AschbacherToolkit.Goldschmidt.card_le_four_of_sq_eq_one
      hKcard hp2 hfodd (by rw [hKcard]; omega) A' hA'sq
    rw [hA', Subgroup.card_map_of_injective (MulAut.congr e).injective] at h4
    omega
  ·
    have hT := CFSG.Goldschmidt.GoldType.sylow_of_ree_or_j1 (K := L) hRJ
    obtain ⟨hnonab, -⟩ := hT default
    refine card_le_eight_of_sylow_eight hnonab (fun T => ?_) A hA
    obtain ⟨-, h8, hc, hsq⟩ := hT T
    exact ⟨h8, hc, fun t ht => by rw [← pow_two]; exact hsq t ht⟩

end CFSG.LargeExtraspecial.S11
