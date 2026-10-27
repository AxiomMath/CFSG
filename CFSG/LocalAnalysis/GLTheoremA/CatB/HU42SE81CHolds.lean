module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE81
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE81CLin
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE81CU
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE81CD4
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SInnU6Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.CatB

private theorem unitaryFieldData_gf4 :
    CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 (GaloisField 2 2) :=
  ⟨Nat.prime_two, le_rfl, (GaloisField.card 2 2 (by norm_num)).trans (by norm_num)⟩

theorem E81C.innerOfFix_of_host (S : Type) [Group S] [Finite S] (h : catalogIs S IsU42Host) :
    E81C.InnerOfFix S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with hD | hU5 | hU6
  · obtain ⟨K₀, _, _, _, hK₀, ⟨e'⟩⟩ :=
      E81C.exists_om8_of_isD4two (⟨i, hD, ⟨e⟩⟩ : catalogIs S S9.isD4two)
    exact E81C.InnerOfFix.of_mulEquiv e'.symm (E81C.innerOfFix_om8 hK₀)
  · obtain ⟨q, hv, hq2, ⟨e0⟩⟩ := lieIndex_isU5two (⟨i, hU5, ⟨e⟩⟩ : catalogIs S S9.isU5two)
    obtain ⟨e1⟩ := nonempty_equiv_timmesfeldPSU 4 q hv hq2 e0
    exact E81C.InnerOfFix.of_mulEquiv
      (e1.trans (CFSG.GF2Type.timmesfeldPSUEquivStatedProj 5)).symm
      (E81C.innerOfFix_unitary unitaryFieldData_gf4 (by norm_num) (by norm_num))
  · obtain ⟨q, hv, hq2, ⟨e0⟩⟩ :=
      U62RankSound.lieIndex_isU6two (⟨i, hU6, ⟨e⟩⟩ : catalogIs S S9.isU6two)
    obtain ⟨e1⟩ := nonempty_equiv_timmesfeldPSU 5 q hv hq2 e0
    exact E81C.InnerOfFix.of_mulEquiv
      (e1.trans (CFSG.GF2Type.timmesfeldPSUEquivStatedProj 6)).symm
      (E81C.innerOfFix_unitary unitaryFieldData_gf4 (by norm_num) (by norm_num))

theorem u42E81CentAt_holds : U42E81CentAt := by
  intro S _ _ hS E hE hcard t ht hcomm
  haveI := isSimple_of_host S hS
  have hinj := conj_injective_of_center (center_eq_bot_of_simple E hcard)
  have hfix : ∀ e ∈ E, t e = e := by
    intro e he
    apply hinj
    have h1 : MulAut.conj (t e) = t * MulAut.conj e * t⁻¹ := by
      refine MulEquiv.ext fun x => ?_
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
        map_mul, map_inv, MulAut.apply_inv_self]
    rw [h1, ← hcomm e he, mul_inv_cancel_right]
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  obtain ⟨g, rfl⟩ := E81C.innerOfFix_of_host S hS E hE hcard t ht2 hfix
  have hg2 : g ^ 2 = 1 := hinj (by rw [map_pow, ht2, map_one])
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    omega
  have hEg : ∀ e ∈ E, e * g = g * e := by
    intro e he
    apply hinj
    rw [map_mul, map_mul]
    exact hcomm e he
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hg2 hg1, pow_one])
  have hT1 : Subgroup.zpowers g ≠ ⊥ := fun h => hg1 (Subgroup.zpowers_eq_bot.1 h)
  have hgc : g ∈ Subgroup.centralizer (E : Set S) := Subgroup.mem_centralizer_iff.2 hEg
  have hEc : E ≤ Subgroup.centralizer (Subgroup.zpowers g : Set S) :=
    Subgroup.le_centralizer_iff.2 (Subgroup.zpowers_le.2 hgc)
  have hET : E ≤ Subgroup.normalizer (Subgroup.zpowers g : Set S) :=
    hEc.trans (Subgroup.centralizer_le_normalizer _)
  have hle := rankFine_of_host u42E81InnU6At_holds S hS E _ hE hT2 hT1 hET
  rw [hcard] at hle
  norm_num at hle

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
