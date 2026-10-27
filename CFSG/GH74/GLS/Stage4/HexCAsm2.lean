module

public import CFSG.GH74.GLS.Stage4.HexCAsm1

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F : Type} [Field F]

theorem g2Coords_of_data [IsSimpleGroup G] (R : RGD2 6 H r₁ r₂ U root)
    (hgen : (H ⊔ U) ⊔ R.N = ⊤) (D : HexData root F) {e : F} (he : e ≠ 0) (h3 : (3 : F) ≠ 0)
    {Λ : F → G} (hΛmem : ∀ v, Λ v ∈ root 3) (hΛinj : ∀ v w, Λ v = Λ w → v = w)
    (hΛsurj : ∀ u ∈ root 3, ∃ v, Λ v = u)
    (hrel : G2Rel (fun g : Σ _ : Fin 6, F => g2ψ D e Λ g.1 g.2)) :
    G2Coords (R.toPre hgen).toSystemOfSimple (g2ψ D e Λ) where
  rel := hrel
  mem i c := by
    fin_cases i
    · exact D.p1_mem c
    · exact D.p2_mem _
    · exact hΛmem _
    · exact D.p4_mem _
    · exact D.p5_mem c
    · exact D.p6_mem c
  inj i := by
    have hn : -e ≠ 0 := neg_ne_zero.2 he
    have hn3 : -(3 * e) ≠ 0 := neg_ne_zero.2 (mul_ne_zero h3 he)
    fin_cases i
    · exact D.p1_inj
    · intro a b hab
      exact mul_left_cancel₀ hn (D.p2_inj hab)
    · intro a b hab
      exact mul_left_cancel₀ hn3 (hΛinj _ _ hab)
    · intro a b hab
      exact mul_left_cancel₀ hn (D.p4_inj hab)
    · exact D.p5_inj
    · exact D.p6_inj
  surj i y hy := by
    have hn : -e ≠ 0 := neg_ne_zero.2 he
    have hn3 : -(3 * e) ≠ 0 := neg_ne_zero.2 (mul_ne_zero h3 he)
    fin_cases i
    · exact D.p1_surj y hy
    · obtain ⟨d, hd⟩ := D.p2_surj y hy
      refine ⟨d / -e, ?_⟩
      show D.p2 (-e * (d / -e)) = y
      rw [show -e * (d / -e) = d by field_simp]; exact hd
    · obtain ⟨v, hv⟩ := hΛsurj y hy
      refine ⟨v / -(3 * e), ?_⟩
      show Λ (-(3 * e) * (v / -(3 * e))) = y
      rw [show -(3 * e) * (v / -(3 * e)) = v by field_simp]; exact hv
    · obtain ⟨d, hd⟩ := D.p4_surj y hy
      refine ⟨d / -e, ?_⟩
      show D.p4 (-e * (d / -e)) = y
      rw [show -e * (d / -e) = d by field_simp]; exact hd
    · exact D.p5_surj y hy
    · exact D.p6_surj y hy

end CFSG.GH74.GLS.Stage4.Hex
