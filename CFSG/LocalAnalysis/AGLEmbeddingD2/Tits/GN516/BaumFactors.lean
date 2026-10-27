module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B2F CFSG.Quasithin.B6
  CFSG.Quasithin.E2 CFSG.AGLEmbeddingD2.GN

theorem iSup_le_normalizer_of_commuting {G : Type*} [Group G] {I : Finset (Subgroup G)}
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    {L : Subgroup G} (hL : L ∈ I) : (⨆ L' ∈ I, L') ≤ Subgroup.normalizer (L : Set G) := by
  refine iSup₂_le fun L' hL' => ?_
  by_cases h : L' = L
  · subst h
    exact Subgroup.le_normalizer
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hxa : ∀ y ∈ L, a * y = y * a := fun y hy => hcomm L' hL' L hL h a ha y hy
    constructor
    · intro hx
      have : a * x * a⁻¹ = x := by rw [hxa x hx]; group
      rw [this]; exact hx
    · intro hx
      have h3 : a * (a * x * a⁻¹) * a⁻¹ = a * x * a⁻¹ := by rw [hxa _ hx]; group
      have h4 : a * (a * x * a⁻¹) = a * x := mul_right_cancel h3
      have h5 : a * x * a⁻¹ = x := mul_left_cancel h4
      rwa [h5] at hx

variable {G : Type} [Group G] [Finite G]

theorem autI_baum_le_iSup_of_fam {H T V : Subgroup G} {hV : IsElemAbelian 2 V}
    {I : Finset (Subgroup (MulAut (IntMod V hV)))} (hT : IsSylowTwoOf T H)
    (hFam : E23FamGen H T V hV I)
    (hall : (∀ L ∈ I, ∃ n : ℕ, IsL2Natural L (fixV (autI hV (twoResidual H))) n) ∨
      ∃ m : ℕ, 2 ≤ m ∧ ∀ L ∈ I, IsSymCoreModule L (2 ^ m + 1)) :
    autI hV (baum T) ≤ ⨆ L ∈ I, L := by
  obtain ⟨-, hJeq, -, -, -, h6, h7⟩ := hFam
  have hBJ : autI hV (baum T) = autI hV (thompsonJ T) := by
    rcases hall with h | ⟨m, hm, h⟩
    · exact (h6 h).1
    · exact (h7 m hm h).1
  rw [hBJ]
  exact (autI_mono hV (B6.thompsonJ_le_of_sylow hT)).trans hJeq.le

theorem convI_baum_mem_normalizer_of_fam {H T V : Subgroup G} {hV : IsElemAbelian 2 V}
    {I : Finset (Subgroup (MulAut (IntMod V hV)))} (hT : IsSylowTwoOf T H)
    (hFam : E23FamGen H T V hV I)
    (hall : (∀ L ∈ I, ∃ n : ℕ, IsL2Natural L (fixV (autI hV (twoResidual H))) n) ∨
      ∃ m : ℕ, 2 ≤ m ∧ ∀ L ∈ I, IsSymCoreModule L (2 ^ m + 1))
    {b : G} (hb : b ∈ baum T) (hbN : b ∈ Subgroup.normalizer (V : Set G))
    {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    convI hV ⟨b, hbN⟩ ∈ Subgroup.normalizer (L : Set (MulAut (IntMod V hV))) :=
  iSup_le_normalizer_of_commuting hFam.2.2.1 hL
    (autI_baum_le_iSup_of_fam hT hFam hall (convI_mem_autI hV hb hbN))

end CFSG.AGLEmbeddingD2.Tits.GN516
