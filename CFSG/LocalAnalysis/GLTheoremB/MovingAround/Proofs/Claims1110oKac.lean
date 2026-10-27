module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE8

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110o

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix


theorem not_d4Shape_of_five {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E8 L p₀) (h5 : ((5 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTp : rootDiagUnit Tag.E8 a ^ 5 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 4 ∧
       (componentRoots (rootCharHom a) i).ncard = 24) := by
  rintro ⟨hrank, hncard⟩
  obtain ⟨v, μ, hμ, hall⟩ :=
    S.exists_kacT_of_prime (K := kacE8) Nat.prime_five h5 facts_E8 hTp
  obtain ⟨x, -, hi⟩ := hall i
  let C : Finset (Option (Fin Tag.E8.rank)) :=
    (Set.toFinite (KacData.comp kacE8 5 μ x)).toFinset
  have hCcoe : KacData.comp kacE8 5 μ x = (C : Set (Option (Fin Tag.E8.rank))) :=
    (Set.toFinite _).coe_toFinset.symm
  have hCp : ∃ z, z ∉ C := by
    obtain ⟨z, hz⟩ := exists_not_mem_comp kacE8 (by norm_num : 0 < 5) μ x
    exact ⟨z, fun h => hz ((Set.toFinite _).mem_toFinset.1 h)⟩
  rw [hCcoe] at hi
  have hrankC : compRank (componentRoots (rootCharHom a) i) = C.card := by
    rw [hi, compRank_image, compRank_rootsOf kacE8 facts_E8 hCp]
  have hncardC : (componentRoots (rootCharHom a) i).ncard =
      kacCount .E8 kacE8.θ C := by
    rw [hi, ncard_image_smul, ncard_rootsOf kacE8 facts_E8 hCp]
  rw [hrankC] at hrank
  rw [hncardC] at hncard
  have hCeq : C = {some 1, some 2, some 3, some 4} := kacCount_E8_four C hrank hncard
  have h2c : (some 2 : Option (Fin Tag.E8.rank)) ∈ KacData.comp kacE8 5 μ x := by
    rw [hCcoe, hCeq]
    simp
  have h4c : (some 4 : Option (Fin Tag.E8.rank)) ∈ KacData.comp kacE8 5 μ x := by
    rw [hCcoe, hCeq]
    simp
  have h0z : ¬ KacData.IsZ kacE8 5 μ (some 0) := by
    intro hz
    have hadj : KacData.Adj kacE8 (some 2) (some 0) := by
      rw [e8_adj]
      decide
    have hm : (some 0 : Option (Fin Tag.E8.rank)) ∈ KacData.comp kacE8 5 μ x :=
      ⟨hz, h2c.2.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨h2c.1, hz, hadj⟩)⟩
    rw [hCcoe, hCeq] at hm
    exact absurd hm (by decide)
  have h5z : ¬ KacData.IsZ kacE8 5 μ (some 5) := by
    intro hz
    have hadj : KacData.Adj kacE8 (some 4) (some 5) := by
      rw [e8_adj]
      decide
    have hm : (some 5 : Option (Fin Tag.E8.rank)) ∈ KacData.comp kacE8 5 μ x :=
      ⟨hz, h4c.2.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨h4c.1, hz, hadj⟩)⟩
    rw [hCcoe, hCeq] at hm
    exact absurd hm (by decide)
  change ¬ μ 0 = 0 at h0z
  change ¬ μ 5 = 0 at h5z
  have hm0 : 1 ≤ μ 0 := by
    have := hμ.1 0
    omega
  have hm5 : 1 ≤ μ 5 := by
    have := hμ.1 5
    omega
  have hθ : kacE8.θ ⬝ᵥ μ =
      2 * μ 0 + 3 * μ 1 + 4 * μ 2 + 6 * μ 3 + 5 * μ 4 + 4 * μ 5 + 3 * μ 6 +
        2 * μ 7 := by
    rw [show kacE8.θ = ![2, 3, 4, 6, 5, 4, 3, 2] from rfl]
    show ∑ j : Fin 8, (![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ) j * μ j = _
    rw [Fin.sum_univ_eight]
    rfl
  have hμ2 : kacE8.θ ⬝ᵥ μ ≤ (5 : ℤ) := hμ.2
  rw [hθ] at hμ2
  have h1 := hμ.1 1
  have h2 := hμ.1 2
  have h3 := hμ.1 3
  have h4 := hμ.1 4
  have h6 := hμ.1 6
  have h7 := hμ.1 7
  omega

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110o
