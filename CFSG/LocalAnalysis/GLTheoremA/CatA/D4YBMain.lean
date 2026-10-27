module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YBCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4YB

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
  CFSG.LocalAnalysis.GLTheoremA.D4T CFSG.StandardType.Triality
  CFSG.ComponentClassification.OuterAutomorphisms

theorem d4TwoAutNormInn_holds : D4XF.D4TwoAutNormInn := by
  intro K _ _ h P S hP hPn hcard hS2 hS1 hPS hSi
  classical
  obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := D4XF.statedModel_of_d4two h
  have hK₀' : Nat.card K₀ = 2 := by rw [hK₀]; norm_num
  haveI : Finite K₀ := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype K₀ := Fintype.ofFinite K₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K₀ 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK₀']; norm_num)
  have hunits : Nat.card K₀ˣ = 1 := by rw [Nat.card_units, hK₀']
  have hu : Subsingleton K₀ˣ := (Nat.card_eq_one_iff_unique.1 hunits).1
  obtain ⟨Φ⟩ := D4XF.equiv_triality_of_statedProj hu e
  have hOutK : Nat.card (MulAut K ⧸ inner K) ≤ 6 :=
    CFSG.EvenSmallLie.OmegaEight.card_outer_le_six (D4XF.statedModel_of_d4two h)
  have hOut : Nat.card (MulAut (Om8 K₀) ⧸ inner (Om8 K₀)) ≤ 6 := by
    rw [← Nat.card_congr (equivalence Φ).toEquiv]
    exact hOutK
  set Ψ : MulAut K ≃* MulAut (Om8 K₀) := MulAut.congr Φ with hΨ
  refine main_om8 hK₀' hOut (P := P.map Ψ.toMonoidHom) (S := S.map Ψ.toMonoidHom)
    (S9.l94t_isElemAbelian_map _ hP) ?_ ?_ (hS2.map _) ?_ ?_ ?_
  · intro hle
    apply hPn
    intro x hx
    have h1 : Ψ x ∈ inner (Om8 K₀) := hle (Subgroup.mem_map_of_mem _ hx)
    rw [← inner_map_congr Φ] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = x := Ψ.injective hyx
    exact this ▸ hy
  · rw [Subgroup.card_map_of_injective Ψ.injective]
    exact hcard
  · intro hbot
    apply hS1
    exact (Subgroup.map_eq_bot_iff_of_injective S Ψ.injective).1 hbot
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Subgroup.le_normalizer_map Ψ.toMonoidHom (Subgroup.mem_map_of_mem _ (hPS hy))
  · rw [← inner_map_congr Φ]
    exact Subgroup.map_mono hSi

end CFSG.LocalAnalysis.GLTheoremA.D4YB
