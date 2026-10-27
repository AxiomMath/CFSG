module

public import CFSG.ClassicalInvolution.Q3.TL4SepTwoD
public import CFSG.ClassicalInvolution.Q3.TL4SepMain

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def Thm4Res2C3 (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L : Subgroup G,
    T4Min 3 G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L →
    omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ →
    ∀ u v : G, IsUniqueInvolution J u → IsUniqueInvolution L v → TightInO2 u → TightInO2 v →
      v ∉ Subgroup.normalizer (J : Set G) → False

variable {G : Type} [Group G]

theorem tightInO2_of_conj {u : G} (g : G) (h : TightInO2 (g * u * g⁻¹)) :
    TightInO2 u := by
  obtain ⟨P, hPn, hP2, hP⟩ := h
  refine ⟨P, hPn, hP2, ?_⟩
  have := hPn.conj_mem _ hP g⁻¹
  rwa [show g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u by group] at this

theorem thm4Res2C_of_res2C3 {r n : ℕ} (h3 : r = 3 → Thm4Res2C3 n) : Thm4Res2C r n := by
  intro G _ _ hG J L hm hgen
  obtain ⟨u, hu⟩ := (hm.hyp.hyp.omega1 J hm.memJ).1
  obtain ⟨v, hv⟩ := (hm.hyp.hyp.omega1 L hm.memL).1
  have hnu : ¬ TightInO2 u ∧ ¬ TightInO2 v := by
    by_cases hinu : TightInO2 u <;> by_cases hinv : TightInO2 v
    · exfalso
      by_cases hvJ : v ∈ Subgroup.normalizer (J : Set G)
      · exact hm.false_of_mem_normalizer hu hv hinu hinv hvJ
      · have hr3 : r = 3 := le_antisymm
          (hm.hyp.le_three_of_not_mem_normalizer hm.memJ hm.memL hu hv hinu hinv hvJ)
          (hm.hyp.three_le hm.memJ)
        subst hr3
        exact h3 rfl G hG J L hm hgen u v hu hv hinu hinv hvJ
    · exact absurd (hm.false_of_mixed hu hv hinu hinv) id
    · exact absurd (hm.symm.false_of_mixed hv hu hinv hinu) id
    · exact ⟨hinu, hinv⟩
  rintro K (⟨g, rfl⟩ | ⟨g, rfl⟩) z hz hzO
  · exact hnu.1 (tightInO2_of_conj g (hz.eq (hu.conj g) ▸ hzO))
  · exact hnu.2 (tightInO2_of_conj g (hz.eq (hv.conj g) ▸ hzO))

theorem thm4RBelow_of_res2C3 {r n : ℕ} (h3 : r = 3 → Thm4Res2C3 n) (h2f : Thm4Res2F r n) :
    Thm4RBelow r n :=
  thm4RBelow_of_residuals (thm4Res2C_of_res2C3 h3) h2f

end CFSG.ClassicalInvolution.Q3.TL4
