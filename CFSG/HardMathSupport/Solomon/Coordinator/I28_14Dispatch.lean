module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14Assembly
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14Map
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassC
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassNOrth
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymMain
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymAut
public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypes
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLaughlin
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassCGL
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassCOrth
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassCSp

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open Module Submodule
  CFSG.LocalAnalysis.ComponentInitial

section Dispatch
variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

theorem tvIrred_cases {G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)} (hG : IsTvIrred G) :
    G = ⊤ ∨
    (∃ f : LinearMap.BilinForm (ZMod 2) U, f.Nondegenerate ∧ f.IsAlt ∧
      G = bilinIsometryGroup f) ∨
    (∃ Q : QuadraticForm (ZMod 2) U, (QuadraticMap.polarBilin Q).Nondegenerate ∧
      G = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).toMonoidHom) ∨
    (∃ β : U ≃ₗ[ZMod 2] sumZero (finrank (ZMod 2) U + 1), Odd (finrank (ZMod 2) U + 1) ∧
      5 ≤ finrank (ZMod 2) U + 1 ∧
      G.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
        (sumZeroRep (finrank (ZMod 2) U + 1)).range) ∨
    (∃ β : U ≃ₗ[ZMod 2] sumZero (finrank (ZMod 2) U + 2) ⧸ onesLine (finrank (ZMod 2) U + 2),
      Even (finrank (ZMod 2) U + 2) ∧ 5 ≤ finrank (ZMod 2) U + 2 ∧
      G.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
        (heartRep (finrank (ZMod 2) U + 2)).range) := by
  obtain ⟨⟨S, ⟨t₀, ht₀S⟩, hS, hGS⟩, hirr⟩ := hG
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  have ht₀ := hS t₀ ht₀S
  have ht₀G : t₀ ∈ G := hGS ▸ Subgroup.subset_closure ht₀S
  have h2 := mclt_two_le_finrank ht₀
  by_cases hd2 : finrank (ZMod 2) U = 2
  · exact Or.inl (mclt_eq_top_of_finrank_two hd2 ht₀G ht₀ hirr)
  rcases mclaughlin_transvection_groups_F2 (by omega) G ⟨S, hS, hGS⟩ hirr with
    hG | ⟨-, f, hnd, halt, hG⟩ | ⟨-, Q, hQ, hG⟩ | ⟨hev, ⟨β, hβ⟩ | ⟨β, hβ⟩⟩
  · exact Or.inl hG
  · exact Or.inr (Or.inl ⟨f, hnd, halt, hG⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨Q, hQ, hG⟩))
  · obtain ⟨k, hk⟩ := hev
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨β, ⟨k, by omega⟩, by omega, hβ⟩)))
  · obtain ⟨k, hk⟩ := hev
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨β, ⟨k + 1, by omega⟩, by omega, hβ⟩)))

theorem tvIrred_normalizer_le {G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)}
    (hG : IsTvIrred G) {g : LinearMap.GeneralLinearGroup (ZMod 2) U}
    (hg : ∀ x ∈ G, g * x * g⁻¹ ∈ G) : g ∈ G := by
  rcases tvIrred_cases hG with h | ⟨f, hnd, halt, rfl⟩ | ⟨Q, hQ, rfl⟩ | ⟨β, hodd, h5, hβ⟩ |
    ⟨β, hev, h5, hβ⟩
  · rw [h]; trivial
  · exact tvN_sp hnd halt hG hg
  · exact tvN_orth hQ hG hg
  · set Φ := LinearMap.GeneralLinearGroup.congrLinearEquiv β
    have hgΦ : Φ g ∈ G.map Φ.toMonoidHom := by
      rw [hβ]
      refine tvN_symOdd h5 hodd (fun α hα => perm_aut_preserving_swaps_inner h5 α hα) ?_
      intro x hx
      rw [← hβ] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := hg y hy
      rw [← hβ]
      exact ⟨_, this, by simp [map_mul, map_inv]⟩
    obtain ⟨y, hy, hyg⟩ := hgΦ
    have : y = g := Φ.injective hyg
    exact this ▸ hy
  · set Φ := LinearMap.GeneralLinearGroup.congrLinearEquiv β
    have hgΦ : Φ g ∈ G.map Φ.toMonoidHom := by
      rw [hβ]
      refine tvN_symEven h5 hev (fun α hα => perm_aut_preserving_swaps_inner h5 α hα) ?_
      intro x hx
      rw [← hβ] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := hg y hy
      rw [← hβ]
      exact ⟨_, this, by simp [map_mul, map_inv]⟩
    obtain ⟨y, hy, hyg⟩ := hgΦ
    have : y = g := Φ.injective hyg
    exact this ▸ hy

theorem tvIrred_hasCentralizedConj {G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)}
    (hG : IsTvIrred G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)} (hA : IsMaxElemAbelianIn p G A)
    {t : LinearMap.GeneralLinearGroup (ZMod 2) U} (htG : t ∈ G) (ht : IsF2Transvection t) :
    HasCentralizedConj p G A t := by
  rcases tvIrred_cases hG with h | ⟨f, hnd, halt, rfl⟩ | ⟨Q, hQ, rfl⟩ | ⟨β, hodd, h5, hβ⟩ |
    ⟨β, hev, h5, hβ⟩
  · subst h
    exact tvC_top hp hp2 hA.2.1 ht
  · exact tvC_sp hp hp2 hnd halt hA.2.1 hA.1 htG ht
  · exact tvC_orth hp hp2 hQ hG hA.2.1 hA.1 htG ht
  · set Φ := LinearMap.GeneralLinearGroup.congrLinearEquiv β
    refine hasCentralizedConj_of_map Φ ?_
    have hA' := isMaxElemAbelianIn_map Φ hA
    rw [hβ] at hA' ⊢
    exact tvC_symOdd h5 hodd hp hp2 hA'
      (by rw [← hβ]; exact ⟨t, htG, rfl⟩) ((isF2Transvection_congr β t).2 ht)
  · set Φ := LinearMap.GeneralLinearGroup.congrLinearEquiv β
    refine hasCentralizedConj_of_map Φ ?_
    have hA' := isMaxElemAbelianIn_map Φ hA
    rw [hβ] at hA' ⊢
    exact tvC_symEven h5 hev hp hp2 hA'
      (by rw [← hβ]; exact ⟨t, htG, rfl⟩) ((isF2Transvection_congr β t).2 ht)

end Dispatch

theorem tvNormalizer_holds : TvNormalizer :=
  fun _ _ _ _ _ hG _ hg => tvIrred_normalizer_le hG hg

theorem tvCentralized_holds : TvCentralized :=
  fun _ _ _ _ _ hG _ hp hp2 _ hA _ htG ht => tvIrred_hasCentralizedConj hG hp hp2 hA htG ht

end CFSG.HardMathSupport.Solomon.Coordinator
