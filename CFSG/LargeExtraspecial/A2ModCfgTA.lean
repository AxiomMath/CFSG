module

public import CFSG.LargeExtraspecial.A2ModCfgARS
public import CFSG.Timmesfeld.ARS.ConfigA2
public import CFSG.Timmesfeld.ARS.Induction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module Matrix CFSG.RankThree.OrthogonalInvolutions CFSG.Timmesfeld.ARS CFSG.LieType
  CFSG.LieType.Universal
open CFSG.Timmesfeld (sroot)

variable {X : Type} [Group X] {R : Set (Subgroup X)} {D : Set X}

theorem typeA_exists_surjective [Finite X] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d) (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    {m : ℕ} (hm : 2 ≤ m) (hX : HasGenConfig R (CFSG.Timmesfeld.ARS.edgeA m)) :
    ∃ Ψ : SpecialLinearGroup (Fin (m + 1)) (ZMod 2) →* X, Function.Surjective Ψ ∧
      ∀ g ∈ transvectionSet (m + 1) (ZMod 2), Ψ g ∈ D := by
  obtain ⟨A, B, hX, hgen⟩ := hX
  have key : ∃ f : ℕ, (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
      ∃ Ψ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X,
        (∀ k : Fin m,
          ((SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup (sroot k)).map Ψ = A k) ∧
        Function.Surjective Ψ := by
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · obtain ⟨f, -, hcard, Ψ, hΨA, -, hs⟩ := hX.exists_surjective_A_two hR hiso hgen
      exact ⟨f, hcard, Ψ, hΨA, hs⟩
    · obtain ⟨f, -, hcard, Ψ, hΨA, -, hs, -⟩ := hX.exists_surjective_A hR hiso hm3 hgen
      exact ⟨f, hcard, Ψ, hΨA, hs⟩
  obtain ⟨f, hcard, Ψ, hΨA, hs⟩ := key
  obtain rfl : f = 1 := by
    have h2 := hcard _ (hX.memA ⟨0, by omega⟩)
    rw [card_eq_two_of_forall_eq_zpowers hR hRD _ (hX.memA _)] at h2
    exact Nat.pow_right_injective le_rfl (h2.symm.trans (pow_one 2).symm)
  refine ⟨Ψ.comp (slEquiv galoisFieldTwoOneEquiv).symm.toMonoidHom,
    hs.comp (slEquiv galoisFieldTwoOneEquiv).symm.surjective, ?_⟩
  obtain ⟨d, hd, hAd⟩ := hRD _ (hX.memA ⟨0, by omega⟩)
  have h0 : ((SpecialLinear.rootDatum m (ZMod 2)).rootGroup (sroot (⟨0, by omega⟩ : Fin m))).map
      (Ψ.comp (slEquiv galoisFieldTwoOneEquiv).symm.toMonoidHom) = Subgroup.zpowers d :=
    (map_comp_slEquiv_symm_rootGroup galoisFieldTwoOneEquiv Ψ _).trans
      ((hΨA (⟨0, by omega⟩ : Fin m)).trans hAd)
  have h01 : (⟨0, by omega⟩ : Fin m).castSucc ≠ (⟨0, by omega⟩ : Fin m).succ :=
    Fin.castSucc_lt_succ.ne
  refine map_mem_of_elemTv_mem hDc _ h01 ?_
  rw [map_elemTv_castSucc_succ _ _ (mul_self_and_ne_one_of_mem hR (hX.memA _) hAd).2 h0]
  exact hd

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem typeA_finrank_commSpaceOf_le [Finite X] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d) (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) {m : ℕ} (hm : 2 ≤ m) (hX : HasGenConfig R (CFSG.Timmesfeld.ARS.edgeA m)) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 2 * max (m + 1) 3 := by
  obtain ⟨Ψ, hs, hΨ⟩ := typeA_exists_surjective hR hiso hRD hDc hm hX
  obtain ⟨-, hA'⟩ := hA.comp_sl (by omega) hΨ
  rw [← MonoidHom.range_eq_top.mpr hs, commSpaceOf_range]
  exact finrank_commSpaceOf_top_le hA'

theorem typeA_false_of_irreducible [Finite X] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d) (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) {m : ℕ} (hm : 4 ≤ m) (hX : HasGenConfig R (CFSG.Timmesfeld.ARS.edgeA m))
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤) : False := by
  obtain ⟨Ψ, hs, hΨ⟩ := typeA_exists_surjective hR hiso hRD hDc (by omega) hX
  obtain ⟨-, hA'⟩ := hA.comp_sl (by omega) hΨ
  refine false_of_irreducible hA' (by omega) fun W hW => hirr W fun x w hw => ?_
  obtain ⟨g, rfl⟩ := hs x
  exact hW g w hw

theorem typeA_finrank_lt [Finite X] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d) (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) {m : ℕ} (hm : 2 ≤ m) (hX : HasGenConfig R (CFSG.Timmesfeld.ARS.edgeA m))
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤) :
    finrank (ZMod 2) V < 10 := by
  by_cases hm4 : 4 ≤ m
  · exact (typeA_false_of_irreducible hR hiso hRD hDc hA hm4 hX hirr).elim
  have h := typeA_finrank_commSpaceOf_le hR hiso hRD hDc hA hm hX
  obtain ⟨A, B, hX', -⟩ := hX
  obtain ⟨d, hd, -⟩ := hRD _ (hX'.memA ⟨0, by omega⟩)
  rw [hA.commSpaceOf_top_eq_top hd hirr, finrank_top] at h
  have : max (m + 1) 3 ≤ 4 := max_le (by omega) (by omega)
  omega

end CFSG.LargeExtraspecial.A2Mod
