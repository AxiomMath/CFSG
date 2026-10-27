module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Coprime
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviNode

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed
  CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg.Minuscule CFSG.AGLEmbedding.ParabHub
  CFSG.LieType.Steinberg.Minuscule.MinData.Valid

theorem rankOne_eq_range_of_le_range {K F : Type} [Group K] [Field F] {D : UniversalRootDatum K}
    {i : Fin D.rank} (φ : Matrix.SpecialLinearGroup (Fin 2) F →* K)
    (hu : ∀ c, φ (sl2Upper c) ∈ D.rootGroup (Pi.single i 1))
    (hl : ∀ c, φ (sl2Lower c) ∈ D.rootGroup (-Pi.single i 1))
    (hle : rankOne D.rootGroup i ≤ φ.range) : rankOne D.rootGroup i = φ.range := by
  refine le_antisymm hle (fun x hx => ?_)
  obtain ⟨s, rfl⟩ := hx
  have hsub : (Set.range (sl2Upper (k := F)) ∪ Set.range (sl2Lower (k := F))) ⊆
      ((rankOne D.rootGroup i).comap φ : Set _) := by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact Subgroup.mem_sup_left (hu c)
    · exact Subgroup.mem_sup_right (hl c)
  exact (Subgroup.closure_le _).2 hsub (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 s)

variable {k : Type} [Field k] [Finite k] [CharP k 2] {θ : k →+* k}

set_option linter.unusedSectionVars false


theorem nodeLevi_e6tw_fixed {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    {i : Fin (Tag.rank .F4)} (hi : orbitMap a = i) : NodeLevi (twistedDatum k θ) i := by
  subst hi
  have h1 : rho (Pi.single a 1) = Pi.single a 1 := by rw [rho_single, ha]
  have h2 : rho (-Pi.single a 1) = -Pi.single a 1 := by rw [rho_neg_single, ha]
  have hu : ∀ c, slFixedNodeHom θ ha (sl2Upper c) ∈
      twistedRootGroup k θ (Pi.single (orbitMap a) 1) := fun c => by
    rw [← proj_single]
    exact (mem_twistedRootGroup_iff_of_fixed θ (isRoot_single _ a) rfl h1 _).2
      ⟨c, c.2, slFixedNodeE_upper θ a c⟩
  have hl : ∀ c, slFixedNodeHom θ ha (sl2Lower c) ∈
      twistedRootGroup k θ (-Pi.single (orbitMap a) 1) := fun c => by
    rw [← proj_neg_single]
    exact (mem_twistedRootGroup_iff_of_fixed θ (isRoot_neg_single _ a) rfl h2 _).2
      ⟨c, c.2, slFixedNodeE_lower θ a c⟩
  exact nodeLevi_of_range_sl2 (slFixedNodeHom_injective θ ha)
    (rankOne_eq_range_of_le_range _ hu hl (rankOne_le_range_slFixedNodeHom θ ha rfl))

theorem nodeLevi_e6tw_orbit (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {i : Fin (Tag.rank .F4)}
    (hi : orbitMap a = i) : NodeLevi (twistedDatum k θ) i := by
  subst hi
  have hρ := rhoPerm_of_orbit hab
  have hne1 : rho (Pi.single a 1) ≠ Pi.single a 1 := by
    rw [rho_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hne2 : rho (-Pi.single a 1) ≠ -Pi.single a 1 := by
    rw [rho_neg_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hu : ∀ c, slOrbitHom θ hθ hab (sl2Upper c) ∈
      twistedRootGroup k θ (Pi.single (orbitMap a) 1) := fun c => by
    rw [← proj_single]
    refine (mem_twistedRootGroup_iff_of_pair θ (isRoot_single _ a) rfl hne1 _).2 ⟨c, ?_⟩
    rw [show (sl2Upper c : Matrix.SpecialLinearGroup (Fin 2) k) = slUpper k c from rfl,
      slOrbitHom_upper, rho_single, hρ, twistSign_single, Int.cast_one, one_mul]
  have hl : ∀ c, slOrbitHom θ hθ hab (sl2Lower c) ∈
      twistedRootGroup k θ (-Pi.single (orbitMap a) 1) := fun c => by
    rw [← proj_neg_single]
    refine (mem_twistedRootGroup_iff_of_pair θ (isRoot_neg_single _ a) rfl hne2 _).2 ⟨c, ?_⟩
    rw [show (sl2Lower c : Matrix.SpecialLinearGroup (Fin 2) k) = slLower k c from rfl,
      slOrbitHom_slLower, rho_neg_single, hρ, twistSign_neg_single, Int.cast_one, one_mul]
  exact nodeLevi_of_range_sl2 (slOrbitHom_injective θ hθ hab)
    (rankOne_eq_range_of_le_range _ hu hl (rankOne_le_range_slOrbitHom θ hθ hab rfl))

theorem nodeLevi_e6tw (hθ : ∀ c, θ (θ c) = c) (i : Fin (Tag.rank .F4)) :
    NodeLevi (twistedDatum k θ) i := by
  fin_cases i
  · exact nodeLevi_e6tw_fixed (a := nd 1) rfl rfl
  · exact nodeLevi_e6tw_fixed (a := nd 3) rfl rfl
  · exact nodeLevi_e6tw_orbit hθ (a := nd 2) (b := nd 4) (Or.inl ⟨rfl, rfl⟩) rfl
  · exact nodeLevi_e6tw_orbit hθ (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩) rfl

end CFSG.AGLEmbeddingD2.Tits.GN516
