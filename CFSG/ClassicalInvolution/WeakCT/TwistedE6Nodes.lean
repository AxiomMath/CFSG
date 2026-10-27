module

public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic

public noncomputable section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.LieType.Universal CFSG.LieType.CurtisTits MinData.Valid
open CFSG.ClassicalInvolution.Models.TwistedPairs (fixedField liftSL liftSL_injective map_liftSL)
open scoped MatrixGroups

variable {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

@[expose] def rFixed (a : Fin (Tag.rank .E6)) (ha : rhoPerm a = a) :
    SL(2, fixedField θ) →* fixedGroup k θ :=
  ((e6Rank1 k a).comp (liftSL θ 2)).codRestrict (fixedGroup k θ) fun A => by
    rw [mem_fixedGroup, MonoidHom.comp_apply, sigma_e6Rank1, ha, map_liftSL]

theorem rFixed_tv01 (a : Fin (Tag.rank .E6)) (ha : rhoPerm a = a) (c : fixedField θ) :
    (rFixed θ a ha (tv 0 1 c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (Pi.single a 1) c := by
  change e6Rank1 k a (liftSL θ 2 (tv 0 1 c)) = _
  rw [liftSL_tv01, e6Rank1_tv01]

theorem rFixed_tv10 (a : Fin (Tag.rank .E6)) (ha : rhoPerm a = a) (c : fixedField θ) :
    (rFixed θ a ha (tv 1 0 c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (-Pi.single a 1) c := by
  change e6Rank1 k a (liftSL θ 2 (tv 1 0 c)) = _
  rw [liftSL_tv10, e6Rank1_tv10]

theorem rFixed_injective (a : Fin (Tag.rank .E6)) (ha : rhoPerm a = a) :
    Function.Injective (rFixed θ a ha) := by
  intro A B h
  have h1 : e6Rank1 k a (liftSL θ 2 A) = e6Rank1 k a (liftSL θ 2 B) :=
    congrArg (fun g : fixedGroup k θ => (g : e6Data_valid.minGroup k)) h
  exact liftSL_injective θ 2 (e6Rank1_injective a h1)

theorem rFixed_upper (a : Fin (Tag.rank .E6)) (ha : rhoPerm a = a) {i : Fin (Tag.rank .F4)}
    (hai : orbitMap a = i) (c : fixedField θ) :
    rFixed θ a ha (tv 0 1 c) ∈ twistedRootGroup k θ (Pi.single i 1) := by
  subst hai
  have h1 : rho (Pi.single a 1) = Pi.single a 1 := by rw [rho_single, ha]
  rw [← proj_single]
  refine (mem_twistedRootGroup_iff_of_fixed θ (isRoot_single _ a) rfl h1 _).2
    ⟨c, c.2, rFixed_tv01 θ a ha c⟩

theorem rFixed_lower (a : Fin (Tag.rank .E6)) (ha : rhoPerm a = a) {i : Fin (Tag.rank .F4)}
    (hai : orbitMap a = i) (c : fixedField θ) :
    rFixed θ a ha (tv 1 0 c) ∈ twistedRootGroup k θ (-Pi.single i 1) := by
  subst hai
  have h1 : rho (-Pi.single a 1) = -Pi.single a 1 := by rw [rho_neg_single, ha]
  rw [← proj_neg_single]
  refine (mem_twistedRootGroup_iff_of_fixed θ (isRoot_neg_single _ a) rfl h1 _).2
    ⟨c, c.2, rFixed_tv10 θ a ha c⟩

theorem rFixed_param_upper (a : Fin (Tag.rank .E6)) (ha : rhoPerm a = a)
    {i : Fin (Tag.rank .F4)} (hai : orbitMap a = i) :
    ∀ g ∈ twistedRootGroup k θ (Pi.single i 1), ∃ c : fixedField θ,
      rFixed θ a ha (tv 0 1 c) = g := by
  subst hai
  intro g hg
  have h1 : rho (Pi.single a 1) = Pi.single a 1 := by rw [rho_single, ha]
  rw [← proj_single] at hg
  obtain ⟨c, hc, hgc⟩ := (mem_twistedRootGroup_iff_of_fixed θ (isRoot_single _ a) rfl h1 g).1 hg
  exact ⟨⟨c, hc⟩, Subtype.ext ((rFixed_tv01 θ a ha ⟨c, hc⟩).trans hgc.symm)⟩

theorem rFixed_param_lower (a : Fin (Tag.rank .E6)) (ha : rhoPerm a = a)
    {i : Fin (Tag.rank .F4)} (hai : orbitMap a = i) :
    ∀ g ∈ twistedRootGroup k θ (-Pi.single i 1), ∃ c : fixedField θ,
      rFixed θ a ha (tv 1 0 c) = g := by
  subst hai
  intro g hg
  have h1 : rho (-Pi.single a 1) = -Pi.single a 1 := by rw [rho_neg_single, ha]
  rw [← proj_neg_single] at hg
  obtain ⟨c, hc, hgc⟩ :=
    (mem_twistedRootGroup_iff_of_fixed θ (isRoot_neg_single _ a) rfl h1 g).1 hg
  exact ⟨⟨c, hc⟩, Subtype.ext ((rFixed_tv10 θ a ha ⟨c, hc⟩).trans hgc.symm)⟩

theorem slOrbitHom_lower {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) (c : k) :
    (slOrbitHom θ hθ hab (slLower k c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (-Pi.single a 1) c * e6Data_valid.xm k (-Pi.single b 1) (θ c) := by
  change phiOrbit θ hab (slRankOne k a (slLower k c)) = _
  rw [phiOrbit_apply, slRankOne_lower, sigma_xm_neg_single, rhoPerm_of_orbit hab]

theorem slOrbitHom_tv01 {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) (c : k) :
    (slOrbitHom θ hθ hab (tv 0 1 c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (Pi.single a 1) c * e6Data_valid.xm k (Pi.single b 1) (θ c) := by
  rw [tv01_eq_sl2Upper]
  exact slOrbitHom_upper θ hθ hab c

theorem slOrbitHom_tv10 {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) (c : k) :
    (slOrbitHom θ hθ hab (tv 1 0 c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (-Pi.single a 1) c * e6Data_valid.xm k (-Pi.single b 1) (θ c) := by
  rw [tv10_eq_sl2Lower]
  exact slOrbitHom_lower θ hθ hab c

theorem slOrbitHom_upper_mem {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {i : Fin (Tag.rank .F4)}
    (hai : orbitMap a = i) (c : k) :
    slOrbitHom θ hθ hab (tv 0 1 c) ∈ twistedRootGroup k θ (Pi.single i 1) := by
  subst hai
  have hρ := rhoPerm_of_orbit hab
  have hne1 : rho (Pi.single a 1) ≠ Pi.single a 1 := by
    rw [rho_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  rw [← proj_single]
  refine (mem_twistedRootGroup_iff_of_pair θ (isRoot_single _ a) rfl hne1 _).2 ⟨c, ?_⟩
  rw [slOrbitHom_tv01, rho_single, hρ, twistSign_single, Int.cast_one, one_mul]

theorem slOrbitHom_lower_mem {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {i : Fin (Tag.rank .F4)}
    (hai : orbitMap a = i) (c : k) :
    slOrbitHom θ hθ hab (tv 1 0 c) ∈ twistedRootGroup k θ (-Pi.single i 1) := by
  subst hai
  have hρ := rhoPerm_of_orbit hab
  have hne1 : rho (-Pi.single a 1) ≠ -Pi.single a 1 := by
    rw [rho_neg_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  rw [← proj_neg_single]
  refine (mem_twistedRootGroup_iff_of_pair θ (isRoot_neg_single _ a) rfl hne1 _).2 ⟨c, ?_⟩
  rw [slOrbitHom_tv10, rho_neg_single, hρ, twistSign_neg_single, Int.cast_one, one_mul]

theorem slOrbitHom_param_upper {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {i : Fin (Tag.rank .F4)}
    (hai : orbitMap a = i) :
    ∀ g ∈ twistedRootGroup k θ (Pi.single i 1), ∃ c : k,
      slOrbitHom θ hθ hab (tv 0 1 c) = g := by
  subst hai
  intro g hg
  have hρ := rhoPerm_of_orbit hab
  have hne1 : rho (Pi.single a 1) ≠ Pi.single a 1 := by
    rw [rho_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  rw [← proj_single] at hg
  obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ (isRoot_single _ a) rfl hne1 g).1 hg
  refine ⟨c, Subtype.ext ?_⟩
  rw [slOrbitHom_tv01, hc, rho_single, hρ, twistSign_single, Int.cast_one, one_mul]

theorem slOrbitHom_param_lower {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {i : Fin (Tag.rank .F4)}
    (hai : orbitMap a = i) :
    ∀ g ∈ twistedRootGroup k θ (-Pi.single i 1), ∃ c : k,
      slOrbitHom θ hθ hab (tv 1 0 c) = g := by
  subst hai
  intro g hg
  have hρ := rhoPerm_of_orbit hab
  have hne1 : rho (-Pi.single a 1) ≠ -Pi.single a 1 := by
    rw [rho_neg_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  rw [← proj_neg_single] at hg
  obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ (isRoot_neg_single _ a) rfl hne1 g).1 hg
  refine ⟨c, Subtype.ext ?_⟩
  rw [slOrbitHom_tv10, hc, rho_neg_single, hρ, twistSign_neg_single, Int.cast_one, one_mul]

section Nodes

variable (hθ : ∀ c, θ (θ c) = c)

abbrev nodeHom0 : SL(2, fixedField θ) →* fixedGroup k θ := rFixed θ (nd 1) rfl

abbrev nodeHom1 : SL(2, fixedField θ) →* fixedGroup k θ := rFixed θ (nd 3) rfl

include hθ in
abbrev nodeHom2 : SL(2, k) →* fixedGroup k θ :=
  slOrbitHom θ hθ (a := nd 2) (b := nd 4) (Or.inl ⟨rfl, rfl⟩)

include hθ in
abbrev nodeHom3 : SL(2, k) →* fixedGroup k θ :=
  slOrbitHom θ hθ (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩)

end Nodes

end CFSG.ClassicalInvolution.WeakCT
