module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcBQBasic
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Model
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Levi
public import CFSG.LieType.Steinberg.TwistedE6.Clause0
public import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.TwE6

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.TitsSimplicity CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models.TwistedPairs Subgroup

namespace PB2

theorem map_mem_commutator_of_range_le {G H : Type*} [Group G] [Group H] (f : G →* H)
    {L : Subgroup H} (hL : f.range ≤ L) {g : G} (hg : g ∈ _root_.commutator G) :
    f g ∈ ⁅L, L⁆ := by
  have h : f g ∈ (_root_.commutator G).map f := mem_map_of_mem f hg
  rw [map_commutator_eq] at h
  exact commutator_mono hL hL h


variable {k : Type} [Field k] (θ : k →+* k)

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

theorem single_add_single_apply_eq_zero {i : Fin (Tag.rank .F4)} (hi0 : i ≠ nf 0)
    (hi1 : i ≠ nf 1) :
    (Pi.single (nf 0) 1 + Pi.single (nf 1) 1 : Fin (Tag.rank .F4) → ℤ) i = 0 := by
  rw [Pi.add_apply, Pi.single_eq_of_ne hi0, Pi.single_eq_of_ne hi1, add_zero]

theorem rootGroup_le_levi_of_support (hθ : ∀ c, θ (θ c) = c)
    {C : Finset (Fin (twistedDatum k θ).rank)} {β : Fin (twistedDatum k θ).rank → ℤ}
    (hβ : IsRoot .F4 β) (hsupp : ∀ i ∉ C, β i = 0) :
    (twistedDatum k θ).rootGroup β ≤ levi (twistedDatum k θ).rootGroup C := by
  have h := Levi.rootGroup_le_leviC_of_support (D := twistedDatum k θ)
    (e := C.orderEmbOfFin rfl) rfl
    (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ))
    (by rw [twistedDatum_roots]; exact hβ)
    (fun i hi => hsupp i (by rwa [Finset.range_orderEmbOfFin, Finset.mem_coe] at hi))
  rwa [BQ.leviC_orderEmbOfFin] at h

theorem twistedRootGroup_fixed_le_commutator_of_le {a c : Fin (Tag.rank .E6)}
    (ha : rhoPerm a = a) (hc : rhoPerm c = c) (hac : IsRoot .E6 (Pi.single a 1 + Pi.single c 1))
    {i l : Fin (Tag.rank .F4)} (hi : orbitMap a = i) (hl : orbitMap c = l)
    {L : Subgroup (fixedGroup k θ)}
    (hL₁ : twistedRootGroup k θ (Pi.single i 1 + Pi.single l 1) ≤ L)
    (hL₂ : twistedRootGroup k θ (-Pi.single l 1) ≤ L) :
    twistedRootGroup k θ (Pi.single i 1) ≤ ⁅L, L⁆ := by
  subst hi hl
  intro x hx
  have h1 : rho (Pi.single a 1) = Pi.single a 1 := by rw [rho_single, ha]
  rw [← proj_single] at hx
  obtain ⟨u, hu, hxu⟩ :=
    (mem_twistedRootGroup_iff_of_fixed θ (isRoot_single _ a) rfl h1 x).1 hx
  have hδ : IsRoot .E6 (-Pi.single c 1) := isRoot_neg_single _ c
  have hsum : (Pi.single a 1 + Pi.single c 1 + -Pi.single c 1 : Fin (Tag.rank .E6) → ℤ) =
      Pi.single a 1 := add_neg_cancel_right _ _
  have hne : (Pi.single a 1 + Pi.single c 1 + -Pi.single c 1 : Fin (Tag.rank .E6) → ℤ) ≠ 0 := by
    rw [hsum]
    exact (isRoot_single _ a).ne_zero
  have hroot : IsRoot .E6 (Pi.single a 1 + Pi.single c 1 + -Pi.single c 1) := by
    rw [hsum]
    exact isRoot_single _ a
  obtain ⟨σ, hσ, hcomm⟩ := (e6Data_valid.commutator_xm k hac hδ hne).1 hroot
  have hrγ : rho (Pi.single a 1 + Pi.single c 1) = Pi.single a 1 + Pi.single c 1 := by
    change rho (Pi.single a 1) + rho (Pi.single c 1) = _
    rw [rho_single, rho_single, ha, hc]
  have hrδ : rho (-Pi.single c 1) = -Pi.single c 1 := by rw [rho_neg_single, hc]
  have hσθ : θ σ = σ := by rcases hσ with rfl | rfl <;> simp
  let y := xFixed θ hac hrγ (σ * u) (by rw [map_mul, hσθ, hu])
  let z := xFixed θ hδ hrδ 1 (map_one θ)
  have hy : y ∈ twistedRootGroup k θ (proj (Pi.single a 1 + Pi.single c 1)) :=
    xFixed_mem θ hac hrγ _ _
  have hz : z ∈ twistedRootGroup k θ (proj (-Pi.single c 1)) := xFixed_mem θ hδ hrδ _ _
  rw [map_add, proj_single, proj_single] at hy
  rw [proj_neg_single] at hz
  have e : x = ⁅y, z⁆ := by
    apply Subtype.ext
    change (x : e6Data_valid.minGroup k) =
      ⁅e6Data_valid.xm k (Pi.single a 1 + Pi.single c 1) (σ * u),
        e6Data_valid.xm k (-Pi.single c 1) 1⁆
    rw [hxu, hcomm, hsum]
    congr 1
    rcases hσ with rfl | rfl <;> ring
  rw [e]
  exact commutator_mem_commutator (hL₁ hy) (hL₂ hz)

end PB2


variable {k : Type} [Field k] (θ : k →+* k)

theorem rootGroup_short_le_commutator_levi (hθ : ∀ c, θ (θ c) = c)
    (hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) k))
    {C : Finset (Fin (twistedDatum k θ).rank)} {j : Fin (twistedDatum k θ).rank} (hj : j ∈ C)
    (hj23 : j = nf 2 ∨ j = nf 3) :
    (twistedDatum k θ).rootGroup (Pi.single j 1) ≤
      ⁅levi (twistedDatum k θ).rootGroup C, levi (twistedDatum k θ).rootGroup C⁆ := by
  have hle := rankOne_le_levi (twistedDatum k θ).rootGroup hj
  have hmem : ∀ M : Matrix.SpecialLinearGroup (Fin 2) k, M ∈ _root_.commutator _ := fun M => by
    rw [Group.isPerfect_def.1 hSL]
    exact mem_top M
  intro g hg
  rcases hj23 with rfl | rfl
  · obtain ⟨c, rfl⟩ := slOrbitHom_param_upper θ hθ (a := nd 2) (b := nd 4) (Or.inl ⟨rfl, rfl⟩)
      (i := nf 2) rfl g hg
    exact PB2.map_mem_commutator_of_range_le _ ((rankOne_twistedE6_two θ hθ).symm.le.trans hle)
      (hmem _)
  · obtain ⟨c, rfl⟩ := slOrbitHom_param_upper θ hθ (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩)
      (i := nf 3) rfl g hg
    exact PB2.map_mem_commutator_of_range_le _
      ((rankOne_twistedE6_three θ hθ).symm.le.trans hle) (hmem _)

theorem rootGroup_long_le_commutator_levi
    (hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (fixedField θ)))
    {C : Finset (Fin (twistedDatum k θ).rank)} {j : Fin (twistedDatum k θ).rank} (hj : j ∈ C)
    (hj01 : j = nf 0 ∨ j = nf 1) :
    (twistedDatum k θ).rootGroup (Pi.single j 1) ≤
      ⁅levi (twistedDatum k θ).rootGroup C, levi (twistedDatum k θ).rootGroup C⁆ := by
  have hle := rankOne_le_levi (twistedDatum k θ).rootGroup hj
  have hmem : ∀ M : Matrix.SpecialLinearGroup (Fin 2) (fixedField θ),
      M ∈ _root_.commutator _ := fun M => by
    rw [Group.isPerfect_def.1 hSL]
    exact mem_top M
  intro g hg
  rcases hj01 with rfl | rfl
  · obtain ⟨c, rfl⟩ := rFixed_param_upper θ (nd 1) rfl (i := nf 0) rfl g hg
    exact PB2.map_mem_commutator_of_range_le _ ((rankOne_twistedE6_zero θ).symm.le.trans hle)
      (hmem _)
  · obtain ⟨c, rfl⟩ := rFixed_param_upper θ (nd 3) rfl (i := nf 1) rfl g hg
    exact PB2.map_mem_commutator_of_range_le _ ((rankOne_twistedE6_one θ).symm.le.trans hle)
      (hmem _)

theorem rootGroup_long_le_commutator_levi_of_long (hθ : ∀ c, θ (θ c) = c)
    {C : Finset (Fin (twistedDatum k θ).rank)} (h0 : nf 0 ∈ C) (h1 : nf 1 ∈ C)
    {j : Fin (twistedDatum k θ).rank} (hj01 : j = nf 0 ∨ j = nf 1) :
    (twistedDatum k θ).rootGroup (Pi.single j 1) ≤
      ⁅levi (twistedDatum k θ).rootGroup C, levi (twistedDatum k θ).rootGroup C⁆ := by
  have h01 : twistedRootGroup k θ (Pi.single (nf 0) 1 + Pi.single (nf 1) 1) ≤
      levi (twistedDatum k θ).rootGroup C := by
    refine PB2.rootGroup_le_levi_of_support θ hθ ?_ fun i hi =>
      PB2.single_add_single_apply_eq_zero (ne_of_mem_of_not_mem h0 hi).symm
        (ne_of_mem_of_not_mem h1 hi).symm
    have h := isRoot_proj isRoot_single_add_single_one_three
    rwa [map_add, proj_single, proj_single] at h
  have hneg : ∀ i ∈ C, twistedRootGroup k θ (-Pi.single i 1) ≤
      levi (twistedDatum k θ).rootGroup C :=
    fun i hi => le_sup_right.trans (rankOne_le_levi _ hi)
  rcases hj01 with rfl | rfl
  · exact PB2.twistedRootGroup_fixed_le_commutator_of_le θ (a := nd 1) (c := nd 3) rfl rfl
      isRoot_single_add_single_one_three (i := nf 0) (l := nf 1) rfl rfl h01 (hneg _ h1)
  · refine PB2.twistedRootGroup_fixed_le_commutator_of_le θ (a := nd 3) (c := nd 1) rfl rfl
      isRoot_single_add_single_three_one (i := nf 1) (l := nf 0) rfl rfl ?_ (hneg _ h0)
    rw [add_comm]
    exact h01

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.TwE6
