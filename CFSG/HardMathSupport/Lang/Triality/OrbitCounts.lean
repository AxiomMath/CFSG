module

public import CFSG.Timmesfeld.Orders.ExceptionalTwistedOrder

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Triality

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders

@[expose] def orbitsIn (t : TwistTag) (S : Set (Fin t.tag.rank → ℤ)) : ℕ :=
  {O : Finset (Fin t.tag.rank → ℤ) | O ∈ t.diagramRootOrbits ∧
    (O : Set (Fin t.tag.rank → ℤ)) ⊆ S}.ncard

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K} {q : ℕ}


theorem card_diagramOrbit_inf_const (hq : ∀ a, Nat.card (orbitField t K σ a) = q)
    {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) :
    Nat.card ↥(rootSpan t.tag K (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)) ⊓
      twistedFixedGroup t K σ) = q := by
  obtain ⟨w, hw, a, heq, -, -⟩ := (diagram_root_orbit_reduction t).1 α hα
  have hset : (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)) =
      (fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a) := by
    rw [heq, Finset.coe_image]
  rw [hset, ← Nat.card_congr (orbitConjEquiv t σ a hw).toEquiv]
  exact (Nat.card_congr Multiplicative.toAdd).trans (hq a)

theorem card_rootSpan_inf_twistedFixedGroup_const (hσ : Function.Surjective σ)
    (hq : ∀ a, Nat.card (orbitField t K σ a) = q)
    {S : Set (Fin t.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot t.tag α ∧ 0 < height α)
    (hSρ : ∀ α ∈ S, permLattice t.perm α ∈ S)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • α + b • β) →
      a • α + b • β ∈ S) :
    Nat.card ↥(rootSpan t.tag K S ⊓ twistedFixedGroup t K σ) = q ^ orbitsIn t S := by
  classical
  set 𝒪 : Set (Finset (Fin t.tag.rank → ℤ)) :=
    {O' | O' ∈ t.diagramRootOrbits ∧ (O' : Set (Fin t.tag.rank → ℤ)) ⊆ S}
  have hfin : 𝒪.Finite := by
    refine ((finite_setOf_isRoot t.tag).image fun α => t.diagramOrbit α).subset ?_
    rintro O ⟨⟨α, hα, rfl⟩, -⟩
    exact ⟨α, hα, rfl⟩
  set F := hfin.toFinset
  set O : Fin F.card → Finset (Fin t.tag.rank → ℤ) := fun j => (F.equivFin.symm j : _)
  have hO : Function.Injective O := fun i j h => F.equivFin.symm.injective (Subtype.ext h)
  have hrange : Set.range O = 𝒪 := by
    ext O'
    refine ⟨fun ⟨j, hj⟩ => hj ▸ hfin.mem_toFinset.1 (F.equivFin.symm j).2, fun h =>
      ⟨F.equivFin ⟨O', hfin.mem_toFinset.2 h⟩, by simp [O]⟩⟩
  have hbij := bijOn_prod_graphFixed hσ hS hSρ hclosed O hO hrange
  have hmemO : ∀ j, O j ∈ 𝒪 := fun j => hrange ▸ Set.mem_range_self j
  have hcardO : ∀ j, Nat.card ↥(rootSpan t.tag K (O j : Set (Fin t.tag.rank → ℤ)) ⊓
      twistedFixedGroup t K σ) = q := fun j => by
    obtain ⟨⟨α, hα, hαO⟩, -⟩ := hmemO j
    rw [← hαO]
    exact card_diagramOrbit_inf_const hq hα
  have hcount : orbitsIn t S = F.card := by
    rw [orbitsIn, Set.ncard_eq_toFinset_card _ hfin]
  calc Nat.card ↥(rootSpan t.tag K S ⊓ twistedFixedGroup t K σ)
      = Nat.card (Set.univ : Set ((j : Fin F.card) → ↥(rootSpan t.tag K
          (O j : Set (Fin t.tag.rank → ℤ)) ⊓ twistedFixedGroup t K σ))) :=
        (Nat.card_congr hbij.equiv).symm
    _ = ∏ j, Nat.card ↥(rootSpan t.tag K (O j : Set (Fin t.tag.rank → ℤ)) ⊓
          twistedFixedGroup t K σ) := by rw [Nat.card_univ, Nat.card_pi]
    _ = q ^ orbitsIn t S := by
      rw [Finset.prod_congr rfl fun j _ => hcardO j, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, hcount]

theorem card_graphFixedPosUnipotent_const (hσ : Function.Surjective σ)
    (hq : ∀ a, Nat.card (orbitField t K σ a) = q) :
    Nat.card (graphFixedPosUnipotent t K σ) =
      q ^ orbitsIn t {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α} := by
  refine card_rootSpan_inf_twistedFixedGroup_const hσ hq (fun _ h => h)
    (fun α hα => ⟨hα.1.permLattice t.cartan_perm, by rw [height_permLattice]; exact hα.2⟩)
    fun α hα β hβ a b ha hb hr => ⟨hr, ?_⟩
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  rw [height_nsmul_add_nsmul]
  nlinarith [hα.2, hβ.2]

theorem card_graphFixedInversionUnipotent_const (hσ : Function.Surjective σ)
    (hq : ∀ a, Nat.card (orbitField t K σ a) = q) {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) :
    Nat.card (graphFixedInversionUnipotent t K σ w) = q ^ orbitsIn t (inversionSet w) := by
  refine card_rootSpan_inf_twistedFixedGroup_const hσ hq (fun _ h => inversionSet_pos h) ?_
    (inversionSet_closed w)
  rintro α ⟨hα, hpos, -, hneg⟩
  refine ⟨hα.permLattice t.cartan_perm, by rwa [height_permLattice],
    IsRoot.smul (hα.permLattice t.cartan_perm) w, ?_⟩
  rw [← (mem_relWeylTwist t).1 hw, weylTwist_smul_permLattice, height_permLattice]
  exact hneg

open Classical in
theorem card_graphFixedRootGroup_const [Finite K] [Fintype (WeylGroup t.tag)]
    (hσ : Function.Surjective σ) (hq : ∀ a, Nat.card (orbitField t K σ a) = q) :
    Nat.card (graphFixedRootGroup t K σ) = Nat.card (compatTorus (t := t) σ) *
      q ^ orbitsIn t {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α} *
        ∑ w ∈ Finset.univ.filter (· ∈ relWeylTwist t), q ^ orbitsIn t (inversionSet w) := by
  rw [card_graphFixedRootGroup_eq hσ, card_graphFixedRootBorel hσ,
    graphFixedRootTorus_eq_compatTorus hσ, card_graphFixedPosUnipotent_const hσ hq,
    finsum_eq_sum_of_fintype]
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ relWeylTwist t)) (fun w => by simp)
    (fun w => Nat.card (graphFixedInversionUnipotent t K σ w))]
  refine Finset.sum_congr rfl fun w hw => ?_
  exact card_graphFixedInversionUnipotent_const hσ hq (Finset.mem_filter.1 hw).2

end CFSG.HardMathSupport.Lang.Triality
