module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.ComponentClassification CFSG.LocalCores Subgroup

theorem i183v_outer_component_of_ne_top (hS : CatalogueRelativeB.CatalogueSchreier)
    {H : Type} [Group H] [Finite H] (hKP : CFSG.IsKProper H) (N : Subgroup H) [N.Normal]
    (K : Subgroup (H ⧸ N)) (hK : CFSG.IsComponent K) (hne : K ≠ ⊤) :
    Group.IsSolvable (OuterAutomorphisms.Outer (K ⧸ center K)) := by
  set K' : Subgroup H := K.comap (QuotientGroup.mk' N) with hK'
  have hK'ne : K' ≠ ⊤ := by
    intro h
    apply hne
    rw [eq_top_iff]
    intro q _
    obtain ⟨h0, rfl⟩ := QuotientGroup.mk_surjective q
    have : h0 ∈ K' := by rw [h]; exact mem_top _
    exact this
  have hopen : CFSG.Open.IsKGroup ↥K' :=
    CatalogueKProper.proper_subgroup_open_isKGroup
      (CatalogueKProper.kProper_of_isKProper hKP) K' hK'ne
  have hsch := LBalance.schreierSections_of_kGroup hS hopen
  have : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
  let g : K' →* K := ((QuotientGroup.mk' N).comp K'.subtype).codRestrict K fun x => x.2
  have hg : Function.Surjective g := by
    intro k
    obtain ⟨h0, hh0⟩ := QuotientGroup.mk_surjective (k : H ⧸ N)
    exact ⟨⟨h0, by show QuotientGroup.mk' N h0 ∈ K; rw [QuotientGroup.mk'_apply, hh0]; exact k.2⟩,
      Subtype.ext hh0⟩
  exact hsch.outer_solvable (⊤ : Subgroup K') hK.1.2.2
    ((QuotientGroup.mk' (center K)).comp (g.comp (Subgroup.topEquiv (G := K')).toMonoidHom))
    (fun s => by
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center K) s
      obtain ⟨a, rfl⟩ := hg k
      exact ⟨⟨a, mem_top _⟩, rfl⟩)

theorem i183v_lBalancePLayer_centralizer_element_le (hS : CatalogueRelativeB.CatalogueSchreier)
    {H : Type} [Group H] [Finite H] (hKP : CFSG.IsKProper H) {p : ℕ} [Fact p.Prime] {x : H}
    (hx : ∃ n : ℕ, x ^ p ^ n = 1) :
    lBalancePLayer p (centralizer ({x} : Set H)) ≤ lBalancePLayer p ⊤ := by
  rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_top]
  refine LBalance.pLayer_centralizer_le_pLayer_of_quotient hx fun L hLC hL => ?_
  by_cases htop : CFSG.IsComponent (⊤ : Subgroup (H ⧸ pPrimeCore p H))
  · exact (le_top).trans (CFSG.LocalCores.component_le_layer htop)
  · refine LBalance.pComponent_centralizer_le_layer
      (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p)
      (LBalance.Quot.exists_mk_pow_eq_one hx) (fun K hK => ?_) hLC hL
    exact i183v_outer_component_of_ne_top hS hKP (pPrimeCore p H) K hK
      (fun h => htop (h ▸ hK))

theorem i183v_glaPLayer_centralizer_le_top (hS : CatalogueRelativeB.CatalogueSchreier)
    {G : Type} [Group G] [Finite G] (hKP : CFSG.IsKProper G) {x : G} (hx : x ^ 3 = 1) :
    GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)) ≤ GLAPLayer 3 (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [i183_glaPLayer_eq, i183_glaPLayer_eq]
  exact i183v_lBalancePLayer_centralizer_element_le hS hKP ⟨1, by simpa using hx⟩

end CFSG.HardMathSupport.Solomon.Coordinator
