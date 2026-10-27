module

public import CFSG.Fischer.Rec23Star
public import CFSG.Fischer.Polar.Facts
public import CFSG.Sporadic.Fi22.LH.Facts
public import CFSG.Sporadic.Fi23.Fischer

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Rec23

theorem exists_mem_localClass_of_loc {Z : Type} [Group Z] {C : Set Z} (hP : Pair Z C)
    (hloc : ∀ f ∈ C, Nonempty (LocalPoints (pairModel Sporadic.Fi22.pair_D) C f)) :
    ∃ d ∈ C, ∃ f, f ∈ LocalClass C d := by
  obtain ⟨e, he⟩ := hP.2.1
  have hd : e ∈ C := by rw [he]; exact IsConj.refl e
  obtain ⟨L⟩ := hloc e hd
  exact ⟨e, hd, exists_mem_localClass_of_localPoints L⟩

variable {Y Z : Type} [Group Y] [Group Z] {E : Set Y} {F : Set Z}

theorem exists_mulEquiv_of_connected
    (hF : F23 Z F) (hZF : Subgroup.center Z = ⊥)
    (hSF : IsSimpleGroup (commutator Z)) (hE : Pair Y E)
    (hloc : ∀ f ∈ E, Nonempty (LocalPoints (pairModel Sporadic.Fi22.pair_D) E f))
    (hconn : (commGraph E).Connected) (hZ : Subgroup.center Y = ⊥) :
    ∃ φ : Y ≃* Z, φ '' E = F := by
  have hPF := polarFacts
  have hHF := hyperovalFacts
  have hFF := Sporadic.Fi22.fi22Facts hPF hHF
  have hlocF : ∀ f ∈ F, Nonempty (LocalPoints (pairModel Sporadic.Fi22.pair_D) F f) :=
    fun _ hf => Sporadic.Fi22.F23.nonempty_localPoints_fi22 hPF hF hf
  obtain ⟨d, hd, f, hf⟩ := exists_mem_localClass_of_loc hE hloc
  obtain ⟨d', hd', f', hf'⟩ := exists_mem_localClass_of_loc hF.1 hlocF
  have hconnF : (commGraph F).Connected :=
    Pair.connected_of_simple hF.1 hSF ⟨d', f', hd', hf'.1, hf'.2.1.symm, hf'.2.2.symm⟩
  have huE : compSet E d = Set.univ :=
    compSet_eq_univ fun c hc hcd => Pair.muSet_nonempty hE hconn hd hc hcd
  have huF : compSet F d' = Set.univ :=
    compSet_eq_univ fun c hc hcd => Pair.muSet_nonempty hF.1 hconnF hd' hc hcd
  obtain ⟨ι⟩ := F23.nonempty_compGraphIso' hPF hHF hFF hE hF.1 hloc hlocF hd hd'
  let β : commGraph E ≃g commGraph F :=
    (compGraphIsoTop huE).symm.trans (ι.trans (compGraphIsoTop huF))
  refine Pair.mulEquiv_of_graphIso hE hF.1 hZ hZF β fun e x he hx hex => ?_
  exact Pair.ySet_subset_of_fi22 hPF hHF hFF hF.1 hlocF he hx hex
    (Pair.muSet_nonempty hF.1 hconnF he hx fun h => hex h.symm)

@[expose] def comp (E : Set Y) (d : E) : Set Y :=
  {c | ∃ hc : c ∈ E, (commGraph E).Reachable d ⟨c, hc⟩}

theorem self_mem_comp (E : Set Y) (d : E) : (d : Y) ∈ comp E d :=
  ⟨d.2, SimpleGraph.Reachable.refl d⟩

theorem isStarClosed_comp (hE : Pair Y E) (d : E) : IsStarClosed E (comp E d) where
  subset _ hc := hc.1
  nonempty := ⟨d, self_mem_comp E d⟩
  nbr k hk c hc hck :=
    ⟨hc, hk.2.trans (commGraph_reachable_of_commute (a := ⟨k, hk.1⟩) (b := ⟨c, hc⟩) hck.symm)⟩
  conj k hk c hc := by
    have h1 := Pair.reachable_conjPerm_self hE (e := ⟨k, hk.1⟩) (a := ⟨c, hc.1⟩)
      (hk.2.symm.trans hc.2)
    have e : (Pair.conjPerm hE k ⟨c, hc.1⟩ : E) =
        ⟨k * c * k, Pair.mul_mul_mem hE hk.1 hc.1⟩ :=
      Subtype.ext (by rw [Pair.conjPerm_apply, Pair.inv_eq hE hk.1])
    rw [e] at h1
    exact ⟨_, hk.2.trans h1⟩

theorem connected_comp (hE : Pair Y E) (d : E) :
    (commGraph (Subtype.val ⁻¹' comp E d : Set (Subgroup.closure (comp E d)))).Connected := by
  have hK := isStarClosed_comp hE d
  let d₀ : ↥(Subtype.val ⁻¹' comp E d : Set (Subgroup.closure (comp E d))) :=
    ⟨⟨d, Subgroup.subset_closure (self_mem_comp E d)⟩, self_mem_comp E d⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨d₀, fun v => ?_⟩
  obtain ⟨v, hv⟩ := v
  have key := reachable_induction (G := commGraph E)
    (p := fun a : E => ∃ ha : (a : Y) ∈ comp E d, (commGraph (Subtype.val ⁻¹' comp E d :
      Set (Subgroup.closure (comp E d)))).Reachable d₀
        ⟨⟨a, Subgroup.subset_closure ha⟩, ha⟩) ?_ hv.2 ⟨self_mem_comp E d,
        SimpleGraph.Reachable.refl d₀⟩
  · obtain ⟨_, h⟩ := key
    exact h
  · rintro a b hab ⟨ha, hra⟩
    have hb : (b : Y) ∈ comp E d := hK.nbr a ha b b.2 hab.2.symm
    refine ⟨hb, hra.trans (SimpleGraph.Adj.reachable ?_)⟩
    exact ⟨fun h => hab.1 (Subtype.ext (by simpa using h)), Subtype.ext hab.2⟩

section Component

variable (hE : Pair Y E)
  (hloc : ∀ f ∈ E, Nonempty (LocalPoints (pairModel Sporadic.Fi22.pair_D) E f))
  (hZ : HasZ E) (d : E)
include hE hloc hZ

theorem exists_mulEquiv_comp
    (hF : F23 Z F) (hZF : Subgroup.center Z = ⊥)
    (hSF : IsSimpleGroup (commutator Z)) :
    ∃ φ : Subgroup.closure (comp E d) ≃* Z,
      φ '' (Subtype.val ⁻¹' comp E d : Set (Subgroup.closure (comp E d))) = F := by
  have := Pair.finite hE
  have hK := isStarClosed_comp hE d
  have hH : LocalHyp Y E := LocalHyp.of_pair hE hloc
  have hKS : comp E d ⊆ Subgroup.closure (comp E d) := Subgroup.subset_closure
  have hloc' : ∀ f ∈ (Subtype.val ⁻¹' comp E d : Set (Subgroup.closure (comp E d))),
      Nonempty (LocalPoints (pairModel Sporadic.Fi22.pair_D)
        (Subtype.val ⁻¹' comp E d : Set (Subgroup.closure (comp E d))) f) := by
    intro f hf
    obtain ⟨L⟩ := hloc (f : Y) (hK.subset hf)
    exact ⟨restrictPoints hK hKS hf L⟩
  have hZ' := hZ.subgroup hK hKS
  have hcenter : Subgroup.center (Subgroup.closure (comp E d)) = ⊥ := by
    refine hZ'.center_eq_bot ⟨⟨d, Subgroup.subset_closure (self_mem_comp E d)⟩,
      self_mem_comp E d⟩ fun f hf => ?_
    obtain ⟨L⟩ := hloc' f hf
    exact exists_mem_localClass_of_localPoints L
  exact exists_mulEquiv_of_connected hF hZF hSF (hK.pair_closure hH) hloc' (connected_comp hE d)
    hcenter

theorem isSimpleGroup_closure_comp :
    IsSimpleGroup (Subgroup.closure (comp E d)) := by
  obtain ⟨φ, -⟩ := exists_mulEquiv_comp hE hloc hZ d Sporadic.Fi23.f23_J Sporadic.Fi23.center_J
    Sporadic.Fi23.isSimpleGroup_commutator_J
  exact @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.Fi23.isSimpleGroup_J φ

end Component

theorem connected_of_hasZ
    (hE : Pair Y E)
    (hloc : ∀ f ∈ E, Nonempty (LocalPoints (pairModel Sporadic.Fi22.pair_D) E f))
    (hZ : HasZ E) : (commGraph E).Connected := by
  by_contra hconn
  obtain ⟨d, y, hdy⟩ : ∃ d y : E, ¬(commGraph E).Reachable d y := by
    by_contra hall
    push Not at hall
    obtain ⟨e, he⟩ := Pair.nonempty hE
    exact hconn ((SimpleGraph.connected_iff _).2 ⟨fun u v => hall u v, ⟨⟨e, he⟩⟩⟩)
  have hK := isStarClosed_comp hE d
  have hS := isSimpleGroup_closure_comp hE hloc hZ d
  let ψ : Subgroup.closure (comp E d) →* Equiv.Perm (commGraph E).ConnectedComponent :=
    (Pair.compPerm hE).comp (Subgroup.closure (comp E d)).subtype
  let xd : Subgroup.closure (comp E d) := ⟨d, Subgroup.subset_closure (self_mem_comp E d)⟩
  rcases hS.eq_bot_or_eq_top_of_normal ψ.ker with hbot | htop
  · obtain ⟨L⟩ := hloc d d.2
    obtain ⟨f, hf⟩ := exists_mem_localClass_of_localPoints L
    have hfK : f ∈ comp E d := hK.nbr d (self_mem_comp E d) f hf.1 hf.2.2
    let xf : Subgroup.closure (comp E d) := ⟨f, Subgroup.subset_closure hfK⟩
    have hadj : (commGraph E).Adj d ⟨f, hf.1⟩ :=
      ⟨fun h => hf.2.1 (congrArg Subtype.val h).symm, hf.2.2.symm⟩
    have heq := Pair.compPerm_eq_of_adj hE hadj
    have hmem : xd * xf ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      change Pair.compPerm hE ((d : Y) * f) = 1
      rw [map_mul]
      have heq' : Pair.compPerm hE f = Pair.compPerm hE d := heq.symm
      rw [heq', ← map_mul, Pair.mul_self hE d.2, map_one]
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : (d : Y) * f = 1 := congrArg Subtype.val hmem
    exact hf.2.1 ((eq_inv_of_mul_eq_one_right h1).trans (Pair.inv_eq hE d.2))
  · have hxd : xd ∈ ψ.ker := by rw [htop]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hxd
    change Pair.compPerm hE (d : Y) = 1 at hxd
    exact Pair.compPerm_mul_ne hE hdy (by rw [hxd, one_mul, mul_one])

end Rec23

end CFSG.Fischer
