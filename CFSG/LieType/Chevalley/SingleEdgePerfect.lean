module

public import CFSG.LieType.Chevalley.A2Commutator
public import CFSG.LieType.Chevalley.PerfectSimpleRoot

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped commutatorElement

variable {τ : Tag} {K : Type*} [Field K]

theorem mem_commutator_of_eq_conj {G : Type*} [Group G] {x g c : G} (hc : c ∈ commutator G)
    (h : x = g * c * g⁻¹) : x ∈ commutator G :=
  h ▸ (Subgroup.commutator_normal ⊤ ⊤).conj_mem c hc g

@[expose] def nElt
    (i : Fin τ.rank) : adjointGroup τ K :=
  ⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩

theorem coe_nElt_inv (i : Fin τ.rank) :
    (((nElt (K := K) i)⁻¹ : adjointGroup τ K) : ModGL τ K) = weylElt τ K i (-1) := by
  rw [Subgroup.coe_inv, nElt, weylElt_inv]

theorem xElt_mem_commutator_of_cartan
    {i j : Fin τ.rank} (hij : τ.cartan i j = -1)
    (hji : τ.cartan j i = -1) (a : K) : xElt j a ∈ commutator (adjointGroup τ K) := by
  have h := (a2_simple_root_commutator τ K i j hij hji 1 a).1
  rw [one_mul] at h
  refine mem_commutator_of_eq_conj (g := (nElt i)⁻¹) (c := ⁅xElt i 1, xElt j a⁆)
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) ?_
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, inv_inv, coe_nElt_inv, commutatorElement_def,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
  change xUnit τ K j a = weylElt τ K i (-1) *
    (xUnit τ K i 1 * xUnit τ K j a * (xUnit τ K i 1)⁻¹ * (xUnit τ K j a)⁻¹) * weylElt τ K i 1
  rw [← xUnit_neg, ← xUnit_neg, h, ← weylElt_inv]
  group

theorem yElt_mem_commutator_of_cartan
    {i j : Fin τ.rank} (hij : τ.cartan i j = -1)
    (hji : τ.cartan j i = -1) (a : K) : yElt j a ∈ commutator (adjointGroup τ K) := by
  have h := (a2_simple_root_commutator τ K i j hij hji 1 (-a)).2
  rw [one_mul, neg_neg] at h
  refine mem_commutator_of_eq_conj (g := (nElt i)⁻¹) (c := ⁅yElt i 1, yElt j (-a)⁆)
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) ?_
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, inv_inv, coe_nElt_inv, commutatorElement_def,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
  change yUnit τ K j a = weylElt τ K i (-1) *
    (yUnit τ K i 1 * yUnit τ K j (-a) * (yUnit τ K i 1)⁻¹ * (yUnit τ K j (-a))⁻¹) *
      weylElt τ K i 1
  rw [← yUnit_neg, ← yUnit_neg, neg_neg, h, ← weylElt_inv]
  group

variable (τ K) in
theorem single_edge_perfect
    (hτ : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    commutator (adjointGroup τ K) = ⊤ := by
  rw [eq_top_iff, ← iSup_simplePosSubgroup_sup_simpleNegSubgroup]
  refine iSup_le fun j => ?_
  obtain ⟨i, -, hij, hji⟩ := cartan_single_edge_neighbor τ hτ j
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨c, hc⟩ := mem_simplePosSubgroup.1 hg
    rw [show g = xElt j c from Subtype.ext hc]
    exact xElt_mem_commutator_of_cartan hij hji c
  · obtain ⟨c, hc⟩ := mem_simpleNegSubgroup.1 hg
    rw [show g = yElt j c from Subtype.ext hc]
    exact yElt_mem_commutator_of_cartan hij hji c

end CFSG.LieType.Chevalley
