module

public import CFSG.Certificates.Kernel.RouteP.MonoWSound
public import CFSG.Certificates.Kernel.RouteP.MonoPerm

public section

namespace CFSG.KS.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.Fi24Net
  CFSG.KC.RouteP CFSG.KS.Fi24Net Pointwise

variable {G : Type*} [Group G] [MulAction G Pt]

theorem smul_mem_orbit_of_mem {H : Subgroup G} {g : G} (hg : g ∈ H) {x y : Pt}
    (hy : y ∈ MulAction.orbit H x) : g • y ∈ MulAction.orbit H x := by
  obtain ⟨h, rfl⟩ := hy
  exact ⟨⟨g, hg⟩ * h, mul_smul (⟨g, hg⟩ : H) h x⟩

theorem mem_orbit_of_closeS {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {gens : List Int}
    (hg : ∀ z ∈ gens, LOK NW KA KB z) (ρ : Int → G)
    (hρ : ∀ z ∈ gens, ∀ y : Pt, (ρ z • y).val = eL NW KA KB z y.val) {H : Subgroup G}
    (hH : ∀ z ∈ gens, ρ z ∈ H) (n : Nat) (x N : Pt)
    (h : memS (closeS NW KA KB gens n (single x.val)) N.val = true) : N ∈ MulAction.orbit H x := by
  obtain ⟨_, hN⟩ := closeS_min hg (fun M => ∃ hM : M < 920808, (⟨M, hM⟩ : Pt) ∈ MulAction.orbit H x)
    (fun M ⟨hM, ho⟩ z hz => ⟨eL_lt (hg z hz) hM, by
      have e : (⟨eL NW KA KB z M, eL_lt (hg z hz) hM⟩ : Pt) = ρ z • (⟨M, hM⟩ : Pt) :=
        Fin.ext (hρ z hz ⟨M, hM⟩).symm
      rw [e]
      exact smul_mem_orbit_of_mem (hH z hz) ho⟩)
    n (single x.val) (fun M hM hs => by
      rw [memS_single x.isLt hM] at hs
      have e : (⟨M, hM⟩ : Pt) = x := Fin.ext (of_decide_eq_true hs)
      refine ⟨hM, ?_⟩
      rw [e]
      exact MulAction.mem_orbit_self x) N.val N.isLt h
  exact hN

theorem mem_orbit_of_closeW {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {ws : List (List Int)}
    (hg : ∀ w ∈ ws, ∀ z ∈ w, LOK NW KA KB z) (σ : List Int → G)
    (hσ : ∀ w ∈ ws, ∀ y : Pt, (σ w • y).val = eW NW KA KB w y.val) {H : Subgroup G}
    (hH : ∀ w ∈ ws, σ w ∈ H) (n : Nat) (x N : Pt)
    (h : memS (closeW NW KA KB ws n (single x.val)) N.val = true) : N ∈ MulAction.orbit H x := by
  obtain ⟨_, hN⟩ := closeW_min hg (fun M => ∃ hM : M < 920808, (⟨M, hM⟩ : Pt) ∈ MulAction.orbit H x)
    (fun M _ ⟨hM, ho⟩ w hw => ⟨eW_lt w (hg w hw) hM, by
      have e : (⟨eW NW KA KB w M, eW_lt w (hg w hw) hM⟩ : Pt) = σ w • (⟨M, hM⟩ : Pt) :=
        Fin.ext (hσ w hw ⟨M, hM⟩).symm
      rw [e]
      exact smul_mem_orbit_of_mem (hH w hw) ho⟩)
    n (single x.val) (fun M hM hs => by
      rw [memS_single x.isLt hM] at hs
      have e : (⟨M, hM⟩ : Pt) = x := Fin.ext (of_decide_eq_true hs)
      refine ⟨hM, ?_⟩
      rw [e]
      exact MulAction.mem_orbit_self x) N.val N.isLt h
  exact hN

theorem mem_of_mem_orbit {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {gens : List Int}
    (hg : ∀ z ∈ gens, LOK NW KA KB z) (ρ : Int → G)
    (hρ : ∀ z ∈ gens, ∀ y : Pt, (ρ z • y).val = eL NW KA KB z y.val) {H : Subgroup G}
    (hH : H ≤ Subgroup.closure {g | ∃ z ∈ gens, ρ z = g}) {S : Nat}
    (hc : closedS NW KA KB gens S = true) {x : Pt} (hx : memS S x.val = true) (N : Pt)
    (hN : N ∈ MulAction.orbit H x) : memS S N.val = true := by
  let T : Set Pt := {y | memS S y.val = true}
  have hT : Subgroup.closure {g | ∃ z ∈ gens, ρ z = g} ≤ MulAction.stabilizer G T := by
    rw [Subgroup.closure_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have e := memS_imgS (hg z hz) S ((ρ z)⁻¹ • y).isLt
    rw [closedS_spec gens hc z hz, ← hρ z hz, smul_inv_smul] at e
    change memS S ((ρ z)⁻¹ • y).val = true ↔ memS S y.val = true
    rw [e]
  obtain ⟨h, rfl⟩ := hN
  have hs : (h : G) • T = T := hT (hH h.2)
  have hm : (h : G) • x ∈ (h : G) • T := Set.smul_mem_smul_set hx
  rw [hs] at hm
  exact hm

theorem card_filter_fin (p : Nat → Bool) :
    Fintype.card {N : Pt // p N.val = true} = ((List.range 920808).filter p).length := by
  rw [Fintype.card_subtype, ← Finset.card_map Fin.valEmbedding]
  have e : (Finset.univ.filter fun N : Pt => p N.val = true).map Fin.valEmbedding =
      (Finset.range 920808).filter fun k => p k = true := by
    ext k
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.isLt, ha⟩
    · rintro ⟨hk, hp⟩
      exact ⟨⟨k, hk⟩, hp, rfl⟩
  rw [e, Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  simp

theorem orbOK_orbit {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {gens : List Int} {n m : Nat}
    (hg : ∀ z ∈ gens, LOK NW KA KB z) (ρ : Int → G)
    (hρ : ∀ z ∈ gens, ∀ y : Pt, (ρ z • y).val = eL NW KA KB z y.val) {H : Subgroup G}
    (hH1 : ∀ z ∈ gens, ρ z ∈ H) (hH2 : H ≤ Subgroup.closure {g | ∃ z ∈ gens, ρ z = g}) (x : Pt)
    (h : orbOK NW KA KB gens x.val n m = true) :
    (∀ N : Pt, memS (closeS NW KA KB gens n (single x.val)) N.val = true ↔
      N ∈ MulAction.orbit H x) ∧ Nat.card (MulAction.orbit H x) = m := by
  obtain ⟨hx, hcl, -, hcount⟩ := orb_spec x.isLt hg h
  have hc : closedS NW KA KB gens (closeS NW KA KB gens n (single x.val)) = true := by
    unfold orbOK at h
    rw [letB_eq'] at h
    exact (andB_true h).1
  have hiff : ∀ N : Pt, memS (closeS NW KA KB gens n (single x.val)) N.val = true ↔
      N ∈ MulAction.orbit H x := fun N =>
    ⟨mem_orbit_of_closeS hg ρ hρ hH1 n x N, mem_of_mem_orbit hg ρ hρ hH2 hc hx N⟩
  refine ⟨hiff, ?_⟩
  have e : MulAction.orbit H x = {N : Pt | memS (closeS NW KA KB gens n (single x.val)) N.val = true} :=
    Set.ext fun N => (hiff N).symm
  rw [e, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', ← hcount, ← card_filter_fin]
  rw [Set.toFinset_card]
  rfl

end CFSG.KS.RouteP

end
