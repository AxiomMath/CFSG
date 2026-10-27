module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Split

variable {τ : Tag} {K : Type} [Field K]

theorem odd_card_highTorusLine {f : ℕ} (hf : 1 ≤ f) (hKc : Nat.card K = 2 ^ f) :
    Odd (Nat.card (EPilot.highTorusLine τ K)) := by
  have h : Nat.card (EPilot.highTorusLine τ K) ∣ Nat.card Kˣ := card_range_dvd _
  rw [Nat.card_units, hKc] at h
  refine Odd.of_dvd_nat (Nat.Even.sub_odd Nat.one_le_two_pow ?_ odd_one) h
  exact (Nat.even_pow' (by omega)).2 even_two

theorem commute_of_mem_highTorusLine {x y : ModGL τ K} (hx : x ∈ EPilot.highTorusLine τ K)
    (hy : y ∈ EPilot.highTorusLine τ K) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem highTorusLine_subgroupOf_le_centralizer_self :
    (EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) ≤
      centralizer ((EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) :
        Set (adjointGroup τ K)) := fun _ hx =>
  Subgroup.mem_centralizer_iff.2 fun _ hy => Subtype.ext
    (commute_of_mem_highTorusLine (Subgroup.mem_subgroupOf.1 hy) (Subgroup.mem_subgroupOf.1 hx))


theorem highTorusLine_le_adjointGroup (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    EPilot.highTorusLine τ K ≤ adjointGroup τ K :=
  (EPilot.highTorusLine_le_highRootSL2 hτ).trans EPilot.highRootSL2_le_adjointGroup

theorem rootDiagUnit_highDiag_mem_adjointGroup (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (c : Kˣ) :
    rootDiagUnit τ (EPilot.highDiag τ c) ∈ adjointGroup τ K :=
  highTorusLine_le_adjointGroup hτ (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c)

theorem highTorusLine_subgroupOf_le_centralizer_perpLevi :
    (EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) ≤
      centralizer ((rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) :
        Set (adjointGroup τ K)) := fun _ hx =>
  Subgroup.mem_centralizer_iff.2 fun _ hy => Subtype.ext
    (EPilot.commute_of_mem_highTorusLine_of_mem_rootSpan (Subgroup.mem_subgroupOf.1 hx)
      (Subgroup.mem_subgroupOf.1 hy)).eq.symm

theorem disjoint_highTorusLine_subgroupOf_perpLevi (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    [CharP K 2] :
    Disjoint ((EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K))
      ((rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K)) := by
  rw [Subgroup.disjoint_def]
  intro g hgT hgD
  exact Subtype.ext ((Subgroup.disjoint_def.1 (EPilot.disjoint_highTorusLine_rootSpan hτ
    (ringChar.eq K 2))) (Subgroup.mem_subgroupOf.1 hgT) (Subgroup.mem_subgroupOf.1 hgD))

theorem centralizer_le_highTorusLine_sup (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K]
    [CharP K 2] {c : Kˣ} (hc : 3 ≤ orderOf c) {X : Subgroup (adjointGroup τ K)}
    (hcX : (⟨rootDiagUnit τ (EPilot.highDiag τ c), rootDiagUnit_highDiag_mem_adjointGroup hτ c⟩ :
      adjointGroup τ K) ∈ X) :
    centralizer (X : Set (adjointGroup τ K)) ≤
      (EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) ⊔
        (rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) := by
  intro g hg
  have hgc := congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hg _ hcX)
  have hm : (g : ModGL τ K) ∈ toralCentralizer τ K (EPilot.highDiag τ c) := by
    refine mem_toralCentralizer.2 ⟨g.2, ?_⟩
    change rootDiagUnit τ (EPilot.highDiag τ c) * (g : ModGL τ K) = (g : ModGL τ K) *
      rootDiagUnit τ (EPilot.highDiag τ c) at hgc
    rw [hgc, mul_inv_cancel_right]
  rw [(EPilot.toralCentralizer_highDiag_eq_sup hτ (ringChar.eq K 2) hc).1, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      EPilot.highTorusLine_le_normalizer_perpLevi] at hm
  obtain ⟨t, ht, d, hd, htd⟩ := Set.mem_mul.1 hm
  have hg' : g = ⟨t, highTorusLine_le_adjointGroup hτ ht⟩ *
      ⟨d, EPilot.rootSpan_le_adjointGroup' _ hd⟩ := Subtype.ext htd.symm
  rw [hg']
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 ht))
    (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hd))

theorem centralizer_eq_highTorusLine_sup_of_le (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K]
    [CharP K 2] {c : Kˣ} (hc : 3 ≤ orderOf c) {A : Subgroup (adjointGroup τ K)}
    (hAT : A ≤ (EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K))
    (hcA : (⟨rootDiagUnit τ (EPilot.highDiag τ c), rootDiagUnit_highDiag_mem_adjointGroup hτ c⟩ :
      adjointGroup τ K) ∈ A) :
    centralizer (A : Set (adjointGroup τ K)) =
      (EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) ⊔
        (rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) := by
  refine le_antisymm (centralizer_le_highTorusLine_sup hτ hc hcA) (sup_le (fun x hx => ?_) ?_)
  · exact Subgroup.mem_centralizer_iff.2 fun a ha =>
      Subgroup.mem_centralizer_iff.1 (highTorusLine_subgroupOf_le_centralizer_self hx) a (hAT ha)
  · rw [← Subgroup.le_centralizer_iff]
    exact hAT.trans highTorusLine_subgroupOf_le_centralizer_perpLevi

theorem centralizer_highTorusLine_eq (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) :
    centralizer ((EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) :
        Set (adjointGroup τ K)) =
      (EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) ⊔
        (rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) := by
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  exact centralizer_eq_highTorusLine_sup_of_le hτ hc le_rfl
    (Subgroup.mem_subgroupOf.2 (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c))

end Split

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem inSubgroup_layer_inf_centralizer_nonsplit_E6 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E6 K) {X : Subgroup (adjointGroup .E6 K)}
    (hXJ : X ≤ (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    inSubgroup layer
        (L ⊓ centralizer (((X.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) =
      ((a5Levi K).map e.symm.toMonoidHom).map L.subtype := by
  obtain ⟨hcen, -, hXD⟩ := centralizer_nonsplit_E6 hXJ hX hcyc
  exact F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hcen hXD
    (F4Pilot.le_centralizer_self_of_isCyclic hcyc) isQuasisimple_a5Levi

theorem inf_centralizer_nonsplit_E6 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E6 K) {X : Subgroup (adjointGroup .E6 K)}
    (hXJ : X ≤ (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    L ⊓ centralizer (((X.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) =
      (X.map e.symm.toMonoidHom).map L.subtype ⊔
        ((a5Levi K).map e.symm.toMonoidHom).map L.subtype := by
  rw [F4Pilot.inf_centralizer_map_symm, (centralizer_nonsplit_E6 hXJ hX hcyc).1, Subgroup.map_sup,
    Subgroup.map_sup]

theorem inSubgroup_layer_inf_centralizer_split_E6 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E6 K) {c : Kˣ} (hc : 3 ≤ orderOf c)
    {A : Subgroup (adjointGroup .E6 K)}
    (hAT : A ≤ (EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K))
    (hcA : (⟨rootDiagUnit .E6 (EPilot.highDiag .E6 c),
      rootDiagUnit_highDiag_mem_adjointGroup (Or.inl rfl) c⟩ : adjointGroup .E6 K) ∈ A) :
    inSubgroup layer
        (L ⊓ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) =
      ((a5Levi K).map e.symm.toMonoidHom).map L.subtype :=
  F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e
    (centralizer_eq_highTorusLine_sup_of_le (Or.inl rfl) hc hAT hcA)
    highTorusLine_subgroupOf_le_centralizer_perpLevi highTorusLine_subgroupOf_le_centralizer_self
    isQuasisimple_a5Levi

theorem inSubgroup_layer_inf_centralizer_highTorusLine_E6 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E6 K) (hq : 4 ≤ Nat.card K) :
    inSubgroup layer (L ⊓ centralizer
        ((((EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K)).map
          e.symm.toMonoidHom).map L.subtype : Set G)) =
      ((a5Levi K).map e.symm.toMonoidHom).map L.subtype := by
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  exact inSubgroup_layer_inf_centralizer_split_E6 e hc le_rfl
    (Subgroup.mem_subgroupOf.2 (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c))

theorem inSubgroup_layer_inf_centralizer_highRootSL2_E6 {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .E6 K) (hq : 4 ≤ Nat.card K) :
    inSubgroup layer (L ⊓ centralizer
        ((((EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K)).map
          e.symm.toMonoidHom).map L.subtype : Set G)) =
      ((a5Levi K).map e.symm.toMonoidHom).map L.subtype := by
  have hcen : centralizer (((EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) :
      Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) = ⊥ ⊔ a5Levi K := by
    rw [bot_sup_eq]
    exact EPilot.centralizer_highRootSL2_subgroupOf (Or.inl rfl) hq
  exact F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hcen bot_le bot_le
    isQuasisimple_a5Levi

end CFSG.SeitzReduction.E6Pilot
