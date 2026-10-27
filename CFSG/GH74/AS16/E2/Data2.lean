module

public import CFSG.GH74.AS16.E2.Small
public import CFSG.GH74.AS16.E2.Data

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint
open CFSG.GH74.E2 hiding Hyp

@[expose] def InnerAction {G : Type*} [Group G] (T L : Subgroup G) : Prop :=
  ∀ t ∈ T, ∃ l ∈ L, ∀ x ∈ L, t * x * t⁻¹ = l * x * l⁻¹

structure SmallData (P : (K : Type) → [Group K] → Prop) : Prop where
  sylow : ∀ (K : Type) [Group K] [Finite K], P K → ∀ Q : Subgroup K, IsPGroup 2 Q →
    ¬ 2 ∣ Q.index → SmallTable (⊤ : Subgroup K) Q

@[expose] def OutTrivial (P : (K : Type) → [Group K] → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], P K → ∀ φ : MulAut K, ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹

section Cfg

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem Cfg.decomp_of_inner (h : Cfg G T z L) (hZ : center ↥L = ⊥)
    (hinn : InnerAction (T : Subgroup G) L) :
    ∀ t ∈ (T : Subgroup G), ∃ s ∈ (T : Subgroup G) ⊓ L,
      ∃ c ∈ (T : Subgroup G) ⊓ centralizer (L : Set G), t = s * c :=
  exists_decomp_of_inner T.isPGroup' (center_trivial' hZ)
    (fun _ hP hPL hle => h.isSylowOf_inf.eq_of_le hle hPL hP) hinn

theorem Cfg.innerAction_of_out (h : Cfg G T z L)
    (hout : ∀ φ : MulAut ↥L, ∃ k : ↥L, ∀ x : ↥L, φ x = k * x * k⁻¹) :
    InnerAction (T : Subgroup G) L := by
  intro t ht
  have htN := h.le_normalizer ht
  obtain ⟨k, hk⟩ := hout (L.normalizerMonoidHom ⟨t, htN⟩)
  exact ⟨(k : G), k.2, fun x hx => congrArg Subtype.val (hk ⟨x, hx⟩)⟩

theorem Cfg.smallTable (h : Cfg G T z L) {P : (K : Type) → [Group K] → Prop} (hS : SmallData P)
    (hP : P ↥L) : SmallTable L ((T : Subgroup G) ⊓ L) := by
  have hsyl := h.isSylowOf_inf
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hsyl
  have h1 := SmallTable.of_subtype L _ (hS.sylow ↥L hP
    (((T : Subgroup G) ⊓ L).subgroupOf L) hsyl.2.1.comap_subtype hsyl.2.2)
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right] at h1
  exact h1

theorem Cfg.false_of_smallTable (h : Cfg G T z L) (hZ : center ↥L = ⊥)
    (hinn : InnerAction (T : Subgroup G) L)
    (hcyc : IsCyclic ↥((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (hB : SmallTable L ((T : Subgroup G) ⊓ L)) : False :=
  CFSG.GH74.AS16.E2.false_of_small h.hyp.simple h.hyp.nonabelian h.pair.orderOf_eq
    h.pair.mem_sylow h.pair.central
    (fun _ hl => Subgroup.mem_centralizer_singleton_iff.1 (h.pair.isComp.1 hl))
    (h.decomp_of_inner hZ hinn) (center_trivial hZ) hcyc hB

end Cfg

theorem noPairM11_of_cyclic (hD3 : K0Data3) (hS : SmallData ShapeM11) (hO : OutTrivial ShapeM11)
    {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (hcfg : Cfg G T z L) (hsh : ShapeM11 ↥L)
    (hcyc : IsCyclic ↥((T : Subgroup G) ⊓ centralizer (L : Set G))) : False := by
  have hZ : center ↥L = ⊥ :=
    hD3.center_bot ↥L (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hsh)))))
  exact hcfg.false_of_smallTable hZ (hcfg.innerAction_of_out (hO ↥L hsh)) hcyc (hcfg.smallTable hS hsh)

theorem noPairL33_of_cyclic_inner (hD3 : K0Data3) (hS : SmallData ShapeL33)
    {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (hcfg : Cfg G T z L) (hsh : ShapeL33 ↥L) (hinn : InnerAction (T : Subgroup G) L)
    (hcyc : IsCyclic ↥((T : Subgroup G) ⊓ centralizer (L : Set G))) : False := by
  have hZ : center ↥L = ⊥ :=
    hD3.center_bot ↥L (Or.inr (Or.inr (Or.inr (Or.inl hsh))))
  exact hcfg.false_of_smallTable hZ hinn hcyc (hcfg.smallTable hS hsh)

theorem noPairU33_of_inner (hD3 : K0Data3) (hS : SmallData ShapeU33)
    {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (hcfg : Cfg G T z L) (hsh : ShapeU33 ↥L) (hinn : InnerAction (T : Subgroup G) L) : False := by
  have hZ : center ↥L = ⊥ :=
    hD3.center_bot ↥L (Or.inr (Or.inl hsh))
  obtain ⟨U, hU, hr⟩ := hD3.rank_ge3 ↥L (Or.inr (Or.inl hsh))
  exact hcfg.false_of_smallTable hZ hinn (hcfg.tC_cyclic hZ hU hr) (hcfg.smallTable hS hsh)

@[expose] def NoPairU33O : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (z : G) (L : Subgroup G),
    Cfg G T z L → GLS.IsTerminalPair 2 z L → ShapeU33 ↥L →
      ¬ InnerAction (T : Subgroup G) L → False

theorem noPairU33_of (hD3 : K0Data3) (hS : SmallData ShapeU33) (h : NoPairU33O) :
    NoPairOf ShapeU33 := by
  intro G _ _ T z L hcfg hterm hsh
  by_cases hc : InnerAction (T : Subgroup G) L
  · exact noPairU33_of_inner hD3 hS hcfg hsh hc
  · exact h G T z L hcfg hterm hsh hc

end CFSG.GH74.AS16.E2
