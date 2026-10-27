module

public import CFSG.ClassicalInvolution.Q3.TL3T21

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

structure StarHyp (Ω : Set (Subgroup G)) : Prop where
  thmD : ThmDHyp 3 Ω
  below : ThmDAbsBelow 3 (Nat.card G)
  center : Subgroup.center G = ⊥

theorem StarHyp.ofDCex {IH : ℕ → Prop} {Ω : Set (Subgroup G)} (hc : DCex 3 IH Ω)
    (hZ : Subgroup.center G = ⊥) : StarHyp Ω :=
  ⟨hc.toThmDHyp, hc.below, hZ⟩

@[expose] def compStab (Ω : Set (Subgroup G)) (K : Subgroup G) : Subgroup G where
  carrier := {g | ∀ L : Subgroup G, L ∈ dstarComp Ω K ↔ conjSub g L ∈ dstarComp Ω K}
  mul_mem' := by
    intro a b ha hb L
    rw [conjSub_mul]
    exact (hb L).trans (ha _)
  one_mem' := by
    intro L
    rw [conjSub_one]
  inv_mem' := by
    intro a ha L
    have h := ha (conjSub a⁻¹ L)
    rw [conjSub_conjSub_inv] at h
    exact h.symm

theorem mem_compStab {Ω : Set (Subgroup G)} {K : Subgroup G} {g : G} :
    g ∈ compStab Ω K ↔ ∀ L : Subgroup G, L ∈ dstarComp Ω K ↔ conjSub g L ∈ dstarComp Ω K :=
  Iff.rfl

namespace StarHyp

variable {Ω : Set (Subgroup G)} (h : StarHyp Ω)
include h

theorem mem_dstarComp_self {K : Subgroup G} (_hK : K ∈ Ω) : K ∈ dstarComp Ω K :=
  Relation.ReflTransGen.refl

theorem mem_dstarComp_comm {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ dstarComp Ω K) :
    K ∈ dstarComp Ω L :=
  (Asc77.T3.mem_dstarComp_symm hK hL).2

theorem mem_dstarComp_trans {K L M : Subgroup G} (hL : L ∈ dstarComp Ω K)
    (hM : M ∈ dstarComp Ω L) : M ∈ dstarComp Ω K :=
  Relation.ReflTransGen.trans hL hM

theorem mem_of_mem_dstarComp {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ dstarComp Ω K) :
    L ∈ Ω :=
  (Asc77.T3.mem_dstarComp_symm hK hL).1

theorem mem_dstarComp_of_commutes {L M : Subgroup G} (hL : L ∈ Ω) (hM : M ∈ Ω)
    (hc : Commutes L M) : L ∈ dstarComp Ω M := by
  by_cases hLM : L = M
  · subst hLM
    exact h.mem_dstarComp_self hL
  have hnbr : L ∈ omegaNbr Ω M := (TC.mem_omegaNbr_iff h.thmD.hyp h.thmD.two).mpr
    ⟨hL, hLM, Asc77.AscL62.le_normalizer_of_commutes hc⟩
  exact Relation.ReflTransGen.single
    ⟨hL, Or.inl (Q3T6.Mu.omegaNbr_subset_omegaStarNbr h.thmD.hyp M hnbr)⟩

theorem conjSub_mem_dstarComp {K L : Subgroup G} (_hK : K ∈ Ω) (hL : L ∈ dstarComp Ω K)
    (g : G) : conjSub g L ∈ dstarComp Ω (conjSub g K) :=
  dstarComp_conj h.thmD.hyp.conjInvariant hL g

theorem mem_compStab_iff {K : Subgroup G} (hK : K ∈ Ω) {g : G} :
    g ∈ compStab Ω K ↔ conjSub g K ∈ dstarComp Ω K := by
  refine ⟨fun hg => (mem_compStab.mp hg K).mp (h.mem_dstarComp_self hK), fun hgK L => ?_⟩
  refine ⟨fun hL => h.mem_dstarComp_trans hgK (h.conjSub_mem_dstarComp hK hL g), fun hL => ?_⟩
  have hKg := h.mem_dstarComp_trans (h.mem_dstarComp_comm hK hgK) hL
  have h1 := h.conjSub_mem_dstarComp (h.thmD.hyp.conjInvariant g K hK) hKg g⁻¹
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h1

end StarHyp

end CFSG.ClassicalInvolution.Q3.Sec13
