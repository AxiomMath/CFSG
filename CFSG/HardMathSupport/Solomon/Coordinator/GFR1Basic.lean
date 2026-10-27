module

public import CFSG.HardMathSupport.Solomon.Coordinator.GapFinalDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Layer

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem gfr1_isHatSix_of_equiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : IsHatSix X) : IsHatSix X' := by
  obtain ⟨hc, hz, ⟨f⟩⟩ := h
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' := Subgroup.map_center_eq e
  refine ⟨?_, ?_, ⟨?_⟩⟩
  · have h1 := Subgroup.map_commutator (f := e.toMonoidHom) (⊤ : Subgroup X) ⊤
    have e1 : (⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X) = ⊤ := hc
    rw [e1, Subgroup.map_top_of_surjective _ e.surjective] at h1
    exact h1.symm
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hz]
  · exact (QuotientGroup.congr _ _ e hcen).symm.trans f

theorem gfr1_isHatON_of_equiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : IsHatON X) : IsHatON X' := by
  obtain ⟨hc, hz, ⟨f⟩⟩ := h
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' := Subgroup.map_center_eq e
  refine ⟨?_, ?_, ⟨?_⟩⟩
  · have h1 := Subgroup.map_commutator (f := e.toMonoidHom) (⊤ : Subgroup X) ⊤
    have e1 : (⁅(⊤ : Subgroup X), ⊤⁆ : Subgroup X) = ⊤ := hc
    rw [e1, Subgroup.map_top_of_surjective _ e.surjective] at h1
    exact h1.symm
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hz]
  · exact (QuotientGroup.congr _ _ e hcen).symm.trans f

theorem gfr1_component_ne_bot {G : Type} [Group G] [Finite G] {p : ℕ} {X J : Subgroup G}
    (hJ : GLAPComponent p X J) : J ≠ ⊥ := by
  intro hbot
  obtain ⟨-, -, ⟨-, -, hq⟩, -⟩ := hJ
  obtain ⟨-, hs⟩ := hq
  have : Subsingleton ↥(barX p X J) := by
    rw [barX, hbot, Subgroup.bot_subgroupOf, Subgroup.map_bot]
    infer_instance
  have h2 : Subsingleton (↥(barX p X J) ⧸ Subgroup.center ↥(barX p X J)) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a b]
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  exact hab (h2.elim a b)

theorem gfr1_eq_of_subnormal {G : Type} [Group G] {K J : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥K) (_hJK : J ≤ K) (hsn : IsSubnormal J K)
    (hperf : ⁅J, J⁆ = J) (hne : J ≠ ⊥) : J = K := by
  by_contra hJne
  obtain ⟨N, hJN, hNK, hNne, hNn, -⟩ := isSubnormal_exists_normal hsn hJne
  have := hNn
  rcases on25_normal_le_center_or_top hq (N.subgroupOf K) with hc | htop
  · apply hne
    have hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
      intro x hx y hy
      have := Subgroup.mem_center_iff.1 (hc (show (⟨y, hNK hy⟩ : ↥K) ∈ N.subgroupOf K from hy))
        ⟨x, hNK hx⟩
      exact congrArg Subtype.val this
    have h1 : ⁅J, J⁆ ≤ ⊥ := by
      refine Subgroup.commutator_le.2 fun x hx y hy => ?_
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hab x (hJN hx) y (hJN hy))
    rw [← hperf]
    exact le_bot_iff.1 h1
  · apply hNne
    refine le_antisymm hNK fun x hx => ?_
    have : (⟨x, hx⟩ : ↥K) ∈ N.subgroupOf K := by rw [htop]; trivial
    exact this

end CFSG.HardMathSupport.Solomon.Coordinator
