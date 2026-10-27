module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate5

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Bridge

theorem card_quot_pCore_of_core {H : Type*} [Group H] {K I : Subgroup H}
    (hcore : blockQ K = I) (hI : Nat.card ↥I = 4) (hK : Nat.card ↥K = 12) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 := by
  have h1 : Nat.card ↥(CFSG.pCore 2 ↥K) = 4 := by
    have h0 : Nat.card ↥(blockQ K) = Nat.card ↥(CFSG.pCore 2 ↥K) := by
      rw [blockQ_eq_map]
      exact Subgroup.card_map_of_injective K.subtype_injective
    rw [← h0, hcore]
    exact hI
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
  rw [hK, h1] at h2
  omega

theorem map_subtype_conj {G : Type*} [Group G] {P : Subgroup G} (t : ↥P) (X : Subgroup ↥P) :
    (X.map P.subtype).map (MulAut.conj (t : G)).toMonoidHom =
      (X.map (MulAut.conj t).toMonoidHom).map P.subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem solvableA3Family : Top.SolvableA3Family := by
  intro G _ _ S P h hsolv
  classical
  have hg := gateHyp_of_pushUpObstruction h hsolv
  have hR := reducedAction_of_pushUpObstruction h
  have hSP : S ≤ P := h.sylow.1
  have hVP : Top.reducedModule S P ≤ P := hR.reduced.1
  obtain ⟨r, I, W, F, Pm, hw, K, hpow, -, -, hK⟩ :=
    solvable_reduced_action_produces_A3_family (charTwo_top_of_charTwo h.charTwo) hg.sylow
      hg.nonnormal hg.le_M hg.M_lt hg.M_max (noCharNormal_top_of hSP h.noCharNormal) hg.reduced
      hg.not_top_le hg.solvable
  have hf : Function.Injective P.subtype := P.subtype_injective
  have hK12 : ∀ i, Nat.card ↥(K i) = 12 := fun i => by
    obtain ⟨e⟩ := hK.alt4 i
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hK3 : ∀ i, Nat.card (↥(K i) ⧸ CFSG.pCore 2 ↥(K i)) = 3 := fun i =>
    card_quot_pCore_of_core (hK.core i) (hw.I_card i) (hK12 i)
  have hdirect : ∀ i, (K i) ⊓ (⨆ j, ⨆ (_ : j ≠ i), K j) = ⊥ := fun i =>
    disjoint_iff.mp (hK.indep i)
  have hdirect' : ∀ i, (K i).map P.subtype ⊓
      (⨆ j, ⨆ (_ : j ≠ i), (K j).map P.subtype) = ⊥ := by
    intro i
    have h1 : (⨆ j, ⨆ (_ : j ≠ i), (K j).map P.subtype) =
        (⨆ j, ⨆ (_ : j ≠ i), K j).map P.subtype := by
      rw [Subgroup.map_iSup]
      congr 1
      funext j
      rw [Subgroup.map_iSup]
    rw [h1, ← Subgroup.map_inf_eq _ _ P.subtype hf, hdirect i, Subgroup.map_bot]
  refine ⟨r, fun i => (K i).map P.subtype, ?_, fun i => ?_, hdirect'⟩
  · exact
      { pow_two := hpow
        injective := fun i j hij => by
          have h1 : K i = K j := Subgroup.map_injective hf hij
          exact hw.I_injective (((hK.core i).symm.trans (congrArg blockQ h1)).trans (hK.core j))
        le_odd := fun i => by
          rw [← oddOrderSubgroup_top_map P]
          exact Subgroup.map_mono (hK.K_le_N i)
        permuted := fun s hs i => by
          obtain ⟨j, hj⟩ := hK.permuted ⟨s, hSP hs⟩ (Subgroup.mem_subgroupOf.2 hs) i
          refine ⟨j, ?_⟩
          have := map_subtype_conj (P := P) ⟨s, hSP hs⟩ (K i)
          rw [hj] at this
          exact this
        transitive := fun i j => by
          obtain ⟨t, ht, hj⟩ := hK.transitive i j
          refine ⟨(t : G), Subgroup.mem_subgroupOf.1 ht, ?_⟩
          have := map_subtype_conj (P := P) t (K i)
          rw [hj] at this
          exact this
        chi0 := fun i => by
          have hc := hK.chi0 i
          have hshort' : IsShort2 ((K i).map P.subtype) :=
            IsShort2.map_of_injective P.subtype hf hc.1.1
          have hsub := isSubnormal_map_injective P.subtype hf hc.1.2.2
          rw [Subgroup.map_top, Subgroup.range_subtype] at hsub
          have h3 : Nat.card (↥((K i).map P.subtype) ⧸
              CFSG.pCore 2 ↥((K i).map P.subtype)) = 3 :=
            (card_quot_pCore_map_injective P.subtype hf (K i)).trans (hK3 i)
          exact ⟨⟨hshort', BlueprintB2.map_subtype_le_self _, hsub⟩,
            Or.inr (Or.inl (short_order_three_is_alternating_four hshort' h3).2.2.2.2)⟩
        commute := fun i j hij => by
          rw [← Subgroup.map_commutator, hK.commute i j hij, Subgroup.map_bot]
        odd_eq := by
          rw [← oddOrderSubgroup_top_map P, hK.N_eq, Subgroup.map_iSup]
        central := fun i => by
          rw [hdirect' i]
          exact bot_le
        perfect := fun i => by
          have hJ : (thompsonJ (S.subgroupOf P)).map P.subtype = thompsonJ S := by
            rw [← elemThompsonIn_two_eq, elemThompsonIn_subgroupOf_map_eq hSP]
          rw [← hJ, ← Subgroup.map_commutator, hK.perfect_J i]
        gen := fun i => by
          have h1 := (hK.local_i i).H_eq
          have h2 : K i ⊔ S.subgroupOf P = ⊤ := by
            have : (K i ⊔ elemBaumannIn 2 (S.subgroupOf P)) ⊔ S.subgroupOf P ≤
                K i ⊔ S.subgroupOf P :=
              sup_le (sup_le le_sup_left ((elemBaumannIn_le 2 _).trans le_sup_right)) le_sup_right
            exact top_le_iff.mp (h1 ▸ this)
          have h3 := congrArg (Subgroup.map P.subtype) h2
          rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hSP, Subgroup.map_top,
            Subgroup.range_subtype] at h3
          exact h3.symm
        u_le := fun i => by
          rw [blockU_map_injective P.subtype hf]
          have h1 : blockU (K i) ≤ (Top.reducedModule S P).subgroupOf P :=
            (C1.blockU_le_blockQ (hK.chi0 i).1.1).trans
              ((hK.core i).le.trans ((hw.I_le i).trans hw.W_le))
          have := Subgroup.map_mono (f := P.subtype) h1
          rwa [Subgroup.map_subgroupOf_eq_of_le hVP] at this }
  · obtain ⟨e⟩ := hK.alt4 i
    exact ⟨((K i).equivMapOfInjective P.subtype hf).symm.trans e⟩

end Bridge

end CFSG.QuasithinUnique.Setup.Wreath
