module

public import CFSG.GH74.Generic.S1.TLeafA
public import CFSG.GH74.Generic.S45.PumpC1

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan CFSG.LocalCores

@[expose] def S1NbrCompHighAt {G : Type} [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  S1LargeModel K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
    S1Frame x K u hu → S1SymFrame x u →
      ∀ c ∈ symJ (symX x u) 3, orderOf c = 2 → (∀ a ∈ symJ (symX x u) 3, a * c = c * a) →
        (S45.barSub c (symJ (symX x u) 0 ⊔ symJ (symX x u) 1)).IsSubnormal →
          ((symJ (symX x u) 0 ⊔ symJ (symX x u) 1).subgroupOf (centralizer ({c} : Set G))).IsSubnormal

@[expose] def S1NbrComp3At {G : Type} [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)), S1Frame x K u hu →
    ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 →
      S1SymFrameLin x u F → S1FrameOddFree x u →
        ∀ c ∈ symJ3 (symX x u) 3, orderOf c = 2 → (∀ a ∈ symJ3 (symX x u) 3, a * c = c * a) →
          (S45.barSub c (symJ3 (symX x u) 0 ⊔ symJ3 (symX x u) 1)).IsSubnormal →
            ((symJ3 (symX x u) 0 ⊔ symJ3 (symX x u) 1).subgroupOf (centralizer ({c} : Set G))).IsSubnormal

@[expose] def B_S1_nbrCompHigh : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → S1Front G x K → S1NbrCompHighAt x K

@[expose] def B_S1_nbrComp3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → S1Front G x K → S1NbrComp3At x K

section Transition

variable {G : Type} [Group G] [Finite G]

theorem s1_Lxy_data_high (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hfront : S1Front G x K) (hbigK : S1LargeModel K) {u : Fin 4 → G}
    {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu) (hsym : S1SymFrame x u)
    {c : G} (hcJ : c ∈ symJ (symX x u) 3) :
    symJ (symX x u) 0 ⊔ symJ (symX x u) 1 ≤ centralizer ({c} : Set G) ∧
      IsQuasisimple ↥(symJ (symX x u) 0 ⊔ symJ (symX x u) 1) := by
  have hcomm := symJ_comm_high hExact hset hfront hbigK hf hsym
  have hLJ := sup_comm_three hcomm
  have hLC : symJ (symX x u) 0 ⊔ symJ (symX x u) 1 ≤ centralizer ({c} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.2 (hLJ a ha c hcJ)
  refine ⟨hLC, ?_⟩
  rcases id hsym with ⟨F, _, _, hF, hlin⟩ | ⟨q, F, _, _, hF, hq, huni⟩
  · have h4 : 3 < Nat.card F := three_lt_card_of_largeModel hbigK hF (sym_model_four hfront hlin)
    have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
    obtain ⟨⟨hcomm', hpair⟩, q8, hq8, hq8J⟩ := sym_a4_lin hExact hset hf hF h4 hlin
    obtain ⟨W01, hW01⟩ := hpair 0 1 rfl
    obtain ⟨hWe, -⟩ := lin_pair_fusion h2 hW01
    obtain ⟨hWq, hWc⟩ := lin_pair_W_facts hW01
    subst hWe
    exact hWq
  · obtain ⟨p, f, hud, hqpf, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨hud.prime⟩
    have : CharP F p := hud.charP
    subst hqpf
    have hodd : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
    obtain ⟨⟨hcomm', hpair⟩, q8, hq8, hq8J⟩ := sym_a4_uni hExact hset hf hF hq huni p f hp2 rfl
    obtain ⟨W01, hW01⟩ := hpair 0 1 rfl
    obtain ⟨hWe, -⟩ := uni_pair_fusion hF hodd hW01
    obtain ⟨hWq, hWc⟩ := uni_pair_W_facts hF hodd hW01
    subst hWe
    exact hWq

end Transition

end CFSG.GH74.Generic.S1
