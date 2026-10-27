module

public import CFSG.GH74.Generic.S1.RNormalizer

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.Generic

@[expose] def S1FrameOddFree {G : Type} [Group G] (x : G) (u : Fin 4 → G) : Prop :=
  ∀ e : Fin 5, pPrimeCore 2 ↥(centralizer ({symX x u e} : Set G)) = ⊥

@[expose] def S1NbhdQ3Lin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 →
        S1SymFrameLin x u F → ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J

@[expose] def S1NbhdQ3Bad : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 →
        S1SymFrameLin x u F → ¬ S1FrameOddFree x u → ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J

@[expose] def S1NbhdQ3Good : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 →
        S1SymFrameLin x u F → S1FrameOddFree x u → ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J

theorem s1NbhdQ3Lin_of_cases (hBad : S1NbhdQ3Bad) (hGood : S1NbhdQ3Good) : S1NbhdQ3Lin := by
  intro G _ _ x K hset hfront u hu hf F hFld hFin h3 hlin
  by_cases hodd : S1FrameOddFree x u
  · exact hGood G x K hset hfront u hu hf F hFld hFin h3 hlin hodd
  · exact hBad G x K hset hfront u hu hf F hFld hFin h3 hlin hodd

variable {G : Type} [Group G] [Finite G]

theorem s1NbhdSym_of_yclause_lin (hExact : S1LiftExactProp) (hY : S1NormalizerYClause)
    (hQ3 : S1NbhdQ3Lin) : S1NbhdSym := by
  intro G _ _ x K hset hfront u hu hf hsym
  rcases id hsym with ⟨F, _, _, hF, hlin⟩ | ⟨q, F, _, _, hF, hq, huni⟩
  · by_cases h3 : Nat.card F = 3
    · exact hQ3 G x K hset hfront u hu hf F inferInstance inferInstance h3 hlin
    · have h4 : 3 < Nat.card F := by
        have hpos : 0 < Nat.card F := Nat.card_pos
        omega
      exact s1Nbhd_lin_of_yclause hExact hY hset hfront hf hsym hF h4 hlin (linBlockOps hF h4)
        (fun a b c hab hac hbc => lin_std hF h4 a b c hab hac hbc) (lin_chain hF h4)
        (lin_blk_center hF h4)
  · obtain ⟨p, f, hud, hqpf, -⟩ := FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨hud.prime⟩
    have : CharP F p := hud.charP
    exact s1Nbhd_uni_of_yclause hExact hY hset hfront hf hsym hF hq huni (uniBlockOps hF hq) p f
      hqpf (fun a b c hab hac hbc => uni_std hF hq hqpf a b c hab hac hbc) (uni_chain hF hq hqpf)
      (uni_blk_center hF hq)

end CFSG.GH74.Generic.S1
