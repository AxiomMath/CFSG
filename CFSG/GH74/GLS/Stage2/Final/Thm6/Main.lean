module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.Prop201
public import CFSG.GH74.GLS.Stage2.Final.Thm6.DerOddCore
public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundMain

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
  CFSG.GH74.GLS.Stage2.Final
open scoped commutatorElement

section Easy

variable {G : Type} [Group G]

theorem pPrimeCoreOf_eq_bot_iff' (X : Subgroup G) : pPrimeCoreOf 2 X = ⊥ ↔ pPrimeCore 2 ↥X = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective (pPrimeCore 2 ↥X) X.subtype_injective

theorem oddCore_eq_bot_iff {z : G} : OddCore z = ⊥ ↔ pPrimeCore 2 ↥(Cen z) = ⊥ :=
  pPrimeCoreOf_eq_bot_iff' (Cen z)

end Easy

section Final

theorem oddCoreOverC_of_prop201 (h4 : Ch4Thm4) (h : Prop201) : OddCoreOverC := by
  intro G _ _ z k S hctx M hM hev hne
  have hC : Ctx17 G z k S M := ⟨hctx, hM, hev⟩
  have h4M := h4 G z k S hctx M hM hev
  by_cases hk : k = Kind.m12
  · subst hk
    by_contra hMC
    have hlt : Cen z < M := lt_of_le_of_ne hM.2 (fun e => hMC e.symm)
    rcases (h4M.2.1 hlt).1 with h1 | ⟨ε, h1⟩ <;> cases h1
  · rcases h G z k S M ⟨hC, h4M⟩ hk with h0 | ⟨ε, q, -, hMC, -⟩
    · exact absurd h0 hne
    · exact hMC

theorem oddCore_bot_or_conc
    (hex : ExistsEvenFStar) (h4 : Ch4Thm4) (h34 : Leaf_Prop34) (L : Thm6Leaves)
    {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G} (hctx : Stage2Ctx G z k S)
    (hk : k ≠ Kind.m12) : OddCore z = ⊥ ∨ Conc201 z k S (Cen z) := by
  obtain ⟨M, hM, hev⟩ := hex G z k S hctx
  have h20 : Ctx20 G z k S M := ⟨⟨hctx, hM, hev⟩, h4 G z k S hctx M hM hev⟩
  rcases prop201_of_leaves L G z k S M h20 hk with h0 | hconc
  · left
    by_cases hMC : M = Cen z
    · subst hMC
      exact h0
    · have hlt : Cen z < M := lt_of_le_of_ne hM.2 (fun e => hMC e.symm)
      exact le_bot_iff.mp (h0 ▸ oddCoreLeM_of h34 G z k S M h20 hlt)
  · right
    obtain ⟨ε, q, hT, hMC, hrest⟩ := hconc
    subst hMC
    exact ⟨ε, q, hT, rfl, hrest⟩

theorem thm6
    (hex : ExistsEvenFStar) (h4 : Ch4Thm4) (h34 : Leaf_Prop34) (L : Thm6Leaves) :
    Thm6OddCore ∧ Thm6OddCoreL4 := by
  refine ⟨?_, ?_⟩
  · intro G _ _ z k S hctx hk'
    by_cases hm : k = Kind.m12
    · subst hm
      exact stage2OddCoreM12_of_thm4 hex h4 G z S hctx
    · rcases oddCore_bot_or_conc hex h4 h34 L hctx hm with h0 | ⟨ε, q, ⟨hk, -⟩, -⟩
      · exact oddCore_eq_bot_iff.mp h0
      · exact absurd hk (hk' ε)
  · intro G _ _ z S ε q L₁ L₂ hctx hq
    have hm : Kind.l4 ε ≠ Kind.m12 := fun e => by cases e
    rcases oddCore_bot_or_conc hex h4 h34 L hctx hm with h0 | hconc
    · rw [oddCore_eq_bot_iff.mp h0]
      exact ⟨inferInstance, by simp⟩
    · obtain ⟨ε', q', ⟨hk', L₁', L₂', hq'⟩, -, K₁, K₂, hcp, h1, h2, hcyc, t, htc, htS, htN, hdvd, hiff⟩ :=
        hconc
      have hεε : ε = ε' := Kind.l4.inj hk'
      subst hεε
      have hqq : q = q' := stage1L4_q_eq hq hq'
      subst hqq
      have hb := sl2OddCentBound_thm G z S ε q hctx ⟨rfl, L₁', L₂', hq'⟩ K₁ K₂ hcp h1 h2 t htc htS htN hiff
      have hcard : Nat.card ↥(pPrimeCoreOf 2 (Cen z)) = Nat.card ↥(pPrimeCore 2 ↥(Cen z)) :=
        Subgroup.card_map_of_injective (Cen z).subtype_injective
      refine ⟨?_, ?_⟩
      · have : IsCyclic ↥((pPrimeCore 2 ↥(Cen z)).map (Cen z).subtype) := hcyc
        let e := Subgroup.equivMapOfInjective (pPrimeCore 2 ↥(Cen z)) (Cen z).subtype
          (Cen z).subtype_injective
        exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
      · rw [← hcard]
        exact hdvd.trans hb

end Final

end CFSG.GH74.GLS.Stage2.Final.Thm6
