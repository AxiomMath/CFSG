module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FRee
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel
public import CFSG.LieType.BorelTits.AllModels
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenAct

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Ree
open CFSG.AGLEmbedding


theorem borelTitsConcl_ree {Y : Type} [Group Y] {f : ℕ} (hm : LieModel Y .twistedG2 0 3 f) :
    BorelTitsConcl 3 Y := by
  intro U hU hUp
  obtain ⟨S, P, hP, hN, -, -, hNS, -⟩ :=
    CFSG.LieType.BorelTits.lieModel_conclusion Y .twistedG2 0 3 f hm U hU hUp
  exact ⟨S, P, hP, hN, hNS (by decide)⟩


theorem ree_normalizer_isCoatom_even {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (hm : ReeTitsModel Y .twistedG2 3 f) (S : Sylow 3 Y) :
    IsCoatom (normalizer ((S : Subgroup Y) : Set Y)) ∧
      Even (normalizer ((S : Subgroup Y) : Set Y)).index := by
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.ree_model_data_pos hm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨P, hP⟩, hNU, hco, -⟩ := ReeModel.std_facts hK
  obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq e S P
  have h1 : (normalizer ((S : Subgroup Y) : Set Y)).map e'.toMonoidHom = ReeModel.stdB a K := by
    rw [Subgroup.map_equiv_normalizer_eq, he', hP, hNU]
  have h2 : normalizer ((S : Subgroup Y) : Set Y) = (ReeModel.stdB a K).comap e'.toMonoidHom := by
    rw [← h1, Subgroup.comap_map_eq_self_of_injective e'.injective]
  refine ⟨h2 ▸ (Subgroup.isCoatom_comap e').2 hco, ?_⟩
  rw [h2, Subgroup.index_comap_of_surjective _ e'.surjective]
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, -, -, hcardΩ, -⟩ :=
    small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  have hq : Odd (3 ^ (2 * a + 1)) := (by decide : Odd 3).pow
  have hidx : (ReeModel.stdB a K).index = (3 ^ (2 * a + 1)) ^ 3 + 1 := hcardΩ
  rw [hidx]
  exact (hq.pow).add_one

theorem evenParabolics_ree {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hf : 1 ≤ f)
    (hm : LieModel Y .twistedG2 0 3 f) : EvenParabolics 3 Y := by
  obtain ⟨f', hR⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.reeTitsModel_of_FRee (Y := Y) ⟨f, hf, hm⟩
  intro S M hSM hM
  obtain ⟨hco, hev⟩ := ree_normalizer_isCoatom_even hR S
  have hMeq : M = normalizer ((S : Subgroup Y) : Set Y) := (hco.le_iff.1 hSM).resolve_left hM
  rw [hMeq]
  exact hev

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
