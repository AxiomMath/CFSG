module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open

theorem card_le_five_of_isElemAbelian_of_cyclic_sylow {L : Type} [Group L] [Finite L]
    (hcyc : ∀ S : Sylow 5 L, IsCyclic (S : Subgroup L)) {E : Subgroup L}
    (hE : IsElemAbelian 5 E) : Nat.card E ≤ 5 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hEp : IsPGroup 5 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 x x.2⟩
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  haveI := hcyc S
  haveI : Fintype (S : Subgroup L) := Fintype.ofFinite _
  let φ : E → {a : (S : Subgroup L) // a ^ 5 = 1} := fun e =>
    ⟨Subgroup.inclusion hES e, Subtype.ext (by simpa using hE.2 e e.2)⟩
  have hφ : Function.Injective φ := fun a b h => by
    have h1 : Subgroup.inclusion hES a = Subgroup.inclusion hES b := congrArg Subtype.val h
    exact Subgroup.inclusion_injective hES h1
  calc Nat.card E ≤ Nat.card {a : (S : Subgroup L) // a ^ 5 = 1} :=
        Nat.card_le_card_of_injective φ hφ
    _ = Fintype.card {a : (S : Subgroup L) // a ^ 5 = 1} := Nat.card_eq_fintype_card
    _ = Finset.card (Finset.univ.filter fun a : (S : Subgroup L) => a ^ 5 = 1) :=
        Fintype.card_subtype _
    _ ≤ 5 := IsCyclic.card_pow_eq_one_le (by norm_num)

theorem false_of_isElemAbelian_of_cyclic_sylow {L : Type} [Group L] [Finite L]
    (hcyc : ∀ S : Sylow 5 L, IsCyclic (S : Subgroup L)) {E : Subgroup L}
    (hE : IsElemAbelian 5 E) (hcard : 5 ^ 2 ≤ Nat.card E) : False := by
  have := card_le_five_of_isElemAbelian_of_cyclic_sylow hcyc hE
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
