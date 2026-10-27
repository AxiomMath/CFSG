module

public import CFSG.GH74.GLS.Stage2.Local.P34NS12Grp
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34NS

open Subgroup CFSG CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normal_subgroupOf_of_conj {N X : Subgroup G} (hX : ∀ n ∈ N, ∀ j ∈ X, n * j * n⁻¹ ∈ X) :
    (X.subgroupOf N).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hX g g.2 n hn⟩

omit [Finite G] in
theorem le_oPrimeResidualOf_of_isPGroup {N T : Subgroup G} (hTN : T ≤ N) (hT : IsPGroup 2 ↥T) :
    T ≤ oPrimeResidualOf 2 N := by
  intro t ht
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  refine ⟨⟨t, hTN ht⟩, Subgroup.subset_closure ⟨k, ?_⟩, rfl⟩
  apply Subtype.ext
  have := congrArg (fun u : ↥T => (u : G)) hk
  simpa using this

theorem not_two_dvd_relIndex_oPrimeResidual_sup {N O : Subgroup G} :
    ¬ 2 ∣ (oPrimeResidualOf 2 N ⊔ O).relIndex N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 N
  obtain ⟨hTN, hT2, hTodd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 hT₀
  have hle : T₀ ≤ oPrimeResidualOf 2 N ⊔ O := le_sup_of_le_left (le_oPrimeResidualOf_of_isPGroup hTN hT2)
  exact fun h => hTodd (h.trans (Subgroup.relIndex_dvd_of_le_left N hle))

theorem perfect_le_of_structure {N J O R T : Subgroup G} (hJN : J ≤ N) (hON : O ≤ N) (hRN : R ≤ N)
    (hJn : ∀ n ∈ N, ∀ j ∈ J, n * j * n⁻¹ ∈ J)
    (hOn : ∀ n ∈ N, ∀ o ∈ O, n * o * n⁻¹ ∈ O) (hRn : ∀ n ∈ N, ∀ r ∈ R, n * r * n⁻¹ ∈ R)
    (hOodd : Odd (Nat.card ↥O)) (hT : Group.IsSolvable ↥T) (hTN : T ≤ N)
    (hodd : ¬ 2 ∣ (R ⊔ O).relIndex N) (hf : R ⊔ O ≤ O ⊔ J ⊔ T) {P : Subgroup G} (hPN : P ≤ N)
    (hperf : ⁅P, P⁆ = P) : P ≤ J := by
  have hJ' : (J.subgroupOf N).Normal := normal_subgroupOf_of_conj hJn
  have hO' : (O.subgroupOf N).Normal := normal_subgroupOf_of_conj hOn
  have hR' : (R.subgroupOf N).Normal := normal_subgroupOf_of_conj hRn
  have hf' : R.subgroupOf N ⊔ O.subgroupOf N ≤ (O.subgroupOf N ⊔ J.subgroupOf N) ⊔ T.subgroupOf N := by
    rw [← Subgroup.subgroupOf_sup hRN hON, ← Subgroup.subgroupOf_sup hON hJN,
      ← Subgroup.subgroupOf_sup (sup_le hON hJN) hTN]
    exact Subgroup.comap_mono hf
  have hP' : ⁅P.subgroupOf N, P.subgroupOf N⁆ = P.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPN, hperf]
  have hM : (R.subgroupOf N ⊔ O.subgroupOf N).Normal := inferInstance
  have hodd1 : Odd (Nat.card (↥N ⧸ (R.subgroupOf N ⊔ O.subgroupOf N))) := by
    rw [← Subgroup.index_eq_card, ← Subgroup.subgroupOf_sup hRN hON]
    exact Nat.odd_iff.2 (by
      have := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
      exact Nat.coprime_two_left.1 this |> Nat.odd_iff.1)
  have h1 : P.subgroupOf N ≤ R.subgroupOf N ⊔ O.subgroupOf N :=
    perfect_le_of_odd_quot hodd1 hP'
  have hsolT : Group.IsSolvable ↥(T.subgroupOf N) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hTN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hTN).symm.surjective
  have h2 : P.subgroupOf N ≤ O.subgroupOf N ⊔ J.subgroupOf N :=
    perfect_le_of_sup (K := O.subgroupOf N ⊔ J.subgroupOf N) hsolT hP' (h1.trans hf')
  have hsolO : Group.IsSolvable ↥(O.subgroupOf N) := by
    have : Odd (Nat.card ↥(O.subgroupOf N)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hON).toEquiv]; exact hOodd
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ this
  have h3 : P.subgroupOf N ≤ J.subgroupOf N := by
    have h2' : P.subgroupOf N ≤ J.subgroupOf N ⊔ O.subgroupOf N := by rw [sup_comm]; exact h2
    exact perfect_le_of_sup (K := J.subgroupOf N) hsolO hP' h2'
  intro g hg
  have := h3 (Subgroup.mem_subgroupOf.2 hg : (⟨g, hPN hg⟩ : ↥N) ∈ P.subgroupOf N)
  exact Subgroup.mem_subgroupOf.1 this

end CFSG.GH74.GLS.Stage2.Local.P34NS
