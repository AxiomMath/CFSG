module

public import Certificates.Certificate441691
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem card_centerOf_eq_of_card_sylow {M : Type} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    {S T : Subgroup M} (hS : Nat.card S = p ^ (Nat.card M).factorization p)
    (hT : Nat.card T = p ^ (Nat.card M).factorization p) :
    Nat.card ↥(centerOf S) = Nat.card ↥(centerOf T) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M (Sylow.ofCard S hS) (Sylow.ofCard T hT)
  have hgsub : T = S.map (MulAut.conj g).toMonoidHom :=
    calc T = ((Sylow.ofCard T hT : Sylow p M) : Subgroup M) := rfl
      _ = ((g • Sylow.ofCard S hS : Sylow p M) : Subgroup M) := by rw [hg]
      _ = S.map (MulAut.conj g).toMonoidHom := by
        rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
        rfl
  rw [hgsub, centerOf_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective S, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem mem_of_orderOf_two_of_le_centralizer {M : Type} [Group M] [Finite M] {T : Subgroup M}
    (hT : Nat.card T = 2 ^ (Nat.card M).factorization 2) {x : M} (hx : orderOf x = 2)
    (hTx : T ≤ centralizer ({x} : Set M)) : x ∈ T := by
  let S : Sylow 2 M := Sylow.ofCard T hT
  have hxp : IsPGroup 2 (zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx, pow_one]
  have hnorm : T ≤ normalizer ((zpowers x : Subgroup M) : Set M) := by
    refine hTx.trans ?_
    have h : centralizer ({x} : Set M) = centralizer ((zpowers x : Subgroup M) : Set M) := by
      rw [zpowers_eq_closure, centralizer_closure]
    rw [h]
    exact centralizer_le_normalizer _
  have hmax : T ⊔ zpowers x = T :=
    S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' hxp hnorm) le_sup_left
  exact (le_sup_right.trans hmax.le) (mem_zpowers x)

section Cert

theorem card_centerOf_sylow_P1408 (hP : Nat.card ↥P1408 = 177408000) (T : Subgroup ↥P1408)
    (hT : Nat.card T = 2 ^ 11) : Nat.card ↥(centerOf T) = 4 := by
  have hsyl : 2 ^ (Nat.card ↥P1408).factorization 2 = 2 ^ 11 := by
    rw [hP, two_factorization_card_P1408]
  have hle : HaradaModel.wordSubgroup HaradaModel.sWords ≤ P1408 :=
    HaradaModel.wordSubgroup_le _
  have hS₀ : Nat.card ↥((HaradaModel.wordSubgroup HaradaModel.sWords).subgroupOf P1408) =
      2 ^ 11 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, Certificates.certificate441691.card_S]
  rw [← card_centerOf_eq_of_card_sylow (p := 2) (by rw [hS₀, hsyl]) (by rw [hT, hsyl])
    (S := (HaradaModel.wordSubgroup HaradaModel.sWords).subgroupOf P1408) (T := T)]
  rw [← Subgroup.card_map_of_injective (f := P1408.subtype) P1408.subtype_injective,
    ← centerOf_map_of_injective P1408.subtype_injective, map_subgroupOf_eq_of_le hle]
  exact Certificates.certificate441691

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
