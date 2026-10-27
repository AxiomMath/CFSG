module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Sub

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.GH74.Uniqueness.SU.SU5

variable {Q : Type} [Group Q]

theorem perfect_top_of_commutator_eq (X : Subgroup Q) (h : ⁅X, X⁆ = X) :
    ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = ⊤ := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map X.subtype, Subgroup.range_subtype, h]

theorem card_centralizer_subtype_eq (X : Subgroup Q) {c : Q} (hc : c ∈ X)
    (hcX : centralizer ({c} : Set Q) ≤ X) :
    Nat.card ↥(centralizer ({(⟨c, hc⟩ : ↥X)} : Set ↥X)) =
      Nat.card ↥(centralizer ({c} : Set Q)) := by
  have hmap := map_subtype_centralizer_singleton X (⟨c, hc⟩ : ↥X)
  rw [inf_eq_left.mpr hcX] at hmap
  have hmap' : (centralizer ({(⟨c, hc⟩ : ↥X)} : Set ↥X)).map X.subtype =
      centralizer ({c} : Set Q) := by simpa using hmap
  rw [← hmap', Subgroup.card_map_of_injective (f := X.subtype) X.subtype_injective]

theorem exists_sylow_isA8Type [Finite Q]
    (hmax : ∀ R : Subgroup Q, IsPGroup 2 R → Nat.card R ≤ 64)
    {X P : Subgroup Q} (hPX : P ≤ X) (hP2 : IsPGroup 2 P) (hPcard : Nat.card P = 64)
    (hPA8 : IsA8Type ↥P) : ∃ S : Sylow 2 ↥X, IsA8Type ↥(S : Subgroup ↥X) := by
  have hP'2 : IsPGroup 2 (P.subgroupOf X) :=
    hP2.comap_of_injective X.subtype X.subtype_injective
  have hP'card : Nat.card (P.subgroupOf X) = 64 := by
    rw [card_subgroupOf_of_le X hPX, hPcard]
  obtain ⟨S, hS⟩ := hP'2.exists_le_sylow
  refine ⟨S, ?_⟩
  have hcard_le : Nat.card ((S : Subgroup ↥X).map X.subtype) ≤ 64 :=
    hmax _ (S.isPGroup'.map X.subtype)
  have hcard_eq : Nat.card ((S : Subgroup ↥X).map X.subtype) =
      Nat.card (S : Subgroup ↥X) :=
    Subgroup.card_map_of_injective X.subtype_injective
  have hS_le : Nat.card (S : Subgroup ↥X) ≤ 64 := hcard_eq ▸ hcard_le
  have hPS : Nat.card (P.subgroupOf X) ≤ Nat.card (S : Subgroup ↥X) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hS)
  have hcardS : Nat.card (S : Subgroup ↥X) = 64 :=
    le_antisymm hS_le (by rw [← hP'card]; exact hPS)
  have hSP : (S : Subgroup ↥X) = P.subgroupOf X :=
    (Subgroup.eq_of_le_of_card_ge hS (by simp [hcardS, hP'card])).symm
  rw [hSP]
  exact isA8Type_subgroupOf X hPX hPA8

theorem conj_centralizer_data {x c : Q} (hxc : IsConj x c) {M : Subgroup Q}
    (hMC : M ≤ centralizer ({x} : Set Q)) (hMp : ⁅M, M⁆ = M) (hM : Nat.card M = 60)
    (hC : Nat.card ↥(centralizer ({x} : Set Q)) = 480) :
    ∃ M' : Subgroup Q, M' ≤ centralizer ({c} : Set Q) ∧ ⁅M', M'⁆ = M' ∧ Nat.card M' = 60 ∧
      Nat.card ↥(centralizer ({c} : Set Q)) = 480 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxc
  have hcent : (centralizer ({x} : Set Q)).map (MulAut.conj g) = centralizer ({c} : Set Q) := by
    refine le_antisymm ?_ ?_
    · refine (Subgroup.map_centralizer_le_centralizer_image ({x} : Set Q)
        ((MulAut.conj g) : Q →* Q)).trans ?_
      rw [Set.image_singleton]
      change centralizer ({MulAut.conj g x} : Set Q) ≤ centralizer {c}
      rw [MulAut.conj_apply, hg]
    · rintro y hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      rw [Subgroup.mem_map]
      refine ⟨(MulAut.conj g).symm y, ?_, (MulAut.conj g).apply_symm_apply y⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply (MulAut.conj g).injective
      simp only [MulEquiv.map_mul, MulEquiv.apply_symm_apply]
      rw [MulAut.conj_apply, hg]
      exact hy
  refine ⟨M.map (MulAut.conj g), ?_, ?_, ?_, ?_⟩
  · rw [← hcent]
    exact Subgroup.map_mono hMC
  · rw [← Subgroup.map_commutator, hMp]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hM]
  · rw [← hcent, Subgroup.card_map_of_injective (MulAut.conj g).injective, hC]

end CFSG.EvenSporadicStandard.HNRecog.Harada
