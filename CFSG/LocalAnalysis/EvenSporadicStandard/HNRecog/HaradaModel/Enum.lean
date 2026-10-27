module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.EnumCount

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem ncard_filter_of_isEnumSet {n : ℕ} {E : Array Table} {S : Set (Equiv.Perm (Fin n))}
    (h : IsEnumSet n E S) (hsize : E.size = S.ncard) (b : Table → Bool)
    (Q : Equiv.Perm (Fin n) → Prop)
    (hb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g → (b x = true ↔ Q g)) :
    {g : Equiv.Perm (Fin n) | g ∈ S ∧ Q g}.ncard = (E.filter b).size :=
  h.ncard_filter hsize b Q hb

theorem isEnumSet_filter {n : ℕ} {E : Array Table} {S : Set (Equiv.Perm (Fin n))}
    (h : IsEnumSet n E S) (b : Table → Bool) (Q : Equiv.Perm (Fin n) → Prop)
    (hb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g → (b x = true ↔ Q g)) :
    IsEnumSet n (E.filter b) {g : Equiv.Perm (Fin n) | g ∈ S ∧ Q g} :=
  h.filter b Q hb

theorem preservesHalves_iff {T : Table} {g : Equiv.Perm (Fin 1408)} (h : Rep 1408 T g) :
    preservesHalves T = true ↔ g ∈ blocks1408 := by
  refine ⟨mem_blocks1408_of_preservesHalves h, fun hg => ?_⟩
  simp only [preservesHalves, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  intro k hk
  have hgi : ∀ i (hi : i < 1408), ap T i = (g ⟨i, hi⟩).val := fun i hi => by
    rw [h i hi, idx_of_lt g hi, Equiv.Perm.smul_def]
  refine ⟨?_, ?_⟩
  · rw [hgi k (by omega)]
    exact (hg ⟨k, by omega⟩).2 hk
  · rw [hgi (704 + k) (by omega)]
    by_contra hlt
    have h1 := (hg ⟨704 + k, by omega⟩).1 (by omega)
    simp only at h1
    omega

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
