module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexSylow

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem prime_not_dvd_intersection_index (N D : Subgroup G) (Q : Sylow p D)
    (hQ : (Q : Subgroup D).map D.subtype ≤ N) :
    ¬ p ∣ (N ⊓ D).relIndex D := by
  have hle : (Q : Subgroup D) ≤ (N ⊓ D).subgroupOf D := by
    intro x hx
    exact ⟨hQ (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩), x.property⟩
  exact fun h => Q.not_dvd_index
    (h.trans (Subgroup.index_dvd_of_le hle))

theorem primePower_intersection_index_dvd (N D H : Subgroup G)
    (hNH : N ≤ H) (hDH : D ≤ H) (Q : Sylow p D)
    (hQ : (Q : Subgroup D).map D.subtype ≤ N)
    (hindex : ∃ e : ℕ, D.relIndex N = p ^ e) :
    D.relIndex N ∣ D.relIndex H := by
  have hcoprime : (D.relIndex N).Coprime ((N ⊓ D).relIndex D) := by
    obtain ⟨e, he⟩ := hindex
    rw [he]
    exact (Fact.out : p.Prime).coprime_pow_of_not_dvd
      (prime_not_dvd_intersection_index N D Q hQ) |>.symm
  have hmul : D.relIndex N * N.relIndex H =
      (N ⊓ D).relIndex D * D.relIndex H := by
    calc
      _ = (N ⊓ D).relIndex H := by
        simpa only [Subgroup.inf_relIndex_left] using
          Subgroup.relIndex_mul_relIndex (N ⊓ D) N H inf_le_left hNH
      _ = _ := (Subgroup.relIndex_mul_relIndex (N ⊓ D) D H inf_le_right hDH).symm
  exact hcoprime.dvd_of_dvd_mul_left
    (hmul ▸ dvd_mul_right (D.relIndex N) (N.relIndex H))

theorem supplied_sylow_in_overgroup_of_index_eq (N D H : Subgroup G)
    (hNH : N ≤ H) (hDH : D ≤ H) (Q : Sylow p D)
    (hQ : (Q : Subgroup D).map D.subtype ≤ N)
    (heq : D.relIndex N = D.relIndex H) (S : Sylow p N) :
    ∃ R : Sylow p H,
      (R : Subgroup H).map H.subtype = (S : Subgroup N).map N.subtype := by
  have hmul : D.relIndex N * N.relIndex H =
      (N ⊓ D).relIndex D * D.relIndex H := by
    calc
      _ = (N ⊓ D).relIndex H := by
        simpa only [Subgroup.inf_relIndex_left] using
          Subgroup.relIndex_mul_relIndex (N ⊓ D) N H inf_le_left hNH
      _ = _ := (Subgroup.relIndex_mul_relIndex (N ⊓ D) D H inf_le_right hDH).symm
  have hindexeq : N.relIndex H = (N ⊓ D).relIndex D := by
    apply Nat.eq_of_mul_eq_mul_left
      (show 0 < D.relIndex H from
        Nat.pos_of_ne_zero (D.subgroupOf H).index_ne_zero_of_finite)
    simpa only [heq, mul_comm] using hmul
  have hnot : ¬ p ∣ N.relIndex H := by
    rw [hindexeq]
    exact prime_not_dvd_intersection_index N D Q hQ
  let A : Subgroup H := (S : Subgroup N).map (Subgroup.inclusion hNH)
  have hmap : A.map H.subtype = (S : Subgroup N).map N.subtype := by
    change ((S : Subgroup N).map (Subgroup.inclusion hNH)).map H.subtype = _
    rw [Subgroup.map_map]
    rfl
  have hpA : IsPGroup p A := S.isPGroup'.map (Subgroup.inclusion hNH)
  have hAindex : A.index = (S : Subgroup N).index * N.relIndex H := by
    change ((S : Subgroup N).map (Subgroup.inclusion hNH)).index = _
    rw [(S : Subgroup N).index_map_of_injective (Subgroup.inclusion_injective hNH),
      Subgroup.inclusion_range]
    rfl
  have hAnot : ¬ p ∣ A.index := by
    rw [hAindex]
    exact (Fact.out : p.Prime).not_dvd_mul S.not_dvd_index hnot
  exact ⟨hpA.toSylow hAnot, by simpa using hmap⟩

theorem supplied_sylow_in_ambient_of_index_eq (N D H : Subgroup G)
    (hNH : N ≤ H) (hDH : D ≤ H) (Q : Sylow p D)
    (hQ : (Q : Subgroup D).map D.subtype ≤ N)
    (heq : D.relIndex N = D.relIndex H) (hH : ¬ p ∣ H.index)
    (S : Sylow p N) :
    ∃ R : Sylow p G,
      (R : Subgroup G) = (S : Subgroup N).map N.subtype := by
  obtain ⟨R, hR⟩ := supplied_sylow_in_overgroup_of_index_eq N D H hNH hDH Q hQ heq S
  have hpR := R.isPGroup'.map H.subtype
  have hnot : ¬ p ∣ ((R : Subgroup H).map H.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul R.not_dvd_index hH
  exact ⟨hpR.toSylow hnot, by simpa using hR⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
