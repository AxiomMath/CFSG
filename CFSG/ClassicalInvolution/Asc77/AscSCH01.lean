module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallSylowCentralCover

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open scoped commutatorElement

variable {E J : Type*} [Group E] [Group J]

theorem ker_le_comm_sub {p : ℕ} [Fact p.Prime] [Finite E] [Group.IsPerfect E] (π : E →* J)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) (Q : Subgroup E)
    (hQ : (Nat.card E).factorization p ≤ (Nat.card Q).factorization p) :
    π.ker ≤ ⁅Q, Q⁆ := by
  classical
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow p Q))
  set P₁ : Subgroup E := (Q₀ : Subgroup Q).map Q.subtype with hP₁
  have hcard1 : Nat.card P₁ = p ^ (Nat.card Q).factorization p := by
    rw [hP₁, Subgroup.card_map_of_injective Q.subtype_injective, Sylow.card_eq_multiplicity]
  have hle : (Nat.card Q).factorization p ≤ (Nat.card E).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_subgroup_dvd_card Q) p
  have hP : Nat.card P₁ = p ^ (Nat.card E).factorization p := by
    rw [hcard1, le_antisymm hle hQ]
  set P : Sylow p E := Sylow.ofCard P₁ hP with hPdef
  have hPQ : (P : Subgroup E) ≤ Q := by
    rw [hPdef, Sylow.coe_ofCard, hP₁]
    exact Subgroup.map_subtype_le _
  have hKP : π.ker ≤ (P : Subgroup E) :=
    CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow P π.ker hC hCp
  obtain ⟨C⟩ := (inferInstance : Nonempty (Sylow p π.ker))
  have hder := CFSG.ShultStronglyClosedTI.central_kernel_sylow_restriction_le_derived π hC C P
  intro x hx
  have hxP : x ∈ (P : Subgroup E) := hKP hx
  have h1 : (⟨x, hxP⟩ : (P : Subgroup E)) ∈ (π.subgroupMap (P : Subgroup E)).ker :=
    Subtype.ext (MonoidHom.mem_ker.1 hx)
  have h2 := hder h1
  have h3 : x ∈ ⁅(P : Subgroup E), (P : Subgroup E)⁆ := by
    have : (commutator (P : Subgroup E)).map (P : Subgroup E).subtype =
        ⁅(P : Subgroup E), (P : Subgroup E)⁆ := by
      rw [commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← this]
    exact ⟨_, h2, rfl⟩
  exact Subgroup.commutator_mono hPQ hPQ h3

theorem card_comap_mul_card [Finite E] (π : E →* J) (hπ : Function.Surjective π) (H : Subgroup J) :
    Nat.card (H.comap π) * Nat.card J = Nat.card E * Nat.card H := by
  have h1 := Subgroup.card_mul_index (H.comap π)
  have h2 := Subgroup.card_mul_index H
  rw [Subgroup.index_comap_of_surjective H hπ] at h1
  calc Nat.card (H.comap π) * Nat.card J = Nat.card (H.comap π) * (Nat.card H * H.index) := by
        rw [h2]
    _ = (Nat.card (H.comap π) * H.index) * Nat.card H := by ring
    _ = Nat.card E * Nat.card H := by rw [h1]

theorem factorization_comap_ge {p : ℕ} [Finite E] (π : E →* J) (hπ : Function.Surjective π)
    (H : Subgroup J) (hH : (Nat.card J).factorization p ≤ (Nat.card H).factorization p) :
    (Nat.card E).factorization p ≤ (Nat.card (H.comap π)).factorization p := by
  have hJ : Finite J := Finite.of_surjective π hπ
  have h := congrArg (fun n => n.factorization p) (card_comap_mul_card π hπ H)
  simp only [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply] at h
  omega

end CFSG.ClassicalInvolution.Asc77.SCH
