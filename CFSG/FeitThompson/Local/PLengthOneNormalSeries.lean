module

public import CFSG.FeitThompson.Definitions.ConventionForPLengthAtMostOne

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p : ℕ} {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem natCard_quotient_subgroupOf (D T : Subgroup X) :
    Nat.card (↥T ⧸ D.subgroupOf T) = D.relIndex T := (Subgroup.index_eq_card _).symm

omit [Finite X] in
theorem relIndex_comap_mk' (N : Subgroup X) [N.Normal] (S : Subgroup (X ⧸ N)) :
    N.relIndex (S.comap (QuotientGroup.mk' N)) = Nat.card S := by
  have h := Subgroup.relIndex_ker (S.comap (QuotientGroup.mk' N)) (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk',
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)] at h
  exact h

def pComplPCore (p : ℕ) (X : Type*) [Group X] [Finite X] : Subgroup X :=
  (pCore p (X ⧸ pComplCore p X)).comap (QuotientGroup.mk' (pComplCore p X))

theorem pComplPCore_eq_comap (p : ℕ) (X : Type*) [Group X] [Finite X] :
    pComplPCore p X
      = (pCore p (X ⧸ pComplCore p X)).comap (QuotientGroup.mk' (pComplCore p X)) := (rfl)

theorem mem_pComplPCore_iff {x : X} :
    x ∈ pComplPCore p X ↔ (x : X ⧸ pComplCore p X) ∈ pCore p (X ⧸ pComplCore p X) := by
  rw [pComplPCore_eq_comap]; exact Iff.rfl

instance pComplPCore_normal (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (pComplPCore p X).Normal := by
  rw [pComplPCore_eq_comap]
  exact Subgroup.Normal.comap (Subgroup.normal_of_characteristic _) _

theorem pComplCore_le_pComplPCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    pComplCore p X ≤ pComplPCore p X := by
  intro x hx
  rw [mem_pComplPCore_iff, (QuotientGroup.eq_one_iff x).2 hx]
  exact one_mem _

theorem map_mk'_pComplPCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (pComplPCore p X).map (QuotientGroup.mk' (pComplCore p X))
      = pCore p (X ⧸ pComplCore p X) := by
  rw [pComplPCore_eq_comap]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem index_pComplPCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (pComplPCore p X).index = (pCore p (X ⧸ pComplCore p X)).index := by
  rw [pComplPCore_eq_comap]
  exact Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem relIndex_pComplCore_pComplPCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (pComplCore p X).relIndex (pComplPCore p X) = Nat.card (pCore p (X ⧸ pComplCore p X)) := by
  rw [pComplPCore_eq_comap]
  exact relIndex_comap_mk' _ _

variable [Fact p.Prime]

theorem isPGroup_quotient_pComplCore_subgroupOf :
    IsPGroup p (↥(pComplPCore p X) ⧸ (pComplCore p X).subgroupOf (pComplPCore p X)) := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)
    (G := pCore p (X ⧸ pComplCore p X))).1 (isPGroup_pCore Fact.out _)
  refine IsPGroup.of_card (n := n) ?_
  rw [natCard_quotient_subgroupOf, relIndex_pComplCore_pComplPCore, hn]

theorem hasPLengthLeOne_iff_not_dvd_index_pComplPCore :
    HasPLengthLeOne p X ↔ ¬ p ∣ (pComplPCore p X).index := by
  rw [hasPLengthLeOne_iff_not_dvd_index, index_pComplPCore]

theorem hasPLengthLeOne_iff_exists_normal :
    HasPLengthLeOne p X ↔ ∃ D T : Subgroup X, D.Normal ∧ T.Normal ∧ D ≤ T ∧
      ¬ p ∣ Nat.card D ∧ (∃ n : ℕ, Nat.card (↥T ⧸ D.subgroupOf T) = p ^ n) ∧
      ¬ p ∣ T.index := by
  have hp : p.Prime := Fact.out
  constructor
  ·
    intro h
    exact ⟨pComplCore p X, pComplPCore p X, Subgroup.normal_of_characteristic _,
      pComplPCore_normal p X, pComplCore_le_pComplPCore p X,
      not_dvd_natCard_pComplCore hp X,
      IsPGroup.iff_card.1 isPGroup_quotient_pComplCore_subgroupOf,
      hasPLengthLeOne_iff_not_dvd_index_pComplPCore.1 h⟩
  · rintro ⟨D, T, hD, hT, hDT, hDcard, ⟨n, hn⟩, hTidx⟩
    set N := pComplCore p X with hN
    have hDN : D ≤ N := le_pComplCore hD fun hmem => hDcard (Nat.dvd_of_mem_primeFactors hmem)
    have hcard : Nat.card (T.map (QuotientGroup.mk' N)) ∣ p ^ n := by
      rw [← Subgroup.relIndex_ker T (QuotientGroup.mk' N), QuotientGroup.ker_mk', ← hn,
        natCard_quotient_subgroupOf]
      exact Subgroup.relIndex_dvd_of_le_left T hDN
    have hle : T ≤ pComplPCore p X := by
      rw [pComplPCore_eq_comap, ← Subgroup.map_le_iff_le_comap]
      exact le_pCore hp (hT.map _ (QuotientGroup.mk'_surjective N))
        (IsPGroup.of_card_dvd_pow hcard)
    rw [hasPLengthLeOne_iff_not_dvd_index_pComplPCore]
    exact fun hdvd => hTidx (hdvd.trans (Subgroup.index_dvd_of_le hle))

end

end CFSG.FeitThompson
