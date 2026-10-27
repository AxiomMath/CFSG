module

public import CFSG.FeitThompson.Definitions.ConventionForPLengthAtMostOne
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex

namespace CFSG.FeitThompson

open Pointwise

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p : ℕ} {X : Type*} [Group X]

def pLengthCore (p : ℕ) (X : Type*) [Group X] [Finite X] : Subgroup X :=
  (pCore p (X ⧸ pComplCore p X)).comap (QuotientGroup.mk' (pComplCore p X))

theorem pLengthCore_eq_comap (p : ℕ) (X : Type*) [Group X] [Finite X] :
    pLengthCore p X =
      (pCore p (X ⧸ pComplCore p X)).comap (QuotientGroup.mk' (pComplCore p X)) := (rfl)

theorem mem_pLengthCore_iff [Finite X] {x : X} :
    x ∈ pLengthCore p X ↔
      (x : X ⧸ pComplCore p X) ∈ pCore p (X ⧸ pComplCore p X) := (Iff.rfl)

instance pLengthCore_normal (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (pLengthCore p X).Normal := by
  rw [pLengthCore_eq_comap]
  exact Subgroup.Normal.comap (Subgroup.normal_of_characteristic _) _

theorem pComplCore_le_pLengthCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    pComplCore p X ≤ pLengthCore p X :=
  (QuotientGroup.ker_mk' (pComplCore p X)).ge.trans (MonoidHom.ker_le_comap _ _)

theorem map_mk'_pLengthCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (pLengthCore p X).map (QuotientGroup.mk' (pComplCore p X)) = pCore p (X ⧸ pComplCore p X) :=
  Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem index_pLengthCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (pLengthCore p X).index = (pCore p (X ⧸ pComplCore p X)).index :=
  Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem hasPLengthLeOne_iff_not_dvd_index_pLengthCore [Finite X] [Fact p.Prime] :
    HasPLengthLeOne p X ↔ ¬ p ∣ (pLengthCore p X).index := by
  rw [hasPLengthLeOne_iff_not_dvd_index, index_pLengthCore]

theorem hasPLengthLeOne_iff_not_dvd_natCard_range_leftCoset [Finite X] [Fact p.Prime] :
    HasPLengthLeOne p X ↔
      ¬ p ∣ Nat.card (Set.range fun g : X => g • (pLengthCore p X : Set X)) := by
  rw [hasPLengthLeOne_iff_not_dvd_index_pLengthCore, natCard_range_leftCoset]

def IsNormalPComplement (p : ℕ) {X : Type*} [Group X] (N : Subgroup X) : Prop :=
  N.Normal ∧ ¬ p ∣ Nat.card N ∧ ∃ n : ℕ, N.index = p ^ n

theorem isNormalPComplement_iff {N : Subgroup X} :
    IsNormalPComplement p N ↔ N.Normal ∧ ¬ p ∣ Nat.card N ∧ ∃ n : ℕ, N.index = p ^ n := (Iff.rfl)

theorem IsNormalPComplement.normal {N : Subgroup X} (h : IsNormalPComplement p N) : N.Normal := h.1

theorem IsNormalPComplement.not_dvd_natCard {N : Subgroup X} (h : IsNormalPComplement p N) :
    ¬ p ∣ Nat.card N := h.2.1

theorem IsNormalPComplement.exists_index_eq_pow {N : Subgroup X} (h : IsNormalPComplement p N) :
    ∃ n : ℕ, N.index = p ^ n := h.2.2

theorem isNormalPComplement_of {N : Subgroup X} (hnorm : N.Normal) (hcard : ¬ p ∣ Nat.card N)
    (hindex : ∃ n : ℕ, N.index = p ^ n) : IsNormalPComplement p N := ⟨hnorm, hcard, hindex⟩

theorem IsNormalPComplement.le_pComplCore [Finite X] {N : Subgroup X}
    (h : IsNormalPComplement p N) : N ≤ pComplCore p X :=
  _root_.CFSG.FeitThompson.le_pComplCore h.normal
    fun hmem => h.not_dvd_natCard (Nat.mem_primeFactors.1 hmem).2.1

theorem IsNormalPComplement.eq_pComplCore [Finite X] (hp : p.Prime) {N : Subgroup X}
    (h : IsNormalPComplement p N) : N = pComplCore p X := by
  have hnorm := h.normal
  refine le_antisymm h.le_pComplCore ?_
  obtain ⟨n, hidx⟩ := h.exists_index_eq_pow
  set Q := (pComplCore p X).map (QuotientGroup.mk' N) with hQ
  have h1 : Nat.card Q ∣ Nat.card (pComplCore p X) := Subgroup.card_map_dvd _ _
  have h2 : Nat.card Q ∣ p ^ n := by
    refine (Subgroup.card_subgroup_dvd_card Q).trans ?_
    rw [← Subgroup.index_eq_card, hidx]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 h2
  have hk0 : k = 0 := by
    by_contra hne
    exact not_dvd_natCard_pComplCore hp X (dvd_trans (dvd_pow_self p hne) (hk ▸ h1))
  have hQbot : Q = ⊥ := Subgroup.card_eq_one.1 (by rw [hk, hk0, pow_zero])
  rw [hQ, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hQbot
  exact hQbot

def pElementCore (p : ℕ) (X : Type*) [Group X] : Subgroup X :=
  Subgroup.closure {x : X | ∃ k : ℕ, orderOf x = p ^ k}

theorem pElementCore_eq_closure (p : ℕ) (X : Type*) [Group X] :
    pElementCore p X = Subgroup.closure {x : X | ∃ k : ℕ, orderOf x = p ^ k} := (rfl)

theorem mem_pElementCore_of_orderOf_eq_pow {x : X} {k : ℕ} (h : orderOf x = p ^ k) :
    x ∈ pElementCore p X :=
  Subgroup.subset_closure ⟨k, h⟩

theorem one_mem_pElementCore (p : ℕ) (X : Type*) [Group X] : (1 : X) ∈ pElementCore p X :=
  one_mem _

theorem pElementCore_le_iff {K : Subgroup X} :
    pElementCore p X ≤ K ↔ ∀ x : X, (∃ k : ℕ, orderOf x = p ^ k) → x ∈ K := by
  rw [pElementCore_eq_closure, Subgroup.closure_le]
  exact ⟨fun h x hx => h hx, fun h _ hx => h _ hx⟩

instance pElementCore_characteristic (p : ℕ) (X : Type*) [Group X] :
    (pElementCore p X).Characteristic := by
  refine Subgroup.characteristic_iff_map_le.2 fun ϕ => ?_
  rw [pElementCore_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro y ⟨x, ⟨k, hk⟩, rfl⟩
  exact mem_pElementCore_of_orderOf_eq_pow (by rw [ϕ.coe_toMonoidHom, ϕ.orderOf_eq, hk])

theorem pElementCore_eq_top_of_isPGroup [Finite X] (hp : p.Prime) (hX : IsPGroup p X) :
    pElementCore p X = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨k, hk⟩ := hX.exists_orderOf_eq_pow x
  exact mem_pElementCore_of_orderOf_eq_pow hk

theorem pCore_le_pElementCore [Finite X] (hp : p.Prime) : pCore p X ≤ pElementCore p X := by
  have : Fact p.Prime := ⟨hp⟩
  intro x hx
  obtain ⟨k, hk⟩ := (isPGroup_pCore hp X).exists_orderOf_eq_pow ⟨x, hx⟩
  exact mem_pElementCore_of_orderOf_eq_pow ((Subgroup.orderOf_mk x hx).symm.trans hk)

variable [Finite X]

theorem exists_pow_pow_mem_pComplCore_of_mem_pLengthCore [Fact p.Prime] {x : X}
    (hx : x ∈ pLengthCore p X) : ∃ k : ℕ, x ^ p ^ k ∈ pComplCore p X := by
  rw [pLengthCore_eq_comap, Subgroup.mem_comap] at hx
  obtain ⟨k, hk⟩ :=
    (isPGroup_pCore Fact.out (X ⧸ pComplCore p X)).exists_pow_pow_eq_one ⟨_, hx⟩
  refine ⟨k, ?_⟩
  have h : (QuotientGroup.mk' (pComplCore p X) x) ^ p ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h

theorem pComplCore_subgroupOf_le (p : ℕ) [Fact p.Prime] (Y : Subgroup X) :
    (pComplCore p X).subgroupOf Y ≤ pComplCore p Y := by
  refine le_pComplCore Subgroup.normal_subgroupOf fun hmem => ?_
  have hdvd : Nat.card ((pComplCore p X).subgroupOf Y) ∣ Nat.card (pComplCore p X) :=
    Subgroup.card_comap_dvd_of_injective _ _ Y.subtype_injective
  exact not_dvd_natCard_pComplCore Fact.out X
    ((Nat.mem_primeFactors.1 hmem).2.1.trans hdvd)

theorem pLengthCore_subgroupOf_le [Fact p.Prime] (Y : Subgroup X) :
    (pLengthCore p X).subgroupOf Y ≤ pLengthCore p Y := by
  rw [pLengthCore_eq_comap p Y, ← Subgroup.map_le_iff_le_comap]
  refine le_pCore Fact.out
    (Subgroup.Normal.map Subgroup.normal_subgroupOf _ (QuotientGroup.mk'_surjective _)) fun g => ?_
  obtain ⟨y, hy, hgy⟩ := Subgroup.mem_map.1 g.2
  obtain ⟨k, hk⟩ :=
    exists_pow_pow_mem_pComplCore_of_mem_pLengthCore (Subgroup.mem_subgroupOf.1 hy)
  refine ⟨k, ?_⟩
  have hmem : y ^ p ^ k ∈ pComplCore p Y :=
    pComplCore_subgroupOf_le p Y (Subgroup.mem_subgroupOf.2 (by push_cast; exact hk))
  have h1 : (QuotientGroup.mk' (pComplCore p Y) y) ^ p ^ k = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmem
  ext
  push_cast
  rw [← hgy]
  exact h1

theorem HasPLengthLeOne.subgroup [Fact p.Prime] (h : HasPLengthLeOne p X) (Y : Subgroup X) :
    HasPLengthLeOne p Y := by
  rw [hasPLengthLeOne_iff_not_dvd_index_pLengthCore] at h ⊢
  refine fun hdvd => h (hdvd.trans ((Subgroup.index_dvd_of_le
    (pLengthCore_subgroupOf_le Y)).trans ?_))
  exact Subgroup.relIndex_dvd_index_of_normal _ _

theorem HasPLengthLeOne.subgroup_of_prime (hp : p.Prime) (h : HasPLengthLeOne p X)
    (Y : Subgroup X) : HasPLengthLeOne p Y :=
  have : Fact p.Prime := ⟨hp⟩
  h.subgroup Y

end

end CFSG.FeitThompson
