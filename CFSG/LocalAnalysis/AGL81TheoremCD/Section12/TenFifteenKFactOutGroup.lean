module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutExcBurnside

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.AGLEmbedding.TwoGenInner (PGoodOut)
open scoped commutatorElement

theorem not_dvd_card_commutator_of_forall_commute {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (h : ∀ α γ : Q, (∃ k : ℕ, α ^ (p ^ k) = 1) → ⁅γ, α⁆ = 1) :
    ¬ p ∣ Nat.card (commutator Q) := by
  have : Fact p.Prime := ⟨hp⟩
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := commutator Q) p hdvd
  have hcen : ∀ y : Q, (∃ k : ℕ, y ^ (p ^ k) = 1) → y ∈ Subgroup.center Q := fun y hy =>
    Subgroup.mem_center_iff.2 fun γ => commutatorElement_eq_one_iff_mul_comm.1 (h y γ hy)
  have hxp : (x : Q) ^ (p ^ 1) = 1 := by
    rw [pow_one, ← hx]
    exact_mod_cast pow_orderOf_eq_one x
  have h1 : x = 1 := Subtype.ext
    (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.eq_one_of_mem_commutator_of_central_pElements hcen
      x.2 ⟨1, hxp⟩)
  rw [h1, orderOf_one] at hx
  exact hp.one_lt.ne hx

section Quotient

variable {A : Type*} [Group A] {p : ℕ}

theorem forall_commute_quotient (D : Subgroup A) [D.Normal]
    (h : ∀ α γ : A, (∃ k : ℕ, α ^ (p ^ k) ∈ D) → ⁅γ, α⁆ ∈ D) :
    ∀ α γ : A ⧸ D, (∃ k : ℕ, α ^ (p ^ k) = 1) → ⁅γ, α⁆ = 1 := by
  rintro α γ ⟨k, hk⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective α
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective γ
  have h1 : a ^ (p ^ k) ∈ D := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hk
  have h2 : (QuotientGroup.mk' D) ⁅c, a⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (h a c ⟨k, h1⟩)
  rwa [map_commutatorElement] at h2

variable [Finite A]

theorem not_dvd_card_map_mk (hp : p.Prime) (I D : Subgroup A) [I.Normal]
    (hD : ∀ δ ∈ D, ∀ k : ℕ, δ ^ (p ^ k) ∈ I → δ ∈ I) :
    ¬ p ∣ Nat.card (D.map (QuotientGroup.mk' I)) := by
  have : Fact p.Prime := ⟨hp⟩
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D.map (QuotientGroup.mk' I)) p hdvd
  obtain ⟨δ, hδ, hδx⟩ := Subgroup.mem_map.1 x.2
  have hxp : (x : A ⧸ I) ^ p = 1 := by
    rw [← hx]
    exact_mod_cast pow_orderOf_eq_one x
  have h1 : δ ^ (p ^ 1) ∈ I := by
    rw [pow_one, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hxp, ← hδx]
    rfl
  have h2 : x = 1 := Subtype.ext (by
    rw [← hδx]
    exact (QuotientGroup.eq_one_iff δ).2 (hD δ hδ 1 h1))
  rw [h2, orderOf_one] at hx
  exact hp.one_lt.ne hx

omit [Finite A] in
theorem card_commutator_quotient_dvd (I D : Subgroup A) [I.Normal] [D.Normal] (hID : I ≤ D) :
    Nat.card (commutator (A ⧸ I)) ∣
      Nat.card (commutator (A ⧸ D)) * Nat.card (D.map (QuotientGroup.mk' I)) := by
  let φ : A ⧸ I →* A ⧸ D := QuotientGroup.map I D (MonoidHom.id A) hID
  have hφ : Function.Surjective φ := fun x => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨(a : A ⧸ I), rfl⟩
  let f : commutator (A ⧸ I) →* A ⧸ D := φ.comp (commutator (A ⧸ I)).subtype
  have hrange : f.range = commutator (A ⧸ D) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, commutator_def, commutator_def,
      Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hφ]
  have hker : Nat.card f.ker ∣ Nat.card (D.map (QuotientGroup.mk' I)) := by
    rw [← Subgroup.card_map_of_injective (commutator (A ⧸ I)).subtype_injective]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (x : A ⧸ I)
    have h1 : φ (x : A ⧸ I) = 1 := MonoidHom.mem_ker.1 hx
    rw [← ha] at h1
    exact ⟨a, (QuotientGroup.eq_one_iff a).1 h1, ha⟩
  rw [← Subgroup.card_ker_mul_card_range f, hrange, mul_comm]
  exact Nat.mul_dvd_mul_left _ hker

theorem not_dvd_card_commutator_quotient (hp : p.Prime) (I D : Subgroup A) [I.Normal]
    [D.Normal] (hID : I ≤ D) (hD : ∀ δ ∈ D, ∀ k : ℕ, δ ^ (p ^ k) ∈ I → δ ∈ I)
    (hcent : ∀ α γ : A, (∃ k : ℕ, α ^ (p ^ k) ∈ D) → ⁅γ, α⁆ ∈ D) :
    ¬ p ∣ Nat.card (commutator (A ⧸ I)) := by
  intro hdvd
  have h1 := not_dvd_card_commutator_of_forall_commute hp (forall_commute_quotient D hcent)
  have h2 := not_dvd_card_map_mk hp I D hD
  rcases (Nat.Prime.dvd_mul hp).1 (hdvd.trans (card_commutator_quotient_dvd I D hID)) with h | h
  exacts [h1 h, h2 h]

end Quotient

theorem not_dvd_card_commutator_outer_of_pGoodOut {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (h : PGoodOut p X) : ¬ p ∣ Nat.card (commutator (Outer X)) := by
  obtain ⟨D, hDn, hID, hD, hcent⟩ := h
  exact not_dvd_card_commutator_quotient hp (inner X) D hID hD hcent

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
