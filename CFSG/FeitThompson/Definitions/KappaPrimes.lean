module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] {p : ℕ} {M : Subgroup G}

theorem map_centralizer_eq_centralizer_image {G' : Type*} [Group G'] (s : Set G) (e : G ≃* G') :
    (centralizer s).map (e : G →* G') = centralizer (e '' s) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image s _) ?_
  intro y hy
  refine ⟨e.symm y, ?_, by simp⟩
  have := Subgroup.map_centralizer_le_centralizer_image (e '' s) (e.symm : G' →* G)
    (Subgroup.mem_map_of_mem _ hy)
  simpa [Set.image_image] using this

theorem isCyclic_map_subtype_iff (Q : Subgroup M) :
    IsCyclic ((Q.map M.subtype : Subgroup G)) ↔ IsCyclic Q :=
  (MulEquiv.isCyclic (Q.equivMapOfInjective M.subtype M.subtype_injective)).symm

theorem isCyclic_map_conj_iff (Q : Subgroup G) (g : G) :
    IsCyclic (Q.map (MulAut.conj g : G →* G)) ↔ IsCyclic Q :=
  (MulEquiv.isCyclic
    (Q.equivMapOfInjective (MulAut.conj g : G →* G) (MulAut.conj g).injective)).symm

theorem exists_ne_one_inf_centralizer_ne_bot_map_conj {N P : Subgroup G} {g : G}
    (hg : g ∈ normalizer (N : Set G))
    (h : ∃ x ∈ P, x ≠ (1 : G) ∧ N ⊓ centralizer ({x} : Set G) ≠ ⊥) :
    ∃ x ∈ P.map (MulAut.conj g : G →* G), x ≠ (1 : G) ∧
      N ⊓ centralizer ({x} : Set G) ≠ ⊥ := by
  obtain ⟨x, hxP, hx1, hne⟩ := h
  refine ⟨MulAut.conj g x, Subgroup.mem_map_of_mem _ hxP, by simpa using hx1, ?_⟩
  have hN : N.map (MulAut.conj g : G →* G) = N := Subgroup.mem_normalizer_iff_map_conj_eq.1 hg
  have hkey : (N ⊓ centralizer ({x} : Set G)).map (MulAut.conj g : G →* G)
      = N ⊓ centralizer ({MulAut.conj g x} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hN,
      map_centralizer_eq_centralizer_image]
    simp
  rw [← hkey]
  exact fun hc =>
    hne ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).1 hc)

def kappaPrimes [Finite G] (M : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧ p ∣ Nat.card M ∧ p ∉ sigmaPrimes M ∧
    ∃ S : Sylow p M, IsCyclic ((S : Subgroup M).map M.subtype : Subgroup G) ∧
      ∃ x ∈ ((S : Subgroup M).map M.subtype : Subgroup G), x ≠ (1 : G) ∧
        sigmaCore M ⊓ centralizer ({x} : Set G) ≠ ⊥}

variable [Finite G]

theorem mem_kappaPrimes_iff :
    p ∈ kappaPrimes M ↔ p.Prime ∧ p ∣ Nat.card M ∧ p ∉ sigmaPrimes M ∧
      ∃ S : Sylow p M, IsCyclic ((S : Subgroup M).map M.subtype : Subgroup G) ∧
        ∃ x ∈ ((S : Subgroup M).map M.subtype : Subgroup G), x ≠ (1 : G) ∧
          sigmaCore M ⊓ centralizer ({x} : Set G) ≠ ⊥ :=
  (Iff.rfl)

theorem prime_of_mem_kappaPrimes (hp : p ∈ kappaPrimes M) : p.Prime := hp.1

theorem dvd_natCard_of_mem_kappaPrimes (hp : p ∈ kappaPrimes M) : p ∣ Nat.card M := hp.2.1

theorem notMem_sigmaPrimes_of_mem_kappaPrimes (hp : p ∈ kappaPrimes M) : p ∉ sigmaPrimes M :=
  hp.2.2.1

theorem kappaPrimes_subset_setOf_prime (M : Subgroup G) : kappaPrimes M ⊆ {p : ℕ | p.Prime} :=
  fun _ hp => hp.1

theorem disjoint_kappaPrimes_sigmaPrimes (M : Subgroup G) :
    Disjoint (kappaPrimes M) (sigmaPrimes M) :=
  Set.disjoint_left.2 fun _ hp => hp.2.2.1

theorem kappaPrimes_subset_primeFactors (M : Subgroup G) :
    kappaPrimes M ⊆ ↑(Nat.card M).primeFactors := fun _ hp =>
  Nat.mem_primeFactors.2 ⟨hp.1, hp.2.1, Nat.card_pos.ne'⟩

theorem kappaPrimes_finite (M : Subgroup G) : (kappaPrimes M).Finite :=
  (Nat.card M).primeFactors.finite_toSet.subset (kappaPrimes_subset_primeFactors M)

theorem mem_kappaPrimes_iff_exists_subgroup (hp : p.Prime) :
    p ∈ kappaPrimes M ↔ p ∣ Nat.card M ∧ p ∉ sigmaPrimes M ∧
      ∃ P : Subgroup G, P ≤ M ∧ Nat.card P = p ^ (Nat.card M).factorization p ∧ IsCyclic P ∧
        ∃ x ∈ P, x ≠ (1 : G) ∧ sigmaCore M ⊓ centralizer ({x} : Set G) ≠ ⊥ := by
  rw [mem_kappaPrimes_iff]
  simp only [hp, true_and]
  constructor
  · rintro ⟨hd, hσ, S, hcyc, hx⟩
    obtain ⟨h1, h2⟩ := (exists_sylow_map_subtype_eq_iff hp).1 ⟨S, rfl⟩
    exact ⟨hd, hσ, _, h1, h2, hcyc, hx⟩
  · rintro ⟨hd, hσ, P, h1, h2, hcyc, hx⟩
    obtain ⟨S, hS⟩ := (exists_sylow_map_subtype_eq_iff hp (P := P)).2 ⟨h1, h2⟩
    exact ⟨hd, hσ, S, by rw [hS]; exact ⟨hcyc, hx⟩⟩

theorem mem_kappaPrimes_iff_forall (hp : p.Prime) :
    p ∈ kappaPrimes M ↔ p ∣ Nat.card M ∧ p ∉ sigmaPrimes M ∧
      ∀ S : Sylow p M, IsCyclic ((S : Subgroup M).map M.subtype : Subgroup G) ∧
        ∃ x ∈ ((S : Subgroup M).map M.subtype : Subgroup G), x ≠ (1 : G) ∧
          sigmaCore M ⊓ centralizer ({x} : Set G) ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [mem_kappaPrimes_iff]
  simp only [hp, true_and]
  refine ⟨?_, fun h => ⟨h.1, h.2.1, (default : Sylow p M), h.2.2 _⟩⟩
  rintro ⟨hd, hσ, S, hcyc, hx⟩
  refine ⟨hd, hσ, fun S' => ?_⟩
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (M : Type _) S S'
  have h1 : (S : Subgroup M).map (MulAut.conj m) = (S' : Subgroup M) := by
    have h := Sylow.coe_subgroup_smul (g := m) (P := S)
    rw [hm] at h
    exact h.symm
  have h2 : ((S' : Subgroup M).map M.subtype : Subgroup G)
      = ((S : Subgroup M).map M.subtype).map (MulAut.conj (m : G) : G →* G) := by
    rw [← h1, map_subtype_map_conj]
  rw [h2]
  exact ⟨(isCyclic_map_conj_iff _ _).2 hcyc,
    exists_ne_one_inf_centralizer_ne_bot_map_conj (le_normalizer_sigmaCore M m.2) hx⟩

theorem mem_kappaPrimes_iff_isCyclic_sylow :
    p ∈ kappaPrimes M ↔ p.Prime ∧ p ∣ Nat.card M ∧ p ∉ sigmaPrimes M ∧
      ∃ S : Sylow p M, IsCyclic (S : Subgroup M) ∧
        ∃ x ∈ ((S : Subgroup M).map M.subtype : Subgroup G), x ≠ (1 : G) ∧
          sigmaCore M ⊓ centralizer ({x} : Set G) ≠ ⊥ := by
  rw [mem_kappaPrimes_iff]
  simp only [isCyclic_map_subtype_iff]

@[simp]
theorem kappaPrimes_bot : kappaPrimes (⊥ : Subgroup G) = ∅ := by
  ext p
  simp only [mem_kappaPrimes_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp hdvd
  rw [Subgroup.card_bot, Nat.dvd_one] at hdvd
  exact absurd hdvd hp.ne_one

theorem kappaPrimes_top : kappaPrimes (⊤ : Subgroup G) = ∅ := by
  ext p
  simp only [mem_kappaPrimes_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp hdvd hσ
  exact absurd (by rw [sigmaPrimes_top]; exact ⟨hp, by simpa using hdvd⟩) hσ

end

end CFSG.FeitThompson
