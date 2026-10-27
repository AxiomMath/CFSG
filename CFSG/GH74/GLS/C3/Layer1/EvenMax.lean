module

public import CFSG.GH74.GLS.C3.Layer1.EvenSetup
public import CFSG.GH74.GLS.C3.Layer1.EvenMaxSE

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG Blueprint

structure IsSimpleSocle {G : Type} [Group G] (H N : Subgroup G) : Prop where
  le : H ≤ N
  normal : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H
  simple : IsSimpleGroup ↥H
  centralizer_trivial : ∀ n ∈ N, (∀ h ∈ H, n * h = h * n) → n = 1

@[expose] def EvenMaxCase {G : Type} [Group G] (K H N : Subgroup G) : Prop :=
  (N = H ∧ ∃ n ∈ ({5, 6} : Finset ℕ), Nonempty (↥K ≃* alternatingGroup (Fin n)) ∧
      Nonempty (↥H ≃* alternatingGroup (Fin (n + 4)))) ∨
  (Nonempty (↥K ≃* alternatingGroup (Fin 5)) ∧ NativeSporadic.IsSporadic ↥H .M12 ∧
      Nat.card ↥N = 2 * Nat.card ↥H) ∨
  (Nonempty (↥K ≃* alternatingGroup (Fin 5)) ∧ NativeSporadic.IsSporadic ↥H .J2 ∧
      (N = H ∨ Nat.card ↥N = 2 * Nat.card ↥H))

@[expose] def B_even_N_core : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → IsEvenType G →
    (¬ ∃ (x y : G) (K : Subgroup G), IsV2Triple x y K) →
    ∀ (x : G) (K T Q N : Subgroup G), EvenSel x K T Q → IsStandardSubgroup K →
      gammaK 2 Q 1 ≤ normalizer (K : Set G) → normalizer (K : Set G) < N → N ≠ ⊤ →
      ∃ H : Subgroup G, K < H ∧ IsSimpleSocle H N ∧ EvenMaxCase K H N

@[expose] def B_even_N_alt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → IsEvenType G →
    (¬ ∃ (x y : G) (K : Subgroup G), IsV2Triple x y K) →
    ∀ (x : G) (K T Q N : Subgroup G), EvenSel x K T Q → IsStandardSubgroup K →
      gammaK 2 Q 1 ≤ normalizer (K : Set G) → normalizer (K : Set G) < N → N ≠ ⊤ →
      ∀ n ∈ ({5, 6} : Finset ℕ), Nonempty (↥K ≃* alternatingGroup (Fin n)) →
        Nonempty (↥N ≃* alternatingGroup (Fin (n + 4))) → SameCentralizerOfInvolutionPattern G ↥N

@[expose] def B_even_N_spor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → IsEvenType G →
    (¬ ∃ (x y : G) (K : Subgroup G), IsV2Triple x y K) →
    ∀ (x : G) (K T Q N H : Subgroup G), EvenSel x K T Q → IsStandardSubgroup K →
      gammaK 2 Q 1 ≤ normalizer (K : Set G) → normalizer (K : Set G) < N → N ≠ ⊤ →
      K < H → IsSimpleSocle H N → Nonempty (↥K ≃* alternatingGroup (Fin 5)) →
      ((NativeSporadic.IsSporadic ↥H .M12 ∧ Nat.card ↥N = 2 * Nat.card ↥H) ∨
        (NativeSporadic.IsSporadic ↥H .J2 ∧ (N = H ∨ Nat.card ↥N = 2 * Nat.card ↥H))) → False

section Glue

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q : Subgroup G}

theorem normalizer_ne_top_of_evenSel (hG : C3Hyp G) (hs : EvenSel x K T Q) :
    normalizer (K : Set G) ≠ ⊤ := by
  intro htop
  have hsimp : IsSimpleGroup G := hG.kproper.1
  have hnorm : ∀ g : G, g ∈ normalizer (K : Set G) := fun g => by
    rw [htop]
    exact mem_top g
  have hKn : K.Normal := ⟨fun n hn g => (mem_normalizer_iff.1 (hnorm g) n).1 hn⟩
  have hK2 := hs.two_dvd_K
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hb | ht
  · rw [hb] at hK2
    simp at hK2
  · have hxz : ∀ g : G, g * x = x * g := fun g => by
      have hgK : g ∈ K := by
        rw [ht]
        exact mem_top g
      have : g ∈ centralizer ({x} : Set G) := hs.K_le_C hgK
      exact mem_centralizer_singleton_iff.1 this
    have hxc : x ∈ center G := Subgroup.mem_center_iff.2 (fun g => hxz g)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hb | ht'
    · rw [hb, Subgroup.mem_bot] at hxc
      have := hs.terminal.1
      rw [hxc, orderOf_one] at this
      omega
    · obtain ⟨a, b, hab⟩ := hG.kproper.2.1
      apply hab
      have : a ∈ center G := by
        rw [ht']
        exact mem_top a
      exact (Subgroup.mem_center_iff.1 this b).symm

theorem even_card_of_evenSel (hs : EvenSel x K T Q) : Even (Nat.card G) := by
  have h2 : 2 ∣ Nat.card G := by
    have := orderOf_dvd_natCard x
    rwa [hs.terminal.1] at this
  exact even_iff_two_dvd.2 h2

end Glue

theorem b_even_max_of_leaves
    (hcore : B_even_N_core) (halt : B_even_N_alt) (hspor : B_even_N_spor) :
    B_even_max := by
  intro G _ _ hG hE hV x K T Q hs hstd hgam
  refine ⟨normalizer_ne_top_of_evenSel hG hs, fun N hMN => ?_⟩
  by_contra hN
  obtain ⟨H, hKH, hsoc, hcase⟩ := hcore G hG hE hV x K T Q N hs hstd hgam hMN hN
  rcases hcase with ⟨hNH, n, hn, hKn, hHn⟩ | ⟨hK5, hM12, hcard⟩ | ⟨hK5, hJ2, hcard⟩
  · subst hNH
    have hpat := halt G hG hE hV x K T Q N hs hstd hgam hMN hN n hn hKn hHn
    have hm : n + 4 = 9 ∨ n + 4 = 10 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      omega
    obtain ⟨e⟩ := hHn
    exact false_of_samePattern_alt hG hN (even_card_of_evenSel hs) hm e hpat
  · exact hspor G hG hE hV x K T Q N H hs hstd hgam hMN hN hKH hsoc hK5 (Or.inl ⟨hM12, hcard⟩)
  · exact hspor G hG hE hV x K T Q N H hs hstd hgam hMN hN hKH hsoc hK5 (Or.inr ⟨hJ2, hcard⟩)

theorem s_evenSetup_of_leaves'
    (h1 : B_even_select) (h2 : B_even_std) (hcore : B_even_N_core)
    (halt : B_even_N_alt) (hspor : B_even_N_spor) : S_evenSetup_rank4 :=
  s_evenSetup_of_leaves h1 h2 (b_even_max_of_leaves hcore halt hspor)

end CFSG.GH74.GLS
