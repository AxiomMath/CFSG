module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.SylowCentre
public meta import Lean.Meta.Tactic.NormCast
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

theorem commutator_top_eq_center_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 3) (hZ : Nat.card (Subgroup.center G) = p) :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = Subgroup.center G := by
  have hp2 : 2 ≤ p := hp.two_le
  have : Fact p.Prime := ⟨hp⟩
  have hidx : (Subgroup.center G).index = p ^ 2 := by
    have h := (Subgroup.center G).index_mul_card
    rw [hZ, hG] at h
    apply Nat.eq_of_mul_eq_mul_right hp.pos
    rw [h]
    ring
  have hQ : Nat.card (G ⧸ Subgroup.center G) = p ^ 2 := hidx
  have hcomm : IsMulCommutative (G ⧸ Subgroup.center G) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ
  have hle : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ Subgroup.center G :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm)
  have hne : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≠ ⊥ := by
    intro h
    have htop : Subgroup.center G = ⊤ := by
      have := (commutator_eq_bot_iff_center_eq_top (G := G)).mp h
      exact this
    rw [htop, Subgroup.card_top, hG] at hZ
    nlinarith
  have hcard : Nat.card (Subgroup.center G) ≤ Nat.card (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :
      Subgroup G) := by
    have hdvd : Nat.card (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ : Subgroup G) ∣
        Nat.card (Subgroup.center G) := Subgroup.card_dvd_of_le hle
    rw [hZ] at hdvd
    have hgt : 1 < Nat.card (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ : Subgroup G) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    have heq := (Nat.dvd_prime hp).mp hdvd
    rcases heq with h1 | h1
    · omega
    · omega
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem commutator_eq_inf_centralizer_of_card {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (H : Subgroup X) (hH : Nat.card H = p ^ 3)
    (hC : Nat.card (H ⊓ Subgroup.centralizer (H : Set X) : Subgroup X) = p) :
    ⁅H, H⁆ = H ⊓ Subgroup.centralizer (H : Set X) := by
  have hZ : Nat.card (Subgroup.center H) = p := by
    rw [← card_inf_centralizer_eq_card_center H]
    exact hC
  have key := commutator_top_eq_center_of_card hp hH hZ
  calc ⁅H, H⁆
      = (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆).map H.subtype := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = (Subgroup.center H).map H.subtype := by rw [key]
    _ = H ⊓ Subgroup.centralizer (H : Set X) := (inf_centralizer_eq_center_map H).symm

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
