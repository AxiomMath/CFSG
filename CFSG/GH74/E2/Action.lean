module

public import CFSG.GH74.E2.Coprime
public import CFSG.GH74.E2.Basic

public section

namespace CFSG.GH74.E2

open Subgroup

theorem rank_le_one_of_card_le_two {H : Type*} [Group H] [Finite H] (h : Nat.card H ≤ 2) :
    Group.rank H ≤ 1 := by
  by_cases h1 : Nat.card H = 1
  · have hsub : Subsingleton H := (Nat.card_eq_one_iff_unique.1 h1).1
    rw [Group.rank_eq_zero_iff.2 hsub]
    omega
  · have h2 : Nat.card H = 2 := by
      have := Nat.card_pos (α := H)
      omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc : IsCyclic H := isCyclic_of_prime_card h2
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hmem : g ∈ (Subgroup.closure ((({g} : Finset H) : Finset H) : Set H)) :=
      Subgroup.subset_closure (by simp)
    have htop : Subgroup.closure ((({g} : Finset H) : Finset H) : Set H) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨k, rfl⟩ := hg x
      exact Subgroup.zpow_mem _ hmem k
    have := Group.rank_le htop
    simpa using this

theorem exists_centralizer_index_pow {G : Type*} [Group G] [Finite G] {B X : Subgroup G}
    (hX : IsPGroup 2 X) (hnorm : ∀ b ∈ B, ∀ x ∈ X, b * x * b⁻¹ ∈ X) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hB : ElemAb p B) :
    ∃ r : ℕ, Nat.card B = p ^ r * Nat.card ↥(B ⊓ centralizer (X : Set G)) ∧
      orderOf (2 : ZMod p) * r ≤ Group.rank X := by
  have : Fact p.Prime := ⟨hp⟩
  have hnormX := le_normalizer_of_normalizes hnorm
  let φ : B →* MulAut X := conjAction B X hnormX
  let K : Subgroup B := φ.ker
  have hQcomm : ∀ a b : B ⧸ K, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | _ a => ?_
    induction b using QuotientGroup.induction_on with | _ b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hB.1 a a.2 b b.2)
  have hQpow : ∀ a : B ⧸ K, a ^ p = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with | _ a => ?_
    rw [← QuotientGroup.mk_pow]
    have : a ^ p = 1 := Subtype.ext (hB.2 a a.2)
    rw [this]; rfl
  have hBp : IsPGroup p B := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hB.2 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hBp
  have hQcard : Nat.card (B ⧸ K) ∣ p ^ n := by
    rw [← hn]
    exact ⟨Nat.card K, Subgroup.card_eq_card_quotient_mul_card_subgroup K⟩
  obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow hp).1 hQcard
  have hF1 := ord_mul_card_le_rank_hom (X := X) hX (A := B ⧸ K) (QuotientGroup.kerLift φ)
    (QuotientGroup.kerLift_injective φ) hp hp2 hQcomm hQpow hr
  have hKeq : Nat.card K = Nat.card ↥(B ⊓ centralizer (X : Set G)) := by
    refine Nat.card_congr ⟨fun k => ⟨(k.1 : G), k.1.2, ?_⟩, fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩, ?_, ?_⟩
    · refine mem_centralizer_iff.2 ?_
      intro h hh
      have h1 : φ k.1 = 1 := k.2
      have h2 := congrArg (fun f : MulAut X => ((f ⟨h, hh⟩ : X) : G)) h1
      have h3 : ((φ k.1 ⟨h, hh⟩ : X) : G) = (k.1 : G) * h * (k.1 : G)⁻¹ := rfl
      simp only [h3] at h2
      change (k.1 : G) * h * (k.1 : G)⁻¹ = h at h2
      calc h * (k.1 : G) = ((k.1 : G) * h * (k.1 : G)⁻¹) * (k.1 : G) := by rw [h2]
        _ = (k.1 : G) * h := by group
    · show φ ⟨y.1, y.2.1⟩ = 1
      ext x
      have hy := mem_centralizer_iff.1 y.2.2 x x.2
      change (y.1 : G) * x * (y.1 : G)⁻¹ = x
      calc (y.1 : G) * x * (y.1 : G)⁻¹ = ((y.1 : G) * x) * (y.1 : G)⁻¹ := rfl
        _ = (x * (y.1 : G)) * (y.1 : G)⁻¹ := by rw [← hy]
        _ = x := by group
    · intro k; exact Subtype.ext (Subtype.ext rfl)
    · intro y; exact Subtype.ext rfl
  refine ⟨r, ?_, hF1⟩
  rw [← hKeq, ← hr]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup K

end CFSG.GH74.E2
