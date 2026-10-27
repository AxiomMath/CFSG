module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.Fusion
public import CFSG.GH74.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14

open Subgroup CFSG.GH74.GLS.Stage1.Thm6.Sec13 CFSG.GH74.GLS.Stage1.Thm6.M12Facts

variable {G : Type} [Group G] {x : G} {T V S : Subgroup G} {a b y : G}

theorem isCentralInvolution_z (o : Out13 G x T V S a b y) : IsCentralInvolution (a ^ 2 * b ^ 2) := by
  have h := o.data
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS2, hSidx⟩ := sylow_S o
  refine ⟨orderOf_eq_prime (by rw [pow_two]; exact z_sq h) (z_ne_one h), ?_⟩
  let S' : Sylow 2 G := hS2.toSylow hSidx
  exact ⟨S', z_mem h, fun s hs => z_central h hs⟩

theorem sylow2In_centralizer_z (h : M12Data S a b y x) (hS : Sylow2In S ⊤) :
    Sylow2In S (centralizer ({a ^ 2 * b ^ 2} : Set G)) := by
  have hSz : S ≤ centralizer ({a ^ 2 * b ^ 2} : Set G) := by
    intro s hs
    rw [mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact (z_central h hs).symm
  refine ⟨hSz, hS.2.1, ?_⟩
  intro hdvd
  apply hS.2.2
  rw [Subgroup.relIndex_top_right, ← Subgroup.relIndex_mul_index hSz]
  exact Dvd.dvd.mul_right hdvd _

end CFSG.GH74.GLS.Stage1.Thm6.Sec14
