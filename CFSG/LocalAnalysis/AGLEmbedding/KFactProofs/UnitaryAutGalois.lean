module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.AGLEmbedding.UnitaryModel

section FiniteField

variable (K : Type) [Field K] [Finite K]

theorem finite_ringEquiv : Finite (K ≃+* K) :=
  Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective

def ringEquivMulEquiv (p : ℕ) [Fact p.Prime] [CharP K p] :
    letI := ZMod.algebra K p
    (K ≃+* K) ≃* (K ≃ₐ[ZMod p] K) :=
  letI := ZMod.algebra K p
  { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (fun x => by
      have := RingHom.ext_zmod ((σ : K →+* K).comp (algebraMap (ZMod p) K)) (algebraMap (ZMod p) K)
      exact RingHom.congr_fun this x)
    invFun := fun τ => τ.toRingEquiv
    left_inv := fun σ => by ext; rfl
    right_inv := fun τ => by ext; rfl
    map_mul' := fun σ τ => by ext; rfl }

theorem isCyclic_ringEquiv (p : ℕ) [Fact p.Prime] [CharP K p] : IsCyclic (K ≃+* K) := by
  let _ := ZMod.algebra K p
  have : IsCyclic (K ≃ₐ[ZMod p] K) := inferInstance
  exact (ringEquivMulEquiv K p).isCyclic.2 this

theorem card_ringEquiv (p n : ℕ) [Fact p.Prime] [CharP K p] (hK : Nat.card K = p ^ n) :
    Nat.card (K ≃+* K) = n := by
  let _ := ZMod.algebra K p
  rw [Nat.card_congr (ringEquivMulEquiv K p).toEquiv]
  have h1 := IsGalois.card_aut_eq_finrank (ZMod p) K
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := K)
  rw [Nat.card_zmod, hK] at h2
  rw [h1]
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h2).symm

theorem card_le_of_pow_eq_one {G : Type*} [Group G] [IsCyclic G] [Finite G] (H : Subgroup G)
    {n : ℕ} (hn : 0 < n) (h : ∀ x ∈ H, x ^ n = 1) : Nat.card H ≤ n := by
  have : IsCyclic H := inferInstance
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have hord : orderOf g = Nat.card H := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgn : g ^ n = 1 := Subtype.ext (by simpa using h g.1 g.2)
  rw [← hord]
  exact Nat.le_of_dvd hn (orderOf_dvd_of_pow_eq_one hgn)

theorem card_eq_pow_card_fixed (σ : K ≃+* K) (p : ℕ) [Fact p.Prime] (h1 : σ ≠ 1)
    (hp : σ ^ p = 1) : Nat.card K = Nat.card {x : K // σ x = x} ^ p := by
  have : Finite (K ≃+* K) := finite_ringEquiv K
  have hord : orderOf σ = p := orderOf_eq_prime hp h1
  let G := Subgroup.zpowers σ
  have hG : Nat.card G = p := by rw [Nat.card_zpowers, hord]
  have : Fintype G := Fintype.ofFinite G
  have : FaithfulSMul G K := ⟨fun {g₁ g₂} h => Subtype.ext (RingEquiv.ext h)⟩
  have h := FixedPoints.finrank_eq_card G K
  rw [Fintype.card_eq_nat_card, hG] at h
  have : Module.Finite (FixedPoints.subfield G K) K := Module.Finite.of_finite
  have h2 := Module.natCard_eq_pow_finrank (K := FixedPoints.subfield G K) (V := K)
  rw [h] at h2
  have h3 : Nat.card (FixedPoints.subfield G K) = Nat.card {x : K // σ x = x} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    constructor
    · intro hx
      exact hx ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro hx
      have hst : G ≤ MulAction.stabilizer (K ≃+* K) x :=
        (Subgroup.zpowers_le).2 (by simpa [MulAction.mem_stabilizer_iff] using hx)
      intro g
      exact hst g.2
  rw [h2, h3]

end FiniteField

end CFSG.AGLEmbedding.UnitaryModel
