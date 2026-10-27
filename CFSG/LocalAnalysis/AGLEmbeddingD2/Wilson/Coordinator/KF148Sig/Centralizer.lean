module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Image
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.FixedLift
public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig

open Subgroup CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.GH74.GLS

variable {Γ : Type*} [Group Γ] {L K A : Subgroup Γ} (hKL : K ≤ L) {X : Type*} [Group X]
  (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X) (hAL : A ≤ normalizer (L : Set Γ))
  (hAK : A ≤ normalizer (K : Set Γ)) (hc : center X = ⊥)
  (hodd : ∀ α : MulAut X, Odd (orderOf α) → ∃ g : X, α = MulAut.conj g)
  (hA3 : ∀ a ∈ A, a ^ 3 = 1)

include hAK in
theorem kappa_mul_innerHom_of_commute (x : A) {k : K} (hk : (x : Γ) * k = k * x) :
    kappa hKL ψ k * innerHom hAL ψ hc hodd hA3 x = innerHom hAL ψ hc hodd hA3 x * kappa hKL ψ k := by
  have h := kappa_conj hKL ψ hAL hAK hc hodd hA3 x k
  have e : (⟨(x : Γ) * k * (x : Γ)⁻¹, (hAK x.2 k).mp k.2⟩ : K) = k :=
    Subtype.ext (show (x : Γ) * k * (x : Γ)⁻¹ = k by rw [hk, mul_inv_cancel_right])
  rw [e] at h
  calc kappa hKL ψ k * innerHom hAL ψ hc hodd hA3 x
      = (innerHom hAL ψ hc hodd hA3 x * kappa hKL ψ k * (innerHom hAL ψ hc hodd hA3 x)⁻¹) *
          innerHom hAL ψ hc hodd hA3 x := by rw [← h]
    _ = innerHom hAL ψ hc hodd hA3 x * kappa hKL ψ k := by group

@[expose] noncomputable def centMap (x : A) :
    ↥(K ⊓ centralizer ({(x : Γ)} : Set Γ)) →*
      ↥((kappa hKL ψ).range ⊓ centralizer ({innerHom hAL ψ hc hodd hA3 x} : Set X)) where
  toFun c := ⟨kappa hKL ψ ⟨c, (mem_inf.1 c.2).1⟩, mem_inf.2 ⟨⟨_, rfl⟩,
    mem_centralizer_singleton_iff.2 (kappa_mul_innerHom_of_commute hKL ψ hAL hAK hc hodd hA3 x
      (mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).2).symm)⟩⟩
  map_one' := Subtype.ext (map_one (kappa hKL ψ))
  map_mul' a b := Subtype.ext (map_mul (kappa hKL ψ) ⟨a, (mem_inf.1 a.2).1⟩ ⟨b, (mem_inf.1 b.2).1⟩)

theorem coe_centMap (x : A) (c : ↥(K ⊓ centralizer ({(x : Γ)} : Set Γ))) :
    (centMap hKL ψ hAL hAK hc hodd hA3 x c : X) = kappa hKL ψ ⟨c, (mem_inf.1 c.2).1⟩ := rfl

variable [Finite Γ]

theorem centMap_surjective (x : A) : Function.Surjective (centMap hKL ψ hAL hAK hc hodd hA3 x) := by
  rintro ⟨d, hd⟩
  obtain ⟨⟨k0, rfl⟩, hdc⟩ := mem_inf.1 hd
  have hdc' := mem_centralizer_singleton_iff.1 hdc
  set n : normalizer (K : Set Γ) := ⟨x, hAK x.2⟩ with hn
  set σ := K.normalizerMonoidHom n with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : n ^ 3 = 1 := Subtype.ext (by simpa [hn] using hA3 x x.2)
    rw [this, map_one]
  have hσg : ∀ g : K, (σ g : Γ) = x * g * (x : Γ)⁻¹ := fun g => rfl
  have hy : ∀ g : K, kappa hKL ψ g = kappa hKL ψ k0 → kappa hKL ψ (σ g) = kappa hKL ψ k0 := by
    intro g hg
    have e : σ g = ⟨(x : Γ) * g * (x : Γ)⁻¹, (hAK x.2 g).mp g.2⟩ := Subtype.ext (hσg g)
    rw [e, kappa_conj hKL ψ hAL hAK hc hodd hA3 x g, hg, ← hdc']
    group
  obtain ⟨g, hg, hσg'⟩ := Proving.exists_fixed_lift_of_pow_three (kappa hKL ψ)
    (coprime_card_ker_kappa hKL ψ) σ hσ3 hy
  have hgx : (g : Γ) ∈ centralizer ({(x : Γ)} : Set Γ) := by
    rw [mem_centralizer_singleton_iff]
    have h1 := congrArg Subtype.val hσg'
    rw [hσg] at h1
    calc (g : Γ) * x = (x * g * (x : Γ)⁻¹) * x := by rw [h1]
      _ = x * g := by group
  exact ⟨⟨g, mem_inf.2 ⟨g.2, hgx⟩⟩, Subtype.ext hg⟩

include hAK in
theorem map_pPrimeCoreOf_le (x : A) :
    ((pPrimeCoreOf 3 (K ⊓ centralizer ({(x : Γ)} : Set Γ))).subgroupOf K).map (kappa hKL ψ) ≤
      pPrimeCoreOf 3 ((kappa hKL ψ).range ⊓
        centralizer ({innerHom hAL ψ hc hodd hA3 x} : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨c, hc', hck⟩ := mem_subgroupOf.1 hk
  have hmem := map_pPrimeCore_le (p := 3) (centMap hKL ψ hAL hAK hc hodd hA3 x)
    (centMap_surjective hKL ψ hAL hAK hc hodd hA3 x) ⟨c, hc', rfl⟩
  refine ⟨_, hmem, ?_⟩
  rw [coe_subtype, coe_centMap]
  congr 1
  exact Subtype.ext hck

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig
