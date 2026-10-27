module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI713OutPComp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.AGLEmbedding.TwoGenInner (PGoodOut)

theorem mem_of_conjNormal_mem_inner' {X : Type*} [Group X] (K : Subgroup X) [K.Normal]
    (hKC : Subgroup.centralizer (K : Set X) = ⊥) {x : X}
    (hx : (MulAut.conjNormal (H := K)) x ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K) : x ∈ K := by
  obtain ⟨k, hk⟩ := hx
  have h1 : ∀ y ∈ K, (k : X) * y * (k : X)⁻¹ = x * y * x⁻¹ := by
    intro y hy
    have := congrArg (fun f : MulAut K => ((f ⟨y, hy⟩ : K) : X)) hk
    simpa using this
  have hc : (k : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := h1 y hy
    calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * x := by group
      _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [this]
      _ = (k : X)⁻¹ * x * y := by group
  rw [hKC, Subgroup.mem_bot] at hc
  have : x = (k : X) := by
    calc x = (k : X) * ((k : X)⁻¹ * x) := by group
      _ = k := by rw [hc, mul_one]
  exact this ▸ k.2

theorem exists_normal_index_pow_of_pGoodOut {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] (K : Subgroup X) [K.Normal] (hKC : Subgroup.centralizer (K : Set X) = ⊥)
    (h : PGoodOut p ↥K) {q : X} (hq : ∃ k : ℕ, q ^ (p ^ k) = 1) (hqK : q ∉ K) :
    ∃ N : Subgroup X, N.Normal ∧ (∃ k : ℕ, N.index = p ^ k) ∧ N ≠ ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨NO, hNOn, hNOcard, k, hk⟩ := exists_normal_pComplement_of_pGoodOut hp h
  let θ : X →* Outer ↥K :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K)).comp
      (MulAut.conjNormal (H := K))
  refine ⟨NO.comap θ, hNOn.comap θ, ?_, ?_⟩
  · have h1 : (NO.comap θ).index = NO.relIndex θ.range := Subgroup.index_comap NO θ
    have h2 : NO.relIndex θ.range ∣ NO.index := Subgroup.relIndex_dvd_index_of_normal _ _
    rw [hk] at h2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h2
    exact ⟨j, h1.trans hj⟩
  · intro htop
    have hq' : θ q ∈ NO := by
      have : q ∈ NO.comap θ := htop ▸ Subgroup.mem_top q
      exact this
    obtain ⟨k0, hk0⟩ := hq
    have hord : (θ q) ^ (p ^ k0) = 1 := by rw [← map_pow, hk0, map_one]
    have hθ1 : θ q = 1 := by
      have h1 : orderOf (⟨θ q, hq'⟩ : NO) ∣ p ^ k0 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hord))
      have h2 : orderOf (⟨θ q, hq'⟩ : NO) ∣ Nat.card NO := orderOf_dvd_natCard _
      have hcop : Nat.Coprime (p ^ k0) (Nat.card NO) :=
        Nat.Coprime.pow_left k0 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hNOcard)
      have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
      have h4 : (⟨θ q, hq'⟩ : NO) = 1 := orderOf_eq_one_iff.mp h3
      exact congrArg Subtype.val h4
    apply hqK
    refine mem_of_conjNormal_mem_inner' K hKC ?_
    exact (QuotientGroup.eq_one_iff _).1 hθ1

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
