module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLinBase

public section

universe v

namespace CFSG.QuasithinUnique.Setup.Wreath

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.Quasithin.B6
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem pow_two_pow_mem_of_sup_eq {H J T : Subgroup (V ≃ₗ[k] V)} (hJH : J ≤ H)
    (hJn : (J.subgroupOf H).Normal) (hTH : T ≤ H) (hT2 : IsPGroup 2 T) (hsup : J ⊔ T = H) :
    ∀ g ∈ H, ∃ n : ℕ, g ^ 2 ^ n ∈ J := by
  intro g hg
  have hTn : T ≤ Subgroup.normalizer (J : Set (V ≃ₗ[k] V)) :=
    hTH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJH).1 hJn)
  have hg' : g ∈ J ⊔ T := by rw [hsup]; exact hg
  obtain ⟨j, hj, t, ht, rfl⟩ := mem_sup_mul hTn hg'
  let q : ↥H →* ↥H ⧸ J.subgroupOf H := QuotientGroup.mk' (J.subgroupOf H)
  have hjH : j ∈ H := hJH hj
  have htH : t ∈ H := hTH ht
  obtain ⟨n, hn⟩ := hT2 ⟨t, ht⟩
  refine ⟨n, ?_⟩
  have hn' : (⟨t, htH⟩ : ↥H) ^ 2 ^ n = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hn
    simpa using this
  have hq : q ⟨j * t, hg⟩ = q ⟨t, htH⟩ := by
    have e : (⟨j * t, hg⟩ : ↥H) = ⟨j, hjH⟩ * ⟨t, htH⟩ := rfl
    rw [e, map_mul]
    have h1 : q ⟨j, hjH⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hj
    rw [h1, one_mul]
  have h1 : (q ⟨j * t, hg⟩) ^ 2 ^ n = 1 := by rw [hq, ← map_pow, hn', map_one]
  have h2 : (⟨j * t, hg⟩ : ↥H) ^ 2 ^ n ∈ J.subgroupOf H :=
    (QuotientGroup.eq_one_iff _).1
      (show q ((⟨j * t, hg⟩ : ↥H) ^ 2 ^ n) = 1 by rw [map_pow]; exact h1)
  have h3 := Subgroup.mem_subgroupOf.1 h2
  simpa using h3

theorem isInvariant_commGL {H N : Subgroup (V ≃ₗ[k] V)} (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) :
    Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) H (commGL N ⊤) := by
  intro h hh u hu
  have hnorm : h ∈ Subgroup.normalizer (N : Set (V ≃ₗ[k] V)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).1 hNn hh
  have e := commGL_conjSub h N
  rw [conjSub_eq_self hnorm] at e
  have : h u ∈ (commGL N ⊤).map (h : V →ₗ[k] V) := ⟨u, hu, rfl⟩
  rw [← e] at this
  exact this

theorem pCore_trivial_of_centralizer_le {H N : Subgroup (V ≃ₗ[k] V)} (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (hodd : Odd (Nat.card N))
    (hC : H ⊓ Subgroup.centralizer (N : Set (V ≃ₗ[k] V)) ≤ N) :
    ∀ N' : Subgroup (V ≃ₗ[k] V), N' ≤ H → (N'.subgroupOf H).Normal → IsPGroup 2 N' →
      N' = ⊥ := by
  intro N' hN'H hN'n hN'2
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxH : x ∈ H := hN'H hx
  have hxC : x ∈ Subgroup.centralizer (N : Set (V ≃ₗ[k] V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hnH : n ∈ H := hNH hn
    have h1 : x * n * x⁻¹ * n⁻¹ ∈ N := by
      have := (Subgroup.normal_subgroupOf_iff hNH).1 hNn n x hn hxH
      exact N.mul_mem this (N.inv_mem hn)
    have h2 : x * n * x⁻¹ * n⁻¹ ∈ N' := by
      have := (Subgroup.normal_subgroupOf_iff hN'H).1 hN'n x⁻¹ n (N'.inv_mem hx) hnH
      have e : x * n * x⁻¹ * n⁻¹ = x * (n * x⁻¹ * n⁻¹) := by group
      rw [e]
      exact N'.mul_mem hx this
    have h3 : x * n * x⁻¹ * n⁻¹ = 1 := by
      apply eq_one_of_two_pow_of_odd_card hodd h1
      obtain ⟨m, hm⟩ := hN'2 ⟨_, h2⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    have : n * x = x * n := by
      have h4 : x * n * x⁻¹ = n := by
        have := congrArg (· * n) h3
        simpa [mul_assoc] using this
      calc n * x = x * n * x⁻¹ * x := by rw [h4]
        _ = x * n := by group
    exact this
  have hxN : x ∈ N := hC ⟨hxH, hxC⟩
  apply eq_one_of_two_pow_of_odd_card hodd hxN
  obtain ⟨m, hm⟩ := hN'2 ⟨x, hx⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

theorem exists_two_pow_of_transitive {r : ℕ} (hr : 1 ≤ r) {P : Subgroup (Equiv.Perm (Fin r))}
    (hP : IsPGroup 2 ↥P) (htrans : ∀ i j : Fin r, ∃ σ ∈ P, σ i = j) : ∃ m : ℕ, r = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a : Fin r := ⟨0, hr⟩
  obtain ⟨m, hm⟩ := hP.card_orbit a
  refine ⟨m, ?_⟩
  have horb : MulAction.orbit ↥P a = Set.univ := by
    ext j
    simp only [Set.mem_univ, iff_true]
    obtain ⟨σ, hσ, hσa⟩ := htrans a j
    exact ⟨⟨σ, hσ⟩, hσa⟩
  rw [horb] at hm
  rw [← hm]
  rw [Nat.card_congr (Equiv.Set.univ (Fin r))]
  simp

@[expose] def permImage {ι : Type*} (H : Subgroup (V ≃ₗ[k] V)) (I : ι → Submodule k V) :
    Subgroup (Equiv.Perm ι) where
  carrier := {σ | ∃ x ∈ H, ActsAs I x σ}
  one_mem' := ⟨1, H.one_mem, ActsAs.one I⟩
  mul_mem' := by
    rintro σ τ ⟨x, hx, hxσ⟩ ⟨y, hy, hyτ⟩
    exact ⟨x * y, H.mul_mem hx hy, hxσ.mul hyτ⟩
  inv_mem' := by
    rintro σ ⟨x, hx, hxσ⟩
    exact ⟨x⁻¹, H.inv_mem hx, hxσ.inv⟩

theorem mem_permImage {ι : Type*} {H : Subgroup (V ≃ₗ[k] V)} {I : ι → Submodule k V}
    {σ : Equiv.Perm ι} : σ ∈ permImage H I ↔ ∃ x ∈ H, ActsAs I x σ := Iff.rfl

theorem nonempty_mulEquiv_gl {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W] {n : ℕ}
    (hd : Module.finrank k W = n) : Nonempty ((W ≃ₗ[k] W) ≃* Matrix.GeneralLinearGroup (Fin n) k) :=
  ⟨((Matrix.GeneralLinearGroup.toLin' (Module.finBasisOfFinrankEq k W hd)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k W)).symm⟩

end CFSG.QuasithinUnique.Setup.Wreath
