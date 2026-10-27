module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup
open scoped Pointwise
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem mulAut_apply_apply_of_mul_self {G : Type*} [Group G] {σ : MulAut G} (hσ : σ * σ = 1)
    (x : G) : σ (σ x) = x := by
  have h := congrArg (fun e : MulAut G => e x) hσ
  simpa using h

theorem card_le_card_fixedSubgroup_sq {G : Type*} [Group G] [Finite G] (σ : MulAut G)
    (hσ : σ * σ = 1) (A : Subgroup G) (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hsq : ∀ x ∈ A, x * x = 1) (hinv : ∀ x ∈ A, σ x ∈ A) :
    Nat.card A ≤ Nat.card (fixedSubgroup σ) ^ 2 := by
  have hσσ : ∀ x, σ (σ x) = x := mulAut_apply_apply_of_mul_self hσ
  let φ : A →* A :=
    { toFun := fun x => ⟨(x : G) * σ x, A.mul_mem x.2 (hinv x x.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hc : (y : G) * σ x = σ x * y := hcomm _ y.2 _ (hinv x x.2)
        change (x : G) * y * σ ((x : G) * y) = (x : G) * σ x * ((y : G) * σ y)
        rw [map_mul]
        calc (x : G) * y * (σ x * σ y) = x * (y * σ x) * σ y := by group
          _ = x * (σ x * y) * σ y := by rw [hc]
          _ = (x : G) * σ x * ((y : G) * σ y) := by group }
  have hkerF : Nat.card φ.ker ≤ Nat.card (fixedSubgroup σ) := by
    refine Nat.card_le_card_of_injective
      (fun x : φ.ker => (⟨((x : A) : G), ?_⟩ : fixedSubgroup σ)) ?_
    · have hx : ((x : A) : G) * σ ((x : A) : G) = 1 := congrArg Subtype.val x.2
      have h1 : σ ((x : A) : G) = ((x : A) : G)⁻¹ := eq_inv_of_mul_eq_one_right hx
      have h2 : ((x : A) : G)⁻¹ = ((x : A) : G) :=
        inv_eq_of_mul_eq_one_right (hsq _ (x : A).2)
      exact h1.trans h2
    · intro x y h
      exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))
  have hrangeF : Nat.card φ.range ≤ Nat.card (fixedSubgroup σ) := by
    refine Nat.card_le_card_of_injective
      (fun y : φ.range => (⟨((y : A) : G), ?_⟩ : fixedSubgroup σ)) ?_
    · obtain ⟨a, x, hx⟩ := y
      change σ (a : G) = a
      rw [← hx]
      change σ ((x : G) * σ x) = (x : G) * σ x
      rw [map_mul, hσσ]
      exact hcomm _ (hinv x x.2) _ x.2
    · intro x y h
      exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))
  have hcard : Nat.card A = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  rw [hcard, sq]
  exact Nat.mul_le_mul hrangeF hkerF

theorem exists_sylow_two_invariant {G : Type*} [Group G] [Finite G] (σ : MulAut G)
    (hσ : σ * σ = 1) : ∃ P : Sylow 2 G, ∀ x ∈ (P : Subgroup G), σ x ∈ (P : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup (MulAut G) := Subgroup.zpowers σ
  have hH : IsPGroup 2 H := by
    have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hσ)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)
  letI : MulAction H (Sylow 2 G) := MulAction.compHom (Sylow 2 G) H.subtype
  have hmod := hH.card_modEq_card_fixedPoints (Sylow 2 G)
  have hone := card_sylow_modEq_one 2 G
  have hodd : Nat.card (MulAction.fixedPoints H (Sylow 2 G)) ≠ 0 := by
    intro h0
    have h1 : Nat.card (Sylow 2 G) ≡ 0 [MOD 2] := by rw [← h0]; exact hmod
    have h2 : 1 ≡ 0 [MOD 2] := hone.symm.trans h1
    exact absurd h2 (by decide)
  obtain ⟨⟨P, hP⟩⟩ := Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hodd) |>.1
  refine ⟨P, fun x hx => ?_⟩
  have hfix : (⟨σ, Subgroup.mem_zpowers σ⟩ : H) • P = P := hP ⟨σ, Subgroup.mem_zpowers σ⟩
  have hsmul : (σ • (P : Subgroup G)) = (P : Subgroup G) := by
    have := congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) hfix
    exact this
  rw [← hsmul]
  exact Subgroup.smul_mem_pointwise_smul x σ _ hx

theorem card_fixedSubgroup_conj_eq {G : Type*} [Group G] (σ c : MulAut G) :
    Nat.card (fixedSubgroup (c⁻¹ * σ * c)) = Nat.card (fixedSubgroup σ) := by
  refine Nat.card_congr (Equiv.subtypeEquiv c.toEquiv fun x => ?_)
  change (c⁻¹ * σ * c) x = x ↔ σ (c x) = c x
  rw [MulAut.mul_apply, MulAut.mul_apply]
  constructor
  · intro h
    have h' := congrArg c h
    rwa [MulAut.apply_inv_self] at h'
  · intro h
    rw [h, MulAut.inv_apply_self]

theorem four_lt_card_fixedSubgroup_of_unique_abelian {G : Type*} [Group G] [Finite G]
    {S₀ A₀ : Subgroup G} (hS : IsPGroup 2 ↥S₀) (hidx : ¬ 2 ∣ S₀.index) (hA₀ : A₀ ≤ S₀)
    (hcomm : ∀ x ∈ A₀, ∀ y ∈ A₀, x * y = y * x) (hsq : ∀ x ∈ A₀, x * x = 1)
    (hcard : 16 < Nat.card A₀)
    (huniq : ∀ B : Subgroup G, B ≤ S₀ → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      Nat.card B = Nat.card A₀ → B = A₀)
    (σ : MulAut G) (hσ : σ * σ = 1) : 4 < Nat.card (fixedSubgroup σ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_two_invariant σ hσ
  let S₀' : Sylow 2 G := hS.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀' P
  have hPeq : (P : Subgroup G) = MulAut.conj g • S₀ := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  set c : MulAut G := MulAut.conj g with hc
  have hmemP : ∀ x : G, x ∈ (P : Subgroup G) ↔ c⁻¹ x ∈ S₀ := by
    intro x
    rw [hPeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
  let τ : MulAut G := c⁻¹ * σ * c
  have hτ : τ * τ = 1 := by
    calc τ * τ = c⁻¹ * (σ * σ) * c := by simp only [τ]; group
      _ = 1 := by rw [hσ]; group
  have hτS : ∀ s ∈ S₀, τ s ∈ S₀ := by
    intro s hs
    have h1 : c s ∈ (P : Subgroup G) := (hmemP _).2 (by rw [MulAut.inv_apply_self]; exact hs)
    exact (hmemP _).1 (hP _ h1)
  have hBS : A₀.map τ.toMonoidHom ≤ S₀ := by
    rintro _ ⟨a, ha, rfl⟩
    exact hτS a (hA₀ ha)
  have hBcomm : ∀ x ∈ A₀.map τ.toMonoidHom, ∀ y ∈ A₀.map τ.toMonoidHom, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    change τ a * τ b = τ b * τ a
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hBcard : Nat.card (A₀.map τ.toMonoidHom) = Nat.card A₀ :=
    Subgroup.card_map_of_injective τ.injective
  have hBA : A₀.map τ.toMonoidHom = A₀ := huniq _ hBS hBcomm hBcard
  have hτinv : ∀ a ∈ A₀, τ a ∈ A₀ := fun a ha => hBA ▸ ⟨a, ha, rfl⟩
  have hle := card_le_card_fixedSubgroup_sq τ hτ A₀ hcomm hsq hτinv
  rw [card_fixedSubgroup_conj_eq σ c] at hle
  by_contra hcon
  have h4 : Nat.card (fixedSubgroup σ) ≤ 4 := not_lt.mp hcon
  have h16 : Nat.card (fixedSubgroup σ) ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left h4 2
  omega

end CFSG.EvenSporadicStandard.Co3Std.CentT
