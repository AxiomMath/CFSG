module

public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
public import CFSG.LinearAlgebra.CoprimeActions.AbelianNormalizerSmallDimension

public section

namespace CFSG.LinearAlgebra.CoprimeActions.SmallModuleSpecialTwoGroup

open CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups

private lemma normalizes_char_small {H : Type*} [Group H] (E U : Subgroup H) (d : H)
    (hd : d ∈ Subgroup.normalizer (E : Set H)) (hUE : U ≤ E)
    (hchar : (U.subgroupOf E).Characteristic) :
    d ∈ Subgroup.normalizer (U : Set H) := by
  have hdQ : ∀ x ∈ E, d * x * d⁻¹ ∈ E := fun x hx => (Subgroup.mem_normalizer_iff.mp hd x).mp hx
  have hdQ' : ∀ x ∈ E, d⁻¹ * x * d ∈ E := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hd)) x
    simpa using this.mp hx
  let φ : E ≃* E :=
    { toFun := fun x => ⟨d * x * d⁻¹, hdQ x x.2⟩
      invFun := fun x => ⟨d⁻¹ * x * d, hdQ' x x.2⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun x => by ext; simp [mul_assoc]
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  have hfix := hchar.fixed φ
  have key : ∀ x ∈ U, d * x * d⁻¹ ∈ U := by
    intro x hx
    have hmem : (⟨x, hUE hx⟩ : E) ∈ U.subgroupOf E := hx
    rw [← hfix] at hmem
    exact hmem
  have hfix' := hchar.fixed φ.symm
  have key' : ∀ x ∈ U, d⁻¹ * x * d ∈ U := by
    intro x hx
    have hmem : (⟨x, hUE hx⟩ : E) ∈ U.subgroupOf E := hx
    rw [← hfix'] at hmem
    exact hmem
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key x hx, fun hx => ?_⟩
  have := key' _ hx
  simpa [mul_assoc] using this

private lemma centralizes_small {F : Type*} {H : Type} {V : Type*} [Field F] [IsAlgClosed F]
    [Group H] [Finite H] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hF : (2 : F) ≠ 0) (ρ : Representation F H V) (hρ : Function.Injective ρ)
    (q : ℕ) (hq : q.Prime) (hdim : Module.finrank F V < q)
    (D E : Subgroup H) (hD : Nat.card D = q) (hE2 : IsPGroup 2 E)
    (hDE : D ≤ Subgroup.normalizer (E : Set H))
    (U : Subgroup H) (hUE : U ≤ E) (hchar : (U.subgroupOf E).Characteristic)
    (hUc : IsMulCommutative U) :
    D ≤ Subgroup.centralizer (U : Set H) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CommGroup U := { (inferInstance : Group U) with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  have hcard : (Nat.card U : F) ≠ 0 := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := E)).mp hE2
    have hdvd : Nat.card U ∣ 2 ^ m := by
      rw [← hm]; exact Subgroup.card_dvd_of_le hUE
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hk]; push_cast; exact pow_ne_zero _ hF
  let τ : Representation F U V := ρ.comp U.subtype
  have hτ : Function.Injective τ := fun a b h => Subtype.ext (hρ h)
  have hpow : ∀ d ∈ D, d ^ q = 1 := by
    intro d hd
    have h1 := orderOf_dvd_natCard (⟨d, hd⟩ : D)
    rw [hD] at h1
    have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
    have := congrArg Subtype.val h2
    simpa using this
  have hD1 : ∀ d ∈ D, d ∈ Subgroup.centralizer (U : Set H) := by
    intro d hd
    have hdN := normalizes_char_small E U d (hDE hd) hUE hchar
    let α : MulAut U :=
      { toFun := fun x => ⟨d * x * d⁻¹, (Subgroup.mem_normalizer_iff.mp hdN (x : H)).mp x.2⟩
        invFun := fun x => ⟨d⁻¹ * x * d, by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) (x : H)).mp x.2
          simpa [mul_assoc] using this⟩
        left_inv := fun x => by ext; simp [mul_assoc]
        right_inv := fun x => by ext; simp [mul_assoc]
        map_mul' := fun x y => by ext; simp [mul_assoc] }
    have hαpow : ∀ n : ℕ, ∀ x : U, ((α ^ n) x : H) = d ^ n * x * (d ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro x; simp
      | succ n ih =>
        intro x
        rw [pow_succ, MulAut.mul_apply]
        rw [ih]
        show d ^ n * (d * x * d⁻¹) * (d ^ n)⁻¹ = d ^ (n + 1) * x * (d ^ (n + 1))⁻¹
        group
    have hα : α ^ q = 1 := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [hαpow q x, hpow d hd]
      simp
    have h1 : ρ d * ρ d⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : ρ d⁻¹ * ρ d = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    let σ : V ≃ₗ[F] V := LinearEquiv.ofLinear (ρ d) (ρ d⁻¹)
      (by rw [← Module.End.mul_eq_comp, h1]; rfl) (by rw [← Module.End.mul_eq_comp, h2]; rfl)
    have hcov : ∀ (g : U) (v : V), σ (τ g v) = τ (α g) (σ v) := by
      intro g v
      show ρ d (ρ (g : H) v) = ρ ((α g : U) : H) (ρ d v)
      have e1 : ((α g : U) : H) = d * g * d⁻¹ := rfl
      rw [e1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    have hα1 : α = 1 := AbelianNormalizerSmallDimension.eq_one τ hτ hcard q hq hdim α hα σ hcov
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h3 : d * x * d⁻¹ = x := by
      have := congrArg (fun φ : MulAut U => ((φ ⟨x, hx⟩ : U) : H)) hα1
      exact this
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  intro d hd
  exact hD1 d hd

theorem special_and_center {F : Type*} {H : Type} {V : Type*} [Field F] [IsAlgClosed F] [Group H] [Finite H]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hF : (2 : F) ≠ 0) (ρ : Representation F H V) (hρ : Function.Injective ρ)
    (q : ℕ) (hq : q.Prime) (hq3 : 3 < q) (hdim : Module.finrank F V < q)
    (D E : Subgroup H) (hD : Nat.card D = q) (hE : E ≠ ⊥) (hE2 : IsPGroup 2 E)
    (hDE : D ≤ Subgroup.normalizer (E : Set H)) (hED : ⁅E, D⁆ = E) :
    IsSpecialPGroup E ∧
      (Subgroup.center E).map E.subtype = E ⊓ Subgroup.centralizer (D : Set H) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hcop : Nat.Coprime 2 (Nat.card D) := by
    rw [hD, Nat.coprime_primes Nat.prime_two hq]
    omega
  rcases exists_characteristic_abelian_not_centralized_or_special_center_eq_centralizer 2 Nat.prime_two E D hE2 hE hcop hDE hED with
    ⟨U, hUE, hchar, hUc, hnot⟩ | h
  · exfalso
    exact hnot (centralizes_small hF ρ hρ q hq hdim D E hD hE2 hDE U hUE hchar hUc)
  · exact h

end CFSG.LinearAlgebra.CoprimeActions.SmallModuleSpecialTwoGroup
