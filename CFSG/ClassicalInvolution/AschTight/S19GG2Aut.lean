module

public import CFSG.ClassicalInvolution.AschTight.S19FGraph
public import CFSG.ClassicalInvolution.AschTight.S19GTrace

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19F Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

theorem map_eq_self_of_fixes {G : Type*} [Group G] {α : MulAut G} {R : Subgroup G}
    (hfix : ∀ x ∈ R, α x = x) : R.map α.toMonoidHom = R := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change α y ∈ R
    rw [hfix y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, hfix x hx⟩

theorem eq_of_fixes_g2 (hodd : Odd (Nat.card K)) (σ : K →+* K) (β : MulAut ↥(adjointGroup .G2 K))
    (hβ : ∀ u, (β u : ModGL .G2 K) = Units.map (entrywiseHom σ) (u : ModGL .G2 K))
    (g : adjointGroup .G2 K) {R : Subgroup ↥(adjointGroup .G2 K)}
    (hR : R ∈ fundamentalSubgroups .G2 (g2Datum K)) (hfix : ∀ x ∈ R, (MulAut.conj g * β) x = x)
    (c : K) : σ c = c := by
  obtain ⟨i, h, rfl⟩ := exists_eq_conjSub_g2Chart hR
  have hK2 := CFSG.ClassicalInvolution.Balance.Bootstrap.ringChar_ne_two_of_odd_nat_card hodd
  exact eq_of_fixes_conjSub (g2Chart K i) (g2Chart_injective hK2 i) β σ
    (fun A => Subtype.ext (by rw [hβ, coe_g2Chart, coe_g2Chart, simpleRootSL2_entrywise]))
    (fun c hc => linAct_g2Chart hodd i hc) g h hfix c

omit [Finite K] in
theorem eq_one_of_entrywise_id (β : MulAut ↥(adjointGroup .G2 K)) (σ : K →+* K)
    (hβ : ∀ u, (β u : ModGL .G2 K) = Units.map (entrywiseHom σ) (u : ModGL .G2 K))
    (hσ : ∀ c, σ c = c) : β = 1 := by
  have hσ' : σ = RingHom.id K := RingHom.ext hσ
  refine MulEquiv.ext fun u => Subtype.ext ?_
  rw [hβ, hσ', MulAut.one_apply]
  exact Units.ext (entrywise_id _)

theorem exists_conj_of_fixes_g2_ne_three {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (α : MulAut ↥(adjointGroup .G2 K))
    {R : Subgroup ↥(adjointGroup .G2 K)} (hR : R ∈ fundamentalSubgroups .G2 (g2Datum K))
    (hfix : ∀ x ∈ R, α x = x) : ∃ g, α = MulAut.conj g := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨hNF, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hK .G2 (Or.inr ⟨rfl, hp3⟩)
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α
  set β : MulAut ↥(adjointGroup .G2 K) := (MulAut.conj g)⁻¹ * α with hβdef
  have hαβ : α = MulAut.conj g * β := by rw [hβdef, mul_inv_cancel_left]
  have hβ : ∀ u, (β u : ModGL .G2 K) = Units.map (entrywiseHom σ.toRingHom) (u : ModGL .G2 K) := by
    intro u
    have e : β u = g⁻¹ * α u * g := by
      rw [hβdef, MulAut.mul_apply, MulAut.inv_def, MulAut.conj_symm_apply]
    rw [e, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hgσ u]
    group
  refine ⟨g, ?_⟩
  rw [hαβ, eq_one_of_entrywise_id β σ.toRingHom hβ
    (eq_of_fixes_g2 hodd σ.toRingHom β hβ g hR (fun x hx => by rw [← hαβ]; exact hfix x hx)),
    mul_one]

section Three

variable [CharP K CFSG.LieType.Ree.ReeTag.G2.prime]

theorem exists_entrywise_g2FrobAut_pow (b : ℕ) :
    ∃ σ : K →+* K, (∀ c, σ c = c ^ 3 ^ b) ∧ ∀ h : adjointGroup .G2 K,
      ((g2FrobAut K ^ b) h : ModGL .G2 K) = Units.map (entrywiseHom σ) (h : ModGL .G2 K) := by
  have : CharP K 3 := ‹CharP K CFSG.LieType.Ree.ReeTag.G2.prime›
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 3 b)
    ⟨RingHom.injective _, Finite.surjective_of_injective (RingHom.injective _)⟩ with hσdef
  have hσ : ∀ c, σ c = c ^ CFSG.LieType.Ree.ReeTag.G2.prime ^ b := fun c =>
    iterateFrobenius_def 3 b c
  have hEq : exactNormalAut .G2 K 1 σ 0 = g2FrobAut K ^ b :=
    exactNormalAut_one_eq_finiteFrobeniusAut_pow CFSG.LieType.Ree.ReeTag.G2 hσ
  refine ⟨σ.toRingHom, hσ, fun h => ?_⟩
  rw [← hEq, coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one]

theorem exists_conj_of_fixes_g2_three {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (α : MulAut ↥(adjointGroup .G2 K)) {R : Subgroup ↥(adjointGroup .G2 K)}
    (hR : R ∈ fundamentalSubgroups .G2 (g2Datum K)) (hfix : ∀ x ∈ R, α x = x) :
    ∃ g, α = MulAut.conj g := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (by decide : Odd 3).pow
  obtain ⟨-, hNF, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hNF α
  rcases Nat.even_or_odd (k : ℕ) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hφ : CFSG.LieType.Ree.ReeTag.G2.finiteExceptionalAut K ^ (k : ℕ) = g2FrobAut K ^ m := by
      rw [hm, ← two_mul]
      exact finiteExceptionalAut_pow_two_mul CFSG.LieType.Ree.ReeTag.G2 m
    have hαβ : α = (MulAut.conj g : MulAut ↥(adjointGroup .G2 K)) * g2FrobAut K ^ m := by
      have h := hgk
      rw [hφ] at h
      exact h
    obtain ⟨σ, -, hσ⟩ := exists_entrywise_g2FrobAut_pow (K := K) m
    refine ⟨g, ?_⟩
    rw [hαβ, eq_one_of_entrywise_id _ σ hσ (eq_of_fixes_g2 hodd σ _ hσ g hR
      (fun x hx => by rw [← hαβ]; exact hfix x hx)), mul_one]
  · have hφ : CFSG.LieType.Ree.ReeTag.G2.finiteExceptionalAut K ^ (k : ℕ) = g2ReeAut K m := by
      rw [hm, pow_succ', finiteExceptionalAut_pow_two_mul CFSG.LieType.Ree.ReeTag.G2 m]
      rfl
    have hαβ : α = (MulAut.conj g : MulAut ↥(adjointGroup .G2 K)) * g2ReeAut K m := by
      have h := hgk
      rw [hφ] at h
      exact h
    have hαR := map_eq_self_of_fixes hfix
    rw [hαβ] at hαR
    exact absurd hαR (graphInvolution_not_normalize m g hR)

end Three

theorem exists_conj_of_fixes_g2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (α : MulAut ↥(adjointGroup .G2 (GaloisField p e)))
    {R : Subgroup ↥(adjointGroup .G2 (GaloisField p e))}
    (hR : R ∈ fundamentalSubgroups .G2 (g2Datum (GaloisField p e))) (hfix : ∀ x ∈ R, α x = x) :
    ∃ g, α = MulAut.conj g := by
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  by_cases h3 : p = 3
  · subst h3
    have : CharP (GaloisField 3 e) CFSG.LieType.Ree.ReeTag.G2.prime :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_three he hK
    exact exists_conj_of_fixes_g2_three he hK α hR hfix
  · exact exists_conj_of_fixes_g2_ne_three Fact.out hp2 h3 he hK α hR hfix

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19G
