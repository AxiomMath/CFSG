module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Basic

public noncomputable section

namespace CFSG.HardMathSupport.Lang.D4Three

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.E6Descent

set_option linter.unusedSectionVars false


section InnerSquare

open CFSG.StandardType.RecipeExcLang

theorem coe_conj_mul_exactNormalAut_one {K : Type} [Field K]
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (h : adjointGroup Tag.D4 K) :
    ((MulAut.conj g * exactNormalAut Tag.D4 K a 1 0) h : ModGL Tag.D4 K) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) * (h : ModGL Tag.D4 K) *
        ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a)⁻¹ := by
  have h1 : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL Tag.D4 K) = h := by
    have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
    rw [e1]
    exact Units.ext (entrywise_id (R := K) _)
  rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_exactNormalAut, exactQ_zero, h1]
  group

theorem exists_inner_sq_conj_mul_exactNormalAut_one {K : Type} [Field K]
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) :
    ∃ h : adjointGroup Tag.D4 K,
      (MulAut.conj g * exactNormalAut Tag.D4 K a 1 0) ^ 2 = MulAut.conj h := by
  have hγ : (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a ∈ inndiagGroup Tag.D4 K :=
    mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
  refine ⟨⟨_, sq_mem_adjointGroup_of_mem_inndiagGroup hγ⟩, ?_⟩
  refine MulEquiv.ext fun u => Subtype.ext ?_
  rw [pow_two, MulAut.mul_apply, coe_conj_mul_exactNormalAut_one,
    coe_conj_mul_exactNormalAut_one, MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, pow_two]
  group

end InnerSquare

variable {K : Type} [Field K] [Finite K]

theorem exists_normal_form_of_pow_eq_one (α : MulAut (adjointGroup Tag.D4 K)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hα : α ^ p = 1) :
    ∃ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K),
      α = MulAut.conj g * exactNormalAut Tag.D4 K a σ 0 := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨c, β, hU, hV, rfl⟩ :=
    (exceptional_ordinary_Sylow_opposition Tag.D4 K (ringChar K) w₀ hw₀).2.2.2.2.2 α
  have hA : β ∈ unipotentPairAut Tag.D4 K := ⟨hU, hV⟩
  obtain ⟨π, hπ⟩ := exists_perm_map_simple hA
  have hβp : β ^ p = MulAut.conj (((List.range p).map fun i => (β ^ i) c).prod)⁻¹ := by
    have h1 := conj_mul_pow c β p
    have h2 : MulAut.conj (((List.range p).map fun i => (β ^ i) c).prod) * β ^ p = 1 := by
      rw [← h1, hα]
    rw [eq_inv_of_mul_eq_one_right h2, map_inv]
  have hβpA : β ^ p ∈ unipotentPairAut Tag.D4 K := pow_mem hA p
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag (τ := Tag.D4) (K := K)
    (hβp ▸ hβpA)
  have hπp : π ^ p = 1 := by
    refine perm_map_simple_unique (α := β ^ p) (π := π ^ p) (π' := 1)
      (fun i => map_simplePos_pow (fun j => (hπ j).1) p i) (fun i => ?_)
    rw [hβp, hb, map_simplePosSubgroup_exactNormalAut b 1 0 i]
    rfl
  have hπ24 : π ^ 24 = 1 := by
    have h := pow_card_eq_one (x := π)
    rwa [show Fintype.card (Equiv.Perm (Fin Tag.D4.rank)) = 24 from by decide] at h
  have hgcd : Nat.gcd p 24 = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd hne
    have hqp : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq hp).1 (hqg.trans (Nat.gcd_dvd_left p 24))
    have hp24 : p ∣ 24 := hqp ▸ hqg.trans (Nat.gcd_dvd_right p 24)
    have h24 : p ∣ 2 ^ 3 * 3 := by
      rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num] at hp24
      exact hp24
    rcases hp.dvd_mul.mp h24 with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  have hπ1 : π = 1 := by
    have hdvd : orderOf π ∣ Nat.gcd p 24 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hπp) (orderOf_dvd_of_pow_eq_one hπ24)
    rw [hgcd] at hdvd
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.mp hdvd)
  rw [hπ1] at hπ
  have hπ' : ∀ i, (simplePosSubgroup Tag.D4 K i).map β.toMonoidHom =
        simplePosSubgroup Tag.D4 K ((d4Rho ^ 0) i) ∧
      (simpleNegSubgroup Tag.D4 K i).map β.toMonoidHom =
        simpleNegSubgroup Tag.D4 K ((d4Rho ^ 0) i) := by
    intro i
    simpa using hπ i
  obtain ⟨a, σ, hβ⟩ := exists_normalAut_mul_graph (K := K) hπ'
  refine ⟨c, a, σ, ?_⟩
  rw [hβ, d4Graph_zero, mul_one]

end CFSG.HardMathSupport.Lang.D4Three
