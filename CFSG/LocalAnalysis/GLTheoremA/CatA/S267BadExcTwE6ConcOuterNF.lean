module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenB
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.BorelTits.UnitaryForm
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcG2
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267CenterMultiplier
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)


variable {Ω : Type} [Group Ω] {S : Subgroup Ω}

theorem exists_fieldTransport_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiag : ¬ p ∣ Nat.gcd 3 (ℓ ^ f + 1)) {φ : ↥(twistedE6RootGroup K σ) →* Ω}
    (hφ : Function.Injective φ) (hφS : φ.range = S) {b : Ω} (hbp : b ^ p = 1)
    {β : MulAut ↥(twistedE6RootGroup K σ)}
    (hβ : β ∉ (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)).range)
    (hβφ : ∀ x, φ (β x) = b * φ x * b⁻¹) :
    ∃ (ε : K ≃+* K) (φ' : ↥(twistedE6RootGroup K σ) →* Ω), orderOf ε = p ∧
      fieldActor σ ε ∉
        (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)).range ∧
      Function.Injective φ' ∧ φ'.range = S ∧
      ∀ x, b * φ' x * b⁻¹ = φ' (fieldActor σ ε x) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hβk : ∀ k : ℕ, ∀ x, φ ((β ^ k) x) = b ^ k * φ x * (b ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ β k, MulAut.mul_apply, ih, hβφ, pow_succ b k]
      group
  have hβp : β ^ p = 1 := by
    refine MulEquiv.ext fun x => hφ ?_
    rw [hβk p x, hbp, one_mul, inv_one, mul_one, MulAut.one_apply]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hη1 : Θ β ≠ 1 := by
    intro h1
    have hmem : β ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    exact hβ (CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_inn_sup_diag hp hK hσ hdiag
      hcube hβp hmem)
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, ψ, -, hψβ⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_conj_of_prime_order hℓ hf K hK'
      σ hσ Θ hΘ hp hp2 β hβp hη1
  have hεo : orderOf (Θ β) = p := orderOf_eq_prime (by rw [← map_pow, hβp, map_one]) hη1
  refine ⟨Θ β, φ.comp ψ.symm.toMonoidHom, hεo, ?_, hφ.comp ψ.symm.injective, ?_, fun x => ?_⟩
  · rintro ⟨g, hg⟩
    refine hβ ⟨ψ⁻¹ g, MulEquiv.ext fun x => ?_⟩
    have h1 : β = ψ⁻¹ * fieldActor σ (Θ β) * ψ := by rw [← hψβ]; group
    rw [h1, ← hg, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
      map_mul, map_mul, map_inv, MulAut.inv_apply_self]
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 ψ.symm.surjective,
      ← MonoidHom.range_eq_map, hφS]
  · rw [← hψβ, MulAut.mul_apply, MulAut.mul_apply]
    change b * φ (ψ.symm x) * b⁻¹ = φ (ψ.symm (ψ (β (ψ.symm x))))
    rw [MulEquiv.symm_apply_apply, hβφ]

variable [Finite Ω] {B : Subgroup Ω}

theorem concA_of_twistedE6_of_outer_of_modelBGen {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdiag : ¬ p ∣ Nat.gcd 3 (ℓ ^ f + 1)) (hn : 2 ≤ n)
    (hS : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (hBc : Nat.card B = p ^ (n + 2))
    (eX : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) ≃* PSimple p S)
    (hX : ∀ F : Subgroup ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)), IsElemAbelian p F →
      Nat.card F ≤ p ^ n)
    (hM : ∀ ε : K ≃+* K, orderOf ε = p →
      fieldActor (unitaryInvolution K ℓ f) ε ∉
        (MulAut.conj : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
          MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range →
      ModelGen.ModelBGen p n ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))
        (fieldActor (unitaryInvolution K ℓ f) ε)) :
    S267ConcA p S B := by
  set eS : PSimple p S ≃* ↥S := (psimpleEquivCenterQuotOfCore hcore).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) with heS
  set φ : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →* Ω :=
    S.subtype.comp (eX.trans eS).toMonoidHom with hφdef
  have hφ : Function.Injective φ := S.subtype_injective.comp (eX.trans eS).injective
  have hφS : φ.range = S := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (eX.trans eS).surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  haveI : Finite ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := Finite.of_injective φ hφ
  have hZX : Subgroup.center ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) = ⊥ :=
    center_graphFixedRootGroup_eq_bot (unitaryInvolution K ℓ f).surjective
  obtain ⟨b, hb, β, hβ, hβφ⟩ := exists_outer_mem_of_card hp hS hcore hB hBc hBC φ hφ hφS hZX hX
  obtain ⟨ε, φ', hε, hout, hφ', hφ'S, hbφ'⟩ := exists_fieldTransport_twistedE6 Fact.out hf hK
    (unitaryInvolution_apply K ℓ f) hp hp2 hdiag hφ hφS (hB.2 b hb) hβ hβφ
  exact ModelGen.concA_of_modelBGen hp hn hS hcore hZ hB hBC hBc.le φ' hφ' hφ'S (hB.2 b hb)
    (fun c hc => congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc.1⟩)) hbφ'
    (hM ε hε hout)

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer

end
