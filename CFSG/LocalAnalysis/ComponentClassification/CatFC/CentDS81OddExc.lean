module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddToral
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddFam
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeafProof

set_option linter.unusedSectionVars false


theorem oddDichotomyFamily_of_toral {t : StatedLieTag} {τ : Tag}
    (ht : t ∈ chevalleyExceptionalTags) (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    (hmodel : ∀ (J : Type) [Group J] (p f : ℕ), ChevalleyExceptionalModel J t p f →
      UntwistedChevalleyModel J τ (p ^ f)) :
    OddDichotomyFamily t := by
  intro X _ _ n p f hp hp2 hadm hX z hz
  obtain ⟨K, _, _, hK, ⟨E⟩⟩ := nonempty_mulEquiv_adjointGroup τ
    (hmodel X p f (hX.chevalleyExceptionalModel ht))
  have hf : 1 ≤ f := hadm.2.1
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  set z' : adjointGroup τ K := E z with hz'def
  have hz' : orderOf z' = 2 := (orderOf_injective E.toMonoidHom E.injective z).trans hz
  set α : MulAut (adjointGroup τ K) := MulAut.conj z' with hαdef
  have hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      (z' : ModGL τ K) * rootDiagUnit τ (1 : Fin τ.rank → Kˣ) * (h : ModGL τ K) *
        (rootDiagUnit τ (1 : Fin τ.rank → Kˣ))⁻¹ * (z' : ModGL τ K)⁻¹ := by
    intro h
    rw [rootDiagUnit_one, mul_one, inv_one, mul_one]
    rfl
  have hα : α ^ 2 = 1 := by
    rw [hαdef, ← map_pow, ← hz', pow_orderOf_eq_one, map_one]
  obtain ⟨b, hb, -, ⟨Θ₁⟩⟩ := exists_toralCentralizer_equiv_of_innerDiag hτ hKodd hαg hα
  have hfix : (centralizer ({z} : Set X)).map E.toMonoidHom =
      FixedCommutingProduct.fixedSubgroup α := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 hx
      change z' * E x * z'⁻¹ = E x
      rw [hz'def, ← map_inv, ← map_mul, ← map_mul, ← hx', mul_inv_cancel_right]
    · intro hy
      have hy' : z' * y * z'⁻¹ = y := hy
      refine ⟨E.symm y, Subgroup.mem_centralizer_singleton_iff.2 (E.injective ?_),
        E.apply_symm_apply y⟩
      rw [map_mul, map_mul, E.apply_symm_apply, ← hz'def]
      calc y * z' = z' * y * z'⁻¹ * z' := by rw [hy']
        _ = z' * y := by group
  let Θ₀ : centralizer ({z} : Set X) ≃* FixedCommutingProduct.fixedSubgroup α :=
    ((centralizer ({z} : Set X)).equivMapOfInjective E.toMonoidHom E.injective).trans
      (MulEquiv.subgroupCongr hfix)
  exact HasCompOrSolv.of_mulEquiv (Θ₀.trans Θ₁).symm
    (hasCompOrSolv_toralCentralizer τ hK2 b hb)

theorem oddDichotomyFamily_G2 : OddDichotomyFamily .G2 :=
  oddDichotomyFamily_of_toral (τ := .G2) (by decide) (Or.inl rfl) (fun _ _ _ _ h => h.2)

theorem oddDichotomyFamily_F4 : OddDichotomyFamily .F4 :=
  oddDichotomyFamily_of_toral (τ := .F4) (by decide) (Or.inr (Or.inl rfl))
    (fun _ _ _ _ h => h.2)

theorem oddDichotomyFamily_E6 : OddDichotomyFamily .E6 :=
  oddDichotomyFamily_of_toral (τ := .E6) (by decide) (Or.inr (Or.inr (Or.inl rfl)))
    (fun _ _ _ _ h => h.2)

theorem oddDichotomyFamily_E8 : OddDichotomyFamily .E8 :=
  oddDichotomyFamily_of_toral (τ := .E8) (by decide) (Or.inr (Or.inr (Or.inr rfl)))
    (fun _ _ _ _ h => h.2)

end CFSG.ComponentClassification.CatFC.DS81
