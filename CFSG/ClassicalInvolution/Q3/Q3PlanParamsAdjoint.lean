module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsToral
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLang
public import CFSG.ClassicalInvolution.Q3.Q3PlanParams
public import CFSG.ClassicalInvolution.SmallCases.UpgradeExcRoots
public import CFSG.ClassicalInvolution.SmallCases.UpgradeParamsOrthogonal

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.Generic
open CFSG.Open (IsSubnormal)
open scoped commutatorElement

section Adjoint

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem adjoint_derivedSeries_two_eq_bot
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) (hKodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) {w : ↥(adjointGroup τ K)} (hw : w * w = 1)
    {N : Subgroup ↥(adjointGroup τ K)}
    (hNs : IsSubnormal N (Subgroup.centralizer ({w} : Set ↥(adjointGroup τ K))))
    (hsolv : Group.IsSolvable N) (hodd : IsOddGenerated N) : derivedSeries ↥N 2 = ⊥ := by
  have hK2 : ringChar K ≠ 2 := CFSG.ClassicalInvolution.Upgrade.ringChar_ne_two_of_odd_card hKodd
  obtain ⟨g, b, hb, hgb⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_conj_eq_rootDiagUnit_of_involution hτ hKodd w hw
  set w' : ↥(adjointGroup τ K) := g * w * g⁻¹ with hw'
  let f : ↥(adjointGroup τ K) →* ModGL τ K :=
    (adjointGroup τ K).subtype.comp (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f := (adjointGroup τ K).subtype_injective.comp
    (MulAut.conj g).injective
  have hCeq : (Subgroup.centralizer ({w} : Set ↥(adjointGroup τ K))).map f =
      toralCentralizer τ K b := by
    have h1 := map_centralizer_singleton_mulEquiv₃ (MulAut.conj g) w
    have h2 := CFSG.ClassicalInvolution.ModelFacts.centralizer_eq_subgroupOf_toralCentralizer
      (τ := τ) b w' hgb
    have h3 : (MulAut.conj g) w = w' := by rw [MulAut.conj_apply]
    rw [h3] at h1
    rw [show f = (adjointGroup τ K).subtype.comp (MulAut.conj g).toMonoidHom from rfl,
      ← Subgroup.map_map, h1, h2, Subgroup.map_subgroupOf_eq_of_le
      (CFSG.ClassicalInvolution.ModelFacts.toralCentralizer_le_adjointGroup b)]
  have hJs : IsSubnormal (N.map f) (toralCentralizer τ K b) := by
    rw [← hCeq]
    exact CFSG.ClassicalInvolution.ModelFacts.isSubnormal_map f hNs
  have hJC : N.map f ≤ toralCentralizer τ K b := CFSG.ClassicalInvolution.isSubnormal_le hJs
  have hsolvJ : Group.IsSolvable ↥(N.map f) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective N f hf).symm.toMonoidHom)
      (Subgroup.equivMapOfInjective N f hf).symm.injective
  exact derivedSeries_eq_bot_of_map f hf
    (derivedSeries_two_eq_bot_of_toral hK2 h5 hb hJC hJs hsolvJ (hodd.map f hf))

end Adjoint

theorem false_of_isClassicalMember3_adjoint {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) {r e : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (he : 1 ≤ e) (h5 : 5 ≤ r ^ e) {X : Type} [Group X] [Finite X]
    (ψ : ↥(adjointGroup τ (GaloisField r e)) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center _) {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z) :
    False := by
  have hodd : Odd (Nat.card (GaloisField r e)) :=
    CFSG.ClassicalInvolution.Upgrade.odd_card_galoisField hr2 he
  have h5' : 5 ≤ Nat.card (GaloisField r e) := by
    rw [GaloisField.card r e (by omega)]
    exact h5
  have : Finite (ModGL τ (GaloisField r e)) := finite_modGL
  refine false_of_isClassicalMember3_of_oddGenerated ψ hψ hker ?_ h
  intro w hw N _ hNs hsolv hOdd
  exact adjoint_derivedSeries_two_eq_bot hτ hodd h5' hw hNs hsolv hOdd

theorem classicalMemberParameters3At_G2 : ClassicalMemberParameters3At .G2 := by
  intro n r e hr hr2 hadm hne X _ _ ψ hψ hker L z h
  have : Fact r.Prime := ⟨hr⟩
  exact false_of_isClassicalMember3_adjoint (τ := .G2) (Or.inl rfl) hr2 hadm.2.1
    (five_le_pow_of_odd_prime_of_ne_three hr hr2 hadm.2.1 hne) ψ hψ hker h

theorem classicalMemberParameters3At_F4 : ClassicalMemberParameters3At .F4 := by
  intro n r e hr hr2 hadm hne X _ _ ψ hψ hker L z h
  have : Fact r.Prime := ⟨hr⟩
  exact false_of_isClassicalMember3_adjoint (τ := .F4) (Or.inr (Or.inl rfl)) hr2 hadm.2.1
    (five_le_pow_of_odd_prime_of_ne_three hr hr2 hadm.2.1 hne) ψ hψ hker h

theorem classicalMemberParameters3At_E8 : ClassicalMemberParameters3At .E8 := by
  intro n r e hr hr2 hadm hne X _ _ ψ hψ hker L z h
  have : Fact r.Prime := ⟨hr⟩
  exact false_of_isClassicalMember3_adjoint (τ := .E8) (Or.inr (Or.inr (Or.inr rfl))) hr2
    hadm.2.1 (five_le_pow_of_odd_prime_of_ne_three hr hr2 hadm.2.1 hne) ψ hψ hker h

end CFSG.ClassicalInvolution.Q3
