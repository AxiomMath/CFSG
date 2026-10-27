module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralB4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4SignOrbit
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralC3

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem f4_toralCentralizer_component
    {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K)
    {b : Fin Tag.F4.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1)
    {M : Subgroup (toralCentralizer .F4 K b)} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨ρ, hρ, w, hw, hmap⟩ :=
    exists_conj_toralCentralizer_of_orbitCheck hK2 f4SignOrbitB4_check hb
  have hlen : f4SignRepsB4.length = 3 := rfl
  rw [hlen] at hρ
  have key : ∀ (c : Fin (Tag.rank .F4) → Kˣ),
      (toralCentralizer .F4 K c).map
        (MulAut.conj (canonicalRep (coxeterSystem .F4) K w)).toMonoidHom =
          toralCentralizer .F4 K b →
      (∀ N : Subgroup (toralCentralizer .F4 K c), IsComponent N → OddLieCentralQuotient p N) →
        OddLieCentralQuotient p M := by
    intro c hc hcomp
    let e : toralCentralizer .F4 K c ≃* toralCentralizer .F4 K b :=
      ((toralCentralizer .F4 K c).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hc)
    exact oddLieCentralQuotient_of_mulEquiv (M.equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective) (hcomp _ (LocalCores.isComponent_map_mulEquiv e.symm hM))
  interval_cases ρ
  · exact absurd (eq_one_of_rootChar_smul_eq_one (w := w) (by
      intro v
      rw [hw v]
      congr 1
      funext i
      have h0 : listMask (τ := .F4) (f4SignRepsB4.getD 0 []) i = false := by
        revert i
        decide
      change (if listMask (τ := .F4) (f4SignRepsB4.getD 0 []) i then (-1 : Kˣ) else 1) = 1
      rw [h0]
      rfl)) hb1
  · exact key _ hmap fun N hN => f4_toral_C3_component hp hp2 hK h5 hN
  · exact key _ hmap fun N hN => f4_toral_B4_component hp hp2 hK h5 hN


theorem oddExcInnerDiag_F4_of_five_le
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hKp : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K) {α : MulAut (adjointGroup .F4 K)}
    {g : adjointGroup .F4 K} {a : Fin Tag.F4.rank → Kˣ}
    (hαg : ∀ h : adjointGroup .F4 K, (α h : ModGL .F4 K) = (g : ModGL .F4 K) *
      rootDiagUnit .F4 a * (h : ModGL .F4 K) * (rootDiagUnit .F4 a)⁻¹ * (g : ModGL .F4 K)⁻¹)
    (hαo : orderOf α = 2) {L : Subgroup (fixedSubgroup α)} (hL : IsComponent L) :
    OddLieCentralQuotient p L := by
  have hKodd : Odd (Nat.card K) := by rw [hKp]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ :=
    exists_toralCentralizer_equiv_of_innerDiag (Or.inr (Or.inl rfl)) hKodd hαg hα
  exact oddLieCentralQuotient_of_mulEquiv (L.equivMapOfInjective Θ.toMonoidHom Θ.injective)
    (f4_toralCentralizer_component hp hp2 hKp h5 hb (hb1 hα1)
      (LocalCores.isComponent_map_mulEquiv Θ hL))

end CFSG.ComponentClassification.CatLeafProof
