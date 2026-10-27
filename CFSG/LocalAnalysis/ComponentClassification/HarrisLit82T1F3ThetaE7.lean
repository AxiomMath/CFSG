module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Odd
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7CoreRows
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaExc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Field
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Split

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.HighestRoot (rankOneGroup rankOneGroup_adjDatum)
open CFSG.LieType.AlgebraicGroups (signMaskTuple)

@[expose] def e7GammaLevi : List ((Fin (Tag.rank .E7) → ℤ) × ℤ) :=
  [(Pi.single (e7Node 0) 1, -4), (Pi.single (e7Node 1) 1, 1), (Pi.single (e7Node 2) 1, 3),
    (Pi.single (e7Node 3) 1, -4), (Pi.single (e7Node 4) 1, 4), (Pi.single (e7Node 5) 1, -2)]

theorem e7GammaLevi_reg : ∀ α ∈ rootFinset .E7,
    (∑ j, regCoweight e7GammaLevi j * α j) ≠ 0 ∧
      (∑ j, regCoweight e7GammaLevi j * α j).natAbs < 19 := by
  decide +kernel

theorem e7GammaLevi_nodes :
    ∀ y ∈ e7GammaLevi, ∃ k : Fin 6, y.1 = Pi.single (e7LeviE6Node k) 1 := by
  decide


theorem exists_eq_rootDiagAut_of_odd_fix_e7LeviE6 {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) {β : MulAut (adjointGroup .E7 K)} (hβ : Odd (orderOf β))
    (hfix : ∀ x ∈ e7LeviE6 K, β x = x) :
    ∃ e : Fin (Tag.rank .E7) → Kˣ, β = rootDiagAut .E7 K e := by
  have hL : ∀ (k : Fin 6) (x : adjointGroup .E7 K),
      x ∈ rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7LeviE6Node k) →
        x ∈ e7LeviE6 K := fun k x hx =>
    le_iSup (fun k => rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup
      (e7LeviE6Node k)) k hx
  have hQ : ∀ (k : Fin 6) (u : adjointGroup .E7 K), (u : ModGL .E7 K) ∈
      rootSubgroup .E7 K (Pi.single (e7LeviE6Node k) 1) ⊔
        rootSubgroup .E7 K (-Pi.single (e7LeviE6Node k) 1) → β u = u := by
    intro k u hu
    refine hfix u (hL k u ?_)
    change _ ∈ rankOneGroup (adjDatum (rootOperatorFamily .E7) K) (Pi.single (e7LeviE6Node k) 1)
    rw [rankOneGroup_adjDatum _ (isRoot_single _ _), mem_subgroupOf]
    exact hu
  exact exists_eq_rootDiagAut_of_odd_fix (Or.inr (Or.inl rfl)) hK2 hβ (e7LeviE6Node 0)
    (fun x hx => hfix x (hL 0 x hx)) e7GammaLevi
    (fun y hy => by obtain ⟨k, hk⟩ := e7GammaLevi_nodes y hy; rw [hk]; exact isRoot_single _ _)
    (fun y hy u hu => by
      obtain ⟨k, hk⟩ := e7GammaLevi_nodes y hy
      rw [hk] at hu
      exact hQ k u hu)
    19 (fun α hα => e7GammaLevi_reg α (mem_rootFinset.2 hα))

theorem oddCoreExp_E7_t7 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    OddCoreExp (rootDiagAut .E7 K (bitsTuple e7BitsSix)) (Nat.card K - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (one_le_and_three_le_of_card hp hp2 hK).1 hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine oddCoreExp_of_fix (center_adjointGroup_eq_bot_field .E7 K)
    (isQuasisimple_e7LeviE6 hp hp2 hK) (e7LeviE6_le_fixedSubgroup hK2)
    (fixedSubgroup_le_normalizer_e7LeviE6 hK2) fun β hβ _ hfix => ?_
  obtain ⟨e, rfl⟩ := exists_eq_rootDiagAut_of_odd_fix_e7LeviE6 hK2 hβ hfix
  change (rootDiagAutHom .E7 K e) ^ (Nat.card K - 1) = 1
  have he : e ^ (Nat.card K - 1) = 1 := by
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    exact PSL.units_pow_card_sub_one (e i)
  rw [← map_pow, he, map_one]

theorem burgRowExp_E7_split {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) {m : ℕ} (hm : m = 1 ∨ m = 2 ∨ m = 3) :
    BurgCoreFor (rootDiagAut .E7 K (signMaskTuple .E7 K m)) ∨
      OddCoreExp (rootDiagAut .E7 K (signMaskTuple .E7 K m)) (Nat.card K - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (one_le_and_three_le_of_card hp hp2 hK).1 hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  rcases hm with rfl | rfl | rfl
  · exact Or.inl (by rw [signMaskTuple_one]; exact burgCoreFor_E7_t1 hK2)
  · exact Or.inl (by rw [signMaskTuple_two]; exact burgCoreFor_E7_t4 hK2)
  · rw [signMaskTuple_three]
    obtain ⟨n, hn⟩ := exists_conj_rootDiagAut_three (K := K) hK2
    rw [hn]
    exact Or.inr ((oddCoreExp_E7_t7 hp hp2 hK).conj _)

theorem burgRowExp_E7 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (α : MulAut (adjointGroup .E7 K)) (hα : orderOf α = 2) :
    BurgCoreFor α ∨ OddCoreExp α (Nat.card K - 1) ∨
      ∃ (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ),
        α = MulAut.conj g * rootDiagAut .E7 K a ∧
        (∀ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3) → ∀ ψ : MulAut (adjointGroup .E7 K),
          ψ * α * ψ⁻¹ ≠ rootDiagAut .E7 K (signMaskTuple .E7 K m)) ∧
        pPrimeCore 2 (fixedSubgroup α) ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hf := (one_le_and_three_le_of_card hp hp2 hK).1
  have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα2 : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  rcases LieType.AlgebraicGroups.odd_E7_involution_inner_or_quadratic hodd hα2 with
    ⟨g, a, hga⟩ | ⟨p', e, hp', he, hK', δ, hδ, g, a, hga⟩
  · have hαeq : α = MulAut.conj g * rootDiagAut .E7 K a := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [hga x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    by_cases hsplit : ∃ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3) ∧ ∃ ψ : MulAut (adjointGroup .E7 K),
        ψ * α * ψ⁻¹ = rootDiagAut .E7 K (signMaskTuple .E7 K m)
    · obtain ⟨m, hm, ψ, hψ⟩ := hsplit
      have hback : ψ⁻¹ * rootDiagAut .E7 K (signMaskTuple .E7 K m) * ψ⁻¹⁻¹ = α := by
        rw [← hψ]
        group
      rcases burgRowExp_E7_split hp hp2 hK hm with h | h
      · left
        rw [← hback]
        exact h.conj ψ⁻¹
      · right
        left
        rw [← hback]
        exact h.conj ψ⁻¹
    · push Not at hsplit
      by_cases hcore : pPrimeCore 2 (fixedSubgroup α) = ⊥
      · left
        subst hαeq
        exact TwE7.burgCoreFor_twisted_of_core hp2 hf hK hα hsplit hcore
      · exact Or.inr (Or.inr ⟨g, a, hαeq, hsplit, hcore⟩)
  · exact Or.inl (burgCoreFor_E7_field hp' he hK2 hK' hδ hga hα2)

end CFSG.ComponentClassification.Burgoyne.E2
