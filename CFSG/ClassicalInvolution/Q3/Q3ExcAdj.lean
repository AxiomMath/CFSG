module

public import CFSG.ClassicalInvolution.Q3.Q3ExcToral
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.HighestRoot CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Balance CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

theorem exc3_natCard_galoisField_three : Nat.card (GaloisField 3 1) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [GaloisField.card 3 1 (by norm_num)]
  norm_num

variable {τ : Tag}

theorem exc3_exists_conj_rootGroup_of_member
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    (hU : ∀ χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ, UniqIsolated τ χ)
    {L : Subgroup ↥(adjointGroup τ (GaloisField 3 1))}
    {z : ↥(adjointGroup τ (GaloisField 3 1))} (h : IsClassicalMember3 L z)
    (hO : classicalInvolutionOddCore L = ⊥) :
    ∃ (g : ↥(adjointGroup τ (GaloisField 3 1))) (b : Fin τ.rank → (GaloisField 3 1)ˣ)
      (γ : Fin τ.rank → ℤ) (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      L = (rootGroup (rootOperatorFamily τ) (GaloisField 3 1) γ ⊔
          rootGroup (rootOperatorFamily τ) (GaloisField 3 1) (-γ)).map
          (MulAut.conj g⁻¹).toMonoidHom ∧
        componentRootSpan (GaloisField 3 1) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
          rootSubgroup τ (GaloisField 3 1) γ ⊔ rootSubgroup τ (GaloisField 3 1) (-γ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 := exc3_natCard_galoisField_three
  have hK : ringChar (GaloisField 3 1) ≠ 2 := ringChar_ne_two_of_card_eq_three hK3
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hK3]; decide
  have : Finite (ModGL τ (GaloisField 3 1)) := finite_modGL
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  obtain ⟨g, b, hb, hgz⟩ := exists_conj_eq_rootDiagUnit_of_involution hτ hodd z hz2
  have hL' : IsClassicalMember3 (conjSub g L) (g * z * g⁻¹) := h.conj g
  have hO' : classicalInvolutionOddCore (conjSub g L) = ⊥ :=
    oddCore_eq_bot_of_equiv ((L.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm) hO
  have hCz := centralizer_eq_subgroupOf_toralCentralizer b (g * z * g⁻¹) hgz
  have hXC := toralCentralizer_le_adjointGroup (K := GaloisField 3 1) (τ := τ) b
  have hL'C : conjSub g L ≤ Subgroup.centralizer
      ({g * z * g⁻¹} : Set ↥(adjointGroup τ (GaloisField 3 1))) := isSubnormal_le hL'.subnormal
  obtain ⟨e⟩ := hL'.nonempty_equiv_sl2 hO'
  let eL : SL(2, ZMod 3) ≃* ↥((conjSub g L).map (adjointGroup τ (GaloisField 3 1)).subtype) :=
    e.symm.trans ((conjSub g L).equivMapOfInjective (adjointGroup τ (GaloisField 3 1)).subtype
      (adjointGroup τ (GaloisField 3 1)).subtype_injective)
  have hLX : (conjSub g L).map (adjointGroup τ (GaloisField 3 1)).subtype ≤
      toralCentralizer τ (GaloisField 3 1) b := by
    rintro _ ⟨x, hx, rfl⟩
    have := hCz ▸ hL'C hx
    exact Subgroup.mem_subgroupOf.1 this
  have hsub : IsSubnormal ((conjSub g L).map (adjointGroup τ (GaloisField 3 1)).subtype)
      (toralCentralizer τ (GaloisField 3 1) b) := by
    have h1 := CFSG.ComponentClassification.Components.chain_map
      (adjointGroup τ (GaloisField 3 1)).subtype hL'.subnormal
    rwa [hCz, Subgroup.map_subgroupOf_eq_of_le hXC] at h1
  have hU' := fun i j (hi : ¬ 2 < (componentRoots (maskChar (signTupleBits b)) i).ncard)
      (hj : ¬ 2 < (componentRoots (maskChar (signTupleBits b)) j).ncard) =>
    exc3_small_unique hK (hU (maskChar (signTupleBits b))) i j hi hj
  obtain ⟨γ, hγ, h1, h2⟩ := exc3_exists_rankOne_of_member hK3 hb hU' eL hLX hsub
  refine ⟨g, b, γ, hγ, ?_, h2⟩
  have hL'eq := eq_rootGroup_sup_of_map_eq (rootOperatorFamily τ) hγ.1 (h1.trans h2)
  have hLL : L = (conjSub g L).map (MulAut.conj g⁻¹).toMonoidHom := by
    ext x
    simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hx
      exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, by group⟩
    · rintro ⟨y, ⟨x', hx', rfl⟩, rfl⟩
      convert hx' using 1
      group
  rw [hLL, hL'eq]

theorem exc3_oddCore_centralizer_eq_bot (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    {z : ↥(adjointGroup τ (GaloisField 3 1))} (hz2 : z * z = 1) :
    oddCoreIn (Subgroup.centralizer ({z} : Set ↥(adjointGroup τ (GaloisField 3 1)))) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 := exc3_natCard_galoisField_three
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hK3]; decide
  have : Finite (ModGL τ (GaloisField 3 1)) := finite_modGL
  obtain ⟨g, b, hb, hgz⟩ := exists_conj_eq_rootDiagUnit_of_involution hτ hodd z hz2
  refine oddCoreIn_centralizer_eq_bot_of_mulEquiv
    (MulAut.conj g : ↥(adjointGroup τ (GaloisField 3 1)) ≃* ↥(adjointGroup τ (GaloisField 3 1)))
    z ?_
  have hz' : ((MulAut.conj g) z : ↥(adjointGroup τ (GaloisField 3 1))) = g * z * g⁻¹ := rfl
  rw [hz']
  have hCz := centralizer_eq_subgroupOf_toralCentralizer b (g * z * g⁻¹) hgz
  have hXC := toralCentralizer_le_adjointGroup (K := GaloisField 3 1) (τ := τ) b
  set O := oddCoreIn (Subgroup.centralizer ({g * z * g⁻¹} :
    Set ↥(adjointGroup τ (GaloisField 3 1)))) with hO
  have hN := exc3_oddNormal_eq_bot hK3 hb
    (N := O.map (adjointGroup τ (GaloisField 3 1)).subtype) (by
      rintro _ ⟨x, hx, rfl⟩
      have := hCz ▸ oddCoreIn_le _ hx
      exact Subgroup.mem_subgroupOf.1 this) (by
      rintro x hxX _ ⟨n, hn, rfl⟩
      have hxC : (⟨x, hXC hxX⟩ : ↥(adjointGroup τ (GaloisField 3 1))) ∈
          Subgroup.centralizer ({g * z * g⁻¹} : Set ↥(adjointGroup τ (GaloisField 3 1))) := by
        rw [hCz]
        exact Subgroup.mem_subgroupOf.2 hxX
      exact ⟨⟨x, hXC hxX⟩ * n * ⟨x, hXC hxX⟩⁻¹, conj_mem_oddCoreIn hxC hn, rfl⟩) (by
      rw [Subgroup.card_map_of_injective (adjointGroup τ (GaloisField 3 1)).subtype_injective]
      exact odd_card_oddCoreIn _)
  exact (Subgroup.map_eq_bot_iff_of_injective _
    (adjointGroup τ (GaloisField 3 1)).subtype_injective).mp hN


theorem exc3_involutionOddCore_adjoint_eq_bot
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    (s : ↥(adjointGroup τ (GaloisField 3 1)) ⧸
      Subgroup.center ↥(adjointGroup τ (GaloisField 3 1))) (hs : orderOf s = 2) :
    CFSG.Assembly.Dichotomy.involutionOddCore s = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL τ (GaloisField 3 1)) := finite_modGL
  have hcen : Subgroup.center ↥(adjointGroup τ (GaloisField 3 1)) = ⊥ :=
    center_adjointGroup_eq_bot
  let e : ↥(adjointGroup τ (GaloisField 3 1)) ⧸ Subgroup.center ↥(adjointGroup τ (GaloisField 3 1))
      ≃* ↥(adjointGroup τ (GaloisField 3 1)) :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have hs2 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs, pow_two] at this
  rw [involutionOddCore_eq_oddCoreIn]
  refine oddCoreIn_centralizer_eq_bot_of_mulEquiv e s ?_
  exact exc3_oddCore_centralizer_eq_bot hτ (by rw [← map_mul, hs2, map_one])


end CFSG.ClassicalInvolution.Q3
