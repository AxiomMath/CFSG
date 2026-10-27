module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FourAux.HI
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FourAux.Torus
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FourAux.Plane
public import CFSG.RankThree.PartOne.KE.E7FourStab

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

set_option linter.unusedSectionVars false


theorem e7Four_exists_zeta_five {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] :
    ∃ ζ : Lˣ, orderOf ζ = 5 := by
  have : NeZero ((5 : ℕ) : L) := NeZero.of_not_dvd L (p := 2) (by norm_num)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 5
  have hu : IsUnit ζ := hζ.isUnit (by norm_num)
  have hζu : IsPrimitiveRoot hu.unit 5 := IsPrimitiveRoot.coe_units_iff.1 (by simpa using hζ)
  exact ⟨hu.unit, hζu.eq_orderOf.symm⟩

theorem innerPlaneBalance_adjointE7_five_two (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) : InnerPlaneBalance 5 (adjointGroup .E7 K) := by
  classical
  have hℓ : Nat.Prime 2 := Nat.prime_two
  haveI : Fact (Nat.Prime 2) := ⟨hℓ⟩
  have hf : 1 ≤ 1 := le_rfl
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; rfl
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK'
  let L := AlgebraicClosure K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hpf : ((5 : ℕ) : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by rw [hK]; norm_num
  obtain ⟨F⟩ := exists_e7FourFrame K hf hK' Nat.prime_five (by norm_num) hpf L
  have hstab := e7_stabHyp F hK' Nat.prime_five (by norm_num) hpf
  obtain ⟨ζ, hζ⟩ := e7Four_exists_zeta_five (L := L)
  have hFr : ∀ x : L, iterateFrobenius L 2 1 x = x ^ 2 := fun x => by
    rw [iterateFrobenius_def]; simp
  have hdiv : ∀ cert ∈ e7F4Certs, 5 ∣ Nat.card ↥(rootSpan .E7 L (e7D4Set cert) ⊓
      twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L 2 1)))) := by
    intro cert hcert
    obtain ⟨d, hd, hdord⟩ := exists_order_five_mem_D4 hζ hFr F.hT hcert
    have h1 := orderOf_dvd_natCard (⟨d, hd⟩ : ↥(rootSpan .E7 L (e7D4Set cert) ⊓
      twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L 2 1)))))
    rwa [Subgroup.orderOf_mk, hdord] at h1
  intro E hEin hE hEc H hH
  have hEel : IsElementaryAbelian 5 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 5 E).2 hE
  exact e7_four_hI_pPrime d4TranspositionLayer_E7 F hf hK' Nat.prime_five (by norm_num) hpf hstab
    hdiv H hH E (hEin.trans hH) hEel hEc hEin

theorem e7TwoFiveBalance_holds : E7TwoFiveBalance := by
  intro q hv hq2
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_adjointE7_five_two K (hK.trans hq2))

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
