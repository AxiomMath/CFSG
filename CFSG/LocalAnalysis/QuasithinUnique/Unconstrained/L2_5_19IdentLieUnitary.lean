module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieBase
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocle

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.OutcomeLocal CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag

theorem tabIdentFor_u3Even
    : TabIdentFor @Ident.FamU3Even := by
  intro G _ _ X K t hs hX
  obtain ⟨hsimple, f, hf3, hmodel⟩ := hX
  exfalso
  obtain ⟨-, F, _, _, hF, ⟨φ0⟩⟩ := hmodel
  have := hsimple
  have : Finite (MulAut ↥X) :=
    Finite.of_injective (fun β : MulAut ↥X => (β : ↥X → ↥X)) fun _ _ h => MulEquiv.ext (congrFun h)
  have hZ := hs.center_eq_bot_of_simple hsimple
  obtain ⟨a, L, ha, hLW, hL, ⟨eL⟩⟩ := hs.exists_socle hsimple
  obtain ⟨p, f', hp, hp2, hf', hsrc⟩ := hs.ktype.exists_psl_two_source_quot eL
  have h : UnitaryFieldData 2 f F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  let φ : ↥(inner ↥X) ≃* unitaryPSU h 3 :=
    (innerEquiv hZ).symm.trans (φ0.trans (unitaryPSUEquiv h (by norm_num)).symm)
  have hq : ¬ (3 = 3 ∧ 2 ^ f = 2) := fun ⟨_, h2⟩ => by
    have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    omega
  obtain ⟨ρ, -, -, -, -, H₀, C, hC, -, θ, -, ρC, -, -, σ, -, -, Cl, hCl, hlet⟩ :=
    faithful_even_unitary_socle_small_source_involution_selector
      (isSimpleGroup_inner hZ) (hs.exists_noncomm_inner hsimple)
      (centralizer_inner_eq_bot_of_center_bot hZ) ha hLW hL hp hp2 hf' (Or.inl hsrc) h
      (n := 3) le_rfl hq φ
  obtain ⟨-, -, -, -, -, -, -, -, hrows, -⟩ := hlet
  rcases hrows with ⟨-, he2, -⟩ | ⟨hn4, -⟩ | ⟨hn5, -⟩
  · omega
  · omega
  · omega

end CFSG.QuasithinUnique.Id2519
