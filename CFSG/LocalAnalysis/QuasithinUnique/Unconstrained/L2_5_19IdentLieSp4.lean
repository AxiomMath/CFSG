module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieBase
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISpSocle

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.OutcomeLocal

theorem tabIdentFor_sp4Even :
    TabIdentFor @Ident.FamSp4Even := by
  intro G _ _ X K t hs hX
  obtain ⟨hsimple, f, hf3, hmodel⟩ := hX
  exfalso
  obtain ⟨-, F, _, _, hF, ⟨φ0⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have := hsimple
  have : Finite (MulAut ↥X) :=
    Finite.of_injective (fun β : MulAut ↥X => (β : ↥X → ↥X)) fun _ _ h => MulEquiv.ext (congrFun h)
  have hZ := hs.center_eq_bot_of_simple hsimple
  obtain ⟨a, L, ha, hLW, hL, ⟨eL⟩⟩ := hs.exists_socle hsimple
  obtain ⟨p, f', hp, hp2, hf', hsrc⟩ := hs.ktype.exists_psl_two_source_quot eL
  let φ : ↥(inner ↥X) ≃* StatedProj (StatedSp 2 F) := (innerEquiv hZ).symm.trans φ0
  obtain ⟨ρ, -, -, -, -, he2, -⟩ :=
    faithful_even_symplectic_socle_small_source_involution_selector
      (isSimpleGroup_inner hZ) (hs.exists_noncomm_inner hsimple)
      (centralizer_inner_eq_bot_of_center_bot hZ) ha hLW hL hp hp2 hf' (Or.inl hsrc)
      (r := 2) (e := f) le_rfl (by omega) (by omega) hF φ
  omega

end CFSG.QuasithinUnique.Id2519
