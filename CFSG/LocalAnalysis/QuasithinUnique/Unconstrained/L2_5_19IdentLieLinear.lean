module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieBase
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.OutcomeLocal CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem IsKType.card_ne_twenty_thousand {G : Type} [Group G] {K : Subgroup G} (hK : IsKType K) :
    Nat.card ↥K ≠ 20160 := by
  intro h
  rcases isKType_card hK with h1 | h1 | ⟨p, -, hp7, hp⟩
  · omega
  · omega
  · rw [h] at hp
    have hp40 : p < 40 := by
      by_contra hc
      push Not at hc
      have : 40 * (40 * 40 - 1) ≤ p * (p * p - 1) :=
        Nat.mul_le_mul hc (Nat.sub_le_sub_right (Nat.mul_le_mul hc hc) 1)
      omega
    interval_cases p <;> omega

theorem tabIdentFor_l3Even
    : TabIdentFor @Ident.FamL3Even := by
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
  let φ : ↥(inner ↥X) ≃* projectiveSL 3 F :=
    (innerEquiv hZ).symm.trans (φ0.trans (projectiveSLEquivStatedProj 3 F).symm)
  have hWalt : ∀ m : ℕ, 5 ≤ m → IsEmpty (↥(inner ↥X) ≃* alternatingGroup (Fin m)) := fun m hm =>
    ⟨fun e => (projectiveSL_three_not_alternating hf3 hF m hm).false (φ.symm.trans e)⟩
  obtain ⟨ρ, -, -, -, -, -, -, c, hrows⟩ :=
    faithful_even_higher_linear_socle_small_source_involution_selector
      (isSimpleGroup_inner hZ) (hs.exists_noncomm_inner hsimple)
      (centralizer_inner_eq_bot_of_center_bot hZ) ha hLW hL hp hp2 hf' (Or.inl hsrc) hWalt
      (n := 3) (e := f) le_rfl (by omega) hF φ
  rcases hrows with ⟨σ, hrowsF, -⟩ | ⟨-, -, -, -, -, -, hrowsG⟩
  · rcases hrowsF with ⟨-, he2, -⟩ | ⟨-, he4, -, hL34, -⟩
    · omega
    · have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hL34).1 rfl
      have h20160 : Nat.card ↥L = 20160 := by
        rw [hcard]
        decide +kernel
      exact hs.ktype.card_ne_twenty_thousand (by rw [← Nat.card_congr eL.toEquiv]; exact h20160)
  · rcases hrowsG with ⟨-, he2, -⟩ | ⟨hn5, -⟩
    · omega
    · omega

end CFSG.QuasithinUnique.Id2519
