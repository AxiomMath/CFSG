module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347F
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347I
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347O
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347V
public import CFSG.Quasithin.H13.U3S1347Z1
public import CFSG.Quasithin.H13.U3S1347Z2
public import CFSG.Quasithin.H13.U3S1347Z4
public import CFSG.Quasithin.H13.U3S1347Z5

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s1347_concl_iii_F4 (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4)
    (h1228 : Stmt12_2_8_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5_F4) (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big)
    (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hsolv : Group.IsSolvable ↥(H₁ ⊔ H₂))
    (hcomm : ¬ ⁅oTwoRes H₁, oTwoRes H₂⁆ ≤ centralizer (v0Of T H₁ H₂ : Set G)) :
    Concl1347iii T H₁ H₂ := by
  obtain ⟨hH₀, -, -, -, -, hc₁, -⟩ := s1347_one_first_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h
  have hne := s1347_pCoreOf_ne S h hH₀ hc₁ hsolv hcomm
  obtain ⟨hcase, hT4⟩ := s1347_solv_f618 hF hBig S h hH₀ hsolv hne
  have hN := s1347_pPrimeCore_eq S h hH₀ hsolv hne hT4
  have hext : F6.IsExtensionWith (↥(H₁ ⊔ H₂) ⧸ Open.pCore 2 ↥(H₁ ⊔ H₂))
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) fun N => IsPOnePlusTwo 3 ↥N := by
    rcases hcase with he | hext
    · obtain ⟨e⟩ := he
      exact (s1347_not_s3s3 S hH₀ hN hcomm e).elim
    · exact isExtensionWith_of_eq hN hext
  have hcent := s1347_centralizer_eq_of_pPrimeCore S h hH₀ hN
  obtain ⟨K, -, hKn, hK⟩ := s1347_aut_structure S hH₀ hcent hext
  obtain ⟨x, y, hz1, hzc, hexp, hzn⟩ := s1347_exists_z hKn hK
  have hred := s1347_reduced S hH₀
  have : IsMulCommutative ↥(v0Of T H₁ H₂) := hred.2.2.1.1
  have hW2 : ∀ w : ↥(v0Of T H₁ H₂), w ^ 2 = 1 := fun w => Subtype.ext (hred.2.2.1.2 w w.2)
  have h6k := card_range_commAutU3 hW2 hzc hexp
  have hz1' : ((⁅x, y⁆ : ↥K) : MulAut ↥(v0Of T H₁ H₂)) ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hz3 : ((⁅x, y⁆ : ↥K) : MulAut ↥(v0Of T H₁ H₂)) ^ 3 = 1 := by
    have := congrArg Subtype.val (hexp ⁅x, y⁆)
    simpa using this
  obtain ⟨hV64, hzfix⟩ := s1347_card_V0 S h hH₀ hc₁ hT4 hz1' hz3 hzn h6k
  exact ⟨hcent.symm, hext, hV64, s1347_thompsonJ S h hH₀ hc₁ hT4 hV64 hz3 hzfix hzn⟩

theorem s1347_one_F4 (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4)
    (h1228 : Stmt12_2_8_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5_F4) (h1345 : NQS134.Stmt13_4_5_F4) (hF : F6.TheoremF618Cat)
    (hBig : A5.FactF618Big) (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) :
    InH T (H₁ ⊔ H₂) ∧ ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G) ∧
      quasithinOmegaOneCenter T = fsuV1 T V ∧
      cZ T H₁ ⊔ cZ T H₂ = quasithinOmegaOneCenter T ∧ cZ T H₁ ⊓ cZ T H₂ = ⊥ ∧
      Nat.card ↥(cZ T H₁) = 2 ∧ Nat.card ↥(cZ T H₂) = 2 ∧
      (Concl1347i T H₁ H₂ ∨ Concl1347ii T H₁ H₂ ∨ Concl1347iii T H₁ H₂ ∨
        Concl1347iv T H₁ H₂) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := s1347_one_first_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h
  refine ⟨a1, a2, a3, a4, a5, a6, a7, ?_⟩
  by_cases hc : ⁅oTwoRes H₁, oTwoRes H₂⁆ ≤ centralizer (v0Of T H₁ H₂ : Set G)
  · exact Or.inl (s1347_concl_i_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h hc)
  by_cases hsolv : Group.IsSolvable ↥(H₁ ⊔ H₂)
  · exact Or.inr (Or.inr (Or.inl
      (s1347_concl_iii_F4 hedge h1332 h1228 hC58 h317 h56 h135 hF hBig S h hsolv hc)))
  obtain ⟨K₀, hK₀, hN, hloc, hcases, hK₁, hK₂, hsup, hcentK⟩ :=
    s1347_K0_F4 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig S h hsolv
  rcases hcases with hLie | hA6
  · exact Or.inr (Or.inl
      (s1347_concl_ii_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h hK₀ hN hloc hLie hsup))
  · exact Or.inr (Or.inr (Or.inr (s1347_concl_iv_F4 hedge h1332 h1228 hC58 h317 h56 h135 h1345 S
      h hsolv hK₀ hN hA6 hK₁ hK₂ hsup hcentK)))

end CFSG.Quasithin.H13.U3
