module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenRankTwo
public import CFSG.Milestones.ASVolI.F4Native

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPGen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.Quasithin.H13.F431.TwoF4 CFSG.ASVolI.ChF.ExceptionalRoots

theorem hasParGen_gm
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : HasParGen (Gm K a) := by
  haveI : Finite (ModGL F4.tag K) := finite_modGL
  haveI : Finite (Gm K a) := Subtype.finite
  exact hasParGen_of_rankTwoSystem (CFSG.ASVolI.burnsideF4h_ree_system hK) (isSylowTwoOf_Ug hK)

theorem commutator_reeGroup_eq
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : ⁅reeGroup K a, reeGroup K a⁆ = reeGroup K a := by
  have h1 : _root_.commutator (F4.reeGamma K a) = ⊤ := commutator_reeGamma_eq_top ha hK
  have h2 : F4.reeGamma K a = reeGroup K a :=
    reeGamma_eq_reeFixedGroup (t := F4) (K := K) (a := a)
  have h3 := Subgroup.map_subtype_commutator (F4.reeGamma K a)
  rw [h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h3
  rw [← h2]
  exact h3.symm

theorem hasParGen_of_reeModel_twistedF4
    {G : Type} [Group G] [Finite G] {f : ℕ} (h : ReeTitsModel G .twistedF4 2 f) :
    HasParGen G := by
  obtain ⟨⟨-, -, -, -, -, hf3⟩, a, hfa, K, _, _, hK, ⟨e⟩⟩ := h
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : CharP K F4.prime := inferInstanceAs (CharP K 2)
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have ha : 1 ≤ a := by omega
  have hperf := commutator_reeGroup_eq ha hK'
  let E' : ↥⁅reeGroup K a, reeGroup K a⁆ ≃* ↥(reeGroup K a) := MulEquiv.subgroupCongr hperf
  let iso : CFSG.Blueprint.DerivedCentralQuotient (reeGroup K a) ≃*
      (↥(reeGroup K a) ⧸ Subgroup.center ↥(reeGroup K a)) :=
    QuotientGroup.congr _ _ E' (Subgroup.map_center_eq E')
  obtain ⟨Φ, -⟩ := CFSG.ASVolI.burnsideF4h_ree_exists_iso hK'
  haveI : Finite (ModGL F4.tag K) := finite_modGL
  haveI : Finite (Gm K a) := Subtype.finite
  exact hasParGen_of_mulEquiv ((e.trans iso).trans Φ.symm).symm (hasParGen_gm hK')

end KPGen

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
