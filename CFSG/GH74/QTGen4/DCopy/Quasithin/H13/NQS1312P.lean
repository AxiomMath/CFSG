module

public import CFSG.Quasithin.H13.NQS1312P
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS1312D
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS1312J
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS1312Q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3Codim3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem le_of_not_le_normalizer_line_F4
    (h1332 : Stmt13_3_2_F4) (h24 : ASC24OneMoved G) (hA3 : A3Orbits G) (h38 : A38ForSQTK)
    {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    (hΦT : ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s)
    {K : Subgroup G} (hK : K ∈ cComp (lineH Φ)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hQK : ¬ pCoreOf 2 (L ⊔ T) ≤ normalizer (K : Set G)) : K ≤ normalizer (L : Set G) := by
  have hLV : L ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.1
  have hyp : HypC23 (lineH Φ) (pCoreOf 2 (L ⊔ T)) (lineH Φ ⊓ normalizer (L : Set G)) :=
    hypC23_line_F4 h1332 hH hF hΦLs hΦN
  have hKc : CharTwo K :=
    charTwo_of_isSubnormal_line (subnormal_of_mem_cComp hK) (charTwo_lineH hH hF hΦT)
  obtain ⟨S, hS, -, hSQ, -, -, -⟩ := exists_sylow_lineH_F4 h1332 hH hF hΦN
  have hsyl : IsSylowTwoOf (pCoreOf 2 (L ⊔ T) ⊓ K) K :=
    C2Push.isSylowTwoOf_inf_of_not_le_normalizer hyp.radical hS hSQ hK hq hQK
  rcases h24 _ _ _ K hyp hK hKc hq hsyl hQK with hKM | ⟨hchi, -, -⟩
  · exact hKM.trans inf_le_right
  exfalso
  have hK3 := three_dvd_card_of_isChi0Block hchi
  obtain ⟨k₁, hk₁L, x, hxL, hk₁3, hx3, hxk, hk₁τ, hxτ⟩ := exists_e9 hU3 hF hΦLs
  have hk₁H := mem_lineH_of_tau_k (hLV hk₁L) hk₁τ
  obtain ⟨-, hNK⟩ := le_normalizer_of_commute_three hA3 h38 (isSQTKIn_lineN hH) lineH_le_lineN
    lineN_le_normalizer_lineH (cComp_mem_of_subnormal isSubnormal_lineH hK) (le_of_mem_cComp hK)
    hK3 (mem_lineN_of_tau_k2 (hLV hxL) hxτ) (lineH_le_lineN hk₁H) hx3 hk₁3 hxk hk₁H
    (not_mem_lineH_of_tau_k2 (hLV hxL) hxτ)
  exact hQK (hyp.radical.1.trans (lineH_le_lineN.trans hNK))

theorem comp_le_line_F4
    (h1332 : Stmt13_3_2_F4) (h24 : ASC24OneMoved G) (hA3 : A3Orbits G) (h38 : A38ForSQTK)
    (hQ : U3LineComponentExclusionQ_F4)
    {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    (hΦT : ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s)
    {K : Subgroup G} (hK : K ∈ cComp (lineH Φ)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    K ≤ normalizer (L : Set G) := by
  by_cases hQK : pCoreOf 2 (L ⊔ T) ≤ normalizer (K : Set G)
  · have h1552 : b0V Φ (Additive.ofMul ⟨ptOf Φ (vecOf 15), ptOf_mem _⟩)
        (Additive.ofMul ⟨ptOf Φ (vecOf 52), ptOf_mem _⟩) ≠ 0 := by
      rw [b0V_apply, phi_ptOf, phi_ptOf, b0_vecOf, dotB_15_52]
      decide
    exact hQ G T L V z hH hU3 hF (b0V Φ) (b0V_nondegenerate Φ) (b0V_isAlt Φ)
      (b0V_invariant hΦN) _ _ (ptOf_mem _) (ptOf_mem _) h1552 K hK hq hQK
  · exact le_of_not_le_normalizer_line_F4 h1332 h24 hA3 h38 hH hU3 hF hΦLs hΦN hΦT hK hq hQK

end CFSG.Quasithin.H13.U3.NLine

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB NLine
open scoped IsMulCommutative

theorem u3LineComponentExclusion_of_q_F4
    (h1332 : Stmt13_3_2_F4) (h24 : ∀ (G : Type) [Group G] [Finite G], ASC24OneMoved G)
    (hQ : U3LineComponentExclusionQ_F4) : U3LineComponentExclusion_F4 := by
  intro G _ _ T L V z _ hH hU3 hF b hbn hba hbi u v hu hv huv K hK hq
  obtain ⟨hA37, hA38, -⟩ := a3ForSQTK_holds
  have hA3 : A3Orbits G := a3Orbits_of_a37_a38 hA37 hA38
  have hLV : L ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.1
  have hV64 : Nat.card V = 64 := hF.2.2.2.1
  have hV1 : V ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hV64
    norm_num at hV64
  obtain ⟨Φ, -, hΦLs, hΦN, hΦT⟩ := u3_six_module_transport_adapted_F4 h1332 hH hU3 hF
  have huv0 : b0 (Φ (Additive.ofMul ⟨u, hu⟩)) (Φ (Additive.ofMul ⟨v, hv⟩)) ≠ 0 := by
    rwa [← form_eq_b0 hLV hΦLs hV1 hbn hbi]
  obtain ⟨l, hl, hlu, hlv⟩ := exists_conj_line hLV hΦLs hu hv huv0

  have hinv15 : (ptOf Φ (vecOf 15))⁻¹ = ptOf Φ (vecOf 15) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) _ (ptOf_mem _)
  have h15 : l⁻¹ * u * l⁻¹⁻¹ = ptOf Φ (vecOf 15) := by rw [← hlu]; group
  have h52 : l⁻¹ * v * l⁻¹⁻¹ = ptOf Φ (vecOf 52) ∨
      l⁻¹ * v * l⁻¹⁻¹ = ptOf Φ (vecOf 52) * ptOf Φ (vecOf 15) := by
    rcases hlv with h | h
    · left
      rw [← h]
      group
    · right
      have hv' : v = l * ptOf Φ (vecOf 52) * l⁻¹ * u⁻¹ := by rw [h]; group
      rw [hv', ← hlu]
      group
      rw [zpow_neg_one, hinv15]
  have hC : (centralizer ({u, v} : Set G)).map (MulAut.conj l⁻¹).toMonoidHom = lineH Φ := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      have h1 := conj_mem_centralizer_pair hlu hlv hc
      rw [lineH]
      simpa [MulAut.conj_apply, mul_assoc] using h1
    · intro hx
      refine ⟨l * x * l⁻¹, ?_, ?_⟩
      · have h1 := conj_mem_centralizer_pair h15 h52 hx
        simpa [mul_assoc] using h1
      · simp [mul_assoc]

  set K' := K.map (MulAut.conj l⁻¹).toMonoidHom with hK'
  have hK'c : K' ∈ cComp (lineH Φ) := by
    have h1 := cComp_map_mulEquiv (MulAut.conj l⁻¹) hK
    rwa [hC] at h1
  have hq' : CFSG.IsQuasisimple (↥K' ⧸ CFSG.pCore 2 ↥K') := by
    let e : ↥K ≃* ↥K' := K.equivMapOfInjective (MulAut.conj l⁻¹).toMonoidHom
      (MulAut.conj l⁻¹).injective
    have he : (CFSG.pCore 2 ↥K).map e.toMonoidHom = CFSG.pCore 2 ↥K' := CFSG.pCore_map_iso 2 e
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr (CFSG.pCore 2 ↥K) (CFSG.pCore 2 ↥K') e he) hq
  have hK'M := comp_le_line_F4 h1332 (h24 G) hA3 hA38 hQ hH hU3 hF hΦLs hΦN hΦT hK'c hq'

  have hlM : l ∈ normalizer (L : Set G) := Subgroup.le_normalizer hl
  intro k hk
  have h1 : l⁻¹ * k * l ∈ normalizer (L : Set G) :=
    hK'M ⟨k, hk, by simp⟩
  have h2 : l * (l⁻¹ * k * l) * l⁻¹ ∈ normalizer (L : Set G) :=
    mul_mem (mul_mem hlM h1) (inv_mem hlM)
  rwa [show l * (l⁻¹ * k * l) * l⁻¹ = k by group] at h2

end CFSG.Quasithin.H13.U3
