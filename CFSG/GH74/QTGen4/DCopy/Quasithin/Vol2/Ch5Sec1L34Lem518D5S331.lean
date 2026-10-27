module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518D5TS331
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement Pointwise

section Setting

variable {G : Type} [Group G]

namespace Setting518D5

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D D₃ D₅ : Subgroup G} {n : ℕ}
  (s : Setting518D5 G T M L V H B D D₃ D₅ n)
include s

theorem parabolic_facts_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact)
    {U : Subgroup G} (hU : ParData518 T H B D U) :
    T ⊓ Subgroup.normalizer (U : Set G) ≤
        Subgroup.normalizer (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) : Set G) ∧
      oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ∈
        lFamily (T ⊓ Subgroup.normalizer (U : Set G)) ∧
      Nonempty (↥(oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G))) ⧸
        CFSG.pCore 2 ↥(oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G))) ≃*
          alternatingGroup (Fin 5)) ∧
      B ≤ oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ∧
      B ≤ Subgroup.normalizer (((T ⊓ Subgroup.normalizer (U : Set G)) ⊓
        oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  set K₂ := oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) with hK₂def
  obtain ⟨hST, -, hTKS, -, -, -⟩ := s.S_facts_F4 h510 h331 hR
  obtain ⟨-, hUTK, hUN, φ, hφs, hφk⟩ := hU
  have hTK := h.isSylowTwoOf_inf_K
  have hTKN : T ⊓ oTwoUpper H ≤ Subgroup.normalizer (U : Set G) :=
    hTKS.trans (le_sup_right.trans hUN)
  obtain ⟨hL2K₂, -, -, -, -⟩ := oTwoUpper_parabolic_facts rfl hTK hUTK hTKN φ hφs hφk
  have hTMp := h.T_le_Mp
  have hT₀K₂ : T ⊓ Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K₂ : Set G) :=
    fun x hx => Hyp5_1_14.mem_normalizer_oTwoUpper_inf (hTMp hx.1) hx.2
  obtain ⟨e⟩ := hL2K₂
  have e' : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 2 2) := (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K₂ 2)).trans e
  have := isSimpleGroup_psl24
  obtain ⟨eA⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five
    (G := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) card_psl24'
  have hq : CFSG.IsQuasisimple (↥K₂ ⧸ CFSG.pCore 2 ↥K₂) := isQuasisimple_of_nonempty_psl24 ⟨e'⟩
  have hsub : IsSubnormal K₂ (K₂ ⊔ (T ⊓ Subgroup.normalizer (U : Set G))) :=
    A4.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hT₀K₂))
  have hlfam : K₂ ∈ lFamily (T ⊓ Subgroup.normalizer (U : Set G)) :=
    mem_cComp_of_quasisimple_quotient (oTwoUpper_eq_top_of_isPGroup _) hq hsub
  have hBK₂ : B ≤ K₂ := by
    intro b hb
    have hodd : Odd (orderOf b) := h.notation59.1.2.1.of_dvd_nat
      (by rw [← Subgroup.orderOf_mk b hb]; exact orderOf_dvd_natCard _)
    exact mem_oTwoUpper_of_odd ⟨h.mem_K_of_mem_B hb,
      hUN (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))⟩ hodd
  have hBT : B ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) :=
    (le_sup_right.trans le_sup_left).trans
      (h.DBT_le_normalizer_inf_K_of_le_F4 h510 (d518_le H D) (d518_le_Mp H D))
  have hK₂K : K₂ ≤ oTwoUpper H := (oTwoUpper_le _).trans inf_le_left
  have heq : (T ⊓ Subgroup.normalizer (U : Set G)) ⊓ K₂ = (T ⊓ oTwoUpper H) ⊓ K₂ := by
    apply le_antisymm
    · exact le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans hK₂K)) inf_le_right
    · exact le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans hTKN))
        inf_le_right
  refine ⟨hT₀K₂, hlfam, ⟨e'.trans eA⟩, hBK₂, ?_⟩
  rw [heq]
  exact fun b hb => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hBT hb, Subgroup.le_normalizer (hBK₂ hb)⟩

theorem pCoreOf_X₁_ne_bot_F4 (hF : L2TorusFact) (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) {U : Subgroup G}
    (hO : pCoreOf 2 (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅) ≠ ⊥) :
    pCoreOf 2 ((oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔ sd5 T L H B D D₅) ⊔
      (T ⊓ Subgroup.normalizer (U : Set G))) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hSN⟩ := s.S_facts_F4 h510 h331 hR
  have hTMp := s.hyp.T_le_Mp
  have hT₀X : T ⊓ Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer
      ((oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔ sd5 T L H B D D₅ :
        Subgroup G) : Set G) :=
    le_normalizer_sup_of_le
      (fun x hx => Hyp5_1_14.mem_normalizer_oTwoUpper_inf (hTMp hx.1) hx.2)
      (inf_le_left.trans (le_normalizer_sup_of_le (s.T_le_normalizer_z518 hF)
        (le_sup_right.trans hSN)))
  have hOX := le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le 2 (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅)).trans (le_sup_left (b := T ⊓ Subgroup.normalizer (U : Set G))))
    ((sup_le Subgroup.le_normalizer hT₀X).trans (normalizer_le_normalizer_pCoreOf 2 _))
    (pCoreOf_isPGroup 2 _)
  intro h0
  rw [h0] at hOX
  exact hO (le_bot_iff.mp hOX)

end Setting518D5

end Setting

end CFSG.Quasithin.H13
