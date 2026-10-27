module

public import CFSG.Quasithin.H13.A5S136ab2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136j

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem false_of_comm_le_F4 (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4) (h1336 : Input1336_F4)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) (h : ⁅pCoreOf 2 L, L⁆ ≤ V) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  have hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of S.isPGroup_T S.T_le_NL
      (S.omegaOneCenter_inf_centralizer_L_F4 h331 h1327)
  have hO : pCoreOf 2 (L ⊔ T) ≤ V :=
    S.pCoreOf_LT_le_V (S.isBlock2_of_comm_le h) (S.isAltType_of_comm_le h) hCTL
  have hOM : pCoreOf 2 M ≤ V := by
    refine le_trans ?_ hO
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (S.pCoreOf_M_le_T.trans le_sup_right)
      ((sup_le Subgroup.le_normalizer S.T_le_NL).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)

  have hCV : Subgroup.centralizer (V : Set G) ≤ V := by
    intro c hc
    have hcM : c ∈ M := S.NV_le_M (Subgroup.centralizer_le_normalizer _ hc)
    have hcC : c ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
      Subgroup.centralizer_le hOM hc
    exact hOM (S.charTwo_M ⟨hcM, hcC⟩)

  have hconj : ∀ g ∈ S.G1, ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    intro g hg v hv
    refine hCV ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : g * v * g⁻¹ ∈ conjClosure V S.G1 := mem_conjClosure hg hv
    have h2 : u ∈ conjClosure V S.G1 := le_conjClosure _ _ hu
    exact congrArg Subtype.val (hab.1.is_comm.comm ⟨u, h2⟩ ⟨_, h1⟩)
  refine h1336 G T L V S fun g hg => S.NV_le_M ?_
  refine B6.mem_normalizer_of_forall_mem (hconj g hg) fun v hv => ?_
  simpa using hconj g⁻¹ (S.G1.inv_mem hg) v hv

theorem false_of_alt6_F4 (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4) (h1336 : Input1336_F4)
    (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : Vol2Native.A38ForSQTKCat)
    (hKF : KnownFacts15122Types) (hab : IsElemAbelian 2 (conjClosure V S.G1)) {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (e : ↥K ≃* alternatingGroup (Fin 6)) : False := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hKG : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
  have hqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hKG)).1 hK.2.1
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimp : IsSimpleGroup ↥K := e.isSimpleGroup
  let e₀ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq (ConfAB.pCore_two_eq_bot_of_simple hqs hsimp)).trans
      QuotientGroup.quotientBot
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hqs
  have hLvK := S.Lv_le_of_exclusion_quot hF318 h36 h38 hKc hq (e₀.trans e) hKF.alt6
  exact S.false_of_comm_le_F4 h331 h1327 h1336 hab (S.commutator_pCoreOf_L_le_V hLvK e)

end Setting

end CFSG.Quasithin.H13.A5
