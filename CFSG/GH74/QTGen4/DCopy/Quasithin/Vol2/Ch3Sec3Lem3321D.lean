module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321Steps
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321D

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

namespace L3321

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem step3_3_21d_of_F4 (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h14 : Stmt3_3_14_F4) :
    Step3_3_21d_F4 := by
  intro G _ _ T M L D h ⟨e⟩ hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨hVe, -, -, hVO, hOR, hRT, -⟩ := setting_facts h hTL
  have hJC : thompsonJ (rD T L) ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    iSup₂_le fun A hA => le_centralizer_of_isMaxElemAbelian h9 h hML hTL e hmod hA
  have h7' := (h7 G T M L D h).1.2
  rw [hML] at h7'
  have hJO : thompsonJ (rD T L) ≤ pCoreOf 2 (L ⊔ T) := by
    rw [← h7']
    exact le_inf ((thompsonJ_le_self _).trans hRT) hJC
  have hJeq : thompsonJ (rD T L) = thompsonJ (pCoreOf 2 (L ⊔ T)) := thompsonJ_eq_of_le hJO hOR
  intro g hg
  have hgJ : g ∈ Subgroup.normalizer (thompsonJ (rD T L) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (cjSub_thompsonJ hg)
  rw [hJeq] at hgJ
  refine L3322.normalizer_le_M h5 h hML ?_ ?_ ?_ hgJ
  ·
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian (pCoreOf 2 (L ⊔ T))
    have hAJ : A ≤ thompsonJ (pCoreOf 2 (L ⊔ T)) := le_iSup₂_of_le A hA le_rfl
    intro hbot
    rw [hbot, le_bot_iff] at hAJ
    have hVA := hA.2.2 (vPlus L T) hVO hVe
    rw [hAJ, Subgroup.card_bot] at hVA
    have hsubV : Subsingleton ↥(vPlus L T) := Finite.card_le_one_iff_subsingleton.1 hVA
    have hsub : Subsingleton (MulAut ↥(vPlus L T)) :=
      ⟨fun a b => MulEquiv.ext fun v => Subsingleton.elim _ _⟩
    have h1 : Nat.card ↥(autOn L (vPlus L T)) ≤ 1 := by
      have : Subsingleton ↥(autOn L (vPlus L T)) :=
        ⟨fun a b => Subtype.ext (Subsingleton.elim (a : MulAut ↥(vPlus L T)) b)⟩
      exact Finite.card_le_one_iff_subsingleton.2 this
    rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 4 (Or.inl rfl)] at h1
    norm_num at h1
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le (thompsonJ_le_self _)
  · intro x hx
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2
      (cjSub_thompsonJ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) hx))

end L3321

end CFSG.Quasithin.H13
