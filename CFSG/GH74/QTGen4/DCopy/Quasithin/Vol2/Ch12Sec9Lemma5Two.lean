module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Two
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma6

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

namespace L1295B

section Star

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T V L V₁ Vp H K : Subgroup G}

end Star

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {n : ℕ} {V₁ K₁ : Subgroup G}

theorem T_le_normalizer_F4 (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hcx : Cx1291 G T L V n) (hV₁ : IsTSub T V V₁ 1) (hLK : lOne L V₁ ≤ K₁)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G))) :
    T ≤ Subgroup.normalizer (K₁ : Set G) := by
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  exact hV₁.2.2.trans (normalizer_le_of_lOne_le_F4 h1222 h37 h38 hcx.hyp hn hV₁ hLK hK)

theorem hypF918_F4 (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hcx : Cx1291 G T L V n) (hV₁ : IsTSub T V V₁ 1) (hU : IsMulCommutative ↥(u128 V V₁))
    (hLK : lOne L V₁ ≤ K₁) (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hHz : IsHzOne T L V₁ (K₁ ⊔ T)) (hq : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) :
    HypF918 T V L V₁ V (K₁ ⊔ T) K₁ := by
  have hTK := T_le_normalizer_F4 h1222 h37 h38 hcx hV₁ hLK hK
  have hq' : CFSG.IsQuasisimple (↥K₁ ⧸ (pCoreOf 2 K₁).subgroupOf K₁) := by
    have e : (pCoreOf 2 K₁).subgroupOf K₁ = CFSG.pCore 2 ↥K₁ := by
      rw [pCoreOf, map_subtype_subgroupOf']
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq e.symm) hq
  refine
    { toHypF98 := L1286.hypF98_of_abelian_F4 h1222 h37 h38 h39 hcx.hyp hV₁ hU hHz
      K_cComp := mem_cComp_sup hK hTK
      K_quasisimple := hq'
      H_eq := ?_
      K₀_normal := ?_ }
  · rw [conjClosure_eq hTK]
    exact le_antisymm (sup_le le_sup_left ((le_inf le_sup_right le_sup_right).trans le_sup_right))
      (sup_le le_sup_left inf_le_right)
  · rw [conjClosure_eq hTK]
    exact sup_le Subgroup.le_normalizer hTK

theorem fourList_of_simple_F4 (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hcx : Cx1291 G T L V n)
    (hV₁ : IsTSub T V V₁ 1) (hU : IsMulCommutative ↥(u128 V V₁)) (hLK : lOne L V₁ ≤ K₁)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hHz : IsHzOne T L V₁ (K₁ ⊔ T)) (hS : IsSimpleGroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) :
    FourList (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
  have hperf : Group.IsPerfect (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
    have hK' : Group.IsPerfect ↥K₁ := Subgroup.isPerfect_iff.mpr hK.2.1
    exact Group.IsPerfect.ofSurjective (G := ↥K₁) (f := QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
  have hF := hypF918_F4 h1222 h37 h38 h39 hcx hV₁ hU hLK hK hHz (isQuasisimple_of_simple hperf hS)
  have hTK := T_le_normalizer_F4 h1222 h37 h38 hcx hV₁ hLK hK
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have h4 := (F918_4' hF (sqtkGroup hcx hHz) (conjClosure_eq hTK) hV₁I hIU W hW hirrU hD310
    hD391 hI4).1
  obtain ⟨e⟩ := nonempty_mulEquiv_autIH hF

  have hSA : IsSimpleGroup ↥(autIH V₁ V (K₁ ⊔ T) K₁) := MulEquiv.isSimpleGroup e.symm
  have hperfA : Group.IsPerfect ↥(autIH V₁ V (K₁ ⊔ T) K₁) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hZ : Subgroup.center ↥(autIH V₁ V (K₁ ⊔ T) K₁) = ⊥ :=
    (center_eq_bot_of_simple hperfA hSA).2
  exact fourList_congr ((e.trans (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm))).symm) h4

theorem false_of_hatA7_F4 (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hFine : F918Fine4)
    (hcx : Cx1291 G T L V n) (hV₁ : IsTSub T V V₁ 1) (hU : IsMulCommutative ↥(u128 V V₁))
    (hLK : lOne L V₁ ≤ K₁) (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hHz : IsHzOne T L V₁ (K₁ ⊔ T)) (hA7 : IsHatA7 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) : False := by
  have hF := hypF918_F4 h1222 h37 h38 h39 hcx hV₁ hU hLK hK hHz hA7.1
  have hTK := T_le_normalizer_F4 h1222 h37 h38 hcx hV₁ hLK hK
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have h4 := (F918_4_fine' hF (sqtkGroup hcx hHz) (conjClosure_eq hTK) hV₁I hIU W hW hirrU hD310
    hD391 hI4 hFine).1
  obtain ⟨e⟩ := nonempty_mulEquiv_autIH hF
  have hhat : IsHat ↥(autIH V₁ V (K₁ ⊔ T) K₁) ↥(alternatingGroup (Fin 7)) :=
    IsHat.of_mulEquiv e hA7
  exact h4.2.1 hhat.2.2 hhat

end L1295B

end CFSG.Quasithin.H13
