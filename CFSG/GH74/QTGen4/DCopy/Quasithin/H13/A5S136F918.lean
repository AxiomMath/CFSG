module

public import CFSG.Quasithin.H13.A5S136F918
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S135

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Quasithin.E3
open CFSG.Blueprint CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting

variable {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem hypF98_of_mem_Hz_F4 (h1323 : Input1323Two_F4)
    (h24 : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
      ⁅V, conjSub g⁻¹ V⁆ = ⊥) {H : Subgroup G} (hH : H ∈ S.Hz) :
    HypF98 T V L S.V1 S.V3 H where
  toHypF91 := S.hypF91_F4 h1323 hH
  weak_f := fun g hg => by
    by_cases hgN : g ∈ Subgroup.normalizer (V : Set G)
    · rw [conjSub_self_of_mem (Subgroup.inv_mem _ hgN),
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
    · have hne : V ⊓ conjSub g⁻¹ V ≠ ⊥ := by
        intro h
        have : S.z ∈ V ⊓ conjSub g⁻¹ V := ⟨S.z_mem_V, hg (Subgroup.mem_zpowers _)⟩
        rw [h] at this
        exact S.z_ne_one (Subgroup.mem_bot.mp this)
      exact h24 g hgN hne
  case_g := Or.inl (by
    have h1 : ⁅V, H ⊓ Subgroup.centralizer (S.V3 : Set G)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
        h1323 G T L V S (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hx).2)
      exact S.mem_centralizer_V_of_V3 hxN (Subgroup.mem_inf.mp hx).2
    rw [h1]
    exact bot_le)

theorem sup_mem_Hz_F4 (h1336 : Input1336_F4) {K : Subgroup G} (hK : K ∈ cComp S.G1)
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G)) : K ⊔ (S.L1 ⊔ T) ∈ S.Hz := by
  have hG := S.G1_mem_Hz_F4 h1336
  have hle : K ⊔ (S.L1 ⊔ T) ≤ S.G1 := sup_le (le_of_mem_cComp hK) hG.1.1
  exact ⟨⟨le_sup_right, S.pCoreOf_ne_bot_of_le_G1 (le_sup_right.trans le_sup_right) hle⟩, hle,
    fun h => hKM (le_sup_left.trans h)⟩

theorem T_le_normalizer_of_G1_F4 (h1336 : Input1336_F4) {K : Subgroup G}
    (hKn : S.G1 ≤ Subgroup.normalizer (K : Set G)) : T ≤ Subgroup.normalizer (K : Set G) :=
  le_sup_right.trans ((S.G1_mem_Hz_F4 h1336).1.1.trans hKn)

theorem hypF918_sup_F4 (h1323 : Input1323Two_F4) (h1336 : Input1336_F4)
    (h24 : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
      ⁅V, conjSub g⁻¹ V⁆ = ⊥) {K : Subgroup G} (hK : K ∈ cComp S.G1)
    (hKn : S.G1 ≤ Subgroup.normalizer (K : Set G))
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    HypF918 T V L S.V1 S.V3 (K ⊔ (S.L1 ⊔ T)) K := by
  have hHz := S.sup_mem_Hz_F4 h1336 hK hKM
  have hTK := S.T_le_normalizer_of_G1_F4 h1336 hKn
  have hq' : CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K) := by
    have e : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := by
      rw [pCoreOf, map_subtype_subgroupOf']
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq e.symm) hq
  refine
    { toHypF98 := S.hypF98_of_mem_Hz_F4 h1323 h24 hHz
      K_cComp := mem_cComp_of_normal hK hKn le_sup_left hHz.2.1
      K_quasisimple := hq'
      H_eq := ?_
      K₀_normal := ?_ }
  · rw [L1295B.conjClosure_eq hTK]
    refine le_antisymm (sup_le_sup_left ?_ K) (sup_le le_sup_left inf_le_right)
    exact le_inf (sup_le (S.L1_le_L.trans le_sup_left) le_sup_right) le_sup_right
  · rw [L1295B.conjClosure_eq hTK]
    exact hHz.2.1.trans hKn

theorem fourList_of_cComp_G1_F4 (h1323 : Input1323Two_F4) (h1336 : Input1336_F4)
    (h24 : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
      ⁅V, conjSub g⁻¹ V⁆ = ⊥) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) {K : Subgroup G}
    (hK : K ∈ cComp S.G1) (hKn : S.G1 ≤ Subgroup.normalizer (K : Set G))
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G))
    (hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) : FourList (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have hperf : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := by
    have hK' : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK.2.1
    exact Group.IsPerfect.ofSurjective (G := ↥K) (f := QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
  have hF := S.hypF918_sup_F4 h1323 h1336 h24 hK hKn hKM (L1295B.isQuasisimple_of_simple hperf hS)
  have hHz := S.sup_mem_Hz_F4 h1336 hK hKM
  have hTK := S.T_le_normalizer_of_G1_F4 h1336 hKn
  have hSQ : SQTKGroup ↥(K ⊔ (S.L1 ⊔ T)) := by
    obtain ⟨hk, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian
      (T := T) ⟨le_sup_right.trans le_sup_right, hHz.1.2⟩
    exact ⟨hq, hk⟩
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have h4 := (F918_4' hF hSQ (L1295B.conjClosure_eq hTK) hV₁I hIU W hW hirrU hD310 hD391
    hI4).1
  obtain ⟨e⟩ := L1295B.nonempty_mulEquiv_autIH hF
  have hSA : IsSimpleGroup ↥(autIH S.V1 S.V3 (K ⊔ (S.L1 ⊔ T)) K) :=
    MulEquiv.isSimpleGroup e.symm
  have hperfA : Group.IsPerfect ↥(autIH S.V1 S.V3 (K ⊔ (S.L1 ⊔ T)) K) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hZ : Subgroup.center ↥(autIH S.V1 S.V3 (K ⊔ (S.L1 ⊔ T)) K) = ⊥ :=
    (L1295B.center_eq_bot_of_simple hperfA hSA).2
  exact fourList_congr ((e.trans (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm))).symm) h4

theorem false_of_J2_F4
    (h1323 : Input1323Two_F4) (h1336 : Input1336_F4)
    (h24 : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
      ⁅V, conjSub g⁻¹ V⁆ = ⊥) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) {K : Subgroup G}
    (hK : K ∈ cComp S.G1) (hKn : S.G1 ≤ Subgroup.normalizer (K : Set G))
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G))
    (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* NativeSporadic.J2) : False := by
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e
  have h4 := S.fourList_of_cComp_G1_F4 h1323 h1336 h24 hD310 hD391 hI4 hK hKn hKM hS
  have hc := L1295B.card_of_fourList (fourList_congr e h4)
  rw [CFSG.Sporadic.J2.card_J2] at hc
  exact not_fourListOrder_J2 hc

theorem false_of_M23_F4
    (h1323 : Input1323Two_F4) (h1336 : Input1336_F4)
    (h24 : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
      ⁅V, conjSub g⁻¹ V⁆ = ⊥) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) {K : Subgroup G}
    (hK : K ∈ cComp S.G1) (hKn : S.G1 ≤ Subgroup.normalizer (K : Set G))
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G))
    (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* NativeSporadic.M23) : False := by
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2 e
  have h4 := S.fourList_of_cComp_G1_F4 h1323 h1336 h24 hD310 hD391 hI4 hK hKn hKM hS
  have hc := L1295B.card_of_fourList (fourList_congr e h4)
  rw [L1295B.card_M23] at hc
  exact L1295B.not_fourListOrder_M23 hc

theorem false_of_3D4_F4
    (h1323 : Input1323Two_F4) (h1336 : Input1336_F4)
    (h24 : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
      ⁅V, conjSub g⁻¹ V⁆ = ⊥) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) {K : Subgroup G}
    (hK : K ∈ cComp S.G1) (hKn : S.G1 ≤ Subgroup.normalizer (K : Set G))
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G))
    (h3 : Is3D4 2 1 (↥K ⧸ CFSG.pCore 2 ↥K)) : False := by
  obtain ⟨-, hS⟩ := CFSG.LieType.Simplicity.fam_3d4_simplicity _ 2 1 h3
  have h4 := S.fourList_of_cComp_G1_F4 h1323 h1336 h24 hD310 hD391 hI4 hK hKn hKM hS
  have hc := L1295B.card_of_fourList h4
  rw [card_of_is3D4_two h3] at hc
  exact not_fourListOrder_3D4 hc

end Setting

end CFSG.Quasithin.H13.A5
