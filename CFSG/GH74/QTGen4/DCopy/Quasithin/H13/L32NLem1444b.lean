module

public import CFSG.Quasithin.H13.L32NLem1444b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NInputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems144
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.GoldschmidtL128Four3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444

variable {G : Type} [Group G]

theorem exists_gh_F4 [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]
    (S : L32NSet14.Setting_F4 G T L V V₂) :
    ∃ g' ∈ L, ∃ h' ∈ L, V = fsuV1 T V ⊔ rconj (fsuV1 T V) g' ⊔ rconj (fsuV1 T V) h' := by
  obtain ⟨z, a, b, hz, hz1, haV₂, haV₁, hb, hbV₂⟩ := S.exists_basis_F4
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hzV₂ : z ∈ V₂ := S.hV2.1 hz
  have ha : a ∈ V := S.hV2.2.1 haV₂
  have ha1 : a ≠ 1 := fun h => haV₁ (h ▸ one_mem _)
  have hb1 : b ≠ 1 := fun h => hbV₂ (h ▸ one_mem _)
  have hzb : z ≠ b := fun h => hbV₂ (h ▸ hzV₂)
  have hab : a ≠ b := fun h => hbV₂ (h ▸ haV₂)
  have hza : z ≠ a := fun h => haV₁ (h ▸ hz)
  have habz : a ≠ b * z := fun h => hbV₂ (by
    have : b = a * z⁻¹ := by rw [h]; group
    rw [this]
    exact mul_mem haV₂ (inv_mem hzV₂))
  have hbaz : b ≠ a * z := fun h => hbV₂ (h ▸ mul_mem haV₂ hzV₂)
  obtain ⟨l₁, hl₁, -, -, hl₁z, -⟩ := S.exists_rot_F4 hb hzV ha hz1 ha1 hzb hab hza habz
  obtain ⟨l₂, hl₂, -, -, hl₂z, -⟩ := S.exists_rot_F4 ha hzV hb hz1 hb1 hza hab.symm hzb hbaz
  have hrV : ∀ l ∈ L, rconj (fsuV1 T V) l ≤ V := fun l hl y hy => by
    rw [mem_rconj] at hy
    have h1 := (Subgroup.mem_normalizer_iff.mp (S.LV_F4 (L.inv_mem hl)) _).mp
      (Subgroup.mem_inf.mp hy).1
    simpa [mul_assoc] using h1
  have haJ : a ∈ rconj (fsuV1 T V) l₁⁻¹ := by
    rw [mem_rconj, inv_inv, ← hl₁z]
    simpa [mul_assoc] using hz
  have hbJ : b ∈ rconj (fsuV1 T V) l₂⁻¹ := by
    rw [mem_rconj, inv_inv, ← hl₂z]
    simpa [mul_assoc] using hz
  refine ⟨l₁⁻¹, L.inv_mem hl₁, l₂⁻¹, L.inv_mem hl₂, le_antisymm ?_ ?_⟩
  · set J := fsuV1 T V ⊔ rconj (fsuV1 T V) l₁⁻¹ ⊔ rconj (fsuV1 T V) l₂⁻¹
    have hV1J : fsuV1 T V ≤ J := le_sup_left.trans le_sup_left
    have haJ' : a ∈ J := (le_sup_right.trans le_sup_left : rconj (fsuV1 T V) l₁⁻¹ ≤ J) haJ
    have hbJ' : b ∈ J := (le_sup_right : rconj (fsuV1 T V) l₂⁻¹ ≤ J) hbJ
    have hV₂J : ∀ w ∈ V₂, w ∈ J := by
      intro w hw
      rcases S.mem_V2_F4 haV₂ haV₁ hw with hw1 | hw1
      · exact hV1J hw1
      · have := J.mul_mem (J.inv_mem haJ') (hV1J hw1)
        simpa using this
    intro v hv
    rcases S.mem_V_F4 hb hbV₂ hv with hv2 | hv2
    · exact hV₂J v hv2
    · have := J.mul_mem (J.inv_mem hbJ') (hV₂J _ hv2)
      simpa using this
  · exact sup_le (sup_le inf_le_left (hrV _ (L.inv_mem hl₁))) (hrV _ (L.inv_mem hl₂))

end L1444

open L1444 in

theorem lemma1444Four_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) : Lemma1444Four_F4 := by
  intro G _ _ T L V h _ h32 _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨V₂, hV₂⟩ := h.exists_plane_F4 hV
  obtain ⟨_, S⟩ := L14332.exists_setting_F4 h1332 h1334 h1222 h hV₂
  obtain ⟨-, hyp⟩ := lemma12_8_8_four_of_F4 h1222 h12213 G T L V 3 (fsuV1 T V) V₂
    (h.setting1282One_F4 h13322 hV hV₂) le_rfl
  obtain ⟨g', hg, h', hh, hVgh⟩ := exists_gh_F4 S
  have hUT : fsuU T V ≤ T := hyp.base.G22_three.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hyp.base.T_le_normL
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := S.LV_F4
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hyp.base.T_le_normV
  have hVT : V ≤ T := hyp.base.V_le_T
  have hTU : T ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    hyp.base.T_le_H.trans (le_normalizer_conjClosure V _)
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 3) (by rw [S.card_V_F4]; norm_num)
  have hVU : V ≤ fsuU T V := le_conjClosure V _

  have hVL : V ≤ L := by
    rw [← S.hV.2.2.2.1]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hVT.trans hTL)
  have hVO₂L : V ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 hVL hLV hV2

  obtain ⟨-, -, hU4, -⟩ := hyp.G25_one
  have hcardU := card_secImg_mul (A := L ⊔ T) (B := pCoreOf 2 (L ⊔ T)) (X := fsuU T V)
    (hUT.trans le_sup_right)
  have hU4' : Nat.card (secImg (L ⊔ T) (pCoreOf 2 (L ⊔ T)) (fsuU T V)) = 4 := hU4
  rw [hU4', h32] at hcardU
  have hVO : V ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hVT.trans le_sup_right) (sup_le hLV hTV) hV2
  have hUO : fsuU T V ⊓ pCoreOf 2 (L ⊔ T) = V :=
    (Subgroup.eq_of_le_of_card_ge (le_inf hVU hVO) (by rw [S.card_V_F4]; omega)).symm

  obtain ⟨D'⟩ := hyp.natural.nonempty_data
  let St : L3Setting 1 V (fsuV1 T V) L T (l32nH T V) := ⟨hyp, D'⟩
  obtain ⟨I, hI⟩ : ∃ I : Subgroup G, I = fsuU T V ⊔ rconj (fsuU T V) g' ⊔ rconj (fsuU T V) h' :=
    ⟨_, rfl⟩
  obtain ⟨Sg, hSg⟩ : ∃ Sg : Subgroup G, Sg = pCoreOf 2 I := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, W = fsuU T V ⊓ Sg := ⟨_, rfl⟩
  have hI' : I = L ⊔ fsuU T V := hI.trans (St.G25_two_aux hg hh hVgh)
  obtain ⟨hSj, -⟩ := hyp.G25_three rfl hg hh hVgh hI hSg hW
  obtain ⟨-, -, -, hVZ, -, -, -⟩ := hyp.G25_four rfl hg hh hVgh hI hSg hW

  have hIle : I ≤ L ⊔ T := by
    rw [hI']
    exact sup_le le_sup_left (hUT.trans le_sup_right)
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (I : Set G) := by
    rw [hI']
    exact sup_le (le_sup_left.trans Subgroup.le_normalizer)
      (A1a.le_normalizer_sup (hTL) hTU)
  have hSgLT : Sg ≤ pCoreOf 2 (L ⊔ T) := by
    rw [hSg]
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 I).trans hIle)
      (hLTN.trans (normalizer_le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)

  have hVSg : V ≤ Sg := hVZ.trans inf_le_left
  have hWV : W = V := by
    rw [hW]
    exact le_antisymm ((inf_le_inf_left _ hSgLT).trans hUO.le) (le_inf hVU hVSg)
  have hSgV : Sg = V := by
    rw [hSj, hWV, rconj_eq_self (hLV hg), rconj_eq_self (hLV hh), sup_idem, sup_idem]

  have hO₂L : pCoreOf 2 L ≤ Sg := by
    rw [hSg]
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans ?_) ?_ (pCoreOf_isPGroup 2 L)
    · rw [hI']
      exact le_sup_left
    · rw [hI']
      exact sup_le (le_normalizer_pCoreOf 2 L)
        ((hUT.trans hTL).trans (normalizer_le_normalizer_pCoreOf 2 L))
  exact le_antisymm hVO₂L (hO₂L.trans hSgV.le)

end CFSG.Quasithin.H13
