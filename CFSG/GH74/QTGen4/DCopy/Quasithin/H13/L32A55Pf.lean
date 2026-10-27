module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A55Q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL24
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASetting
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem143
public import CFSG.Quasithin.H13.L32A53b
public import CFSG.Quasithin.H13.L32A55Am

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem lemma14_5_5Q_of_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hlist : F6.GoldschmidtS3ListCat.{0}) (hKG : KGAutM12E16) : Lemma14_5_5Q_F4 := by
  intro G _ _ T L V V₂ Y h hV2 hYo hYG1 hTY hS3Y hYM hS3X hinf hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := L₁Of L V₂ with hX
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨hVe, hV8, -, hV12, -⟩ := hMod G T L V h.hyp h.fsu
  obtain ⟨hV1V, -, hTV1⟩ := h.isTSub_V1_F4 hMod
  have hTsyl := h.fsu.sylow

  have hUe := L32A.isElemAbelian_fsuU_of_F4 h hMod
  have hU2 : ∀ u ∈ fsuU T V, u ^ 2 = 1 := (F7.isElemAbelian_iff.mp hUe).2
  have hUp : IsPGroup 2 (fsuU T V) := fun u => ⟨1, Subtype.ext (by simpa using hU2 u u.2)⟩
  have hG1U : A6.g1 T V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    le_normalizer_conjClosure V _
  have hVU : V ≤ fsuU T V := le_conjClosure V _

  have hVG1 : V ≤ A6.g1 T V := fun w hw =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (F7.isElemAbelian_iff.mp hVe).1 z (hV1V hz) w hw)
  have hUG1 : fsuU T V ≤ A6.g1 T V := conjClosure_le fun g hg w hw =>
    (A6.g1 T V).mul_mem ((A6.g1 T V).mul_mem hg (hVG1 hw)) ((A6.g1 T V).inv_mem hg)

  have hUT : fsuU T V ≤ T :=
    (le_pCoreOf_of_le_normalizer 2 hUG1 hG1U hUp).trans
      (pCoreOf_le_of_isSylowIn (isSylowTwoOf_of_quasithinIsSylowTwo hTsyl hTV1))
  have hYTU : Y ⊔ T ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    sup_le (hYG1.trans hG1U) (hTV1.trans hG1U)

  have hVneU : V ≠ fsuU T V := by
    intro hVU'
    apply hYM
    intro y hy
    have hyV : y ∈ Subgroup.normalizer (V : Set G) := by
      rw [hVU']
      exact hG1U (hYG1 hy)
    rw [lemma1433Five_of_inputs_F4 h1332 h1334 G T L V h.hyp h.fsu] at hyV
    exact hyV.1
  have hU16 : 16 ≤ Nat.card (fsuU T V) := by
    have hdvd := Subgroup.card_dvd_of_le hVU
    rw [hV8] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hc1 : c ≠ 1 := fun h1 => hVneU (Subgroup.eq_of_le_of_card_ge hVU (by rw [hc, hV8, h1]))
    have hc0 : c ≠ 0 := fun h0 => by
      have := (Nat.card_pos (α := fsuU T V)).ne'
      rw [hc, h0, mul_zero] at this
      exact this rfl
    rw [hc]
    omega

  obtain ⟨v, hvV1, hv1⟩ : ∃ v ∈ fsuV1 T V, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : fsuV1 T V = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [hbot, Subgroup.card_bot] at hV12
    exact absurd hV12 (by norm_num)
  have hvU : v ∈ fsuU T V := hVU (hV1V hvV1)
  have hYTC : Y ⊔ T ≤ Subgroup.centralizer (fsuV1 T V : Set G) := by
    rw [← L32A.normalizer_eq_centralizer_of_card_two hV12]
    exact sup_le hYG1 hTV1
  have hvC : v ∈ Subgroup.centralizer ((Y ⊔ T : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun g hg =>
      (Subgroup.mem_centralizer_iff.mp (hYTC hg) v hvV1).symm

  have hTP : ((hTsyl.1.toSylow hTsyl.2 : Sylow 2 G) : Subgroup G) = T := IsPGroup.toSylow_coe _ _
  have hV2V : V₂ ≤ V := hV2.2.1
  have hcXT : CharTwo (X ⊔ T) := by
    refine charTwo_of_inH h.fsu.qtke.2.1 (hTsyl.1.toSylow hTsyl.2)
      ⟨by rw [hTP]; exact le_sup_right, ?_⟩
    have hV2le : V₂ ≤ pCoreOf 2 (X ⊔ T) := by
      refine le_pCoreOf_of_le_normalizer 2 ((hV2V.trans (hVU.trans hUT)).trans le_sup_right)
        (sup_le ((oTwoRes_le _).trans inf_le_right) hV2.2.2.1) ?_
      exact hUp.to_le (hV2V.trans hVU)
    intro hbot
    have h4 := hV2.2.2.2
    rw [le_bot_iff.mp (hV2le.trans hbot.le), Subgroup.card_bot] at h4
    exact absurd h4 (by norm_num)
  have hcYT : CharTwo (Y ⊔ T) := by
    refine charTwo_of_inH h.fsu.qtke.2.1 (hTsyl.1.toSylow hTsyl.2)
      ⟨by rw [hTP]; exact le_sup_right, ?_⟩
    have hV1le : fsuV1 T V ≤ pCoreOf 2 (Y ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 ((hV1V.trans (hVU.trans hUT)).trans le_sup_right)
        (sup_le hYG1 hTV1) (hUp.to_le (hV1V.trans hVU))
    intro hbot
    rw [le_bot_iff.mp (hV1le.trans hbot.le), Subgroup.card_bot] at hV12
    exact absurd hV12 (by norm_num)

  set H := X ⊔ Y ⊔ T with hH
  have hXTH : X ⊔ T ≤ H := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hYTH : Y ⊔ T ≤ H := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hgen : (X ⊔ T) ⊔ (Y ⊔ T) = H :=
    le_antisymm (sup_le hXTH hYTH)
      (sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
        (le_sup_right.trans le_sup_right))
  have hTIn : F6.IsGoldschmidtTripleIn H (X ⊔ T) (Y ⊔ T) := by
    refine ⟨hgen, L32A.T53.nonempty_open_of_quasithinO2QuotientIso hS3X,
      L32A.T53.nonempty_open_of_quasithinO2QuotientIso hS3Y, ?_⟩
    rw [hinf]
    exact isSylowTwoOf_of_quasithinIsSylowTwo hTsyl le_sup_right
  have hGA : IsGoldschmidtAmalgam ((X ⊔ T).subgroupOf H) ((Y ⊔ T).subgroupOf H) :=
    { hTIn.subgroupOf with
      pCore_eq_bot := (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hQ }
  have hUH : fsuU T V ≤ H := hUT.trans le_sup_right
  refine L32A.T55.false_of_goldschmidtAmalgam hlist hKG hGA
    (F6.charTwo_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXTH).symm hcXT)
    (F6.charTwo_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYTH).symm hcYT)
    (U := (fsuU T V).subgroupOf H) (Subgroup.comap_mono (hUT.trans le_sup_right)) ?_ ?_ ?_
    (v := ⟨v, hUH hvU⟩) (Subgroup.mem_subgroupOf.mpr hvU)
    (fun h1 => hv1 (congrArg Subtype.val h1)) ?_
  · intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro w
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hYTU (Subgroup.mem_subgroupOf.mp hb)) w
  · intro u hu
    exact Subtype.ext (by simpa using hU2 u (Subgroup.mem_subgroupOf.mp hu))
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv] at hU16
    exact hU16
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hvC b (Subgroup.mem_subgroupOf.mp hb))

end CFSG.Quasithin.H13
