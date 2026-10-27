module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A5F91

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped Pointwise

@[expose] def Input1323Two_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V),
    Subgroup.normalizer (S.V3 : Set G) ≤ Subgroup.normalizer (V : Set G)

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem coreIn_le_pCoreOf_F4 (h1323 : Input1323Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz) :
    coreIn (centralizerMod S.V1 H S.V3) H ≤ pCoreOf 2 H := by
  set K := coreIn (centralizerMod S.V1 H S.V3) H with hKdef
  have hKH : K ≤ H := coreIn_le_left _ _
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_coreIn _ _
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hHG1 : H ≤ S.G1 := hH.2.1

  have hgenV3 : ∀ y ∈ K, (∃ m : ℕ, Odd m ∧ y ^ m = 1) →
      y ∈ Subgroup.centralizer (S.V3 : Set G) := by
    rintro y hyK ⟨m, hm, hym⟩
    have hyC : y ∈ centralizerMod S.V1 H S.V3 := coreIn_le_right _ _ hyK
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hyz : ∀ c ∈ S.V1, y * c * y⁻¹ = c := by
      intro c hc
      have hyG1 := hHG1 (hKH hyK)
      rw [← S.centralizer_V1] at hyG1
      have := Subgroup.mem_centralizer_iff.mp hyG1 c hc
      calc y * c * y⁻¹ = c * y * y⁻¹ := by rw [this]
        _ = c := by group
    have := conj_eq_of_odd_of_comm (U := S.V3) (V₁ := S.V1)
      (F7.isElemAbelian_mono S.elemAbelian_V S.V3_le_V) S.V1_le_V3 hm hym hyz hyC.2.2 hu
    calc u * y = y * u * y⁻¹ * y := by rw [this]
      _ = y * u := by group
  have hgenV : ∀ y ∈ K, (∃ m : ℕ, Odd m ∧ y ^ m = 1) → y ∈ Subgroup.centralizer (V : Set G) := by
    intro y hyK hy
    have hy3 := hgenV3 y hyK hy
    have hyN : y ∈ Subgroup.normalizer (V : Set G) :=
      h1323 G T L V S (Subgroup.centralizer_le_normalizer (S.V3 : Set G) hy3)
    exact S.mem_centralizer_V_of_V3 hyN hy3
  have hYV : oTwoRes K ≤ Subgroup.centralizer (V : Set G) :=
    (Subgroup.closure_le _).2 fun y hy => hgenV y hy.1 hy.2

  have hYH : H ≤ Subgroup.normalizer (oTwoRes K : Set G) :=
    le_normalizer_oTwoRes_of_le_normalizer hHK
  have hLY : L ≤ Subgroup.normalizer (oTwoRes K : Set G) := by
    refine le_normalizer_oTwoRes_of_gen fun l hl y hyK ⟨m, hm, hym⟩ => ?_
    have hyY : y ∈ oTwoRes K := Subgroup.subset_closure ⟨hyK, m, hm, hym⟩
    have hyCV : y ∈ Subgroup.centralizer (V : Set G) := hYV hyY
    have hyM : y ∈ Subgroup.normalizer (L : Set G) :=
      S.NV_le_M (Subgroup.centralizer_le_normalizer (V : Set G) hyCV)
    have hcomm : l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 (L ⊔ T) := by
      rw [← S.cLT]
      refine ⟨le_sup_left (a := L) ?_, ?_⟩
      · have : y * l⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyM _).mp (L.inv_mem hl)
        have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
        rw [e]
        exact L.mul_mem hl this
      · have hlN : l ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hl
        have h1 : l * y * l⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
          conj_mem_centralizer_of_mem_normalizer hlN hyCV
        exact (Subgroup.centralizer (V : Set G)).mul_mem h1
          ((Subgroup.centralizer (V : Set G)).inv_mem hyCV)
    have hmem : l * y * l⁻¹ ∈ oTwoRes K ⊔ pCoreOf 2 (L ⊔ T) := by
      have e : l * y * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact Subgroup.mul_mem _ (le_sup_right (a := oTwoRes K) hcomm)
        (le_sup_left (a := oTwoRes K) hyY)
    refine mem_of_odd_of_mem_sup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      ((S.pCoreOf_LT_le_T.trans hTH).trans hYH) hmem hm ?_
    rw [conj_pow, hym]
    group

  have hY : oTwoRes K = ⊥ := by
    by_contra hY
    have hchar : CharTwo (oTwoRes K) :=
      A4.charTwo_of_normal ((oTwoRes_le K).trans hKH) hYH
        (S.charTwo_of_inH ⟨hTH, hH.1.2⟩)
    have hO2 : pCoreOf 2 (oTwoRes K) ≠ ⊥ := by
      intro h0
      apply hY
      have hle : oTwoRes K ≤ oTwoRes K ⊓
          Subgroup.centralizer (pCoreOf 2 (oTwoRes K) : Set G) := by
        intro x hx
        refine ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        rw [h0] at hy
        rw [show y = 1 from hy]
        simp
      have := hle.trans hchar
      rw [h0] at this
      exact le_bot_iff.mp this
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (oTwoRes K) : Set G)) :=
      ⟨_, hO2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩
    have hN := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (oTwoRes K)
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hLTM' : L ⊔ T ≤ M' := sup_le (hLY.trans (hN.trans hle))
      ((hTH.trans hYH).trans (hN.trans hle))
    have := S.uniqueM.2 M' ⟨hM', hLTM'⟩
    exact hH.2.2 (this ▸ (hYH.trans (hN.trans hle)))

  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKH hHK
    (isPGroup_of_oTwoRes_eq_bot hY)

theorem hypF91_F4 (h1323 : Input1323Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz) :
    HypF91 T V L S.V1 S.V3 H where
  sylow := S.sylow_top
  elemAbelian := S.elemAbelian_V
  normalizes_L := S.T_le_NL
  oTwoRes_eq := S.oTwoRes_L
  charTwo_L := S.charTwo_L
  reduced := S.reduced
  cT := S.cT
  card_V₁ := S.card_V1
  V₁_lt_Vp := S.V1_lt_V3
  Vp_le_V := S.V3_le_V
  T_normalizes_V₁ := S.T_le_NV1
  H_le_centralizer := S.centralizer_V1 ▸ hH.2.1
  L₁T_le_H := hH.1.1
  charTwo_H := S.charTwo_of_inH ⟨le_sup_right.trans hH.1.1, hH.1.2⟩
  ker_le := S.coreIn_le_pCoreOf_F4 h1323 hH
  L₁T_normalizes_Vp := S.L1T_le_NV3
  irred := S.irred_V3
  normalizer_le := fun _ hx => h1323 G T L V S hx.2
  o2_trivial := S.o2_eq_bot_of_not_le le_sup_left fun h => hH.2.2 (le_sup_right.trans h)
  weak_e := fun _ hg h1 h2 h3 => S.weak_e (hH.2.1 hg) h1 h2 h3

end Setting

end CFSG.Quasithin.H13.A5
