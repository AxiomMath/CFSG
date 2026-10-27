module

public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelBase
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3L34
public import CFSG.GH74.GLS.C3.Layer1.St1PumpH2
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelLeaves
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3Pump

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L34

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid

variable {G : Type} [Group G] [Finite G]

theorem L34_core_rel
    (h610 : B_ig_6_10) (h720 : B_ivk_7_20) (h14 : B_prop14) (h103 : B_ivk_10_3)
    (hL34 : B_gen4_noL34_elem) (hL29 : B_inC2_L29) (h102 : B_ivk_10_2) (hC2 : C2Facts)
    (hP31 : B_thm1_P31s_rel) {G : Type} [Group G] [Finite G] (hG : C3Hyp G) (hNo : NoV2Fine G)
    {x y : G} {K : Subgroup G} {f : G} (hmax : FMax3 x y K f) (hf2 : orderOf f = 2)
    {J : Subgroup G} (hJc : IsPCompIn 2 (centralizer ({f} : Set G)) J) (hIJ : layerI K f ≤ J)
    (hlt : layerI K f ⊔ pPrimeCoreOf 2 J < J) {r : ℕ} (hrodd : Odd r) (hr5 : 5 ≤ r)
    (hI : HasL2Model (kBar (layerI K f)) (fun q => q = r))
    (hKshape : HasL2Model (kBar K) (fun q => q = r ^ 2) ∨
      (r = 5 ∧ Nonempty (kBar K ≃* alternatingGroup (Fin 7))))
    (hJshape : HasL2Model (kBar J) (fun q => q = r) ∨ HasL2Model (kBar J) (fun q => q = r ^ 2) ∨
      Nonempty (kBar J ≃* alternatingGroup (Fin 7)))
    (hA7 : Nonempty (kBar J ≃* alternatingGroup (Fin 7)) →
      HasL2Model (kBar K) (fun q => q = 5 ^ 2) ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    ∃ w : G, orderOf w = 2 ∧ Is2TerminalU2Triple f w J := by
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  have hJshape' : HasL2Model (kBar J) (fun q => q = r ^ 2) ∨
      Nonempty (kBar J ≃* alternatingGroup (Fin 7)) := by
    rcases hJshape with h | h | h
    · exact absurd (sup_eq_of_hasL2Model hIJ hI h) (ne_of_lt hlt)
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨hJU, hJN, hJs⟩ := J_class hG hC2 hL34 hf2 hJc hrodd hr5 hJshape'
  have hpairJ : IsIL2Pair f J := ⟨hf2, hJc⟩
  have hILo : IsILo 2 f J := by
    refine ⟨hf2, ?_, hJc⟩
    have := h14 G hG f J hpairJ hJU
    simp only [oBound, ite_true]
    omega
  obtain ⟨t, L, hlong, hterm⟩ := h610 G hG.kproper (by rw [hr4]; norm_num) f J hILo
  obtain ⟨hUL, hNL⟩ := h720 G hG f J t L hpairJ hJU hJN hlong
  have hILoL : IsILo 2 t L := hlong.isILo_right
  obtain ⟨v, hv⟩ := Thm1Pump.exists_u2_of_terminal h14 h103 hL34 hL29 hG hILoL hterm hUL hNL
  have h5L : ¬ HasL2Model (kBar L) (fun q => q = 5) := not_hasL2Model_five_of_not_inC2 hUL hNL
  have hrk : pRank 2 ↥(CxK t L) ≤ 1 := by
    by_contra h
    exact h5L (hNo t v L ⟨hv.1, hv.2.1, Or.inl (by omega), fun _ => hv⟩)
  have hLK : hatCard L ≤ hatCard K := by
    obtain ⟨T', hT'⟩ := Thm1.exists_setup1D t L
    have hshape := Thm1.kBar_model_of_U2 hG h102 hL34 hv
    obtain ⟨-, -, -, hT⟩ := hP31 G hG hNo t v L hv hshape h5L
    obtain ⟨⟨f', hf', -⟩, -, -⟩ := hT T' hT'
    have := hmax.1.1.2 t v L f' ⟨hv, T', hT', hf'⟩
    rw [hatCard_eq', hatCard_eq']
    exact this
  have hchain : Relation.ReflTransGen (Thm1Pump.PStep G) (f, J) (t, L) := hlong.2
  have hS : ∀ a : G × Subgroup G, Relation.ReflTransGen (Thm1Pump.PStep G) (f, J) a →
      IsSimpleGroup (kBar a.2) := by
    intro a ha
    have hlonga : LongPumpUp 2 f J a.1 a.2 := ⟨hILo, ha⟩
    obtain ⟨hUa, -⟩ := h720 G hG f J a.1 a.2 hpairJ hJU hJN hlonga
    have hILoa : IsILo 2 a.1 a.2 := hlonga.isILo_right
    exact isSimple_of_inU2 hUa (hL34 G hG.gen4 a.1 a.2 hILoa.1 hILoa.2.2)
  have hJL : hatCard J ≤ hatCard L := by
    have := PumpRigid.hat_le_of_chain hchain
    exact this
  have hJK : hatCard J ≤ hatCard K := hJL.trans hLK
  have hJrk : pRank 2 ↥(CxK f J) ≤ 1 := by
    rcases hJshape' with hJ2 | hJA7
    · rcases hKshape with hK2 | ⟨hr5', hKA7⟩
      · have hcards : hatCard K = hatCard J := by
          rw [hatCard_of_hasL2Model hK2, hatCard_of_hasL2Model hJ2]
        exact Thm1Pump.chain_back_rigid (p := (f, J)) (q := (t, L)) hr4 hrk hchain (hLK.trans hcards.le) hS
      · exfalso
        subst hr5'
        have h1 := hatCard_of_hasL2Model hJ2
        have h2 := hatCard_of_alt7 hKA7
        rw [show (5 : ℕ) ^ 2 = 25 by norm_num, ordA_one_25] at h1
        omega
    · have h2 := hatCard_of_alt7 hJA7
      rcases hA7 hJA7 with hK2 | hKA7
      · have h1 := hatCard_of_hasL2Model hK2
        rw [show (5 : ℕ) ^ 2 = 25 by norm_num, ordA_one_25] at h1
        exact Thm1Pump.chain_back_num (p := (f, J)) (q := (t, L)) (j := 2520) (B := 7800) hr4 hrk
          (by norm_num) (by norm_num) hchain (h1 ▸ hLK) h2.ge hS
      · have h3 := hatCard_of_alt7 hKA7
        exact Thm1Pump.chain_back_rigid (p := (f, J)) (q := (t, L)) hr4 hrk hchain (by show hatCard L ≤ hatCard J; omega) hS
  have hterm' : IsTwoTerminal f J := PumpH1.isTwoTerminal_of_pRank_le_one hILo hJrk
  obtain ⟨w, hw⟩ := Thm1Pump.exists_u2_of_terminal h14 h103 hL34 hL29 hG hILo hterm' hJU hJN
  exact ⟨w, hw.1.2.1, hw⟩

theorem thm1_L34a_of_rel
    (h610 : B_ig_6_10) (h720 : B_ivk_7_20) (h14 : B_prop14) (h103 : B_ivk_10_3)
    (hL34 : B_gen4_noL34_elem) (hL29 : B_inC2_L29) (h102 : B_ivk_10_2) (hC2 : C2Facts)
    (hP31 : B_thm1_P31s_rel) (hL32 : B_thm1_L32'_rel) : B_thm1_L34a_rel := by
  intro G _ _ hG hNo x y K T f hmax hsetup hmem hlt h5
  obtain ⟨hJc, -, r, hrodd, hr5, hI, hKshape, hJshape, hA7⟩ := hL32 G hG hNo x y K f hmax h5
  exact L34_core_rel h610 h720 h14 h103 hL34 hL29 h102 hC2 hP31 hG hNo hmax hmem.2.1 hJc
    (Thm1.layerI_le_pumpJ K f) hlt hrodd hr5 hI hKshape hJshape hA7

theorem pumpJ_not_five_of_L32 (hL32 : B_thm1_L32'_rel) {G : Type} [Group G] [Finite G]
    (hG : C3Hyp G) (hNo : NoV2Fine G) {x y : G} {K : Subgroup G} {f : G} (hmax : FMax3 x y K f)
    (h5 : ¬ HasL2Model (kBar K) (fun q => q = 5))
    (hlt : layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f) < pumpJ K f) :
    ¬ HasL2Model (kBar (pumpJ K f)) (fun q => q = 5) := by
  obtain ⟨-, -, r, hrodd, hr5, hI, -, hJshape, -⟩ := hL32 G hG hNo x y K f hmax h5
  have hIJ : layerI K f ≤ pumpJ K f := Thm1.layerI_le_pumpJ K f
  have hJshape' : HasL2Model (kBar (pumpJ K f)) (fun q => q = r ^ 2) ∨
      Nonempty (kBar (pumpJ K f) ≃* alternatingGroup (Fin 7)) := by
    rcases hJshape with h | h | h
    · exact absurd (sup_eq_of_hasL2Model hIJ hI h) (ne_of_lt hlt)
    · exact Or.inl h
    · exact Or.inr h
  exact not_hasL2Model_five_of_pumpShape hrodd hr5 hJshape'

theorem b_thm1_L34_of_rel (hL32 : B_thm1_L32'_rel) (h34a : B_thm1_L34a_rel)
    (hP31c : B_thm1_P31c_rel) : B_thm1_L34_rel := by
  intro G _ _ hG hNo x y K T f hmax hsetup hmem hlt h5
  obtain ⟨w, hw2, hw⟩ := h34a G hG hNo x y K T f hmax hsetup hmem hlt h5
  exact ⟨⟨w, hw2, hw⟩,
    hP31c G hG hNo f w (pumpJ K f) hw (pumpJ_not_five_of_L32 hL32 hG hNo hmax h5 hlt)⟩

end CFSG.GH74.GLS.C3.Layer1.Thm1L34
