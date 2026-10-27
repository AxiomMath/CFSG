module

public import CFSG.GH74.GLS.C3.Layer1.Th2P815R4aGamma
public import CFSG.GH74.GLS.C3.Layer1.Th2Tstar
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem r4a_T_fixedK [Finite G] {x y : G} {K T S M B : Subgroup G}
    (h2110 : B_IG_21_10) (h2 : Th2M2 x y K T S M .r4a B) :
    ∀ g ∈ T, g ∈ normalizer (K : Set G) → g ∈ M := by
  intro g hgT hgK
  have hP : g ∈ normalizer (((T ⊓ K) : Subgroup G) : Set G) :=
    CFSG.GH74.GLS.Th2SigHalf.mem_normalizer_inf (Subgroup.le_normalizer hgT) hgK
  have hQ : g ∈ normalizer (((T ⊓ CxK x K) : Subgroup G) : Set G) :=
    CFSG.GH74.GLS.Th2SigHalf.mem_normalizer_inf (Subgroup.le_normalizer hgT)
      (NxK_le_normalizer_CxK x K ⟨h2.std.T_le_C hgT, hgK⟩)
  have hR : g ∈ normalizer (((T ⊓ K) ⊔ (T ⊓ CxK x K) : Subgroup G) : Set G) :=
    Th2.mem_normalizer_sup hP hQ
  have hX : g ∈ normalizer ((Th2Row.Tstar .r4a x K T S : Subgroup G) : Set G) :=
    Th2Tstar.mem_normalizer_biSup_isSn (n := 4)
      (T := ((T ⊓ K) ⊔ (T ⊓ CxK x K) : Subgroup G)) hR
  have hX4 : 4 ≤ pRank 2 ↥(Th2Row.Tstar .r4a x K T S) :=
    Th2Tstar.le_pRank_Tstar (ρ := .r4a) h2.mem h2.isE.2.2
  have hNle : normalizer ((Th2Row.Tstar .r4a x K T S : Subgroup G) : Set G) ≤
      gammaK 2 (Th2Row.Tstar .r4a x K T S) 4 := by
    unfold gammaK
    exact le_iSup₂_of_le (Th2Row.Tstar .r4a x K T S) le_rfl
      (le_iSup_of_le hX4 le_rfl)
  exact (b_thm2_l82_r4a h2110 h2).2.1 (hNle hX)

theorem r4a_T_moved [Finite G] {x y : G} {K T S M B : Subgroup G}
    (h2110 : B_IG_21_10) (h2 : Th2M2 x y K T S M .r4a B) :
    ∀ g ∈ T, cj g K ≠ K → g ∈ M := by
  intro g hgT hne
  classical
  let P : Subgroup G := T ⊓ K
  let Q : Subgroup G := T ⊓ CxK x K
  let Pg : Subgroup G := T ⊓ cj g K
  let Qg : Subgroup G := T ⊓ CxK x (cj g K)
  let R : Subgroup G := P ⊔ Q
  let F : Subgroup G := P ⊔ Pg
  let X : Subgroup G := Th2Row.Tstar .r4a x K T S
  have hstd := h2.std
  have hgC : g ∈ centralizer ({x} : Set G) := hstd.T_le_C hgT
  have hTeq : cj g T = T := Th2Tstar.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hgT)
  have hgx : g * x * g⁻¹ = x := by
    have hcomm : g * x = x * g := mem_centralizer_singleton_iff.1 hgC
    calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [hcomm]
      _ = x := by group
  have hgx' : g⁻¹ * x * g = x := by
    have hcomm : x * g = g * x := (mem_centralizer_singleton_iff.1 hgC).symm
    calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
      _ = g⁻¹ * (g * x) := by rw [hcomm]
      _ = x := by group
  have hXeq : cj g (centralizer ({x} : Set G)) = centralizer ({x} : Set G) := by
    rw [cj_centralizer_singleton, hgx]
  have hKgcomp : IsPCompIn 2 (centralizer ({x} : Set G)) (cj g K) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hstd.comp g
    change IsPCompIn 2 (cj g (centralizer ({x} : Set G))) (cj g K) at this
    rwa [hXeq] at this
  have hK_le_cSec_Kg : K ≤ Stage1.Thm2.Recip.cSec (cj g K) :=
    Stage1.Thm2.Recip.le_cSec_of_ne hstd.comp hKgcomp hne.symm
  have hKg_le_cSec_K : cj g K ≤ Stage1.Thm2.Recip.cSec K :=
    Stage1.Thm2.Recip.le_cSec_of_ne hKgcomp hstd.comp hne
  have hCsEq : cj g (centralizerSection K (pPrimeCoreOf 2 K)) =
      centralizerSection (cj g K) (cj g (pPrimeCoreOf 2 K)) := by
    refine le_antisymm ?_ ?_
    · intro z hz
      rw [mem_cj_iff] at hz
      have h := Stage1.Thm3.Sec4.cmap_mem_centralizerSection hz g
      have h' : g * (g⁻¹ * z * g) * g⁻¹ ∈
          centralizerSection (cj g K) (cj g (pPrimeCoreOf 2 K)) := by
        change g * (g⁻¹ * z * g) * g⁻¹ ∈
          centralizerSection (Subgroup.map (MulAut.conj g).toMonoidHom K)
            (Subgroup.map (MulAut.conj g).toMonoidHom (pPrimeCoreOf 2 K))
        exact h
      rwa [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at h'
    · intro z hz
      change z ∈ centralizerSection (Stage1.Thm3.Sec4.cmap g K)
        (Stage1.Thm3.Sec4.cmap g (pPrimeCoreOf 2 K)) at hz
      have h := Stage1.Thm3.Sec4.cmap_mem_centralizerSection hz g⁻¹
      rw [Stage1.Thm3.Sec4.cmap_inv_cancel, Stage1.Thm3.Sec4.cmap_inv_cancel] at h
      have h' : g⁻¹ * z * g ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
        simpa using h
      rw [mem_cj_iff]
      exact h'
  have hCxKgEq : cj g (CxK x K) = CxK x (cj g K) := by
    change (CxK x K).map (MulAut.conj g).toMonoidHom = CxK x (cj g K)
    unfold CxK
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    change cj g (centralizer ({x} : Set G)) ⊓
        cj g (centralizerSection K (pPrimeCoreOf 2 K)) =
      centralizer ({x} : Set G) ⊓ centralizerSection (cj g K) (pPrimeCoreOf 2 (cj g K))
    rw [cj_centralizer_singleton, hgx, hCsEq, pPrimeCoreOf_cj]
  have hQgEq : Qg = cj g Q := by
    change T ⊓ CxK x (cj g K) = (T ⊓ CxK x K).map (MulAut.conj g).toMonoidHom
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    change T ⊓ CxK x (cj g K) = cj g T ⊓ cj g (CxK x K)
    rw [hTeq, hCxKgEq]
  have hQgInv : cj g⁻¹ Qg = Q := by
    rw [hQgEq, cj_cj_inv]
  have hP_Qg : P ≤ Qg := by
    refine le_inf inf_le_left (le_inf ?_ ?_)
    · exact inf_le_left.trans hstd.T_le_C
    · exact inf_le_right.trans hK_le_cSec_Kg
  have hPg_Q : Pg ≤ Q := by
    refine le_inf inf_le_left (le_inf ?_ ?_)
    · exact inf_le_right.trans hKgcomp.1
    · exact inf_le_right.trans hKg_le_cSec_K
  have hPg_eq : Pg = cj g P := by
    change T ⊓ cj g K = (T ⊓ K).map (MulAut.conj g).toMonoidHom
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    change T ⊓ cj g K = cj g T ⊓ cj g K
    rw [hTeq]
  have hPr : ∀ q : ℕ, q = 5 → Odd q := by rintro q rfl; decide
  obtain ⟨hL2, -⟩ := h2.row
  have hcen : CenterlessBar K := centerlessBar_of_hasL2Model hPr hL2
  have hPQ : CommDisj P Q := hstd.commDisj hcen
  have hPshape : RankTwoShape P :=
    rankTwoShape_sylow_L2 hstd.sylow_P (TwoThin.isQuasisimple_hat hstd.comp) hPr hL2
  have hP4 : Nat.card ↥P = 4 := card_sylow_L2_five hstd.sylow_P hL2
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hPshape
  have hUP : U = P := Subgroup.eq_of_le_of_card_ge hU.1 (by rw [hU.2.2, hP4])
  have hPel : CFSG.IsElementaryAbelian 2 ↥P := hUP ▸ hU.2.1
  have hPrank : pRank 2 ↥P = 2 := by rw [← hUP, pRank_of_isFourSub hU]
  have hPgel : CFSG.IsElementaryAbelian 2 ↥Pg := by
    rw [hPg_eq]
    exact isElementaryAbelian_cj g hPel
  have hPgrank : pRank 2 ↥Pg = 2 := by
    rw [hPg_eq, pRank_cj, hPrank]
  have hPgcard : Nat.card ↥Pg = 4 := by
    rw [hPg_eq, Subgroup.card_map_of_injective (MulAut.conj g).injective, hP4]
  have hPPgcomm : ∀ p ∈ P, ∀ q ∈ Pg, p * q = q * p :=
    fun p hp q hq => hPQ.comm p hp q (hPg_Q hq)
  have hPinfPg : P ⊓ Pg = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    have hzQ : z ∈ Q := hPg_Q hz.2
    have hzinf : z ∈ P ⊓ Q := ⟨hz.1, hzQ⟩
    rwa [hPQ.inf] at hzinf
  have hFel : CFSG.IsElementaryAbelian 2 ↥F :=
    isElementaryAbelian_sup (K := P) (L := Pg) hPel hPgel hPPgcomm
  have hFcard : Nat.card ↥F = 16 := by
    have hcd : CommDisj P Pg := ⟨hPPgcomm, hPinfPg⟩
    rw [show F = P ⊔ Pg from rfl, hcd.card_sup le_rfl le_rfl, hP4, hPgcard]
  have hFrank : pRank 2 ↥F = 4 := by
    have h := C3.Layer1.Back.card_eq_two_pow_pRank hFel
    rw [hFcard] at h
    exact Nat.pow_right_injective le_rfl (by simpa using h.symm)
  have hFR : F ≤ R := sup_le le_sup_left (hPg_Q.trans le_sup_right)
  have hFRg : F ≤ cj g R := by
    refine sup_le ?_ ?_
    · exact hP_Qg.trans ((le_of_eq hQgEq).trans
        (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) le_sup_right))
    · exact (le_of_eq hPg_eq).trans
        (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) le_sup_left)
  have hFX : F ≤ X := by
    obtain ⟨BF, hFBF, hBFIsS⟩ := Th2.exists_maximal_elemAbelian (X := R) hFR hFel
    have hBFrank : 4 ≤ pRank 2 ↥BF :=
      hFrank.ge.trans (C3.Layer1.Back.pRank_mono' hFBF)
    have hBFBT : BF ∈ Th2Row.BT .r4a x K T S := ⟨hBFIsS, hBFrank⟩
    exact hFBF.trans (le_iSup₂ (f := fun B' (_ : B' ∈ Th2Row.BT .r4a x K T S) => B')
      BF hBFBT)
  have hF4 : IsE 4 X F := ⟨hFX, hFel, hFrank.ge⟩
  have hFconjR : cj g⁻¹ F ≤ R := by
    have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hFRg
    change cj g⁻¹ F ≤ cj g⁻¹ (cj g R) at h
    rwa [show cj g⁻¹ (cj g R) = R by simpa using cj_cj_inv (g := g) (H := R)] at h
  have hFconjEl : CFSG.IsElementaryAbelian 2 ↥(cj g⁻¹ F) :=
    isElementaryAbelian_cj g⁻¹ hFel
  have hFconjRank : pRank 2 ↥(cj g⁻¹ F) = 4 := by
    rw [pRank_cj, hFrank]
  have hFconjX : cj g⁻¹ F ≤ X := by
    obtain ⟨BF, hFBF, hBFIsS⟩ := Th2.exists_maximal_elemAbelian (X := R) hFconjR hFconjEl
    have hBFrank : 4 ≤ pRank 2 ↥BF :=
      hFconjRank.ge.trans (C3.Layer1.Back.pRank_mono' hFBF)
    have hBFBT : BF ∈ Th2Row.BT .r4a x K T S := ⟨hBFIsS, hBFrank⟩
    exact hFBF.trans (le_iSup₂ (f := fun B' (_ : B' ∈ Th2Row.BT .r4a x K T S) => B')
      BF hBFBT)
  have hFconj4 : IsE 4 X (cj g⁻¹ F) := ⟨hFconjX, hFconjEl, hFconjRank.ge⟩
  obtain ⟨W, hWR, hWc, hWel, hW3⟩ := r4a_centralW h2
  have hconnF : RConnN 3 4 X F B :=
    rConnN_three_four_of_central hWR hWc hWel (by rw [hW3]) h2.mem F
      (isE_mono_rank hF4 (by norm_num : 3 ≤ 4))
  have hconnFconj : RConnN 3 4 X (cj g⁻¹ F) B :=
    rConnN_three_four_of_central hWR hWc hWel (by rw [hW3]) h2.mem (cj g⁻¹ F)
      (isE_mono_rank hFconj4 (by norm_num : 3 ≤ 4))
  have h74 : Th2Row.BT .r4a x K T S = {B' : Subgroup G | IsSn 4 X B'} := by
    change {B' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'} =
      {B' : Subgroup G |
        IsSn 4 (⨆ B' ∈ {B' : Subgroup G |
          IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'}, B') B'}
    exact Th2.isSn_tstar_eq ((T ⊓ K) ⊔ (T ⊓ CxK x K)) 4
  have hS : ∀ B' : Subgroup G, IsSn 4 X B' →
      IsE 4 ⊤ B' ∧ Th2Level.fiveHalves.IsBal B' := by
    intro B' hB'
    have hmem : B' ∈ Th2Row.BT .r4a x K T S := by rw [h74]; exact hB'
    exact ⟨⟨le_top, (h2.allIsE B' hmem).2.1, (h2.allIsE B' hmem).2.2⟩,
      h2.allBal B' hmem⟩
  have hthetaF : Th2Level.fiveHalves.theta F = Th2Level.fiveHalves.theta B :=
    theta_eq_of_conn .fiveHalves b_ig_21_8 h2110 hS
      (isE_mono_rank hF4 (by norm_num : 3 ≤ 4)) hconnF
  have hthetaFconj : Th2Level.fiveHalves.theta (cj g⁻¹ F) =
      Th2Level.fiveHalves.theta B :=
    theta_eq_of_conn .fiveHalves b_ig_21_8 h2110 hS
      (isE_mono_rank hFconj4 (by norm_num : 3 ≤ 4)) hconnFconj
  have hnat := theta_cj .fiveHalves g (cj g⁻¹ F)
  have hcj : cj g (cj g⁻¹ F) = F := by
    simpa using cj_cj_inv (g := g⁻¹) (H := F)
  rw [hcj, hthetaFconj] at hnat
  have hfix : cj g (Th2Level.fiveHalves.theta B) = Th2Level.fiveHalves.theta B :=
    hnat.symm.trans hthetaF
  exact h2.le_M (mem_normalizer_of_cj_eq hfix)

theorem r4a_T_le_M_of_M2 [Finite G] {x y : G} {K T S M B : Subgroup G}
    (h2110 : B_IG_21_10) (h2 : Th2M2 x y K T S M .r4a B) : T ≤ M := by
  intro g hgT
  by_cases hgK : g ∈ normalizer (K : Set G)
  · exact r4a_T_fixedK h2110 h2 g hgT hgK
  · have hne : cj g K ≠ K := by
      intro h
      exact hgK (mem_normalizer_of_cj_eq h)
    exact r4a_T_moved h2110 h2 g hgT hne

end CFSG.GH74.GLS.Th2
