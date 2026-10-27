module

public import CFSG.GH74.GLS.C3.Layer1.Th2HYM
public import CFSG.GH74.GLS.C3.Layer1.Th2P812Rows
public import CFSG.GH74.GLS.C3.Layer1.Th2L83GenCore
public import CFSG.GH74.GLS.C3.Layer1.Th2L84
public import CFSG.GH74.GLS.C3.Layer1.Th2P812

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.HY

@[expose] def B_thm2_p812_NV' : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G),
    Th2Std x y K T S → HasL2Model (kBar K) Odd → K ≤ M → T ≤ M →
      IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K) →
      ∀ L : Subgroup G, IsMinSubnormalIn K M L → IsPCompIn 2 M L → L = pPrimeCoreOf 2 L ⊔ K →
        ∀ V : Subgroup G, V ≤ T ⊓ CxK x K → CFSG.IsElementaryAbelian 2 ↥V → V ≠ ⊥ →
          IsSylowOf 2 (normalizer (V : Set G) ⊓ (T ⊓ CxK x K))
            (normalizer (V : Set G) ⊓ CMbar M K) →
          pPrimeCoreOf 2 (normalizer (V : Set G)) ≤ M →
          ∀ U : Subgroup G, IsFourSub (T ⊓ K) U →
            normalizer ((U ⊔ V : Subgroup G) : Set G) ≤ M →
            normalizer (((T ⊓ K) ⊔ (normalizer (V : Set G) ⊓ (T ⊓ CxK x K)) : Subgroup G) :
              Set G) ≤ M →
              normalizer (V : Set G) ≤ M


theorem b_thm2_p812_NV'_proved :
    B_thm2_p812_NV' := by
  intro G _ _ hG x y K T S M hstd hL2 hKM hTM hQ L hLmin hLcomp hLeq V hVQ hVel hVne hQ1 hO U hU
    hFUV hPQ₁
  have hS : HYSetup x y K T S V :=
    ⟨hstd, C3.Layer1.Back.isSimpleGroup_of_hasL2Model hL2,
      centerlessBar_of_hasL2Model (fun q hq => hq) hL2, hVQ, hVel, hVne⟩
  have ha := Q₁_sylow_YV hG hS hKM hO hLcomp hLeq hLmin.1 hU hFUV hQ1
  obtain ⟨H, hHN, hHnorm, hHM, hPH, hSyl⟩ := hS.exists_H_of_sylow hG hKM hO ha
  have hVnorm : ∀ n ∈ normalizer (V : Set G), ∀ v ∈ V, n * v * n⁻¹ ∈ V := fun n hn v hv =>
    (Subgroup.mem_normalizer_iff.1 hn v).1 hv
  have hFT : U ⊔ V ≤ T := sup_le (hU.1.trans inf_le_left) (hVQ.trans inf_le_left)
  exact Th2.P812.frattini_core hHnorm hHM hO (hU.1.trans hPH) hVnorm
    (hstd.T_pGroup.to_le hFT)
    (sup_le (hU.1.trans (hPH.trans hHN)) Subgroup.le_normalizer) hFUV hSyl hPQ₁


end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.Th2.P812

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2

variable {G : Type} [Group G]

theorem l812_core' [Finite G] (hG : C3Hyp G) (hNV : B_thm2_p812_NV') {x y : G}
    {K T S M X : Subgroup G} (h : Th2Std x y K T S) (hL2 : HasL2Model (kBar K) Odd) (hKM : K ≤ M)
    (hTM : T ≤ M) (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K))
    {L : Subgroup G} (hLmin : IsMinSubnormalIn K M L) (hLcomp : IsPCompIn 2 M L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) (hrk : 2 ≤ pRank 2 ↥(T ⊓ CxK x K)) {r : ℕ} (hr : r ≤ 3)
    (hBT : ∀ A' : Subgroup G, A' ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) → CFSG.IsElementaryAbelian 2 ↥A' →
      4 ≤ pRank 2 ↥A' → A' ≤ X)
    (hb : gammaK 2 X 4 ≤ M) (hc : ∀ A : Subgroup G, IsE 4 X A → gammaK 2 A r ≤ M)
    {V : Subgroup G} (hVQ : V ≤ T ⊓ CxK x K) (hVel : CFSG.IsElementaryAbelian 2 ↥V) (hVne : V ≠ ⊥)
    (hQ1 : IsSylowOf 2 (normalizer (V : Set G) ⊓ (T ⊓ CxK x K))
      (normalizer (V : Set G) ⊓ CMbar M K)) :
    normalizer (V : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPr : ∀ q : ℕ, Odd q → Odd q := fun q hq => hq
  have hcen := centerlessBar_of_hasL2Model hPr hL2
  have hP := rankTwoShape_sylow_L2 h.sylow_P (TwoThin.isQuasisimple_hat h.comp) hPr hL2
  have hPQ := h.commDisj hcen
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  have hQ2 : IsPGroup 2 ↥(T ⊓ CxK x K) := h.T_pGroup.to_le inf_le_left
  obtain ⟨E₁, hVE₁, hE₁S⟩ := Th2.exists_maximal_elemAbelian hVQ hVel
  have hE₁rk : 2 ≤ pRank 2 ↥E₁ := two_le_pRank_of_isS hQ2 hrk hE₁S
  obtain ⟨hE₁Q, hE₁el, -⟩ := hE₁S
  have hAel : CFSG.IsElementaryAbelian 2 ↥(U ⊔ E₁) :=
    hPQ.isElementaryAbelian_sup' hU.2.1 hE₁el hU.1 hE₁Q
  have hArk : 4 ≤ pRank 2 ↥(U ⊔ E₁) := by
    rw [hPQ.pRank_sup hU.2.1 hE₁el hU.1 hE₁Q, pRank_of_isFourSub hU]
    omega
  have hAR : U ⊔ E₁ ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := sup_le_sup hU.1 hE₁Q
  have hAX : U ⊔ E₁ ≤ X := hBT _ hAR hAel hArk
  set N : Subgroup G := normalizer (V : Set G) with hN
  have hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u := fun u hu v hv =>
    hPQ.comm u (hU.1 hu) v (hVQ hv)
  have hUN : U ≤ N := by
    intro u hu
    refine Subgroup.centralizer_le_normalizer (V : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hUV u hu v hv).symm
  have hE₁N : E₁ ≤ N := by
    intro e he
    refine Subgroup.centralizer_le_normalizer (V : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (C3.Layer1.Back.forall_of_isElementaryAbelian hE₁el).1 v (hVE₁ hv) e he
  have hAN : U ⊔ E₁ ≤ N := sup_le hUN hE₁N
  have hAM : gammaK 2 (U ⊔ E₁) r ≤ M := hc _ ⟨hAX, hAel, hArk⟩
  have hF : ∀ F : Subgroup G, F ≤ U ⊔ E₁ → r ≤ pRank 2 ↥F → normalizer (F : Set G) ≤ M := by
    intro F hFA hFr
    refine le_trans ?_ hAM
    unfold gammaK
    exact le_iSup₂_of_le F hFA (le_iSup_of_le hFr le_rfl)
  have hO : pPrimeCoreOf 2 N ≤ M :=
    Th2.L83.pPrimeCoreOf_le_of_normalizers (K := N) (X := N) (A := U ⊔ E₁)
      (fun a ha k hk => N.mul_mem (N.mul_mem ha hk) (N.inv_mem ha)) r hAel hAN (by omega) hF
  have hUVA : U ⊔ V ≤ U ⊔ E₁ := sup_le_sup le_rfl hVE₁
  have hUVrk : r ≤ pRank 2 ↥(U ⊔ V) := by
    rw [hPQ.pRank_sup hU.2.1 hVel hU.1 hVQ, pRank_of_isFourSub hU]
    have := one_le_pRank_of_ne_bot hVel hVne
    omega
  have hFUV := hF _ hUVA hUVrk
  set Q₁ : Subgroup G := N ⊓ (T ⊓ CxK x K) with hQ₁
  have hAPQ : U ⊔ E₁ ≤ (T ⊓ K) ⊔ Q₁ := sup_le_sup hU.1 (le_inf hE₁N hE₁Q)
  have hPQ₁R : (T ⊓ K) ⊔ Q₁ ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := sup_le_sup le_rfl inf_le_right
  have hPQ₁ : normalizer (((T ⊓ K) ⊔ Q₁ : Subgroup G) : Set G) ≤ M := by
    set X₁ : Subgroup G := ⨆ B ∈ {B : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ Q₁) B}, B with hX₁
    have hX₁X : X₁ ≤ X := by
      refine iSup₂_le fun B hB => ?_
      exact hBT B (hB.1.1.trans hPQ₁R) hB.1.2.1 hB.2
    have hAmem : U ⊔ E₁ ∈ {B : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ Q₁) B} :=
      ⟨isS_of_isE_rank hG hAPQ hAel hArk, hArk⟩
    have hX₁rk : 4 ≤ pRank 2 ↥X₁ :=
      hArk.trans (C3.Layer1.Back.pRank_mono' (le_iSup₂_of_le (U ⊔ E₁) hAmem le_rfl))
    intro a ha
    have ha' : a ∈ normalizer (X₁ : Set G) := Th2Tstar.mem_normalizer_biSup_isSn ha
    have hle : normalizer (X₁ : Set G) ≤ gammaK 2 X 4 := by
      unfold gammaK
      exact le_iSup₂_of_le X₁ hX₁X (le_iSup_of_le hX₁rk le_rfl)
    exact hb (hle ha')
  exact hNV G hG x y K T S M h hL2 hKM hTM hQ L hLmin hLcomp hLeq V hVQ hVel hVne hQ1 hO U hU hFUV hPQ₁

end CFSG.GH74.GLS.Th2.P812

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P812

variable {G : Type} [Group G]

theorem b_thm2_p812_II_of' (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82) (hNV : B_thm2_p812_NV')
    (hA7 : B_thm2_p812_A7) : B_thm2_p812_II := by
  intro G _ _ hG x y K T S M ρ B h2 hKM hQ L hL hLcomp hLeq hrk
  by_cases h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))
  · exact hA7 G hG x y K T S M ρ B h2 h7 hKM hQ L hL hLcomp hLeq hrk
  obtain ⟨hL2, hρ⟩ := l812_rows hL34 hG h2 h7
  have hTM : T ≤ M := t_le_M_of_M2 hL34 h82 hG h2
  obtain ⟨r, hr, hBT, hb, hc⟩ := l812_row_data h82 hG h2 hρ
  have hstd := h2.std
  refine gammaK_le_of_forall_elem (hstd.T_pGroup.to_le inf_le_left) (fun V hVQ hVel hVne => ?_)
  by_contra hNM
  obtain ⟨g, hgC, hVg, hSyl⟩ := exists_conj_sylow_normalizer hQ hVQ
  have hgM : g ∈ M := (inf_le_left : CMbar M K ≤ M) hgC
  have hV'el : CFSG.IsElementaryAbelian 2 ↥(V.map (MulAut.conj g).toMonoidHom) :=
    isElementaryAbelian_cj g hVel
  have hV'ne : V.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
    intro h0
    exact hVne ((Subgroup.map_eq_bot_iff_of_injective V (MulAut.conj g).injective).1 h0)
  have hN' := l812_core' hG hNV hstd hL2 hKM hTM hQ hL hLcomp hLeq hrk hr hBT hb hc hVg hV'el hV'ne hSyl
  apply hNM
  intro n hn
  have h1 : g * n * g⁻¹ ∈ normalizer ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [← Subgroup.map_normalizer_eq_of_bijective V (MulAut.conj g).bijective]
    exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
  have hn' : n = g⁻¹ * (g * n * g⁻¹) * g := by group
  rw [hn']
  exact M.mul_mem (M.mul_mem (M.inv_mem hgM) (hN' h1)) hgM

end CFSG.GH74.GLS
