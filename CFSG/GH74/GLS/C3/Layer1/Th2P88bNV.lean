module

public import CFSG.GH74.GLS.C3.Layer1.Th2P88bY
public import CFSG.GH74.GLS.C3.Layer1.Th2NV7Core
public import CFSG.GH74.GLS.C3.Layer1.Th2NV7Frat
public import CFSG.GH74.GLS.C3.Layer1.Th2P812A7

public section

namespace CFSG.GH74.GLS.Th2.P88b

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.HY
  CFSG.GH74.GLS.Th2.P812 CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.Th2.NV7

variable {G : Type} [Group G] [Finite G]

theorem nv_term
    (hG : C3Hyp G) {x y : G} {K T S M : Subgroup G} (hstd : Th2Std x y K T S)
    (hL2 : HasL2Model (kBar K) Odd) (hKM : K ≤ M) (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K))
    (hterm : IsTerminalSub (imgM M K)) {V : Subgroup G} (hVQ : V ≤ T ⊓ CxK x K)
    (hVel : CFSG.IsElementaryAbelian 2 ↥V) (hVne : V ≠ ⊥)
    (hQ1 : IsSylowOf 2 (normalizer (V : Set G) ⊓ (T ⊓ CxK x K))
      (normalizer (V : Set G) ⊓ CMbar M K))
    (hO : pPrimeCoreOf 2 (normalizer (V : Set G)) ≤ M) {U : Subgroup G}
    (hU : IsFourSub (T ⊓ K) U) (hFUV : normalizer ((U ⊔ V : Subgroup G) : Set G) ≤ M)
    (hPQ₁ : normalizer (((T ⊓ K) ⊔ (normalizer (V : Set G) ⊓ (T ⊓ CxK x K)) : Subgroup G) :
      Set G) ≤ M) :
    normalizer (V : Set G) ≤ M := by
  have hS : HYSetup x y K T S V :=
    ⟨hstd, C3.Layer1.Back.isSimpleGroup_of_hasL2Model hL2,
      centerlessBar_of_hasL2Model (fun q hq => hq) hL2, hVQ, hVel, hVne⟩
  have hVC : V ≤ CMbar M K := hVQ.trans hQ.le
  have ha := Q₁_sylow_YV_term hG hS hKM hO hterm hVC hU hFUV hQ1
  obtain ⟨H, hHN, hHnorm, hHM, hPH, hSyl⟩ := hS.exists_H_of_sylow hG hKM hO ha
  have hVnorm : ∀ n ∈ normalizer (V : Set G), ∀ v ∈ V, n * v * n⁻¹ ∈ V := fun n hn v hv =>
    (Subgroup.mem_normalizer_iff.1 hn v).1 hv
  have hFT : U ⊔ V ≤ T := sup_le (hU.1.trans inf_le_left) (hVQ.trans inf_le_left)
  exact Th2.P812.frattini_core hHnorm hHM hO (hU.1.trans hPH) hVnorm
    (hstd.T_pGroup.to_le hFT)
    (sup_le (hU.1.trans (hPH.trans hHN)) Subgroup.le_normalizer) hFUV hSyl hPQ₁

theorem l812_core_term
    (hG : C3Hyp G) {x y : G}
    {K T S M X : Subgroup G} (h : Th2Std x y K T S) (hL2 : HasL2Model (kBar K) Odd) (hKM : K ≤ M)
    (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K)) (hterm : IsTerminalSub (imgM M K))
    (hrk : 2 ≤ pRank 2 ↥(T ⊓ CxK x K)) {r : ℕ} (hr : r ≤ 3)
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
  exact nv_term hG h hL2 hKM hQ hterm hVQ hVel hVne hQ1 hO hU hFUV hPQ₁

theorem mem_M_of_normalizes_S₀_UV (hG : C3Hyp G) {x y : G} {K T S V : Subgroup G}
    (hS : HYSetup x y K T S V) {M U : Subgroup G} (hU : IsDSub K (T ⊓ K) U)
    (hFUV : normalizer ((U ⊔ V : Subgroup G) : Set G) ≤ M) {m : G}
    (hmN : m ∈ normalizer (V : Set G))
    (hmS : m ∈ normalizer
      ((((T ⊓ K) ⊔ (normalizer (V : Set G) ⊓ (T ⊓ CxK x K)) : Subgroup G)) : Set G)) : m ∈ M := by
  obtain ⟨hmP, -⟩ := mem_normalizer_P_Q₁ hG hS hmN hmS
  have hmU : m ∈ normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => conj_mem_U hG hS hU hmN hmP u hu, fun hu => ?_⟩
    have := conj_mem_U hG hS hU (Subgroup.inv_mem _ hmN) (Subgroup.inv_mem _ hmP) _ hu
    simpa [mul_assoc] using this
  exact hFUV (Th2.mem_normalizer_sup hmU hmN)

theorem nv7_term (hG : C3Hyp G) {x y : G} {K T S M : Subgroup G} (hstd : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) (hKM : K ≤ M)
    (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K)) (hterm : IsTerminalSub (imgM M K))
    {V : Subgroup G} (hVQ : V ≤ T ⊓ CxK x K) (hVel : CFSG.IsElementaryAbelian 2 ↥V)
    (hVne : V ≠ ⊥)
    (hQ1 : IsSylowOf 2 (normalizer (V : Set G) ⊓ (T ⊓ CxK x K))
      (normalizer (V : Set G) ⊓ CMbar M K))
    (hO : pPrimeCoreOf 2 (normalizer (V : Set G)) ≤ M) {U : Subgroup G}
    (hU : IsDSub K (T ⊓ K) U) (hFUV : normalizer ((U ⊔ V : Subgroup G) : Set G) ≤ M) :
    normalizer (V : Set G) ≤ M := by
  obtain ⟨e7⟩ := h7
  have hsimple : IsSimpleGroup (kBar K) := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
    exact MulEquiv.isSimpleGroup e7
  have hS : HYSetup x y K T S V :=
    ⟨hstd, hsimple, centerlessBar_of_A7 ⟨e7⟩, hVQ, hVel, hVne⟩
  have hU4 : IsFourSub (T ⊓ K) U := Th2.P812A7.IsDSub.isFourSub hU
  have hVC : V ≤ CMbar M K := hVQ.trans hQ.le
  have ha := Q₁_sylow_YV_term hG hS hKM hO hterm hVC hU4 hFUV hQ1
  have hSyl := hS.sylow_HY hG ha
  have hVnorm : ∀ n ∈ normalizer (V : Set G), ∀ v ∈ V, n * v * n⁻¹ ∈ V := fun n hn v hv =>
    (Subgroup.mem_normalizer_iff.1 hn v).1 hv
  have hFT : U ⊔ V ≤ T := sup_le (hU.1.trans inf_le_left) (hVQ.trans inf_le_left)
  have hPH : T ⊓ K ≤ HV K V := hS.P_le_lamV.trans le_sup_left
  exact frattini_core' (HYSetup.HV_le_N K V) (hS.hnormH hG)
    (sup_le ((twoGen_le _).trans (inf_le_left.trans hKM)) hO) hO (hU.1.trans hPH) hVnorm
    (hstd.T_pGroup.to_le hFT)
    (sup_le (hU.1.trans (hPH.trans (HYSetup.HV_le_N K V))) Subgroup.le_normalizer) hFUV hSyl
    (fun m hmN hmS => mem_M_of_normalizes_S₀_UV hG hS hU hFUV hmN hmS)

end CFSG.GH74.GLS.Th2.P88b
