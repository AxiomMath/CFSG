module

public import CFSG.GH74.GLS.C3.Layer1.Th2NV7Top

public section

namespace CFSG.GH74.GLS.Th2.NV7

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P812
  CFSG.GH74.GLS.Th2.P812A7
open scoped commutatorElement

variable {G : Type} [Group G]

theorem l812_coreA7' [Finite G] (hG : C3Hyp G) (hNV : B_thm2_p812_NV7') {x y : G}
    {K T S M X : Subgroup G} (h : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) (hKM : K ≤ M)
    (hTM : T ≤ M) (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K))
    {L : Subgroup G} (hLmin : IsMinSubnormalIn K M L) (hLcomp : IsPCompIn 2 M L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K)
    (hrk : 2 ≤ pRank 2 ↥(T ⊓ CxK x K))
    (hBT : ∀ A' : Subgroup G, IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) A' →
      (∃ D : Subgroup G, IsDSub K (T ⊓ K) D ∧ D ≤ A') → A' ≤ X)
    (hb : gammaK 2 X 4 ≤ M) (hc : ∀ A : Subgroup G, IsE 4 X A → gammaK 2 A 3 ≤ M)
    {V : Subgroup G} (hVQ : V ≤ T ⊓ CxK x K) (hVel : CFSG.IsElementaryAbelian 2 ↥V) (hVne : V ≠ ⊥)
    (hQ1 : IsSylowOf 2 (normalizer (V : Set G) ⊓ (T ⊓ CxK x K))
      (normalizer (V : Set G) ⊓ CMbar M K)) :
    normalizer (V : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen := centerlessBar_of_A7 h7
  have hPQ := h.commDisj hcen
  obtain ⟨U, hU⟩ := exists_isDSub h.sylow_P h7
  have hU4 : IsFourSub (T ⊓ K) U := Th2.P812A7.IsDSub.isFourSub hU
  have hQ2 : IsPGroup 2 ↥(T ⊓ CxK x K) := h.T_pGroup.to_le inf_le_left
  obtain ⟨E₁, hVE₁, hE₁S⟩ := Th2.exists_maximal_elemAbelian hVQ hVel
  have hE₁rk : 2 ≤ pRank 2 ↥E₁ := two_le_pRank_of_isS hQ2 hrk hE₁S
  obtain ⟨hE₁Q, hE₁el, -⟩ := hE₁S
  have hAel : CFSG.IsElementaryAbelian 2 ↥(U ⊔ E₁) :=
    hPQ.isElementaryAbelian_sup' hU4.2.1 hE₁el hU4.1 hE₁Q
  have hArk : 4 ≤ pRank 2 ↥(U ⊔ E₁) := by
    rw [hPQ.pRank_sup hU4.2.1 hE₁el hU4.1 hE₁Q, pRank_of_isFourSub hU4]
    omega
  have hAR : U ⊔ E₁ ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := sup_le_sup hU4.1 hE₁Q
  have hAX : U ⊔ E₁ ≤ X :=
    hBT _ ⟨isS_of_isE_rank hG hAR hAel hArk, hArk⟩ ⟨U, hU, le_sup_left⟩
  set N : Subgroup G := normalizer (V : Set G) with hN
  have hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u := fun u hu v hv =>
    hPQ.comm u (hU4.1 hu) v (hVQ hv)
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
  have hAM : gammaK 2 (U ⊔ E₁) 3 ≤ M := hc _ ⟨hAX, hAel, hArk⟩
  have hF : ∀ F : Subgroup G, F ≤ U ⊔ E₁ → 3 ≤ pRank 2 ↥F → normalizer (F : Set G) ≤ M := by
    intro F hFA hFr
    refine le_trans ?_ hAM
    unfold gammaK
    exact le_iSup₂_of_le F hFA (le_iSup_of_le hFr le_rfl)
  have hO : pPrimeCoreOf 2 N ≤ M :=
    Th2.L83.pPrimeCoreOf_le_of_normalizers (K := N) (X := N) (A := U ⊔ E₁)
      (fun a ha k hk => N.mul_mem (N.mul_mem ha hk) (N.inv_mem ha)) 3 hAel hAN (by omega) hF
  have hUVA : U ⊔ V ≤ U ⊔ E₁ := sup_le_sup le_rfl hVE₁
  have hUVrk : 3 ≤ pRank 2 ↥(U ⊔ V) := by
    rw [hPQ.pRank_sup hU4.2.1 hVel hU4.1 hVQ, pRank_of_isFourSub hU4]
    have := one_le_pRank_of_ne_bot hVel hVne
    omega
  have hFUV := hF _ hUVA hUVrk
  set Q₁ : Subgroup G := N ⊓ (T ⊓ CxK x K) with hQ₁
  have hAUQ : U ⊔ E₁ ≤ U ⊔ Q₁ := sup_le_sup le_rfl (le_inf hE₁N hE₁Q)
  have hUQ₁R : U ⊔ Q₁ ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := sup_le_sup hU4.1 inf_le_right
  have hUQ₁ : normalizer ((U ⊔ Q₁ : Subgroup G) : Set G) ≤ M := by
    set X₁ : Subgroup G := ⨆ B ∈ {B : Subgroup G | IsSn 4 (U ⊔ Q₁) B}, B with hX₁
    have hX₁X : X₁ ≤ X := by
      refine iSup₂_le fun B hB => ?_
      obtain ⟨⟨hBX, hBel, hBeq⟩, hBrk⟩ := hB
      have hBR : B ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := hBX.trans hUQ₁R
      refine hBT B ⟨isS_of_isE_rank hG hBR hBel hBrk, hBrk⟩ ⟨U, hU, ?_⟩
      have hUQcomm : ∀ a ∈ U, ∀ c ∈ Q₁, a * c = c * a := fun a ha c hc =>
        hPQ.comm a (hU4.1 ha) c hc.2
      have hUc : U ≤ centralizer (B : Set G) := by
        intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        obtain ⟨u', hu', q, hq, hbuq⟩ := CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute hUQcomm (hBX hb)
        have h1 : u * u' = u' * u :=
          (C3.Layer1.Back.forall_of_isElementaryAbelian hU4.2.1).1 u hu u' hu'
        have h2 : u * q = q * u := hUQcomm u hu q hq
        rw [hbuq]
        calc u' * q * u = u' * (q * u) := by group
          _ = u' * (u * q) := by rw [h2]
          _ = (u' * u) * q := by group
          _ = (u * u') * q := by rw [h1]
          _ = u * (u' * q) := by group
      have hUle : U ≤ omega1 ((U ⊔ Q₁) ⊓ centralizer (B : Set G)) :=
        le_omega1_of_isElementaryAbelian hU4.2.1 (le_inf le_sup_left hUc)
      exact hUle.trans hBeq.ge
    have hAmem : U ⊔ E₁ ∈ {B : Subgroup G | IsSn 4 (U ⊔ Q₁) B} :=
      ⟨isS_of_isE_rank hG hAUQ hAel hArk, hArk⟩
    have hX₁rk : 4 ≤ pRank 2 ↥X₁ :=
      hArk.trans (C3.Layer1.Back.pRank_mono' (le_iSup₂_of_le (U ⊔ E₁) hAmem le_rfl))
    intro a ha
    have ha' : a ∈ normalizer (X₁ : Set G) := Th2Tstar.mem_normalizer_biSup_isSn ha
    have hle : normalizer (X₁ : Set G) ≤ gammaK 2 X 4 := by
      unfold gammaK
      exact le_iSup₂_of_le X₁ hX₁X (le_iSup_of_le hX₁rk le_rfl)
    exact hb (hle ha')
  exact hNV G hG x y K T S M h h7 hKM hTM hQ L hLmin hLcomp hLeq V hVQ hVel hVne hQ1 hO U hU hFUV hUQ₁

theorem gamma_of_r3c' [Finite G] (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82)
    (hNV : B_thm2_p812_NV7') (hG : C3Hyp G) {x y : G} {K T S M B : Subgroup G}
    (h2 : Th2M2 x y K T S M .r3c B) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hKM : K ≤ M) (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K))
    {L : Subgroup G} (hLmin : IsMinSubnormalIn K M L) (hLcomp : IsPCompIn 2 M L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K)
    (hrk : 2 ≤ pRank 2 ↥(T ⊓ CxK x K)) : gammaK 2 (T ⊓ CxK x K) 1 ≤ M := by
  have hstd := h2.std
  have hTM : T ≤ M := t_le_M_of_M2 hL34 h82 hG h2
  have h82' := h82 G hG x y K T S M .r3c B h2
  refine gammaK_le_of_forall_elem (hstd.T_pGroup.to_le inf_le_left) (fun V hVQ hVel hVne => ?_)
  by_contra hNM
  obtain ⟨g, hgC, hVg, hSyl⟩ := exists_conj_sylow_normalizer hQ hVQ
  have hgM : g ∈ M := (inf_le_left : CMbar M K ≤ M) hgC
  have hV'el : CFSG.IsElementaryAbelian 2 ↥(V.map (MulAut.conj g).toMonoidHom) :=
    isElementaryAbelian_cj g hVel
  have hV'ne : V.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
    intro h0
    exact hVne ((Subgroup.map_eq_bot_iff_of_injective V (MulAut.conj g).injective).1 h0)
  have hN' := l812_coreA7' hG hNV hstd h7 hKM hTM hQ hLmin hLcomp hLeq hrk
    (fun A' hA' hD => Th2.le_Tstar (show A' ∈ Th2Row.r3c.BT x K T S from ⟨hA', hD⟩))
    h82'.2.1 h82'.2.2.1 hVg hV'el hV'ne hSyl
  apply hNM
  intro n hn
  have h1 : g * n * g⁻¹ ∈ normalizer ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [← Subgroup.map_normalizer_eq_of_bijective V (MulAut.conj g).bijective]
    exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
  have hn' : n = g⁻¹ * (g * n * g⁻¹) * g := by group
  rw [hn']
  exact M.mul_mem (M.mul_mem (M.inv_mem hgM) (hN' h1)) hgM

end CFSG.GH74.GLS.Th2.NV7

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P812A7 CFSG.GH74.GLS.Th2.NV7

theorem b_thm2_p812_A7_of' (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82)
    (hNV : B_thm2_p812_NV7') : B_thm2_p812_A7 := by
  intro G _ _ hG x y K T S M ρ B h2 h7 hKM hQ L hL hLcomp hLeq hrk
  have hstd := h2.std
  have hrow := h2.row
  cases ρ with
  | r1a => exact absurd h7 (Th2.not_nonempty_A7_of_hasL2Model hrow.1)
  | r1b => exact absurd h7 (Th2.not_nonempty_A7_of_hasL2Model hrow.1)
  | r2 =>
    have hrow' : HasL2Model (kBar K) (fun q => Odd q ∧ IsFM9 q ∧ q ≠ 5) := hrow
    exact absurd h7 (Th2.not_nonempty_A7_of_hasL2Model hrow')
  | r3a =>
    exact (false_of_three_le_rank_Q hG hstd (centerlessBar_of_A7 h7)
      (rankTwoShape_sylow_A7 hstd.sylow_P h7) hrow.2.2).elim
  | r3b => exact (false_of_r3b h2 hL hLcomp hLeq hQ (s_le_M_r3b h82 hG h2)).elim
  | r3c => exact gamma_of_r3c' hL34 h82 hNV hG h2 h7 hKM hQ hL hLcomp hLeq hrk
  | r4a => exact absurd h7 (Th2.not_nonempty_A7_of_hasL2Model hrow.1)
  | r4b => exact absurd h7 (Th2.not_nonempty_A7_of_hasL2Model hrow.1)
  | r4c => exact absurd h7 (Th2.not_nonempty_A7_of_hasL2Model hrow.1)
  | r5 =>
    obtain ⟨hL34', hel, hcard⟩ := hrow
    exact (hL34 G hG.gen4 x K hstd.orderOf_x hstd.comp ⟨hL34', hel, hcard⟩).elim

theorem b_thm2_p812_A7_proved (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82) :
    B_thm2_p812_A7 :=
  b_thm2_p812_A7_of' hL34 h82 b_thm2_p812_NV7'_proved

end CFSG.GH74.GLS
