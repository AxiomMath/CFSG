module

public import CFSG.GH74.GLS.C3.Layer1.Th2P88bNV

public section

namespace CFSG.GH74.GLS.Th2.P88b

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.HY
  CFSG.GH74.GLS.Th2.P812 CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.Th2.NV7 CFSG.GH74.GLS.Th2.P812A7

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_Q_of_struct {x y : G} {K T S M L : Subgroup G}
    (h : P85Struct x y K T S M L) : 2 ≤ pRank 2 ↥(T ⊓ CxK x K) := by
  have h1 := C3.Layer1.Back.card_eq_two_pow_pRank h.Qelem
  rw [h.Qcard] at h1
  have h2 : (2 : ℕ) ^ pRank 2 ↥(T ⊓ CxK x K) = 2 ^ 2 := by omega
  have h3 : pRank 2 ↥(T ⊓ CxK x K) = 2 := Nat.pow_right_injective (le_refl 2) h2
  omega

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers (x : G) :
    centralizer ({x} : Set G) ≤ normalizer ((zpowers x : Subgroup G) : Set G) := by
  intro n hn
  have hc : n * x = x * n := Subgroup.mem_centralizer_singleton_iff.1 hn
  have hcomm : ∀ k : ℤ, n * x ^ k * n⁻¹ = x ^ k := fun k => by
    have h1 : n * x ^ k = x ^ k * n := (Commute.zpow_right (show Commute n x from hc) k).eq
    rw [h1]
    group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [hcomm k]
    exact Subgroup.zpow_mem_zpowers x k
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
    have : h = x ^ k := by
      have h2 : n * h * n⁻¹ = x ^ k := hk.symm
      have h3 : n * x ^ k * n⁻¹ = x ^ k := hcomm k
      have h4 : n * h * n⁻¹ = n * x ^ k * n⁻¹ := h2.trans h3.symm
      simpa using h4
    rw [this]
    exact Subgroup.zpow_mem_zpowers x k

theorem cent_core_A7 (hG : C3Hyp G) {x y : G} {K T S M : Subgroup G} (hstd : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) (hKM : K ≤ M)
    (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K)) (hterm : IsTerminalSub (imgM M K))
    {U A : Subgroup G} (hU : IsDSub K (T ⊓ K) U) (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hUA : U ≤ A) (hxA : x ∈ A) (hA4 : 4 ≤ pRank 2 ↥A)
    (hF : ∀ F : Subgroup G, F ≤ A → 3 ≤ pRank 2 ↥F → normalizer (F : Set G) ≤ M) :
    centralizer ({x} : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : orderOf x = 2 := hstd.orderOf_x
  have hcen := centerlessBar_of_A7 h7
  have hPQ := hstd.commDisj hcen
  have hU4 : IsFourSub (T ⊓ K) U := IsDSub.isFourSub hU
  have hVel : CFSG.IsElementaryAbelian 2 ↥(zpowers x) :=
    isElementaryAbelian_zpowers_of_orderOf_two hx2
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx2
    omega
  have hVne : (zpowers x : Subgroup G) ≠ ⊥ := by
    intro h
    apply hx1
    have : x ∈ (zpowers x : Subgroup G) := Subgroup.mem_zpowers x
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hVQ : (zpowers x : Subgroup G) ≤ T ⊓ CxK x K :=
    (Subgroup.zpowers_le).2 ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩
  have hVA : (zpowers x : Subgroup G) ≤ A := (Subgroup.zpowers_le).2 hxA
  have hCN : centralizer ({x} : Set G) ≤ normalizer ((zpowers x : Subgroup G) : Set G) :=
    centralizer_le_normalizer_zpowers x
  have hAN : A ≤ normalizer ((zpowers x : Subgroup G) : Set G) := by
    intro a ha
    apply hCN
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (C3.Layer1.Back.forall_of_isElementaryAbelian hAel).1 a ha x hxA
  have hO : pPrimeCoreOf 2 (normalizer ((zpowers x : Subgroup G) : Set G)) ≤ M :=
    Th2.L83.pPrimeCoreOf_le_of_normalizers (K := normalizer ((zpowers x : Subgroup G) : Set G))
      (X := normalizer ((zpowers x : Subgroup G) : Set G)) (A := A)
      (fun a ha k hk => (normalizer ((zpowers x : Subgroup G) : Set G)).mul_mem
        ((normalizer ((zpowers x : Subgroup G) : Set G)).mul_mem ha hk)
        ((normalizer ((zpowers x : Subgroup G) : Set G)).inv_mem ha)) 3 hAel hAN (by omega) hF
  have hUVA : U ⊔ zpowers x ≤ A := sup_le hUA hVA
  have hUVrk : 3 ≤ pRank 2 ↥(U ⊔ zpowers x) := by
    rw [hPQ.pRank_sup hU4.2.1 hVel hU4.1 hVQ, pRank_of_isFourSub hU4]
    have := one_le_pRank_of_ne_bot hVel hVne
    omega
  have hFUV := hF _ hUVA hUVrk
  have hQN : T ⊓ CxK x K ≤ normalizer ((zpowers x : Subgroup G) : Set G) :=
    (inf_le_left.trans hstd.T_le_C).trans hCN
  have hQ1 : IsSylowOf 2 (normalizer ((zpowers x : Subgroup G) : Set G) ⊓ (T ⊓ CxK x K))
      (normalizer ((zpowers x : Subgroup G) : Set G) ⊓ CMbar M K) := by
    have heq : normalizer ((zpowers x : Subgroup G) : Set G) ⊓ (T ⊓ CxK x K) = T ⊓ CxK x K :=
      inf_eq_right.2 hQN
    rw [heq]
    exact isSylowOf_of_le_of_le hQ (le_inf hQN hQ.le) inf_le_right
  exact hCN.trans (nv7_term hG hstd h7 hKM hQ hterm hVQ hVel hVne hQ1 hO hU hFUV)

theorem cent_r3c (h82 : B_thm2_l82) (hG : C3Hyp G) {x y : G} {K T S M B : Subgroup G}
    (h2 : Th2M2 x y K T S M .r3c B) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hKM : K ≤ M) (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K))
    (hterm : IsTerminalSub (imgM M K)) (hrk : 2 ≤ pRank 2 ↥(T ⊓ CxK x K)) :
    centralizer ({x} : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := h2.std
  have h82' := h82 G hG x y K T S M .r3c B h2
  have hcen := centerlessBar_of_A7 h7
  have hPQ := hstd.commDisj hcen
  obtain ⟨U, hU⟩ := exists_isDSub hstd.sylow_P h7
  have hU4 : IsFourSub (T ⊓ K) U := IsDSub.isFourSub hU
  have hx2 : orderOf x = 2 := hstd.orderOf_x
  have hVel : CFSG.IsElementaryAbelian 2 ↥(zpowers x) :=
    isElementaryAbelian_zpowers_of_orderOf_two hx2
  have hVQ : (zpowers x : Subgroup G) ≤ T ⊓ CxK x K :=
    (Subgroup.zpowers_le).2 ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩
  have hQ2 : IsPGroup 2 ↥(T ⊓ CxK x K) := hstd.T_pGroup.to_le inf_le_left
  obtain ⟨E₁, hVE₁, hE₁S⟩ := Th2.exists_maximal_elemAbelian hVQ hVel
  have hE₁rk : 2 ≤ pRank 2 ↥E₁ := two_le_pRank_of_isS hQ2 hrk hE₁S
  obtain ⟨hE₁Q, hE₁el, -⟩ := hE₁S
  have hAel : CFSG.IsElementaryAbelian 2 ↥(U ⊔ E₁) :=
    hPQ.isElementaryAbelian_sup' hU4.2.1 hE₁el hU4.1 hE₁Q
  have hArk : 4 ≤ pRank 2 ↥(U ⊔ E₁) := by
    rw [hPQ.pRank_sup hU4.2.1 hE₁el hU4.1 hE₁Q, pRank_of_isFourSub hU4]
    omega
  have hAR : U ⊔ E₁ ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := sup_le_sup hU4.1 hE₁Q
  have hAX : U ⊔ E₁ ≤ Th2Row.r3c.Tstar x K T S :=
    Th2.le_Tstar (show (U ⊔ E₁) ∈ Th2Row.r3c.BT x K T S from
      ⟨⟨isS_of_isE_rank hG hAR hAel hArk, hArk⟩, U, hU, le_sup_left⟩)
  have hAM : gammaK 2 (U ⊔ E₁) 3 ≤ M := h82'.2.2.1 _ ⟨hAX, hAel, hArk⟩
  have hF : ∀ F : Subgroup G, F ≤ U ⊔ E₁ → 3 ≤ pRank 2 ↥F → normalizer (F : Set G) ≤ M := by
    intro F hFA hFr
    refine le_trans ?_ hAM
    unfold gammaK
    exact le_iSup₂_of_le F hFA (le_iSup_of_le hFr le_rfl)
  exact cent_core_A7 hG hstd h7 hKM hQ hterm hU hAel le_sup_left
    (Subgroup.mem_sup_right (hVE₁ (Subgroup.mem_zpowers x))) hArk hF

theorem cent_r3b (h82 : B_thm2_l82) (hG : C3Hyp G) {x y : G} {K T S M B : Subgroup G}
    (h2 : Th2M2 x y K T S M .r3b B) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hKM : K ≤ M) (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K))
    (hterm : IsTerminalSub (imgM M K)) : centralizer ({x} : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := h2.std
  have h82' := h82 G hG x y K T S M .r3b B h2
  obtain ⟨D, hD, hBeq⟩ := h2.mem
  obtain ⟨hBT, hBel, hBrk⟩ := h2.isE
  have hBrk4 : 4 ≤ pRank 2 ↥B := hBrk
  have hBS : IsS T B := isS_of_isE_rank hG hBT hBel hBrk4
  have hDB : D ≤ B := by
    rw [hBeq]
    exact le_iSup₂_of_le (1 : G) S.one_mem (fun d hd => ⟨d, hd, by simp⟩)
  have hxB : x ∈ B := by
    have hx2 : orderOf x = 2 := hstd.orderOf_x
    have hxx : x * x = 1 := by
      rw [← sq]
      have := pow_orderOf_eq_one x
      rwa [hx2] at this
    have hxω : x ∈ omega1 (T ⊓ centralizer (B : Set G)) :=
      Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨hstd.x_mem_T,
        Subgroup.mem_centralizer_iff.2 fun b hb =>
          Subgroup.mem_centralizer_singleton_iff.1 (hstd.T_le_C (hBT hb))⟩, hxx⟩
    rwa [← hBS.2.2] at hxω
  have hF : ∀ F : Subgroup G, F ≤ B → 3 ≤ pRank 2 ↥F → normalizer (F : Set G) ≤ M := by
    intro F hFB hFr
    refine le_trans ?_ h82'.2.2.2
    unfold gammaK
    exact le_iSup₂_of_le F hFB (le_iSup_of_le hFr le_rfl)
  exact cent_core_A7 hG hstd h7 hKM hQ hterm hD hBel hDB hxB hBrk4 hF

theorem centralizer_le_M_A7 (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82) {x y : G}
    {K T S M L : Subgroup G} (hstruct : P85Struct x y K T S M L)
    (hnt : ¬ IsTerminalPair 2 x K) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    centralizer ({x} : Set G) ≤ M := by
  have hG := hstruct.hG
  rcases hstruct.choice with hM1 | ⟨ρ, B, h2⟩
  · exact absurd hM1.terminal hnt
  have hstd := h2.std
  have hrow := h2.row
  have hrk := two_le_pRank_Q_of_struct hstruct
  cases ρ with
  | r1a => exact absurd h7 (Th2.not_nonempty_A7_of_hasL2Model hrow.1)
  | r1b => exact absurd h7 (Th2.not_nonempty_A7_of_hasL2Model hrow.1)
  | r2 =>
    have hrow' : HasL2Model (kBar K) (fun q => Odd q ∧ IsFM9 q ∧ q ≠ 5) := hrow
    exact absurd h7 (Th2.not_nonempty_A7_of_hasL2Model hrow')
  | r3a =>
    exact (false_of_three_le_rank_Q hG hstd (centerlessBar_of_A7 h7)
      (rankTwoShape_sylow_A7 hstd.sylow_P h7) hrow.2.2).elim
  | r3b => exact cent_r3b h82 hG h2 h7 hstruct.KM hstruct.hQ hstruct.terminal
  | r3c => exact cent_r3c h82 hG h2 h7 hstruct.KM hstruct.hQ hstruct.terminal hrk
  | r4a => exact absurd h7 (Th2.not_nonempty_A7_of_hasL2Model hrow.1)
  | r4b => exact absurd h7 (Th2.not_nonempty_A7_of_hasL2Model hrow.1)
  | r4c => exact absurd h7 (Th2.not_nonempty_A7_of_hasL2Model hrow.1)
  | r5 =>
    obtain ⟨hL34', hel, hcard⟩ := hrow
    exact (hL34 G hG.gen4 x K hstd.orderOf_x hstd.comp ⟨hL34', hel, hcard⟩).elim

theorem gammaK_le_M_nonA7
    (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82) {x y : G} {K T S M L : Subgroup G}
    (hstruct : P85Struct x y K T S M L) (hnt : ¬ IsTerminalPair 2 x K)
    (h7 : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    gammaK 2 (T ⊓ CxK x K) 1 ≤ M := by
  have hG := hstruct.hG
  rcases hstruct.choice with hM1 | ⟨ρ, B, h2⟩
  · exact absurd hM1.terminal hnt
  have hKM := hstruct.KM
  have hQ := hstruct.hQ
  have hterm := hstruct.terminal
  have hrk := two_le_pRank_Q_of_struct hstruct
  obtain ⟨hL2, hρ⟩ := l812_rows hL34 hG h2 h7
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
  have hN' := l812_core_term hG hstd hL2 hKM hQ hterm hrk hr hBT hb hc hVg hV'el hV'ne hSyl
  apply hNM
  intro n hn
  have h1 : g * n * g⁻¹ ∈
      normalizer ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [← Subgroup.map_normalizer_eq_of_bijective V (MulAut.conj g).bijective]
    exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
  have hn' : n = g⁻¹ * (g * n * g⁻¹) * g := by group
  rw [hn']
  exact M.mul_mem (M.mul_mem (M.inv_mem hgM) (hN' h1)) hgM

theorem centralizer_le_M_of_struct
    (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82) {x y : G} {K T S M L : Subgroup G}
    (hstruct : P85Struct x y K T S M L) (hnt : ¬ IsTerminalPair 2 x K) :
    centralizer ({x} : Set G) ≤ M := by
  by_cases h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))
  · exact centralizer_le_M_A7 hL34 h82 hstruct hnt h7
  · have hstd : Th2Std x y K T S := hstruct.choice.std
    exact (C3.Layer1.U1a.centralizer_le_gammaK (Q := T ⊓ CxK x K)
      ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩ hstd.orderOf_x).trans
      (gammaK_le_M_nonA7 hL34 h82 hstruct hnt h7)

end CFSG.GH74.GLS.Th2.P88b
