module

public import CFSG.GH74.GLS.C3.Layer1.Th2L74Main
public import CFSG.GH74.GLS.C3.Layer1.Th2Sig10
public import CFSG.GH74.GLS.C3.Layer1.Th2P815R4aT

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

@[expose] def B_thm2_l84_syl : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G),
    Th2Choice x y K T S M → K ≤ M → IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K)

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem mem_normalizer_inf' {A B : Subgroup G} {c : G} (hA : c ∈ normalizer (A : Set G))
    (hB : c ∈ normalizer (B : Set G)) : c ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA h, hB h]

end CFSG.GH74.GLS.Th2

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

section L84

variable {G : Type} [Group G] {x y : G} {K T S : Subgroup G}

theorem mem_normalizer_K_of_KN
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) {t : G}
    (ht : t ∈ centralizer ({x} : Set G)) : t ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨hKN t ht k, fun hk => ?_⟩
  have := hKN t⁻¹ (Subgroup.inv_mem _ ht) _ hk
  simpa [mul_assoc] using this

theorem Th2Std.mem_normalizer_P [Finite G] (h : Th2Std x y K T S)
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) {t : G} (ht : t ∈ T) :
    t ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) :=
  mem_normalizer_inf' (Subgroup.le_normalizer ht) (mem_normalizer_K_of_KN hKN (h.T_le_C ht))

theorem Th2Std.mem_normalizer_Q [Finite G] (h : Th2Std x y K T S)
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) {t : G} (ht : t ∈ T) :
    t ∈ normalizer ((T ⊓ CxK x K : Subgroup G) : Set G) :=
  mem_normalizer_inf' (Subgroup.le_normalizer ht)
    (NxK_le_normalizer_CxK x K ⟨h.T_le_C ht, mem_normalizer_K_of_KN hKN (h.T_le_C ht)⟩)

theorem Th2Std.mem_normalizer_R [Finite G] (h : Th2Std x y K T S)
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) {t : G} (ht : t ∈ T) :
    t ∈ normalizer (((T ⊓ K) ⊔ (T ⊓ CxK x K) : Subgroup G) : Set G) :=
  Th2.mem_normalizer_sup (h.mem_normalizer_P hKN ht) (h.mem_normalizer_Q hKN ht)

theorem Th2Std.K_normal_L2 [Finite G] (hG : C3Hyp G) (h : Th2Std x y K T S) {Pr : ℕ → Prop}
    (hPr : ∀ q, Pr q → Odd q) (hL2 : HasL2Model (kBar K) Pr) :
    ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  have hcen := centerlessBar_of_hasL2Model hPr hL2
  have hP := rankTwoShape_sylow_L2 h.sylow_P (TwoThin.isQuasisimple_hat h.comp) hPr hL2
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  refine h.K_normal (by rw [hG.pRank_eq_four]) hcen ?_
  have := C3.Layer1.Back.pRank_mono' hU.1
  rw [pRank_of_isFourSub hU] at this
  exact this

theorem Th2Std.K_normal_A7 [Finite G] (hG : C3Hyp G) (h : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  have hcen := centerlessBar_of_A7 h7
  have hP := rankTwoShape_sylow_A7 h.sylow_P h7
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  refine h.K_normal (by rw [hG.pRank_eq_four]) hcen ?_
  have := C3.Layer1.Back.pRank_mono' hU.1
  rw [pRank_of_isFourSub hU] at this
  exact this

theorem isDSub_conj {K P D : Subgroup G} {t : G} (ht : t ∈ normalizer (K : Set G))
    (htP : t ∈ normalizer (P : Set G)) (hD : IsDSub K P D) :
    IsDSub K P (D.map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨hDP, hPK, hDel, hDcard, e, he⟩ := hD
  have hKN : ∀ m ∈ normalizer (K : Set G), ∀ l ∈ K, m * l * m⁻¹ ∈ K := fun m hm l hl =>
    (Subgroup.mem_normalizer_iff.1 hm l).1 hl
  refine ⟨?_, hPK, isElementaryAbelian_cj t hDel, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 htP d).1 (hDP hd)
  · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
    exact hDcard
  · have key : ∀ (d : G) (hd : d ∈ K) (hd' : (MulAut.conj t).toMonoidHom d ∈ K),
        (C3.Layer1.Back.actHom hKN ⟨t, ht⟩).symm
          (QuotientGroup.mk (⟨(MulAut.conj t).toMonoidHom d, hd'⟩ : ↥K)) =
        QuotientGroup.mk (⟨d, hd⟩ : ↥K) := by
      intro d hd hd'
      rw [MulEquiv.symm_apply_eq]
      exact (C3.Layer1.Back.actHom_mk hKN ⟨t, ht⟩ ⟨d, hd⟩).symm
    refine ⟨(C3.Layer1.Back.actHom hKN ⟨t, ht⟩).symm.trans e, ?_⟩
    rw [← he]
    congr 1
    ext i
    constructor
    · rintro ⟨_, ⟨d, hd, rfl⟩, hd', hi⟩
      refine ⟨d, hd, hPK (hDP hd), ?_⟩
      rwa [MulEquiv.trans_apply, key d (hPK (hDP hd)) hd'] at hi
    · rintro ⟨d, hd, hd', hi⟩
      refine ⟨(MulAut.conj t).toMonoidHom d, ⟨d, hd, rfl⟩, hKN t ht d hd', ?_⟩
      rwa [MulEquiv.trans_apply, key d hd' (hKN t ht d hd')]

private theorem row3a_theta_eq_of_Keq [Finite G]
    {M B : Subgroup G} (h2 : Th2M2 x y K T S M .r3a B) {g : G}
    (hg : g ∈ T) (hKeq : cj g K = K) :
    (Th2Level.three).theta B = (Th2Level.three).theta (cj g B) := by
  let P : Subgroup G := T ⊓ K
  let Q : Subgroup G := T ⊓ CxK x K
  have hstd := h2.std
  have h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := h2.row.1
  obtain ⟨D0, hD0⟩ := exists_isDSub hstd.sylow_P h7
  have hBTeq := row3a_BT_eq_fam hstd h7 hD0
  have hBmem := h2.mem
  rw [hBTeq] at hBmem
  obtain ⟨E, hE, hErk, hBeq⟩ := hBmem
  have hgC : g ∈ centralizer ({x} : Set G) := hstd.T_le_C hg
  have hgN : g ∈ normalizer (K : Set G) := mem_normalizer_of_cj_eq hKeq
  have hgT : g ∈ normalizer (T : Set G) := Subgroup.le_normalizer hg
  have hgP : g ∈ normalizer (P : Set G) := mem_normalizer_inf' hgT hgN
  have hDg : IsDSub K P (cj g D0) := isDSub_conj hgN hgP hD0
  have hDg_eq : cj g D0 = D0 := isDSub_unique hstd.sylow_P hDg hD0
  have hTeq : cj g T = T := Th2Tstar.map_conj_eq_of_mem_normalizer hgT
  have hgNxK : g ∈ NxK x K := ⟨hgC, hgN⟩
  have hCxKeq : cj g (CxK x K) = CxK x K :=
    Th2Tstar.map_conj_eq_of_mem_normalizer (NxK_le_normalizer_CxK x K hgNxK)
  have hQeq : cj g Q = Q := by
    change (T ⊓ CxK x K).map (MulAut.conj g).toMonoidHom = T ⊓ CxK x K
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    change cj g T ⊓ cj g (CxK x K) = T ⊓ CxK x K
    rw [hTeq, hCxKeq]
  have hEs : IsS Q (cj g E) := by
    have hE0 : IsSn 0 Q E := ⟨hE, Nat.zero_le _⟩
    have hE0g : IsSn 0 (cj g Q) (cj g E) := Th2Tstar.isSn_map (MulAut.conj g) hE0
    rw [hQeq] at hE0g
    exact hE0g.1
  have hErk' : 3 ≤ CFSG.pRank 2 ↥(cj g E) := by
    rw [Th2.pRank_cj]
    exact hErk
  have hcjB : cj g B = D0 ⊔ cj g E := by
    calc cj g B = cj g (D0 ⊔ E) := by rw [hBeq]
      _ = cj g D0 ⊔ cj g E := Subgroup.map_sup _ _ _
      _ = D0 ⊔ cj g E := by rw [hDg_eq]
  have hBgFam : cj g B ∈ {B' : Subgroup G | ∃ E : Subgroup G,
      IsS Q E ∧ 3 ≤ CFSG.pRank 2 ↥E ∧ B' = D0 ⊔ E} :=
    ⟨cj g E, hEs, hErk', hcjB⟩
  have hBgBT : cj g B ∈ Th2Row.BT .r3a x K T S := by
    rw [hBTeq]
    exact hBgFam
  exact (row3a_theta_eq_of_BT b_ig_21_10 h2 hBgBT).symm

private theorem row3a_theta_eq_of_ne [Finite G]
    {M B : Subgroup G} (h2 : Th2M2 x y K T S M .r3a B) {g : G} (hg : g ∈ T)
    (hne : cj g K ≠ K) :
    (Th2Level.three).theta B = (Th2Level.three).theta (cj g B) := by
  let P : Subgroup G := T ⊓ K
  let Q : Subgroup G := T ⊓ CxK x K
  let Pg : Subgroup G := T ⊓ cj g K
  let Qg : Subgroup G := T ⊓ CxK x (cj g K)
  have hstd := h2.std
  have h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := h2.row.1
  have hconn : IsConn2 Q := h2.row.2.1
  have h3 : 3 ≤ CFSG.pRank 2 ↥Q := h2.row.2.2
  have hcen : CenterlessBar K := centerlessBar_of_A7 h7
  have hPQ : CommDisj P Q := hstd.commDisj hcen
  have hT2 : IsPGroup 2 ↥T := hstd.T_pGroup
  have hgC : g ∈ centralizer ({x} : Set G) := hstd.T_le_C hg
  have hTeq : cj g T = T := Th2Tstar.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)
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
  obtain ⟨D0, hD0⟩ := exists_isDSub hstd.sylow_P h7
  have hD0P : D0 ≤ P := hD0.1
  have hD0T : D0 ≤ T := hD0P.trans inf_le_left
  have hD0K : D0 ≤ K := hD0P.trans inf_le_right
  have hD0C : D0 ≤ centralizer ({x} : Set G) := hD0T.trans hstd.T_le_C
  have hxT : x ∈ T := hstd.x_mem_T
  have hxQ : x ∈ Q := ⟨hxT, hstd.x_mem_CxK⟩
  have hx2 : orderOf x = 2 := hstd.orderOf_x
  have hx_not_D0 : x ∉ D0 := by
    intro hxD0
    have hxK : x ∈ K := hD0K hxD0
    have hxO : x ∈ pPrimeCoreOf 2 K := by
      refine mem_pPrimeCoreOf_of_commutators hcen hxK (fun k hk => ?_)
      rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 (hstd.K_le_C hk))]
      exact one_mem _
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      have h := C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot K hT2
      have hx : x ∈ T ⊓ pPrimeCoreOf 2 K := ⟨hxT, hxO⟩
      rwa [h] at hx
    have hx1 : x = 1 := by simpa using hxbot
    have : orderOf x = 1 := by rw [hx1, orderOf_one]
    omega
  have hPgT : Pg ≤ T := inf_le_left
  have hPgC : Pg ≤ centralizer ({x} : Set G) := hPgT.trans hstd.T_le_C
  have hPgKg : Pg ≤ cj g K := inf_le_right
  have hPgCsecK : Pg ≤ Stage1.Thm2.Recip.cSec K := hPgKg.trans hKg_le_cSec_K
  have hPgQ : Pg ≤ Q := le_inf hPgT (le_inf hPgC hPgCsecK)
  have hD0Qg : D0 ≤ Qg := by
    refine le_inf hD0T (le_inf hD0C ?_)
    exact hD0K.trans hK_le_cSec_Kg
  have hPgEq : cj g P = Pg := by
    change (T ⊓ K).map (MulAut.conj g).toMonoidHom = T ⊓ cj g K
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    change cj g T ⊓ cj g K = T ⊓ cj g K
    rw [hTeq]
  let Dg : Subgroup G := cj g D0
  have hDgPg : Dg ≤ Pg := by
    rw [← hPgEq]
    exact Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hD0.1
  have hDgel : IsElementaryAbelian 2 ↥Dg := by
    change IsElementaryAbelian 2 ↥(cj g D0)
    exact isElementaryAbelian_cj g hD0.2.2.1
  have hDgcard : Nat.card ↥Dg = 4 := by
    rw [show Dg = cj g D0 from rfl,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hD0.2.2.2.1
  have hDg4 : IsFourSub Pg Dg := ⟨hDgPg, hDgel, hDgcard⟩
  have hDgQ : Dg ≤ Q := hDgPg.trans hPgQ
  have hDgT : Dg ≤ T := hDgPg.trans hPgT
  have hxDg_comm : ∀ d ∈ Dg, d * x = x * d := by
    intro d hd
    exact mem_centralizer_singleton_iff.1 (hstd.T_le_C (hDgT hd))
  have hx_not_Dg : x ∉ Dg := by
    intro hxDg
    have hxD0 : x ∈ D0 := by
      have h := (mem_cj_iff g D0 x).1 (by simpa [Dg] using hxDg)
      rwa [hgx'] at h
    exact hx_not_D0 hxD0
  have hDgx : CommDisj Dg (zpowers x) := by
    refine ⟨fun d hd y hy => ?_, ?_⟩
    · have hxCent : x ∈ centralizer ({d} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 (hstd.T_le_C (hDgT hd))).symm
      have hyCent : y ∈ centralizer ({d} : Set G) := (Subgroup.zpowers_le.2 hxCent) hy
      exact (Subgroup.mem_centralizer_singleton_iff.1 hyCent).symm
    · rw [eq_bot_iff]
      intro z hz
      rcases mem_zpowers_two hx2 hz.2 with rfl | rfl
      · exact one_mem _
      · exact False.elim (hx_not_Dg hz.1)
  have hx2pow : x ^ 2 = 1 := by
    rw [← hx2]
    exact pow_orderOf_eq_one x
  have hxel : IsElementaryAbelian 2 ↥(zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx2pow
  have hEel : IsElementaryAbelian 2 ↥(Dg ⊔ zpowers x) :=
    isElementaryAbelian_sup hDg4.2.1 hxel hDgx.comm
  have hEcard : Nat.card ↥(Dg ⊔ zpowers x) = 8 := by
    rw [hDgx.card_sup le_rfl le_rfl, hDg4.2.2, Nat.card_zpowers, hx2]
  have hErk : pRank 2 ↥(Dg ⊔ zpowers x) = 3 := by
    have h2 := C3.Layer1.Back.card_eq_two_pow_pRank hEel
    rw [hEcard] at h2
    have hpow : (2 : ℕ) ^ 3 = 2 ^ pRank 2 ↥(Dg ⊔ zpowers x) := by simpa using h2
    exact (Nat.pow_right_injective le_rfl hpow).symm
  let E : Subgroup G := Dg ⊔ zpowers x
  have hE_eq : E = Dg ⊔ zpowers x := rfl
  have hE_Q : E ≤ Q := by
    rw [hE_eq]
    exact sup_le hDgQ (zpowers_le.2 hxQ)
  have hD0E : CommDisj D0 E := by
    refine ⟨fun d hd e he => hPQ.comm d (hD0P hd) e (hE_Q he), ?_⟩
    rw [eq_bot_iff]
    intro z hz
    have hzPQ : z ∈ P ⊓ Q := ⟨hD0P hz.1, hE_Q hz.2⟩
    rwa [hPQ.inf] at hzPQ
  let F : Subgroup G := D0 ⊔ E
  have hF_eq : F = D0 ⊔ E := rfl
  have hFel : IsElementaryAbelian 2 ↥F := by
    rw [hF_eq]
    exact hD0E.isElementaryAbelian_sup' hD0.2.2.1 hEel le_rfl le_rfl
  have hD0rk : pRank 2 ↥D0 = 2 := Th2.pRank_of_isFourSub
    ⟨hD0P.trans inf_le_right, hD0.2.2.1, hD0.2.2.2.1⟩
  have hFrk : pRank 2 ↥F = 5 := by
    rw [hF_eq, hD0E.pRank_sup hD0.2.2.1 hEel le_rfl le_rfl, hD0rk, hErk]
  have hF5 : IsE 5 ⊤ F := ⟨le_top, hFel, by rw [hFrk]⟩
  have hF4 : IsE 4 ⊤ F := isE_mono_rank hF5 (by norm_num)
  obtain ⟨E1, hEE1, hE1S⟩ := Th2.exists_maximal_elemAbelian (X := Q) hE_Q hEel
  have hE1Q : E1 ≤ Q := hE1S.1
  have hQp : IsPGroup 2 ↥Q := hT2.to_le inf_le_left
  have hE1rk : 3 ≤ pRank 2 ↥E1 := Th2.isS_pRank_three_of_isConn2 hQp hconn h3 hE1S
  let B1 : Subgroup G := D0 ⊔ E1
  have hB1fam : B1 ∈ {B' : Subgroup G | ∃ E : Subgroup G,
      IsS Q E ∧ 3 ≤ CFSG.pRank 2 ↥E ∧ B' = D0 ⊔ E} :=
    ⟨E1, hE1S, hE1rk, rfl⟩
  have hBTeq := row3a_BT_eq_fam hstd h7 hD0
  have hB1BT : B1 ∈ Th2Row.BT .r3a x K T S := by
    rw [hBTeq]
    exact hB1fam
  have hB1el : IsElementaryAbelian 2 ↥B1 := by
    rw [show B1 = D0 ⊔ E1 from rfl]
    exact hPQ.isElementaryAbelian_sup' hD0.2.2.1 hE1S.2.1 hD0P hE1Q
  have hB1rk : 5 ≤ pRank 2 ↥B1 := by
    rw [show B1 = D0 ⊔ E1 from rfl,
      hPQ.pRank_sup hD0.2.2.1 hE1S.2.1 hD0P hE1Q, hD0rk]
    omega
  have hB1bal : (Th2Level.three).IsBal B1 := h2.allBal B1 hB1BT
  have hB1_5 : IsE 5 ⊤ B1 := ⟨le_top, hB1el, hB1rk⟩
  have hF_le_B1 : F ≤ B1 := by
    rw [hF_eq, show B1 = D0 ⊔ E1 from rfl]
    exact sup_le_sup le_rfl hEE1
  have hF4_B1 : IsE 4 B1 F := ⟨hF_le_B1, hFel, by omega⟩
  have hThetaF_B1 : (Th2Level.three).theta F = (Th2Level.three).theta B1 :=
    Th2.theta_eq_of_le Th2Level.three b_ig_21_8 b_ig_21_10 hB1_5 hB1bal hF4_B1
  have hThetaB1_B : (Th2Level.three).theta B1 = (Th2Level.three).theta B :=
    row3a_theta_eq_of_BT b_ig_21_10 h2 hB1BT
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
    change cj g (centralizer ({x} : Set G)) ⊓ cj g (centralizerSection K (pPrimeCoreOf 2 K)) =
      centralizer ({x} : Set G) ⊓ centralizerSection (cj g K) (pPrimeCoreOf 2 (cj g K))
    rw [cj_centralizer_singleton, hgx, hCsEq, pPrimeCoreOf_cj]
  have hQgEq : Qg = cj g Q := by
    change T ⊓ CxK x (cj g K) = (T ⊓ CxK x K).map (MulAut.conj g).toMonoidHom
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    change T ⊓ CxK x (cj g K) = cj g T ⊓ cj g (CxK x K)
    rw [hTeq, hCxKgEq]
  have hD0gQ : cj g⁻¹ D0 ≤ Q := by
    have hmap : cj g⁻¹ Qg = Q := by
      rw [hQgEq, cj_cj_inv]
    have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hD0Qg
    change cj g⁻¹ D0 ≤ cj g⁻¹ Qg at h
    rwa [hmap] at h
  have hD0g4 : IsFourSub Q (cj g⁻¹ D0) := by
    refine ⟨hD0gQ, isElementaryAbelian_cj g⁻¹ hD0.2.2.1, ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hD0.2.2.2.1]
  have hx_not_D0g : x ∉ cj g⁻¹ D0 := by
    intro hx
    have h := (mem_cj_iff g⁻¹ D0 x).1 hx
    have hx' : (g⁻¹)⁻¹ * x * g⁻¹ = x := by simpa using hgx
    rw [hx'] at h
    exact hx_not_D0 h
  have hD0gx : CommDisj (cj g⁻¹ D0) (zpowers x) := by
    refine ⟨fun d hd y hy => ?_, ?_⟩
    · have hxCent : x ∈ centralizer ({d} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 (hD0gQ hd).2.1).symm
      have hyCent : y ∈ centralizer ({d} : Set G) := (Subgroup.zpowers_le.2 hxCent) hy
      exact (Subgroup.mem_centralizer_singleton_iff.1 hyCent).symm
    · rw [eq_bot_iff]
      intro z hz
      rcases mem_zpowers_two hx2 hz.2 with rfl | rfl
      · exact one_mem _
      · exact False.elim (hx_not_D0g hz.1)
  have hW2el : IsElementaryAbelian 2 ↥(cj g⁻¹ D0 ⊔ zpowers x) :=
    isElementaryAbelian_sup hD0g4.2.1 hxel hD0gx.comm
  have hW2card : Nat.card ↥(cj g⁻¹ D0 ⊔ zpowers x) = 8 := by
    rw [hD0gx.card_sup le_rfl le_rfl, hD0g4.2.2, Nat.card_zpowers, hx2]
  have hW2rk : pRank 2 ↥(cj g⁻¹ D0 ⊔ zpowers x) = 3 := by
    have h2 := C3.Layer1.Back.card_eq_two_pow_pRank hW2el
    rw [hW2card] at h2
    have hpow : (2 : ℕ) ^ 3 = 2 ^ pRank 2 ↥(cj g⁻¹ D0 ⊔ zpowers x) := by simpa using h2
    exact (Nat.pow_right_injective le_rfl hpow).symm
  let W2 : Subgroup G := cj g⁻¹ D0 ⊔ zpowers x
  have hW2Q : W2 ≤ Q := by
    rw [show W2 = cj g⁻¹ D0 ⊔ zpowers x from rfl]
    exact sup_le hD0gQ (zpowers_le.2 hxQ)
  obtain ⟨E2', hW2E2, hE2'S⟩ := Th2.exists_maximal_elemAbelian (X := Q) hW2Q hW2el
  have hE2'Q : E2' ≤ Q := hE2'S.1
  have hE2'rk : 3 ≤ pRank 2 ↥E2' := Th2.isS_pRank_three_of_isConn2 hQp hconn h3 hE2'S
  let B2' : Subgroup G := D0 ⊔ E2'
  have hB2'fam : B2' ∈ {B' : Subgroup G | ∃ E : Subgroup G,
      IsS Q E ∧ 3 ≤ CFSG.pRank 2 ↥E ∧ B' = D0 ⊔ E} :=
    ⟨E2', hE2'S, hE2'rk, rfl⟩
  have hB2'BT : B2' ∈ Th2Row.BT .r3a x K T S := by
    rw [hBTeq]
    exact hB2'fam
  have hB2'el : IsElementaryAbelian 2 ↥B2' := by
    rw [show B2' = D0 ⊔ E2' from rfl]
    exact hPQ.isElementaryAbelian_sup' hD0.2.2.1 hE2'S.2.1 hD0P hE2'Q
  have hB2'rk : 5 ≤ pRank 2 ↥B2' := by
    rw [show B2' = D0 ⊔ E2' from rfl,
      hPQ.pRank_sup hD0.2.2.1 hE2'S.2.1 hD0P hE2'Q, hD0rk]
    omega
  have hB2'bal : (Th2Level.three).IsBal B2' := h2.allBal B2' hB2'BT
  have hB2'_5 : IsE 5 ⊤ B2' := ⟨le_top, hB2'el, hB2'rk⟩
  have hThetaB2'_B : (Th2Level.three).theta B2' = (Th2Level.three).theta B :=
    row3a_theta_eq_of_BT b_ig_21_10 h2 hB2'BT
  let B2 : Subgroup G := cj g B2'
  have hB2_eq : B2 = Dg ⊔ cj g E2' := by
    change (D0 ⊔ E2').map (MulAut.conj g).toMonoidHom = Dg ⊔ cj g E2'
    rw [Subgroup.map_sup]
  have hB2_5 : IsE 5 ⊤ B2 := by
    refine ⟨le_top, ?_, ?_⟩
    · change IsElementaryAbelian 2 ↥(cj g B2')
      exact isElementaryAbelian_cj g hB2'el
    · rw [show B2 = cj g B2' from rfl, pRank_cj]
      exact hB2'rk
  have hB2bal : (Th2Level.three).IsBal B2 := by
    rw [show B2 = cj g B2' from rfl]
    exact Th2.isKBal_cj g hB2'bal
  have hF_le_B2 : F ≤ B2 := by
    have hW2g : cj g W2 = D0 ⊔ zpowers x := by
      change (cj g⁻¹ D0 ⊔ zpowers x).map (MulAut.conj g).toMonoidHom = D0 ⊔ zpowers x
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      change cj g (cj g⁻¹ D0) ⊔ zpowers ((MulAut.conj g) x) = D0 ⊔ zpowers x
      rw [cj_inv_cj]
      simp [MulAut.conj_apply, hgx]
    have hW2g_le : cj g W2 ≤ B2 := by
      have hmap : cj g W2 ≤ cj g E2' :=
        Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hW2E2
      have hle : cj g E2' ≤ Dg ⊔ cj g E2' := le_sup_right
      rw [hB2_eq]
      exact hmap.trans hle
    have hD0B2 : D0 ≤ B2 := by
      have hD0W : D0 ≤ cj g W2 := by
        rw [hW2g]
        exact le_sup_left
      exact hD0W.trans hW2g_le
    have hDgB2 : Dg ≤ B2 := by
      rw [hB2_eq]
      exact le_sup_left
    have hxB2 : x ∈ B2 := by
      apply hW2g_le
      rw [hW2g]
      exact (le_sup_right : zpowers x ≤ D0 ⊔ zpowers x) (Subgroup.mem_zpowers x)
    rw [hF_eq]
    exact sup_le hD0B2 (sup_le hDgB2 (zpowers_le.2 hxB2))
  have hF4_B2 : IsE 4 B2 F := ⟨hF_le_B2, hFel, by omega⟩
  have hThetaF_B2 : (Th2Level.three).theta F = (Th2Level.three).theta B2 :=
    Th2.theta_eq_of_le Th2Level.three b_ig_21_8 b_ig_21_10 hB2_5 hB2bal hF4_B2
  have hThetaB2_Bg : (Th2Level.three).theta B2 = (Th2Level.three).theta (cj g B) := by
    calc (Th2Level.three).theta B2 = cj g ((Th2Level.three).theta B2') := Th2.theta_cj Th2Level.three g B2'
      _ = cj g ((Th2Level.three).theta B) := by rw [hThetaB2'_B]
      _ = (Th2Level.three).theta (cj g B) := (Th2.theta_cj Th2Level.three g B).symm
  have h1 : (Th2Level.three).theta F = (Th2Level.three).theta B :=
    hThetaF_B1.trans hThetaB1_B
  have h2 : (Th2Level.three).theta F = (Th2Level.three).theta (cj g B) :=
    hThetaF_B2.trans hThetaB2_Bg
  exact h1.symm.trans h2


theorem row3a_T_le_M_of_M2 [Finite G] {M B : Subgroup G}
    (h2 : Th2M2 x y K T S M .r3a B) : T ≤ M := by
  intro g hg
  have htheta : (Th2Level.three).theta B = (Th2Level.three).theta (cj g B) := by
    by_cases hKeq : cj g K = K
    · exact row3a_theta_eq_of_Keq h2 hg hKeq
    · exact row3a_theta_eq_of_ne h2 hg hKeq
  have hcjtheta : cj g ((Th2Level.three).theta B) = (Th2Level.three).theta B := by
    rw [← Th2.theta_cj Th2Level.three g B]
    exact htheta.symm
  exact h2.le_M (Th2.mem_normalizer_of_cj_eq hcjtheta)


theorem t_le_M_aux [Finite G] (h82 : B_thm2_l82) (hG : C3Hyp G) {M : Subgroup G} {ρ : Th2Row}
    {B : Subgroup G} (h2 : Th2M2 x y K T S M ρ B)
    (hN : ∀ t ∈ T, t ∈ normalizer ((ρ.Tstar x K T S : Subgroup G) : Set G))
    (hrk : ρ.level.n ≤ pRank 2 ↥(ρ.Tstar x K T S)) : T ≤ M := by
  intro t ht
  have hb := (h82 G hG x y K T S M ρ B h2).2.1
  have hN' : normalizer ((ρ.Tstar x K T S : Subgroup G) : Set G) ≤
      gammaK 2 (ρ.Tstar x K T S) ρ.level.n := by
    unfold gammaK
    exact le_iSup₂_of_le (ρ.Tstar x K T S) le_rfl (le_iSup_of_le hrk le_rfl)
  exact hb (hN' (hN t ht))

theorem t_le_M_of_M2 [Finite G] (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82) (hG : C3Hyp G)
    {M : Subgroup G} {ρ : Th2Row} {B : Subgroup G} (h2 : Th2M2 x y K T S M ρ B) : T ≤ M := by
  have hstd := h2.std
  have hrow := h2.row
  have hmem := h2.mem
  have hE := h2.isE
  cases ρ with
  | r1a =>
    obtain ⟨hL2, -, h3⟩ := hrow
    have hPr : ∀ q : ℕ, (Odd q ∧ ¬ IsFM9 q) → Odd q := fun q hq => hq.1
    exact (false_of_three_le_rank_Q hG hstd (centerlessBar_of_hasL2Model hPr hL2)
      (rankTwoShape_sylow_L2 hstd.sylow_P (TwoThin.isQuasisimple_hat hstd.comp) hPr hL2) h3).elim
  | r1b =>
    obtain ⟨hL2, -⟩ := hrow
    have hPr : ∀ q : ℕ, (Odd q ∧ ¬ IsFM9 q) → Odd q := fun q hq => hq.1
    have hKN := hstd.K_normal_L2 hG hPr hL2
    have hmem' : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B := hmem
    exact t_le_M_aux h82 hG h2
      (fun t ht => Th2Tstar.mem_normalizer_biSup_isSn (n := 4) (hstd.mem_normalizer_R hKN ht))
      (Th2Tstar.le_pRank_Tstar hmem hmem'.2)
  | r2 =>
    have hPr : ∀ q : ℕ, (Odd q ∧ IsFM9 q ∧ q ≠ 5) → Odd q := fun q hq => hq.1
    have hKN := hstd.K_normal_L2 hG hPr hrow
    have hmem' : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B := hmem
    exact t_le_M_aux h82 hG h2
      (fun t ht => Th2Tstar.mem_normalizer_biSup_isSn (n := 4) (hstd.mem_normalizer_R hKN ht))
      (Th2Tstar.le_pRank_Tstar hmem hmem'.2)
  | r3a =>
    exact row3a_T_le_M_of_M2 h2
  | r3b =>
    exact t_le_M_aux h82 hG h2 (fun t ht => Th2Tstar.mem_normalizer_Tstar_r3b (hstd.T_le_S ht))
      (Th2Tstar.le_pRank_Tstar hmem hE.2.2)
  | r3c =>
    obtain ⟨h7, -⟩ := hrow
    obtain ⟨D₀, hD₀⟩ := exists_isDSub hstd.sylow_P h7
    have hKN := hstd.K_normal_A7 hG h7
    have hTs : Th2Row.r3c.Tstar x K T S =
        ⨆ B' ∈ {B'' : Subgroup G | IsSn 4 (D₀ ⊔ (T ⊓ CxK x K)) B''}, B' := by
      show (⨆ B' ∈ {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'' ∧
        ∃ D, IsDSub K (T ⊓ K) D ∧ D ≤ B''}, B') = _
      rw [bt_3c_eq hstd h7 hD₀]
    have hmem' : B ∈ {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'' ∧
        ∃ D, IsDSub K (T ⊓ K) D ∧ D ≤ B''} := hmem
    have hDN : ∀ t ∈ T, t ∈ normalizer (D₀ : Set G) := by
      intro t ht
      have hD' := isDSub_conj (mem_normalizer_K_of_KN hKN (hstd.T_le_C ht))
        (hstd.mem_normalizer_P hKN ht) hD₀
      exact mem_normalizer_of_cj_eq (isDSub_unique hstd.sylow_P hD' hD₀)
    refine t_le_M_aux h82 hG h2 (fun t ht => ?_) ?_
    · rw [hTs]
      exact Th2Tstar.mem_normalizer_biSup_isSn (n := 4)
        (Th2.mem_normalizer_sup (hDN t ht) (hstd.mem_normalizer_Q hKN ht))
    · exact Th2Tstar.le_pRank_Tstar hmem hmem'.1.2
  | r4a =>
    exact r4a_T_le_M_of_M2 b_ig_21_10 h2
  | r4b =>
    have hmem' : IsSn 4 T B := hmem
    exact t_le_M_aux h82 hG h2
      (fun t ht => Th2Tstar.mem_normalizer_biSup_isSn (n := 4) (Subgroup.le_normalizer ht))
      (Th2Tstar.le_pRank_Tstar hmem hmem'.2)
  | r4c =>
    have hmem' : IsSn 4 T B := hmem
    exact t_le_M_aux h82 hG h2
      (fun t ht => Th2Tstar.mem_normalizer_biSup_isSn (n := 4) (Subgroup.le_normalizer ht))
      (Th2Tstar.le_pRank_Tstar hmem hmem'.2)
  | r5 =>
    obtain ⟨hL34', hel, hcard⟩ := hrow
    exact (hL34 G hG.gen4 x K hstd.orderOf_x hstd.comp ⟨hL34', hel, hcard⟩).elim

theorem b_thm2_l84_of (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82) (hsyl : B_thm2_l84_syl) :
    B_thm2_l84 := by
  intro G _ _ hG x y K T S M hchoice hKM
  refine ⟨hsyl G hG x y K T S M hchoice hKM, fun hnt => ?_⟩
  rcases hchoice with h1 | ⟨ρ, B, h2⟩
  · exact absurd h1.terminal hnt
  · exact t_le_M_of_M2 hL34 h82 hG h2

end L84

end CFSG.GH74.GLS
