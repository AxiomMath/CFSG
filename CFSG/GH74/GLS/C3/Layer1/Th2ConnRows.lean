module

public import CFSG.GH74.GLS.C3.Layer1.Th2Struct
public import CFSG.GH74.GLS.C3.Layer1.Th2A7
public import CFSG.GH74.GLS.C3.Layer1.Th2Dih

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

@[expose] def B_thm2_A7_3b : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
      Nat.card ↥(T ⊓ CxK x K) = 4 → T < S → ∀ D : Subgroup G, IsDSub K (T ⊓ K) D →
        CFSG.IsElementaryAbelian 2 ↥(⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom) ∧
          4 ≤ pRank 2 ↥(⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom)

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem isFourSub_of_isS [Finite G] {P U : Subgroup G} (hP : RankTwoShape P) (hU : IsS P U) :
    IsFourSub P U := by
  obtain ⟨V, hUV, hV⟩ := hP.2.1 U hU.1 hU.2.1
  have hVU : V ≤ U := by
    obtain ⟨hUP, -, hUeq⟩ := hU
    rw [hUeq]
    refine le_omega1_of_isElementaryAbelian hV.2.1 (le_inf hV.1 ?_)
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (C3.Layer1.Back.forall_of_isElementaryAbelian hV.2.1).1 u (hUV hu) v hv
  exact (le_antisymm hVU hUV) ▸ hV

theorem isS_sup_iff_add_two [Finite G] {P Q : Subgroup G} (h : CommDisj P Q)
    (hP : RankTwoShape P) (n : ℕ) (B : Subgroup G) :
    IsSn (n + 2) (P ⊔ Q) B ↔ ∃ U : Subgroup G, IsFourSub P U ∧
      ∃ E : Subgroup G, IsS Q E ∧ n ≤ CFSG.pRank 2 ↥E ∧ B = U ⊔ E := by
  constructor
  · rintro ⟨hBS, hrk⟩
    obtain ⟨hBeq, hUS, hES⟩ := h.isS_proj hBS
    have hU := isFourSub_of_isS hP hUS
    refine ⟨h.projP B, hU, h.projQ B, hES, ?_, hBeq⟩
    have := h.pRank_sup hUS.2.1 hES.2.1 hUS.1 hES.1
    rw [← hBeq, pRank_of_isFourSub hU] at this
    omega
  · rintro ⟨U, hU, E, hE, hrk, rfl⟩
    refine ⟨h.isS_sup (isS_of_isFourSub hP hU) hE, ?_⟩
    rw [h.pRank_sup hU.2.1 hE.2.1 hU.1 hE.1, pRank_of_isFourSub hU]
    omega

theorem isS_sup_iff [Finite G] {P Q : Subgroup G} (h : CommDisj P Q) (hP : RankTwoShape P)
    (B : Subgroup G) :
    IsSn 4 (P ⊔ Q) B ↔ ∃ U : Subgroup G, IsFourSub P U ∧ ∃ E : Subgroup G, IsS Q E ∧
      2 ≤ pRank 2 ↥E ∧ B = U ⊔ E :=
  isS_sup_iff_add_two h hP 2 B

theorem isElementaryAbelian_bot' : CFSG.IsElementaryAbelian 2 ↥(⊥ : Subgroup G) :=
  C3.Layer1.Back.isElementaryAbelian_of_forall
    (fun u hu v hv => by simp [Subgroup.mem_bot.1 hu, Subgroup.mem_bot.1 hv])
    (fun u hu => by simp [Subgroup.mem_bot.1 hu])

theorem isKBal_cj [Finite G] {k : ℕ} {A : Subgroup G} (g : G) (h : IsKBal k A) :
    IsKBal k (cj g A) := by
  intro D hD a ha ha1
  have hD' : IsE k A (cj g⁻¹ D) := by
    have := isE_cj hD g⁻¹
    rwa [cj_cj_inv] at this
  have ha' : g⁻¹ * a * g ∈ A := (mem_cj_iff g A a).1 ha
  have ha1' : g⁻¹ * a * g ≠ 1 := by
    intro h1
    apply ha1
    calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hb := h (cj g⁻¹ D) hD' (g⁻¹ * a * g) ha' ha1'
  have hb' := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hb
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective] at hb'
  have hAG : (AG (cj g⁻¹ D)).map (MulAut.conj g).toMonoidHom = AG D := by
    change cj g (AG (cj g⁻¹ D)) = AG D
    calc cj g (AG (cj g⁻¹ D)) = AG (cj g (cj g⁻¹ D)) := (AG_cj g _).symm
      _ = AG D := by rw [cj_inv_cj]
  have hC : (centralizer ({g⁻¹ * a * g} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({a} : Set G) := by
    change cj g (centralizer ({g⁻¹ * a * g} : Set G)) = centralizer ({a} : Set G)
    have := cj_centralizer_singleton g (g⁻¹ * a * g)
    simpa [show g * (g⁻¹ * a * g) * g⁻¹ = a by group] using this
  have hPC : (pPrimeCoreOf 2 (centralizer ({g⁻¹ * a * g} : Set G))).map
      (MulAut.conj g).toMonoidHom = pPrimeCoreOf 2 (centralizer ({a} : Set G)) := by
    change cj g (pPrimeCoreOf 2 (centralizer ({g⁻¹ * a * g} : Set G))) =
      pPrimeCoreOf 2 (centralizer ({a} : Set G))
    have hC' : cj g (centralizer ({g⁻¹ * a * g} : Set G)) = centralizer ({a} : Set G) := by
      simpa [Th2.cj] using hC
    rw [← pPrimeCoreOf_cj, hC']
  rw [hAG, hC, hPC] at hb'
  exact hb'

end CFSG.GH74.GLS.Th2

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

section Rows

variable {G : Type} [Group G] {x y : G} {K T S : Subgroup G}

theorem exists_isFourSub_of_rankTwoShape {P : Subgroup G} (hP : RankTwoShape P) :
    ∃ U : Subgroup G, IsFourSub P U := by
  obtain ⟨U, -, hU⟩ := hP.2.1 ⊥ bot_le isElementaryAbelian_bot'
  exact ⟨U, hU⟩

theorem false_of_three_le_rank_Q [Finite G] (hG : C3Hyp G) (h : Th2Std x y K T S)
    (hcen : CenterlessBar K) (hP : RankTwoShape (T ⊓ K))
    (h3 : 3 ≤ pRank 2 ↥(T ⊓ CxK x K)) : False := by
  have hPQ := h.commDisj hcen
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  obtain ⟨E, hEQ, hEel, hErk⟩ := exists_elemAbelian_pRank (T ⊓ CxK x K)
  have hsup := hPQ.pRank_sup hU.2.1 hEel hU.1 hEQ
  have h4 := pRank_le_top' (U ⊔ E)
  have h5 := hG.pRank_eq_four
  have h6 := pRank_of_isFourSub hU
  omega

theorem Th2Std.exists_isS_Q [Finite G] (h : Th2Std x y K T S)
    (hnot : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    ∃ E : Subgroup G, IsS (T ⊓ CxK x K) E ∧ 2 ≤ pRank 2 ↥E := by
  have h2 : 2 ≤ pRank 2 ↥(CxK x K) := by
    rcases h.v2ss.isV2Triple.2.2.1 with h1 | h1
    · exact h1
    · exact absurd h1.2.1 hnot
  obtain ⟨F, hFC, hFel, hFrk⟩ := exists_elemAbelian_pRank (CxK x K)
  obtain ⟨g, -, hgF⟩ := Th2.exists_cj_le_of_isSylowOf h.sylow_Q hFC
    (CFSG.IsElementaryAbelian.isPGroup 2 _)
  have hWel := isElementaryAbelian_cj g hFel
  obtain ⟨E, hWE, hE⟩ := exists_maximal_elemAbelian hgF hWel
  refine ⟨E, hE, ?_⟩
  have := C3.Layer1.Back.pRank_mono' hWE
  rw [pRank_cj, hFrk] at this
  omega

theorem conn_L2 [Finite G] (h : Th2Std x y K T S) {Pr : ℕ → Prop} (hPr : ∀ q, Pr q → Odd q)
    (hL2 : HasL2Model (kBar K) Pr)
    {B : Subgroup G} (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) {A : Subgroup G}
    (hA : IsE 3 (⨆ B' ∈ {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B''}, B') A) :
    RConnN 3 4 (⨆ B' ∈ {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B''}, B') A B := by
  have hcen := centerlessBar_of_hasL2Model hPr hL2
  have hPQ := h.commDisj hcen
  have hP := rankTwoShape_sylow_L2 h.sylow_P (TwoThin.isQuasisimple_hat h.comp) hPr hL2
  have hQ : IsPGroup 2 ↥(T ⊓ CxK x K) := h.T_pGroup.to_le inf_le_left
  refine conn_core hPQ hP hQ {U | IsFourSub (T ⊓ K) U} (fun U hU => hU)
    (BT := {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B''})
    (fun B' => isS_sup_iff hPQ hP B') ?_ hB hA
  intro A' _ hA'el
  obtain ⟨U, hAU, hU⟩ := hP.2.1 (hPQ.projP A') (hPQ.projP_le_left A')
    (hPQ.isElementaryAbelian_projP hA'el)
  exact ⟨U, hU, hAU⟩

theorem conn_A7_3c [Finite G] (h : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    {B : Subgroup G}
    (hB : B ∈ {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'' ∧
      ∃ D, IsDSub K (T ⊓ K) D ∧ D ≤ B''}) {A : Subgroup G}
    (hA : IsE 3 (⨆ B' ∈ {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'' ∧
      ∃ D, IsDSub K (T ⊓ K) D ∧ D ≤ B''}, B') A) :
    RConnN 3 4 (⨆ B' ∈ {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'' ∧
      ∃ D, IsDSub K (T ⊓ K) D ∧ D ≤ B''}, B') A B := by
  have hcen := centerlessBar_of_A7 h7
  have hPQ := h.commDisj hcen
  have hP := rankTwoShape_sylow_A7 h.sylow_P h7
  have hQ : IsPGroup 2 ↥(T ⊓ CxK x K) := h.T_pGroup.to_le inf_le_left
  have hDfour : ∀ D, IsDSub K (T ⊓ K) D → IsFourSub (T ⊓ K) D :=
    fun D hD => ⟨hD.1, hD.2.2.1, hD.2.2.2.1⟩
  have hBT : ∀ B' : Subgroup G, B' ∈ {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'' ∧
      ∃ D, IsDSub K (T ⊓ K) D ∧ D ≤ B''} ↔ ∃ D ∈ {D | IsDSub K (T ⊓ K) D}, ∃ E : Subgroup G,
        IsS (T ⊓ CxK x K) E ∧ 2 ≤ pRank 2 ↥E ∧ B' = D ⊔ E := by
    intro B'
    constructor
    · rintro ⟨hSn, D, hD, hDB⟩
      obtain ⟨U, hU, E, hE, hrk, rfl⟩ := (isS_sup_iff hPQ hP B').1 hSn
      have hDU : D ≤ U := by
        intro d hd
        obtain ⟨u, hu, e, he, hde⟩ := exists_mul_of_mem_sup_of_commute
          (fun k hk l hl => hPQ.comm k (hU.1 hk) l (hE.1 hl)) (hDB hd)
        have h1 := hPQ.mul_cancel (hD.1 hd) (hU.1 hu) (one_mem _) (hE.1 he)
          (by rw [mul_one]; exact hde)
        rwa [h1.1]
      have hDeq : D = U := by
        refine le_antisymm hDU ?_
        exact (Subgroup.eq_of_le_of_card_ge hDU (by rw [hU.2.2, hD.2.2.2.1])).ge
      subst hDeq
      exact ⟨D, hD, E, hE, hrk, rfl⟩
    · rintro ⟨D, hD, E, hE, hrk, rfl⟩
      exact ⟨(isS_sup_iff hPQ hP _).2 ⟨D, hDfour D hD, E, hE, hrk, rfl⟩, D, hD, le_sup_left⟩
  obtain ⟨D₀, hD₀, E₀, hE₀, hE₀rk, hBeq⟩ := (hBT B).1 hB
  have hXle : (⨆ B' ∈ {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'' ∧
      ∃ D, IsDSub K (T ⊓ K) D ∧ D ≤ B''}, B') ≤ D₀ ⊔ (T ⊓ CxK x K) := by
    refine iSup₂_le fun B' hB' => ?_
    obtain ⟨D', hD', E', hE', -, rfl⟩ := (hBT B').1 hB'
    have : D' = D₀ := isDSub_unique h.sylow_P hD' hD₀
    rw [this]
    exact sup_le_sup le_rfl hE'.1
  refine conn_core hPQ hP hQ {D | IsDSub K (T ⊓ K) D} hDfour hBT ?_ hB hA
  intro A' hA'X _
  refine ⟨D₀, hD₀, ?_⟩
  intro p hp
  have hp' := (hPQ.mem_projP_iff).1 hp
  obtain ⟨hpP, q, hq, hpq⟩ := hp'
  obtain ⟨d, hd, q', hq', e⟩ := exists_mul_of_mem_sup_of_commute
    (fun k hk l hl => hPQ.comm k (hD₀.1 hk) l hl) (hXle (hA'X hpq))
  have h1 := hPQ.mul_cancel hpP (hD₀.1 hd) hq hq' e
  rw [h1.1]; exact hd

theorem row3a_BT_eq_fam [Finite G] {x y : G} {K T S : Subgroup G}
    (h : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    {D0 : Subgroup G} (hD0 : IsDSub K (T ⊓ K) D0) :
    Th2Row.BT .r3a x K T S =
      {B : Subgroup G | ∃ E : Subgroup G, IsS (T ⊓ CxK x K) E ∧
        3 ≤ CFSG.pRank 2 ↥E ∧ B = D0 ⊔ E} := by
  have hcen := centerlessBar_of_A7 h7
  have hPQ := h.commDisj hcen
  have hP := rankTwoShape_sylow_A7 h.sylow_P h7
  ext B
  constructor
  · rintro ⟨hSn, D, hD, hDB⟩
    obtain ⟨U, hU, E, hE, hrk, rfl⟩ :=
      (isS_sup_iff_add_two hPQ hP 3 B).1 hSn
    have hDU : D ≤ U := by
      intro d hd
      obtain ⟨u, hu, e, he, hde⟩ := exists_mul_of_mem_sup_of_commute
        (fun k hk l hl => hPQ.comm k (hU.1 hk) l (hE.1 hl)) (hDB hd)
      have h1 := hPQ.mul_cancel (hD.1 hd) (hU.1 hu) (one_mem _) (hE.1 he)
        (by rw [mul_one]; exact hde)
      rwa [h1.1]
    have hDeq : D = U := by
      refine le_antisymm hDU ?_
      exact (Subgroup.eq_of_le_of_card_ge hDU (by rw [hU.2.2, hD.2.2.2.1])).ge
    have hD0eq : U = D0 := by
      rw [← hDeq]
      exact isDSub_unique h.sylow_P hD hD0
    refine ⟨E, hE, hrk, ?_⟩
    rw [hD0eq]
  · rintro ⟨E, hE, hrk, rfl⟩
    have hD0four : IsFourSub (T ⊓ K) D0 := ⟨hD0.1, hD0.2.2.1, hD0.2.2.2.1⟩
    refine ⟨(isS_sup_iff_add_two hPQ hP 3 (D0 ⊔ E)).2
      ⟨D0, hD0four, E, hE, hrk, rfl⟩, D0, hD0, le_sup_left⟩

theorem conn_row3a [Finite G] {x y : G} {K T S : Subgroup G} (h : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hconn : IsConn2 (T ⊓ CxK x K))
    (h3 : 3 ≤ CFSG.pRank 2 ↥(T ⊓ CxK x K))
    {B : Subgroup G} (hB : B ∈ Th2Row.BT .r3a x K T S)
    {A : Subgroup G} (hA : IsE 4 (Th2Row.Tstar .r3a x K T S) A) :
    RConnN 4 5 (Th2Row.Tstar .r3a x K T S) A B := by
  have hBmem : B ∈ Th2Row.BT .r3a x K T S := hB
  obtain ⟨-, D0, hD0, -⟩ := hB
  have hcen := centerlessBar_of_A7 h7
  have hPQ := h.commDisj hcen
  have hP := rankTwoShape_sylow_A7 h.sylow_P h7
  have hQp : IsPGroup 2 ↥(T ⊓ CxK x K) := h.T_pGroup.to_le inf_le_left
  have hDfour : ∀ D : Subgroup G, IsDSub K (T ⊓ K) D → IsFourSub (T ⊓ K) D :=
    fun D hD => ⟨hD.1, hD.2.2.1, hD.2.2.2.1⟩
  have hBTeq : ∀ B' : Subgroup G,
      B' ∈ Th2Row.BT .r3a x K T S ↔
        ∃ E : Subgroup G, IsS (T ⊓ CxK x K) E ∧
          3 ≤ CFSG.pRank 2 ↥E ∧ B' = D0 ⊔ E := by
    intro B'
    rw [row3a_BT_eq_fam h h7 hD0]
    rfl
  have hBTset : Th2Row.BT .r3a x K T S =
      {B' : Subgroup G | ∃ E : Subgroup G, IsS (T ⊓ CxK x K) E ∧
        3 ≤ CFSG.pRank 2 ↥E ∧ B' = D0 ⊔ E} := by
    ext B'
    exact hBTeq B'
  have hXeq : Th2Row.Tstar .r3a x K T S =
      ⨆ B' ∈ {B' : Subgroup G | ∃ E : Subgroup G, IsS (T ⊓ CxK x K) E ∧
        3 ≤ CFSG.pRank 2 ↥E ∧ B' = D0 ⊔ E}, B' := by
    unfold Th2Row.Tstar
    rw [hBTset]
  have hBfam : B ∈ {B' : Subgroup G | ∃ E : Subgroup G,
      IsS (T ⊓ CxK x K) E ∧ 3 ≤ CFSG.pRank 2 ↥E ∧ B' = D0 ⊔ E} :=
    (hBTeq B).1 hBmem
  have hAfam : IsE 4 (⨆ B' ∈ {B' : Subgroup G | ∃ E : Subgroup G,
      IsS (T ⊓ CxK x K) E ∧ 3 ≤ CFSG.pRank 2 ↥E ∧ B' = D0 ⊔ E}, B') A := by
    rwa [← hXeq]
  have hD0fourTop : IsFourSub ⊤ D0 :=
    ⟨le_top, (hDfour D0 hD0).2.1, (hDfour D0 hD0).2.2⟩
  have hD0Q : CommDisj D0 (T ⊓ CxK x K) := by
    refine ⟨fun d hd q hq => hPQ.comm d ((hDfour D0 hD0).1 hd) q hq, ?_⟩
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ (T ⊓ K) ⊓ (T ⊓ CxK x K) :=
      ⟨(hDfour D0 hD0).1 hz.1, hz.2⟩
    rw [hPQ.inf] at hz'
    exact hz'
  have hres := conn_fixed_four (D := D0) (Q := T ⊓ CxK x K) hD0Q hD0fourTop hQp hconn h3
    (B := B) hBfam (A := A) hAfam
  rwa [← hXeq] at hres

theorem row3a_BT_eq [Finite G] {x y : G} {K T S : Subgroup G}
    (h : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hconn : IsConn2 (T ⊓ CxK x K))
    (h3 : 3 ≤ CFSG.pRank 2 ↥(T ⊓ CxK x K)) :
    Th2Row.BT .r3a x K T S =
      {B : Subgroup G | IsSn 5 (Th2Row.Tstar .r3a x K T S) B} := by
  let P : Subgroup G := T ⊓ K
  let Q : Subgroup G := T ⊓ CxK x K
  have hQp : IsPGroup 2 ↥Q := h.T_pGroup.to_le inf_le_left
  have hcen := centerlessBar_of_A7 h7
  have hPQ : CommDisj P Q := h.commDisj hcen
  have hP : RankTwoShape P := rankTwoShape_sylow_A7 h.sylow_P h7
  obtain ⟨D0, hD0⟩ := exists_isDSub h.sylow_P h7
  have hD0el : CFSG.IsElementaryAbelian 2 ↥D0 := hD0.2.2.1
  have hD0card : Nat.card ↥D0 = 4 := hD0.2.2.2.1
  have hD0fourP : IsFourSub P D0 := ⟨hD0.1, hD0el, hD0card⟩
  let Fam : Set (Subgroup G) :=
    {B : Subgroup G | ∃ E : Subgroup G, IsS Q E ∧
      3 ≤ CFSG.pRank 2 ↥E ∧ B = D0 ⊔ E}
  have hBTFam : Th2Row.BT .r3a x K T S = Fam := by
    simpa [Fam, P, Q] using row3a_BT_eq_fam h h7 hD0
  set X : Subgroup G := Th2Row.Tstar .r3a x K T S with hXdef
  have hFamX : ∀ B' ∈ Fam, B' ≤ X := by
    intro B' hB'
    have hB'BT : B' ∈ Th2Row.BT .r3a x K T S := by rwa [hBTFam]
    rw [hXdef, Th2Row.Tstar]
    exact le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ Th2Row.BT .r3a x K T S) => B) B' hB'BT
  have hX_le : X ≤ P ⊔ Q := by
    rw [hXdef, Th2Row.Tstar]
    refine iSup₂_le fun B' hB' => ?_
    have hB'Fam : B' ∈ Fam := hBTFam ▸ hB'
    obtain ⟨E, hE, hErk, rfl⟩ := hB'Fam
    exact sup_le (hD0.1.trans le_sup_left) (hE.1.trans le_sup_right)
  have hD0X : D0 ≤ X := by
    obtain ⟨W, hWQ, hWel, -⟩ := exists_elemAbelian_pRank Q
    obtain ⟨E0, hWE0, hE0S⟩ := exists_maximal_elemAbelian hWQ hWel
    have hE0rk : 3 ≤ CFSG.pRank 2 ↥E0 :=
      isS_pRank_three_of_isConn2 hQp hconn h3 hE0S
    have hE0Fam : D0 ⊔ E0 ∈ Fam := ⟨E0, hE0S, hE0rk, rfl⟩
    exact (le_sup_left : D0 ≤ D0 ⊔ E0).trans (hFamX _ hE0Fam)
  have hFamCent : ∀ B' ∈ Fam, B' ≤ centralizer (D0 : Set G) := by
    intro B' hB'
    obtain ⟨E, hE, hErk, rfl⟩ := hB'
    refine sup_le ?_ ?_
    · intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro d' hd'
      exact ((C3.Layer1.Back.forall_of_isElementaryAbelian hD0el).1 d hd d' hd').symm
    · intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact hPQ.comm d (hD0.1 hd) e (hE.1 he)
  have hD0centralX : ∀ d ∈ D0, ∀ x ∈ X, d * x = x * d := by
    intro d hd x hx
    have hXcent : X ≤ centralizer (D0 : Set G) := by
      rw [hXdef, Th2Row.Tstar]
      refine iSup₂_le fun B' hB' => ?_
      exact hFamCent B' (hBTFam ▸ hB')
    exact Subgroup.mem_centralizer_iff.1 (hXcent hx) d hd
  have hFamEl : ∀ B' ∈ Fam, CFSG.IsElementaryAbelian 2 ↥B' := by
    intro B' hB'
    obtain ⟨E, hE, hErk, rfl⟩ := hB'
    exact hPQ.isElementaryAbelian_sup' hD0el hE.2.1 hD0.1 hE.1
  have hFamRank : ∀ B' ∈ Fam, 5 ≤ CFSG.pRank 2 ↥B' := by
    intro B' hB'
    obtain ⟨E, hE, hErk, rfl⟩ := hB'
    have hrank := hPQ.pRank_sup hD0el hE.2.1 hD0.1 hE.1
    rw [hrank, pRank_of_isFourSub hD0fourP]
    omega
  have hFamMax : ∀ B' ∈ Fam, ∀ A : Subgroup G,
      CFSG.IsElementaryAbelian 2 ↥A → A ≤ X → B' ≤ A → A = B' := by
    intro B' hB' A hAel hAX hBA
    obtain ⟨E, hE, hErk, rfl⟩ := hB'
    have hAPQ : A ≤ P ⊔ Q := hAX.trans hX_le
    obtain ⟨C, hAC, hCS⟩ := exists_maximal_elemAbelian hAPQ hAel
    obtain ⟨hCeq, hPS, hQS⟩ := hPQ.isS_proj hCS
    have hD0projP : D0 ≤ hPQ.projP C := by
      intro d hd
      exact hPQ.mem_projP (hD0.1 hd) Q.one_mem
        (by simpa using hAC (hBA (Subgroup.mem_sup_left hd)))
    have hprojPcard : Nat.card ↥(hPQ.projP C) ≤ 4 :=
      hP.1 _ (hPQ.projP_le_left C) hPS.2.1
    have hD0eqProjP : D0 = hPQ.projP C :=
      Subgroup.eq_of_le_of_card_ge hD0projP (by rw [hD0card]; exact hprojPcard)
    have hEprojQ : E ≤ hPQ.projQ C := by
      intro e he
      exact hPQ.mem_projQ P.one_mem (hE.1 he)
        (by simpa using hAC (hBA (Subgroup.mem_sup_right he)))
    have hprojQeq : hPQ.projQ C = E :=
      eq_of_isS_of_le_elem hE (hPQ.projQ_le_right C) hQS.2.1 hEprojQ
    have hCeq : C = D0 ⊔ E := by
      rw [hCeq, ← hD0eqProjP, hprojQeq]
    exact le_antisymm (hCeq ▸ hAC) hBA
  have hFamIsS : ∀ B' ∈ Fam, IsS X B' := by
    intro B' hB'
    have hB'el := hFamEl B' hB'
    have hB'X := hFamX B' hB'
    have hB'max := hFamMax B' hB'
    refine ⟨hB'X, hB'el, le_antisymm ?_ ?_⟩
    · refine le_omega1_of_isElementaryAbelian hB'el (le_inf hB'X ?_)
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      exact ((C3.Layer1.Back.forall_of_isElementaryAbelian hB'el).1 b hb b' hb').symm
    · refine (Subgroup.closure_le B').2 ?_
      rintro u ⟨⟨huX, huC⟩, hu2⟩
      have hzu : CFSG.IsElementaryAbelian 2 ↥(zpowers u) :=
        CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by simpa [pow_two] using hu2)
      have hsupel : CFSG.IsElementaryAbelian 2 ↥(B' ⊔ zpowers u) := by
        refine isElementaryAbelian_sup hB'el hzu ?_
        intro b hb z hz
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hz
        exact (Commute.zpow_right (huC b hb) m).eq
      have hsupX : B' ⊔ zpowers u ≤ X := sup_le hB'X (zpowers_le.2 huX)
      have hsupeq : B' ⊔ zpowers u = B' := hB'max _ hsupel hsupX le_sup_left
      exact hsupeq.symm ▸ Subgroup.mem_sup_right (mem_zpowers u)
  ext B
  constructor
  · intro hB
    have hBFam : B ∈ Fam := hBTFam ▸ hB
    exact ⟨hFamIsS B hBFam, hFamRank B hBFam⟩
  · rintro ⟨hBS, hBrk⟩
    have hBX := hBS.1
    have hBel := hBS.2.1
    have hBmax : ∀ A : Subgroup G, CFSG.IsElementaryAbelian 2 ↥A →
        A ≤ X → B ≤ A → A = B := by
      intro A hAel hAX hBA
      have homega : A ≤ omega1 (X ⊓ centralizer (B : Set G)) := by
        refine le_omega1_of_isElementaryAbelian hAel (le_inf hAX ?_)
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact ((C3.Layer1.Back.forall_of_isElementaryAbelian hAel).1 a ha b (hBA hb)).symm
      rw [← hBS.2.2] at homega
      exact le_antisymm homega hBA
    have hD0B : D0 ≤ B := by
      have hsupel : CFSG.IsElementaryAbelian 2 ↥(B ⊔ D0) := by
        refine isElementaryAbelian_sup hBel hD0el ?_
        intro b hb d hd
        exact (hD0centralX d hd b (hBX hb)).symm
      have hsupX : B ⊔ D0 ≤ X := sup_le hBX hD0X
      have hsupeq : B ⊔ D0 = B := hBmax _ hsupel hsupX le_sup_left
      exact hsupeq.symm ▸ le_sup_right
    have hprojP_eq : hPQ.projP B = D0 := by
      have hD0projP : D0 ≤ hPQ.projP B := by
        intro d hd
        exact hPQ.mem_projP (hD0.1 hd) Q.one_mem (by simpa using hD0B hd)
      have hprojPcard : Nat.card ↥(hPQ.projP B) ≤ 4 :=
        hP.1 _ (hPQ.projP_le_left B) (hPQ.isElementaryAbelian_projP hBel)
      have hD0eq : D0 = hPQ.projP B :=
        Subgroup.eq_of_le_of_card_ge hD0projP (by rw [hD0card]; exact hprojPcard)
      exact hD0eq.symm
    have hprojQel : CFSG.IsElementaryAbelian 2 ↥(hPQ.projQ B) :=
      hPQ.isElementaryAbelian_projQ hBel
    obtain ⟨E', hprojQleE', hE'S⟩ :=
      exists_maximal_elemAbelian (hPQ.projQ_le_right B) hprojQel
    have hE'rk : 3 ≤ CFSG.pRank 2 ↥E' :=
      isS_pRank_three_of_isConn2 hQp hconn h3 hE'S
    have hDE'Fam : D0 ⊔ E' ∈ Fam := ⟨E', hE'S, hE'rk, rfl⟩
    have hDE'X : D0 ⊔ E' ≤ X := hFamX _ hDE'Fam
    have hDE'el : CFSG.IsElementaryAbelian 2 ↥(D0 ⊔ E') :=
      hPQ.isElementaryAbelian_sup' hD0el hE'S.2.1 hD0.1 hE'S.1
    have hBle : B ≤ D0 ⊔ E' := by
      calc B ≤ hPQ.projP B ⊔ hPQ.projQ B :=
            hPQ.le_projP_sup_projQ (hBX.trans hX_le)
        _ ≤ D0 ⊔ E' := sup_le_sup hprojP_eq.le hprojQleE'
    have hDE'eq : D0 ⊔ E' = B := hBmax _ hDE'el hDE'X hBle
    rw [hBTFam]
    exact ⟨E', hE'S, hE'rk, hDE'eq.symm⟩

theorem row3a_theta_eq_of_BT [Finite G] {x y : G} {K T S M B B₁ : Subgroup G}
    (h2110 : B_IG_21_10) (h2 : Th2M2 x y K T S M .r3a B)
    (hB₁ : B₁ ∈ Th2Row.BT .r3a x K T S) :
    (Th2Level.three).theta B₁ = (Th2Level.three).theta B := by
  have hstd := h2.std
  have h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := h2.row.1
  have hconn : IsConn2 (T ⊓ CxK x K) := h2.row.2.1
  have h3 : 3 ≤ CFSG.pRank 2 ↥(T ⊓ CxK x K) := h2.row.2.2
  have h74 := row3a_BT_eq hstd h7 hconn h3
  have hS : ∀ B' : Subgroup G, IsSn 5 (Th2Row.Tstar .r3a x K T S) B' →
      IsE 5 ⊤ B' ∧ (Th2Level.three).IsBal B' := by
    intro B' hB'
    have hmem : B' ∈ Th2Row.BT .r3a x K T S := by
      rw [h74]
      exact hB'
    exact ⟨⟨le_top, (h2.allIsE B' hmem).2.1, (h2.allIsE B' hmem).2.2⟩,
      h2.allBal B' hmem⟩
  have hB₁T : B₁ ≤ Th2Row.Tstar .r3a x K T S :=
    le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ Th2Row.BT .r3a x K T S) => B) B₁ hB₁
  have hB₁5 : IsE 5 (Th2Row.Tstar .r3a x K T S) B₁ :=
    ⟨hB₁T, (h2.allIsE B₁ hB₁).2.1, (h2.allIsE B₁ hB₁).2.2⟩
  have hB₁4 : IsE 4 (Th2Row.Tstar .r3a x K T S) B₁ :=
    isE_mono_rank hB₁5 (by norm_num)
  have hchain : RConnN 4 5 (Th2Row.Tstar .r3a x K T S) B₁ B :=
    conn_row3a hstd h7 hconn h3 h2.mem hB₁4
  exact theta_eq_of_conn Th2Level.three b_ig_21_8 h2110 hS hB₁4 hchain

theorem row3a_gamma [Finite G] {x y : G} {K T S M B : Subgroup G}
    (h2110 : B_IG_21_10) (h2 : Th2M2 x y K T S M .r3a B) :
    gammaK 2 B 4 ≤ M ∧ gammaK 2 (Th2Row.Tstar .r3a x K T S) 4 ≤ M := by
  have h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := h2.row.1
  have hconn : IsConn2 (T ⊓ CxK x K) := h2.row.2.1
  have h3 : 3 ≤ CFSG.pRank 2 ↥(T ⊓ CxK x K) := h2.row.2.2
  have h74 := row3a_BT_eq h2.std h7 hconn h3
  have hconn_local :
      (Th2Row.r3a ≠ .r4b → Th2Row.r3a ≠ .r4c →
        ∀ A : Subgroup G, IsE (Th2Row.r3a.level.r) (Th2Row.Tstar .r3a x K T S) A →
          RConnN (Th2Row.r3a.level.r) (Th2Row.r3a.level.n)
            (Th2Row.Tstar .r3a x K T S) A B) ∧
      (∀ A : Subgroup G, IsE (Th2Row.r3a.level.n) (Th2Row.Tstar .r3a x K T S) A →
        RConnN (Th2Row.r3a.level.r) (Th2Row.r3a.level.n)
          (Th2Row.Tstar .r3a x K T S) A B) := by
    constructor
    · intro _ _ A hA
      exact conn_row3a h2.std h7 hconn h3 h2.mem hA
    · intro A hA
      exact conn_row3a h2.std h7 hconn h3 h2.mem
        (isE_mono_rank hA (by norm_num : 4 ≤ 5))
  have hloc := b_thm2_l82_local h2110 h2 h74 hconn_local
  refine ⟨?_, ?_⟩
  · change gammaK 2 B (Th2Row.r3a.level.r) ≤ M
    exact hloc.2.2.2
  · change gammaK 2 (Th2Row.Tstar .r3a x K T S) (Th2Row.r3a.level.r) ≤ M
    exact hloc.1 (by decide) (by decide)

theorem conn_A7_3b [Finite G] (hG : C3Hyp G) (h3b : B_thm2_A7_3b) (h : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) (hTS : T < S) {B : Subgroup G}
    (hB : B ∈ {B'' : Subgroup G | ∃ D, IsDSub K (T ⊓ K) D ∧
      B'' = ⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom}) {A : Subgroup G}
    (hA : IsE 3 (⨆ B' ∈ {B'' : Subgroup G | ∃ D, IsDSub K (T ⊓ K) D ∧
      B'' = ⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom}, B') A) :
    RConnN 3 4 (⨆ B' ∈ {B'' : Subgroup G | ∃ D, IsDSub K (T ⊓ K) D ∧
      B'' = ⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom}, B') A B := by
  set BT : Set (Subgroup G) := {B'' : Subgroup G | ∃ D, IsDSub K (T ⊓ K) D ∧
    B'' = ⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom} with hBT
  have hB' := hB
  obtain ⟨D₀, hD₀, hBeq⟩ := hB'
  have hBTeq : ∀ B' ∈ BT, B' = B := by
    rintro B' ⟨D', hD', rfl⟩
    have := isDSub_unique h.sylow_P hD' hD₀
    rw [this]; exact hBeq.symm
  have hX : (⨆ B' ∈ BT, B') = B := by
    apply le_antisymm
    · exact iSup₂_le fun B' hB' => (hBTeq B' hB').le
    · exact le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ BT) => B) B hB
  obtain ⟨hel, hrk⟩ := h3b G hG x y K T S h h7 hQ4 hTS D₀ hD₀
  rw [← hBeq] at hel hrk
  rw [hX] at hA ⊢
  obtain ⟨hAB, -, -⟩ := hA
  exact Relation.ReflTransGen.single
    (connStep_of_le_elem ⟨le_rfl, hel, hrk⟩ hAB le_rfl ⟨le_rfl, hel, by omega⟩)

theorem conn_L2_five [Finite G] (hG : C3Hyp G)
    (h : Th2Std x y K T S)
    (hL2 : HasL2Model (kBar K) (fun q => q = 5)) {B : Subgroup G} (hB : IsSn 4 T B)
    {A : Subgroup G} (hA : IsE 4 (⨆ B' ∈ {B'' : Subgroup G | IsSn 4 T B''}, B') A) :
    RConnN 3 4 (⨆ B' ∈ {B'' : Subgroup G | IsSn 4 T B''}, B') A B := by
  have hPr : ∀ q : ℕ, q = 5 → Odd q := by rintro q rfl; decide
  have hcen := centerlessBar_of_hasL2Model hPr hL2
  have hPQ := h.commDisj hcen
  have hP := rankTwoShape_sylow_L2 h.sylow_P (TwoThin.isQuasisimple_hat h.comp) hPr hL2
  have hP4 := card_sylow_L2_five h.sylow_P hL2
  have hQ : IsPGroup 2 ↥(T ⊓ CxK x K) := h.T_pGroup.to_le inf_le_left
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  have hUP : U = T ⊓ K := Subgroup.eq_of_le_of_card_ge hU.1 (by rw [hU.2.2, hP4])
  have hPel : CFSG.IsElementaryAbelian 2 ↥(T ⊓ K) := hUP ▸ hU.2.1
  have hrk : 2 ≤ pRank 2 ↥(T ⊓ K) := by
    rw [← hUP, pRank_of_isFourSub hU]
  have hKN := h.K_normal (by rw [hG.pRank_eq_four]) hcen hrk
  obtain ⟨e5⟩ := C3.Layer1.Back.nonempty_alt5_of_hasL2Model5 hL2
  have hTle := h.card_T_le_of_A5 hKN e5
  have hRcard : Nat.card ↥((T ⊓ K) ⊔ (T ⊓ CxK x K)) = 4 * Nat.card ↥(T ⊓ CxK x K) := by
    rw [hPQ.card_sup le_rfl le_rfl, hP4]
  have hRT : (T ⊓ K) ⊔ (T ⊓ CxK x K) ≤ T := sup_le inf_le_left inf_le_left
  have hidx : ∀ A' : Subgroup G, A' ≤ T →
      Nat.card ↥A' ≤ 2 * Nat.card ↥(((T ⊓ K) ⊔ (T ⊓ CxK x K)) ⊓ A') := fun A' hA' =>
    card_le_two_mul_inf hRT (by omega) hA'
  have hnot7 : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := by
    rintro ⟨e7⟩
    have h1 := Nat.card_congr (e7.symm.trans e5).toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at h1
    simp [Nat.factorial] at h1
  obtain ⟨E₀, hE₀, hE₀rk⟩ := h.exists_isS_Q hnot7
  exact conn_core_T hPQ hPel hP4 hQ hRT hidx hE₀ hE₀rk hB hA

end Rows

end CFSG.GH74.GLS
