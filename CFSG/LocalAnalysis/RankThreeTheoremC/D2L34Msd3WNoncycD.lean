module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WNoncycC
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3GroupStepFree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFConstrained

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]

@[expose] def Center3Conclusion (M : Subgroup G) : Prop :=
  ∃ W : Subgroup G, W ≤ M ∧ IsPGroup 3 W ∧ ¬ 3 ∣ (W.subgroupOf M).index ∧
    ∃ E : Subgroup G, E ≤ W ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ w ∈ W, w ^ 3 = 1 → ∀ e ∈ E, w * e = e * w

omit [Finite G] in
theorem Center3Conclusion.of_central {M W E : Subgroup G} (hWM : W ≤ M) (hWp : IsPGroup 3 W)
    (hWidx : ¬ 3 ∣ (W.subgroupOf M).index) (hEW : E ≤ W) (hEel : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hEC : ∀ w ∈ W, ∀ e ∈ E, w * e = e * w) : Center3Conclusion M :=
  ⟨W, hWM, hWp, hWidx, E, hEW, hEel, hE9, fun w hw _ e he => hEC w hw e he⟩

section Ctx

variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2L34SideCtx3.exists_center3_of_center3Conclusion
    (h : D2L34SideCtx3 G d P M A H R Rbar K) (hc : Center3Conclusion M) :
    ∃ E : Subgroup G, E ≤ (P : Subgroup G) ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ x ∈ (P : Subgroup G), x ^ 3 = 1 → ∀ e ∈ E, x * e = e * x := by
  obtain ⟨W, hWM, hWp, hWidx, E, hEW, hEel, hE9, hEC⟩ := hc
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal h.setting h.sigma h.core
  have hPidx : ¬ 3 ∣ ((P : Subgroup G).subgroupOf M).index := fun hd =>
    P.not_dvd_index (hd.trans (Subgroup.relIndex_dvd_index_of_le hPM))
  obtain ⟨g, hgM, hgP⟩ := exists_conj_map_le_of_isPGroup hPM P.isPGroup' hPidx hWM hWp
  obtain ⟨g', hg'M, hg'W⟩ := exists_conj_map_le_of_isPGroup hWM hWp hWidx hPM P.isPGroup'
  have hcard1 : Nat.card (W.map (MulAut.conj g).toMonoidHom) = Nat.card W :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcard2 : Nat.card ((P : Subgroup G).map (MulAut.conj g').toMonoidHom) =
      Nat.card (P : Subgroup G) := Subgroup.card_map_of_injective (MulAut.conj g').injective
  have hle1 := Subgroup.card_le_of_le hgP
  have hle2 := Subgroup.card_le_of_le hg'W
  have hPeq : W.map (MulAut.conj g).toMonoidHom = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hgP (by omega)
  refine ⟨E.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_mono hEW).trans hgP
  · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hEel _
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE9]
  · intro x hxP hx3 e he
    obtain ⟨e₀, he₀, rfl⟩ := he
    have hxW : g⁻¹ * x * g ∈ W := by
      rw [← hPeq] at hxP
      obtain ⟨w, hw, hwx⟩ := hxP
      have : g⁻¹ * x * g = w := by
        rw [← hwx]
        simp [MulAut.conj_apply]
        group
      rw [this]
      exact hw
    have hx3' : (g⁻¹ * x * g) ^ 3 = 1 := by
      have h3 : x * x * x = 1 := by rw [← pow_three']; exact hx3
      calc (g⁻¹ * x * g) ^ 3 = g⁻¹ * (x * x * x) * g := by
            rw [pow_succ, pow_succ, pow_one]
            group
        _ = 1 := by rw [h3]; group
    have hcomm := hEC _ hxW hx3' e₀ he₀
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc x * (g * e₀ * g⁻¹) = g * ((g⁻¹ * x * g) * e₀) * g⁻¹ := by group
      _ = g * (e₀ * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm]
      _ = g * e₀ * g⁻¹ * x := by group

theorem D2L34SideCtx3.card_le_nine_of_le_ffC
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K)
    (hR9 : Nat.card R = 9) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) :
    ∀ X : Subgroup G, X ≤ ffC M T → IsPGroup 3 X → ¬ IsCyclic X → Nat.card X ≤ 9 := by
  have := ctx.amb
  have hc := ctx.conf
  set Z := quasithinOmegaOneCenter T with hZdef
  set V := CFSG.Quasithin.conjClosure Z M with hVdef
  have hMN : M ≤ Subgroup.normalizer (V : Set G) := CFSG.Quasithin.le_normalizer_conjClosure Z M
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨hU, -⟩ := B2_15 hF hT
  have hCn : ((ffC M T).subgroupOf M).Normal := centralizer_inf_subgroupOf_normal hU hMN
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hZ1 : Z ≠ ⊥ := Setup.omegaOneCenterOf_ne_bot hT.2.1 hT1
  have hZ2 : IsPGroup 2 Z := hT.2.1.to_le (Setup.omegaOneCenterOf_le T)
  have hNZ : ¬ Subgroup.normalizer (Z : Set G) ≤ M := fun h =>
    hNT ((CFSG.AGLEmbeddingD2.Tits.MsidePrelim.normalizer_le_normalizer_quasithinOmegaOneCenter
      T).trans h)
  have hCZ : ffC M T ≤ Subgroup.normalizer (Z : Set G) := by
    refine inf_le_left.trans ?_
    exact (Subgroup.centralizer_le (CFSG.Quasithin.le_conjClosure Z M)).trans
      (Subgroup.centralizer_le_normalizer _)
  intro X hX hXp hXc
  exact ctx.card_le_nine_of_le_normal hR9
    (⟨Z, hZ1, hZ2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (Z : Set G))) hNZ inf_le_right hCZ hCn
    hX hXp hXc

theorem D2L34SideCtx3.hasGoodE9_sylow (h : D2L34SideCtx3 G d P M A H R Rbar K) {C : Subgroup G}
    (hCM : C ≤ M) (hCn : (C.subgroupOf M).Normal) (S : Sylow 3 ↥C)
    (hS : ¬ IsCyclic ↥((S : Subgroup ↥C).map C.subtype)) :
    HasGoodE9 M ((S : Subgroup ↥C).map C.subtype) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D : Subgroup G := (S : Subgroup ↥C).map C.subtype with hD
  have hDC : D ≤ C := Subgroup.map_subtype_le _
  have hDp : IsPGroup 3 D := S.isPGroup'.map _
  obtain ⟨W, hWM, hWp, hWidx, hDW⟩ := exists_sylow_le (hDC.trans hCM) hDp
  have hWC : W ⊓ C = D := by
    have hle : (S : Subgroup ↥C) ≤ (W ⊓ C).subgroupOf C := fun x hx =>
      Subgroup.mem_subgroupOf.mpr ⟨hDW ⟨x, hx, rfl⟩, x.2⟩
    have hp : IsPGroup 3 ((W ⊓ C).subgroupOf C) :=
      (hWp.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have heq := S.is_maximal' hp hle
    rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : W ⊓ C ≤ C), heq]
  have hgood := h.hasGoodE9_inf_normal hCM hCn hWM hWp hWidx (by rw [hWC]; exact hS)
  rwa [hWC] at hgood

end Ctx

theorem ffNoncyclicInput3W_of_nodes
    (hI59 : AGL81I59) (hX : D1NoXBlock3 G) :
    ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
      (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      D2L34SideCtx3 G d P M A H R Rbar K → Nat.card R = 9 →
      CFSG.ABGLocalTools.IsPConstrained 3 ↥M → ∀ T : Subgroup G, IsSylowTwoOf T M →
      ¬ Subgroup.normalizer (T : Set G) ≤ M → ∀ S : Sylow 3 ↥(ffC M T),
        ¬ IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype) → Center3Conclusion M := by
  intro d P M A H R Rbar K ctx hR9 hcon T hT hNT S hS
  have hN : NoXBlockFor G := noXBlockFor_of_setting hX ctx.setting
  have := ctx.amb
  have hc := ctx.conf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMtop : M ≠ ⊤ := fun h => hc.esc.not_le (h ▸ le_top)
  have hKg : CFSG.Open.IsKGroup ↥M :=
    CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1
        (D2Amb3.glob (G := G)).kProper) M hMtop
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  set Z := quasithinOmegaOneCenter T with hZdef
  set V := CFSG.Quasithin.conjClosure Z M with hVdef
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := CFSG.Quasithin.le_normalizer_conjClosure Z M
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  ·
    have hZ1 : Z ≠ ⊥ := Setup.omegaOneCenterOf_ne_bot hT.2.1 hT1
    have hZ2 : IsPGroup 2 Z := hT.2.1.to_le (Setup.omegaOneCenterOf_le T)
    have hJ1 : thompsonJ T ≠ ⊥ := Setup.thompsonJ_ne_bot hT.2.1 hT1
    have hJ2 : IsPGroup 2 (thompsonJ T) := hT.2.1.to_le (B6.thompsonJ_le T)
    obtain ⟨-, hfac⟩ := CFSG.Quasithin.B2_7_of_le_factor hMV hT hJ
    have hfac' : ∀ m ∈ M, ∃ c ∈ ffC M T, ∃ b ∈ M ⊓ Subgroup.normalizer (thompsonJ T : Set G),
        m = c * b := by
      intro m hm
      obtain ⟨n, hn, c, hc', he⟩ := hfac m⁻¹ (M.inv_mem hm)
      refine ⟨c⁻¹, ?_, n⁻¹, (M ⊓ Subgroup.normalizer (thompsonJ T : Set G)).inv_mem hn, ?_⟩
      · have := (M ⊓ Subgroup.centralizer (V : Set G)).inv_mem hc'
        show c⁻¹ ∈ Subgroup.centralizer (V : Set G) ⊓ M
        rwa [inf_comm] at this
      · rw [← mul_inv_rev, ← he, inv_inv]
    have hCZ : ffC M T ≤ Subgroup.normalizer (Z : Set G) :=
      (Subgroup.centralizer_le (CFSG.Quasithin.le_conjClosure Z M)).trans
        (Subgroup.centralizer_le_normalizer _) |> fun h => inf_le_left.trans h
    obtain ⟨W, hWM, hWp, hWidx, E, hEW, hEel, hE9, hEC⟩ :=
      exists_center3_of_factorization3W ctx hR9 hcon hT hNT S hS hZ1 hZ2 hJ1 hJ2
        (CFSG.AGLEmbeddingD2.Tits.MsidePrelim.normalizer_le_normalizer_quasithinOmegaOneCenter T)
        (GammaExtra.normalizer_le_normalizer_thompsonJ T) hCZ inf_le_left inf_le_right hfac'
    exact Center3Conclusion.of_central hWM hWp hWidx hEW hEel hE9 hEC
  ·
    have hconAut := ffQuotientConstrained3_of_small hcon S hS
      (ctx.card_le_nine_of_le_ffC hR9 hT hNT)
    have hFF : FFConclusion M T V := hI59 G M T V hKg hF hT rfl hconAut hJ
    obtain ⟨hU, hMN, I, -, hcard, hJM, hSyl, hperm, hI⟩ :=
      exists_family_of_ffConclusion hT hJ hFF
    obtain ⟨C₁, C₂, hdat⟩ := exists_ffPairData3_free hN ffGroupStep3Free ctx hT hNT hU I hMN hcard
      hJM hSyl hperm hI
    obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
    have hVT : V ≤ T := hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT))
    have hBS : autI hU (baum T) ≤ autI hU (thompsonJ M) :=
      autI_baum_le_autI_thompsonJ hMN hT hVT hI hJM (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
        hperm
    have hSylB : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)) :=
      isSylowTwoOf_of_le_of_le hSyl (autI_mono hU (thompsonJ_le_baum T)) hBS
        (isPGroup_autI hU (hT.2.1.to_le (C1GN.baum_le T)))
    have hCM : ffC M T ≤ M := inf_le_right
    have hCn : ((ffC M T).subgroupOf M).Normal := centralizer_inf_subgroupOf_normal hU hMN
    obtain ⟨B, hBM, hBN, hfac⟩ := exists_factorization_of_pairData3_of_good hc hR9 ctx.normRankTwo
      hT hNT hMN hI hcard hSylB hJM hdat (D := (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype)
      (Subgroup.map_subtype_le _) (S.isPGroup'.map _) hS (ctx.hasGoodE9_sylow hCM hCn S hS)
    obtain ⟨hC₁1, hC₁2, hC₂1, hC₂2, hT₁, hT₂, hCM₁, -, -⟩ := hdat
    obtain ⟨W, hWM, hWp, hWidx, E, hEW, hEel, hE9, hEC⟩ :=
      exists_center3_of_factorization3W ctx hR9 hcon hT hNT S hS hC₁1 hC₁2 hC₂1 hC₂2 hT₁ hT₂
        hCM₁ hBM hBN hfac
    exact Center3Conclusion.of_central hWM hWp hWidx hEW hEel hE9 hEC

end CFSG.LocalAnalysis.RankThreeTheoremC
