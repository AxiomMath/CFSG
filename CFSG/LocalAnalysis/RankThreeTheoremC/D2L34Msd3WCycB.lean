module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WNoncycD
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WCycA

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]

theorem center3_of_cyclic_normal_mul
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    {W D₀ W₂ C₂ : Subgroup G} (hWM : W ≤ M) (hWp : IsPGroup 3 W)
    (hWidx : ¬ 3 ∣ (W.subgroupOf M).index) (hD₀W : D₀ ≤ W)
    (hWN : W ≤ Subgroup.normalizer (D₀ : Set G)) (hD₀c : IsCyclic D₀) (hW₂W : W₂ ≤ W)
    (hW₂N : W₂ ≤ Subgroup.normalizer (C₂ : Set G)) (hC₂ : C₂ ≠ ⊥) (hC₂2 : IsPGroup 2 C₂)
    (hN₂ : ¬ Subgroup.normalizer (C₂ : Set G) ≤ M)
    (hfac : ∀ w ∈ W, ∃ a ∈ D₀, ∃ b ∈ W₂, w = a * b) : Center3Conclusion M := by
  have := ctx.amb
  have hc := ctx.conf
  have hOnly := ctx.allResidue.onlyL34At
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal ctx.setting ctx.sigma ctx.core
  have h3 : 3 ≤ CFSG.Open.pRank 3 M :=
    hP3.ge.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hPM)
  have hPidx : ¬ 3 ∣ ((P : Subgroup G).subgroupOf M).index := fun h =>
    P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hPM))
  have hmax : ∀ A : Subgroup G, A ≤ W → IsElemAbelian 3 A → Nat.card A ≤ 27 := fun A hAW hA =>
    card_le_of_isElemAbelian_of_pRank hPM P.isPGroup' hPidx hP3 (hAW.trans hWM) hA
  obtain ⟨F, hFW, hFel, hFc⟩ := exists_elemAbelian_le_sylow_pow hWM hWp hWidx h3
  have hF27 : Nat.card F = 27 := by rw [hFc]; norm_num
  obtain ⟨E, hEW₂, hEF, hEel, hE9⟩ := exists_E9_le_inf_of_cyclic_normal_mul hWp hmax hFW hFel hF27
    hD₀W hWN hD₀c hW₂W hfac
  have hFM : F ≤ M := hFW.trans hWM
  have hgood : HasGoodE9 M W₂ := ctx.hasGoodE9_of_le_E27 hEW₂ hEF hEel hE9 hFM hFel hF27
  have hW₂M : W₂ ≤ M := hW₂W.trans hWM
  have hW₂p : IsPGroup 3 W₂ := hWp.to_le hW₂W
  have hEnc : ¬ IsCyclic E := not_isCyclic_of_isElemAbelian hEel (by rw [hE9]; norm_num)
  have hW₂c : ¬ IsCyclic W₂ := fun hcyc => by
    have := hcyc
    exact hEnc (Subgroup.isCyclic_of_le hEW₂)
  obtain ⟨hW₂el, hW₂9, -⟩ := D2L34BetaConf3.exists_conj_eq_of_good hc hR9 ctx.normRankTwo hOnly
    (⟨C₂, hC₂, hC₂2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C₂ : Set G))) hN₂ hW₂N hW₂M hW₂p
    hW₂c hgood
  have hEeq : E = W₂ := Subgroup.eq_of_le_of_card_ge hEW₂ (by rw [hE9, hW₂9])
  have hW₂F : W₂ ≤ F := by rw [← hEeq]; exact hEF
  refine ⟨W, hWM, hWp, hWidx, E, hEW₂.trans hW₂W, hEel, hE9, fun w hw hw3 e he => ?_⟩
  have hwF : w ∈ F := pow_three_mem_of_cyclic_normal_mul hWp hmax hFW hFel hF27 hD₀W hWN hD₀c
    hW₂W hfac hW₂el hW₂F hw hw3
  exact congrArg Subtype.val (hFel.1.is_comm.comm ⟨w, hwF⟩ ⟨e, hEF he⟩)

theorem card_le_of_isPGroup_of_sylow {C Q : Subgroup G} (hQC : Q ≤ C) (hQp : IsPGroup 3 Q)
    (S : Sylow 3 ↥C) : Nat.card Q ≤ Nat.card ((S : Subgroup ↥C).map C.subtype) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQp' : IsPGroup 3 (Q.subgroupOf C) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
  obtain ⟨S', hS'⟩ := hQp'.exists_le_sylow
  have hcard : Nat.card S' = Nat.card S := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  calc Nat.card Q = Nat.card (Q.subgroupOf C) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv).symm
    _ ≤ Nat.card S' := Subgroup.card_le_of_le hS'
    _ = Nat.card ((S : Subgroup ↥C).map C.subtype) := by
        rw [hcard, Subgroup.card_map_of_injective C.subtype_injective]

theorem exists_conj_inf_eq_map_sylow {M C W : Subgroup G} (hCM : C ≤ M)
    (hCnM : M ≤ Subgroup.normalizer (C : Set G)) (hWM : W ≤ M) (hWp : IsPGroup 3 W)
    (hWidx : ¬ 3 ∣ (W.subgroupOf M).index) (S : Sylow 3 ↥C) :
    ∃ g ∈ M, W ⊓ C = ((S : Subgroup ↥C).map C.subtype).map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D₀ : Subgroup G := (S : Subgroup ↥C).map C.subtype with hD₀
  have hD₀C : D₀ ≤ C := Subgroup.map_subtype_le _
  have hD₀p : IsPGroup 3 D₀ := S.isPGroup'.map _
  obtain ⟨g, hgM, hgD⟩ := exists_conj_map_le_of_isPGroup hWM hWp hWidx (hD₀C.trans hCM) hD₀p
  have hDC : D₀.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hCnM hgM) x).1 (hD₀C hx)
  have hDcard : Nat.card (D₀.map (MulAut.conj g).toMonoidHom) = Nat.card D₀ :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  refine ⟨g, hgM, (Subgroup.eq_of_le_of_card_ge (le_inf hgD hDC) ?_).symm⟩
  rw [hDcard]
  exact card_le_of_isPGroup_of_sylow inf_le_right (hWp.to_le inf_le_left) S

theorem center3_of_factorization_cyclic3W
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (hR9 : Nat.card R = 9) {T : Subgroup G}
    (hT : IsSylowTwoOf T M) (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (S : Sylow 3 ↥(ffC M T))
    (hS : IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype))
    {C₂ B : Subgroup G} (hC₂ : C₂ ≠ ⊥) (hC₂2 : IsPGroup 2 C₂)
    (hT₂ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₂ : Set G))
    (hBM : B ≤ M) (hBN : B ≤ Subgroup.normalizer (C₂ : Set G))
    (hfac : ∀ m ∈ M, ∃ c ∈ ffC M T, ∃ b ∈ B, m = c * b) : Center3Conclusion M := by
  have := ctx.amb
  have hc := ctx.conf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN₂ : ¬ Subgroup.normalizer (C₂ : Set G) ≤ M := fun h => hNT (hT₂.trans h)
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨hU, -⟩ := B2_15 hF hT
  have hMN : M ≤ Subgroup.normalizer
      ((conjClosure (quasithinOmegaOneCenter T) M : Subgroup G) : Set G) :=
    (conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)).2.2.2.1
  have hCn : ((ffC M T).subgroupOf M).Normal := centralizer_inf_subgroupOf_normal hU hMN
  have hCM : ffC M T ≤ M := inf_le_right
  have hCnM : M ≤ Subgroup.normalizer ((ffC M T : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCM).1 hCn
  obtain ⟨W, W₂, hWM, hWp, hWidx, hW₂B, hW₂W, hWfac⟩ :=
    exists_sylow_of_normal_mul hCM hCnM hBM hfac
  obtain ⟨g, hgM, hWC⟩ := exists_conj_inf_eq_map_sylow hCM hCnM hWM hWp hWidx S
  have hDc : IsCyclic ↥(W ⊓ ffC M T) := by
    rw [hWC]
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective
      ((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)).mp hS
  have hDN : W ≤ Subgroup.normalizer ((W ⊓ ffC M T : Subgroup G) : Set G) := fun w hw =>
    mem_normalizer_inf_of_mem_normalizers (Subgroup.le_normalizer hw) (hCnM (hWM hw))
  exact center3_of_cyclic_normal_mul ctx hR9 hWM hWp hWidx inf_le_left hDN hDc hW₂W
    (hW₂B.trans hBN) hC₂ hC₂2 hN₂ hWfac

theorem center3_of_thompson_cyclic3W
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (hR9 : Nat.card R = 9) {T : Subgroup G}
    (hT : IsSylowTwoOf T M) (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (S : Sylow 3 ↥(ffC M T))
    (hS : IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype))
    (hJ : thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) M : Set G)) : Center3Conclusion M := by
  have := ctx.amb
  have hc := ctx.conf
  set Z := quasithinOmegaOneCenter T with hZdef
  set V := CFSG.Quasithin.conjClosure Z M with hVdef
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := CFSG.Quasithin.le_normalizer_conjClosure Z M
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
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
  exact center3_of_factorization_cyclic3W ctx hR9 hT hNT S hS hJ1 hJ2
    (GammaExtra.normalizer_le_normalizer_thompsonJ T) inf_le_left inf_le_right hfac'

end CFSG.LocalAnalysis.RankThreeTheoremC
