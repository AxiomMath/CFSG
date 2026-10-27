module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WCycB
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WCycC
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Card
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFSolvable
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Escape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {T : Subgroup G}

private theorem card_eq_pow_succ_of_isPGroup {Y : Subgroup G} (hY : IsPGroup 3 Y) {k : ℕ}
    (hlo : 3 ^ k < Nat.card Y) (hhi : Nat.card Y < 3 ^ (k + 2)) :
    Nat.card Y = 3 ^ (k + 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hY
  rw [hn] at hlo hhi ⊢
  have h1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlo
  have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hhi
  rw [show n = k + 1 by omega]

private theorem card_eq_nine_of_isPGroup {Y : Subgroup G} (hY : IsPGroup 3 Y)
    (hlo : 3 < Nat.card Y) (hhi : Nat.card Y < 27) : Nat.card Y = 9 := by
  have h := card_eq_pow_succ_of_isPGroup (k := 1) hY (by simpa using hlo) (by simpa using hhi)
  simpa using h

private theorem card_eq_27_of_isPGroup {Y : Subgroup G} (hY : IsPGroup 3 Y)
    (hlo : 9 < Nat.card Y) (hhi : Nat.card Y ≤ 27) : Nat.card Y = 27 := by
  have h := card_eq_pow_succ_of_isPGroup (k := 2) hY (by simpa using hlo)
    (by norm_num; omega)
  simpa using h

private theorem le_of_centralizes_of_not_comm {W₂ E Y : Subgroup G} (hW₂p : IsPGroup 3 W₂)
    (hW₂27 : Nat.card W₂ = 27) (hnc : ¬ ∀ a ∈ W₂, ∀ b ∈ W₂, a * b = b * a) (hEW₂ : E ≤ W₂)
    (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hYW₂ : Y ≤ W₂)
    (hYel : IsElemAbelian 3 Y) (hYc : ∀ y ∈ Y, ∀ w ∈ W₂, y * w = w * y) : Y ≤ E := by
  have hSel : IsElemAbelian 3 (E ⊔ Y) :=
    hEel.sup_of_commute hYel fun a ha b hb => (hYc b hb a (hEW₂ ha)).symm
  have hSW : E ⊔ Y ≤ W₂ := sup_le hEW₂ hYW₂
  by_contra hYE
  have hlo : 9 < Nat.card (E ⊔ Y : Subgroup G) := by
    by_contra hle
    have hEq : E = E ⊔ Y := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hE9]; omega)
    exact hYE (le_sup_right.trans hEq.symm.le)
  have hS27 := card_eq_27_of_isPGroup (hW₂p.to_le hSW) hlo
    ((Subgroup.card_le_of_le hSW).trans hW₂27.le)
  have hSeq : E ⊔ Y = W₂ := Subgroup.eq_of_le_of_card_ge hSW (by rw [hS27, hW₂27])
  exact hnc fun a ha b hb => hSel.comm (hSeq.ge ha) (hSeq.ge hb)

private theorem core_le_of_le_E27 (ctx : D2L34SideCtx3 G d P M A H R Rbar K) {E F : Subgroup G}
    (hEF : E ≤ F) (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hFM : F ≤ M)
    (hFel : IsElemAbelian 3 F) (hF27 : Nat.card F = 27) : GLBCore 3 1 E ≤ M := by
  obtain ⟨E', hE'E, -, hE'9, hcore⟩ := ctx.hasGoodE9_of_le_E27 le_rfl hEF hEel hE9 hFM hFel hF27
  rwa [← Subgroup.eq_of_le_of_card_ge hE'E (by rw [hE9, hE'9])]

theorem center3_of_cyclic_normal_mul27
    (c : D2L34R27 G d P M A H R Rbar K T) {W D₀ W₂ C₂ P₁ : Subgroup G} (hWM : W ≤ M)
    (hWp : IsPGroup 3 W) (hWidx : ¬ 3 ∣ (W.subgroupOf M).index) (hD₀W : D₀ ≤ W)
    (hWN : W ≤ Subgroup.normalizer (D₀ : Set G)) (hD₀c : IsCyclic D₀) (hW₂W : W₂ ≤ W)
    (hW₂N : W₂ ≤ Subgroup.normalizer (C₂ : Set G)) (hC₂ : C₂ ≠ ⊥) (hC₂2 : IsPGroup 2 C₂)
    (hT₂ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₂ : Set G))
    (hfac : ∀ w ∈ W, ∃ a ∈ D₀, ∃ b ∈ W₂, w = a * b) (hP₁D₀ : P₁ ≤ D₀) (hP₁3 : Nat.card P₁ = 3)
    (hwc : ∀ m ∈ M, ∀ p ∈ P₁, m * p * m⁻¹ ∈ W → m * p * m⁻¹ ∈ P₁) : Center3Conclusion M := by
  have := c.amb
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal c.ctx.setting c.ctx.sigma c.ctx.core
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
  have hW₂M : W₂ ≤ M := hW₂W.trans hWM
  have hW₂p : IsPGroup 3 W₂ := hWp.to_le hW₂W
  have hEcore : GLBCore 3 1 E ≤ M := core_le_of_le_E27 c.ctx hEF hEel hE9 hFM hFel hF27
  have hWN' : ∀ w ∈ W, ∀ e ∈ D₀, w * e * w⁻¹ ∈ D₀ := fun w hw e he =>
    (Subgroup.mem_normalizer_iff.mp (hWN hw) e).mp he
  have hP₁exp : ∀ p ∈ P₁, p ^ 3 = 1 := fun p hp => by
    have h := pow_card_eq_one' (G := ↥P₁) (x := ⟨p, hp⟩)
    rw [hP₁3] at h
    simpa using congrArg Subtype.val h
  have hP₁c : ∀ p ∈ P₁, ∀ w ∈ W, p * w = w * p := fun p hp w hw => by
    have h := conj_eq_of_pow_three_of_cyclic hWp hD₀c hWN' (hP₁D₀ hp) (hP₁exp p hp) hw
    calc p * w = w * p * w⁻¹ * w := by rw [h]
      _ = w * p := by group
  have hP₁W : P₁ ≤ W := hP₁D₀.trans hD₀W
  have hP₁el : IsElemAbelian 3 P₁ :=
    ⟨⟨⟨fun a b => Subtype.ext (hP₁c a a.2 b (hP₁W b.2))⟩⟩, hP₁exp⟩
  have hP₁1 : P₁ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hP₁3
    omega
  have hN2 : IsTwoLocal (Subgroup.normalizer (C₂ : Set G)) := ⟨C₂, hC₂, hC₂2, rfl⟩
  have hNM : ¬ Subgroup.normalizer (C₂ : Set G) ≤ M := fun h => c.not_normalizer_le (hT₂.trans h)
  obtain ⟨N₁, E₀, d₁, Rbar₁, K₁, -, hW₂E₀, hE₀27, hconf⟩ :=
    c.exists_conf_of_good hN2 hT₂ hNM hW₂N hW₂M hW₂p hEW₂ hEel hE9 hEcore
  have hexp : ∀ x ∈ W₂, x ^ 3 = 1 := fun x hx => hconf.pow_three_eq_one x (hW₂E₀ hx)
  have hW₂le : Nat.card W₂ ≤ 27 := (Subgroup.card_le_of_le hW₂E₀).trans hE₀27.le
  by_cases h9 : Nat.card W₂ ≤ 9
  ·
    have hEeq : E = W₂ := Subgroup.eq_of_le_of_card_ge hEW₂ (by rw [hE9]; exact h9)
    have hW₂el : IsElemAbelian 3 W₂ := hEeq ▸ hEel
    have hW₂F : W₂ ≤ F := hEeq ▸ hEF
    refine ⟨W, hWM, hWp, hWidx, E, hEW₂.trans hW₂W, hEel, hE9, fun w hw hw3 e he => ?_⟩
    have hwF : w ∈ F := pow_three_mem_of_cyclic_normal_mul hWp hmax hFW hFel hF27 hD₀W hWN hD₀c
      hW₂W hfac hW₂el hW₂F hw hw3
    exact congrArg Subtype.val (hFel.1.is_comm.comm ⟨w, hwF⟩ ⟨e, hEF he⟩)
  exfalso
  have h27 : Nat.card W₂ = 27 := card_eq_27_of_isPGroup hW₂p (by omega) hW₂le
  have hW₂eq : W₂ = E₀ := Subgroup.eq_of_le_of_card_ge hW₂E₀ (by rw [hE₀27, h27])
  have hnc : ¬ ∀ a ∈ W₂, ∀ b ∈ W₂, a * b = b * a := by
    rcases hconf.card_R_eq_nine_or_27 with h | ⟨-, -, -, h⟩
    · omega
    · rwa [hW₂eq]
  by_cases hP₁W₂ : P₁ ≤ W₂
  ·
    have hP₁E : P₁ ≤ E := le_of_centralizes_of_not_comm hW₂p h27 hnc hEW₂ hEel hE9 hP₁W₂ hP₁el
      fun p hp w hw => hP₁c p hp w (hW₂W hw)
    obtain ⟨p, hp⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hP₁1
    obtain ⟨y, hyE, hyP⟩ : ∃ y ∈ E, y ∉ P₁ := by
      by_contra hall
      have hle : E ≤ P₁ := fun y hy => by_contra fun hyP => hall ⟨y, hy, hyP⟩
      have := Subgroup.card_le_of_le hle
      rw [hE9, hP₁3] at this
      omega
    have hy1 : y ≠ 1 := fun h => hyP (h ▸ P₁.one_mem)
    obtain ⟨n, hn, hny⟩ := c.exists_conj_eq_of_good hN2 hT₂ hNM (hEW₂.trans hW₂N)
      (hEW₂.trans hW₂M) hEel hE9 hEcore p (hP₁E p.2) (fun h => hp (Subtype.ext h)) y hyE hy1
    have hmem : n * (p : G) * n⁻¹ ∈ W := by
      rw [hny]
      exact hW₂W (hEW₂ hyE)
    exact hyP (by rw [← hny]; exact hwc n (Subgroup.mem_inf.mp hn).1 p p.2 hmem)
  ·
    have hext := hconf.isExtraspecialPGroup_of_card_R_eq_27 hE₀27
    rw [← hW₂eq] at hext
    set Z : Subgroup G := (Subgroup.center ↥W₂).map W₂.subtype with hZ
    have hZW₂ : Z ≤ W₂ := Subgroup.map_subtype_le _
    have hZ3 : Nat.card Z = 3 := by
      rw [hZ, Subgroup.card_map_of_injective W₂.subtype_injective]
      exact hext.2.2.2
    have hZc : ∀ z ∈ Z, ∀ w ∈ W₂, z * w = w * z := by
      rintro _ ⟨z, hz, rfl⟩ w hw
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨w, hw⟩)).symm
    have hZel : IsElemAbelian 3 Z :=
      ⟨⟨⟨fun a b => Subtype.ext (hZc a a.2 b (hZW₂ b.2))⟩⟩, fun z hz => hexp z (hZW₂ hz)⟩
    have hZE : Z ≤ E := le_of_centralizes_of_not_comm hW₂p h27 hnc hEW₂ hEel hE9 hZW₂ hZel hZc
    obtain ⟨x, hxW₂, hxE⟩ : ∃ x ∈ W₂, x ∉ E := by
      by_contra hall
      have hle : W₂ ≤ E := fun x hx => by_contra fun hxE => hall ⟨x, hx, hxE⟩
      have := Subgroup.card_le_of_le hle
      rw [h27, hE9] at this
      omega
    set E' : Subgroup G := Subgroup.closure ((Z : Set G) ∪ {x}) with hE'
    have hE'el : IsElemAbelian 3 E' := by
      refine IsElemAbelian.closure_of_commute ?_ ?_
      · rintro a (ha | ha) b (hb | hb)
        · exact hZel.comm ha hb
        · rw [Set.mem_singleton_iff.mp hb]
          exact hZc a ha x hxW₂
        · rw [Set.mem_singleton_iff.mp ha]
          exact (hZc b hb x hxW₂).symm
        · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
      · rintro a (ha | ha)
        · exact hZel.2 a ha
        · rw [Set.mem_singleton_iff.mp ha]
          exact hexp x hxW₂
    have hE'W₂ : E' ≤ W₂ := (Subgroup.closure_le W₂).2
      (Set.union_subset (SetLike.coe_subset_coe.mpr hZW₂) (Set.singleton_subset_iff.2 hxW₂))
    have hxE' : x ∈ E' := Subgroup.subset_closure (Or.inr (Set.mem_singleton x))
    have hZE' : Z ≤ E' := fun z hz => Subgroup.subset_closure (Or.inl hz)
    have hE'9 : Nat.card E' = 9 := by
      refine card_eq_nine_of_isPGroup (hW₂p.to_le hE'W₂) ?_ ?_
      · by_contra hle
        have hZeq : Z = E' := Subgroup.eq_of_le_of_card_ge hZE' (by rw [hZ3]; omega)
        exact hxE (hZE (hZeq.ge hxE'))
      · by_contra hle
        have hEq : E' = W₂ := Subgroup.eq_of_le_of_card_ge hE'W₂ (by rw [h27]; omega)
        exact hnc fun a ha b hb => hE'el.comm (hEq.ge ha) (hEq.ge hb)
    have hF'el : IsElemAbelian 3 (E' ⊔ P₁) := hE'el.sup_of_commute hP₁el
      fun a ha b hb => (hP₁c b hb a (hW₂W (hE'W₂ ha))).symm
    have hF'W : E' ⊔ P₁ ≤ W := sup_le (hE'W₂.trans hW₂W) hP₁W
    have hF'27 : Nat.card (E' ⊔ P₁ : Subgroup G) = 27 := by
      refine card_eq_27_of_isPGroup (hWp.to_le hF'W) ?_ (hmax _ hF'W hF'el)
      by_contra hle
      have hEq : E' = E' ⊔ P₁ := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hE'9]; omega)
      exact hP₁W₂ ((le_sup_right.trans hEq.symm.le).trans hE'W₂)
    have hE'core : GLBCore 3 1 E' ≤ M :=
      core_le_of_le_E27 c.ctx le_sup_left hE'el hE'9 (hF'W.trans hWM) hF'el hF'27
    have hE'E : E' = E := c.eq_of_good hN2 hNM hW₂N hW₂M hW₂p hEW₂ hEel hE9 hEcore hE'W₂ hE'el
      hE'9 hE'core
    exact hxE (hE'E.le hxE')

theorem center3_of_factorization_cyclic27
    (c : D2L34R27 G d P M A H R Rbar K T) (S : Sylow 3 ↥(ffC M T))
    (hS : IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype))
    (hS0 : (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype ≠ ⊥)
    {C₂ B : Subgroup G} (hC₂ : C₂ ≠ ⊥) (hC₂2 : IsPGroup 2 C₂)
    (hT₂ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₂ : Set G))
    (hBM : B ≤ M) (hBN : B ≤ Subgroup.normalizer (C₂ : Set G))
    (hfac : ∀ m ∈ M, ∃ c ∈ ffC M T, ∃ b ∈ B, m = c * b) : Center3Conclusion M := by
  have := c.amb
  have hc := c.ctx.conf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : IsSylowTwoOf T M := c.sylow
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
  have hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M :=
    CFSG.ABGLocalTools.isPConstrained_of_isSolvable c.solvable
  obtain ⟨P₀, hP₀D₀, hP₀3, hP₀n⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_normal_order_three_of_cyclic_sylow hCM hCn
      (ffSolvableInput G M T hF hT hcon S hS) ⟨S, rfl⟩ hS hS0
  have hD₀C : (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype ≤ ffC M T :=
    Subgroup.map_subtype_le _
  have hP₀M : P₀ ≤ M := hP₀D₀.trans (hD₀C.trans hCM)
  set P₁ : Subgroup G := P₀.map (MulAut.conj g).toMonoidHom with hP₁
  have hP₁D : P₁ ≤ W ⊓ ffC M T := by
    rw [hWC]
    exact Subgroup.map_mono hP₀D₀
  have hP₁3 : Nat.card P₁ = 3 := by
    rw [hP₁, Subgroup.card_map_of_injective (MulAut.conj g).injective, hP₀3]
  have hNn : M ≤ Subgroup.normalizer ((GLBPrimeCore 3 M ⊔ P₀ : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hP₀M (glbPrimeCore_le 3 M))).1 hP₀n
  have hNW : Nat.card ((GLBPrimeCore 3 M ⊔ P₀ : Subgroup G) ⊓ W : Subgroup G) ≤ 3 :=
    card_le_three_of_isPGroup_le_sup hP₀3 (glbPrimeCore_coprime 3 M)
      (hP₀M.trans (le_normalizer_glbPrimeCore 3 M)) (hWp.to_le inf_le_right) inf_le_left
  have hP₁NW : P₁ ≤ (GLBPrimeCore 3 M ⊔ P₀ : Subgroup G) ⊓ W := by
    refine le_inf ?_ (hP₁D.trans inf_le_left)
    rintro _ ⟨p, hp, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hNn hgM) p).mp (Subgroup.mem_sup_right hp)
  have hwc : ∀ m ∈ M, ∀ p ∈ P₁, m * p * m⁻¹ ∈ W → m * p * m⁻¹ ∈ P₁ := fun m hm p hp hmp =>
    weakly_closed_of_normal_inf hNn hNW hP₁3 hP₁NW hm hp hmp
  exact center3_of_cyclic_normal_mul27 c hWM hWp hWidx inf_le_left hDN hDc hW₂W
    (hW₂B.trans hBN) hC₂ hC₂2 hT₂ hWfac hP₁D hP₁3 hwc

theorem center3_of_thompson_cyclic27
    (c : D2L34R27 G d P M A H R Rbar K T) (S : Sylow 3 ↥(ffC M T))
    (hS : IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype))
    (hS0 : (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype ≠ ⊥)
    (hJ : thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) M : Set G)) : Center3Conclusion M := by
  have := c.amb
  have hc := c.ctx.conf
  have hT := c.sylow
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
  exact center3_of_factorization_cyclic27 c S hS hS0 hJ1 hJ2
    (GammaExtra.normalizer_le_normalizer_thompsonJ T) inf_le_left inf_le_right hfac'

end CFSG.LocalAnalysis.RankThreeTheoremC
