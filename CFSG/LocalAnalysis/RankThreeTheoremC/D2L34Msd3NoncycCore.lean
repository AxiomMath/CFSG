module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3NoncycSquare
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3TailMain
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFConstrained
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3TwoEscB

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.AGLEmbeddingD2.Tits CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_order_three_of_factorization3
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) (S : Sylow 3 ↥(ffC M T))
    (hS : ¬ IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype))
    {C₁ C₂ B : Subgroup G} (hC₁ : C₁ ≠ ⊥) (hC₁2 : IsPGroup 2 C₁) (hC₂ : C₂ ≠ ⊥)
    (hC₂2 : IsPGroup 2 C₂)
    (hT₁ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₁ : Set G))
    (hT₂ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₂ : Set G))
    (hCM₁ : ffC M T ≤ Subgroup.normalizer (C₁ : Set G))
    (hBM : B ≤ M) (hBN : B ≤ Subgroup.normalizer (C₂ : Set G))
    (hfac : ∀ m ∈ M, ∃ c ∈ ffC M T, ∃ b ∈ B, m = c * b) :
    ∃ P₀ : Subgroup G, P₀ ≤ M ∧ Nat.card P₀ = 3 ∧
      ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal := by
  have := ctx.amb
  have hc := ctx.conf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN₁ : ¬ Subgroup.normalizer (C₁ : Set G) ≤ M := fun h => hNT (hT₁.trans h)
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
  have hC9 : ∀ X : Subgroup G, X ≤ ffC M T → IsPGroup 3 X → ¬ IsCyclic X → Nat.card X ≤ 9 :=
    fun X hX hXp hXc => D2L34BetaConf3.card_le_nine_of_not_isCyclic hc hstr
      (⟨C₁, hC₁, hC₁2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C₁ : Set G))) hN₁
      (hX.trans hCM₁) (hX.trans hCM) hXp hXc
  have hsmall := small_of_noncyclic_sylow (ffC M T) S hS hC9
  obtain ⟨W, W₂, hWM, hWp, hWidx, hW₂B, hW₂W, hWfac⟩ :=
    exists_sylow_of_normal_mul hCM hCnM hBM hfac
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal ctx.setting ctx.sigma ctx.core
  have h3 : 3 ≤ CFSG.Open.pRank 3 M :=
    hP3.ge.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hPM)
  have hPidx : ¬ 3 ∣ ((P : Subgroup G).subgroupOf M).index := fun h =>
    P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hPM))
  obtain ⟨A₀, hA₀W, hA₀el, hA₀c⟩ := exists_elemAbelian_le_sylow_pow hWM hWp hWidx h3
  have hmax : ∀ A : Subgroup G, A ≤ W → IsElemAbelian 3 A → Nat.card A ≤ 27 := fun A hAW hA =>
    card_le_of_isElemAbelian_of_pRank hPM P.isPGroup' hPidx hP3 (hAW.trans hWM) hA
  set D₀ : Subgroup G := (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype with hD₀
  have hD₀C : D₀ ≤ ffC M T := Subgroup.map_subtype_le _
  have hD₀p : IsPGroup 3 D₀ := S.isPGroup'.map _
  obtain ⟨hD₀el, hD₀le⟩ := hsmall D₀ hD₀C hD₀p
  have hD₀9 : Nat.card D₀ = 9 :=
    le_antisymm hD₀le (Nat.le_of_dvd Nat.card_pos (nine_dvd_card_of_not_isCyclic hD₀p hS))
  obtain ⟨g, hgM, hgD⟩ := exists_conj_map_le_of_isPGroup hWM hWp hWidx (hD₀C.trans hCM) hD₀p
  set D : Subgroup G := D₀.map (MulAut.conj g).toMonoidHom with hD
  have hDW : D ≤ W := hgD
  have hDC : D ≤ ffC M T := by
    rintro _ ⟨x, hx, rfl⟩
    have hxC : x ∈ ffC M T := hD₀C hx
    exact (Subgroup.mem_normalizer_iff.1 (hCnM hgM) x).1 hxC
  have hDp : IsPGroup 3 D := hD₀p.map _
  have hDel : IsElemAbelian 3 D :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hD₀el _
  have hD9 : Nat.card D = 9 := by
    rw [hD, Subgroup.card_map_of_injective (MulAut.conj g).injective, hD₀9]
  have hDc : ¬ IsCyclic D := not_isCyclic_of_isElemAbelian hDel (by rw [hD9]; norm_num)
  have hWC : W ⊓ ffC M T = D :=
    (Subgroup.eq_of_le_of_card_ge (le_inf hDW hDC) (by
      have := hsmall (W ⊓ ffC M T) inf_le_right (hWp.to_le inf_le_left)
      rw [hD9]
      exact this.2)).symm
  have hW₂p : IsPGroup 3 W₂ := hWp.to_le hW₂W
  have hWle : W ≤ D ⊔ W₂ := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hWfac w hw
    rw [hWC] at ha
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have hW27 : 27 ≤ Nat.card W := by
    have := Subgroup.card_le_of_le hA₀W
    rw [hA₀c] at this
    norm_num at this
    exact this
  have hW₂cyc : IsCyclic W₂ := by
    by_contra hW₂c
    have hcard : 9 < Nat.card (D ⊔ W₂ : Subgroup G) := by
      have := Subgroup.card_le_of_le hWle
      omega
    exact D2L34BetaConf3.false_of_two_escapes ctx.conf hstr ctx.allResidue hT hNT hC₁ hC₁2 hT₁
      hC₂ hC₂2 hT₂ (W₁ := D) (W₂ := W₂) (le_inf (hDW.trans hWM) (hDC.trans hCM₁))
      (le_inf (hW₂W.trans hWM) (hW₂B.trans hBN)) hDp hW₂p hDc hW₂c
      (hWp.to_le (sup_le hDW hW₂W)) hcard
  have hW₂comm : ∀ y ∈ W₂, ∀ y' ∈ W₂, y * y' = y' * y := fun y hy y' hy' => by
    have := (IsCyclic.commGroup (α := W₂)).mul_comm ⟨y, hy⟩ ⟨y', hy'⟩
    exact congrArg Subtype.val this
  have hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hDel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hR : ∀ a ∈ W ⊓ Subgroup.centralizer (D : Set G), ∀ b ∈ W ⊓ Subgroup.centralizer (D : Set G),
      a * b = b * a := by
    have hpart : ∀ a ∈ W ⊓ Subgroup.centralizer (D : Set G), ∃ x ∈ D, ∃ y ∈ W₂, a = x * y ∧
        ∀ e ∈ D, y * e = e * y := by
      intro a ha
      obtain ⟨x, hx, y, hy, hxy⟩ := hWfac a ha.1
      rw [hWC] at hx
      refine ⟨x, hx, y, hy, hxy, fun e he => ?_⟩
      have h1 := Subgroup.mem_centralizer_iff.1 ha.2 e he
      have h2 := hDab e he x hx
      rw [hxy] at h1
      calc y * e = x⁻¹ * (x * y * e) := by group
        _ = x⁻¹ * (e * (x * y)) := by rw [h1]
        _ = x⁻¹ * (e * x) * y := by group
        _ = x⁻¹ * (x * e) * y := by rw [h2]
        _ = e * y := by group
    intro a ha b hb
    obtain ⟨x, hx, y, hy, rfl, hye⟩ := hpart a ha
    obtain ⟨x', hx', y', hy', rfl, hy'e⟩ := hpart b hb
    have h1 := hW₂comm y hy y' hy'
    have h2 := hDab x hx x' hx'
    calc x * y * (x' * y') = x * (y * x') * y' := by group
      _ = x * (x' * y) * y' := by rw [hye x' hx']
      _ = (x * x') * (y * y') := by group
      _ = (x' * x) * (y' * y) := by rw [h2, h1]
      _ = x' * (x * y') * y := by group
      _ = x' * (y' * x) * y := by rw [hy'e x hx]
      _ = x' * y' * (x * y) := by group
  obtain ⟨s, hsM, hsD, hs2⟩ := exists_inverting_square3 ctx hstr hT hNT hC₁ hC₁2 hT₁
    (hDW.trans hWM) (hDC.trans hCM₁) hDp hDc hD9
  have hA27 : Nat.card A₀ = 27 := by rw [hA₀c]; norm_num
  exact exists_normal_order_three_of_tail3 hcon hCn (fun E hE hEp => (hsmall E hE hEp).2) hWM hWp
    hWidx hDW hDC hD9 hDab hDel.2 hR
    ⟨A₀, hA₀W, fun a ha b hb => congrArg Subtype.val (hA₀el.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩),
      hA₀el.2, hA27⟩
    (fun A hA hab h3' => hmax A hA ⟨⟨⟨fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2)⟩⟩, h3'⟩)
    hsM hsD hs2

end CFSG.LocalAnalysis.RankThreeTheoremC
