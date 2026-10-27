module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Inputs
public import CFSG.Quasithin.Background.FFC10C

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def AsB69GenByMinK : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M : Subgroup (MulAut V)), CFSG.SectionRank.IsKGroupCat ↥X →
      MinParabolic X T M → pCoreOf 2 X = ⊥ → IsFFModule X → ¬ Group.IsSolvable ↥X →
      ffJ X ≤ ffJP {A | IsFFStarMin X A} X

theorem asB69ComponentK_iff : AsB69ComponentK ↔
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (X T M A L : Subgroup (MulAut V)), CompHypK X T M A L →
        ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) → CompShape T M A L W :=
  Iff.rfl

theorem shapeCtxK_of_component (hComp : AsB69ComponentK) (hV : ∀ v : V, v ^ 2 = 1)
    {X T M : Subgroup (MulAut V)} (hK : CFSG.SectionRank.IsKGroupCat ↥X)
    (h : MinParabolic X T M) (hO2 : pCoreOf 2 X = ⊥) (hFF : IsFFModule X)
    (hns : ¬ Group.IsSolvable ↥X) : ShapeCtx X T M :=
  fun A L hA hL hLA W hW =>
    asB69ComponentK_iff.1 hComp V hV X T M A L ⟨hK, h, hO2, hFF, hns, hA, hL, hLA⟩ W hW

theorem asB69GenByMinK_of (hP4 : AsB15Part4) (hComp : AsB69ComponentK) : AsB69GenByMinK := by
  intro V _ _ hV X T M hK h hO2 hFF hns
  have hctx : ShapeCtx X T M := shapeCtxK_of_component hComp hV hK h hO2 hFF hns
  have hact := exists_active hV hP4 h hO2 hFF hns
  have hst : IsStableFF X {A | IsFFStarMin X A} := B1_7 hV hFF
  set N : Subgroup (MulAut V) := ffJP {A | IsFFStarMin X A} X with hNdef
  have hNX : N ≤ X := iSup₂_le fun A _ => iSup_le fun hAX => hAX
  have hNn : X ≤ Subgroup.normalizer (N : Set (MulAut V)) := fun g hg =>
    B6.mem_normalizer_of_forall_mem (fun x hx => B1Red.ffJP_conj_mem hst hg hx)
      (fun x hx => by simpa using B1Red.ffJP_conj_mem hst (X.inv_mem hg) hx)
  have hPN : ∀ A : Subgroup (MulAut V), IsFFStarMin X A → A ≤ N := fun A hA =>
    B19.le_ffJP hA hA.1.1
  have hblkN : ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X → blk X L ≤ N := by
    intro L hL
    obtain ⟨A₀, hA₀, hLA₀⟩ := hact L hL
    refine blk_le_iff.2 ⟨?_, fun A hA _ => hPN A hA⟩
    rw [← hLA₀]
    refine Subgroup.commutator_le.2 fun l hl a ha => ?_
    have h1 : l * a * l⁻¹ ∈ N := B1Red.ffJP_conj_mem hst (hL.1 hl) (hPN A₀ hA₀ ha)
    exact N.mul_mem h1 (N.inv_mem (hPN A₀ hA₀ ha))
  obtain ⟨A₀, hA₀⟩ := hst.1
  have hres : twoResidual X ≤ N := by
    rcases h.le_kerIn_or_twoResidual_le hNX hNn with hJ | hK
    · exfalso
      have hA₀2 : IsPGroup 2 A₀ := fun x => ⟨1, by
        apply Subtype.ext
        simpa using hA₀.1.2.2.1.2 _ x.2⟩
      have := h.le_pCoreOf_of_isPGroup_of_le_kerIn hA₀2 ((hPN A₀ hA₀).trans hJ)
      rw [hO2] at this
      exact hA₀.1.2.1 (le_bot_iff.1 this)
    · exact hK
  set R : Subgroup (MulAut V) := X ⊓ centSub (vSigma X) with hRdef
  have hXst : X ≤ stabSub (vSigma X) := B1.le_stabSub_of_invariant (vSigma_invariant X)
  have hRn : X ≤ Subgroup.normalizer (R : Set (MulAut V)) := fun g hg =>
    B6.mem_normalizer_of_forall_mem
      (fun x hx => ⟨X.mul_mem (X.mul_mem hg hx.1) (X.inv_mem hg), conj_mem_centSub (hXst hg) hx.2⟩)
      (fun x hx => ⟨X.mul_mem (X.mul_mem (X.inv_mem hg) hx.1) hg, by
        simpa using conj_mem_centSub (hXst (X.inv_mem hg)) hx.2⟩)
  have hRN : R ≤ N := by
    refine le_trans ?_ hres
    rcases h.le_kerIn_or_twoResidual_le inf_le_left hRn with hJ | hK
    ·
      intro r hr
      have hrJ : r ∈ kerIn M X := hJ hr
      have hrX : r ∈ X := hr.1
      obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf r) (orderOf_pos r).ne'
      have hm0 : m ≠ 0 := hm.pos.ne'
      have hodd : Odd (orderOf r) := by
        have hord2 : orderOf (r ^ m) = 2 ^ a := by
          rw [orderOf_pow_of_dvd hm0 ⟨2 ^ a, by rw [hord, mul_comm]⟩, hord,
            Nat.mul_div_cancel _ hm.pos]
        have h2grp : IsPGroup 2 (Subgroup.zpowers (r ^ m)) :=
          IsPGroup.of_card (by rw [Nat.card_zpowers, hord2])
        have hzJ : Subgroup.zpowers (r ^ m) ≤ kerIn M X := Subgroup.zpowers_le.2 ((kerIn M X).pow_mem hrJ m)
        have hz := h.le_pCoreOf_of_isPGroup_of_le_kerIn h2grp hzJ
        rw [hO2] at hz
        have h1 : r ^ m = 1 := Subgroup.mem_bot.1 (hz (Subgroup.mem_zpowers _))
        exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient X r hrX
      exact B6.mem_of_pow_mem_of_coprime hk (Nat.Coprime.pow_right k (Odd.coprime_two_right hodd))
    · exfalso
      obtain ⟨L, hL, hLA⟩ := exists_component_of_nonsolvable hV hP4 h hO2 hns hA₀
      have hW : commV L ∈ IrrPlus L (⊤ : Subgroup V) := commV_mem_irrPlus hV hctx hA₀ hL hLA
      have hlt := (mem_irrPlus_top_iff.1 hW).2.2.1
      have hLR : L ≤ R := (component_le_twoResidual hL).trans hK
      refine absurd ?_ (not_le_of_gt hlt)
      intro w hw
      refine ⟨hw, fun l hl => ?_⟩
      exact (hLR hl).2 w (commV_le_vSigma hL hw)
  refine iSup₂_le fun B hB => ?_
  intro b hb
  have hfin : {L : Subgroup (MulAut V) | CFSG.Open.IsComponentOf L X}.Finite := Set.toFinite _
  obtain ⟨hh, hhN, hh1, -⟩ := exists_blk_prod hV hP4 hctx hact hblkN hB hb hfin.toFinset
    (fun L hL => hfin.mem_toFinset.1 hL)
  have hcR : hh⁻¹ * b ∈ R := by
    refine ⟨X.mul_mem (X.inv_mem (hNX hhN)) (hB.1 hb), fun u hu => ?_⟩
    have hle : vSigma X ≤ MonoidHom.eqLocus ((hh⁻¹ * b : MulAut V) : V →* V) (MonoidHom.id V) := by
      refine iSup₂_le fun L hL w hw => ?_
      have e : b w = hh w := (hh1 L (hfin.mem_toFinset.2 hL) w hw).symm
      show hh⁻¹ (b w) = w
      rw [e]
      simp
    exact hle hu
  have := N.mul_mem hhN (hRN hcR)
  simpa using this

theorem blkCtxK_of_inputs (hP4 : AsB15Part4) (hComp : AsB69ComponentK) (hG2 : AsB69GenByMinK)
    (hV : ∀ v : V, v ^ 2 = 1) {X T M : Subgroup (MulAut V)}
    (hK : CFSG.SectionRank.IsKGroupCat ↥X) (h : MinParabolic X T M) (hO2 : pCoreOf 2 X = ⊥)
    (hFF : IsFFModule X) (hns : ¬ Group.IsSolvable ↥X) : BlkCtx X T M := by
  have hctx : ShapeCtx X T M := shapeCtxK_of_component hComp hV hK h hO2 hFF hns
  have hact := exists_active hV hP4 h hO2 hFF hns
  have hffJ : ffJ X ≤ ⨆ (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X), blk X L := by
    refine (hG2 V hV X T M hK h hO2 hFF hns).trans ?_
    refine iSup₂_le fun A hA => iSup_le fun _ => ?_
    obtain ⟨L, hL, hLA⟩ := exists_component_of_nonsolvable hV hP4 h hO2 hns hA
    exact (le_blk_of hA hLA).trans
      (le_iSup₂_of_le (f := fun (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X) =>
        blk X L) L hL le_rfl)
  have hG1' : ∀ A L : Subgroup (MulAut V), IsFFStarMin X A → CFSG.Open.IsComponentOf L X →
      ⁅L, A⁆ = L → AltShape M A L (commV L) → ∀ A' : Subgroup (MulAut V), IsFFStarMin X A' →
        ⁅L, A'⁆ = L → A' ≤ L ⊔ A := fun A L hA hL hLA hAlt A' hA' hLA' =>
    altBlock_of_ctx hV hP4 hctx hO2 hact hA hL hLA hAlt hA' hLA'
  exact ⟨hV, hP4, hctx, hO2, hact, hffJ, hG1'⟩

end B69

end CFSG.Quasithin
