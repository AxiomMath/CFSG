module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterGood
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.XFiveQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterStructCatalog
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupEight
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5AutHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecOdd

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard
  CFSG.OddStandard.AltStdSec CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

@[expose] def HSOuterL44Free : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S : Subgroup G) (z n v s : G),
    CFSG.EvenSporadicStandard.Induction.Balance.UHered G → HSOuterSetup G L t S z n v s →
      ∀ W : Subgroup (OuterSection v), W.Normal → LieModel W .PSL 4 2 2 → False

@[expose] def HSOuterGoodCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S : Subgroup G) (z n v s : G),
    CFSG.EvenSporadicStandard.Induction.Balance.UHered G → HSOuterSetup G L t S z n v s → F v t

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

theorem exactShape_outerSection (h : HSOuterSetup G L t S z n v s) (hF : F v t) :
    ExactShape h.tBar (sectionImage v (derivedCentralizerIn L v)) 8 := by
  have d := good_data h hF
  refine ⟨h.orderOf_tBar, h.sectionImage_equiv, ?_, ?_, ?_⟩
  · intro a ha
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 d.cent a ha)
  · intro y hy
    exact d.H1 y (mem_centralizer_singleton_iff.1 hy)
  · apply le_antisymm
    · rintro y ⟨hyA, hyt⟩
      exact d.H3 y hyA (mem_centralizer_singleton_iff.1 hyt)
    · rw [zpowers_le]
      exact ⟨d.cent, mem_centralizer_singleton_iff.2 rfl⟩

theorem isKGroupCat_outerSection (h : HSOuterSetup G L t S z n v s) :
    CFSG.SectionRank.IsKGroupCat (OuterSection v) :=
  (Zassenhaus.isKGroupCat_of_kProper_aux h.setting.1.kProper
    (centralizer_singleton_ne_top h.setting.1.simple h.setting.1.nonabelian
      h.v_ne_one)).quotient _

theorem oddCore_outerSection (h : HSOuterSetup G L t S z n v s) :
    CFSG.oddCore (OuterSection v) = ⊥ :=
  outerSection_oddCore_eq_bot h.ctx.v_sq h.v_ne_one
    (h.setting.1.oddCore v (orderOf_eq_prime (by rw [pow_two]; exact h.ctx.v_sq) h.v_ne_one))

theorem equiv_mulAut_hs_of_hsOutcome
    {X : Type} [Group X] [Finite X] {τ : X} (h : HSOutcome τ) :
    Nonempty (X ≃* MulAut (Carrier .HS)) := by
  obtain ⟨W, hWN, hCW, hτW, ⟨eW⟩⟩ := h
  have := hWN
  have hMA := card_mulAut_of_isSporadic_hs (Y := ↥W) ⟨eW⟩
  let c : X →* MulAut ↥W := MulAut.conjNormal
  have hinj : Function.Injective c := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hgC : g ∈ centralizer (W : Set X) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := DFunLike.congr_fun (MonoidHom.mem_ker.1 hg) ⟨y, hy⟩
      have h2 : g * y * g⁻¹ = y := by
        have := congrArg Subtype.val h1
        simpa [c, MulAut.conjNormal_apply] using this
      calc y * g = (g * y * g⁻¹) * g := by rw [h2]
        _ = g * y := by group
    rw [hCW] at hgC
    exact hgC
  have hcardW : Nat.card ↥W = 44352000 :=
    (Nat.card_congr eW.toEquiv).trans CFSG.Sporadic.HS.card_HS
  have hle : Nat.card X ≤ 88704000 := hMA ▸ Nat.card_le_card_of_injective c hinj
  have hidx1 : W.index ≠ 1 := fun h1 => hτW (Subgroup.index_eq_one.1 h1 ▸ mem_top τ)
  have hidx0 : W.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul := Subgroup.card_mul_index W
  rw [hcardW] at hmul
  have hcardX : Nat.card X = 88704000 := by
    obtain ⟨k, hk⟩ : ∃ k, W.index = k := ⟨_, rfl⟩
    rw [hk] at hmul hidx1 hidx0
    omega
  have hbij : Function.Bijective c :=
    hinj.bijective_of_nat_card_le (by rw [hMA, hcardX])
  exact ⟨(MulEquiv.ofBijective c hbij).trans (MulAut.congr eW)⟩

end CFSG.EvenSporadicStandard.HSStd
