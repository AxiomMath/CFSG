module

public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma23
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx38
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx41
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic11

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y : Subgroup G}

theorem Y_equiv_SL34 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1))
    (hY : YData S K₁ W₂ U h Y) (h29 : IV2_2_9_no_S3) {t : G} (htS : t ∈ S) (ht2 : t * t = 1)
    (hth : t * h * t⁻¹ = h⁻¹) : Nonempty (↥Y ≃* Bg.TwoGroups.SylSL3_4) := by
  have hhN : h⁻¹ ∈ normalizer (Y : Set G) := inv_mem (hY.h_mem_normalizer hs)
  have htN : t ∈ normalizer (Y : Set G) := hY.S_le_normalizer htS
  obtain ⟨x, hxapp⟩ : ∃ x : MulAut ↥Y, ∀ y : ↥Y, ((x y : ↥Y) : G) = h⁻¹ * y * h :=
    ⟨Basic.conjAut Y h⁻¹ hhN, fun y => by rw [Basic.conjAut_apply, inv_inv]⟩
  have hxx : ∀ y : ↥Y, ((x (x (x y)) : ↥Y) : G) = (y : G) := by
    intro y
    have hcen := hs.h_cube y (hY.le_W y.2)
    have e3 : h ^ 3 = h * h * h := by simp only [pow_succ, pow_zero, one_mul]
    rw [e3] at hcen
    rw [hxapp, hxapp, hxapp]
    calc h⁻¹ * (h⁻¹ * (h⁻¹ * (y : G) * h) * h) * h = (h * h * h)⁻¹ * ((y : G) * (h * h * h)) := by
          group
      _ = (h * h * h)⁻¹ * ((h * h * h) * (y : G)) := by rw [hcen]
      _ = y := by group
  have hx3 : x ^ 3 = 1 := by
    have e : x ^ 3 = x * x * x := by simp only [pow_succ, pow_zero, one_mul]
    rw [e]
    ext y
    exact hxx y
  have hfix : ∀ g : ↥Y, x g = g → g = 1 := by
    intro g hg
    have h1 : h⁻¹ * (g : G) * h = g := by
      have := congrArg (fun a : ↥Y => (a : G)) hg
      simp only [hxapp] at this
      exact this
    have : (g : G) = 1 := hY.cent_h g g.2 (by
      calc h * (g : G) = h * (h⁻¹ * (g : G) * h) := by rw [h1]
        _ = g * h := by group)
    exact Subtype.ext this
  have hxne : x ≠ 1 := by
    intro hx1
    have hall : ∀ y : ↥Y, y = 1 := fun y => hfix y (by rw [hx1]; rfl)
    have hbot : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).2 (fun y hy => by
      have := hall ⟨y, hy⟩
      exact congrArg Subtype.val this)
    have := hY.card
    rw [hbot, Subgroup.card_bot] at this
    omega
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  have hAY : Aof S K₁ W₂ h ≤ Y := hY.A_le
  have hAn : ((Aof S K₁ W₂ h).subgroupOf Y).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hs.A_normS hII hq hrec (hY.Y_le_S g.2) hn⟩
  have hxA : ∀ a ∈ (Aof S K₁ W₂ h).subgroupOf Y, x a ∈ (Aof S K₁ W₂ h).subgroupOf Y := by
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    rw [hxapp]
    exact (hs.A_conj hII hq hrec hk ha).2
  obtain ⟨eA⟩ := hs.A_equiv_Z4Z4 hII hq hrec hk
  have hZ : Nonempty (↥((Aof S K₁ W₂ h).subgroupOf Y) ≃* Bg.TwoGroups.Z4Z4) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hAY).trans eA⟩
  have hcent : centralizer (((Aof S K₁ W₂ h).subgroupOf Y : Subgroup ↥Y) : Set ↥Y) =
      (Aof S K₁ W₂ h).subgroupOf Y := by
    ext g
    constructor
    · intro hg
      rw [Subgroup.mem_subgroupOf, ← hs.cent_eq hII hq hrec]
      refine Subgroup.mem_inf.2 ⟨hY.Y_le_S g.2, Subgroup.mem_centralizer_iff.2 (fun a ha => ?_)⟩
      have hg' := Subgroup.mem_centralizer_iff.1 hg ⟨a, hAY ha⟩ (by
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        exact ha)
      exact congrArg Subtype.val hg'
    · intro hg
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha
      rw [Subgroup.mem_subgroupOf] at hg
      exact Subtype.ext (hs.A_comm hII hq hrec _ ha _ hg)
  obtain ⟨hU, hL⟩ := Bg.TwoGroups.iv2_2_3 ↥Y hY.card x hxo hfix _ hAn hxA hZ hcent
  by_cases hom : Bg.TwoGroups.Om1 ((Aof S K₁ W₂ h).subgroupOf Y) =
      Bg.TwoGroups.Om1 (⊤ : Subgroup ↥Y)
  · exfalso
    obtain ⟨y', hy'app⟩ : ∃ y' : MulAut ↥Y, ∀ y : ↥Y, ((y' y : ↥Y) : G) = t * y * t⁻¹ :=
      ⟨Basic.conjAut Y t htN, fun y => rfl⟩
    have ht2inv : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht2, inv_one]
    have hth' : t * h⁻¹ * t⁻¹ = h := by
      rw [show t * h⁻¹ * t⁻¹ = (t * h * t⁻¹)⁻¹ by group, hth, inv_inv]
    have hy'2 : y' * y' = 1 := by
      ext g
      show ((y' (y' g) : ↥Y) : G) = g
      rw [hy'app, hy'app]
      calc t * (t * (g : G) * t⁻¹) * t⁻¹ = (t * t) * (g : G) * (t⁻¹ * t⁻¹) := by group
        _ = g := by rw [ht2, ht2inv]; group
    have hrel : y' * x * y'⁻¹ = x⁻¹ := by
      have hinv : y'⁻¹ = y' := inv_eq_of_mul_eq_one_right hy'2
      apply eq_inv_of_mul_eq_one_left
      rw [hinv]
      ext g
      show ((y' (x (y' (x g))) : ↥Y) : G) = g
      rw [hy'app, hxapp, hy'app, hxapp]
      calc t * (h⁻¹ * (t * (h⁻¹ * (g : G) * h) * t⁻¹) * h) * t⁻¹
          = (t * h⁻¹ * t⁻¹) * (t * t) * (h⁻¹ * (g : G) * h) * (t⁻¹ * t⁻¹) * (t * h * t⁻¹) := by
            group
        _ = h * 1 * (h⁻¹ * (g : G) * h) * 1 * h⁻¹ := by rw [hth', ht2, ht2inv, hth]
        _ = g := by group
    obtain ⟨hNorm, ⟨e⟩⟩ := Basic.exists_sigma3 (G := MulAut ↥Y) (h := x) (t := y') (m := 0)
      (by rw [hxo]; norm_num) hy'2 hrel
    have hbot : (zpowers (x ^ 3)).subgroupOf (zpowers x ⊔ zpowers y') = ⊥ := by
      rw [hx3, Subgroup.zpowers_one_eq_bot, Subgroup.bot_subgroupOf]
    haveI := hNorm
    have e' : ↥(zpowers x ⊔ zpowers y') ≃* Equiv.Perm (Fin 3) :=
      ((QuotientGroup.quotientBot (G := ↥(zpowers x ⊔ zpowers y'))).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e
    exact h29 ↥Y (hU hom) (zpowers x ⊔ zpowers y') ⟨e'⟩
  · exact hL hom

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
