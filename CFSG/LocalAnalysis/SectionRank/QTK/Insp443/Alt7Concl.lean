module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Quasithin.Vol2.KGFactC31J4Gen
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFe
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E14Iso
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E17Trans
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.KGFactC31Ident

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
open CFSG.Quasithin.KGC31
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {v : Fin 4 → G} {hv : EBasis v} {M : Subgroup G}

theorem alt7_card (hle : eSub hv ≤ M) (α : ↥M →* ↥(alternatingGroup (Fin 7)))
    (hα : Function.Surjective α) (hker : α.ker = (eSub hv).subgroupOf M) :
    Nat.card M = 40320 := by
  have h := card_range_eq hle α hker
  rw [MonoidHom.range_eq_top.mpr hα, Subgroup.card_top, A7.card_alt7, card_eSub] at h
  rw [← h]
  norm_num

theorem alt7_pCoreOf (hd : RefData (eSub hv) M) (α : ↥M →* ↥(alternatingGroup (Fin 7)))
    (hα : Function.Surjective α) (hker : α.ker = (eSub hv).subgroupOf M) :
    pCoreOf 2 M = eSub hv := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine pCoreOf_eq_of_max hd.le hd.norm (IsPGroup.of_card (n := 4) (card_eSub hv)) hd.simple ?_
  intro h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  rw [alt7_card hd.le α hα hker] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 40320)
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

noncomputable def alt7QuotEquiv (hd : RefData (eSub hv) M)
    (α : ↥M →* ↥(alternatingGroup (Fin 7))) (hα : Function.Surjective α)
    (hker : α.ker = (eSub hv).subgroupOf M) :
    ↥M ⧸ CFSG.pCore 2 ↥M ≃* ↥(alternatingGroup (Fin 7)) :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [← Hex.pCoreOf_subgroupOf', alt7_pCoreOf hd α hα hker, hker])).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)

theorem alt7_isFFModule (hd : RefData (eSub hv) M) (α : ↥M →* ↥(alternatingGroup (Fin 7)))
    (hα : Function.Surjective α) (hker : α.ker = (eSub hv).subgroupOf M)
    [IsMulCommutative ↥(eSub hv)] : IsFFModule (autOn M (eSub hv)) := by
  let V := eSub hv
  letI : IsMulCommutative ↥V := ‹IsMulCommutative ↥(eSub hv)›
  let ρ : ↥M →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion hd.norm)
  have hρker : ρ.ker = V.subgroupOf M := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      change conjAct V ⟨x, hd.norm x.2⟩ = 1 at h
      have hmem : (x : G) ∈ Subgroup.centralizer (V : Set G) :=
        (CFSG.Quasithin.AutOn.conjAct_eq_one_iff (V := V) ⟨x, hd.norm x.2⟩).mp h
      exact hd.cent hmem
    · intro hx
      have hmem : (x : G) ∈ Subgroup.centralizer (V : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm hv y x hy hx
      show conjAct V ⟨x, hd.norm x.2⟩ = 1
      exact (CFSG.Quasithin.AutOn.conjAct_eq_one_iff (V := V) ⟨x, hd.norm x.2⟩).mpr hmem
  have hkerρα : α.ker ≤ ρ.ker := by rw [hρker, hker]
  let ρbar : ↥(alternatingGroup (Fin 7)) →* MulAut ↥V :=
    MonoidHom.liftOfSurjective α hα ⟨ρ, hkerρα⟩
  have hρbar_apply : ∀ x : ↥M, ρbar (α x) = ρ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply α _ _ ⟨ρ, hkerρα⟩ x
  have hρbar_ker : ρbar.ker = ⊥ := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_bot]
      obtain ⟨x, rfl⟩ := hα y
      have h1 : ρ x = 1 := by rw [← hρbar_apply x]; exact hy
      have h1' : x ∈ ρ.ker := by rwa [MonoidHom.mem_ker]
      rw [hρker, Subgroup.mem_subgroupOf] at h1'
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      exact h1'
    · intro hy
      rw [Subgroup.mem_bot] at hy
      rw [MonoidHom.mem_ker, hy, MonoidHom.map_one]
  have hρbar_inj : Function.Injective ρbar := (MonoidHom.ker_eq_bot_iff ρbar).mp hρbar_ker
  let E : Subgroup (MulAut ↥V) := (ρbar.comp FFe.k7).range
  have hcomp_inj : Function.Injective (ρbar.comp FFe.k7) := hρbar_inj.comp FFe.k7_injective
  have hEcard : Nat.card E = 4 := by
    change Nat.card ↥((ρbar.comp FFe.k7).range) = 4
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hcomp_inj, Subgroup.card_top]
    show Nat.card (Fin 2 → ZMod 2) = 4
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    rfl
  have hE_le : E ≤ autOn M V := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨x, hx⟩ := hα (FFe.k7 w)
    have hρx : ρ x = ρbar (FFe.k7 w) := by
      rw [← hρbar_apply x, hx]
    change ρbar (FFe.k7 w) ∈ autOn M V
    rw [← hρx]
    exact CFSG.Quasithin.AutOn.conjAct_mem_autOn (X := M) ⟨x, hd.norm x.2⟩ x.2
  have hE2 : ∀ e ∈ E, e ^ 2 = 1 := by
    rintro _ ⟨w, rfl⟩
    rw [← map_pow]
    have hw : w ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      funext j
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul,
        Nat.cast_ofNat]
      exact (show ∀ x : ZMod 2, 2 * x = 0 by decide) _
    rw [hw, map_one]
  have hNE : E ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card E = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hEcard] at h1
    norm_num at h1
  have hEcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := by
    rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩
    change ρbar (FFe.k7 w) * ρbar (FFe.k7 w') = ρbar (FFe.k7 w') * ρbar (FFe.k7 w)
    calc ρbar (FFe.k7 w) * ρbar (FFe.k7 w')
        = ρbar (FFe.k7 (w * w')) := by rw [← map_mul, ← map_mul (f := FFe.k7) w w']
      _ = ρbar (FFe.k7 (w' * w)) := by rw [mul_comm w w']
      _ = ρbar (FFe.k7 w' * FFe.k7 w) := by rw [map_mul (f := FFe.k7) w' w]
      _ = ρbar (FFe.k7 w') * ρbar (FFe.k7 w) := map_mul ρbar _ _
  let τ : MulAut ↥V := ρbar FFe.t7
  have hτ3 : τ ^ 3 = 1 := by rw [← map_pow, FFe.t7_pow_three, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    exact FFe.t7_ne_one (hρbar_inj (h.trans (map_one ρbar).symm))
  have hτE : ∀ e ∈ E, e * τ = τ * e := by
    rintro _ ⟨w, rfl⟩
    change ρbar (FFe.k7 w) * ρbar FFe.t7 = ρbar FFe.t7 * ρbar (FFe.k7 w)
    calc ρbar (FFe.k7 w) * ρbar FFe.t7
        = ρbar (FFe.k7 w * FFe.t7) := (map_mul ρbar _ _).symm
      _ = ρbar (FFe.t7 * FFe.k7 w) := by rw [FFe.t7_comm]
      _ = ρbar FFe.t7 * ρbar (FFe.k7 w) := map_mul ρbar _ _
  have hV2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => by
    rw [pow_two]
    exact Subtype.ext (eSub_sq hv (w : G) w.2)
  have hfix : 4 ≤ Nat.card (fixV E) := FFe.four_le_card_fixV hV2 hE2 hτ3 hτ1 hτE
  refine ⟨E, hE_le, hNE, ⟨hEcomm, hE2⟩, ?_⟩
  rw [card_eSub, hEcard]
  have h4 := Nat.mul_le_mul_left 4 hfix
  norm_num at h4 ⊢
  exact h4

theorem conclK_of_alt7 (hd : RefData (eSub hv) M) (α : ↥M →* ↥(alternatingGroup (Fin 7)))
    (hα : Function.Surjective α) (hker : α.ker = (eSub hv).subgroupOf M) (MK : Subgroup G) :
    ConclK G M (eSub hv) MK := by
  unfold ConclK
  let e := alt7QuotEquiv hd α hα hker
  have hq : CFSG.IsQuasisimple (↥M ⧸ CFSG.pCore 2 ↥M) :=
    CFSG.IsQuasisimple.of_mulEquiv e
      (Hex.isQuasisimple_of_simple A7.alt7_simple A7.alt7_nonabelian)
  have hcardX : Nat.card (↥M ⧸ CFSG.pCore 2 ↥M) = 2520 := by
    rw [Nat.card_congr e.toEquiv, A7.card_alt7]
  have hshape : Shape443 (↥M ⧸ CFSG.pCore 2 ↥M) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))
  have hcommV : IsMulCommutative ↥(eSub hv) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm hv x y hx hy
  letI : IsMulCommutative ↥(eSub hv) := hcommV
  have hFF : IsFFModule (autOn (Subgroup.normalizer (eSub hv : Set G)) (eSub hv)) :=
    isFFModule_of_le (autOn_mono' hd.norm) (alt7_isFFModule hd α hα hker)
  refine Or.inl ⟨hq, hshape, Or.inl ⟨⟨hcommV, hFF⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro h3
    have h1 := LieModel.card_psl_three_two h3
    rw [hcardX] at h1
    norm_num at h1
  ·
    intro h4
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (h4.statedClassicalModel (by decide))
    rw [hcardX] at h1
    norm_num at h1
  ·
    rintro ⟨-, hc, -⟩
    rw [F420.center_eq_bot_of_mulEquiv' e (alternatingGroup.center_eq_bot (by norm_num))] at hc
    rw [Subgroup.card_bot] at hc
    norm_num at hc
  ·
    intro _ h64
    rw [card_eSub] at h64
    norm_num at h64

end CFSG.SectionRank.QTK.Insp443

end
