module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.NoOther

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace CentConfig

variable {X : Type} [Group X] [Finite X] {a b : X} {E : Subgroup X} {Fus : X → Prop}

theorem self_comm (E : Subgroup X) : ⁅E, centralizer (E : Set X)⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Subgroup.le_centralizer_iff.mpr le_rfl

theorem self_inf (h : CentConfig X a b E Fus) : E ⊓ centralizer (E : Set X) = zpowers b := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_inf] at hx
    rcases h.center_E hx.1
      (fun y hy => Subgroup.mem_centralizer_iff.mp hx.2 y hy) with hx1 | hxb
    · rw [hx1]; exact Subgroup.one_mem _
    · rw [hxb]; exact Subgroup.mem_zpowers b
  · intro hx
    rw [Subgroup.mem_inf]
    exact ⟨Subgroup.zpowers_le.mpr h.b_mem hx,
      Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_iff.mpr fun e _he =>
          Subgroup.mem_center_iff.mp h.b_central e) hx⟩

theorem self_a_mem (h : CentConfig X a b E Fus) : a ∈ centralizer (E : Set X) :=
  Subgroup.mem_centralizer_iff.mpr fun _e he => h.a_comm he

theorem self_a_not_mem (h : CentConfig X a b E Fus) : a ∉ E := by
  intro ha
  have hbot : a ∈ (⊥ : Subgroup X) :=
    h.disj.le_bot (Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers a, ha⟩)
  exact h.a_ne (Subgroup.mem_bot.mp hbot)

theorem self_cent (h : CentConfig X a b E Fus) :
    ∀ y ∈ centralizer (E : Set X), y * a = a * y → y = 1 ∨ y = a ∨ y = b ∨ y = a * b := by
  intro y hy hya
  exact h.cent_cent_E hya fun e he => (Subgroup.mem_centralizer_iff.mp hy e he).symm

section Certified


theorem self_normal (h : CentConfig X a b E Fus) (hE : IsComponentOf E ⊤) : E.Normal :=
  h.normal_of_fixLarge hE le_rfl (fixLarge_of_isSp62Cover (IsTwoSp62.isSp62Cover h.E_two))

theorem self_sup (h : CentConfig X a b E Fus) (hE : IsComponentOf E ⊤) :
    E ⊔ centralizer (E : Set X) = ⊤ := by
  haveI : E.Normal := self_normal h hE
  rw [eq_top_iff]
  intro x _
  obtain ⟨e, he⟩ := (IsTwoSp62.isSp62Cover h.E_two).aut_inner
    (MulAut.conjNormal (H := E) x)
  let c : X := (e : X)⁻¹ * x
  have hc : c ∈ centralizer (E : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hxl : x * (l : X) * x⁻¹ = (e : X) * (l : X) * (e : X)⁻¹ := by
      have h1 := congrArg Subtype.val (DFunLike.congr_fun he (⟨l, hl⟩ : ↥E))
      simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using h1
    rw [show c = (e : X)⁻¹ * x from rfl]
    calc (l : X) * ((e : X)⁻¹ * x)
        = ((e : X)⁻¹ * ((e : X) * (l : X) * (e : X)⁻¹)) * x := by group
      _ = ((e : X)⁻¹ * (x * (l : X) * x⁻¹)) * x := by rw [← hxl]
      _ = ((e : X)⁻¹ * x) * (l : X) := by group
  have hx_eq : x = (e : X) * c := by
    dsimp only [c]
    group
  rw [hx_eq]
  exact Subgroup.mul_mem_sup e.2 hc

theorem self_quotient (h : CentConfig X a b E Fus) (hE : IsComponentOf E ⊤) [E.Normal] :
    LieModel (X ⧸ centralizer (E : Set X)) .PSp 3 2 1 := by
  let N : Subgroup X := centralizer (E : Set X)
  haveI : N.Normal := Subgroup.normal_centralizer
  let φ : ↥E →* X ⧸ N := (QuotientGroup.mk' N).comp E.subtype
  have hker : φ.ker = Subgroup.center ↥E := by
    ext l
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' N (l : X) = 1 ↔ l ∈ Subgroup.center ↥E
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_centralizer_iff,
      Subgroup.mem_center_iff]
    constructor
    · intro hh g
      exact Subtype.ext (hh g g.2)
    · intro hh e he
      simpa using congrArg Subtype.val (hh ⟨e, he⟩)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N := N) y
    have hx : x ∈ E ⊔ centralizer (E : Set X) := by
      rw [self_sup h hE]
      exact Subgroup.mem_top x
    obtain ⟨e, he, c, hc, hxec⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    refine ⟨⟨e, he⟩, ?_⟩
    rw [← hxec]
    change QuotientGroup.mk' N e = QuotientGroup.mk' N (e * c)
    rw [map_mul, show QuotientGroup.mk' N c = 1 from (QuotientGroup.eq_one_iff c).mpr hc,
      mul_one]
  exact LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ))
    h.E_two.2.2

theorem self_card (h : CentConfig X a b E Fus) : ∃ m, Odd m ∧ Nat.card E = 2 ^ 10 * m := by
  refine ⟨2835, by decide, ?_⟩
  rw [IsSp62Cover.card_eq (IsTwoSp62.isSp62Cover h.E_two), h.E_two.2.1]
  norm_num

end Certified

end CentConfig

end CFSG.EvenSporadicStandard.Co3Std.CentT
