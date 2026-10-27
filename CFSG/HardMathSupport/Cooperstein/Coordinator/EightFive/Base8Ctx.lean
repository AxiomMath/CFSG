module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Defs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7Ctx
import CFSG.GH74.Exceptional.LinearFourTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Equiv Equiv.Perm

theorem statedClassicalModel_of_alt8 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 8)) :
    StatedClassicalModel X .PSL 4 2 1 :=
  ⟨⟨Nat.prime_two, le_rfl, by decide⟩, ZMod 2, inferInstance, inferInstance, by simp,
    ⟨(e.trans CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo).trans
      (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo (Nat.card_zmod 2) 4).symm⟩⟩

theorem b42TypeL42_of_equiv {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    (e : X ≃* alternatingGroup (Fin 8)) : B42TypeL42 X := by
  let e₁ : (X ⧸ Subgroup.center X) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨hZ, statedClassicalModel_of_alt8 (e₁.trans e), ⟨e₁.trans e⟩⟩

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 8)}

theorem b42Hyp_autSec (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 8) ≤ ψ.range)
    {Y₀ Y₁ : Subgroup V} (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) :
    autSec (altPre ψ) Y₁ Y₀ = quasithinGenFitting (autSec H Y₁ Y₀) ∧
      CFSG.IsQuasisimple ↥(autSec (altPre ψ) Y₁ Y₀) ∧ B42TypeL42 ↥(autSec (altPre ψ) Y₁ Y₀) := by
  set σ := secHom hH₀ hH₁ with hσdef
  have hσinj : Function.Injective σ :=
    secHom_injective hH₀ hH₁ (inf_centSec_eq_bot (by norm_num) hψ hA hH₀ hH₁ hL)
  have hrange : σ.range = autSec H Y₁ Y₀ := range_secHom hH₀ hH₁
  have hLX : ((altPre ψ).subgroupOf H).map σ = autSec (altPre ψ) Y₁ Y₀ :=
    map_secHom hH₀ hH₁ altPre_le
  let eL : ↥(autSec (altPre ψ) Y₁ Y₀) ≃* alternatingGroup (Fin 8) :=
    ((MulEquiv.subgroupCongr hLX).symm.trans
      (Subgroup.equivMapOfInjective ((altPre ψ).subgroupOf H) σ hσinj).symm).trans
      ((Subgroup.subgroupOfEquivOfLe altPre_le).trans (altPreEquiv hψ hA))
  let eH : ↥H ≃* ↥(autSec H Y₁ Y₀) :=
    (MonoidHom.ofInjective hσinj).trans (MulEquiv.subgroupCongr hrange)
  have hmemG : ∀ y ∈ autSec H Y₁ Y₀, ∃ h : ↥H, σ h = y := fun y hy => by
    rw [← hrange] at hy
    exact hy
  have hsq : ∀ y ∈ autSec H Y₁ Y₀, y ^ 2 ∈ autSec (altPre ψ) Y₁ Y₀ := by
    intro y hy
    obtain ⟨h, rfl⟩ := hmemG y hy
    rw [← hLX, ← map_pow]
    refine ⟨h ^ 2, ?_, rfl⟩
    change h ^ 2 ∈ (altPre ψ).subgroupOf H
    rw [Subgroup.mem_subgroupOf]
    refine coe_mem_altPre_iff.2 ?_
    rw [map_pow, Equiv.Perm.mem_alternatingGroup, map_pow, Int.units_sq]
  have hnormal : ∀ y ∈ autSec H Y₁ Y₀, ∀ l ∈ autSec (altPre ψ) Y₁ Y₀,
      y * l * y⁻¹ ∈ autSec (altPre ψ) Y₁ Y₀ := by
    intro y hy l hl
    obtain ⟨h, rfl⟩ := hmemG y hy
    rw [← hLX] at hl ⊢
    obtain ⟨l', hl', rfl⟩ := hl
    rw [← map_inv, ← map_mul, ← map_mul]
    exact ⟨h * l' * h⁻¹, altPre_normal.conj_mem l' hl' h, rfl⟩
  have : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hsimp : IsSimpleGroup ↥(autSec (altPre ψ) Y₁ Y₀) := eL.isSimpleGroup
  have hnonab : ∃ a b : ↥(autSec (altPre ψ) Y₁ Y₀), a * b ≠ b * a := by
    have h4 : 4 ≤ Nat.card (Fin 8) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
    have hc := alternatingGroup.center_eq_bot h4
    have : Nontrivial (alternatingGroup (Fin 8)) :=
      alternatingGroup.nontrivial_of_three_le_card (by omega)
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := exists_ne (1 : alternatingGroup (Fin 8))
    have hxc : x ∈ Subgroup.center (alternatingGroup (Fin 8)) :=
      Subgroup.mem_center_iff.2 fun g => by
        have := h (eL.symm g) (eL.symm x)
        exact eL.symm.injective (by rw [map_mul, map_mul]; exact this)
    rw [hc] at hxc
    exact hx (Subgroup.mem_bot.1 hxc)
  obtain ⟨hquasi, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab
  have hquasi' : CFSG.Open.IsQuasisimple ↥(autSec (altPre ψ) Y₁ Y₀) :=
    A3.isQuasisimple_iff_open.1 hquasi
  have hNbot : ∀ N : Subgroup ↥(autSec H Y₁ Y₀), N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hNn hNp
    have h1 : N.comap eH.toMonoidHom = ⊥ :=
      eq_bot_of_normal_isPGroup_two (by norm_num) hψ hA (hNn.comap _)
        (hNp.comap_of_injective _ eH.injective)
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := eH.toMonoidHom) eH.surjective N, h1,
      Subgroup.map_bot]
  have hO2 : CFSG.Open.pCoreOf 2 (autSec H Y₁ Y₀) = ⊥ := by
    rw [CFSG.Open.pCoreOf, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)]
    simp only [CFSG.pCore_eq_iSup, iSup_eq_bot]
    exact fun N hNn hNp => hNbot N hNn hNp
  have : Finite (MulAut (Sec Y₁ Y₀)) := Finite.of_injective _ DFunLike.coe_injective
  exact ⟨(B1Red.quasithinGenFitting_eq_of_two_quot (autSec_mono altPre_le Y₁ Y₀) hnormal
    hquasi' hsq hO2).symm, hquasi, b42TypeL42_of_equiv hZ eL⟩

theorem b42_autSec (hB42 : B42L42Core) (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 8) ≤ ψ.range) {Y₀ Y₁ : Subgroup V} (hH₀ : H ≤ stabSub Y₀)
    (hH₁ : H ≤ stabSub Y₁) (hlt : Y₀ < Y₁) (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁)
    (hirr : ∀ Y : Subgroup V, (∀ l ∈ altPre ψ, ∀ y ∈ Y, l y ∈ Y) → Y₀ ≤ Y → Y ≤ Y₁ →
      Y = Y₀ ∨ Y = Y₁)
    {A₀ : Subgroup (MulAut (Sec Y₁ Y₀))} (hA₀ : IsFFStarOffender (autSec H Y₁ Y₀) A₀) :
    B42Case9 (autSec H Y₁ Y₀) (autSec (altPre ψ) Y₁ Y₀) ∨
      B42Case10 (autSec H Y₁ Y₀) (autSec (altPre ψ) Y₁ Y₀) A₀ := by
  obtain ⟨hF, hq, hT⟩ := b42Hyp_autSec hψ hA hH₀ hH₁ hL
  have hI := isIrrSec_autSec (altPre_le.trans hH₀) (altPre_le.trans hH₁) hlt hirr
  exact hB42 (Sec Y₁ Y₀) (sq_eq_one_sec hV Y₁ Y₀) _ _ ⟨hF, hq, hI⟩ hT A₀ hA₀

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
