module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7Sec
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Basic
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Perfect
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleFaith
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.QuasithinUnique Equiv Equiv.Perm

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}

theorem eq_bot_of_normal_isPGroup_two (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) {N : Subgroup ↥H} (hN : N.Normal)
    (hp : IsPGroup 2 N) : N = ⊥ := by
  set L := altPre ψ with hLdef
  let K : Subgroup ↥L := (N.map H.subtype).subgroupOf L
  have hKn : K.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨⟨g, altPre_le g.2⟩ * y * ⟨g, altPre_le g.2⟩⁻¹, hN.conj_mem y hy _, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyx ⊢
    rw [hyx]⟩
  have : IsSimpleGroup ↥L := isSimpleGroup_altPre h5 hψ hA
  rcases hKn.eq_bot_or_eq_top with hK | hK
  · rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine eq_one_of_commute_altPre (by omega) hψ hA x.2 fun l hl => ?_
    have hlH : l ∈ H := altPre_le hl
    have hc : (x : MulAut V) * l * (x : MulAut V)⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem (conj_mem_altPre x.2 hl) (L.inv_mem hl)
    have hcN : x * ⟨l, hlH⟩ * x⁻¹ * (⟨l, hlH⟩ : ↥H)⁻¹ ∈ N := by
      have h1 := hN.conj_mem x⁻¹ (N.inv_mem hx) ⟨l, hlH⟩
      have h2 := N.mul_mem hx h1
      simpa only [mul_assoc] using h2
    have hcK : (⟨_, hc⟩ : ↥L) ∈ K := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨_, hcN, rfl⟩
    rw [hK, Subgroup.mem_bot] at hcK
    have h3 : (x : MulAut V) * l * (x : MulAut V)⁻¹ * l⁻¹ = 1 := congrArg Subtype.val hcK
    calc (x : MulAut V) * l = (x : MulAut V) * l * (x : MulAut V)⁻¹ * l⁻¹ * (l * x) := by group
      _ = l * x := by rw [h3, one_mul]
  · exfalso
    obtain ⟨σ, hσ⟩ := exists_isThreeCycle (m := n) (by omega)
    set l : ↥L := (altPreEquiv hψ hA).symm σ with hl
    have hlK : l ∈ K := hK ▸ Subgroup.mem_top l
    rw [Subgroup.mem_subgroupOf] at hlK
    obtain ⟨y, hy, hyl⟩ := hlK
    obtain ⟨k, hk⟩ := hp ⟨y, hy⟩
    have h1 : (y : MulAut V) ^ 2 ^ k = 1 := by
      have := congrArg (fun z : ↥N => ((z : ↥H) : MulAut V)) hk
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using this
    have h2 : l ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hyl]
      exact h1
    have h3 : σ ^ 2 ^ k = 1 := by
      have := congrArg (altPreEquiv hψ hA) h2
      rwa [map_pow, hl, MulEquiv.apply_symm_apply, map_one] at this
    have h4 : (σ : Perm (Fin n)) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val h3
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using this
    have h5 := orderOf_dvd_of_pow_eq_one h4
    rw [hσ.orderOf] at h5
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5)
    omega

variable [Finite V]

theorem ctx_autSec (hn : n = 5 ∨ n = 7) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) {Y₀ Y₁ : Subgroup V} (hH₀ : H ≤ stabSub Y₀)
    (hH₁ : H ≤ stabSub Y₁) (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) :
    Bridge.Alt57.Ctx (autSec H Y₁ Y₀) (autSec (altPre ψ) Y₁ Y₀) n := by
  have h5 : 5 ≤ n := by omega
  set σ := secHom hH₀ hH₁ with hσdef
  have hσinj : Function.Injective σ :=
    secHom_injective hH₀ hH₁ (inf_centSec_eq_bot h5 hψ hA hH₀ hH₁ hL)
  have hrange : σ.range = autSec H Y₁ Y₀ := range_secHom hH₀ hH₁
  have hLX : ((altPre ψ).subgroupOf H).map σ = autSec (altPre ψ) Y₁ Y₀ :=
    map_secHom hH₀ hH₁ altPre_le
  let eL : ↥(autSec (altPre ψ) Y₁ Y₀) ≃* alternatingGroup (Fin n) :=
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
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hsimp : IsSimpleGroup ↥(autSec (altPre ψ) Y₁ Y₀) := eL.isSimpleGroup
  have hnonab : ∃ a b : ↥(autSec (altPre ψ) Y₁ Y₀), a * b ≠ b * a := by
    have h4 : 4 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
    have hc := alternatingGroup.center_eq_bot h4
    have : Nontrivial (alternatingGroup (Fin n)) :=
      alternatingGroup.nontrivial_of_three_le_card (by omega)
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := exists_ne (1 : alternatingGroup (Fin n))
    have hxc : x ∈ Subgroup.center (alternatingGroup (Fin n)) :=
      Subgroup.mem_center_iff.2 fun g => by
        have := h (eL.symm g) (eL.symm x)
        exact eL.symm.injective (by rw [map_mul, map_mul]; exact this)
    rw [hc] at hxc
    exact hx (Subgroup.mem_bot.1 hxc)
  have hquasi : CFSG.Open.IsQuasisimple ↥(autSec (altPre ψ) Y₁ Y₀) :=
    A3.isQuasisimple_iff_open.1 (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1
  have hNbot : ∀ N : Subgroup ↥(autSec H Y₁ Y₀), N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hNn hNp
    have h1 : N.comap eH.toMonoidHom = ⊥ :=
      eq_bot_of_normal_isPGroup_two h5 hψ hA (hNn.comap _) (hNp.comap_of_injective _ eH.injective)
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := eH.toMonoidHom) eH.surjective N, h1,
      Subgroup.map_bot]
  have hO2 : CFSG.Open.pCoreOf 2 (autSec H Y₁ Y₀) = ⊥ := by
    rw [CFSG.Open.pCoreOf, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)]
    simp only [CFSG.pCore_eq_iSup, iSup_eq_bot]
    exact fun N hNn hNp => hNbot N hNn hNp
  have : Finite (MulAut (Sec Y₁ Y₀)) := Finite.of_injective _ DFunLike.coe_injective
  exact ⟨hn, ⟨eL⟩, (B1Red.quasithinGenFitting_eq_of_two_quot (autSec_mono altPre_le Y₁ Y₀) hnormal
    hquasi hsq hO2).symm, hsq⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
