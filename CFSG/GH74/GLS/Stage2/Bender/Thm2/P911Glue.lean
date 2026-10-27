module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Inner

variable {Y : Type} [Group Y]

theorem conj_range_normal : ((MulAut.conj : Y →* MulAut Y).range).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨g, rfl⟩ φ
  refine ⟨φ g, ?_⟩
  ext x
  simp [MulAut.conj_apply]

theorem center_eq_bot_of_simple (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a) :
    Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center Y := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem conj_injective_of_center_eq_bot (hc : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  intro a b hab
  have h : ∀ x : Y, a * x * a⁻¹ = b * x * b⁻¹ := fun x => by
    have := congrArg (fun φ : MulAut Y => φ x) hab
    simpa [MulAut.conj_apply] using this
  have hmem : b⁻¹ * a ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := h (x * b⁻¹ * a)
    have h2 := h x
    calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * a := by group
      _ = b⁻¹ * (a * x * a⁻¹) * a := by rw [← h2]
      _ = b⁻¹ * a * x := by group
  rw [hc] at hmem
  have : b⁻¹ * a = 1 := Subgroup.mem_bot.mp hmem
  exact (inv_mul_eq_one.mp this).symm

theorem eq_one_of_commute_conj (hc : Subgroup.center Y = ⊥) {φ : MulAut Y}
    (h : ∀ g : Y, φ * MulAut.conj g = MulAut.conj g * φ) : φ = 1 := by
  ext x
  have h1 : MulAut.conj (φ x) = MulAut.conj x := by
    have := h x
    ext y
    have h3 := congrArg (fun ψ : MulAut Y => ψ (φ⁻¹ y)) this
    simpa [MulAut.conj_apply] using h3
  have := conj_injective_of_center_eq_bot hc h1
  simpa using this

end Inner

section Main

theorem no911_of_oddCore {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a)
    (hY : ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X) [S.Normal], Nonempty (S ≃* Y) →
      centralizer (S : Set X) = ⊥ → ∀ t : X, orderOf t = 2 →
        CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥) :
    No911 Y := by
  rintro p V z ⟨hp, hpodd, hVe, hVc, hz1, hzz, hVz, ⟨O, hOH, hVO, hOodd, hOz, hON⟩, -⟩
  have hc : Subgroup.center Y = ⊥ := center_eq_bot_of_simple hs hna
  have hinn : (MulAut.conj : Y →* MulAut Y).range ≤ hbar Y V z := le_trans le_sup_left le_sup_left
  have hzH : z ∈ hbar Y V z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have : ((MulAut.conj : Y →* MulAut Y).range).Normal := conj_range_normal
  let S : Subgroup ↥(hbar Y V z) := (MulAut.conj : Y →* MulAut Y).range.subgroupOf (hbar Y V z)
  have : S.Normal := Subgroup.Normal.subgroupOf inferInstance _
  let e : S ≃* Y := (Subgroup.subgroupOfEquivOfLe hinn).trans
    (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hc)).symm
  have hC : centralizer (S : Set ↥(hbar Y V z)) = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    rw [Subgroup.mem_centralizer_iff] at hφ
    refine Subgroup.mem_bot.mpr (Subtype.ext (eq_one_of_commute_conj hc fun g => ?_))
    have hs' : (⟨MulAut.conj g, hinn ⟨g, rfl⟩⟩ : ↥(hbar Y V z)) ∈ S :=
      Subgroup.mem_subgroupOf.mpr ⟨g, rfl⟩
    have := hφ _ hs'
    exact (congrArg Subtype.val this).symm
  let t : ↥(hbar Y V z) := ⟨z, hzH⟩
  have ht : orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have hodd := hY ↥(hbar Y V z) S ⟨e⟩ hC t ht
  let OX : Subgroup ↥(hbar Y V z) := O.subgroupOf (hbar Y V z)
  let C : Subgroup ↥(hbar Y V z) := centralizer ({t} : Set ↥(hbar Y V z))
  have hOXC : OX ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact hOz _ (Subgroup.mem_subgroupOf.mp hx)
  let OC : Subgroup ↥C := OX.subgroupOf C
  have hnorm : OC.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgC := g.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hgC
    have hgz : ((g : ↥(hbar Y V z)) : MulAut Y) * z = z * ((g : ↥(hbar Y V z)) : MulAut Y) :=
      congrArg Subtype.val hgC
    exact hON _ (g : ↥(hbar Y V z)).2 hgz _ hn
  have hcard : Nat.card ↥OC = Nat.card ↥O := by
    refine (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOXC).toEquiv).trans ?_
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv
  have hle : OC ≤ CFSG.oddCore ↥C :=
    CFSG.ABGLocalTools.le_oddCore_of_normal hnorm (hcard ▸ hOodd)
  have hbot : OC = ⊥ := by
    rw [hodd] at hle
    exact le_bot_iff.mp hle
  have h1 : Nat.card ↥O = 1 := by
    rw [← hcard, hbot]
    exact Subgroup.card_bot
  have hVbot : Nat.card ↥V = 1 := by
    have hdvd : Nat.card ↥V ∣ Nat.card ↥O := Subgroup.card_dvd_of_le hVO
    rw [h1] at hdvd
    exact Nat.dvd_one.mp hdvd
  rw [hVc] at hVbot
  have : p = 1 := by
    have := (Nat.pow_eq_one.mp hVbot)
    rcases this with h | h
    · exact h
    · omega
  exact hp.one_lt.ne' this

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
