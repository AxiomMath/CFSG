module

public import CFSG.LargeExtraspecial.S4CEA6Basic
public import CFSG.LargeExtraspecial.S4CESmallThree

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module CFSG.LargeExtraspecial.OrthoF2
open scoped commutatorElement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem ker_eq_bot_or_card_eq_three_of_a6Pair {K : Type*} [Group K] [Finite K]
    {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V} {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (ha : a ≠ 0) (hA : A6Pair X E₀ a) (h : CEHyp π E a X E₀) :
    π.ker = ⊥ ∨ Nat.card π.ker = 3 := by
  have hperf := le_commutator_of_a6Pair ha hA h
  obtain ⟨h4, β, hβ, hnd, hX, hE₀U, hcard, hτ, hno⟩ := hA
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  have hXcard : Nat.card X = 360 := by
    rw [hX]
    exact card_commutator_isometryGroup_four hβ hnd h4
  have hE₀4 : Nat.card E₀ = 4 := by
    have h8 := card_spPointRadical hβ hnd ha
    rw [h4] at h8
    omega
  obtain ⟨b, c, d, hab, hcd, hac, had, hbc, hbd⟩ := exists_symplectic_four hβ hnd h4 ha
  have hca : β c a = 0 := by rw [isAlt_symm hβ, hac]
  have hda : β d a = 0 := by rw [isAlt_symm hβ, had]
  have hdc : β d c = 1 := by rw [isAlt_symm hβ, hcd]
  have hba : β b a = 1 := by rw [isAlt_symm hβ, hab]
  have hdb : β d b = 0 := by rw [isAlt_symm hβ, hbd]
  have hcb : β c b = 0 := by rw [isAlt_symm hβ, hbc]
  have haa := hβ.self_eq_zero a
  have hbb := hβ.self_eq_zero b
  have hcc := hβ.self_eq_zero c
  have hdd := hβ.self_eq_zero d
  have hc0 : c ≠ 0 := fun h0 => by rw [h0, map_zero, LinearMap.zero_apply] at hcd; simp at hcd
  have hcna : c ∉ (ZMod 2) ∙ a := by
    intro hmem
    rcases mem_span_singleton_iff.mp hmem with h0 | h1
    · exact hc0 h0
    · rw [h1, hab] at hcb
      exact one_ne_zero hcb
  set u := b + c + d with hu
  set w := a + b + d with hw
  have hau : β a u = 1 := by
    rw [hu, map_add, map_add, hab, hac, had]
    decide
  have haw : β a w = 1 := by
    rw [hw, map_add, map_add, haa, hab, had]
    decide
  have hu0 : u ≠ 0 := fun h0 => by rw [h0, map_zero] at hau; exact zero_ne_one hau
  have hw0 : w ≠ 0 := fun h0 => by rw [h0, map_zero] at haw; exact zero_ne_one haw
  set g := spTransvection β hβ u * spTransvection β hβ w with hg
  have hgSp : g ∈ TauCeti.BilinForm.isometryGroup β :=
    mul_mem (spTransvection_mem_isometryGroup hβ u) (spTransvection_mem_isometryGroup hβ w)
  have hgX : g ∈ X := by
    rw [hX, commutator_isometryGroup_eq hβ hnd]
    exact spTransvection_mul_mem_spDer hβ hu0 hw0
  have hga : g a = c := by
    have e1 : spTransvection β hβ w a = b + d := by
      rw [spTransvection_apply, haw, one_smul, hw, ← add_assoc, ← add_assoc, vec_add_self,
        zero_add]
    have e2 : β (b + d) u = 1 := by
      simp only [hu, map_add, LinearMap.add_apply, hbb, hbc, hbd, hdb, hdc, hdd]
      decide
    rw [hg, LinearEquiv.mul_apply, e1, spTransvection_apply, e2, one_smul, hu]
    rw [show b + d + (b + c + d) = c + (b + b) + (d + d) by abel, vec_add_self, vec_add_self,
      add_zero, add_zero]
  obtain ⟨k, hk⟩ : g ∈ π.range := h.range_eq ▸ hgX
  have hka : π k a = c := by rw [hk, hga]
  have hp : ∃ k, π k a = c := ⟨k, hka⟩
  set t := spRho hβ hca 1 with ht
  have htE : t ∈ (Ept π E a c).map π := by
    rw [h.map_Ept hka, hk]
    have hgi : g⁻¹ ∈ TauCeti.BilinForm.isometryGroup β := inv_mem hgSp
    have hiso := TauCeti.BilinForm.mem_isometryGroup_iff.mp hgi
    have hgc : g⁻¹ c = a := by rw [← hga]; exact inv_apply_self' g a
    have hca' : β (g⁻¹ c) (g⁻¹ a) = 0 := by rw [hiso, hca]
    have ha' : β a (g⁻¹ a) = 0 := by
      have e := hca'
      rw [hgc] at e
      exact e
    refine ⟨g⁻¹ * t * g⁻¹⁻¹, ?_, by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩
    rw [ht, conj_spRho hβ hca 1 hgi hca', spRho_congr hβ hca' ha' hgc rfl rfl]
    refine spRho_one_mem_of_a6Pair hβ hE₀U hcard hτ hno ha' fun hmem => ?_
    rcases mem_span_singleton_iff.mp hmem with h0 | h1
    · apply ha
      rw [← apply_inv_self' g a, h0, map_zero]
    · apply hcna
      have hgaa : g a = a := by
        conv_lhs => rw [← h1]
        exact apply_inv_self' g a
      rw [← hga, hgaa]
      exact Submodule.mem_span_singleton_self a
  obtain ⟨htlE, htl⟩ := liftPt_spec htE
  set tl := liftPt π E a c t with htldef
  have htltl : tl * tl = 1 := h.eq_one_of_mem_Ept hp (mul_mem htlE htlE) (by
    rw [map_mul, htl, ht, spRho_mul_self])
  have hta : t a = a := by
    rw [ht, spRho_apply, haa, hac]
    simp
  have htlN : tl ∈ normalizer (E : Set K) := h.le_normalizer tl (by rw [htl, hta])
  have htE₀ : t ∉ E₀ := by
    intro htE₀
    have hmem := (hE₀U htE₀).2.2.1 d had
    have htd : t d - d = a + c := by
      rw [ht, spRho_apply, hdc, hda, one_smul, one_mul, zero_add, one_smul, add_assoc,
        add_sub_cancel_left]
    rw [htd] at hmem
    apply hcna
    have := Submodule.sub_mem _ hmem (Submodule.mem_span_singleton_self a)
    rwa [add_sub_cancel_left] at this
  set U := E ⊔ zpowers tl with hU
  have hUle : Nat.card U ≤ 8 := by
    refine (card_sup_le_of_le_normalizer (zpowers_le.mpr htlN)).trans ?_
    rw [h.card_E_eq, hE₀4, Nat.card_zpowers]
    have : orderOf tl ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two, htltl])
    omega
  have hE₀πU : E₀ ≤ U.map π := h.map_eq ▸ map_mono le_sup_left
  have htπU : t ∈ U.map π := ⟨tl, mem_sup_right (mem_zpowers tl), htl⟩
  have hπU8 : Nat.card (U.map π) = 8 := by
    have h1 : Nat.card (U.map π) ≤ 8 :=
      (Nat.le_of_dvd Nat.card_pos (U.card_map_dvd π)).trans hUle
    have h2 : 4 ∣ Nat.card (U.map π) := hE₀4 ▸ card_dvd_of_le hE₀πU
    have h3 : 4 < Nat.card (U.map π) := hE₀4 ▸ card_lt_of_lt
      (lt_of_le_of_ne hE₀πU fun he => htE₀ (he ▸ htπU))
    omega
  have hUZ : U ⊓ π.ker = ⊥ := inf_ker_eq_bot_of_card_le π (hUle.trans hπU8.ge)
  have hU8 : Nat.card U = 8 :=
    le_antisymm hUle (hπU8 ▸ Nat.le_of_dvd Nat.card_pos (U.card_map_dvd π))
  have hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 2 ∣ Nat.card X := by
    intro p hp hp2 hp3 hdvd
    rw [hXcard] at hdvd
    have hle : p ^ 2 ≤ 360 := Nat.le_of_dvd (by norm_num) hdvd
    have hp19 : p < 19 := by nlinarith
    interval_cases p <;> revert hp hp2 hp3 hdvd <;> norm_num
  rcases h.card_ker_eq_one_or_three hperf hUZ (m := 45) ⟨22, rfl⟩ (by rw [hXcard, hU8]) hsq
      (by rw [hXcard]; norm_num) with h1 | h3
  · exact Or.inl (card_eq_one.mp h1)
  · exact Or.inr h3

end CFSG.LargeExtraspecial.S4
