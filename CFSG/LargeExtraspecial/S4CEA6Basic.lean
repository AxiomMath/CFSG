module

public import CFSG.LargeExtraspecial.S45QPhi
public import CFSG.LargeExtraspecial.S4CESmallTool
public import CFSG.LargeExtraspecial.S4SevenInput

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module CFSG.LargeExtraspecial.OrthoF2
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
  (exists_symplectic_basis_prescribed_pair)
open scoped commutatorElement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

theorem card_commutator_isometryGroup_four [FiniteDimensional (ZMod 2) V] (hβ : β.IsAlt)
    (hnd : β.Nondegenerate) (h4 : finrank (ZMod 2) V = 4) :
    Nat.card (⁅TauCeti.BilinForm.isometryGroup β, TauCeti.BilinForm.isometryGroup β⁆ :
      Subgroup (V ≃ₗ[ZMod 2] V)) = 360 := by
  obtain ⟨Φ⟩ := S45Q.nonempty_isometryGroup_equiv_perm hβ hnd h4
  obtain ⟨-, -, hrel, -⟩ := S45Q.commutator_isometryGroup_four hβ hnd h4
  have h720 := S45Q.card_self_of_equiv Φ
  have hm := relIndex_mul_card ⁅TauCeti.BilinForm.isometryGroup β,
    TauCeti.BilinForm.isometryGroup β⁆ (TauCeti.BilinForm.isometryGroup β)
  rw [hrel, h720, inf_eq_left.mpr (commutator_le_self _)] at hm
  omega

theorem spRho_mul_self (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) (l : ZMod 2) :
    spRho hβ hcd l * spRho hβ hcd l = 1 := by
  have h0 : β c (d + d) = 0 := by rw [vec_add_self]; exact map_zero (β c)
  rw [spRho_mul hβ hcd hcd l l h0, spRho_congr hβ h0 (map_zero (β c)) rfl (vec_add_self d)
    (by rw [hβ.self_eq_zero, add_zero, zmod2_add_self]), spRho_zero_zero]

theorem spRho_one_mem_of_a6Pair [FiniteDimensional (ZMod 2) V] (hβ : β.IsAlt) {a : V}
    {E₀ : Subgroup (V ≃ₗ[ZMod 2] V)} (hE₀U : E₀ ≤ spPointRadical β a)
    (hcard : Nat.card (spPointRadical β a) = 2 * Nat.card E₀)
    (hτ : spTransvection β hβ a ∉ E₀)
    (hno : ∀ d (hd : β a d = 0), d ∉ (ZMod 2) ∙ a → spRho hβ hd 0 ∉ E₀) {d : V}
    (hd : β a d = 0) (hda : d ∉ (ZMod 2) ∙ a) : spRho hβ hd 1 ∈ E₀ := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  rcases mem_or_mul_mem_of_card hE₀U hcard.le (spTransvection_mem_U hβ a) hτ
    (spRho_mem_spPointRadical hβ hd 0) with h0 | h1
  · exact absurd h0 (hno d hd hda)
  · rwa [← spRho_one_eq] at h1

theorem commutatorElement_spRho (hβ : β.IsAlt) {a u : V} {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.BilinForm.isometryGroup β) (hga : g a = a) (hu : β a u = 0)
    (hgu : β a (g u) = 0) (huu : β a (u + g u) = 0) :
    ⁅spRho hβ hu 1, g⁆ = spRho hβ huu (β u (g u)) := by
  have hconj : g * spRho hβ hu 1 * g⁻¹ = spRho hβ hgu 1 :=
    (conj_spRho hβ hu 1 hg (by rw [hga]; exact hgu)).trans
      (spRho_congr hβ _ hgu hga rfl rfl)
  have hinv : (spRho hβ hgu 1)⁻¹ = spRho hβ hgu 1 :=
    inv_eq_of_mul_eq_one_right (spRho_mul_self hβ hgu 1)
  calc ⁅spRho hβ hu 1, g⁆ = spRho hβ hu 1 * (g * spRho hβ hu 1 * g⁻¹)⁻¹ := by
        rw [commutatorElement_def, mul_inv_rev, mul_inv_rev, inv_inv,
          inv_eq_of_mul_eq_one_right (spRho_mul_self hβ hu 1)]
        group
    _ = spRho hβ huu (β u (g u)) := by
        rw [hconj, hinv, spRho_mul hβ hu hgu 1 1 huu]
        exact spRho_congr hβ _ huu rfl rfl (by rw [zmod2_add_self, zero_add])

theorem sub_mem_span_of_spRho_eq (hβ : β.IsAlt) {a b x x' : V} (hab : β a b = 1)
    (hx : β a x = 0) (hx' : β a x' = 0) {l l' : ZMod 2}
    (heq : spRho hβ hx l = spRho hβ hx' l') : x - x' ∈ (ZMod 2) ∙ a := by
  have e := LinearEquiv.congr_fun heq b
  have hba : β b a = 1 := by rw [isAlt_symm hβ, hab]
  rw [spRho_apply, spRho_apply, hba, one_smul, one_smul, mul_one, mul_one] at e
  rw [Submodule.mem_span_singleton]
  refine ⟨(β b x' + l') - (β b x + l), ?_⟩
  calc ((β b x' + l') - (β b x + l)) • a =
        (b + x' + (β b x' + l') • a) - (b + x + (β b x + l) • a) + (x - x') := by module
    _ = x - x' := by rw [e, sub_self, zero_add]

theorem exists_symplectic_four [FiniteDimensional (ZMod 2) V] (hβ : β.IsAlt)
    (hnd : β.Nondegenerate) (h4 : finrank (ZMod 2) V = 4) {a : V} (ha : a ≠ 0) :
    ∃ b c d : V, β a b = 1 ∧ β c d = 1 ∧ β a c = 0 ∧ β a d = 0 ∧ β b c = 0 ∧ β b d = 0 := by
  obtain ⟨b, hb⟩ : ∃ b, β a b ≠ 0 := by
    by_contra! hc
    exact ha (hnd.1 a hc)
  have hab : β a b = 1 := zmod2_eq_one_of_ne_zero hb
  obtain ⟨m, e, hm, h11, h22, h12, he0, hf0⟩ :=
    exists_symplectic_basis_prescribed_pair
      β hβ hnd a b hab
  obtain rfl : m = 1 := by omega
  refine ⟨b, e (Sum.inl 1), e (Sum.inr 1), hab, by simpa using h12 1 1, ?_, ?_, ?_, ?_⟩
  · rw [← he0]
    exact h11 0 1
  · rw [← he0]
    simpa using h12 0 1
  · rw [← hf0, isAlt_symm hβ]
    simpa using h12 1 0
  · rw [← hf0]
    exact h22 0 1

theorem le_commutator_of_a6Pair [FiniteDimensional (ZMod 2) V] {K : Type*} [Group K]
    {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V} {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (ha : a ≠ 0) (hA : A6Pair X E₀ a) (h : CEHyp π E a X E₀) : E₀ ≤ ⁅E₀, stabIn X a⁆ := by
  obtain ⟨h4, β, hβ, hnd, hX, hE₀U, hcard, hτ, hno⟩ := hA
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  have hE₀4 : Nat.card E₀ = 4 := by
    have h8 := card_spPointRadical hβ hnd ha
    rw [h4] at h8
    omega
  obtain ⟨b, c, d, hab, hcd, hac, had, hbc, hbd⟩ := exists_symplectic_four hβ hnd h4 ha
  have hcb : β c b = 0 := by rw [isAlt_symm hβ, hbc]
  have hdb : β d b = 0 := by rw [isAlt_symm hβ, hbd]
  have hdc : β d c = 1 := by rw [isAlt_symm hβ, hcd]
  have hcc : β c c = 0 := hβ.self_eq_zero c
  have hdd : β d d = 0 := hβ.self_eq_zero d
  have hnot : ∀ x : V, β x b = 0 → (∃ y, β x y ≠ 0) → x ∉ (ZMod 2) ∙ a := by
    rintro x hxb ⟨y, hy⟩ hx
    rcases mem_span_singleton_iff.mp hx with rfl | rfl
    · exact hy (by simp)
    · rw [hab] at hxb
      exact one_ne_zero hxb
  have hc : c ∉ (ZMod 2) ∙ a := hnot c hcb ⟨d, by rw [hcd]; exact one_ne_zero⟩
  have hd : d ∉ (ZMod 2) ∙ a := hnot d hdb ⟨c, by rw [hdc]; exact one_ne_zero⟩
  have hcd' : c + d ∉ (ZMod 2) ∙ a := hnot (c + d)
    (by rw [map_add, LinearMap.add_apply, hcb, hdb, add_zero])
    ⟨c, by rw [map_add, LinearMap.add_apply, hcc, hdc, zero_add]; exact one_ne_zero⟩
  have hne0 : ∀ x : V, x ∉ (ZMod 2) ∙ a → x ≠ 0 := fun x hx h0 =>
    hx (h0 ▸ Submodule.zero_mem _)
  set g := spTransvection β hβ c * spTransvection β hβ d with hg
  have hgSp : g ∈ TauCeti.BilinForm.isometryGroup β :=
    mul_mem (spTransvection_mem_isometryGroup hβ c) (spTransvection_mem_isometryGroup hβ d)
  have hgX : g ∈ X := by
    rw [hX, commutator_isometryGroup_eq hβ hnd]
    exact spTransvection_mul_mem_spDer hβ (hne0 c hc) (hne0 d hd)
  have hτda : spTransvection β hβ d a = a := by
    rw [spTransvection_apply, had, zero_smul, add_zero]
  have hτca : spTransvection β hβ c a = a := by
    rw [spTransvection_apply, hac, zero_smul, add_zero]
  have hga : g a = a := by rw [hg, LinearEquiv.mul_apply, hτda, hτca]
  have hτdc : spTransvection β hβ d c = c + d := by rw [spTransvection_apply, hcd, one_smul]
  have hτccd : spTransvection β hβ c (c + d) = d := by
    rw [spTransvection_apply, map_add, LinearMap.add_apply, hcc, hdc, zero_add, one_smul,
      add_comm c d, add_assoc, vec_add_self, add_zero]
  have hgc : g c = d := by rw [hg, LinearEquiv.mul_apply, hτdc, hτccd]
  have hτdd : spTransvection β hβ d d = d := by
    rw [spTransvection_apply, hdd, zero_smul, add_zero]
  have hτcd : spTransvection β hβ c d = d + c := by rw [spTransvection_apply, hdc, one_smul]
  have hgd : g d = d + c := by rw [hg, LinearEquiv.mul_apply, hτdd, hτcd]
  have hgXa : g ∈ stabIn X a := ⟨hgX, hga⟩
  have hacd : β a (c + d) = 0 := by rw [map_add, hac, had, add_zero]
  have hdcc : d + (d + c) = c := by rw [← add_assoc, vec_add_self, zero_add]
  have hk₁ : ⁅spRho hβ hac 1, g⁆ = spRho hβ hacd 1 := by
    rw [commutatorElement_spRho hβ hgSp hga hac (by rw [hgc]; exact had)
      (by rw [hgc]; exact hacd)]
    exact spRho_congr hβ _ hacd rfl (by rw [hgc]) (by rw [hgc, hcd])
  have hk₂ : ⁅spRho hβ had 1, g⁆ = spRho hβ hac 1 := by
    rw [commutatorElement_spRho hβ hgSp hga had (by rw [hgd, add_comm]; exact hacd)
      (by rw [hgd, hdcc]; exact hac)]
    exact spRho_congr hβ _ hac rfl (by rw [hgd, hdcc])
      (by rw [hgd, map_add, hdd, hdc, zero_add])
  have hm₁ : spRho hβ hacd 1 ∈ ⁅E₀, stabIn X a⁆ := hk₁ ▸ commutator_mem_commutator
    (spRho_one_mem_of_a6Pair hβ hE₀U hcard hτ hno hac hc) hgXa
  have hm₂ : spRho hβ hac 1 ∈ ⁅E₀, stabIn X a⁆ := hk₂ ▸ commutator_mem_commutator
    (spRho_one_mem_of_a6Pair hβ hE₀U hcard hτ hno had hd) hgXa
  have h0 : β a 0 = 0 := map_zero (β a)
  refine h.le_commutator_of_card_eq_four hE₀4 hm₁ hm₂ (fun h1 => hcd' ?_) (fun h1 => hc ?_)
    (fun h12 => hd ?_)
  · have := sub_mem_span_of_spRho_eq hβ hab hacd h0 (h1.trans (spRho_zero_zero hβ a h0).symm)
    rwa [sub_zero] at this
  · have := sub_mem_span_of_spRho_eq hβ hab hac h0 (h1.trans (spRho_zero_zero hβ a h0).symm)
    rwa [sub_zero] at this
  · have := sub_mem_span_of_spRho_eq hβ hab hacd hac h12
    rwa [add_sub_cancel_left] at this

end CFSG.LargeExtraspecial.S4
