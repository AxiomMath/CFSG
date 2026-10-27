module

public import CFSG.LargeExtraspecial.S12InspXOrd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem s12_card_mul_relIndex_of_le {X : Type*} [Group X] {H K : Subgroup X} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  have h1 := (H.subgroupOf K).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h1
  exact h1

theorem card_le_of_twoRank_le {X : Type*} [Group X] [Finite X] {r : ℕ}
    (hr : CFSG.Open.twoRank X ≤ r) (E : Subgroup X) (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤ 2 ^ r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hk2 := CFSG.SectionRank.le_pRank Nat.one_lt_two le_top hE hk
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) (hk2.trans hr)

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem two_pow_dvd_card_Lbar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : 2 ^ (S.width - 1) ∣ Nat.card (S.Lbar g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsElementaryAbelian 2 (S.Lbar g) := S.isElementaryAbelian_Lbar haQ
  have hp : IsPGroup 2 (S.Lbar g) := fun x =>
    ⟨1, Subtype.ext (by simpa using elemPow_eq_one_of_isElementaryAbelian _ x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have h1 := S.card_Lbar_ge haQ hne
  rw [hk] at h1 ⊢
  exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).mp h1)

theorem sixteen_dvd_card_Mbar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 5 ≤ S.width) : 2 ^ 4 ∣ Nat.card S.Mbar :=
  (pow_dvd_pow 2 (by omega : 4 ≤ S.width - 1)).trans
    ((two_pow_dvd_card_Lbar haQ hne).trans (Subgroup.card_dvd_of_le (S.Lbar_le_Mbar g)))

theorem sixteen_dvd_card_Xbar12_mul_card_outer {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 5 ≤ S.width) {t : S.O} (hS : S.S12Standing g t) :
    2 ^ 4 ∣ Nat.card (S.Xbar12 g) * Nat.card (Outer (S.Xbar12 g)) :=
  (sixteen_dvd_card_Mbar haQ hne hn).trans (card_Mbar_dvd_card_Xbar12_mul_card_outer hS)

theorem card_Lbar_le_mul_card_outer {g : G} {t : S.O} (hS : S.S12Standing g t) :
    Nat.card (S.Lbar g) ≤
      Nat.card (S.Xbar12 g ⊓ S.Lbar g : Subgroup S.O) * Nat.card (Outer (S.Xbar12 g)) := by
  have hdvd := card_Mbar_dvd_card_Xbar12_mul_card_outer hS
  have h1 := s12_card_mul_relIndex_of_le (Xbar12_le_Mbar (S := S) (g := g))
  have hX0 : 0 < Nat.card (S.Xbar12 g) := Nat.card_pos
  have hrel : (S.Xbar12 g).relIndex S.Mbar ∣ Nat.card (Outer (S.Xbar12 g)) := by
    rw [← h1] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hX0 hdvd
  have hO0 : 0 < Nat.card (Outer (S.Xbar12 g)) := Nat.card_pos
  have hM0 : (S.Xbar12 g).relIndex S.Mbar ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at h1
    exact absurd h1.symm Nat.card_pos.ne'
  have h2 := s12_card_mul_relIndex_of_le (inf_le_right : S.Xbar12 g ⊓ S.Lbar g ≤ S.Lbar g)
  rw [Subgroup.inf_relIndex_right] at h2
  have h3 : (S.Xbar12 g).relIndex (S.Lbar g) ≤ (S.Xbar12 g).relIndex S.Mbar :=
    Subgroup.relIndex_le_of_le_right (S.Lbar_le_Mbar g) hM0
  rw [← h2]
  exact Nat.mul_le_mul_left _ (h3.trans (Nat.le_of_dvd hO0 hrel))

theorem card_inf_Lbar_le_of_forall {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {r : ℕ}
    (h : ∀ E : Subgroup (S.Xbar12 g), CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 2 ^ r) :
    Nat.card (S.Xbar12 g ⊓ S.Lbar g : Subgroup S.O) ≤ 2 ^ r := by
  have hEA : IsElementaryAbelian 2 (S.Lbar g) := S.isElementaryAbelian_Lbar haQ
  set E : Subgroup (S.Xbar12 g) := (S.Lbar g).subgroupOf (S.Xbar12 g) with hE
  have hEcard : Nat.card E = Nat.card (S.Xbar12 g ⊓ S.Lbar g : Subgroup S.O) := by
    rw [hE, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm]
  have hElem : CFSG.Open.IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have := congrArg Subtype.val
        (hEA.is_comm.comm ⟨((a : S.Xbar12 g) : S.O), a.2⟩ ⟨((b : S.Xbar12 g) : S.O), b.2⟩)
      simpa using this
    · simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := S.Lbar g) _ hx
  rw [← hEcard]
  exact h E hElem

theorem false_of_elemAbelian_le_four {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 5 ≤ S.width) {t : S.O} (hS : S.S12Standing g t)
    (h : ∀ E : Subgroup (S.Xbar12 g), CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 2 ^ 2)
    (hO : Nat.card (Outer (S.Xbar12 g)) ≤ 2) : False := by
  have h1 := card_Lbar_le_mul_card_outer hS
  have h2 := card_inf_Lbar_le_of_forall haQ h
  have h3 := S.card_Lbar_ge haQ hne
  have h4 : 2 ^ 4 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : Nat.card (S.Xbar12 g ⊓ S.Lbar g : Subgroup S.O) * Nat.card (Outer (S.Xbar12 g)) ≤
      2 ^ 2 * 2 := Nat.mul_le_mul h2 hO
  omega

theorem false_of_twoRank_le_two {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 5 ≤ S.width) {t : S.O} (hS : S.S12Standing g t)
    (hr : CFSG.Open.twoRank (S.Xbar12 g) ≤ 2) (hO : Nat.card (Outer (S.Xbar12 g)) ≤ 2) :
    False :=
  false_of_elemAbelian_le_four haQ hne hn hS (card_le_of_twoRank_le hr) hO

theorem finrank_le_width_of_isotropic {U : Submodule (ZMod 2) S.Qt}
    (hU : ∀ a ∈ U, ∀ b ∈ U, polar S.q a b = 0) : finrank (ZMod 2) U ≤ S.width := by
  have hle : U ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin U := fun b hb =>
    (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun a ha => by
      show S.q.polarBilin a b = 0
      rw [polarBilin_apply_apply]
      exact hU a ha b hb
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate, S.finrank_Qt_eq_two_mul_width]
    at h1
  omega

theorem polar_eq_zero_sup_left {U₁ U₂ W : Submodule (ZMod 2) S.Qt}
    (h₁ : ∀ a ∈ U₁, ∀ b ∈ W, polar S.q a b = 0) (h₂ : ∀ a ∈ U₂, ∀ b ∈ W, polar S.q a b = 0) :
    ∀ a ∈ U₁ ⊔ U₂, ∀ b ∈ W, polar S.q a b = 0 := by
  intro a ha b hb
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp ha
  rw [polar_add_left, h₁ a₁ ha₁ b hb, h₂ a₂ ha₂ b hb, add_zero]

theorem polar_eq_zero_symm {U W : Submodule (ZMod 2) S.Qt}
    (h : ∀ a ∈ U, ∀ b ∈ W, polar S.q a b = 0) : ∀ a ∈ W, ∀ b ∈ U, polar S.q a b = 0 :=
  fun a ha b hb => by rw [polar_comm]; exact h b hb a ha

theorem polar_eq_zero_commSpace {α : S.Qt ≃ₗ[ZMod 2] S.Qt} (hα : IsTypeA S.q α 2) :
    ∀ a ∈ commSpace α, ∀ b ∈ commSpace α, polar S.q a b = 0 := by
  intro a ha b hb
  rw [polar, hα.2.2.2.2 _ ((commSpace α).add_mem ha hb), hα.2.2.2.2 a ha, hα.2.2.2.2 b hb,
    sub_zero, sub_zero]

theorem finrank_sup_le_three {α β : S.Qt ≃ₗ[ZMod 2] S.Qt} (hα : IsTypeA S.q α 2)
    (hβ : IsTypeA S.q β 2) (h : commSpace α ⊓ commSpace β ≠ ⊥) :
    finrank (ZMod 2) (commSpace α ⊔ commSpace β : Submodule (ZMod 2) S.Qt) ≤ 3 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (commSpace α) (commSpace β)
  have h2 : 0 < finrank (ZMod 2) (commSpace α ⊓ commSpace β : Submodule (ZMod 2) S.Qt) :=
    Nat.pos_of_ne_zero fun h0 => h (Submodule.finrank_eq_zero.mp h0)
  rw [hα.2.2.2.1, hβ.2.2.2.1] at h1
  omega

theorem finrank_sup_three_le_width (hn : 5 ≤ S.width) {α β γ : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hα : IsTypeA S.q α 2) (hβ : IsTypeA S.q β 2) (hγ : IsTypeA S.q γ 2)
    (hαβ : α * β = β * α) (hαγ : α * γ = γ * α) (hβγ : β * γ = γ * β) :
    finrank (ZMod 2) (commSpace α ⊔ commSpace β ⊔ commSpace γ : Submodule (ZMod 2) S.Qt) ≤
      S.width := by
  have hq := S.q_nondegenerate
  have hC := hγ.2.2.2.1
  have hB := hβ.2.2.2.1
  have hA := hα.2.2.2.1
  rcases (commute_iff_of_isTypeA hq hα hβ).mp hαβ with h1 | h1
  · have h3 := finrank_sup_le_three hα hβ h1
    have h4 := Submodule.finrank_add_le_finrank_add_finrank (commSpace α ⊔ commSpace β)
      (commSpace γ)
    omega
  rcases (commute_iff_of_isTypeA hq hα hγ).mp hαγ with h2 | h2
  · have h3 := finrank_sup_le_three hα hγ h2
    have e : commSpace α ⊔ commSpace β ⊔ commSpace γ =
        commSpace α ⊔ commSpace γ ⊔ commSpace β := by
      rw [sup_assoc, sup_comm (commSpace β), ← sup_assoc]
    rw [e]
    have h4 := Submodule.finrank_add_le_finrank_add_finrank (commSpace α ⊔ commSpace γ)
      (commSpace β)
    omega
  rcases (commute_iff_of_isTypeA hq hβ hγ).mp hβγ with h3 | h3
  · have h5 := finrank_sup_le_three hβ hγ h3
    rw [sup_assoc]
    have h4 := Submodule.finrank_add_le_finrank_add_finrank (commSpace α)
      (commSpace β ⊔ commSpace γ)
    omega
  refine finrank_le_width_of_isotropic ?_
  have hA' := polar_eq_zero_symm (polar_eq_zero_sup_left (polar_eq_zero_sup_left
    (polar_eq_zero_commSpace hα) (polar_eq_zero_symm h1)) (polar_eq_zero_symm h2))
  have hB' := polar_eq_zero_symm (polar_eq_zero_sup_left (polar_eq_zero_sup_left h1
    (polar_eq_zero_commSpace hβ)) (polar_eq_zero_symm h3))
  have hC' := polar_eq_zero_symm (polar_eq_zero_sup_left (polar_eq_zero_sup_left h2 h3)
    (polar_eq_zero_commSpace hγ))
  exact polar_eq_zero_sup_left (polar_eq_zero_sup_left hA' hB') hC'

theorem commSub12_mono {H K : Subgroup S.O} (h : H ≤ K) : S.commSub12 H ≤ S.commSub12 K :=
  Submodule.span_mono fun _ ⟨x, hx, w, hw⟩ => ⟨x, h hx, w, hw⟩

end Setting

end CFSG.LargeExtraspecial
