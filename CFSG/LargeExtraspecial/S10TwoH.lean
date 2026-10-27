module

public import CFSG.LargeExtraspecial.S7Perm
public import CFSG.LargeExtraspecial.S10ModelD
public import CFSG.LargeExtraspecial.S10TwoE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

@[expose] noncomputable def Ybar (y d : S.O) : Subgroup S.O := zpowers y ⊔ zpowers d

theorem zpowers_le_normalizer_of_inv {X : Type*} [Group X] {y d : X}
    (hyd : y * d * y⁻¹ = d⁻¹) : zpowers y ≤ normalizer (zpowers d : Set X) := by
  have hmap : (zpowers d).map (MulAut.conj y).toMonoidHom = zpowers d := by
    rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hyd, zpowers_inv]
  rw [zpowers_le, mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [← hmap]
    exact ⟨z, hz, rfl⟩
  · intro hz
    rw [← hmap] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwz
    have : w = z := by
      have := congrArg (fun u => y⁻¹ * u * y) hwz
      simpa [mul_assoc] using this
    rw [← this]
    exact hw

section Ybar

variable (X : Hyp10 S g t) (F : Frame X) {y : S.O} (hyL : y ∈ S.Lbar g)
  (hπy : F.π ⟨y, Lbar_le_Rbar X.ht hyL⟩ = τ₂) {d : Rbar S g t} (hd3 : d ^ 3 = 1)
  (hd1 : (F.π d).1 = 1) (hdne : F.π d ≠ 1) (hπd3 : F.π d ^ 3 = 1)
  (hyd : y * (d : S.O) * y⁻¹ = (d : S.O)⁻¹)

include hyL hπy in
theorem orderOf_y_eq_two : orderOf y = 2 := by
  refine orderOf_eq_prime (by rw [_root_.sq]; exact S4.mul_self_of_mem_Lbar S X.haQ hyL) ?_
  rintro rfl
  have : (⟨1, Lbar_le_Rbar X.ht hyL⟩ : Rbar S g t) = 1 := rfl
  rw [this, map_one] at hπy
  exact τ₂_ne_one hπy.symm

include hd3 hdne in
theorem orderOf_d_eq_three : orderOf (d : S.O) = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · exact congrArg Subtype.val hd3
  · intro h1
    apply hdne
    have : d = 1 := Subtype.ext h1
    rw [this, map_one]

include hyL hπy hd3 hdne hyd in
theorem card_Ybar : Nat.card (Ybar y (d : S.O)) = 6 := by
  have h1 := card_sup_mul_card_inf (zpowers_le_normalizer_of_inv hyd)
  have hy2 := orderOf_y_eq_two X F hyL hπy
  have hd3' := orderOf_d_eq_three X F hd3 hdne
  have hbot : zpowers y ⊓ zpowers (d : S.O) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h2 : orderOf z ∣ orderOf y := orderOf_dvd_of_mem_zpowers hz.1
    have h3 : orderOf z ∣ orderOf (d : S.O) := orderOf_dvd_of_mem_zpowers hz.2
    rw [hy2] at h2
    rw [hd3'] at h3
    have : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h2 h3
    exact orderOf_eq_one_iff.mp this
  rw [hbot, card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hy2, hd3'] at h1
  rw [Ybar]
  exact h1

include hyL hπy hd1 in
theorem Ybar_le_pre_Γ₂ : Ybar y (d : S.O) ≤ F.pre Γ₂ := by
  refine sup_le ((zpowers_le).mpr ((F.mem_pre).mpr ⟨Lbar_le_Rbar X.ht hyL, ?_⟩))
    ((zpowers_le).mpr ((F.mem_pre).mpr ⟨d.2, ?_⟩))
  · rw [hπy]; exact τ₂_mem_Γ₂
  · rw [Subtype.coe_eta, mem_Γ₂]; exact hd1

include hyL hπy hd1 hdne hπd3 in
theorem exists_mem_Ybar_of_Γ₂ {γ : Gm} (hγ : γ.1 = 1) :
    ∃ z : Rbar S g t, (z : S.O) ∈ Ybar y (d : S.O) ∧ F.π z = γ := by
  obtain ⟨i, -, j, -, hij⟩ := Γ₂_gen (F.π d) hd1 hπd3 hdne γ hγ
  refine ⟨⟨y, Lbar_le_Rbar X.ht hyL⟩ ^ j * d ^ i, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
    exact mul_mem (pow_mem (Subgroup.mem_sup_left (mem_zpowers y)) j)
      (pow_mem (Subgroup.mem_sup_right (mem_zpowers (d : S.O))) i)
  · rw [map_mul, map_pow, map_pow, hπy, hij]

include hyL hπy hd3 hd1 hdne hπd3 hyd in
theorem eq_one_of_mem_Ybar_of_mem_Nbar {z : S.O} (hzY : z ∈ Ybar y (d : S.O))
    (hzN : z ∈ Nbar S g t) : z = 1 := by
  have hYR : Ybar y (d : S.O) ≤ Rbar S g t := (Ybar_le_pre_Γ₂ X F hyL hπy hd1).trans
    (F.pre_le_Rbar Γ₂)
  set πY : Ybar y (d : S.O) →* Gm := F.π.comp (Subgroup.inclusion hYR) with hπY
  have hrange : Γ₂ ≤ πY.range := by
    intro γ hγ
    obtain ⟨w, hwY, hwπ⟩ := exists_mem_Ybar_of_Γ₂ X F hyL hπy hd1 hdne hπd3 (mem_Γ₂.mp hγ)
    exact ⟨⟨w, hwY⟩, hwπ⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup πY.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange πY).toEquiv,
    card_Ybar X F hyL hπy hd3 hdne hyd] at h1
  have h2 := Subgroup.card_le_of_le hrange
  rw [card_Γ₂] at h2
  have hker : Nat.card πY.ker = 1 := by
    have hpos : 0 < Nat.card πY.ker := Nat.card_pos
    have hle : Nat.card πY.range ≤ 6 := by
      rw [h1]
      exact Nat.le_mul_of_pos_right _ hpos
    have : Nat.card πY.range = 6 := le_antisymm hle h2
    rw [this] at h1
    omega
  have hmem : (⟨z, hzY⟩ : Ybar y (d : S.O)) ∈ πY.ker := by
    rw [MonoidHom.mem_ker, hπY, MonoidHom.comp_apply]
    exact (F.ker _).mpr hzN
  rw [Subgroup.card_eq_one] at hker
  rw [hker] at hmem
  exact congrArg Subtype.val ((Subgroup.mem_bot).mp hmem)

include hyL hπy hd3 hd1 hdne hπd3 hyd in
theorem inf_Ybar_eq_bot : F.pre Γ₁ ⊓ Ybar y (d : S.O) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  obtain ⟨hzR, hzπ1⟩ := (F.mem_pre).mp hz1
  obtain ⟨hzR', hzπ2⟩ := (F.mem_pre).mp (Ybar_le_pre_Γ₂ X F hyL hπy hd1 hz2)
  have h1 : F.π ⟨z, hzR⟩ = 1 :=
    eq_one_of_mem_Γ₁_of_mem_Γ₂ (mem_Γ₁.mp hzπ1) (mem_Γ₂.mp hzπ2)
  exact (Subgroup.mem_bot).mpr
    (eq_one_of_mem_Ybar_of_mem_Nbar X F hyL hπy hd3 hd1 hdne hπd3 hyd hz2 ((F.ker _).mp h1))

include hyL hπy hd1 hdne hπd3 in
theorem sup_Ybar_eq : F.pre Γ₁ ⊔ Ybar y (d : S.O) = Rbar S g t := by
  refine le_antisymm (sup_le (F.pre_le_Rbar Γ₁)
    ((Ybar_le_pre_Γ₂ X F hyL hπy hd1).trans (F.pre_le_Rbar Γ₂))) fun r hr => ?_
  obtain ⟨w, hwY, hwπ⟩ := exists_mem_Ybar_of_Γ₂ X F hyL hπy hd1 hdne hπd3
    (γ := (1, (F.π ⟨r, hr⟩).2)) rfl
  have h1 : r * (w : S.O)⁻¹ ∈ F.pre Γ₁ := by
    refine (F.mem_pre).mpr ⟨mul_mem hr (inv_mem w.2), ?_⟩
    have e : (⟨r * (w : S.O)⁻¹, mul_mem hr (inv_mem w.2)⟩ : Rbar S g t) = ⟨r, hr⟩ * w⁻¹ :=
      Subtype.ext (by simp)
    rw [e, map_mul, map_inv, hwπ, mem_Γ₁]
    simp
  have e2 : r = (r * (w : S.O)⁻¹) * (w : S.O) := by group
  rw [e2]
  exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hwY)

theorem commute_of_mem_Ybar {R0 : Subgroup S.O} (hy : ∀ r ∈ R0, Commute r y)
    (hd : ∀ r ∈ R0, Commute r (d : S.O)) {a : S.O} (ha : a ∈ R0) {b : S.O}
    (hb : b ∈ Ybar y (d : S.O)) : Commute a b := by
  have hle : Ybar y (d : S.O) ≤ centralizer ({a} : Set S.O) :=
    sup_le ((zpowers_le).mpr (mem_centralizer_singleton_iff.mpr (hy a ha).symm))
      ((zpowers_le).mpr (mem_centralizer_singleton_iff.mpr (hd a ha).symm))
  exact (mem_centralizer_singleton_iff.mp (hle hb)).symm

include hyL hπy hd3 hd1 hdne hπd3 hyd in
theorem nonempty_Ybar_mulEquiv : Nonempty (Ybar y (d : S.O) ≃* Equiv.Perm (Fin 3)) := by
  have hyY : y ∈ Ybar y (d : S.O) := Subgroup.mem_sup_left (mem_zpowers y)
  have hdY : (d : S.O) ∈ Ybar y (d : S.O) := Subgroup.mem_sup_right (mem_zpowers _)
  refine S7.nonempty_mulEquiv_perm_three (card_Ybar X F hyL hπy hd3 hdne hyd)
    (T := (zpowers y).subgroupOf (Ybar y (d : S.O))) ?_ ?_
  · have hle : zpowers y ≤ Ybar y (d : S.O) := le_sup_left
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers,
      orderOf_y_eq_two X F hyL hπy]
  · intro hn
    have hmem := hn.conj_mem ⟨y, hyY⟩ (Subgroup.mem_subgroupOf.mpr (mem_zpowers y)) ⟨_, hdY⟩
    rw [Subgroup.mem_subgroupOf] at hmem
    have hy2 := orderOf_y_eq_two X F hyL hπy
    rcases mem_zpowers_of_orderOf_two hy2 hmem with h1 | h1
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      have : y = 1 := by
        have := congrArg (fun u => (d : S.O)⁻¹ * u * (d : S.O)) h1
        simpa [mul_assoc] using this
      rw [this, orderOf_one] at hy2
      exact absurd hy2 (by norm_num)
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      have hc : F.π (d * ⟨y, Lbar_le_Rbar X.ht hyL⟩ * d⁻¹) = F.π ⟨y, Lbar_le_Rbar X.ht hyL⟩ :=
        congrArg F.π (Subtype.ext (by simpa using h1))
      rw [map_mul, map_mul, map_inv, hπy] at hc
      exact conj_τ₂_ne _ hd1 hπd3 hdne hc

end Ybar

end CFSG.LargeExtraspecial.S10
