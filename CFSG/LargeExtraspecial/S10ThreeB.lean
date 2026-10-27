module

public import CFSG.LargeExtraspecial.S10TwoC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem cube_of_pow_nine : ∀ γ : Gm, γ ^ 9 = 1 → γ ^ 3 = 1 := by decide +kernel

theorem stab_comm_Γ₁ : ∀ s : Gm, s.2 = 1 → s ^ 3 = 1 → s ≠ 1 → ∀ γ : Gm,
    act γ E00 = E00 → γ * s = s * γ → γ = 1 ∨ γ = τ₂ := by
  decide +kernel

theorem exists_pf_Γ₁Γ₂ : ∀ s₁ s₂ : Gm, s₁.2 = 1 → s₁ ^ 3 = 1 → s₁ ≠ 1 → s₂.1 = 1 →
    s₂ ^ 3 = 1 → s₂ ≠ 1 → ∃ a < 3, ∃ b < 3, pf E00 (act (s₁ ^ a * s₂ ^ b) E00) = 1 := by
  decide +kernel

theorem comm_conj_of_comm {X : Type*} [Group X] {a k l : X} (hak : a * k = k * a)
    (hal : a * l = l * a) : k * l * k⁻¹ * a = a * (k * l * k⁻¹) := by
  have hak' : a * k⁻¹ = k⁻¹ * a := by
    calc a * k⁻¹ = k⁻¹ * (k * a) * k⁻¹ := by group
      _ = k⁻¹ * (a * k) * k⁻¹ := by rw [hak]
      _ = k⁻¹ * a := by group
  calc k * l * k⁻¹ * a = k * l * (k⁻¹ * a) := by group
    _ = k * l * (a * k⁻¹) := by rw [hak']
    _ = k * (l * a) * k⁻¹ := by group
    _ = k * (a * l) * k⁻¹ := by rw [hal]
    _ = (k * a) * l * k⁻¹ := by group
    _ = (a * k) * l * k⁻¹ := by rw [hak]
    _ = a * (k * l * k⁻¹) := by group

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem false_of_Abar_comm (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X)
    {k : Rbar S g t} (hβ : pf E00 (act (F.π k) E00) = 1)
    (hcomm : ∀ a ∈ S.Lbar g ⊓ Nbar S g t, a * k = k * a) : False := by
  obtain ⟨k', hk'⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar k.2)
  have hk'R : S.ρ k' ∈ Rbar S g t := by rw [hk']; exact k.2
  have hkk : (⟨S.ρ k', hk'R⟩ : Rbar S g t) = k := Subtype.ext hk'
  have hβ' : beta X.H X.C X.ht X.ht1 X.hVQ (aV X.ht) (orbV X.haQ X.ht hk'R) = 1 := by
    rw [orbV_eq_resV X, F.beta_eq, F.compat, hkk, F.base]
    exact hβ
  have hR := (timmesfeld_4_7_b hCE X.H X.hNo X.C X.ht X.ht1 X.hVQ (Or.inr X.hΩ) hk'R hβ').1
  apply X.hA
  refine le_antisymm ?_ ((zpowers_le).mpr X.t_mem_Abar)
  rw [← timmesfeld_4_7_c X.H X.C X.ht X.ht1 X.hVQ]
  intro a ha
  refine ⟨mem_centralizer_iff.mpr fun r hr => ?_, ha.1⟩
  rw [SetLike.mem_coe, hR] at hr
  have hle : S.Lbar g ⊔ S.Lbar ((k' : G) * g) ≤ centralizer ({a} : Set S.O) := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · exact mem_centralizer_singleton_iff.mpr (S4.Lbar_comm S X.haQ hz ha.1)
    · rw [Lbar_mul S k'] at hz
      obtain ⟨l, hl, rfl⟩ := hz
      refine mem_centralizer_singleton_iff.mpr ?_
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hak : a * S.ρ k' = S.ρ k' * a := by rw [hk']; exact hcomm a ha
      have hal : a * l = l * a := S4.Lbar_comm S X.haQ ha.1 hl
      exact comm_conj_of_comm hak hal
  exact mem_centralizer_singleton_iff.mp (hle hr)

theorem cube_π_of_odd {X : Hyp10 S g t} (F : Frame X) {H : Subgroup S.O}
    (hodd : Odd (Nat.card H)) {h : S.O} (hh : h ∈ H) (hR : h ∈ Rbar S g t) :
    F.π ⟨h, hR⟩ ^ 3 = 1 := by
  apply cube_of_pow_nine
  have h1 : orderOf (F.π ⟨h, hR⟩) ∣ Nat.card H := by
    refine (orderOf_map_dvd F.π ⟨h, hR⟩).trans ?_
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_dvd_natCard H hh
  have h2 : orderOf (F.π ⟨h, hR⟩) ∣ 36 := by
    rw [← card_Gm]
    exact orderOf_dvd_natCard _
  have hodd' : Odd (orderOf (F.π ⟨h, hR⟩)) := Odd.of_dvd_nat hodd h1
  have h3 : orderOf (F.π ⟨h, hR⟩) ∣ 9 := by
    have hcop : Nat.Coprime (orderOf (F.π ⟨h, hR⟩)) 4 :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd') |>.coprime_dvd_right
        (by norm_num)
    exact hcop.dvd_of_dvd_mul_left (by simpa using h2)
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem eq_one_of_mem_Nbar_of_odd (hCE : CentralExtInput.{u}) (X : Hyp10 S g t)
    {H : Subgroup S.O} (hodd : Odd (Nat.card H)) {z : S.O} (hzH : z ∈ H)
    (hzN : z ∈ Nbar S g t) : z = 1 := by
  obtain ⟨k, hk⟩ := (X.isPGroup_Nbar hCE) ⟨z, hzN⟩
  have hzk : z ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h1 : orderOf z ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hzH
  have h2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
  have hcop : Nat.Coprime (orderOf z) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (Odd.of_dvd_nat hodd h1))
  have := Nat.Coprime.eq_one_of_dvd hcop h2
  exact orderOf_eq_one_iff.mp this

end CFSG.LargeExtraspecial.S10
