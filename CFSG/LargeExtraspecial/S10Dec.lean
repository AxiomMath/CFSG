module

public import CFSG.LargeExtraspecial.S10ModelD
public import CFSG.LargeExtraspecial.S10TwoC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem exists_mul_of_mem_sup_of_commute {X : Type*} [Group X] {A B : Subgroup X}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : X} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup X :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  exact hle hx

theorem involution_cases : ∀ e : Gm, e * e = 1 → e ≠ 1 → ∃ δ : Gm,
    e = δ * τ₁ * δ⁻¹ ∨ e = δ * τ₂ * δ⁻¹ ∨ e = δ * (τ₁ * τ₂) * δ⁻¹ := by
  decide +kernel

theorem card_cube_set : (Finset.univ.filter fun s : Gm => s ^ 3 = 1).card = 9 := by
  decide +kernel

theorem normal_card_six {N : Subgroup Gm} (hN : ∀ δ : Gm, ∀ n ∈ N, δ * n * δ⁻¹ ∈ N)
    (h6 : Nat.card N = 6) : N = Γ₁ ∨ N = Γ₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 (by rw [h6]; norm_num)
  have he2 : (e : Gm) * e = 1 := by
    have := pow_orderOf_eq_one (e : Gm)
    rwa [Subgroup.orderOf_coe, he, _root_.sq] at this
  have he1 : (e : Gm) ≠ 1 := by
    intro h1
    have : orderOf (e : Gm) = 1 := by rw [h1, orderOf_one]
    rw [Subgroup.orderOf_coe, he] at this
    exact absurd this (by norm_num)
  have hconjN : ∀ {x : Gm} (δ : Gm), x = δ * (e : Gm) * δ⁻¹ → δ⁻¹ * x * δ ∈ N := by
    intro x δ hx
    have := hN δ⁻¹ x (by rw [hx]; exact hN δ _ e.2)
    simpa using this
  obtain ⟨δ, hδ | hδ | hδ⟩ := involution_cases _ he2 he1
  · left
    have hτ : τ₁ ∈ N := by
      have := hN δ⁻¹ _ e.2
      rw [hδ] at this
      simpa [mul_assoc] using this
    have hle : Γ₁ ≤ N := by
      intro γ hγ
      obtain ⟨δ₁, δ₂, h1 | h2⟩ := Γ₁_closure γ (mem_Γ₁.mp hγ)
      · rw [h1]; exact hN _ _ hτ
      · rw [h2]; exact mul_mem (hN _ _ hτ) (hN _ _ hτ)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h6, card_Γ₁])).symm
  · right
    have hτ : τ₂ ∈ N := by
      have := hN δ⁻¹ _ e.2
      rw [hδ] at this
      simpa [mul_assoc] using this
    have hle : Γ₂ ≤ N := by
      intro γ hγ
      obtain ⟨δ₁, δ₂, h1 | h2⟩ := Γ₂_closure γ (mem_Γ₂.mp hγ)
      · rw [h1]; exact hN _ _ hτ
      · rw [h2]; exact mul_mem (hN _ _ hτ) (hN _ _ hτ)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h6, card_Γ₂])).symm
  · exfalso
    have hτ : τ₁ * τ₂ ∈ N := by
      have := hN δ⁻¹ _ e.2
      rw [hδ] at this
      simpa [mul_assoc] using this
    have hsub : (Finset.univ.filter fun s : Gm => s ^ 3 = 1 : Set Gm) ⊆ N := by
      intro s hs
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs
      obtain ⟨δ₁, δ₂, h⟩ := diag_closure s hs
      rw [h]
      exact mul_mem (hN _ _ hτ) (hN _ _ hτ)
    have h9 : 9 ≤ Nat.card N := by
      rw [← card_cube_set]
      calc (Finset.univ.filter fun s : Gm => s ^ 3 = 1).card =
            Nat.card (Finset.univ.filter fun s : Gm => s ^ 3 = 1 : Set Gm) := by
            rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
        _ ≤ Nat.card N := Nat.card_mono (Set.toFinite _) hsub
    omega

theorem mem_Γ₁_of_comm_Γ₂ : ∀ γ : Gm, (∀ δ : Gm, δ.1 = 1 → γ * δ = δ * γ) → γ.2 = 1 := by
  decide +kernel

theorem perm_three_exists_conj_mul : ∀ σ : Equiv.Perm (Fin 3), σ * σ = 1 → σ ≠ 1 →
    ∃ τ : Equiv.Perm (Fin 3), (σ * (τ * σ * τ⁻¹)) ^ 3 = 1 ∧ σ * (τ * σ * τ⁻¹) ≠ 1 := by
  decide +kernel

theorem perm_three_pow_six : ∀ σ : Equiv.Perm (Fin 3), σ ^ 6 = 1 := by decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

variable (S g t) in
structure DirDec (Xb Yb : Subgroup S.O) : Prop where
  sup : Xb ⊔ Yb = Rbar S g t
  inf : Xb ⊓ Yb = ⊥
  comm : ∀ a ∈ Xb, ∀ b ∈ Yb, a * b = b * a
  iso : Nonempty (Yb ≃* Equiv.Perm (Fin 3))

namespace DirDec

variable {Xb Yb : Subgroup S.O} (D : DirDec S g t Xb Yb)
include D

theorem le_Rbar_left : Xb ≤ Rbar S g t := D.sup ▸ le_sup_left

theorem le_Rbar_right : Yb ≤ Rbar S g t := D.sup ▸ le_sup_right

theorem card_Yb : Nat.card Yb = 6 := by
  obtain ⟨e⟩ := D.iso
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem exists_mul {r : S.O} (hr : r ∈ Rbar S g t) : ∃ a ∈ Xb, ∃ b ∈ Yb, r = a * b :=
  exists_mul_of_mem_sup_of_commute D.comm (D.sup ▸ hr)

theorem conj_mem_Yb {r : S.O} (hr : r ∈ Rbar S g t) {y : S.O} (hy : y ∈ Yb) :
    r * y * r⁻¹ ∈ Yb := by
  obtain ⟨a, ha, b, hb, rfl⟩ := D.exists_mul hr
  have h1 : a * b * y * (a * b)⁻¹ = b * y * b⁻¹ := by
    have hay : a * (b * y * b⁻¹) = (b * y * b⁻¹) * a :=
      D.comm a ha _ (mul_mem (mul_mem hb hy) (inv_mem hb))
    calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      _ = (b * y * b⁻¹) * a * a⁻¹ := by rw [hay]
      _ = b * y * b⁻¹ := by group
  rw [h1]
  exact mul_mem (mul_mem hb hy) (inv_mem hb)

theorem eq_one_of_mem_Nbar (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {z : S.O}
    (hzY : z ∈ Yb) (hzN : z ∈ Nbar S g t) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := D.iso
  by_contra hz1
  have hz6 : (⟨z, hzY⟩ : Yb) ^ 6 = 1 := e.injective (by rw [map_pow, map_one, perm_three_pow_six])
  obtain ⟨k, hk⟩ := (X.isPGroup_Nbar hCE) ⟨z, hzN⟩
  have hzk : z ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hz6' : z ^ 6 = 1 := congrArg Subtype.val hz6
  have hord : orderOf z ∣ Nat.gcd (2 ^ k) 6 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzk)
    (orderOf_dvd_of_pow_eq_one hz6')
  have hgcd : Nat.gcd (2 ^ k) 6 ∣ 2 := by
    rcases k with _ | k
    · simp
    · rw [pow_succ, show (6 : ℕ) = 3 * 2 by rfl]
      exact (Nat.gcd_mul_right _ _ _ ▸ Nat.mul_dvd_mul_right (Nat.Coprime.gcd_eq_one
        (Nat.Coprime.pow_left _ (by norm_num))).dvd 2 |>.trans (by simp))
  have hz2 : z * z = 1 := by
    rw [← _root_.sq]
    exact orderOf_dvd_iff_pow_eq_one.mp (hord.trans hgcd)
  have hez : e ⟨z, hzY⟩ * e ⟨z, hzY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hzY⟩ : Yb) * ⟨z, hzY⟩ = 1 := Subtype.ext hz2
    rw [this, map_one]
  have hez1 : e ⟨z, hzY⟩ ≠ 1 := fun h => hz1 (congrArg Subtype.val (e.injective
    (h.trans (map_one e).symm)))
  obtain ⟨τ, hτ3, hτ1⟩ := perm_three_exists_conj_mul _ hez hez1
  have hexy : ∃ y₁ : Yb, y₁ = e.symm τ := ⟨_, rfl⟩
  obtain ⟨y₁, hy₁⟩ := hexy
  have hWe : e (⟨z, hzY⟩ * (y₁ * ⟨z, hzY⟩ * y₁⁻¹)) =
      e ⟨z, hzY⟩ * (τ * e ⟨z, hzY⟩ * τ⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, hy₁, MulEquiv.apply_symm_apply]
  have hW3 : (⟨z, hzY⟩ * (y₁ * ⟨z, hzY⟩ * y₁⁻¹) : Yb) ^ 3 = 1 :=
    e.injective (by rw [map_pow, hWe, hτ3, map_one])
  have hW1 : (⟨z, hzY⟩ * (y₁ * ⟨z, hzY⟩ * y₁⁻¹) : Yb) ≠ 1 := fun h => hτ1 (by
    rw [← hWe, h, map_one])
  have hWc : ((⟨z, hzY⟩ * (y₁ * ⟨z, hzY⟩ * y₁⁻¹) : Yb) : S.O) =
      z * ((y₁ : S.O) * z * (y₁ : S.O)⁻¹) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hw3 : (z * ((y₁ : S.O) * z * (y₁ : S.O)⁻¹)) ^ 3 = 1 := by
    rw [← hWc, ← Subgroup.coe_pow, hW3]
    rfl
  have hw1 : z * ((y₁ : S.O) * z * (y₁ : S.O)⁻¹) ≠ 1 := fun h => hW1 (Subtype.ext (by
    rw [hWc, h]
    rfl))
  have hy₁R : (y₁ : S.O) ∈ Rbar S g t := D.le_Rbar_right y₁.2
  obtain ⟨kk, hkk⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hy₁R)
  have hkkR : S.ρ kk ∈ Rbar S g t := by rw [hkk]; exact hy₁R
  have hc := conj_mem_Nbar X.haQ (commute_of_mem_Rbar X.haQ hkkR) hzN
  rw [hkk] at hc
  have hwN : z * ((y₁ : S.O) * z * (y₁ : S.O)⁻¹) ∈ Nbar S g t := mul_mem hzN hc
  obtain ⟨k', hk'⟩ := (X.isPGroup_Nbar hCE) ⟨_, hwN⟩
  have hwk : (z * ((y₁ : S.O) * z * (y₁ : S.O)⁻¹)) ^ (2 ^ k') = 1 := congrArg Subtype.val hk'
  have h1 : orderOf (z * ((y₁ : S.O) * z * (y₁ : S.O)⁻¹)) ∣ Nat.gcd (2 ^ k') 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hwk) (orderOf_dvd_of_pow_eq_one hw3)
  rw [(Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, Nat.dvd_one,
    orderOf_eq_one_iff] at h1
  exact hw1 h1

@[expose] noncomputable def piY {X : Hyp10 S g t} (F : Frame X) : Yb →* Gm :=
  F.π.comp (Subgroup.inclusion D.le_Rbar_right)

theorem piY_apply {X : Hyp10 S g t} (F : Frame X) (y : Yb) :
    D.piY F y = F.π ⟨y, D.le_Rbar_right y.2⟩ := rfl

theorem piY_injective (hCE : CentralExtInput.{u}) {X : Hyp10 S g t} (F : Frame X) :
    Function.Injective (D.piY F) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  rw [piY_apply] at hy
  exact Subtype.ext (D.eq_one_of_mem_Nbar hCE X y.2 ((F.ker _).mp hy))

theorem range_piY (hCE : CentralExtInput.{u}) {X : Hyp10 S g t} (F : Frame X) :
    (D.piY F).range = Γ₁ ∨ (D.piY F).range = Γ₂ := by
  refine normal_card_six ?_ ?_
  · rintro δ _ ⟨y, rfl⟩
    obtain ⟨r, rfl⟩ := F.surj δ
    refine ⟨⟨(r : S.O) * y * (r : S.O)⁻¹, D.conj_mem_Yb r.2 y.2⟩, ?_⟩
    rw [piY_apply, piY_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  · rw [← Nat.card_congr (MonoidHom.ofInjective (D.piY_injective hCE F)).toEquiv, D.card_Yb]

theorem exists_frame (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) :
    ∃ F : Frame X, (D.piY F).range = Γ₂ ∧ Xb = F.pre Γ₁ := by
  obtain ⟨F₀⟩ := X.exists_frame
  obtain ⟨F, hF⟩ : ∃ F : Frame X, (D.piY F).range = Γ₂ := by
    rcases D.range_piY hCE F₀ with h1 | h2
    · refine ⟨F₀.swap, ?_⟩
      ext γ
      rw [MonoidHom.mem_range, mem_Γ₂]
      constructor
      · rintro ⟨y, rfl⟩
        rw [piY_apply, F₀.swap_π]
        have : F₀.π ⟨y, D.le_Rbar_right y.2⟩ ∈ Γ₁ := h1 ▸ ⟨y, rfl⟩
        exact mem_Γ₁.mp this
      · intro hγ
        have : γ.swap ∈ Γ₁ := mem_Γ₁.mpr hγ
        rw [← h1] at this
        obtain ⟨y, hy⟩ := this
        refine ⟨y, ?_⟩
        rw [piY_apply, F₀.swap_π, ← D.piY_apply, hy, Prod.swap_swap]
    · exact ⟨F₀, h2⟩
  refine ⟨F, hF, le_antisymm (fun x hx => ?_) (fun r hr => ?_)⟩
  ·
    refine (F.mem_pre).mpr ⟨D.le_Rbar_left hx, mem_Γ₁.mpr (mem_Γ₁_of_comm_Γ₂ _ fun δ hδ => ?_)⟩
    have : δ ∈ (D.piY F).range := hF ▸ mem_Γ₂.mpr hδ
    obtain ⟨y, rfl⟩ := this
    rw [piY_apply, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (D.comm x hx y y.2)
  · obtain ⟨hrR, hrπ⟩ := (F.mem_pre).mp hr
    obtain ⟨a, ha, b, hb, rfl⟩ := D.exists_mul hrR
    have haπ : F.π ⟨a, D.le_Rbar_left ha⟩ ∈ Γ₁ := by
      refine mem_Γ₁.mpr (mem_Γ₁_of_comm_Γ₂ _ fun δ hδ => ?_)
      have : δ ∈ (D.piY F).range := hF ▸ mem_Γ₂.mpr hδ
      obtain ⟨y, rfl⟩ := this
      rw [piY_apply, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (D.comm a ha y y.2)
    have hbπ2 : F.π ⟨b, D.le_Rbar_right hb⟩ ∈ Γ₂ := hF ▸ ⟨⟨b, hb⟩, rfl⟩
    have hbπ1 : F.π ⟨b, D.le_Rbar_right hb⟩ ∈ Γ₁ := by
      have e : (⟨b, D.le_Rbar_right hb⟩ : Rbar S g t) =
          (⟨a, D.le_Rbar_left ha⟩ : Rbar S g t)⁻¹ * ⟨a * b, hrR⟩ := Subtype.ext (by simp)
      rw [e, map_mul, map_inv]
      exact mul_mem (inv_mem haπ) hrπ
    have hb1 : b = 1 := D.eq_one_of_mem_Nbar hCE X hb ((F.ker _).mp
      (eq_one_of_mem_Γ₁_of_mem_Γ₂ (mem_Γ₁.mp hbπ1) (mem_Γ₂.mp hbπ2)))
    rw [hb1, mul_one]
    exact ha

theorem Nbar_le (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) : Nbar S g t ≤ Xb := by
  obtain ⟨F, -, hX⟩ := D.exists_frame hCE X
  rw [hX]
  exact F.Nbar_le_pre Γ₁

end DirDec

end CFSG.LargeExtraspecial.S10
