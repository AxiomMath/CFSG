module

public import CFSG.LargeExtraspecial.S10EightD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem exists_pf_pow : ∀ γ δ : Gm, γ ^ 3 = 1 → γ.1 ≠ 1 → δ.1 = 1 → δ ^ 3 = 1 → δ ≠ 1 →
    ∃ a b : Fin 3, pf E00 (act (γ ^ (a : ℕ) * δ ^ (b : ℕ)) E00) = 1 := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem conj_mem_Nbar_of_mem_Rbar (haQ : g * S.z * g⁻¹ ∈ S.QG) {h : S.O}
    (hh : h ∈ Rbar S g t) {x : S.O} (hx : x ∈ Nbar S g t) : h * x * h⁻¹ ∈ Nbar S g t := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hh)
  exact conj_mem_Nbar haQ (commute_of_mem_Rbar haQ hh) hx

namespace DirDec

variable {Xb Yb : Subgroup S.O} (D : DirDec S g t Xb Yb)
include D

theorem isOp_commutator (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) :
    IsOp 3 (Rbar S g t) ⁅Yb, Yb⁆ where
  le := fun y hy => D.le_Rbar_right ((D.mem_commutator_iff).mp hy).1
  isPGroup := IsPGroup.of_card (n := 1) (by rw [D.card_commutator, pow_one])
  conj_mem := fun r hr y hy => D.conj_mem_commutator hr hy
  le_of := by
    intro H hHR hH hHn
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := hH.exists_card_eq
    have hodd : Odd (Nat.card H) := by rw [hn]; exact Odd.pow (by decide)
    obtain ⟨F, hFY, -⟩ := D.exists_frame hCE X
    by_cases hπ : ∀ h (hh : h ∈ H), (F.π ⟨h, hHR hh⟩).1 = 1
    · exact le_commutator_of_Γ₂ hCE X D F hFY hHR hodd hπ
    exfalso
    push Not at hπ
    obtain ⟨h, hh, hh1⟩ := hπ
    have hhR := hHR hh
    have hcomm : ∀ z ∈ S.Lbar g ⊓ Nbar S g t, z * h = h * z := by
      intro z hz
      have hzR := Nbar_le_Rbar hz.2
      have hcH : z * h * z⁻¹ * h⁻¹ ∈ H := mul_mem (hHn z hzR h hh) (inv_mem hh)
      have hcN : z * h * z⁻¹ * h⁻¹ ∈ Nbar S g t := by
        have e : z * h * z⁻¹ * h⁻¹ = z * (h * z⁻¹ * h⁻¹) := by group
        rw [e]
        exact mul_mem hz.2 (conj_mem_Nbar_of_mem_Rbar X.haQ hhR (inv_mem hz.2))
      have h1 := eq_one_of_mem_Nbar_of_odd hCE X hodd hcH hcN
      calc z * h = z * h * z⁻¹ * h⁻¹ * (h * z) := by group
        _ = h * z := by rw [h1, one_mul]
    obtain ⟨⟨d, hdY'⟩, hd1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp D.commutator_ne_bot
    have hd1 : d ≠ 1 := fun h => hd1' (Subtype.ext h)
    have hdY := ((D.mem_commutator_iff).mp hdY').1
    have hd3 := ((D.mem_commutator_iff).mp hdY').2
    have hdR := D.le_Rbar_right hdY
    have hπd1 : (F.π ⟨d, hdR⟩).1 = 1 := mem_Γ₂.mp (hFY ▸ ⟨⟨d, hdY⟩, rfl⟩)
    have hπd3 : F.π ⟨d, hdR⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨d, hdR⟩ : Rbar S g t) ^ 3 = 1 := Subtype.ext hd3
      rw [this, map_one]
    have hπdne : F.π ⟨d, hdR⟩ ≠ 1 := fun h => hd1 (by
      have := D.piY_injective hCE F (a₁ := ⟨d, hdY⟩) (a₂ := 1)
        (by rw [DirDec.piY_apply, map_one]; exact h)
      exact congrArg Subtype.val this)
    obtain ⟨a, b, hab⟩ := exists_pf_pow _ _ (cube_π_of_odd F hodd hh hhR) hh1 hπd1 hπd3 hπdne
    refine false_of_Abar_comm hCE X F (k := ⟨h, hhR⟩ ^ (a : ℕ) * ⟨d, hdR⟩ ^ (b : ℕ)) ?_ ?_
    · rw [map_mul, map_pow, map_pow]
      exact hab
    · intro z hz
      have hz1 := hcomm z hz
      have hz2 : z * d = d * z := D.comm z (D.Nbar_le hCE X hz.2) d hdY
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
      exact ((Commute.pow_right hz1 a).mul_right (Commute.pow_right hz2 b))

end DirDec

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem isOp_sup :
    IsOp 3 ((S.Lbar g ⊓ Xb) ⊔ Yb) ⁅Yb, Yb⁆ where
  le := fun y hy => Subgroup.mem_sup_right ((D.dec.mem_commutator_iff).mp hy).1
  isPGroup := IsPGroup.of_card (n := 1) (by rw [D.dec.card_commutator, pow_one])
  conj_mem := by
    intro r hr y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute (A := S.Lbar g ⊓ Xb)
      (B := Yb) (fun a ha b hb => D.dec.comm a ha.2 b hb) hr
    have hyY := ((D.dec.mem_commutator_iff).mp hy).1
    have hby : b * y * b⁻¹ ∈ ⁅Yb, Yb⁆ := D.dec.conj_mem_commutator (D.dec.le_Rbar_right hb) hy
    have hac : a * (b * y * b⁻¹) = (b * y * b⁻¹) * a :=
      D.dec.comm a ha.2 _ ((D.dec.mem_commutator_iff).mp hby).1
    have e : a * b * y * (a * b)⁻¹ = b * y * b⁻¹ := by
      calc a * b * y * (a * b)⁻¹ = (a * (b * y * b⁻¹)) * a⁻¹ := by group
        _ = b * y * b⁻¹ := by rw [hac]; group
    rw [e]
    exact hby
  le_of := by
    intro H hHR hH _ x hx
    obtain ⟨m, hm⟩ := hH ⟨x, hx⟩
    have hxm : x ^ (3 ^ m) = 1 := congrArg Subtype.val hm
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute (A := S.Lbar g ⊓ Xb)
      (B := Yb) (fun a ha b hb => D.dec.comm a ha.2 b hb) (hHR hx)
    have hab : Commute a b := D.dec.comm a ha.2 b hb
    rw [hab.mul_pow] at hxm
    have haX : a ^ (3 ^ m) ∈ Xb := pow_mem ha.2 _
    have hbY : (b ^ (3 ^ m))⁻¹ ∈ Yb := inv_mem (pow_mem hb _)
    have hab' : a ^ (3 ^ m) = (b ^ (3 ^ m))⁻¹ := eq_inv_of_mul_eq_one_left hxm
    have ha1 : a ^ (3 ^ m) = 1 := by
      have : a ^ (3 ^ m) ∈ Xb ⊓ Yb := ⟨haX, hab' ▸ hbY⟩
      rw [D.dec.inf] at this
      exact (Subgroup.mem_bot).mp this
    have hb1 : b ^ (3 ^ m) = 1 := by
      rw [ha1, one_mul] at hxm
      exact hxm
    have haa : a * a = 1 := S4.mul_self_of_mem_Lbar S X.haQ ha.1
    have hodd : Odd (3 ^ m) := Odd.pow (by decide)
    have ha' : a = 1 := by
      obtain ⟨j, hj⟩ := hodd
      have h2 : a ^ (2 * j) = 1 := by rw [pow_mul, _root_.sq, haa, one_pow]
      rw [hj, pow_succ, h2, one_mul] at ha1
      exact ha1
    rw [ha', one_mul]
    refine (D.dec.mem_commutator_iff).mpr ⟨hb, ?_⟩
    obtain ⟨e⟩ := D.dec.iso
    have h6 : (⟨b, hb⟩ : Yb) ^ 6 = 1 := e.injective (by
      rw [map_pow, map_one]
      exact perm_three_pow_six _)
    have h6' : b ^ 6 = 1 := congrArg Subtype.val h6
    have hdvd : orderOf b ∣ Nat.gcd (3 ^ m) 6 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hb1) (orderOf_dvd_of_pow_eq_one h6')
    have hg : Nat.gcd (3 ^ m) 6 ∣ 3 := by
      have h1 : Nat.gcd (3 ^ m) 6 = Nat.gcd (3 ^ m) 3 * Nat.gcd (3 ^ m) 2 :=
        Nat.Coprime.gcd_mul _ (by norm_num : Nat.Coprime 3 2)
      have h2 : Nat.gcd (3 ^ m) 2 = 1 :=
        Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 3 2)
      rw [h1, h2, mul_one]
      exact Nat.gcd_dvd_right _ _
    exact orderOf_dvd_iff_pow_eq_one.mp (hdvd.trans hg)

theorem exists_dirDec_of_hyp10 (hCE : CentralExtInput.{u}) {τ : S.O}
    (hτ : τ ∈ S.Lbar g ⊓ Xb) (Y : Hyp10 S g τ) :
    ∃ Xτ Yτ : Subgroup S.O, DirDec S g τ Xτ Yτ ∧ ⁅Yb, Yb⁆ = ⁅Yτ, Yτ⁆ := by
  obtain ⟨x, hx, hxN⟩ : ∃ x ∈ S.Lbar g ⊓ Xb, x ∉ Nbar S g τ := by
    by_contra hcon
    push Not at hcon
    have := D.card_LmodN_le_two hCE hτ hcon
    rw [Y.card_LmodN] at this
    omega
  obtain ⟨k, hkY', -, hne, hPa, -⟩ := D.exists_d hCE
  have hkY := ((D.dec.mem_commutator_iff).mp hkY').1
  obtain ⟨F, -, -, -⟩ := D.exists_frame hCE
  have hkR := D.dec.le_Rbar_right hkY
  have hπk : act (F.π ⟨S.ρ k, hkR⟩) E00 ≠ E00 := by
    intro h
    have hth := D.mem_Lbar_mul (D.t_mem_Ebar hCE) hkY
    have h1 : F.φ (bV hth) = F.φ (aV X.ht) := by
      rw [bV_eq_resV X hkR hth, F.φ_resV_aV, h, F.base]
    have h2 := congrArg Subtype.val (F.φ.injective h1)
    rw [coe_bV] at h2
    exact hne h2
  have hdim := finrank_commSpace_le_four_of_fixW X F hkR hπk hPa hx.1 (D.fixW x hx.2)
    (D.mem_Lbar_mul hx hkY)
  have hxW := mem_fixWstar_of_finrank_le Y hx.1 hxN hdim
  obtain ⟨F₀⟩ := Y.exists_frame
  obtain ⟨F', hπx⟩ : ∃ F' : Frame Y, F'.π ⟨x, Lbar_le_Rbar Y.ht hx.1⟩ = τ₁ := by
    rcases pi_eq_τ₁_or_τ₂ hCE Y F₀ hx.1 hxN hxW with h | h
    · exact ⟨F₀, h⟩
    · exact ⟨F₀.swap, by rw [F₀.swap_π, h, τ₂_swap]⟩
  obtain ⟨-, Yτ, -, hiso, hsup, hinf, hcomm, -, -⟩ := timmesfeld_10_2_frame hCE Y F' hx.1 hxW hπx
  have Dτ : DirDec S g τ (R0 S g τ x) Yτ := ⟨hsup, hinf, hcomm, hiso⟩
  refine ⟨R0 S g τ x, Yτ, Dτ, ?_⟩
  obtain ⟨hidx, hc⟩ := timmesfeld_10_3_hyperplane hCE X D.dec
  refine timmesfeld_10_3_beta hCE Y Dτ (fun y hy => D.Yb_le_Rbar hτ
    ((D.dec.mem_commutator_iff).mp hy).1) (by rw [D.dec.card_commutator]; decide)
    D.dec.commutator_ne_bot inf_le_left hidx hc

end Dec108

end CFSG.LargeExtraspecial.S10
