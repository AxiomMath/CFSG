module

public import CFSG.GH74.GLS.Bg.TwoGroups.L26Main
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma23
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21a

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L26

open A44

theorem k2_card : K2Prop := by
  intro T _ _ hp α hα hfix A hAn hAα hθ hC hAtop
  obtain ⟨θ⟩ := hθ
  have hA16 : Nat.card A = 16 := (Nat.card_congr θ.toEquiv).trans card_Z4Z4
  let ρ : T →* G96 := L23.rhoHom A θ
  let ξ : G96 := L23.xi A θ α hAα
  have hker : ρ.ker = A := L23.ker_rho A θ hC
  have hxfix : ∀ g : T, ξ * ρ g * ξ⁻¹ = ρ g → ρ g = 1 := fun g h =>
    L23.xi_fpf A θ α hAα hα hfix hC hA16 g h
  have hξ3 : ξ ^ 3 = 1 := L23.xi_pow_three A θ α hAα hα
  have hξord : ξ.1 ∈ ord3list := L23.xi_mem_ord3 A θ α hAα hα hfix
  have hrx : ∀ g : T, ρ (α g) = ξ * ρ g * ξ⁻¹ := fun g => L23.rho_x A θ α hAα g
  let K0 : Subgroup G96 := subOfList K0list K0_closed
  have hK0mem : ∀ w : G96, w ∈ K0 ↔ w.1 ∈ K0list := fun w => mem_subOfList K0_closed w
  have hK0conj : ∀ g w : G96, w ∈ K0 → g * w * g⁻¹ ∈ K0 := by
    intro g w hw
    rw [hK0mem] at hw ⊢
    exact K0_conj g.1 g.2 w.1 hw
  have hξK0 : ξ ∈ K0 := (hK0mem ξ).mpr (ord3_sub_K0 _ hξord)
  have hRK0 : ∀ g : T, ρ g ∈ K0 := by
    have htop := commAut_eq_top hp α 1 (by rw [pow_one]; exact hα) hfix
    intro g
    have hg : g ∈ commAut α := by rw [htop]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [map_mul, hrx h, map_inv]
      have h1 : (ρ h)⁻¹ * ξ * (ρ h)⁻¹⁻¹ ∈ K0 := hK0conj _ _ hξK0
      have h2 : (ρ h)⁻¹ * ξ * (ρ h)⁻¹⁻¹ * ξ⁻¹ ∈ K0 := mul_mem h1 (inv_mem hξK0)
      have e : (ρ h)⁻¹ * (ξ * ρ h * ξ⁻¹) = (ρ h)⁻¹ * ξ * (ρ h)⁻¹⁻¹ * ξ⁻¹ := by group
      rw [e]; exact h2
    | one => rw [map_one]; exact one_mem K0
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact inv_mem hx
  have hcard96 : Nat.card G96 = 96 := by rw [Nat.card_eq_fintype_card]; exact M4.card_G96
  have hV4 : ∀ g : T, (ρ g).1 ∈ V4list := by
    intro g
    have hK := (hK0mem _).mp (hRK0 g)
    have h32 : (ρ g) ^ 32 = 1 := by
      obtain ⟨n, hn⟩ := hp g
      have h0 : (ρ g) ^ (2 ^ n) = 1 := by rw [← map_pow, hn, map_one]
      have h1 : orderOf (ρ g) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h0
      have h2 : orderOf (ρ g) ∣ 96 := hcard96 ▸ orderOf_dvd_natCard (ρ g)
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      rw [hj] at h2
      have hk5 : j ≤ 5 := by
        by_contra hlt
        have h6 : 6 ≤ j := by omega
        have h7 : 2 ^ 6 ∣ 2 ^ j := Nat.pow_dvd_pow 2 h6
        have := dvd_trans h7 h2
        omega
      rw [← orderOf_dvd_iff_pow_eq_one, hj]
      exact Nat.pow_dvd_pow 2 hk5
    exact K0_two _ hK (pow32_eq_one_iff.mp h32)
  let R : Subgroup G96 := ρ.range
  have hRle : Nat.card R ≤ 4 := by
    let f : R → {m : M4 // m ∈ V4list} := fun r => ⟨r.1.1, by
      obtain ⟨_, g, rfl⟩ := r
      exact hV4 g⟩
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      exact h'
    have := Nat.card_le_card_of_injective f hf
    have h4 : Nat.card {m : M4 // m ∈ V4list} = 4 := by
      rw [Nat.card_eq_fintype_card]; decide +kernel
    omega
  have hRne : R ≠ ⊥ := by
    intro h
    apply hAtop
    rw [← hker, eq_top_iff]
    intro g _
    have : ρ g ∈ R := ⟨g, rfl⟩
    rw [h] at this
    exact this
  have hRge : 2 ≤ Nat.card R := by
    have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hRne
    exact Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.mpr this)
  have hRinv : ∀ v ∈ R, (MulAut.conj ξ) v ∈ R := by
    rintro _ ⟨g, rfl⟩
    refine ⟨α g, ?_⟩
    rw [hrx g, MulAut.conj_apply]
  have hcj3 : (MulAut.conj ξ) ^ (3 ^ 1) = 1 := by
    rw [pow_one, ← map_pow, hξ3, map_one]
  have hmod := card_fix_modEq3 (MulAut.conj ξ) 1 hcj3 R hRinv
  have hfixcard : Nat.card {v : R // (MulAut.conj ξ) v = v} = 1 := by
    have : Unique {v : R // (MulAut.conj ξ) v = v} :=
      { default := ⟨1, map_one _⟩
        uniq := by
          rintro ⟨⟨_, g, rfl⟩, hv⟩
          apply Subtype.ext
          apply Subtype.ext
          exact hxfix g (by rw [← MulAut.conj_apply]; exact hv) }
    exact Nat.card_unique
  rw [hfixcard] at hmod
  have hRcard : Nat.card R = 4 := by
    have h1 : Nat.card R % 3 = 1 := hmod
    omega
  have hmul := Subgroup.card_ker_mul_card_range ρ
  rw [hker, hA16] at hmul
  have : Nat.card ρ.range = 4 := hRcard
  omega

end L26

end CFSG.GH74.GLS.Bg.TwoGroups
