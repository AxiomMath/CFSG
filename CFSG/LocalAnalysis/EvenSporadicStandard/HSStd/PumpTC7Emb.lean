module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup

@[expose] noncomputable def conjEmb {Γ D : Type*} [Group Γ] [Group D] (N : Subgroup Γ)
    [N.Normal] (e : N ≃* D) : Γ →* MulAut D :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem conjEmb_apply {Γ D : Type*} [Group Γ] [Group D] (N : Subgroup Γ) [N.Normal]
    (e : N ≃* D) (n : N) (x : D) : conjEmb N e (n : Γ) x = e n * x * (e n)⁻¹ := by
  have h : (MulAut.conjNormal (n : Γ) : MulAut N) (e.symm x) = n * e.symm x * n⁻¹ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply])
  simp only [conjEmb, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, h, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem conjEmb_injective {Γ D : Type*} [Group Γ] [Group D] (N : Subgroup Γ) [N.Normal]
    (e : N ≃* D) (hN : centralizer (N : Set Γ) = ⊥) : Function.Injective (conjEmb N e) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : (MulAut.conjNormal g : MulAut N) = 1 := by
    apply (MulAut.congr e).injective
    rw [map_one]
    exact hg
  have hmem : g ∈ centralizer (N : Set Γ) := by
    rw [mem_centralizer_iff]
    intro n hn
    have h2 := congrArg (fun γ : MulAut N => (γ ⟨n, hn⟩ : Γ)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  rw [hN] at hmem
  exact mem_bot.1 hmem

theorem card_dvd_of_injective' {Γ H : Type*} [Group Γ] [Group H] (ρ : Γ →* H)
    (hρ : Function.Injective ρ) : Nat.card Γ ∣ Nat.card H :=
  Subgroup.card_dvd_of_injective ρ hρ

theorem card_centralizer_dvd {Γ H : Type*} [Group Γ] [Group H] (ρ : Γ →* H)
    (hρ : Function.Injective ρ) (y : Γ) :
    Nat.card (centralizer ({y} : Set Γ)) ∣ Nat.card (centralizer ({ρ y} : Set H)) := by
  have hle : (centralizer ({y} : Set Γ)).map ρ ≤ centralizer ({ρ y} : Set H) := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c ∈ centralizer ({y} : Set Γ) := hc
    rw [mem_centralizer_singleton_iff] at hc' ⊢
    rw [← map_mul, ← map_mul, hc']
  rw [← Subgroup.card_map_of_injective hρ]
  exact Subgroup.card_dvd_of_le hle

theorem exists_orderOf_of_dvd_card {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} [Fact p.Prime]
    (h : p ∣ Nat.card Γ) : ∃ g : Γ, orderOf g = p :=
  exists_prime_orderOf_dvd_card' p h

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
