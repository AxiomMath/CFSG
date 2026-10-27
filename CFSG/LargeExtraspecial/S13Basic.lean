module

public import CFSG.LargeExtraspecial.S13Mul

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g g' : G} {K : Subgroup S.O}

variable (S) in
@[expose] def NormalInMbar (K : Subgroup S.O) : Prop :=
  ∀ m ∈ S.Mbar, ∀ k ∈ K, m * k * m⁻¹ ∈ K

variable (S) in
@[expose] def FixFree (K : Subgroup S.O) : Prop :=
  ∀ v : S.Qt, (∀ k ∈ K, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → v = 0

variable (S) in
@[expose] noncomputable def Ebar (g : G) (K : Subgroup S.O) : Subgroup S.O :=
  S.Lbar g ⊓ centralizer (K : Set S.O)

theorem Ebar_le_Lbar : Ebar S g K ≤ S.Lbar g := inf_le_left

theorem mem_Ebar {x : S.O} : x ∈ Ebar S g K ↔ x ∈ S.Lbar g ∧ ∀ k ∈ K, k * x = x * k := by
  rw [Ebar, mem_inf, mem_centralizer_iff]
  rfl

section Three

variable (hK3 : Nat.card K = 3)
include hK3

theorem eq_zpowers {k : S.O} (hk : k ∈ K) (hk1 : k ≠ 1) : K = zpowers k := by
  have hle : zpowers k ≤ K := zpowers_le.mpr hk
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hK3] at hdvd
  have h1 : Nat.card (zpowers k) ≠ 1 := by
    intro h
    apply hk1
    have := Subgroup.eq_bot_of_card_eq _ h
    have hm : k ∈ zpowers k := mem_zpowers k
    rw [this, mem_bot] at hm
    exact hm
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd h h1
  · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h, hK3])).symm

theorem pow_three_eq_one {k : S.O} (hk : k ∈ K) : k ^ 3 = 1 := by
  have h2 : (⟨k, hk⟩ : K) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := K) (x := ⟨k, hk⟩)
    rwa [hK3] at this
  exact congrArg Subtype.val h2

theorem fix_eq_zero (hfpf : FixFree S K) {k : S.O} (hk : k ∈ K) (hk1 : k ≠ 1) (v : S.Qt)
    (hv : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : v = 0 := by
  apply hfpf v
  intro k' hk'
  rw [eq_zpowers hK3 hk hk1] at hk'
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hk'
  have key : ∀ j : ℕ, ((k ^ j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Subgroup.coe_mul, LinearEquiv.mul_apply, hv, ih]
  have hk3 := pow_three_eq_one hK3 hk
  have e : k ^ i = k ^ (i.natMod 3) := by
    rw [← zpow_natCast, Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    exact zpow_eq_zpow_emod' i hk3
  rw [e]
  exact key _

theorem comm_or_inv {x : S.O} (hx : ∀ k ∈ K, x * k * x⁻¹ ∈ K) :
    (∀ k ∈ K, k * x = x * k) ∨ ∀ k ∈ K, x * k * x⁻¹ = k⁻¹ := by
  by_cases hK : ∃ k ∈ K, k ≠ 1
  · obtain ⟨k, hk, hk1⟩ := hK
    have hk3 := pow_three_eq_one hK3 hk
    have hxk := hx k hk
    rw [eq_zpowers hK3 hk hk1] at hxk
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hxk
    have hk1' : x * k * x⁻¹ ≠ 1 := fun h => hk1 (by
      have : k = x⁻¹ * (x * k * x⁻¹) * x := by group
      rw [this, h]; group)
    have hpow : ∀ j : ℤ, k ^ j = k ^ (j % 3) := fun j => zpow_eq_zpow_emod' j hk3
    have hr : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    have hgen : ∀ k' ∈ K, ∃ j : ℤ, k' = k ^ j := fun k' hk' => by
      rw [eq_zpowers hK3 hk hk1] at hk'
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hk'
      exact ⟨j, rfl⟩
    rcases hr with h0 | h1 | h2
    · exfalso
      apply hk1'
      rw [← hi, hpow, h0, zpow_zero]
    · left
      intro k' hk'
      obtain ⟨j, rfl⟩ := hgen k' hk'
      have e1 : x * k * x⁻¹ = k := by rw [← hi, hpow, h1, zpow_one]
      have e2 : x * k ^ j * x⁻¹ = k ^ j := by
        rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, e1]
      calc k ^ j * x = x * k ^ j * x⁻¹ * x := by rw [e2]
        _ = x * k ^ j := by group
    · right
      intro k' hk'
      obtain ⟨j, rfl⟩ := hgen k' hk'
      have e1 : x * k * x⁻¹ = k⁻¹ := by
        rw [← hi, hpow, h2]
        have : k ^ (2 : ℤ) * k = 1 := by
          rw [← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num, zpow_ofNat, hk3]
        exact eq_inv_of_mul_eq_one_left this
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, e1, inv_zpow]
  · push Not at hK
    left
    intro k hk
    rw [hK k hk, one_mul, mul_one]

end Three

theorem Ebar_mul (hN : NormalInMbar S K) {h : S.M} (hg : g' = (h : G) * g) :
    Ebar S g' K = (Ebar S g K).map (cK S h) := by
  have hρ : S.ρ h ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨h, rfl⟩
  ext x
  rw [mem_map_cK_iff, mem_Ebar, mem_Ebar, Lbar_mul' hg, mem_map_cK_iff]
  refine and_congr_right fun _ => ⟨fun hx k hk => ?_, fun hx k hk => ?_⟩
  · have hk' := hN _ hρ k hk
    have := hx _ hk'
    calc k * ((S.ρ h)⁻¹ * x * S.ρ h)
        = (S.ρ h)⁻¹ * ((S.ρ h * k * (S.ρ h)⁻¹) * x) * S.ρ h := by group
      _ = (S.ρ h)⁻¹ * (x * (S.ρ h * k * (S.ρ h)⁻¹)) * S.ρ h := by rw [this]
      _ = (S.ρ h)⁻¹ * x * S.ρ h * k := by group
  · have hk' := hN _ (inv_mem hρ) k hk
    rw [inv_inv] at hk'
    have := hx _ hk'
    calc k * x = S.ρ h * (((S.ρ h)⁻¹ * k * S.ρ h) * ((S.ρ h)⁻¹ * x * S.ρ h)) * (S.ρ h)⁻¹ := by
          group
      _ = S.ρ h * (((S.ρ h)⁻¹ * x * S.ρ h) * ((S.ρ h)⁻¹ * k * S.ρ h)) * (S.ρ h)⁻¹ := by
          rw [this]
      _ = x * k := by group

section Hyperplane

variable (H : Hyp4 S g) (hK3 : Nat.card K = 3) (hN : NormalInMbar S K) (hfpf : FixFree S K)
include H hK3 hN hfpf

omit H hfpf in
theorem inv_of_not_mem_Ebar {x : S.O} (hx : x ∈ S.Lbar g) (hxE : x ∉ Ebar S g K) :
    ∀ k ∈ K, x * k * x⁻¹ = k⁻¹ := by
  rcases comm_or_inv hK3 (fun k hk => hN x (S.Lbar_le_Mbar g hx) k hk) with h | h
  · exact absurd ((mem_Ebar).mpr ⟨hx, h⟩) hxE
  · exact h

omit hK3 hN in
theorem exists_not_mem_Ebar : ∃ x ∈ S.Lbar g, x ∉ Ebar S g K := by
  by_contra hcon
  push Not at hcon
  apply cl_conj_z_ne_zero S H.conj_mem H.conj_ne
  apply hfpf
  intro k hk
  have hkN : k ∈ normalizer (S.Lbar g : Set S.O) := by
    rw [mem_normalizer_iff]
    intro y
    have hc : ∀ y ∈ S.Lbar g, k * y = y * k := fun y hy => ((mem_Ebar).mp (hcon y hy)).2 k hk
    constructor
    · intro hy
      rwa [hc y hy, mul_inv_cancel_right]
    · intro hy
      have e : y = k⁻¹ * (k * y * k⁻¹) * k := by group
      have h2 := hc _ hy
      have e2 : k⁻¹ * (k * y * k⁻¹) * k = k * y * k⁻¹ := by
        calc k⁻¹ * (k * y * k⁻¹) * k = k⁻¹ * ((k * y * k⁻¹) * k) := by group
          _ = k⁻¹ * (k * (k * y * k⁻¹)) := by rw [h2]
          _ = k * y * k⁻¹ := by group
      rw [e, e2]
      exact hy
  exact fix_of_mem_normalizer H hkN

omit H hfpf in
theorem mul_mem_Ebar {x y : S.O} (hx : x ∈ S.Lbar g) (hxE : x ∉ Ebar S g K)
    (hy : y ∈ S.Lbar g) (hyE : y ∉ Ebar S g K) : x * y ∈ Ebar S g K := by
  refine (mem_Ebar).mpr ⟨mul_mem hx hy, fun k hk => ?_⟩
  have h1 := inv_of_not_mem_Ebar hK3 hN hx hxE k hk
  have h2 := inv_of_not_mem_Ebar hK3 hN hy hyE k hk
  have e : x * y * k * (x * y)⁻¹ = k := by
    calc x * y * k * (x * y)⁻¹ = x * (y * k * y⁻¹) * x⁻¹ := by group
      _ = x * k⁻¹ * x⁻¹ := by rw [h2]
      _ = (x * k * x⁻¹)⁻¹ := by group
      _ = k := by rw [h1, inv_inv]
  calc k * (x * y) = x * y * k * (x * y)⁻¹ * (x * y) := by rw [e]
    _ = x * y * k := by group

end Hyperplane

end CFSG.LargeExtraspecial.S13
