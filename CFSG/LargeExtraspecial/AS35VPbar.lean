module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.OrthoF2PairsCases
public import CFSG.LargeExtraspecial.S12Defs
public import CFSG.LargeExtraspecial.S14W4LocDefs
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

namespace AS35V

theorem eq_one_or_eq_or_eq_inv_of_mem_zpowers {Γ : Type*} [Group Γ] {a x : Γ} (ha : a ^ 3 = 1)
    (hx : x ∈ zpowers a) : x = 1 ∨ x = a ∨ x = a⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have h3 : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha
  have hk : a ^ k = a ^ (k % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 3]
    rw [zpow_add, zpow_mul, h3, one_zpow, one_mul]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h1 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  rw [hk]
  set r := k % 3
  interval_cases r
  · exact Or.inl (zpow_zero a)
  · exact Or.inr (Or.inl (zpow_one a))
  · refine Or.inr (Or.inr ?_)
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, ha])

theorem orderOf_eq_three_of_pow {Γ : Type*} [Group Γ] {a : Γ} (ha : a ^ 3 = 1) (ha1 : a ≠ 1) :
    orderOf a = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime ha ha1

variable {G : Type} [Group G] [Finite G]

structure PbarFacts (S : Setting G) (τ : S.O) (P : Subgroup S.O) : Prop where
  typeA : IsTypeA S.q (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2
  le_Mbar : P ≤ S.Mbar
  mem : τ ∈ P
  extra : CFSG.IsExtraspecialPGroup 2 P
  card_eq : Nat.card P = 2 ^ (2 * S.width - 3)
  center_eq : ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x = 1 ∨ x = τ
  normalized : ∀ c ∈ S.Mbar, c * τ = τ * c → ∀ x ∈ P, c * x * c⁻¹ ∈ P
  trivial_comm : ∀ x ∈ P, ∀ v ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt),
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
  trivial_fix : ∀ x ∈ P, ∀ v ∈ fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt),
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)

namespace PbarFacts

variable {S : Setting G} {τ : S.O} {P : Subgroup S.O}

theorem mul_self (h : PbarFacts S τ P) : τ * τ = 1 := Subtype.ext h.typeA.2.2.1

theorem inv_eq (h : PbarFacts S τ P) : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right h.mul_self

theorem ne_one (h : PbarFacts S τ P) : τ ≠ 1 := fun e => h.typeA.2.1 (by rw [e]; rfl)

theorem mem_center (h : PbarFacts S τ P) : (⟨τ, h.mem⟩ : P) ∈ Subgroup.center P := by
  obtain ⟨-, -, -, hc⟩ := h.extra
  have : Nontrivial (Subgroup.center P) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hc]
    norm_num
  obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center P)
  have hcm : ∀ y ∈ P, ((c : P) : S.O) * y = y * c := by
    intro y hy
    exact (congrArg Subtype.val (mem_center_iff.mp c.2 ⟨y, hy⟩)).symm
  rcases h.center_eq _ (c : P).2 hcm with h1 | h1
  · exact absurd (Subtype.ext (Subtype.ext h1)) hc1
  · have e : (c : P) = ⟨τ, h.mem⟩ := Subtype.ext h1
    rw [← e]
    exact c.2

theorem commute (h : PbarFacts S τ P) {x : S.O} (hx : x ∈ P) : x * τ = τ * x :=
  congrArg Subtype.val (mem_center_iff.mp h.mem_center ⟨x, hx⟩)

theorem mem_commutator (h : PbarFacts S τ P) : (⟨τ, h.mem⟩ : P) ∈ commutator P := by
  rw [h.extra.2.1]
  exact h.mem_center

theorem commutator_eq (h : PbarFacts S τ P) {x y : S.O} (hx : x ∈ P) (hy : y ∈ P) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = τ := by
  have hmem : ⁅(⟨x, hx⟩ : P), ⟨y, hy⟩⁆ ∈ Subgroup.center P := by
    rw [← h.extra.2.1]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  have hc : ∀ w ∈ P, x * y * x⁻¹ * y⁻¹ * w = w * (x * y * x⁻¹ * y⁻¹) := by
    intro w hw
    exact (congrArg Subtype.val (mem_center_iff.mp hmem ⟨w, hw⟩)).symm
  have hP : x * y * x⁻¹ * y⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)
  exact h.center_eq _ hP hc

theorem false_of_inverts (h : PbarFacts S τ P) {a : S.O} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hP : ∀ p ∈ P, p * a * p⁻¹ ∈ zpowers a) (hτ : τ * a * τ⁻¹ = a⁻¹) : False := by
  have key : ∀ p ∈ P, p * a * p⁻¹ = a ∨ p * a * p⁻¹ = a⁻¹ := by
    intro p hp
    rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers ha3 (hP p hp) with h1 | h1 | h1
    · refine absurd ?_ ha1
      calc a = p⁻¹ * (p * a * p⁻¹) * p := by group
        _ = 1 := by rw [h1]; group
    · exact Or.inl h1
    · exact Or.inr h1
  have keyinv : ∀ p : S.O, p * a * p⁻¹ = a⁻¹ → p⁻¹ * a * p = a⁻¹ := by
    intro p hpa
    have e : p * a⁻¹ * p⁻¹ = a := by
      rw [show p * a⁻¹ * p⁻¹ = (p * a * p⁻¹)⁻¹ by group, hpa, inv_inv]
    calc p⁻¹ * a * p = p⁻¹ * (p * a⁻¹ * p⁻¹) * p := by rw [e]
      _ = a⁻¹ := by group
  have keyfix : ∀ p : S.O, p * a * p⁻¹ = a → p⁻¹ * a * p = a := by
    intro p hpa
    calc p⁻¹ * a * p = p⁻¹ * (p * a * p⁻¹) * p := by rw [hpa]
      _ = a := by group
  have hci : ∀ g : S.O, g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := fun g => by group
  have hci' : ∀ g : S.O, g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := fun g => by group
  have hcomm : ∀ p ∈ P, ∀ q ∈ P, (p * q * p⁻¹ * q⁻¹) * a * (p * q * p⁻¹ * q⁻¹)⁻¹ = a := by
    intro p hp q hq
    have e : (p * q * p⁻¹ * q⁻¹) * a * (p * q * p⁻¹ * q⁻¹)⁻¹ =
        p * (q * (p⁻¹ * (q⁻¹ * a * q) * p) * q⁻¹) * p⁻¹ := by group
    rw [e]
    rcases key p hp with hp1 | hp1 <;> rcases key q hq with hq1 | hq1
    · rw [keyfix q hq1, keyfix p hp1, hq1, hp1]
    · rw [keyinv q hq1, hci' p, keyfix p hp1, hci q, hq1, inv_inv, hp1]
    · rw [keyfix q hq1, keyinv p hp1, hci q, hq1, hci p, hp1, inv_inv]
    · rw [keyinv q hq1, hci' p, keyinv p hp1, inv_inv, hq1, hci p, hp1, inv_inv]
  have hle : commutator P ≤ (centralizer ({a} : Set S.O)).comap P.subtype := by
    rw [commutator_def, commutator_le]
    rintro ⟨p, hp⟩ - ⟨q, hq⟩ -
    rw [mem_comap, mem_centralizer_singleton_iff]
    have e := hcomm p hp q hq
    change (p * q * p⁻¹ * q⁻¹) * a = a * (p * q * p⁻¹ * q⁻¹)
    calc (p * q * p⁻¹ * q⁻¹) * a
        = ((p * q * p⁻¹ * q⁻¹) * a * (p * q * p⁻¹ * q⁻¹)⁻¹) * (p * q * p⁻¹ * q⁻¹) := by
          group
      _ = a * (p * q * p⁻¹ * q⁻¹) := by rw [e]
  have hτa := hle h.mem_commutator
  rw [mem_comap, mem_centralizer_singleton_iff] at hτa
  change τ * a = a * τ at hτa
  have e1 : a⁻¹ = a := by rw [← hτ, hτa]; group
  have e2 : a * a = 1 := by
    calc a * a = a * a⁻¹ := by rw [e1]
      _ = 1 := mul_inv_cancel a
  apply ha1
  calc a = a ^ 3 := by rw [pow_succ, pow_two, e2, one_mul]
    _ = 1 := ha3

theorem eq_one_of_commute (h : PbarFacts S τ P) {i : S.O} (hi3 : i ^ 3 = 1) (hi1 : i ≠ 1)
    (hτi : τ * i * τ⁻¹ = i⁻¹) {p : S.O} (hp : p ∈ P) (hpi : p * i = i * p) : p = 1 := by
  set T : S.Qt ≃ₗ[ZMod 2] S.Qt := (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hT
  set I : S.Qt ≃ₗ[ZMod 2] S.Qt := (i : S.Qt ≃ₗ[ZMod 2] S.Qt) with hI
  set Pl : S.Qt ≃ₗ[ZMod 2] S.Qt := (p : S.Qt ≃ₗ[ZMod 2] S.Qt) with hPl
  have hI3 : I ^ 3 = 1 := by rw [hI, ← Subgroup.coe_pow, hi3]; rfl
  have hPI : Pl * I = I * Pl := by rw [hPl, hI, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hpi]
  have hsA : IsTypeA S.q (I * T * I⁻¹) 2 := s12_isTypeA_conj h.typeA i.2
  have hτs : T * (I * T * I⁻¹) = I := by
    have e : τ * (i * τ * i⁻¹) = i := by
      have hτ' : τ⁻¹ = τ := h.inv_eq
      have e1 : τ * i * τ = i⁻¹ := by rw [← hτi, hτ']
      calc τ * (i * τ * i⁻¹) = (τ * i * τ) * i⁻¹ := by group
        _ = i⁻¹ * i⁻¹ := by rw [e1]
        _ = i ^ 3 * (i⁻¹ * i⁻¹) := by rw [hi3, one_mul]
        _ = i := by group
    have e' := congrArg (fun x : S.O => (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) e
    simpa [hT, hI] using e'
  have hord : orderOf (T * (I * T * I⁻¹)) = 3 := by
    rw [hτs, hI, Subgroup.orderOf_coe]
    exact orderOf_eq_three_of_pow hi3 hi1
  obtain ⟨-, hcomm, -, -, hfix⟩ :=
    commSpace_mul_of_orderOf_eq_three S.q_nondegenerate h.typeA hsA hord
  rw [hτs] at hcomm hfix
  have hcT : commSpace T ≤ fixSpace Pl := fun v hv => mem_fixSpace.mpr (h.trivial_comm p hp v hv)
  have hcS : commSpace (I * T * I⁻¹) ≤ fixSpace Pl := by
    rw [commSpace_conj]
    rintro _ ⟨v, hv, rfl⟩
    refine mem_fixSpace.mpr ?_
    change Pl (I v) = I v
    rw [← LinearEquiv.mul_apply, hPI, LinearEquiv.mul_apply, mem_fixSpace.mp (hcT hv)]
  have hcI : commSpace I ≤ fixSpace Pl := by
    rw [hcomm]
    exact sup_le hcT hcS
  have hfI : fixSpace I ≤ fixSpace Pl := by
    intro w hw
    have hwT : w ∈ fixSpace T := by
      rw [hfix] at hw
      exact hw.1
    have h1 : Pl w - w ∈ commSpace I := by
      rw [hcomm]
      exact Submodule.mem_sup_left (h.trivial_fix p hp w hwT)
    have h2 : Pl w - w ∈ fixSpace I := by
      refine Submodule.sub_mem _ (mem_fixSpace.mpr ?_) hw
      rw [← LinearEquiv.mul_apply, ← hPI, LinearEquiv.mul_apply, mem_fixSpace.mp hw]
    have h3 : Pl w - w = 0 := by
      have := OrthoF2.commSpace_inf_fixSpace_eq_bot_of_pow_three hI3
      rw [eq_bot_iff] at this
      exact (Submodule.mem_bot _).mp (this ⟨h1, h2⟩)
    exact mem_fixSpace.mpr (sub_eq_zero.mp h3)
  have hsup : fixSpace I ⊔ commSpace I = ⊤ := by
    have hinf := OrthoF2.commSpace_inf_fixSpace_eq_bot_of_pow_three hI3
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (fixSpace I) (commSpace I)
    rw [inf_comm, hinf, finrank_bot, add_zero, add_comm,
      finrank_commSpace_add_finrank_fixSpace] at h1
    exact Submodule.eq_top_of_finrank_eq h1
  have htop : fixSpace Pl = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le hfI hcI
  refine Subtype.ext (OrthoF2.eq_one_of_forall_apply_eq fun v => ?_)
  have hv : v ∈ fixSpace Pl := htop ▸ Submodule.mem_top
  exact mem_fixSpace.mp hv

end PbarFacts

end AS35V

end CFSG.LargeExtraspecial
