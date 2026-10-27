module

public import CFSG.Holt.H78.Sec4Defs
import CFSG.Holt.H78.Sec4Prop43A
import CFSG.Holt.H78.Sec4Box
import CFSG.Holt.H78.Sec4CCLMatch
import CFSG.Holt.H78.Sec4AltSylow
import CFSG.Holt.H78.Sec4SEAut
import CFSG.Holt.H78.KernelSplit
public import CFSG.Holt.H78.Sections

public section

namespace CFSG.Holt.H78

open Equiv Equiv.Perm MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

section GroupFacts

variable {A : Type*} [Group A]

theorem isPGroup_zpowers_of_pow_two_pow_eq_one {x : A} {a : ℕ} (hx : x ^ 2 ^ a = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨a, Subtype.ext ?_⟩
  change (x ^ n) ^ 2 ^ a = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem exists_odd_pow_isPGroup [Finite A] (c : A) :
    ∃ m : ℕ, Odd m ∧ ∃ a : ℕ, (c ^ m) ^ 2 ^ a = 1 := by
  obtain ⟨a, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  exact ⟨m, hm, a, by rw [← pow_mul, mul_comm, ← hcm, pow_orderOf_eq_one]⟩

theorem pow_eq_self_of_odd {y : A} (hy : y * y = 1) {m : ℕ} (hm : Odd m) : y ^ m = y := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, hy, one_pow, one_mul]

theorem exists_mem_zpowers_orderOf_eq_two [Finite A] {B : Type*} [Group B] (f : A →* B) {h : A}
    (hh : f h * f h = 1) (hh1 : f h ≠ 1) (hker : ∀ k : A, f k = 1 → Odd (orderOf k)) :
    ∃ u ∈ Subgroup.zpowers h, f u = f h ∧ orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, a, ha⟩ := exists_odd_pow_isPGroup h
  have hfu : f (h ^ m) = f h := by rw [map_pow, pow_eq_self_of_odd hh hm]
  refine ⟨h ^ m, Subgroup.npow_mem_zpowers h m, hfu, ?_⟩
  have hu1 : h ^ m ≠ 1 := fun h1 => hh1 (by rw [← hfu, h1, map_one])
  have hsq : (h ^ m) ^ 2 = 1 := by
    have hodd := hker ((h ^ m) ^ 2) (by rw [map_pow, hfu, sq, hh])
    obtain ⟨b, hb⟩ : ∃ b, orderOf ((h ^ m) ^ 2) = 2 ^ b := by
      have hdvd : orderOf ((h ^ m) ^ 2) ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one (by
        rw [← pow_mul, mul_comm, pow_mul, ha, one_pow])
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨b, hb⟩
    rw [hb] at hodd
    have hb0 : b = 0 := by
      by_contra hb0
      exact Nat.not_even_iff_odd.mpr hodd ((Nat.even_pow' hb0).mpr even_two)
    rw [hb0, pow_zero, orderOf_eq_one_iff] at hb
    exact hb
  exact orderOf_eq_prime hsq hu1

theorem exists_mem_conj_commute_of_odd [Finite A] {O : Subgroup A} (hO : Odd (Nat.card O))
    {x u : A} (hx : x * x = 1) (hu : u * u = 1) (hxu : (x * u) ^ 2 ∈ O) :
    ∃ p ∈ O, Commute (p * x * p⁻¹) u := by
  set r := x * u with hr
  set m := orderOf (r ^ 2) with hm
  have hmodd : Odd m := Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard O hxu)
  have hr2m : r ^ m * r ^ m = 1 := by rw [← pow_add, ← two_mul, pow_mul, hm, pow_orderOf_eq_one]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hrinv : r⁻¹ = u * x := by rw [hr, mul_inv_rev, hxi, hui]
  have hconj : ∀ g : A, g * g = 1 → g * r * g = r⁻¹ → ∀ n : ℕ, g * r ^ n * g = (r ^ n)⁻¹ := by
    intro g hg hgr n
    have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
    have h := map_pow (MulAut.conj g) r n
    simp only [MulAut.conj_apply, hgi] at h
    rw [h, hgr, inv_pow]
  have hur : u * r * u = r⁻¹ := by rw [hrinv, hr, mul_assoc, mul_assoc, hu, mul_one]
  have hxr : x * r * x = r⁻¹ := by rw [hrinv, hr, ← mul_assoc, hx, one_mul]
  have hrm : (r ^ m)⁻¹ = r ^ m := inv_eq_of_mul_eq_one_right hr2m
  set x' := u * r ^ m with hx'
  have hcomm : x' * u = u * x' := by
    rw [hx', hconj u hu hur m, hrm, ← mul_assoc, hu, one_mul]
  have hx'x' : x' * x' = 1 := by
    rw [hx', ← mul_assoc, hconj u hu hur m, hrm, hr2m]
  have hux : u = x * r := by rw [hr, ← mul_assoc, hx, one_mul]
  have hx'eq : x' = (r ^ (m + 1))⁻¹ * x := by
    rw [← hconj x hx hxr (m + 1), mul_assoc, hx, mul_one, hx', hux, pow_succ', mul_assoc]
  have hqO : (r ^ (m + 1))⁻¹ ∈ O := by
    obtain ⟨j, hj⟩ := hmodd
    refine inv_mem ?_
    rw [show m + 1 = 2 * (j + 1) by omega, pow_mul]
    exact pow_mem hxu _
  obtain ⟨p, hp, hpx⟩ := exists_conj_eq_mul_of_odd_orderOf
    (Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard O hqO)) hx (by rw [← hx'eq, hx'x'])
  refine ⟨p, Subgroup.zpowers_le.mpr hqO hp, ?_⟩
  rw [Commute, SemiconjBy, hpx, ← hx'eq, hcomm]

end GroupFacts

section Perm

variable {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

theorem exists_perm_mul_self_eq_one_apply_eq_iff (F : Set Ψ) [DecidablePred (· ∈ F)]
    (hF : Even (Fintype.card {x // x ∉ F})) :
    ∃ σ : Perm Ψ, σ * σ = 1 ∧ (∀ x, σ x = x ↔ x ∈ F) ∧
      sign σ = (-1) ^ (Fintype.card {x // x ∉ F} / 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ, hτfix⟩ := exists_mul_self_eq_one_forall_apply_ne hF
  refine ⟨ofSubtype τ, by rw [← map_mul, hτ, map_one], fun x => ?_, ?_⟩
  · by_cases hx : x ∈ F
    · exact iff_of_true (ofSubtype_apply_of_not_mem τ (not_not.mpr hx)) hx
    · rw [ofSubtype_apply_of_mem τ hx]
      exact iff_of_false (fun h => hτfix ⟨x, hx⟩ (Subtype.ext h)) hx
  · have hτ2 : τ ^ 2 = 1 := by rw [sq, hτ]
    have hct := cycleType_of_pow_prime_eq_one hτ2
    have hsupp : τ.support = Finset.univ := Finset.eq_univ_of_forall fun x =>
      Perm.mem_support.mpr (hτfix x)
    have hsum := sum_cycleType τ
    rw [hct, Multiset.sum_replicate, smul_eq_mul, hsupp, Finset.card_univ] at hsum
    rw [sign_ofSubtype, sign_of_cycleType, hct, Multiset.sum_replicate, Multiset.card_replicate,
      smul_eq_mul, pow_add, pow_mul', Int.units_sq, one_pow, one_mul, ← hsum,
      Nat.mul_div_cancel _ two_pos]

theorem permCongr_mem_longInv {X Y : Type*} (e : X ≃ Y) {y : Perm X}
    (hy : y ∈ longInv (Perm X) X) : e.permCongr y ∈ longInv (Perm Y) Y := by
  obtain ⟨x₀, hx₀, hu⟩ := hy.2
  refine ⟨(MulEquiv.orderOf_eq (Equiv.permCongrHom e) y).trans hy.1, e x₀, ?_, fun z hz => ?_⟩
  · change e (y (e.symm (e x₀))) = e x₀
    rw [Equiv.symm_apply_apply]
    exact congrArg e hx₀
  · have hz' : e (y (e.symm z)) = z := hz
    have hfix : y • e.symm z = e.symm z := by
      change y (e.symm z) = e.symm z
      conv_rhs => rw [← hz']
      rw [Equiv.symm_apply_apply]
    rw [← hu _ hfix, Equiv.apply_symm_apply]

theorem exists_mem_longInv_perm_commute_of_fixed {ū : Perm Ψ} (hū : ū * ū = 1)
    {P : Fin 5 → Ψ} (hP : Function.Injective P) (hfix : ∀ y, ū y = y ↔ ∃ m, P m = y)
    {i j l : Fin 5} (hidx : [0, 1, i, j, l].Nodup) :
    ∃ x ∈ longInv (Perm Ψ) Ψ, Commute x ū ∧ x (P 0) = P 1 ∧ x (P i) = P i ∧
      x * ū⁻¹ ∈ alternatingGroup Ψ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hidx
  obtain ⟨⟨h01, h0i, h0j, h0l⟩, ⟨h1i, h1j, h1l⟩, ⟨hij, hil⟩, hjl, -⟩ := hidx
  have key : ∀ m : Fin 5, m = 0 ∨ m = 1 ∨ m = i ∨ m = j ∨ m = l := by
    revert h01 h0i h0j h0l h1i h1j h1l hij hil hjl
    revert i j l
    decide
  have hne : ∀ {m m' : Fin 5}, m ≠ m' → P m ≠ P m' := fun h e => h (hP e)
  set σ : Perm Ψ := swap (P 0) (P 1) * swap (P j) (P l) with hσ
  have hcomm₁ : Commute (swap (P 0) (P 1)) (swap (P j) (P l)) :=
    (disjoint_swap_swap (by simp [hne h01, hne h0j, hne h0l, hne h1j, hne h1l, hne hjl])).commute
  have hσσ : σ ^ 2 = 1 := by
    rw [hσ, hcomm₁.mul_pow, sq, sq, swap_mul_self, swap_mul_self, one_mul]
  have hūP : ∀ m, ū (P m) = P m := fun m => (hfix _).mpr ⟨m, rfl⟩
  have hσū : Commute σ ū := by
    have h : ∀ x y : Ψ, ū x = x → ū y = y → Commute (swap x y) ū := fun x y hx hy => by
      have h' := swap_apply_apply ū x y
      rw [hx, hy] at h'
      rw [Commute, SemiconjBy]
      conv_lhs => rw [h']
      rw [inv_mul_cancel_right]
    exact (h _ _ (hūP 0) (hūP 1)).mul_left (h _ _ (hūP j) (hūP l))
  have hσfix : ∀ y, y ≠ P 0 → y ≠ P 1 → y ≠ P j → y ≠ P l → σ y = y := fun y h0 h1 hj hl => by
    rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne hj hl, swap_apply_of_ne_of_ne h0 h1]
  have hσ0 : σ (P 0) = P 1 := by
    rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne (hne h0j) (hne h0l), swap_apply_left]
  have hσi : σ (P i) = P i := hσfix _ (hne h0i).symm (hne h1i).symm (hne hij) (hne hil)
  have hσ1 : σ (P 1) = P 0 := by
    rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne (hne h1j) (hne h1l), swap_apply_right]
  have hσj : σ (P j) = P l := by
    rw [hσ, Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne (hne h0l).symm (hne h1l).symm]
  have hσl : σ (P l) = P j := by
    rw [hσ, Perm.mul_apply, swap_apply_right,
      swap_apply_of_ne_of_ne (hne h0j).symm (hne h1j).symm]
  have hxx : σ * ū * (σ * ū) = 1 := by
    rw [← sq, hσū.mul_pow, hσσ, sq, hū, one_mul]
  have hxfix : ∀ y, (σ * ū) • y = y ↔ y = P i := fun y => by
    rw [Perm.smul_def, Perm.mul_apply]
    constructor
    · intro hy
      by_cases huy : ū y = y
      · obtain ⟨m, rfl⟩ := (hfix y).mp huy
        rw [hūP] at hy
        rcases key m with rfl | rfl | rfl | rfl | rfl
        · exact absurd (hσ0.symm.trans hy) (hne h01).symm
        · exact absurd (hσ1.symm.trans hy) (hne h01)
        · rfl
        · exact absurd (hσj.symm.trans hy) (hne hjl).symm
        · exact absurd (hσl.symm.trans hy) (hne hjl)
      · have hnP : ∀ m, ū y ≠ P m := fun m h => huy (by
          have h2 : ū (ū y) = ū y := by rw [h, hūP]
          rw [← Perm.mul_apply, hū, Perm.one_apply] at h2
          exact h2.symm)
        rw [hσfix _ (hnP 0) (hnP 1) (hnP j) (hnP l)] at hy
        exact absurd hy huy
    · rintro rfl
      rw [hūP, hσi]
  refine ⟨σ * ū, (mem_longInvAt_of_mul_self hxx hxfix ⟨P 0, hne h0i⟩).1, hσū.mul_left
    (Commute.refl ū), by rw [Perm.mul_apply, hūP, hσ0], by rw [Perm.mul_apply, hūP, hσi], ?_⟩
  rw [mul_inv_cancel_right, mem_alternatingGroup, hσ, map_mul, sign_swap (hne h01),
    sign_swap (hne hjl)]
  decide

end Perm

theorem fusionIsSylowIn_inf_of_forall_conj_mem {K : Type*} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] {S H N : Subgroup K} (hS : fusionIsSylowIn p S H) (hNH : N ≤ H)
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) : fusionIsSylowIn p (S ⊓ N) N := by
  refine ⟨inf_le_right, hS.2.1.to_le inf_le_left, fun P hPN hP hle => ?_⟩
  obtain ⟨R, hPR, hR⟩ := exists_fusionIsSylowIn_ge hP (hPN.trans hNH)
  obtain ⟨k, hk, hkR⟩ := exists_mem_conj_of_fusionIsSylowIn hS hR
  have hconj : ∀ x ∈ P, k⁻¹ * x * k ∈ S ⊓ N := fun x hx => ⟨(hkR x).mp (hPR hx), by
    simpa using hN k⁻¹ (inv_mem hk) x (hPN hx)⟩
  have hcard : Nat.card P ≤ Nat.card ↥(S ⊓ N) := Nat.card_le_card_of_injective
    (fun x : P => (⟨k⁻¹ * x * k, hconj x x.2⟩ : ↥(S ⊓ N))) (fun x y h => by
      have h' := congrArg Subtype.val h
      simp only [mul_left_inj, mul_right_inj] at h'
      exact Subtype.ext h')
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

section Factor


theorem IsHoltFactor.exists_commute_mul_self_eq_one {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ]
    {M : Subgroup (Perm Ψ)} (hM : IsHoltFactor M) {m : Perm Ψ} (hm : m ∈ M) (hm2 : m * m = 1)
    (hm1 : m ≠ 1) {c₁ c₂ c₃ : Ψ} (h₁ : m c₁ = c₁) (h₂ : m c₂ = c₂) (h₃ : m c₃ = c₃) :
    ∃ m' ∈ M, m' * m' = 1 ∧ m' ≠ 1 ∧ m' ≠ m ∧ m * m' = m' * m ∧ m' c₁ = c₁ ∧ m' c₂ = c₂ ∧
      m' c₃ = c₃ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hM with ⟨rfl, h7⟩ | hSE
  ·
    have hm2' : m ^ 2 = 1 := by rw [sq, hm2]
    have hct := cycleType_of_pow_prime_eq_one hm2'
    have hsum := sum_cycleType m
    rw [hct, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hsign := hm
    rw [mem_alternatingGroup, sign_of_cycleType, hct, Multiset.sum_replicate,
      Multiset.card_replicate, smul_eq_mul, pow_add, pow_mul', Int.units_sq, one_pow,
      one_mul] at hsign
    have heven : Even m.cycleType.card := by
      by_contra hodd
      rw [Int.units_pow_eq_pow_mod_two, Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hodd),
        pow_one] at hsign
      exact absurd hsign (by decide)
    have hpos : 0 < m.cycleType.card := by
      rw [Multiset.card_pos]
      intro h0
      exact hm1 (cycleType_eq_zero.mp h0)
    have h4 : 4 ≤ m.support.card := by
      obtain ⟨t, ht⟩ := heven
      omega
    obtain ⟨a₁, ha₁⟩ : ∃ a₁, m a₁ ≠ a₁ := by
      by_contra h
      push Not at h
      exact hm1 (Equiv.ext h)
    set a₂ := m a₁ with ha₂def
    have ha₂ : m a₂ = a₁ := by rw [ha₂def, ← Perm.mul_apply, hm2, Perm.one_apply]
    obtain ⟨a₃, ha₃⟩ : ∃ a₃ ∈ (m.support.erase a₁).erase a₂, True := by
      have : 0 < ((m.support.erase a₁).erase a₂).card := by
        have h1 := Finset.pred_card_le_card_erase (s := m.support) (a := a₁)
        have h2 := Finset.pred_card_le_card_erase (s := m.support.erase a₁) (a := a₂)
        omega
      obtain ⟨a₃, h⟩ := Finset.card_pos.mp this
      exact ⟨a₃, h, trivial⟩
    obtain ⟨ha₃₂, ha₃₁, ha₃m⟩ : a₃ ≠ a₂ ∧ a₃ ≠ a₁ ∧ m a₃ ≠ a₃ := by
      simp only [Finset.mem_erase, Perm.mem_support] at ha₃
      exact ⟨ha₃.1.1, ha₃.1.2.1, ha₃.1.2.2⟩
    set a₄ := m a₃ with ha₄def
    have ha₄ : m a₄ = a₃ := by rw [ha₄def, ← Perm.mul_apply, hm2, Perm.one_apply]
    have h12 : a₁ ≠ a₂ := fun h => ha₁ h.symm
    have h34 : a₃ ≠ a₄ := fun h => ha₃m h.symm
    have h14 : a₁ ≠ a₄ := fun h => ha₃₂ (by rw [← ha₄, ← h, ha₂def])
    have h24 : a₂ ≠ a₄ := fun h => ha₃₁ (by rw [← ha₄, ← h, ha₂])
    have hdisj : Commute (swap a₁ a₃) (swap a₂ a₄) := (disjoint_swap_swap (by
      simp [h12, ha₃₁.symm, h14, ha₃₂, h24, h34])).commute
    have hfixc : ∀ c, m c = c → (swap a₁ a₃ * swap a₂ a₄) c = c := fun c hc => by
      have hc1 : c ≠ a₁ := fun h => ha₁ (by rw [ha₂def, ← h, hc])
      have hc2 : c ≠ a₂ := fun h => h12 (by rw [← ha₂, ← h, hc])
      have hc3 : c ≠ a₃ := fun h => ha₃m (by rw [ha₄def, ← h, hc])
      have hc4 : c ≠ a₄ := fun h => h34 (by rw [← ha₄, ← h, hc])
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hc2 hc4, swap_apply_of_ne_of_ne hc1 hc3]
    refine ⟨swap a₁ a₃ * swap a₂ a₄, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_alternatingGroup, map_mul, sign_swap ha₃₁.symm, sign_swap h24]
      decide
    · rw [← sq, hdisj.mul_pow, sq, sq, swap_mul_self, swap_mul_self, one_mul]
    · intro h
      have := congrArg (fun π : Perm Ψ => π a₁) h
      simp only [Perm.mul_apply, Perm.one_apply, swap_apply_of_ne_of_ne h12 h14,
        swap_apply_left] at this
      exact ha₃₁ this
    · intro h
      have := congrArg (fun π : Perm Ψ => π a₁) h
      simp only [Perm.mul_apply, swap_apply_of_ne_of_ne h12 h14, swap_apply_left] at this
      exact ha₃₂ this
    · have hconj : m * (swap a₁ a₃ * swap a₂ a₄) * m⁻¹ = swap a₁ a₃ * swap a₂ a₄ := by
        rw [show m * (swap a₁ a₃ * swap a₂ a₄) * m⁻¹ = (m * swap a₁ a₃ * m⁻¹) *
          (m * swap a₂ a₄ * m⁻¹) by group, ← swap_apply_apply, ← swap_apply_apply, ← ha₂def,
          ← ha₄def, ha₂, ha₄]
        exact hdisj.eq.symm
      rwa [mul_inv_eq_iff_eq_mul] at hconj
    · exact ⟨hfixc c₁ h₁, hfixc c₂ h₂, hfixc c₃ h₃⟩
  ·
    obtain ⟨n, i, e, hA⟩ := hSE.exists_isBenderAction
    have hord : orderOf (⟨m, hm⟩ : M) = 2 := orderOf_eq_prime
      (Subtype.ext (by rw [Subgroup.coe_pow, sq, hm2]; rfl)) fun h => hm1 (congrArg Subtype.val h)
    obtain ⟨c, -, hcu⟩ := hA.existsUnique_fixed hord
    have hc₂ : c₂ = c₁ := (hcu c₂ h₂).trans (hcu c₁ h₁).symm
    have hc₃ : c₃ = c₁ := (hcu c₃ h₃).trans (hcu c₁ h₁).symm
    have hmR := hSE.mem_rootCenter_seRadical hm h₁ hm2
    obtain ⟨m', hm'R, hm'1, hm'm⟩ :
        ∃ m' ∈ CFSG.GH74.Uniqueness.Bender.rootCenter (seRadical M c₁), m' ≠ 1 ∧ m' ≠ m := by
      by_contra h
      push Not at h
      have hsub : ((CFSG.GH74.Uniqueness.Bender.rootCenter (seRadical M c₁) :
          Subgroup (Perm Ψ)) : Set (Perm Ψ)) ⊆ {1, m} := fun z hz => by
        by_cases hz1 : z = 1
        · exact Or.inl hz1
        · exact Or.inr (h z hz hz1)
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 := Set.ncard_insert_le (1 : Perm Ψ) {m}
      rw [Set.ncard_singleton] at h2
      have h3 := hA.card_rootCenter_seRadical c₁
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq] at h3
      have := hA.four_le_q
      omega
    have hm'Rad := CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hm'R
    have hm'c : m' c₁ = c₁ := apply_eq_of_mem_seRadical hm'Rad
    refine ⟨m', seRadical_le hm'Rad, hSE.mul_self_eq_one_of_mem_rootCenter hm'R, hm'1, hm'm,
      (CFSG.GH74.Uniqueness.Bender.mem_rootCenter_iff.mp hm'R).2 m
        (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hmR), hm'c, ?_, ?_⟩
    · rw [hc₂]; exact hm'c
    · rw [hc₃]; exact hm'c

end Factor

section KnownGroup

variable {K : Type} [Group K] [Finite K] {X : Type} [MulAction K X] [Finite X] [FaithfulSMul K X]

namespace HoltData

theorem exists_involution_fixSet_five (hK : IsStarGroup K X)
    (hB : HoltTheorem1Below (Nat.card K) (Nat.card X + 1)) (D : HoltData K X) {k : D.ι}
    (hk : ∀ k', k' = k) (hA : factorImage K X (D.L k) (D.ρ k) = alternatingGroup (D.Ψc k))
    (h3 : Fintype.card (D.Ψc k) % 4 = 3) (p : Fin 5 → X)
    (hp : Function.Injective fun i => D.coord (p i) k) :
    ∃ u ∈ jHull K X, orderOf u = 2 ∧ ∃ q : Fin 5 → X, (∀ i, D.coord (q i) = D.coord (p i)) ∧
      (∀ i, u • q i = q i) ∧ (∀ x, u • x = x → ∃ i, x = q i) ∧
      (∀ i x, D.coord x = D.coord (p i) → u • x = x → x = q i) ∧
      ∀ i : Fin 5, 2 ≤ i.val → ∃ t ∈ longInv K X, t • q 0 = q 1 ∧ t • q i = q i := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcoord : ∀ x y : X, D.coord x = D.coord y ↔ D.coord x k = D.coord y k := fun x y =>
    ⟨fun h => congrFun h k, fun h => funext fun k' => by obtain rfl := hk k'; exact h⟩
  have hker : jOrbitKernel K X = jOddCore K X := D.ker_outer ⟨k, hA, h3⟩
  have hρker : ∀ h : jHull K X, D.ρ k h = 1 → (h : K) ∈ jOddCore K X := fun h h1 => by
    rw [← hker, D.mem_jOrbitKernel_iff_rho]
    intro k'
    obtain rfl := hk k'
    exact h1
  set P : Fin 5 → D.Ψc k := fun i => D.coord (p i) k with hPdef
  have hΨ7 : 7 ≤ Fintype.card (D.Ψc k) := by have := D.five_le_card k; omega
  have hPc : Fintype.card {x // x ∉ Set.range P} = Fintype.card (D.Ψc k) - 5 := by
    rw [Fintype.card_subtype_compl, (Fintype.card_congr (Equiv.ofInjective P hp)).symm.trans
      (Fintype.card_fin 5)]
  obtain ⟨ū, hū2, hūfix, hūsign⟩ := exists_perm_mul_self_eq_one_apply_eq_iff (Set.range P)
    (by rw [hPc]; exact ⟨(Fintype.card (D.Ψc k) - 5) / 2, by omega⟩)
  have hūsign' : sign ū = -1 := by
    rw [hūsign, hPc, show (Fintype.card (D.Ψc k) - 5) / 2 =
      2 * ((Fintype.card (D.Ψc k) - 7) / 4) + 1 by omega, pow_succ, pow_mul, Int.units_sq,
      one_pow, one_mul]
  have hsignt : sign (D.ρ k D.tHull) = -1 := by
    rw [sign_of_mem_longInv_perm (D.rho_mem_longInv D.t_mem k), show (Fintype.card (D.Ψc k) - 1)
      / 2 = 2 * ((Fintype.card (D.Ψc k) - 3) / 4) + 1 by omega, pow_succ, pow_mul,
      Int.units_sq, one_pow, one_mul]
  have hMrange : ∀ π ∈ alternatingGroup (D.Ψc k), π ∈ (D.ρ k).range := fun π hπ =>
    Subgroup.map_le_range _ _ (show π ∈ factorImage K X (D.L k) (D.ρ k) by rw [hA]; exact hπ)
  have hrange : ∀ π : Perm (D.Ψc k), sign π = -1 → π ∈ (D.ρ k).range := fun π hπ => by
    have h1 : π * (D.ρ k D.tHull)⁻¹ ∈ alternatingGroup (D.Ψc k) := by
      rw [mem_alternatingGroup, map_mul, map_inv, hπ, hsignt, mul_inv_cancel]
    have h2 := mul_mem (hMrange _ h1) (⟨D.tHull, rfl⟩ : D.ρ k D.tHull ∈ (D.ρ k).range)
    rwa [inv_mul_cancel_right] at h2
  obtain ⟨h₀, hh₀⟩ := hrange ū hūsign'
  have hū1 : ū ≠ 1 := fun h => by
    rw [h, map_one] at hūsign'
    exact absurd hūsign' (by decide)
  obtain ⟨u, -, hu, hu2⟩ := exists_mem_zpowers_orderOf_eq_two (D.ρ k) (h := h₀)
    (by rw [hh₀, hū2]) (by rw [hh₀]; exact hū1) fun k' hk' => by
      rw [← Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat odd_card_jOddCore (Subgroup.orderOf_dvd_natCard _ (hρker k' hk'))
  rw [hh₀] at hu
  have huJ : (u : K) ∈ jHull K X := u.2
  have hu2' : orderOf (u : K) = 2 := by rw [Subgroup.orderOf_coe, hu2]
  have husoc : (u : K) ∉ D.socPre := fun h => by
    have hM : D.ρ k u ∈ factorImage K X (D.L k) (D.ρ k) := D.rho_mem_M_of_mem_socPre h k
    rw [hA, mem_alternatingGroup, hu, hūsign'] at hM
    exact absurd hM (by decide)
  have hsmul : ∀ x : X, D.coord ((u : K) • x) k = ū (D.coord x k) := fun x => by
    rw [D.coord_smul u x k, hu]
  have hstab : ∀ i, (u : K) • p i ∈ orbit (jOddCore K X) (p i) := fun i => by
    rw [← D.coord_eq_iff, hcoord, hsmul, (hūfix _).mpr ⟨i, rfl⟩]
  choose q hq hqu using fun i => (D.lemma_2_4_iv hK hB huJ hu2' (hstab i)).2 husoc
  have hqcoord : ∀ i, D.coord (q i) = D.coord (p i) := fun i =>
    ((D.coord_eq_iff _ _).mpr (hq i).1).symm
  have hquniq : ∀ i x, D.coord x = D.coord (p i) → (u : K) • x = x → x = q i :=
    fun i x hx hux => hqu i x ⟨(D.coord_eq_iff _ _).mp hx.symm, hux⟩
  have hfixq : ∀ x, (u : K) • x = x → ∃ i, x = q i := fun x hux => by
    have h1 : ū (D.coord x k) = D.coord x k := by rw [← hsmul, hux]
    obtain ⟨i, hi⟩ := (hūfix _).mp h1
    exact ⟨i, hquniq i x ((hcoord _ _).mpr hi.symm) hux⟩
  refine ⟨u, huJ, hu2', q, hqcoord, fun i => (hq i).2, hfixq, hquniq, fun i hi => ?_⟩
  obtain ⟨j, l, hidx⟩ : ∃ j l : Fin 5, [0, 1, i, j, l].Nodup := by
    fin_cases i
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
    · exact ⟨3, 4, by decide⟩
    · exact ⟨2, 4, by decide⟩
    · exact ⟨2, 3, by decide⟩
  obtain ⟨xb, hxb, hxbū, hxb0, hxbi, hxbalt⟩ := exists_mem_longInv_perm_commute_of_fixed hū2 hp
    (fun y => (hūfix y).trans Set.mem_range) hidx
  have hxbrange : xb ∈ (D.ρ k).range := by
    have h := mul_mem (hMrange _ hxbalt) (⟨h₀, hh₀⟩ : ū ∈ (D.ρ k).range)
    rwa [inv_mul_cancel_right] at h
  obtain ⟨x, hxJ, hxρ⟩ := D.exists_mem_longInv_rho_eq
    (Function.update (fun k' => D.ρ k' D.tHull) k xb)
    (fun k' => by obtain rfl := hk k'; rw [Function.update_self]; exact hxbrange)
    (fun k' => by obtain rfl := hk k'; rw [Function.update_self]; exact hxb)
  have hxρk : D.ρ k x = xb := by rw [hxρ k, Function.update_self]
  have huu : (u : K) * u = 1 := by rw [← sq, ← hu2', pow_orderOf_eq_one]
  have hxu : ((x : K) * u) ^ 2 ∈ jOddCore K X := hρker ((x * u) ^ 2) (by
    rw [map_pow, map_mul, hxρk, hu, hxbū.mul_pow, sq, sq, mul_self_eq_one_of_mem_longInv hxb,
      hū2, one_mul])
  obtain ⟨o, ho, hoc⟩ := exists_mem_conj_commute_of_odd odd_card_jOddCore
    (mul_self_eq_one_of_mem_longInv hxJ) huu hxu
  have hoJ : o ∈ jHull K X := jOddCore_le_jHull ho
  set t : jHull K X := ⟨o, hoJ⟩ * x * ⟨o, hoJ⟩⁻¹ with ht
  have htρ : D.ρ k t = xb := by
    rw [ht, map_mul, map_mul, map_inv, D.rho_eq_one_of_mem_jOddCore (h := ⟨o, hoJ⟩) ho k,
      one_mul, inv_one, mul_one, hxρk]
  have htu : ∀ y : X, (u : K) • (t : K) • y = (t : K) • (u : K) • y := fun y => by
    rw [← mul_smul, ← mul_smul, show ((u : K) * t) = t * u from (hoc.eq).symm]
  have htq : ∀ m m' : Fin 5, xb (P m) = P m' → (t : K) • q m = q m' := fun m m' hm => by
    refine hquniq m' _ ((hcoord _ _).mpr ?_) (by rw [htu, (hq m).2])
    rw [D.coord_smul t (q m) k, htρ, (hcoord _ _).mp (hqcoord m)]
    exact hm
  exact ⟨t, conj_mem_longInv hxJ o, htq 0 1 hxb0, htq i i hxbi⟩

end HoltData

end KnownGroup

section Section

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem coe_pow_apply_eq_pow_smul {V : Subgroup G} {π : Perm (fixSet Ω V)} {c : G}
    (hc : ∀ ω : fixSet Ω V, (π ω : Ω) = c • (ω : Ω)) (n : ℕ) (ω : fixSet Ω V) :
    ((π ^ n) ω : Ω) = c ^ n • (ω : Ω) := by
  induction n generalizing ω with
  | zero => rw [pow_zero, pow_zero, one_smul, Perm.one_apply]
  | succ n ih => rw [pow_succ, pow_succ, Perm.mul_apply, ih, hc, mul_smul]

omit [Fintype Ω] [DecidableEq Ω] in
theorem exists_isPGroup_zpowers_of_mem_centralizerImage {V : Subgroup G}
    {π : Perm (fixSet Ω V)} (hπ : π ∈ centralizerImage Ω V) (hπ2 : π * π = 1) :
    ∃ c ∈ Subgroup.centralizer (V : Set G), IsPGroup 2 (Subgroup.zpowers c) ∧
      ∀ ω : fixSet Ω V, (π ω : Ω) = c • (ω : Ω) := by
  obtain ⟨c, hcV, hc⟩ := mem_centralizerImage.mp hπ
  obtain ⟨m, hm, a, ha⟩ := exists_odd_pow_isPGroup c
  refine ⟨c ^ m, pow_mem hcV m, isPGroup_zpowers_of_pow_two_pow_eq_one ha, fun ω => ?_⟩
  rw [← coe_pow_apply_eq_pow_smul hc m ω, pow_eq_self_of_odd hπ2 hm]

variable [FaithfulSMul G Ω]

theorem Sec4Setting.odd_card_inf_fixingSubgroup_centralizerImage (hS : Sec4Setting G Ω)
    {α β : Ω} (hαβ : α ≠ β) {X : Subgroup G} (hX : IsPGroup 2 X) {Λ : Set Ω}
    (hΛΔ : Λ ⊆ holtDelta G Ω α β)
    (hsyl : fusionIsSylowIn 2 X (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ))
    {a b : fixSet Ω X} (ha : (a : Ω) = α) (hb : (b : Ω) = β) :
    Odd (Nat.card ↥(stabilizer (centralizerImage Ω X) a ⊓ stabilizer (centralizerImage Ω X) b ⊓
      fixingSubgroup (centralizerImage Ω X)
        (holtDelta (centralizerImage Ω X) (fixSet Ω X) a b))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hab : a ≠ b := fun h => hαβ (by rw [← ha, ← hb, h])
  have h3 := hS.three_le_card_fixSet_of_ne hX hab
  by_contra hodd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2
    (even_iff_two_dvd.mp ((Nat.even_or_odd _).resolve_right hodd))
  obtain ⟨hgab, hgΔ⟩ := Subgroup.mem_inf.mp g.2
  obtain ⟨hga, hgb⟩ := Subgroup.mem_inf.mp hgab
  have hg2 : ((g : centralizerImage Ω X) : Perm (fixSet Ω X)) *
      ((g : centralizerImage Ω X) : Perm (fixSet Ω X)) = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg, sq] at h
    have h1 : (g : centralizerImage Ω X) * (g : centralizerImage Ω X) = 1 := by
      have h' := congrArg Subtype.val h
      rwa [Subgroup.coe_mul, Subgroup.coe_one] at h'
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_mul, Subgroup.coe_one] at h2
  obtain ⟨c, hcX, hc2, hcg⟩ :=
    exists_isPGroup_zpowers_of_mem_centralizerImage (g : centralizerImage Ω X).2 hg2
  have hcfix : ∀ ω : fixSet Ω X, (g : centralizerImage Ω X) • ω = ω → c • (ω : Ω) = ω :=
    fun ω h => (hcg ω).symm.trans (congrArg Subtype.val h)
  have hcmem : c ∈ stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, (mem_fixingSubgroup_iff G).mpr
      fun y hy => ?_⟩
    · rw [mem_stabilizer_iff, ← ha]
      exact hcfix a hga
    · rw [mem_stabilizer_iff, ← hb]
      exact hcfix b hgb
    · have hyX : y ∈ fixSet Ω X := fun x hx =>
        (mem_fixingSubgroup_iff G).mp (Subgroup.mem_inf.mp (hsyl.1 hx)).2 y hy
      have hyK : (⟨y, hyX⟩ : fixSet Ω X) ∈ holtDelta (centralizerImage Ω X) (fixSet Ω X) a b :=
        (hS.mem_holtDelta_centralizerImage_iff hX h3 hab).mpr (by rw [ha, hb]; exact hΛΔ hy)
      exact hcfix ⟨y, hyX⟩ ((mem_fixingSubgroup_iff _).mp hgΔ _ hyK)
  have hsup := hsyl.2.2 (X ⊔ Subgroup.zpowers c)
    (sup_le hsyl.1 (Subgroup.zpowers_le.mpr hcmem))
    (IsPGroup.to_sup_of_normal_left' hX hc2
      (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hcX))) le_sup_left
  have hcX' : c ∈ X := hsup ▸ (le_sup_right : Subgroup.zpowers c ≤ X ⊔ Subgroup.zpowers c)
    (Subgroup.mem_zpowers c)
  have hg1 : g = 1 := Subtype.ext (Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
    rw [hcg ω]
    exact mem_fixSet_iff_le_stabilizer.mp ω.2 hcX')))
  rw [hg1, orderOf_one] at hg
  exact absurd hg (by decide)

end Section

section Orbits

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω]

theorem exists_invariant_subset_of_isPGroup {A : Subgroup G} (hA : IsPGroup 2 A) {Θ : Set Ω}
    (hΘfin : Θ.Finite) (hΘ : ∀ a ∈ A, ∀ θ ∈ Θ, a • θ ∈ Θ)
    (hfree : ∀ θ ∈ Θ, ∃ a ∈ A, a • θ ≠ θ) {θ₁ θ₂ : Ω} (hθ₁ : θ₁ ∈ Θ) (hθ₂ : θ₂ ∈ Θ)
    (hntr : ∀ a ∈ A, a • θ₁ ≠ θ₂) (h8 : 8 ≤ Θ.ncard) :
    ∃ Λ ⊆ Θ, (∀ a ∈ A, ∀ θ ∈ Λ, a • θ ∈ Λ) ∧ Λ.ncard % 4 = 0 ∧ 4 ≤ Λ.ncard ∧ Λ ≠ Θ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : ∀ θ ∈ Θ, orbit A θ ⊆ Θ := by
    rintro θ hθ _ ⟨⟨a, ha⟩, rfl⟩
    exact hΘ a ha θ hθ
  have hfin : ∀ θ ∈ Θ, (orbit A θ).Finite := fun θ hθ => hΘfin.subset (hsub θ hθ)
  have hinv : ∀ θ : Ω, ∀ a ∈ A, ∀ x ∈ orbit A θ, a • x ∈ orbit A θ := by
    rintro θ a ha _ ⟨b, rfl⟩
    exact ⟨⟨a, ha⟩ * b, mul_smul _ _ _⟩
  have hcard : ∀ θ ∈ Θ, ∃ e, 1 ≤ e ∧ (orbit A θ).ncard = 2 ^ e := by
    intro θ hθ
    have := (hfin θ hθ).to_subtype
    obtain ⟨e, he⟩ := hA.card_orbit θ
    refine ⟨e, Nat.one_le_iff_ne_zero.mpr fun h0 => ?_, by rw [← Nat.card_coe_set_eq, he]⟩
    rw [h0, pow_zero, Nat.card_coe_set_eq, Set.ncard_eq_one] at he
    obtain ⟨x, hx⟩ := he
    obtain ⟨a, ha, haθ⟩ := hfree θ hθ
    have h1 : a • θ ∈ orbit A θ := ⟨⟨a, ha⟩, rfl⟩
    rw [hx, Set.mem_singleton_iff] at h1
    have h2 := mem_orbit_self (M := A) θ
    rw [hx, Set.mem_singleton_iff] at h2
    exact haθ (h1.trans h2.symm)
  have hθ₂₁ : θ₂ ∉ orbit A θ₁ := fun ⟨⟨a, ha⟩, h⟩ => hntr a ha h
  by_cases hbig : ∃ θ ∈ Θ, 4 ≤ (orbit A θ).ncard
  · obtain ⟨θ, hθ, h4⟩ := hbig
    obtain ⟨e, -, he⟩ := hcard θ hθ
    refine ⟨orbit A θ, hsub θ hθ, fun a ha x hx => hinv θ a ha x hx, ?_, h4, fun h => ?_⟩
    · rw [he] at h4 ⊢
      have he2 : 2 ≤ e := by
        by_contra he2
        interval_cases e <;> simp at h4
      rw [show e = (e - 2) + 2 by omega, pow_add]
      simp
    · have h1 : orbit A θ₁ = orbit A θ := orbit_eq_iff.mpr (h ▸ hθ₁)
      have h2 : orbit A θ₂ = orbit A θ := orbit_eq_iff.mpr (h ▸ hθ₂)
      exact hθ₂₁ (orbit_eq_iff.mp (h2.trans h1.symm))
  · push Not at hbig
    have h2 : ∀ θ ∈ Θ, (orbit A θ).ncard = 2 := fun θ hθ => by
      obtain ⟨e, he1, he⟩ := hcard θ hθ
      have h3 := hbig θ hθ
      rw [he] at h3 ⊢
      have he1' : e = 1 := by
        by_contra hne
        have : 2 ≤ e := by omega
        have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) this
        omega
      rw [he1', pow_one]
    have hdisj : Disjoint (orbit A θ₁) (orbit A θ₂) := Set.disjoint_left.mpr fun x hx hx' =>
      hθ₂₁ (orbit_eq_iff.mp ((orbit_eq_iff.mpr hx').symm.trans (orbit_eq_iff.mpr hx)))
    have hU : (orbit A θ₁ ∪ orbit A θ₂).ncard = 4 := by
      rw [Set.ncard_union_eq hdisj (hfin _ hθ₁) (hfin _ hθ₂), h2 _ hθ₁, h2 _ hθ₂]
    refine ⟨orbit A θ₁ ∪ orbit A θ₂, Set.union_subset (hsub _ hθ₁) (hsub _ hθ₂),
      fun a ha x hx => ?_, by rw [hU], hU.ge, fun h => ?_⟩
    · rcases hx with hx | hx
      · exact Or.inl (hinv _ a ha x hx)
      · exact Or.inr (hinv _ a ha x hx)
    · rw [← h, hU] at h8
      omega

end Orbits

section Generic

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α β : Ω}

theorem stabilizer_inf_le_stabilizer_holtDelta (α β : Ω) :
    stabilizer G α ⊓ stabilizer G β ≤ stabilizer G (holtDelta G Ω α β) :=
  (stabilizer_inf_le_stabilizer_pair α β).trans (stabilizer_pair_le α β)

theorem mem_normalizer_of_forall_conj_mem {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (h' : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := h' _ hx
  simpa [mul_assoc] using this

theorem le_stabilizer_of_forall_smul_mem {A : Subgroup G} {Λ : Set Ω}
    (h : ∀ a ∈ A, ∀ x ∈ Λ, a • x ∈ Λ) : A ≤ stabilizer G Λ := fun a ha => by
  rw [mem_stabilizer_set]
  intro x
  refine ⟨fun hx => ?_, h a ha x⟩
  have := h a⁻¹ (inv_mem ha) _ hx
  rwa [inv_smul_smul] at this

theorem conj_mem_inf_fixingSubgroup {Λ : Set Ω} {h n : G}
    (hh : h ∈ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G Λ)
    (hn : n ∈ stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ) :
    h * n * h⁻¹ ∈ stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ := by
  obtain ⟨hhαβ, hhΛ⟩ := Subgroup.mem_inf.mp hh
  obtain ⟨hnαβ, hnΛ⟩ := Subgroup.mem_inf.mp hn
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hhαβ hnαβ) (inv_mem hhαβ),
    (mem_fixingSubgroup_iff G).mpr fun x hx => ?_⟩
  have hx' : h⁻¹ • x ∈ Λ := (mem_stabilizer_set.mp (inv_mem hhΛ) x).mpr hx
  rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp hnΛ _ hx', smul_inv_smul]

theorem exists_eq_insert_of_ncard_eq_five (hαβ : α ≠ β) {F : Set Ω} (hF : F.ncard = 5)
    (hα : α ∈ F) (hβ : β ∈ F) (hFΔ : ∀ ω ∈ F, ω ≠ α → ω ≠ β → ω ∈ holtDelta G Ω α β) :
    ∃ δ₁ δ₂ δ₃ : Ω, δ₁ ∈ holtDelta G Ω α β ∧ δ₂ ∈ holtDelta G Ω α β ∧
      δ₃ ∈ holtDelta G Ω α β ∧ δ₁ ≠ δ₂ ∧ δ₁ ≠ δ₃ ∧ δ₂ ≠ δ₃ ∧ F = {α, β, δ₁, δ₂, δ₃} := by
  have hsub : ({α, β} : Set Ω) ⊆ F := Set.insert_subset hα (Set.singleton_subset_iff.mpr hβ)
  have h3 : (F \ {α, β}).ncard = 3 := by
    rw [Set.ncard_sdiff hsub (Set.toFinite _), hF, Set.ncard_pair hαβ]
  obtain ⟨δ₁, δ₂, δ₃, h12, h13, h23, heq⟩ := Set.ncard_eq_three.mp h3
  have hmem : ∀ δ ∈ ({δ₁, δ₂, δ₃} : Set Ω), δ ∈ holtDelta G Ω α β := fun δ hδ => by
    rw [← heq] at hδ
    obtain ⟨hδF, hδαβ⟩ := hδ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hδαβ
    exact hFΔ δ hδF hδαβ.1 hδαβ.2
  refine ⟨δ₁, δ₂, δ₃, hmem _ (Or.inl rfl), hmem _ (Or.inr (Or.inl rfl)),
    hmem _ (Or.inr (Or.inr rfl)), h12, h13, h23, ?_⟩
  ext ω
  constructor
  · intro hω
    by_cases hωα : ω = α
    · exact Or.inl hωα
    by_cases hωβ : ω = β
    · exact Or.inr (Or.inl hωβ)
    have h : ω ∈ F \ {α, β} := ⟨hω, by simp [hωα, hωβ]⟩
    rw [heq] at h
    exact Or.inr (Or.inr h)
  · rintro (rfl | rfl | h)
    · exact hα
    · exact hβ
    · rw [← heq] at h
      exact h.1

end Generic

section OneCoordinate

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω}

namespace AltConfig

variable (C : AltConfig G Ω α β)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
private theorem smul_mem_of_mem_stabilizer_set {g : G} {s : Set Ω} (hg : g ∈ stabilizer G s)
    {ω : Ω} (hω : ω ∈ s) : g • ω ∈ s := by
  rw [← mem_stabilizer_iff.mp hg]
  exact Set.smul_mem_smul_set hω

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem subsingleton_ι (hr : Fintype.card C.D.ι = 1) : Subsingleton C.D.ι :=
  Fintype.card_le_one_iff_subsingleton.mp hr.le

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem coord_apply_injective (hr : Fintype.card C.D.ι = 1) (i : C.D.ι) :
    Function.Injective fun δ : holtDelta G Ω α β => C.D.coord δ i := by
  have := C.subsingleton_ι hr
  intro δ δ' h
  refine HoltData.coord_injective (D := C.D) C.oddCore_eq_bot (funext fun j => ?_)
  obtain rfl := Subsingleton.elim j i
  exact h

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem card_holtDelta_eq (hr : Fintype.card C.D.ι = 1) :
    Nat.card (holtDelta G Ω α β) = Fintype.card (C.D.Ψc C.i₁) := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.ofBijective _
    ⟨C.coord_apply_injective hr C.i₁, fun b => C.D.exists_coord_apply_eq C.i₁ b⟩)


omit [FaithfulSMul G Ω] in
theorem exists_mem_longInvSwap_smul_eq (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hr : Fintype.card C.D.ι = 1) {y : Perm (holtDelta G Ω α β)}
    (hy : y ∈ longInv (Perm (holtDelta G Ω α β)) (holtDelta G Ω α β)) :
    ∃ u ∈ longInvSwap G Ω α β, ∀ δ : holtDelta G Ω α β, u • (δ : Ω) = (y δ : Ω) := by
  set e : ∀ i, holtDelta G Ω α β ≃ C.D.Ψc i := fun i =>
    Equiv.ofBijective _ ⟨C.coord_apply_injective hr i, fun b => C.D.exists_coord_apply_eq i b⟩
    with he
  obtain ⟨u, hu, hcoord⟩ := hS.exists_mem_longInvSwap_coord_smul hαβ C.D C.alt
    (fun i => (e i).permCongr y) (fun i => permCongr_mem_longInv (e i) hy)
  refine ⟨u, hu, fun δ => ?_⟩
  have huδ : u • (δ : Ω) ∈ holtDelta G Ω α β :=
    smul_mem_of_mem_stabilizer_set (mem_stabilizer_holtDelta_of_mem_longInvSwap hu) δ.2
  have h := hcoord δ ⟨_, huδ⟩ rfl
  have hyδ : (⟨_, huδ⟩ : holtDelta G Ω α β) = y δ := by
    refine HoltData.coord_injective (D := C.D) C.oddCore_eq_bot (h.trans (funext fun i => ?_))
    change e i (y ((e i).symm (e i δ))) = e i (y δ)
    rw [Equiv.symm_apply_apply]
  exact congrArg Subtype.val hyδ

omit [FaithfulSMul G Ω] in
theorem alternatingGroup_le_inducedPerm (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hr : Fintype.card C.D.ι = 1) [Fintype (holtDelta G Ω α β)] :
    alternatingGroup (holtDelta G Ω α β) ≤ inducedPerm (stabilizer G α ⊓ stabilizer G β)
      (holtDelta G Ω α β) (stabilizer_inf_le_stabilizer_holtDelta α β) := by
  set s : Set (Perm (holtDelta G Ω α β)) :=
    {π | ∃ y₁ ∈ longInv (Perm (holtDelta G Ω α β)) (holtDelta G Ω α β),
      ∃ y₂ ∈ longInv (Perm (holtDelta G Ω α β)) (holtDelta G Ω α β), y₁ * y₂ = π} with hs
  have h5 : 5 ≤ Nat.card (holtDelta G Ω α β) := by
    rw [C.card_holtDelta_eq hr]; exact C.D.five_le_card C.i₁
  have hodd : Odd (Fintype.card (holtDelta G Ω α β)) := by
    rw [← Nat.card_eq_fintype_card, C.card_holtDelta_eq hr]; exact C.D.odd_card_Ψc C.i₁
  have hsH : Subgroup.normalClosure s ≤ inducedPerm (stabilizer G α ⊓ stabilizer G β)
      (holtDelta G Ω α β)
      (stabilizer_inf_le_stabilizer_holtDelta α β) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨_, ⟨y₁, hy₁, y₂, hy₂, rfl⟩, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    obtain ⟨u₁, hu₁, h₁⟩ := C.exists_mem_longInvSwap_smul_eq hS hαβ hr (conj_mem_longInv hy₁ c)
    obtain ⟨u₂, hu₂, h₂⟩ := C.exists_mem_longInvSwap_smul_eq hS hαβ hr (conj_mem_longInv hy₂ c)
    refine mem_inducedPerm.mpr ⟨u₁ * u₂, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, fun δ => ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, hu₂.2, smul_eq_of_mem_longInvSwap hu₁]
    · rw [mem_stabilizer_iff, mul_smul, smul_eq_of_mem_longInvSwap hu₂, hu₁.2]
    · rw [mul_smul, h₂, h₁]
      simp [Perm.mul_apply]
  have h5' : 5 ≤ Fintype.card (holtDelta G Ω α β) := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨y₁, hy₁⟩ := exists_mem_longInv_perm hodd (by omega)
  obtain ⟨a, ha, hau⟩ := hy₁.2
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by omega) a
  set y₂ := swap a b * y₁ * (swap a b)⁻¹ with hy₂
  have hy₂J : y₂ ∈ longInv (Perm (holtDelta G Ω α β)) (holtDelta G Ω α β) := conj_mem_longInv hy₁ _
  have hne : y₁ * y₂ ≠ 1 := by
    intro h
    have h' : y₂ = y₁ := by
      rw [← inv_eq_of_mul_eq_one_right h, inv_eq_self_of_mem_longInv hy₁]
    have hyb : y₁ • b = b := by
      rw [← h', hy₂, Perm.smul_def, Perm.mul_apply, Perm.mul_apply, swap_inv, swap_apply_right,
        show y₁ a = a from ha, swap_apply_left]
    exact hb (hau b hyb)
  have : (Subgroup.normalClosure s).Normal := Subgroup.normalClosure_normal
  have hnt : Nontrivial (Subgroup.normalClosure s) :=
    ⟨⟨⟨y₁ * y₂, Subgroup.subset_normalClosure ⟨y₁, hy₁, y₂, hy₂J, rfl⟩⟩, 1,
      fun h => hne (congrArg Subtype.val h)⟩⟩
  exact (alternatingGroup_le_of_normal h5 hnt).trans hsH

omit [FaithfulSMul G Ω] in
theorem fusionIsSylowIn_inducedPerm_inf_alternatingGroup (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hr : Fintype.card C.D.ι = 1) [Fintype (holtDelta G Ω α β)] {Λ : Set Ω}
    (hΛ : Λ ⊆ holtDelta G Ω α β) {X : Subgroup G}
    (hX : fusionIsSylowIn 2 X (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ)) :
    fusionIsSylowIn 2 (inducedPerm X (holtDelta G Ω α β)
      (hX.1.trans (inf_le_left.trans (stabilizer_inf_le_stabilizer_holtDelta α β))) ⊓
        (alternatingGroup (holtDelta G Ω α β) ⊓
          fixingSubgroup (Perm (holtDelta G Ω α β))
          (Subtype.val ⁻¹' Λ : Set (holtDelta G Ω α β))))
      (alternatingGroup (holtDelta G Ω α β) ⊓
        fixingSubgroup (Perm (holtDelta G Ω α β))
          (Subtype.val ⁻¹' Λ : Set (holtDelta G Ω α β))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Λ' : Set (holtDelta G Ω α β) := Subtype.val ⁻¹' Λ with hΛ'
  have hK : stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ ≤
      stabilizer G (holtDelta G Ω α β) :=
    inf_le_left.trans (stabilizer_inf_le_stabilizer_holtDelta α β)
  have hXΔ := fusionIsSylowIn_inducedPerm (h := hK) hX
  set N := alternatingGroup (holtDelta G Ω α β) ⊓ fixingSubgroup (Perm (holtDelta G Ω α β)) Λ'
    with hN
  have hfixΛ : ∀ π ∈ inducedPerm (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ)
      (holtDelta G Ω α β) hK, ∀ x ∈ Λ', π x = x := fun π hπ x hx => by
    obtain ⟨k, hk, hkπ⟩ := mem_inducedPerm.mp hπ
    exact Subtype.ext ((hkπ x).trans ((mem_fixingSubgroup_iff G).mp
      (Subgroup.mem_inf.mp hk).2 x hx))
  have hNK : N ≤ inducedPerm (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ)
      (holtDelta G Ω α β) hK := by
    intro π hπ
    obtain ⟨g, hg, hgπ⟩ := mem_inducedPerm.mp (C.alternatingGroup_le_inducedPerm hS hαβ hr
      (Subgroup.mem_inf.mp hπ).1)
    refine mem_inducedPerm.mpr ⟨g, Subgroup.mem_inf.mpr ⟨hg, (mem_fixingSubgroup_iff G).mpr
      fun y hy => ?_⟩, hgπ⟩
    have hyΛ' : (⟨y, hΛ hy⟩ : holtDelta G Ω α β) ∈ Λ' := hy
    have h := (mem_fixingSubgroup_iff _).mp (Subgroup.mem_inf.mp hπ).2 _ hyΛ'
    exact (hgπ ⟨y, hΛ hy⟩).symm.trans (congrArg Subtype.val h)
  have hnorm : ∀ h ∈ inducedPerm (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ)
      (holtDelta G Ω α β) hK, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    intro h hh n hn
    obtain ⟨hnA, hnF⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨?_, (mem_fixingSubgroup_iff _).mpr fun x hx => ?_⟩
    · rw [mem_alternatingGroup] at hnA ⊢
      rw [map_mul, map_mul, hnA, mul_one, map_inv, mul_inv_cancel]
    · have hhx : h x = x := hfixΛ h hh x hx
      have hhx' : h⁻¹ x = x := by rw [Perm.inv_eq_iff_eq, hhx]
      change h (n (h⁻¹ x)) = x
      rw [hhx', show n x = x from (mem_fixingSubgroup_iff _).mp hnF x hx, hhx]
  exact fusionIsSylowIn_inf_of_forall_conj_mem hXΔ hNK hnorm

omit [FaithfulSMul G Ω] in
theorem mem_fixSet_iff_of_fusionIsSylowIn (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hr : Fintype.card C.D.ι = 1) {Λ : Set Ω} (hΛ : Λ ⊆ holtDelta G Ω α β)
    (heven : Even (Nat.card ↥(holtDelta G Ω α β \ Λ)))
    (h2 : Nat.card ↥(holtDelta G Ω α β \ Λ) ≠ 2) {X : Subgroup G}
    (hX : fusionIsSylowIn 2 X (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ))
    {δ : Ω} (hδ : δ ∈ holtDelta G Ω α β) : δ ∈ fixSet Ω X ↔ δ ∈ Λ := by
  classical
  refine ⟨fun hδX => ?_, fun hδΛ => mem_fixSet_iff_le_stabilizer.mpr fun x hx =>
    (mem_fixingSubgroup_iff G).mp (Subgroup.mem_inf.mp (hX.1 hx)).2 δ hδΛ⟩
  have hV := C.fusionIsSylowIn_inducedPerm_inf_alternatingGroup hS hαβ hr hΛ hX
  have hcard : Nat.card ↥((Subtype.val ⁻¹' Λ : Set (holtDelta G Ω α β))ᶜ) =
      Nat.card ↥(holtDelta G Ω α β \ Λ) := Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfix := fixSet_eq_of_fusionIsSylowIn_alternatingGroup_inf_fixingSubgroup
    (hcard ▸ heven) (hcard ▸ h2) hV
  have hmem : (⟨δ, hδ⟩ : holtDelta G Ω α β) ∈ fixSet (holtDelta G Ω α β)
      (inducedPerm X (holtDelta G Ω α β)
        (hX.1.trans (inf_le_left.trans (stabilizer_inf_le_stabilizer_holtDelta α β))) ⊓
        (alternatingGroup (holtDelta G Ω α β) ⊓
          fixingSubgroup (Perm (holtDelta G Ω α β))
          (Subtype.val ⁻¹' Λ : Set (holtDelta G Ω α β)))) := fun π hπ => by
    obtain ⟨x, hx, hxπ⟩ := mem_inducedPerm.mp (Subgroup.mem_inf.mp hπ).1
    exact Subtype.ext ((hxπ _).trans (mem_fixSet_iff_le_stabilizer.mp hδX hx))
  rw [hfix] at hmem
  exact hmem

theorem exists_holtData_centralizerImage (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hr : Fintype.card C.D.ι = 1) {X : Subgroup G} (hX : IsPGroup 2 X) (hX1 : X ≠ ⊥)
    (hXαβ : X ≤ stabilizer G α ⊓ stabilizer G β) {Λ : Set Ω} (hΛΔ : Λ ⊆ holtDelta G Ω α β)
    (hXΛ : ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω X ↔ δ ∈ Λ) (h5 : 5 ≤ Λ.ncard)
    (hsyl : fusionIsSylowIn 2 X (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ)) :
    ∃ (D : HoltData (centralizerImage Ω X) (fixSet Ω X)) (k : D.ι), (∀ k', k' = k) ∧
      factorImage _ _ (D.L k) (D.ρ k) = alternatingGroup (D.Ψc k) ∧
      Fintype.card (D.Ψc k) = Λ.ncard + 2 ∧
      ∀ x y : fixSet Ω X, ((x : Ω) = α ∨ (x : Ω) = β ∨ (x : Ω) ∈ Λ) →
        ((y : Ω) = α ∨ (y : Ω) = β ∨ (y : Ω) ∈ Λ) → D.coord x k = D.coord y k → x = y := by
  classical
  have hsub := C.subsingleton_ι hr
  set a : fixSet Ω X := ⟨α, mem_fixSet_iff_le_stabilizer.mpr (hXαβ.trans inf_le_left)⟩ with ha
  set b : fixSet Ω X := ⟨β, mem_fixSet_iff_le_stabilizer.mpr (hXαβ.trans inf_le_right)⟩ with hb
  have hab : a ≠ b := fun h => hαβ (congrArg Subtype.val h)
  have h3 := hS.three_le_card_fixSet_of_ne hX hab
  set Λc : ∀ i, Set (C.D.Ψc i) := fun i =>
    (fun δ : holtDelta G Ω α β => C.D.coord δ i) '' (Subtype.val ⁻¹' Λ) with hΛc
  have hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω X ↔ ∀ i, C.D.coord δ i ∈ Λc i := by
    intro δ
    rw [hXΛ δ δ.2]
    refine ⟨fun h i => ⟨δ, h, rfl⟩, fun h => ?_⟩
    obtain ⟨δ', hδ', he⟩ := h C.i₁
    rw [← C.coord_apply_injective hr C.i₁ he]
    exact hδ'
  have hcardΛc : ∀ i, (Λc i).ncard = Λ.ncard := fun i => by
    rw [hΛc, Set.ncard_image_of_injective _ (C.coord_apply_injective hr i),
      Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
        (by rwa [Subtype.range_coe])]
  have hnt : ∀ i, (Λc i).Nontrivial := fun i =>
    Set.one_lt_ncard_iff_nontrivial.mp (by rw [hcardΛc]; omega)
  obtain ⟨e, he, hcoord, hreal⟩ := hS.exists_boxEquiv_ccl hαβ C.D C.oddCore_eq_bot C.alt hX
    (a := a) (b := b) rfl rfl Λc hbox (p := fun i => (Λc i).Nontrivial) (fun _ h => h)
    (fun i h => absurd (hnt i) h)
  obtain ⟨DK⟩ := hS.holtData_centralizerImage hX hX1 h3
  have h5' : ∀ j : {i // (Λc i).Nontrivial}, 5 ≤ Fintype.card (Λc j) := fun j => by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hcardΛc]
    exact h5
  have hodd := hS.odd_card_inf_fixingSubgroup_centralizerImage hαβ hX hΛΔ hsyl
    (a := a) (b := b) rfl rfl
  obtain ⟨c, -, hca, -, hcd⟩ := DK.ccl (hS.star_centralizerImage hX h3)
    (hS.holtTheorem1Below_centralizerImage hX hX1 h3) hab e h5' hcoord hreal
  set i₁' : {i // (Λc i).Nontrivial} := ⟨C.i₁, hnt _⟩ with hi₁'def
  have hi₁' : ∀ j : {i // (Λc i).Nontrivial}, j = i₁' := fun j =>
    Subtype.ext (Subsingleton.elim _ _)
  obtain ⟨hA, hcard, habk, hδk⟩ := hca i₁'
  refine ⟨DK, c i₁', fun k' => ?_, hA, ?_, ?_⟩
  · obtain ⟨j, rfl⟩ : k' ∈ Set.range c := (hcd hodd).symm ▸ Set.mem_univ k'
    rw [hi₁' j]
  · rw [hcard, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hcardΛc]
  · have hK : ∀ x : fixSet Ω X, (x : Ω) ∈ Λ →
        x ∈ holtDelta (centralizerImage Ω X) (fixSet Ω X) a b := fun x hx =>
      (hS.mem_holtDelta_centralizerImage_iff hX h3 hab).mpr (hΛΔ hx)
    have hxa : ∀ x : fixSet Ω X, (x : Ω) = α → x = a := fun x hx => Subtype.ext hx
    have hxb : ∀ x : fixSet Ω X, (x : Ω) = β → x = b := fun x hx => Subtype.ext hx
    intro x y hx hy hxy
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
    · exact (hxa x hx).trans (hxa y hy).symm
    · rw [hxa x hx, hxb y hy] at hxy
      exact absurd hxy habk
    · rw [hxa x hx] at hxy
      exact absurd hxy.symm (hδk ⟨y, hK y hy⟩ ⟨y, hK y hy⟩).2.1
    · rw [hxb x hx, hxa y hy] at hxy
      exact absurd hxy.symm habk
    · exact (hxb x hx).trans (hxb y hy).symm
    · rw [hxb x hx] at hxy
      exact absurd hxy.symm (hδk ⟨y, hK y hy⟩ ⟨y, hK y hy⟩).2.2
    · rw [hxa y hy] at hxy
      exact absurd hxy (hδk ⟨x, hK x hx⟩ ⟨x, hK x hx⟩).2.1
    · rw [hxb y hy] at hxy
      exact absurd hxy (hδk ⟨x, hK x hx⟩ ⟨x, hK x hx⟩).2.2
    · have h1 := ((hδk ⟨x, hK x hx⟩ ⟨y, hK y hy⟩).1).mp hxy
      have h2 : e ⟨x, hK x hx⟩ = e ⟨y, hK y hy⟩ := funext fun j => by rw [hi₁' j]; exact h1
      exact congrArg Subtype.val (e.injective h2)

theorem exists_W_of_fusionIsSylowIn (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hr : Fintype.card C.D.ι = 1) {X : Subgroup G} (hX : IsPGroup 2 X) (hX1 : X ≠ ⊥)
    (hXαβ : X ≤ stabilizer G α ⊓ stabilizer G β) {Λ : Set Ω} (hΛΔ : Λ ⊆ holtDelta G Ω α β)
    (hXΛ : ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω X ↔ δ ∈ Λ) (hcard : Λ.ncard % 4 = 1)
    (h5 : 5 ≤ Λ.ncard)
    (hsyl : fusionIsSylowIn 2 X (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ))
    {Y₀ : Subgroup G} (hY₀ : IsPGroup 2 Y₀) (hY₀αβ : Y₀ ≤ stabilizer G α ⊓ stabilizer G β)
    (hY₀X : Y₀ ≤ Subgroup.normalizer (X : Set G)) (hY₀F : fixSet Ω Y₀ ⊆ {α, β} ∪ Λ) :
    ∃ W : Subgroup G, IsPGroup 2 W ∧ ∃ δ₁ δ₂ δ₃ : Ω, δ₁ ∈ holtDelta G Ω α β ∧
      δ₂ ∈ holtDelta G Ω α β ∧ δ₃ ∈ holtDelta G Ω α β ∧ δ₁ ≠ δ₂ ∧ δ₁ ≠ δ₃ ∧ δ₂ ≠ δ₃ ∧
        fixSet Ω W = {α, β, δ₁, δ₂, δ₃} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨DK, k, hk, hA, hΨ, hdist⟩ :=
    C.exists_holtData_centralizerImage hS hαβ hr hX hX1 hXαβ hΛΔ hXΛ h5 hsyl
  have hαX : α ∈ fixSet Ω X := mem_fixSet_iff_le_stabilizer.mpr (hXαβ.trans inf_le_left)
  have hβX : β ∈ fixSet Ω X := mem_fixSet_iff_le_stabilizer.mpr (hXαβ.trans inf_le_right)
  set a : fixSet Ω X := ⟨α, hαX⟩ with ha
  set b : fixSet Ω X := ⟨β, hβX⟩ with hb
  have hab : a ≠ b := fun h => hαβ (congrArg Subtype.val h)
  have h3 := hS.three_le_card_fixSet_of_ne hX hab
  have hΛX : Λ ⊆ fixSet Ω X := fun δ hδ => (hXΛ δ (hΛΔ hδ)).mpr hδ
  have hαΛ : α ∉ Λ := fun h => left_notMem_holtDelta hαβ (hΛΔ h)
  have hβΛ : β ∉ Λ := fun h => right_notMem_holtDelta hαβ (hΛΔ h)
  obtain ⟨l₁, hl₁, l₂, hl₂, l₃, hl₃, h12, h13, h23⟩ :=
    (Set.two_lt_ncard (Set.toFinite Λ)).mp (by omega)
  set p : Fin 5 → fixSet Ω X := ![a, b, ⟨l₁, hΛX hl₁⟩, ⟨l₂, hΛX hl₂⟩, ⟨l₃, hΛX hl₃⟩] with hpdef
  have hpdes : ∀ i, ((p i : Ω) = α ∨ (p i : Ω) = β ∨ (p i : Ω) ∈ Λ) := fun i => by
    fin_cases i
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr hl₁), Or.inr (Or.inr hl₂),
      Or.inr (Or.inr hl₃)]
  have hpinj : Function.Injective p := by
    have e1 : a ≠ ⟨l₁, hΛX hl₁⟩ := fun h =>
      hαΛ ((show α = l₁ from congrArg Subtype.val h) ▸ hl₁)
    have e2 : a ≠ ⟨l₂, hΛX hl₂⟩ := fun h =>
      hαΛ ((show α = l₂ from congrArg Subtype.val h) ▸ hl₂)
    have e3 : a ≠ ⟨l₃, hΛX hl₃⟩ := fun h =>
      hαΛ ((show α = l₃ from congrArg Subtype.val h) ▸ hl₃)
    have f1 : b ≠ ⟨l₁, hΛX hl₁⟩ := fun h =>
      hβΛ ((show β = l₁ from congrArg Subtype.val h) ▸ hl₁)
    have f2 : b ≠ ⟨l₂, hΛX hl₂⟩ := fun h =>
      hβΛ ((show β = l₂ from congrArg Subtype.val h) ▸ hl₂)
    have f3 : b ≠ ⟨l₃, hΛX hl₃⟩ := fun h =>
      hβΛ ((show β = l₃ from congrArg Subtype.val h) ▸ hl₃)
    have g12 : (⟨l₁, hΛX hl₁⟩ : fixSet Ω X) ≠ ⟨l₂, hΛX hl₂⟩ := fun h =>
      h12 (congrArg Subtype.val h)
    have g13 : (⟨l₁, hΛX hl₁⟩ : fixSet Ω X) ≠ ⟨l₃, hΛX hl₃⟩ := fun h =>
      h13 (congrArg Subtype.val h)
    have g23 : (⟨l₂, hΛX hl₂⟩ : fixSet Ω X) ≠ ⟨l₃, hΛX hl₃⟩ := fun h =>
      h23 (congrArg Subtype.val h)
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact absurd hij ‹_› | exact absurd hij.symm ‹_›
  have hp : Function.Injective fun i => DK.coord (p i) k := fun i j hij =>
    hpinj (hdist _ _ (hpdes i) (hpdes j) hij)
  obtain ⟨u, huJ, hu2, q, hqc, hqfix, hfixq, hquniq, hE⟩ :=
    DK.exists_involution_fixSet_five (hS.star_centralizerImage hX h3)
      (hS.holtTheorem1Below_centralizerImage hX hX1 h3) hk hA (by omega) p hp
  have huu : (u : Perm (fixSet Ω X)) * u = 1 := by
    have h := congrArg Subtype.val (show u * u = 1 by rw [← sq, ← hu2, pow_orderOf_eq_one])
    rwa [Subgroup.coe_mul, Subgroup.coe_one] at h
  obtain ⟨c, hcX, hc2, hcu⟩ := exists_isPGroup_zpowers_of_mem_centralizerImage u.2 huu
  have hcfix : ∀ y : fixSet Ω X, c • (y : Ω) = y ↔ u • y = y := fun y =>
    ⟨fun h => Subtype.ext ((hcu y).trans h), fun h => (hcu y).symm.trans (congrArg Subtype.val h)⟩
  have hcoordK : ∀ y z : fixSet Ω X, DK.coord y = DK.coord z ↔ DK.coord y k = DK.coord z k :=
    fun y z => ⟨fun h => congrFun h k, fun h => funext fun k' => by rw [hk k']; exact h⟩
  have hblock : ∀ n (hn : n ∈ Subgroup.normalizer (X : Set G)) (y z : fixSet Ω X),
      DK.coord y = DK.coord z ↔
        DK.coord ((⟨n, hn⟩ : Subgroup.normalizer (X : Set G)) • y) =
          DK.coord ((⟨n, hn⟩ : Subgroup.normalizer (X : Set G)) • z) := by
    intro n hn y z
    obtain ⟨σ, hσ⟩ := DK.exists_equiv_coord_eq_iff_of_mem_normalizer
      (toPermHom_mem_normalizer_centralizerImage (Ω := Ω) ⟨n, hn⟩)
    have h := hσ k y z
    rw [hk (σ k)] at h
    rw [hcoordK, hcoordK]
    exact h
  set Bf : fixSet Ω X → Set Ω := fun y₀ =>
    {ω | ∃ h : ω ∈ fixSet Ω X, DK.coord ⟨ω, h⟩ = DK.coord y₀} with hBf
  have hBstab : ∀ n (hn : n ∈ Subgroup.normalizer (X : Set G)) (y₀ : fixSet Ω X),
      DK.coord ((⟨n, hn⟩ : Subgroup.normalizer (X : Set G)) • y₀) = DK.coord y₀ →
        n ∈ stabilizer G (Bf y₀) := by
    intro n hn y₀ hy₀
    rw [mem_stabilizer_set]
    intro ω
    constructor
    · rintro ⟨h, hω⟩
      have hω' : ω ∈ fixSet Ω X := by
        have h' := smul_mem_fixSet_of_mem_normalizer (inv_mem hn) h
        rwa [inv_smul_smul] at h'
      refine ⟨hω', (hblock n hn _ _).mpr ?_⟩
      rw [hy₀]
      exact hω
    · rintro ⟨h, hω⟩
      refine ⟨smul_mem_fixSet_of_mem_normalizer hn h, ?_⟩
      have h' := (hblock n hn _ _).mp hω
      rw [hy₀] at h'
      exact h'
  set 𝔑 := Subgroup.normalizer (X : Set G) ⊓ stabilizer G (Bf a) ⊓ stabilizer G (Bf b) with h𝔑
  have hmem𝔑 : ∀ n (hn : n ∈ Subgroup.normalizer (X : Set G)),
      DK.coord ((⟨n, hn⟩ : Subgroup.normalizer (X : Set G)) • a) = DK.coord a →
      DK.coord ((⟨n, hn⟩ : Subgroup.normalizer (X : Set G)) • b) = DK.coord b → n ∈ 𝔑 :=
    fun n hn ha' hb' => ⟨⟨hn, hBstab n hn a ha'⟩, hBstab n hn b hb'⟩
  have hfixab : ∀ n (hn : n ∈ Subgroup.normalizer (X : Set G)), n • α = α → n • β = β →
      n ∈ 𝔑 := fun n hn hα hβ => hmem𝔑 n hn (by rw [show (⟨n, hn⟩ :
        Subgroup.normalizer (X : Set G)) • a = a from Subtype.ext hα]) (by rw [show (⟨n, hn⟩ :
        Subgroup.normalizer (X : Set G)) • b = b from Subtype.ext hβ])
  have hY₀𝔑 : Y₀ ≤ 𝔑 := fun y hy => hfixab y (hY₀X hy)
    (mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hY₀αβ hy)).1)
    (mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hY₀αβ hy)).2)
  have hX𝔑 : X ≤ 𝔑 := fun x hx => hfixab x (Subgroup.le_normalizer hx)
    (mem_fixSet_iff_le_stabilizer.mp hαX hx) (mem_fixSet_iff_le_stabilizer.mp hβX hx)
  have hcN : c ∈ Subgroup.normalizer (X : Set G) := Subgroup.centralizer_le_normalizer _ hcX
  have hcq : ∀ i, (⟨c, hcN⟩ : Subgroup.normalizer (X : Set G)) • q i = q i := fun i =>
    Subtype.ext ((hcfix (q i)).mpr (hqfix i))
  have hc𝔑 : c ∈ 𝔑 := hmem𝔑 c hcN
    (by rw [(hblock c hcN a (q 0)).mp (hqc 0).symm, hcq, hqc]; rfl)
    (by rw [(hblock c hcN b (q 1)).mp (hqc 1).symm, hcq, hqc]; rfl)
  obtain ⟨Y, hY₀Y, hY⟩ := exists_fusionIsSylowIn_ge hY₀ hY₀𝔑
  have hYN : Y ≤ Subgroup.normalizer (X : Set G) := hY.1.trans (inf_le_left.trans inf_le_left)
  have hXY : X ≤ Y := by
    have h := hY.2.2 (Y ⊔ X) (sup_le hY.1 hX𝔑) (IsPGroup.to_sup_of_normal_right' hY.2.1 hX hYN)
      le_sup_left
    rw [← h]
    exact le_sup_right
  have hBorb : ∀ y₀ : fixSet Ω X,
      Bf y₀ = Subtype.val '' orbit (jOddCore (centralizerImage Ω X) (fixSet Ω X)) y₀ := by
    intro y₀
    ext ω
    constructor
    · rintro ⟨h, hω⟩
      exact ⟨⟨ω, h⟩, (DK.coord_eq_iff y₀ ⟨ω, h⟩).mp hω.symm, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, ((DK.coord_eq_iff y₀ y).mpr hy).symm⟩
  have hYfix : ∀ y₀ : fixSet Ω X, (y₀ = a ∨ y₀ = b) → Y ≤ stabilizer G (Bf y₀) →
      (y₀ : Ω) ∈ fixSet Ω Y := by
    intro y₀ hy₀ hYB
    have hodd : Odd (Nat.card (Bf y₀)) := by
      rw [hBorb, Nat.card_image_of_injective Subtype.val_injective]
      exact odd_card_orbit_jOddCore y₀
    have hF : Odd (Nat.card ↥(fixSet Ω Y ∩ Bf y₀)) := by
      rw [Nat.odd_iff] at hodd ⊢
      rw [← card_modEq_card_fixSet_inter_of_le_stabilizer hY.2.1 hYB, hodd]
    obtain ⟨ω, hωY, hωX, hω⟩ : (fixSet Ω Y ∩ Bf y₀).Nonempty := by
      have h := hF.pos
      rw [Nat.card_pos_iff] at h
      exact Set.nonempty_coe_sort.mp h.1
    have hωdes : ω = α ∨ ω = β ∨ ω ∈ Λ := by
      rcases hY₀F (fixSet_anti hY₀Y hωY) with h | h
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hy₀des : (y₀ : Ω) = α ∨ (y₀ : Ω) = β ∨ (y₀ : Ω) ∈ Λ := by
      rcases hy₀ with rfl | rfl
      exacts [Or.inl rfl, Or.inr (Or.inl rfl)]
    have h := hdist ⟨ω, hωX⟩ y₀ hωdes hy₀des (congrFun hω k)
    rw [← h]
    exact hωY
  have hαY : α ∈ fixSet Ω Y := hYfix a (Or.inl rfl) (hY.1.trans (inf_le_left.trans inf_le_right))
  have hβY : β ∈ fixSet Ω Y := hYfix b (Or.inr rfl) (hY.1.trans inf_le_right)
  obtain ⟨Y', hcY', hY'⟩ := exists_fusionIsSylowIn_ge hc2 (Subgroup.zpowers_le.mpr hc𝔑)
  obtain ⟨n, hn𝔑, hnY⟩ := exists_mem_conj_of_fusionIsSylowIn hY hY'
  have hg'Y : n⁻¹ * c * n ∈ Y := (hnY c).mp (hcY' (Subgroup.mem_zpowers c))
  have hnN : n ∈ Subgroup.normalizer (X : Set G) := (Subgroup.mem_inf.mp
    (Subgroup.mem_inf.mp hn𝔑).1).1
  have hnBa : n ∈ stabilizer G (Bf a) := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hn𝔑).1).2
  have hnBb : n ∈ stabilizer G (Bf b) := (Subgroup.mem_inf.mp hn𝔑).2
  set W := X ⊔ Subgroup.zpowers (n⁻¹ * c * n) with hW
  have hWP : IsPGroup 2 W := hY.2.1.to_le (sup_le hXY (Subgroup.zpowers_le.mpr hg'Y))
  have hkey : ∀ ω ∈ fixSet Ω X, (n⁻¹ * c * n) • ω = ω ↔ ∃ i, n • ω = (q i : Ω) := by
    intro ω hω
    have hnω : n • ω ∈ fixSet Ω X := smul_mem_fixSet_of_mem_normalizer hnN hω
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
    refine (hcfix ⟨n • ω, hnω⟩).trans ⟨fun h => ?_, fun ⟨i, hi⟩ => ?_⟩
    · obtain ⟨i, hi⟩ := hfixq _ h
      exact ⟨i, congrArg Subtype.val hi⟩
    · rw [show (⟨n • ω, hnω⟩ : fixSet Ω X) = q i from Subtype.ext hi]
      exact hqfix i
  have hnpt : ∀ (i : Fin 5) (y₀ : fixSet Ω X), p i = y₀ → n ∈ stabilizer G (Bf y₀) →
      (y₀ : Ω) ∈ fixSet Ω Y → n • (y₀ : Ω) = (q i : Ω) := by
    intro i y₀ hpy hnB hy₀Y
    obtain ⟨j, hj⟩ := (hkey _ y₀.2).mp (mem_fixSet_iff_le_stabilizer.mp hy₀Y hg'Y)
    obtain ⟨h, hcoord'⟩ := (mem_stabilizer_set.mp hnB (y₀ : Ω)).mpr ⟨y₀.2, rfl⟩
    have hx := hquniq i ⟨n • (y₀ : Ω), h⟩ (by rw [hcoord', hpy])
      (by rw [show (⟨n • (y₀ : Ω), h⟩ : fixSet Ω X) = q j from Subtype.ext hj]; exact hqfix j)
    exact congrArg Subtype.val hx
  have hnα : n • α = (q 0 : Ω) := hnpt 0 a rfl hnBa hαY
  have hnβ : n • β = (q 1 : Ω) := hnpt 1 b rfl hnBb hβY
  have hδ : ∀ i : Fin 5, 2 ≤ i.val → n⁻¹ • (q i : Ω) ∈ holtDelta G Ω α β := by
    intro i hi
    obtain ⟨t, ht, ht0, hti⟩ := hE i hi
    obtain ⟨c', hc'J, -, hc't⟩ := (hS.mem_longInv_centralizerImage_iff hX h3 t).mp ht
    refine ⟨n⁻¹ * c' * n⁻¹⁻¹, ⟨conj_mem_longInv hc'J n⁻¹, ?_⟩, ?_⟩
    · rw [inv_inv, mul_smul, mul_smul, hnα, ← hc't (q 0)]
      change n⁻¹ • ((t • q 0 : fixSet Ω X) : Ω) = β
      rw [ht0, ← hnβ, inv_smul_smul]
    · rw [inv_inv, mul_smul, mul_smul, smul_inv_smul, ← hc't (q i)]
      change n⁻¹ • ((t • q i : fixSet Ω X) : Ω) = _
      rw [hti]
  have hqinj : ∀ i j : Fin 5, n⁻¹ • (q i : Ω) = n⁻¹ • (q j : Ω) → i = j := fun i j h => by
    have hq : q i = q j := Subtype.ext (smul_left_cancel _ h)
    have hc := (hqc i).symm.trans ((congrArg DK.coord hq).trans (hqc j))
    exact hp (congrFun hc k)
  have hFin : ∀ i : Fin 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
  refine ⟨W, hWP, n⁻¹ • (q 2 : Ω), n⁻¹ • (q 3 : Ω), n⁻¹ • (q 4 : Ω), hδ 2 (by decide),
    hδ 3 (by decide), hδ 4 (by decide), fun h => absurd (hqinj _ _ h) (by decide),
    fun h => absurd (hqinj _ _ h) (by decide), fun h => absurd (hqinj _ _ h) (by decide), ?_⟩
  ext ω
  rw [hW, fixSet_sup, fixSet_zpowers]
  simp only [Set.mem_inter_iff, mem_fixedBy, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hωX, hω⟩
    obtain ⟨i, hi⟩ := (hkey ω hωX).mp hω
    have hω' : ω = n⁻¹ • (q i : Ω) := by rw [← hi, inv_smul_smul]
    rcases hFin i with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by rw [hω', ← hnα, inv_smul_smul])
    · exact Or.inr (Or.inl (by rw [hω', ← hnβ, inv_smul_smul]))
    · exact Or.inr (Or.inr (Or.inl hω'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hω')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hω')))
  · intro h
    obtain ⟨i, rfl⟩ : ∃ i, ω = n⁻¹ • (q i : Ω) := by
      rcases h with rfl | rfl | h | h | h
      · exact ⟨0, by rw [← hnα, inv_smul_smul]⟩
      · exact ⟨1, by rw [← hnβ, inv_smul_smul]⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
      · exact ⟨4, h⟩
    have hX' : n⁻¹ • (q i : Ω) ∈ fixSet Ω X :=
      smul_mem_fixSet_of_mem_normalizer (inv_mem hnN) (q i).2
    exact ⟨hX', (hkey _ hX').mpr ⟨i, smul_inv_smul n _⟩⟩

theorem exists_W_of_not_odd (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hr : Fintype.card C.D.ι = 1) (hd : Fintype.card (C.D.Ψc C.i₁) % 4 = 1)
    (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α β))) :
    ∃ W : Subgroup G, IsPGroup 2 W ∧ ∃ δ₁ δ₂ δ₃ : Ω, δ₁ ∈ holtDelta G Ω α β ∧
      δ₂ ∈ holtDelta G Ω α β ∧ δ₃ ∈ holtDelta G Ω α β ∧ δ₁ ≠ δ₂ ∧ δ₁ ≠ δ₃ ∧ δ₂ ≠ δ₃ ∧
        fixSet Ω W = {α, β, δ₁, δ₂, δ₃} := by
  have hγ := C.γ.2
  have hX := fusionIsSylowIn_inf_twoPointKernel hγ C.sylow
  have hX1 : C.S ⊓ twoPointKernel G Ω α β ≠ ⊥ := fun h =>
    hT ((inf_twoPointKernel_eq_bot_iff hγ C.sylow).mp h)
  have hSαβ : C.S ≤ stabilizer G α ⊓ stabilizer G β := C.sylow.1.trans inf_le_left
  have hcardΔ : (holtDelta G Ω α β).ncard = Fintype.card (C.D.Ψc C.i₁) := by
    rw [← Nat.card_coe_set_eq, C.card_holtDelta_eq hr]
  have hconj : ∀ g ∈ C.S, ∀ x ∈ C.S ⊓ twoPointKernel G Ω α β,
      g * x * g⁻¹ ∈ C.S ⊓ twoPointKernel G Ω α β := fun g hg x hx =>
    Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg (Subgroup.mem_inf.mp hx).1) (inv_mem hg),
      conj_mem_twoPointKernel (hSαβ hg) (Subgroup.mem_inf.mp hx).2⟩
  refine C.exists_W_of_fusionIsSylowIn hS hαβ hr hX.2.1 hX1 (inf_le_left.trans hSαβ) le_rfl
    (fun δ hδ => iff_of_true (fun x hx => (mem_fixingSubgroup_iff G).mp
      (twoPointKernel_le_fixingSubgroup (Subgroup.mem_inf.mp hx).2) δ hδ) hδ)
    (by rw [hcardΔ]; exact hd) (by rw [hcardΔ]; exact C.D.five_le_card _) hX C.sylow.2.1 hSαβ
    (fun g hg => mem_normalizer_of_forall_conj_mem (hconj g hg) fun x hx => by
      simpa using hconj g⁻¹ (inv_mem hg) x hx) ?_
  rw [C.fixSet_S hαβ]
  rintro ω (rfl | rfl | rfl)
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr hγ

theorem exists_W_of_odd_of_not_transitive (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hr : Fintype.card C.D.ι = 1) (hd : Fintype.card (C.D.Ψc C.i₁) % 4 = 1)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) {δ₁ δ₂ : Ω}
    (hδ₁ : δ₁ ∈ holtDelta G Ω α β) (hδ₂ : δ₂ ∈ holtDelta G Ω α β) (hδ₁γ : δ₁ ≠ C.γ)
    (hδ₂γ : δ₂ ≠ C.γ) (hntr : ∀ s ∈ C.S, s • δ₁ ≠ δ₂) :
    ∃ W : Subgroup G, IsPGroup 2 W ∧ ∃ δ₁ δ₂ δ₃ : Ω, δ₁ ∈ holtDelta G Ω α β ∧
      δ₂ ∈ holtDelta G Ω α β ∧ δ₃ ∈ holtDelta G Ω α β ∧ δ₁ ≠ δ₂ ∧ δ₁ ≠ δ₃ ∧ δ₂ ≠ δ₃ ∧
        fixSet Ω W = {α, β, δ₁, δ₂, δ₃} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hγΔ : (C.γ : Ω) ∈ holtDelta G Ω α β := C.γ.2
  have hSαβ : C.S ≤ stabilizer G α ⊓ stabilizer G β := C.sylow.1.trans inf_le_left
  have hSγ : ∀ s ∈ C.S, s • (C.γ : Ω) = C.γ := fun s hs =>
    mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (C.sylow.1 hs)).2
  have hSΔ : ∀ s ∈ C.S, ∀ δ ∈ holtDelta G Ω α β, s • δ ∈ holtDelta G Ω α β := fun s hs δ hδ =>
    smul_mem_of_mem_stabilizer_set (stabilizer_inf_le_stabilizer_holtDelta α β (hSαβ hs)) hδ
  have hcardΔ : (holtDelta G Ω α β).ncard = Fintype.card (C.D.Ψc C.i₁) := by
    rw [← Nat.card_coe_set_eq, C.card_holtDelta_eq hr]
  have hd9 : 9 ≤ Fintype.card (C.D.Ψc C.i₁) := by
    have h5 := C.D.five_le_card C.i₁
    have hne : Fintype.card (C.D.Ψc C.i₁) ≠ 5 := fun h => C.five hr h hT
    omega
  set Θ := holtDelta G Ω α β \ {(C.γ : Ω)} with hΘdef
  have hΘcard : Θ.ncard = Fintype.card (C.D.Ψc C.i₁) - 1 := by
    rw [hΘdef, Set.ncard_sdiff (Set.singleton_subset_iff.mpr hγΔ) (Set.toFinite _), hcardΔ,
      Set.ncard_singleton]
  have hΘ : ∀ s ∈ C.S, ∀ θ ∈ Θ, s • θ ∈ Θ := fun s hs θ hθ => by
    refine ⟨hSΔ s hs θ hθ.1, fun h => hθ.2 ?_⟩
    rw [Set.mem_singleton_iff] at h ⊢
    rw [← hSγ s hs] at h
    exact smul_left_cancel s h
  have hfree : ∀ θ ∈ Θ, ∃ s ∈ C.S, s • θ ≠ θ := fun θ hθ => by
    by_contra h
    push Not at h
    have hθS : θ ∈ fixSet Ω C.S := fun s hs => h s hs
    rw [C.fixSet_S hαβ] at hθS
    rcases hθS with rfl | rfl | rfl
    · exact left_notMem_holtDelta hαβ hθ.1
    · exact right_notMem_holtDelta hαβ hθ.1
    · exact hθ.2 rfl
  obtain ⟨Λ', hΛ'Θ, hΛ'inv, hΛ'4, hΛ'ge, hΛ'ne⟩ := exists_invariant_subset_of_isPGroup
    C.sylow.2.1 (Set.toFinite Θ) hΘ hfree ⟨hδ₁, hδ₁γ⟩ ⟨hδ₂, hδ₂γ⟩ hntr (by omega)
  set Λ := insert (C.γ : Ω) Λ' with hΛdef
  have hγΛ' : (C.γ : Ω) ∉ Λ' := fun h => (hΛ'Θ h).2 rfl
  have hΛΔ : Λ ⊆ holtDelta G Ω α β := Set.insert_subset hγΔ fun x hx => (hΛ'Θ hx).1
  have hΛcard : Λ.ncard = Λ'.ncard + 1 := Set.ncard_insert_of_notMem hγΛ' (Set.toFinite _)
  have hdiff : holtDelta G Ω α β \ Λ = Θ \ Λ' := by
    ext x
    simp only [hΛdef, hΘdef, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    tauto
  have hlt : Λ'.ncard < Θ.ncard :=
    Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hΛ'Θ, hΛ'ne⟩) (Set.toFinite _)
  have hdcard : Nat.card ↥(holtDelta G Ω α β \ Λ) = Θ.ncard - Λ'.ncard := by
    rw [Nat.card_coe_set_eq, hdiff, Set.ncard_sdiff hΛ'Θ (Set.toFinite _)]
  have hev : Even (Nat.card ↥(holtDelta G Ω α β \ Λ)) := by
    rw [hdcard]
    exact ⟨(Θ.ncard - Λ'.ncard) / 2, by omega⟩
  have h2 : Nat.card ↥(holtDelta G Ω α β \ Λ) ≠ 2 := by
    rw [hdcard]
    omega
  have hSΛ : C.S ≤ stabilizer G Λ := le_stabilizer_of_forall_smul_mem fun s hs x hx => by
    rcases hx with rfl | hx
    · rw [hSγ s hs]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hΛ'inv s hs x hx)
  have hSH : C.S ≤ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G Λ := le_inf hSαβ hSΛ
  have hSsyl : fusionIsSylowIn 2 C.S (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G Λ ⊓
      stabilizer G (C.γ : Ω)) :=
    ⟨le_inf hSH (C.sylow.1.trans inf_le_right), C.sylow.2.1, fun P hPH hP hSP =>
      C.sylow.2.2 P (le_inf ((hPH.trans inf_le_left).trans inf_le_left)
        (hPH.trans inf_le_right)) hP hSP⟩
  have hNH : stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ ≤
      stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G Λ ⊓ stabilizer G (C.γ : Ω) := fun n hn =>
    have hnΛ := (Subgroup.mem_inf.mp hn).2
    ⟨⟨(Subgroup.mem_inf.mp hn).1, fixingSubgroup_le_stabilizer G Λ hnΛ⟩,
      (mem_fixingSubgroup_iff G).mp hnΛ _ (Set.mem_insert _ _)⟩
  have hsyl := fusionIsSylowIn_inf_of_forall_conj_mem hSsyl hNH fun h hh n hn =>
    conj_mem_inf_fixingSubgroup (Subgroup.mem_inf.mp hh).1 hn
  have hXΛ : ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (C.S ⊓ (stabilizer G α ⊓ stabilizer G β ⊓
      fixingSubgroup G Λ)) ↔ δ ∈ Λ := fun δ hδ =>
    C.mem_fixSet_iff_of_fusionIsSylowIn hS hαβ hr hΛΔ hev h2 hsyl hδ
  have hX1 : C.S ⊓ (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ) ≠ ⊥ := fun h => by
    obtain ⟨δ, hδΘ, hδΛ'⟩ := Set.nonempty_of_ssubset (Set.ssubset_iff_subset_ne.mpr
      ⟨hΛ'Θ, hΛ'ne⟩)
    have hδX : δ ∈ fixSet Ω (C.S ⊓ (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ)) := by
      rw [h]
      intro g hg
      rw [Subgroup.mem_bot.mp hg, one_smul]
    rcases (hXΛ δ hδΘ.1).mp hδX with h' | h'
    · exact hδΘ.2 h'
    · exact hδΛ' h'
  refine C.exists_W_of_fusionIsSylowIn hS hαβ hr hsyl.2.1 hX1
    ((inf_le_left.trans hSαβ)) hΛΔ hXΛ (by omega) (by omega) hsyl C.sylow.2.1 hSαβ
    (fun s hs => mem_normalizer_of_forall_conj_mem
      (fun x hx => Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hs (Subgroup.mem_inf.mp hx).1)
        (inv_mem hs), conj_mem_inf_fixingSubgroup (hSH hs) (Subgroup.mem_inf.mp hx).2⟩)
      (fun x hx => by
        have h' := conj_mem_inf_fixingSubgroup (hSH (inv_mem hs)) (Subgroup.mem_inf.mp hx).2
        rw [inv_inv] at h'
        exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hs) (Subgroup.mem_inf.mp hx).1)
          hs, h'⟩)) ?_
  rw [C.fixSet_S hαβ]
  rintro ω (rfl | rfl | rfl)
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr (Set.mem_insert _ _)

omit [FaithfulSMul G Ω] in
theorem exists_mem_longInvSwap_centralizer_swap (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hr : Fintype.card C.D.ι = 1) {W : Subgroup G} (hW : IsPGroup 2 W)
    (hWαβ : W ≤ stabilizer G α ⊓ stabilizer G β) {x y z : Ω} (hx : x ∈ holtDelta G Ω α β)
    (hy : y ∈ holtDelta G Ω α β) (hz : z ∈ holtDelta G Ω α β) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hxW : x ∈ fixSet Ω W) (hyW : y ∈ fixSet Ω W) (hzW : z ∈ fixSet Ω W) :
    ∃ c ∈ longInvSwap G Ω α β, c ∈ Subgroup.centralizer (W : Set G) ∧ c • x = y ∧ c • y = x ∧
      c • z = z := by
  classical
  set x' : holtDelta G Ω α β := ⟨x, hx⟩ with hx'
  set y' : holtDelta G Ω α β := ⟨y, hy⟩ with hy'
  set z' : holtDelta G Ω α β := ⟨z, hz⟩ with hz'
  have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
  have hxz' : x' ≠ z' := fun h => hxz (congrArg Subtype.val h)
  have hyz' : y' ≠ z' := fun h => hyz (congrArg Subtype.val h)
  set Λ : Set (holtDelta G Ω α β) := {x', y', z'} with hΛ
  have hsw : ∀ v, swap x' y' v ∈ Λ ↔ v ∈ Λ := fun v => by
    simp only [hΛ, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hvx : v = x'
    · subst hvx; simp
    by_cases hvy : v = y'
    · subst hvy; simp
    rw [swap_apply_of_ne_of_ne hvx hvy]
  set w : Perm Λ := (swap x' y').subtypePerm hsw with hw
  have hww : w * w = 1 := by
    ext v
    simp [hw, Perm.subtypePerm_apply]
  have hzΛ : z' ∈ Λ := by simp [hΛ]
  have hwfix : ∀ v : Λ, w v = v ↔ v = ⟨z', hzΛ⟩ := fun v => by
    obtain ⟨v, hv⟩ := v
    simp only [hΛ, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    simp only [hw, Subtype.ext_iff, Perm.subtypePerm_apply]
    rcases hv with rfl | rfl | rfl
    · rw [swap_apply_left]
      first
        | exact iff_of_false (fun h => hxy' h.symm) (fun h => hxz' h)
        | exact iff_of_false (fun h => hxy' (Subtype.ext h).symm) (fun h => hxz' (Subtype.ext h))
    · rw [swap_apply_right]
      first
        | exact iff_of_false (fun h => hxy' h) (fun h => hyz' h)
        | exact iff_of_false (fun h => hxy' (Subtype.ext h)) (fun h => hyz' (Subtype.ext h))
    · rw [swap_apply_of_ne_of_ne hxz'.symm hyz'.symm]
  have hcard := C.card_holtDelta_eq hr
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨yΔ, hyΔ, hyΔΛ, -⟩ := exists_mem_longInv_perm_apply_eq (Λ := Λ)
    (by rw [hcard]; exact C.D.odd_card_Ψc C.i₁)
    (by rw [hcard]; have := C.D.five_le_card C.i₁; omega) hww
    ⟨⟨z', hzΛ⟩, (hwfix _).mpr rfl, fun v hv => (hwfix v).mp hv⟩
  obtain ⟨u, hu, huΔ⟩ := C.exists_mem_longInvSwap_smul_eq hS hαβ hr hyΔ
  have hact : ∀ v (hv : v ∈ Λ), u • (v : Ω) = (swap x' y' v : Ω) := fun v hv => by
    rw [huΔ v, hyΔΛ v hv, hw, Perm.subtypePerm_apply]
  have hux : u • x = y := by
    have h := hact x' (by simp [hΛ])
    rwa [swap_apply_left] at h
  have huy : u • y = x := by
    have h := hact y' (by simp [hΛ])
    rwa [swap_apply_right] at h
  have huz : u • z = z := by
    have h := hact z' hzΛ
    rwa [swap_apply_of_ne_of_ne hxz'.symm hyz'.symm] at h
  have hustab : u ∈ stabilizer G ({x, y, z} : Set Ω) := by
    rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_insert, Set.smul_set_singleton,
      hux, huy, huz, Set.insert_comm]
  obtain ⟨c, hc, hcW, hcu⟩ := hS.exists_mem_longInvSwap_centralizer_eqOn hαβ hW hWαβ
    (Λ := {x, y, z}) ⟨x, Or.inl rfl⟩ (by
      rintro v (rfl | rfl | rfl) <;> assumption) hu hustab
  exact ⟨c, hc, hcW, by rw [hcu x (Or.inl rfl), hux], by rw [hcu y (Or.inr (Or.inl rfl)), huy],
    by rw [hcu z (Or.inr (Or.inr rfl)), huz]⟩

omit [FaithfulSMul G Ω] in
theorem alternatingGroup_le_centralizerImage (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hr : Fintype.card C.D.ι = 1) {W : Subgroup G} (hW : IsPGroup 2 W) {δ₁ δ₂ δ₃ : Ω}
    (h₁ : δ₁ ∈ holtDelta G Ω α β) (h₂ : δ₂ ∈ holtDelta G Ω α β) (h₃ : δ₃ ∈ holtDelta G Ω α β)
    (h12 : δ₁ ≠ δ₂) (h13 : δ₁ ≠ δ₃) (h23 : δ₂ ≠ δ₃) (hF : fixSet Ω W = {α, β, δ₁, δ₂, δ₃})
    [DecidablePred (· ∈ fixSet Ω W)] :
    alternatingGroup (fixSet Ω W) ≤ centralizerImage Ω W := by
  have hαδ : ∀ {δ : Ω}, δ ∈ holtDelta G Ω α β → α ≠ δ := fun hδ h =>
    left_notMem_holtDelta hαβ (by subst h; exact hδ)
  have hβδ : ∀ {δ : Ω}, δ ∈ holtDelta G Ω α β → β ≠ δ := fun hδ h =>
    right_notMem_holtDelta hαβ (by subst h; exact hδ)
  have hmem : ∀ {ω : Ω}, ω ∈ fixSet Ω W ↔ ω = α ∨ ω = β ∨ ω = δ₁ ∨ ω = δ₂ ∨ ω = δ₃ := by
    intro ω
    rw [hF]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hα : α ∈ fixSet Ω W := hmem.mpr (Or.inl rfl)
  have hβ : β ∈ fixSet Ω W := hmem.mpr (Or.inr (Or.inl rfl))
  have hd₁ : δ₁ ∈ fixSet Ω W := hmem.mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hd₂ : δ₂ ∈ fixSet Ω W := hmem.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hd₃ : δ₃ ∈ fixSet Ω W := hmem.mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hWαβ : W ≤ stabilizer G α ⊓ stabilizer G β :=
    le_inf (mem_fixSet_iff_le_stabilizer.mp hα) (mem_fixSet_iff_le_stabilizer.mp hβ)
  obtain ⟨c₁, hc₁, hc₁W, hc₁1, hc₁2, hc₁3⟩ := C.exists_mem_longInvSwap_centralizer_swap hS hαβ
    hr hW hWαβ h₁ h₂ h₃ h12 h13 h23 hd₁ hd₂ hd₃
  obtain ⟨c₂, hc₂, hc₂W, hc₂1, hc₂3, hc₂2⟩ := C.exists_mem_longInvSwap_centralizer_swap hS hαβ
    hr hW hWαβ h₁ h₃ h₂ h13 h12 h23.symm hd₁ hd₃ hd₂
  set d₁ : fixSet Ω W := ⟨δ₁, hd₁⟩
  set d₂ : fixSet Ω W := ⟨δ₂, hd₂⟩
  set d₃ : fixSet Ω W := ⟨δ₃, hd₃⟩
  have hd12 : d₁ ≠ d₂ := fun h => h12 (congrArg Subtype.val h)
  have hd13 : d₁ ≠ d₃ := fun h => h13 (congrArg Subtype.val h)
  have hd23 : d₂ ≠ d₃ := fun h => h23 (congrArg Subtype.val h)
  set π : Perm (fixSet Ω W) := (centralizerImageElt (Ω := Ω) hc₁W : Perm (fixSet Ω W)) *
    (centralizerImageElt (Ω := Ω) hc₂W : Perm (fixSet Ω W)) with hπdef
  have hπC : π ∈ centralizerImage Ω W :=
    mul_mem (centralizerImageElt (Ω := Ω) hc₁W).2 (centralizerImageElt (Ω := Ω) hc₂W).2
  have hsw : ∀ x : fixSet Ω W, (x : Ω) ≠ δ₁ → (x : Ω) ≠ δ₂ → (x : Ω) ≠ δ₃ →
      swap d₁ d₂ (swap d₁ d₃ x) = x := fun x e1 e2 e3 => by
    rw [swap_apply_of_ne_of_ne (show x ≠ d₁ from fun h => e1 (congrArg Subtype.val h))
        (show x ≠ d₃ from fun h => e3 (congrArg Subtype.val h)),
      swap_apply_of_ne_of_ne (show x ≠ d₁ from fun h => e1 (congrArg Subtype.val h))
        (show x ≠ d₂ from fun h => e2 (congrArg Subtype.val h))]
  have hπ : π = swap d₁ d₂ * swap d₁ d₃ := by
    ext ⟨ω, hω⟩
    have hπω : ((π ⟨ω, hω⟩ : fixSet Ω W) : Ω) = c₁ • c₂ • ω := rfl
    rw [hπω, Perm.mul_apply]
    rcases hmem.mp hω with h | h | h | h | h
    · rw [hsw _ (fun e => hαδ h₁ (h.symm.trans e)) (fun e => hαδ h₂ (h.symm.trans e))
        (fun e => hαδ h₃ (h.symm.trans e))]
      change c₁ • c₂ • ω = ω
      rw [h, hc₂.2, smul_eq_of_mem_longInvSwap hc₁]
    · rw [hsw _ (fun e => hβδ h₁ (h.symm.trans e)) (fun e => hβδ h₂ (h.symm.trans e))
        (fun e => hβδ h₃ (h.symm.trans e))]
      change c₁ • c₂ • ω = ω
      rw [h, smul_eq_of_mem_longInvSwap hc₂, hc₁.2]
    · rw [show (⟨ω, hω⟩ : fixSet Ω W) = d₁ from Subtype.ext h, swap_apply_left,
        swap_apply_of_ne_of_ne hd13.symm hd23.symm, h, hc₂1, hc₁3]
    · rw [show (⟨ω, hω⟩ : fixSet Ω W) = d₂ from Subtype.ext h,
        swap_apply_of_ne_of_ne hd12.symm hd23, swap_apply_right, h, hc₂2, hc₁2]
    · rw [show (⟨ω, hω⟩ : fixSet Ω W) = d₃ from Subtype.ext h, swap_apply_right,
        swap_apply_left, h, hc₂3, hc₁1]
  have h3c : IsThreeCycle π := hπ ▸ isThreeCycle_swap_mul_swap_same hd12 hd13 hd23
  have hcard : Nat.card (fixSet Ω W) = 5 := by
    rw [Nat.card_coe_set_eq, hF, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_insert_of_notMem, Set.ncard_pair h23]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h12, h13⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨(hβδ h₁), (hβδ h₂), (hβδ h₃)⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hαβ, hαδ h₁, hαδ h₂, hαδ h₃⟩
  have := (hS.star_centralizerImage hW (by rw [hcard]; omega)).isPretransitive
  have hprim : IsPreprimitive (centralizerImage Ω W) (fixSet Ω W) :=
    IsPreprimitive.of_prime_card (by rw [hcard]; norm_num)
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3c hπC

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω]
  in
theorem exists_W_of_mod_four_eq_three (hαβ : α ≠ β)
    (h3 : Fintype.card (C.D.Ψc C.i₁) % 4 = 3) :
    ∃ W : Subgroup G, IsPGroup 2 W ∧ ∃ δ₁ δ₂ δ₃ : Ω, δ₁ ∈ holtDelta G Ω α β ∧
      δ₂ ∈ holtDelta G Ω α β ∧ δ₃ ∈ holtDelta G Ω α β ∧ δ₁ ≠ δ₂ ∧ δ₁ ≠ δ₃ ∧ δ₂ ≠ δ₃ ∧
        fixSet Ω W = {α, β, δ₁, δ₂, δ₃} := by
  obtain ⟨W, hWP, hW5, hWsub⟩ := C.fix_five h3
  have hWS : W ≤ C.S := hWP.trans inf_le_left
  have hWαβ : W ≤ stabilizer G α ⊓ stabilizer G β :=
    hWS.trans (C.sylow.1.trans inf_le_left)
  refine ⟨W, C.sylow.2.1.to_le hWS, exists_eq_insert_of_ncard_eq_five hαβ
    (by rw [← Nat.card_coe_set_eq, hW5])
    (mem_fixSet_iff_le_stabilizer.mpr (hWαβ.trans inf_le_left))
    (mem_fixSet_iff_le_stabilizer.mpr (hWαβ.trans inf_le_right)) fun ω hω hωα hωβ => ?_⟩
  rcases hWsub hω with h | ⟨δ, -, rfl⟩
  · rcases h with h | h
    · exact absurd h hωα
    · exact absurd h hωβ
  · exact δ.2

end AltConfig

end OneCoordinate

section LemmaFourFour

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.fixSet_eq_of_index_two (hS : Sec4Setting G Ω) {α β γ : Ω} (hαβ : α ≠ β)
    (hγ : γ ∈ holtDelta G Ω α β) (h3Δ : 3 ≤ Nat.card (holtDelta G Ω α β))
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) {S : Subgroup G}
    (hSyl : fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ))
    (hFS : fixSet Ω S = {α, β, γ}) {x : G} (hxS : x ∈ Subgroup.centralizer (S : Set G))
    (hx2 : x * x = 1) (hxα : x • α = β) (hxΔ : ∀ δ ∈ holtDelta G Ω α β, x • δ = δ)
    {R : Subgroup G} (hRS : R ≤ S) {s : G} (hs : s ∈ S) (hsR : ∀ g ∈ S, g ∈ R ∨ s * g ∈ R)
    (hs2 : s * s = 1) (hsΔ : ∀ δ ∈ holtDelta G Ω α β, δ ≠ γ → s • δ ≠ δ) {r : G} (hr : r ∈ R)
    (hr2 : r * r = 1) (hrΔ : ∀ δ ∈ holtDelta G Ω α β, δ ≠ γ → r • δ ≠ δ) :
    fixSet Ω R = {α, β, γ} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSαβ : S ≤ stabilizer G α ⊓ stabilizer G β := hSyl.1.trans inf_le_left
  have hSfix : ∀ g ∈ S, g • α = α ∧ g • β = β ∧ g • γ = γ := fun g hg => by
    have h := hSyl.1 hg
    exact ⟨mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp h).1).1,
      mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp h).1).2,
      mem_stabilizer_iff.mp (Subgroup.mem_inf.mp h).2⟩
  have hSΔ : ∀ g ∈ S, ∀ δ ∈ holtDelta G Ω α β, g • δ ∈ holtDelta G Ω α β := fun g hg δ hδ => by
    rw [← mem_stabilizer_iff.mp (stabilizer_inf_le_stabilizer_holtDelta α β (hSαβ hg))]
    exact Set.smul_mem_smul_set hδ
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hsconj : ∀ g ∈ R, s * g * s⁻¹ ∈ R := fun g hg => by
    rcases hsR _ (mul_mem (mul_mem hs (hRS hg)) (inv_mem hs)) with h | h
    · exact h
    · have hgs : g * s ∈ R := by
        rwa [hsi, ← mul_assoc, ← mul_assoc, hs2, one_mul] at h
      have hsR' : s ∈ R := by simpa using mul_mem (inv_mem hg) hgs
      exact mul_mem (mul_mem hsR' hg) (inv_mem hsR')
  have hsN : s ∈ Subgroup.normalizer (R : Set G) :=
    mem_normalizer_of_forall_conj_mem hsconj fun g hg => by
      simpa [hsi] using hsconj g hg
  have hSN : S ≤ Subgroup.normalizer (R : Set G) := fun g hg => by
    rcases hsR g hg with h | h
    · exact Subgroup.le_normalizer h
    · have : g = s⁻¹ * (s * g) := by group
      rw [this]
      exact mul_mem (inv_mem hsN) (Subgroup.le_normalizer h)
  refine Set.Subset.antisymm (fun ω₀ hω₀R => ?_) (hFS ▸ fixSet_anti hRS)
  by_contra hω₀
  have hω₀s : s • ω₀ ≠ ω₀ := fun h => hω₀ (by
    rw [← hFS]
    intro g hg
    rcases hsR g hg with hgR | hsgR
    · exact hω₀R g hgR
    · have h' := hω₀R _ hsgR
      rw [mul_smul] at h'
      calc g • ω₀ = s • s • g • ω₀ := by rw [smul_smul, hs2, one_smul]
        _ = ω₀ := by rw [h', h])
  have hR : IsPGroup 2 R := hSyl.2.1.to_le hRS
  have hFR : ∀ ω ∈ ({α, β, γ} : Set Ω), ω ∈ fixSet Ω R := fun ω hω => fixSet_anti hRS (hFS ▸ hω)
  have hγα : γ ≠ α := fun h => left_notMem_holtDelta hαβ (h ▸ hγ)
  have hγβ : γ ≠ β := fun h => right_notMem_holtDelta hαβ (h ▸ hγ)
  have hαR := hFR α (Or.inl rfl)
  have hβR := hFR β (Or.inr (Or.inl rfl))
  have hγR := hFR γ (Or.inr (Or.inr rfl))
  set a : fixSet Ω R := ⟨α, hαR⟩ with ha
  set b : fixSet Ω R := ⟨β, hβR⟩ with hb
  set c : fixSet Ω R := ⟨γ, hγR⟩ with hc
  have hab : a ≠ b := fun h => hαβ (congrArg Subtype.val h)
  have h3 := hS.three_le_card_fixSet_of_ne hR hab
  have hR1 : R ≠ ⊥ := by
    intro h
    obtain ⟨δ, hδ, hδγ⟩ : ∃ δ ∈ holtDelta G Ω α β, δ ≠ γ := by
      by_contra h'
      push Not at h'
      have hsub : holtDelta G Ω α β ⊆ {γ} := fun δ hδ => h' δ hδ
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_singleton, ← Nat.card_coe_set_eq] at this
      omega
    exact hrΔ δ hδ hδγ (by rw [h] at hr; rw [Subgroup.mem_bot.mp hr, one_smul])
  obtain ⟨DK⟩ := hS.holtData_centralizerImage hR hR1 h3
  have hK := hS.star_centralizerImage hR h3
  have hB := hS.holtTheorem1Below_centralizerImage hR hR1 h3
  have hxyJ : ∀ y ∈ S, y * y = 1 → (∀ δ ∈ holtDelta G Ω α β, δ ≠ γ → y • δ ≠ δ) →
      x * y ∈ longInv G Ω ∧ ∀ ω, (x * y) • ω = ω → ω = γ := by
    intro y hy hy2 hyΔ
    have hxy : y * x = x * y := Subgroup.mem_centralizer_iff.mp hxS y hy
    have hxy2 : x * y * (x * y) = 1 := by
      rw [mul_assoc, ← mul_assoc y, hxy, mul_assoc, hy2, mul_one, hx2]
    have hxyα : (x * y) • α = β := by rw [mul_smul, (hSfix y hy).1, hxα]
    have hγfix : (x * y) • γ = γ := by rw [mul_smul, (hSfix y hy).2.2, hxΔ γ hγ]
    have hord : orderOf (x * y) = 2 := orderOf_eq_prime (by rw [sq]; exact hxy2) fun h =>
      hαβ (by rw [← hxyα, h, one_smul])
    have hJ := (hS.mem_longInv_iff_of_odd_twoPointKernel hαβ hT h3Δ hord hxyα).mpr
      ⟨γ, ⟨hγ, hγfix⟩, fun δ ⟨hδ, hδfix⟩ => by
        by_contra hne
        apply hyΔ δ hδ hne
        rwa [mul_smul, hxΔ _ (hSΔ y (hy) δ hδ)] at hδfix⟩
    refine ⟨hJ, fun ω hω => ?_⟩
    obtain ⟨z, -, hz⟩ := hJ.2
    exact (hz ω hω).trans (hz γ hγfix).symm
  obtain ⟨hxrJ, hxrfix⟩ := hxyJ r (hRS hr) hr2 hrΔ
  obtain ⟨hxsJ, -⟩ := hxyJ s hs hs2 hsΔ
  have hxR : x ∈ Subgroup.centralizer (R : Set G) := Subgroup.centralizer_le hRS hxS
  set xt := centralizerImageElt (Ω := Ω) hxR with hxt
  have hxtJ : xt ∈ longInv (centralizerImage Ω R) (fixSet Ω R) := by
    refine (mem_longInvAt_of_mul_self (δ := c) ?_ (fun ε => ?_) ⟨a, fun h =>
      hγα (congrArg Subtype.val h).symm⟩).1
    · refine Subtype.ext (Equiv.ext fun ω => Subtype.ext ?_)
      change x • x • (ω : Ω) = ω
      rw [smul_smul, hx2, one_smul]
    · constructor
      · intro h
        have h' : x • (ε : Ω) = ε := congrArg Subtype.val h
        refine Subtype.ext (hxrfix _ ?_)
        rw [mul_smul, mem_fixSet_iff_le_stabilizer.mp ε.2 hr, h']
      · rintro rfl
        exact Subtype.ext (hxΔ γ hγ)
  have hRΓ : R ≤ fixingSubgroup G (fixSet Ω R) := fun g hg =>
    (mem_fixingSubgroup_iff G).mpr fun ω hω => hω g hg
  have hxsN : x * s ∈ Subgroup.normalizer (R : Set G) :=
    mul_mem (Subgroup.centralizer_le_normalizer _ hxR) hsN
  obtain ⟨c₂, hc₂J, hc₂R, hc₂⟩ := hS.frattini h3 hR hRΓ hxsJ
    (le_stabilizer_of_forall_smul_mem (A := Subgroup.normalizer (R : Set G))
      (fun g hg ω hω => smul_mem_fixSet_of_mem_normalizer hg hω) hxsN)
  set ct := centralizerImageElt (Ω := Ω) hc₂R with hct
  have hctJ : ct ∈ longInv (centralizerImage Ω R) (fixSet Ω R) :=
    (hS.mem_longInv_centralizerImage_iff hR h3 ct).mpr ⟨c₂, hc₂J, hc₂R, fun _ => rfl⟩
  set st := xt * ct with hst
  have hstact : ∀ ω : fixSet Ω R, ((st : Perm (fixSet Ω R)) ω : Ω) = s • (ω : Ω) := fun ω => by
    change x • c₂ • (ω : Ω) = s • (ω : Ω)
    rw [hc₂ _ ω.2, smul_smul, ← mul_assoc, hx2, one_mul]
  have hstsoc : st ∈ DK.socPre := DK.mul_mem_socPre hK hxtJ hctJ
  have hstJ : st ∈ jHull (centralizerImage Ω R) (fixSet Ω R) := DK.socPre_le_jHull hstsoc
  have hstst : st * st = 1 := Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
    change ((st : Perm (fixSet Ω R)) ((st : Perm (fixSet Ω R)) ω) : Ω) = ω
    rw [hstact, hstact, smul_smul, hs2, one_smul]))
  have hst1 : st ≠ 1 := fun h => hω₀s (by
    have := hstact ⟨ω₀, hω₀R⟩
    rw [h] at this
    exact this.symm)
  have hstord : orderOf st = 2 := orderOf_eq_prime (by rw [sq, hstst]) hst1
  have hstfix : ∀ ω : fixSet Ω R, s • (ω : Ω) = ω → st • ω = ω := fun ω h =>
    Subtype.ext ((hstact ω).trans h)
  set stH : jHull (centralizerImage Ω R) (fixSet Ω R) := ⟨st, hstJ⟩ with hstH
  obtain ⟨k, hk⟩ : ∃ k, DK.ρ k stH ≠ 1 := by
    by_contra h
    push Not at h
    have hker : st ∈ jOrbitKernel (centralizerImage Ω R) (fixSet Ω R) :=
      DK.mem_jOrbitKernel_iff_rho.mpr h
    have hO : st ∈ jOddCore (centralizerImage Ω R) (fixSet Ω R) := by
      rw [← DK.socPre_inf_jOrbitKernel]
      exact ⟨hstsoc, hker⟩
    have h2 := Subgroup.orderOf_dvd_natCard _ hO
    rw [hstord] at h2
    obtain ⟨n, hn⟩ := odd_card_jOddCore (G := centralizerImage Ω R) (Ω := fixSet Ω R)
    omega
  set m := DK.ρ k stH with hm
  have hmM : m ∈ factorImage _ _ (DK.L k) (DK.ρ k) := DK.rho_mem_M_of_mem_socPre hstsoc k
  have hm2 : m * m = 1 := by rw [hm, ← map_mul, show stH * stH = 1 from Subtype.ext hstst,
    map_one]
  have hmfix : ∀ ω : fixSet Ω R, st • ω = ω → m (DK.coord ω k) = DK.coord ω k := fun ω h => by
    rw [hm, ← DK.coord_smul stH ω k]
    exact congrArg (fun z => DK.coord z k) h
  have hmα := hmfix a (hstfix a (hSfix s hs).1)
  have hmβ := hmfix b (hstfix b (hSfix s hs).2.1)
  have hmγ := hmfix c (hstfix c (hSfix s hs).2.2)
  obtain ⟨m', hm'M, hm'2, hm'1, hm'm, hmm', hm'α, hm'β, hm'γ⟩ :=
    (DK.factor k).exists_commute_mul_self_eq_one hmM hm2 hk hmα hmβ hmγ
  obtain ⟨h₀, hh₀, hh₀m⟩ := Subgroup.mem_map.mp hm'M
  obtain ⟨y₀, -, hy₀m, hy₀2⟩ := exists_mem_zpowers_orderOf_eq_two
    ((DK.ρ k).comp ((DK.L k).subgroupOf (jHull (centralizerImage Ω R) (fixSet Ω R))).subtype)
    (h := ⟨h₀, hh₀⟩) (by simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]; rw [hh₀m, hm'2])
    (by simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]; rw [hh₀m]; exact hm'1)
    fun z hz => by
      have hzO : ((z : jHull (centralizerImage Ω R) (fixSet Ω R)) : centralizerImage Ω R) ∈
          jOddCore (centralizerImage Ω R) (fixSet Ω R) := by
        have h' : (z : jHull (centralizerImage Ω R) (fixSet Ω R)) ∈
            (DK.L k).subgroupOf (jHull (centralizerImage Ω R) (fixSet Ω R)) ⊓ (DK.ρ k).ker :=
          ⟨z.2, hz⟩
        rw [DK.inf_ker k] at h'
        exact h'
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat odd_card_jOddCore (Subgroup.orderOf_dvd_natCard _ hzO)
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hy₀m
  rw [hh₀m] at hy₀m
  set yH : jHull (centralizerImage Ω R) (fixSet Ω R) :=
    (y₀ : jHull (centralizerImage Ω R) (fixSet Ω R)) with hyH
  set yt₀ : centralizerImage Ω R := (yH : centralizerImage Ω R) with hyt₀
  have hyL : yt₀ ∈ DK.L k := y₀.2
  have hyρk : DK.ρ k yH = m' := hy₀m
  have hyρ : ∀ j, j ≠ k → DK.ρ j yH = 1 := fun j hj => DK.rho_eq_one_of_mem_L (Ne.symm hj) hyL
  have hy2 : yt₀ * yt₀ = 1 := by
    have h := pow_orderOf_eq_one y₀
    rw [hy₀2, sq] at h
    have h1 := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_mul, Subgroup.coe_one] at h2
  have hyst : (yt₀ * st) ^ 2 ∈ jOddCore (centralizerImage Ω R) (fixSet Ω R) := by
    rw [← DK.socPre_inf_jOrbitKernel]
    refine Subgroup.mem_inf.mpr ⟨pow_mem (mul_mem (DK.L_le_socPre k hyL) hstsoc) 2, ?_⟩
    show (((yH * stH) ^ 2 : jHull (centralizerImage Ω R) (fixSet Ω R)) :
      centralizerImage Ω R) ∈ jOrbitKernel (centralizerImage Ω R) (fixSet Ω R)
    rw [DK.mem_jOrbitKernel_iff_rho]
    intro j
    rw [map_pow, map_mul]
    by_cases hj : j = k
    · subst hj
      rw [hyρk, ← hm, sq, mul_assoc, ← mul_assoc m, hmm', mul_assoc, hm2, mul_one, hm'2]
    · rw [hyρ j hj, one_mul, ← map_pow, sq, show stH * stH = 1 from Subtype.ext hstst, map_one]
  obtain ⟨p, hp, hpc⟩ := exists_mem_conj_commute_of_odd odd_card_jOddCore hy2 hstst hyst
  have hpJ : p ∈ jHull (centralizerImage Ω R) (fixSet Ω R) := jOddCore_le_jHull hp
  set yt := p * yt₀ * p⁻¹ with hytdef
  have hytJ : yt ∈ jHull (centralizerImage Ω R) (fixSet Ω R) :=
    mul_mem (mul_mem hpJ yH.2) (inv_mem hpJ)
  set ytH : jHull (centralizerImage Ω R) (fixSet Ω R) := ⟨yt, hytJ⟩ with hytH
  have hytρ : ∀ j, DK.ρ j ytH = DK.ρ j yH := fun j => by
    rw [show ytH = ⟨p, hpJ⟩ * yH * ⟨p, hpJ⟩⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv,
      DK.rho_eq_one_of_mem_jOddCore (h := ⟨p, hpJ⟩) hp j, one_mul, inv_one, mul_one]
  have hyt2 : yt * yt = 1 := by
    calc yt * yt = p * (yt₀ * yt₀) * p⁻¹ := by rw [hytdef]; group
      _ = 1 := by rw [hy2, mul_one, mul_inv_cancel]
  have hyt1 : yt ≠ 1 := fun h => hm'1 (by
    rw [← hyρk, ← hytρ k, show ytH = 1 from Subtype.ext h, map_one])
  have hytord : orderOf yt = 2 := orderOf_eq_prime (by rw [sq, hyt2]) hyt1
  have hytsoc : yt ∈ DK.socPre :=
    mul_mem (mul_mem (DK.jOddCore_le_socPre hp) (DK.L_le_socPre k hyL))
      (inv_mem (DK.jOddCore_le_socPre hp))
  have hytfix : ∀ ω : fixSet Ω R, m' (DK.coord ω k) = DK.coord ω k → yt • ω = ω := by
    intro ω hω
    have hstab : yt • ω ∈ orbit (jOddCore (centralizerImage Ω R) (fixSet Ω R)) ω := by
      rw [← DK.coord_eq_iff]
      funext j
      rw [show yt • ω = (ytH : centralizerImage Ω R) • ω from rfl, DK.coord_smul, hytρ j]
      by_cases hj : j = k
      · subst hj
        rw [hyρk, hω]
      · rw [hyρ j hj, Perm.one_apply]
    exact (DK.lemma_2_4_iv hK hB hytJ hytord hstab).1 hytsoc ω (mem_orbit_self ω)
  have hytα := hytfix a hm'α
  have hytβ := hytfix b hm'β
  have hytγ := hytfix c hm'γ
  set A := Subgroup.normalizer (R : Set G) ⊓ (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ)
    with hA
  have hAΓ : A ≤ stabilizer G (fixSet Ω R) := inf_le_left.trans
    (le_stabilizer_of_forall_smul_mem fun g hg ω hω =>
      smul_mem_fixSet_of_mem_normalizer hg hω)
  have hSA : S ≤ A := le_inf hSN hSyl.1
  have hSsylA : fusionIsSylowIn 2 S A :=
    ⟨hSA, hSyl.2.1, fun P hPA hP hSP => hSyl.2.2 P (hPA.trans inf_le_right) hP hSP⟩
  have hŜ := fusionIsSylowIn_inducedPerm (h := hAΓ) hSsylA
  set sp : Perm (fixSet Ω R) := (st : Perm (fixSet Ω R)) with hsp
  set yp : Perm (fixSet Ω R) := (yt : Perm (fixSet Ω R)) with hyp
  have hŜsub : ((inducedPerm S (fixSet Ω R) (hSA.trans hAΓ) : Subgroup (Perm (fixSet Ω R))) :
      Set (Perm (fixSet Ω R))) ⊆ {1, sp} := by
    intro π hπ
    obtain ⟨g, hg, hgπ⟩ := mem_inducedPerm.mp hπ
    rcases hsR g hg with hgR | hsgR
    · exact Or.inl (Equiv.ext fun ω => Subtype.ext ((hgπ ω).trans (ω.2 g hgR)))
    · refine Or.inr (Equiv.ext fun ω => Subtype.ext ?_)
      rw [hgπ ω, hsp, hstact ω]
      have h' := ω.2 _ hsgR
      rw [mul_smul] at h'
      calc g • (ω : Ω) = s • s • g • (ω : Ω) := by rw [smul_smul, hs2, one_smul]
        _ = s • (ω : Ω) := by rw [h']
  have hŜcard : Nat.card (inducedPerm S (fixSet Ω R) (hSA.trans hAΓ)) ≤ 2 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard hŜsub (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans
      (by rw [Set.ncard_singleton]))
  have hspA : sp ∈ inducedPerm A (fixSet Ω R) hAΓ :=
    mem_inducedPerm.mpr ⟨s, hSA hs, fun ω => hstact ω⟩
  have hypA : yp ∈ inducedPerm A (fixSet Ω R) hAΓ := by
    obtain ⟨c₃, hc₃R, hc₃⟩ := mem_centralizerImage.mp yt.2
    have hfix3 : ∀ ω : fixSet Ω R, yt • ω = ω → c₃ • (ω : Ω) = ω := fun ω h =>
      (hc₃ ω).symm.trans (congrArg Subtype.val h)
    exact mem_inducedPerm.mpr ⟨c₃, Subgroup.mem_inf.mpr ⟨Subgroup.centralizer_le_normalizer _
      hc₃R, Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr (hfix3 a hytα),
        mem_stabilizer_iff.mpr (hfix3 b hytβ)⟩, mem_stabilizer_iff.mpr (hfix3 c hytγ)⟩⟩, hc₃⟩
  have hsp2 : sp * sp = 1 := by
    rw [hsp, ← Subgroup.coe_mul, hstst, Subgroup.coe_one]
  have hyp2 : yp * yp = 1 := by
    rw [hyp, ← Subgroup.coe_mul, hyt2, Subgroup.coe_one]
  have hcomm : Commute sp yp := by
    have h := hpc.eq
    exact (congrArg (fun z : centralizerImage Ω R => (z : Perm (fixSet Ω R))) h).symm
  have hsp1 : sp ≠ 1 := fun h => hst1 (Subtype.ext h)
  have hyp1 : yp ≠ 1 := fun h => hyt1 (Subtype.ext h)
  have hspyp : sp ≠ yp := fun h => hm'm (by
    rw [← hyρk, ← hytρ k, hm, show stH = ytH from Subtype.ext (Subtype.ext h)])
  set Q := Subgroup.zpowers sp ⊔ Subgroup.zpowers yp with hQ
  have hQ2 : IsPGroup 2 Q := IsPGroup.to_sup_of_normal_left'
    (isPGroup_zpowers_of_pow_two_pow_eq_one (a := 1) (by rw [pow_one, sq, hsp2]))
    (isPGroup_zpowers_of_pow_two_pow_eq_one (a := 1) (by rw [pow_one, sq, hyp2]))
    (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun h hh => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        exact (hcomm.zpow_left n).eq)))
  have hQA : Q ≤ inducedPerm A (fixSet Ω R) hAΓ :=
    sup_le (Subgroup.zpowers_le.mpr hspA) (Subgroup.zpowers_le.mpr hypA)
  have hspQ : sp ∈ Q := Subgroup.mem_sup_left (Subgroup.mem_zpowers sp)
  have hypQ : yp ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers yp)
  have h4 : ({1, sp, yp, sp * yp} : Set (Perm (fixSet Ω R))).ncard = 4 := by
    have hspyp1 : sp * yp ≠ 1 := fun h => hspyp (mul_left_cancel (hsp2.trans h.symm))
    have hspyp2 : sp * yp ≠ sp := fun h => hyp1 (mul_left_cancel (h.trans (mul_one sp).symm))
    have hspyp3 : sp * yp ≠ yp := fun h => hsp1 (mul_right_cancel (h.trans (one_mul yp).symm))
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hspyp3.symm]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hspyp, hspyp2.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hsp1.symm, hyp1.symm, hspyp1.symm⟩
  have hQcard : 4 ≤ Nat.card Q := by
    rw [← h4, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro z (rfl | rfl | rfl | rfl)
    · exact Q.one_mem
    · exact hspQ
    · exact hypQ
    · exact Q.mul_mem hspQ hypQ
  obtain ⟨P, hQP, hP⟩ := exists_fusionIsSylowIn_ge hQ2 hQA
  have hPcard := (card_eq_of_fusionIsSylowIn hP).trans (card_eq_of_fusionIsSylowIn hŜ).symm
  have := Subgroup.card_le_of_le hQP
  omega

end LemmaFourFour

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω}

namespace AltConfig

variable (C : AltConfig G Ω α β)

theorem exists_W_of_odd_of_transitive (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hr : Fintype.card C.D.ι = 1) (hd : Fintype.card (C.D.Ψc C.i₁) % 4 = 1)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β)))
    (htr : ∀ δ₁ ∈ holtDelta G Ω α β, δ₁ ≠ C.γ → ∀ δ₂ ∈ holtDelta G Ω α β, δ₂ ≠ C.γ →
      ∃ s ∈ C.S, s • δ₁ = δ₂) :
    ∃ W : Subgroup G, IsPGroup 2 W ∧ ∃ δ₁ δ₂ δ₃ : Ω, δ₁ ∈ holtDelta G Ω α β ∧
      δ₂ ∈ holtDelta G Ω α β ∧ δ₃ ∈ holtDelta G Ω α β ∧ δ₁ ≠ δ₂ ∧ δ₁ ≠ δ₃ ∧ δ₂ ≠ δ₃ ∧
        fixSet Ω W = {α, β, δ₁, δ₂, δ₃} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hγΔ : (C.γ : Ω) ∈ holtDelta G Ω α β := C.γ.2
  have hSαβ : C.S ≤ stabilizer G α ⊓ stabilizer G β := C.sylow.1.trans inf_le_left
  have hSγ : ∀ s ∈ C.S, s • (C.γ : Ω) = C.γ := fun s hs =>
    mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (C.sylow.1 hs)).2
  have hSΔ : C.S ≤ stabilizer G (holtDelta G Ω α β) :=
    hSαβ.trans (stabilizer_inf_le_stabilizer_holtDelta α β)
  have hcardΔ : (holtDelta G Ω α β).ncard = Fintype.card (C.D.Ψc C.i₁) := by
    rw [← Nat.card_coe_set_eq, C.card_holtDelta_eq hr]
  have hd9 : 9 ≤ Fintype.card (C.D.Ψc C.i₁) := by
    have h5 := C.D.five_le_card C.i₁
    have hne : Fintype.card (C.D.Ψc C.i₁) ≠ 5 := fun h => C.five hr h hT
    omega
  have h3Δ : 3 ≤ Nat.card (holtDelta G Ω α β) := by rw [Nat.card_coe_set_eq]; omega
  have hT1 : C.S ⊓ twoPointKernel G Ω α β = ⊥ :=
    (inf_twoPointKernel_eq_bot_iff C.γ.2 C.sylow).mpr hT
  have hfaith : ∀ g ∈ C.S, ∀ g' ∈ C.S, (∀ δ ∈ holtDelta G Ω α β, g • δ = g' • δ) → g = g' := by
    intro g hg g' hg' h
    have hmem : g * g'⁻¹ ∈ C.S ⊓ twoPointKernel G Ω α β := Subgroup.mem_inf.mpr
      ⟨mul_mem hg (inv_mem hg'), Subgroup.mem_inf.mpr ⟨hSαβ (mul_mem hg (inv_mem hg')),
        (mem_fixingSubgroup_iff G).mpr fun δ hδ => by
          have hδ' : g'⁻¹ • δ ∈ holtDelta G Ω α β := by
            rw [← mem_stabilizer_iff.mp (hSΔ (inv_mem hg'))]
            exact Set.smul_mem_smul_set hδ
          rw [mul_smul, h _ hδ', smul_inv_smul]⟩⟩
    rw [hT1, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp hmem
  have hfix1 : stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G ({(C.γ : Ω)} : Set Ω) =
      stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω) := by
    congr 1
    ext g
    simp [mem_fixingSubgroup_iff, mem_stabilizer_iff]
  have hV := C.fusionIsSylowIn_inducedPerm_inf_alternatingGroup hS hαβ hr
    (Set.singleton_subset_iff.mpr hγΔ) (hfix1 ▸ C.sylow)
  set Λ₀ : Set (holtDelta G Ω α β) := Subtype.val ⁻¹' ({(C.γ : Ω)} : Set Ω) with hΛ₀
  set Q := inducedPerm C.S (holtDelta G Ω α β) hSΔ with hQ
  obtain ⟨δ₀, hδ₀, hδ₀γ⟩ : ∃ δ ∈ holtDelta G Ω α β, δ ≠ C.γ := by
    by_contra h
    push Not at h
    have hsub : holtDelta G Ω α β ⊆ {(C.γ : Ω)} := fun δ hδ =>
      Set.mem_singleton_iff.mpr (h δ hδ)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at this
    omega
  have horb : orbit C.S δ₀ = holtDelta G Ω α β \ {(C.γ : Ω)} := by
    ext ω
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      refine ⟨by rw [← mem_stabilizer_iff.mp (hSΔ hg)]; exact Set.smul_mem_smul_set hδ₀,
        fun h => hδ₀γ ?_⟩
      rw [Set.mem_singleton_iff] at h
      change g • δ₀ = C.γ at h
      rw [← hSγ g hg] at h
      exact smul_left_cancel g h
    · rintro ⟨hω, hωγ⟩
      obtain ⟨g, hg, hgω⟩ := htr δ₀ hδ₀ hδ₀γ ω hω hωγ
      exact ⟨⟨g, hg⟩, hgω⟩
  obtain ⟨e, he⟩ := C.sylow.2.1.card_orbit δ₀
  have hΛ₀c : Nat.card ↥(Λ₀ᶜ) = 2 ^ e := by
    rw [← he, horb]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcardd : Fintype.card (C.D.Ψc C.i₁) = 2 ^ e + 1 := by
    have h1 : (holtDelta G Ω α β \ {(C.γ : Ω)}).ncard = Fintype.card (C.D.Ψc C.i₁) - 1 := by
      rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr hγΔ) (Set.toFinite _), hcardΔ,
        Set.ncard_singleton]
    rw [← horb, ← Nat.card_coe_set_eq, he] at h1
    omega
  have he3 : 3 ≤ e := by
    by_contra h
    interval_cases e <;> omega
  have hQ2 : IsPGroup 2 Q := isPGroup_inducedPerm C.sylow.2.1 hSΔ
  have hQΛ₀ : Q ≤ fixingSubgroup (Perm (holtDelta G Ω α β)) Λ₀ := fun π hπ => by
    obtain ⟨g, hg, hgπ⟩ := mem_inducedPerm.mp hπ
    refine (mem_fixingSubgroup_iff _).mpr fun x hx => Subtype.ext ?_
    rw [Perm.smul_def, hgπ x]
    have hx' : (x : Ω) = C.γ := hx
    rw [hx', hSγ g hg]
  obtain ⟨H₁, hH₁sub, hH₁card, hQH, ⟨sb, hsbV, hsb2, hsbsw, rb, hrbV, hrb2, hrbH, hrbfree, -⟩,
    -⟩ := exists_half_system_of_fusionIsSylowIn_alternatingGroup_inf_fixingSubgroup
      (by omega : 2 ≤ e) hΛ₀c hV hQ2 inf_le_left hQΛ₀
  have hmemΛ₀c : ∀ x : holtDelta G Ω α β, x ∈ Λ₀ᶜ ↔ (x : Ω) ≠ C.γ := fun x => Iff.rfl
  obtain ⟨s₀, hs₀S, hs₀⟩ := mem_inducedPerm.mp (Subgroup.mem_inf.mp hsbV).1
  obtain ⟨r₀, hr₀S, hr₀⟩ := mem_inducedPerm.mp (Subgroup.mem_inf.mp hrbV).1
  have hsq : ∀ (g : G) (hg : g ∈ C.S) (π : Perm (holtDelta G Ω α β)), π ^ 2 = 1 →
      (∀ ω : holtDelta G Ω α β, (π ω : Ω) = g • (ω : Ω)) → g * g = 1 := fun g hg π hπ2 hgπ =>
    hfaith _ (mul_mem hg hg) _ (one_mem _) fun δ hδ => by
      rw [one_smul, mul_smul, ← hgπ ⟨δ, hδ⟩, ← hgπ, ← Perm.mul_apply, ← sq, hπ2, Perm.one_apply]
  have hs₀2 : s₀ * s₀ = 1 := hsq s₀ hs₀S sb hsb2 hs₀
  have hr₀2 : r₀ * r₀ = 1 := hsq r₀ hr₀S rb hrb2 hr₀
  have hs₀Δ : ∀ δ ∈ holtDelta G Ω α β, δ ≠ C.γ → s₀ • δ ≠ δ := fun δ hδ hδγ h => by
    have h1 := hsbsw ⟨δ, hδ⟩ hδγ
    rw [show sb ⟨δ, hδ⟩ = ⟨δ, hδ⟩ from Subtype.ext ((hs₀ _).trans h)] at h1
    tauto
  have hr₀Δ : ∀ δ ∈ holtDelta G Ω α β, δ ≠ C.γ → r₀ • δ ≠ δ := fun δ hδ hδγ h =>
    hrbfree ⟨δ, hδ⟩ hδγ (Subtype.ext ((hr₀ _).trans h))
  have hstabH : ∀ g ∈ C.S, ∀ π : Perm (holtDelta G Ω α β),
      (∀ ω : holtDelta G Ω α β, (π ω : Ω) = g • (ω : Ω)) → (∀ x, π x ∈ H₁ ↔ x ∈ H₁) →
        g ∈ stabilizer G (Subtype.val '' H₁) := by
    intro g hg π hgπ hπH
    rw [mem_stabilizer_set]
    intro ω
    constructor
    · rintro ⟨y, hy, hyω⟩
      have hωΔ : ω ∈ holtDelta G Ω α β := by
        have h := mem_stabilizer_iff.mp (hSΔ (inv_mem hg))
        rw [← h, ← inv_smul_smul g ω, ← hyω]
        exact Set.smul_mem_smul_set y.2
      have hπω : π ⟨ω, hωΔ⟩ = y := Subtype.ext ((hgπ _).trans hyω.symm)
      exact ⟨⟨ω, hωΔ⟩, (hπH _).mp (hπω ▸ hy), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨π x, (hπH x).mpr hx, hgπ x⟩
  set R := C.S ⊓ stabilizer G (Subtype.val '' H₁) with hRdef
  have hRS : R ≤ C.S := inf_le_left
  have hr₀R : r₀ ∈ R := Subgroup.mem_inf.mpr ⟨hr₀S, hstabH r₀ hr₀S rb hr₀ hrbH⟩
  have hsR : ∀ g ∈ C.S, g ∈ R ∨ s₀ * g ∈ R := by
    intro g hg
    set πg := inducedHom C.S (holtDelta G Ω α β) hSΔ ⟨g, hg⟩
    have hπg : ∀ ω : holtDelta G Ω α β, (πg ω : Ω) = g • (ω : Ω) := fun ω => rfl
    rcases hQH πg ⟨⟨g, hg⟩, rfl⟩ with h | h
    · exact Or.inl (Subgroup.mem_inf.mpr ⟨hg, hstabH g hg πg hπg h⟩)
    · refine Or.inr (Subgroup.mem_inf.mpr ⟨mul_mem hs₀S hg, hstabH _ (mul_mem hs₀S hg)
        (sb * πg) (fun ω => by rw [Perm.mul_apply, hs₀, hπg, mul_smul]) fun x => ?_⟩)
      by_cases hx : x ∈ Λ₀
      · have hγ' : πg x = x := (mem_fixingSubgroup_iff _).mp (hQΛ₀ ⟨⟨g, hg⟩, rfl⟩) x hx
        have hsx : sb x = x := (mem_fixingSubgroup_iff _).mp
          (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hsbV).2).2 x hx
        rw [Perm.mul_apply, hγ', hsx]
      · have hπx : πg x ∈ Λ₀ᶜ := fun h' => hx (by
          have h1 : g • (x : Ω) = C.γ := (hπg x).symm.trans h'
          show (x : Ω) = C.γ
          rw [← hSγ g hg] at h1
          exact smul_left_cancel g h1)
        rw [Perm.mul_apply, hsbsw _ hπx, h x hx]
        tauto
  have hwΔ : C.w ∈ stabilizer G (holtDelta G Ω α β) :=
    mem_stabilizer_holtDelta_of_mem_longInvSwap C.w_mem
  set wb := inducedHom (stabilizer G (holtDelta G Ω α β)) (holtDelta G Ω α β) le_rfl ⟨C.w, hwΔ⟩
    with hwb
  have hwbact : ∀ ω : holtDelta G Ω α β, (wb ω : Ω) = C.w • (ω : Ω) := fun ω => rfl
  have hwbΛ₀ : wb ∈ fixingSubgroup (Perm (holtDelta G Ω α β)) Λ₀ :=
    (mem_fixingSubgroup_iff _).mpr fun x hx => Subtype.ext (by
      rw [Perm.smul_def, hwbact]
      have hx' : (x : Ω) = C.γ := hx
      rw [hx', C.w_fix])
  have hwbV : wb ∈ Q ⊓ (alternatingGroup (holtDelta G Ω α β) ⊓
      fixingSubgroup (Perm (holtDelta G Ω α β)) Λ₀) := by
    refine mem_of_commute_of_fusionIsSylowIn_alternatingGroup_inf_fixingSubgroup
      (by rw [hΛ₀c]; exact Nat.pow_dvd_pow 2 (by omega : 2 ≤ e)) hV hwbΛ₀ fun v hv => ?_
    obtain ⟨g, hg, hgv⟩ := mem_inducedPerm.mp (Subgroup.mem_inf.mp hv).1
    have hwg : g * C.w = C.w * g := Subgroup.mem_centralizer_iff.mp C.w_comm g hg
    refine Equiv.ext fun ω => Subtype.ext ?_
    rw [Perm.mul_apply, Perm.mul_apply, hwbact, hgv, hgv, hwbact, ← mul_smul, ← mul_smul, hwg]
  obtain ⟨z, hzS, hz⟩ := mem_inducedPerm.mp (Subgroup.mem_inf.mp hwbV).1
  have hzw : ∀ δ ∈ holtDelta G Ω α β, z • δ = C.w • δ := fun δ hδ =>
    (hz ⟨δ, hδ⟩).symm.trans (hwbact ⟨δ, hδ⟩)
  have hzC : z ∈ Subgroup.centralizer (C.S : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun g hg => hfaith _ (mul_mem hg hzS) _ (mul_mem hzS hg) fun δ hδ => by
      have hgδ : g • δ ∈ holtDelta G Ω α β := by
        rw [← mem_stabilizer_iff.mp (hSΔ hg)]
        exact Set.smul_mem_smul_set hδ
      rw [mul_smul, mul_smul, hzw δ hδ, hzw _ hgδ, ← mul_smul, ← mul_smul,
        Subgroup.mem_centralizer_iff.mp C.w_comm g hg]
  set x := C.w * z⁻¹ with hxdef
  have hwz : z * C.w = C.w * z := Subgroup.mem_centralizer_iff.mp C.w_comm z hzS
  have hw2 : C.w * C.w = 1 := mul_self_eq_one_of_mem_longInv C.w_mem.1
  have hzz : z * z = 1 := hfaith _ (mul_mem hzS hzS) _ (one_mem _) fun δ hδ => by
    have hwδ : C.w • δ ∈ holtDelta G Ω α β := by
      rw [← mem_stabilizer_iff.mp hwΔ]
      exact Set.smul_mem_smul_set hδ
    rw [one_smul, mul_smul, hzw δ hδ, hzw _ hwδ, smul_smul, hw2, one_smul]
  have hxS : x ∈ Subgroup.centralizer (C.S : Set G) := mul_mem C.w_comm (inv_mem hzC)
  have hx2 : x * x = 1 := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    rw [hxdef, hzi, mul_assoc, ← mul_assoc z, hwz, mul_assoc, hzz, mul_one, hw2]
  have hxα : x • α = β := by
    have hzα : z⁻¹ • α = α := by
      rw [inv_smul_eq_iff]
      exact (mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hSαβ hzS)).1).symm
    rw [hxdef, mul_smul, hzα]
    exact C.w_mem.2
  have hxΔ : ∀ δ ∈ holtDelta G Ω α β, x • δ = δ := fun δ hδ => by
    have hzδ : z⁻¹ • δ ∈ holtDelta G Ω α β := by
      rw [← mem_stabilizer_iff.mp (hSΔ (inv_mem hzS))]
      exact Set.smul_mem_smul_set hδ
    rw [hxdef, mul_smul, ← hzw _ hzδ, smul_inv_smul]
  have hFR := hS.fixSet_eq_of_index_two hαβ hγΔ h3Δ hT C.sylow (C.fixSet_S hαβ) hxS hx2 hxα hxΔ
    hRS hs₀S hsR hs₀2 hs₀Δ hr₀R hr₀2 hr₀Δ
  set Λ := insert (C.γ : Ω) (Subtype.val '' H₁) with hΛdef
  have hγH : (C.γ : Ω) ∉ Subtype.val '' H₁ := fun ⟨y, hy, hyγ⟩ => hH₁sub hy hyγ
  have hΛΔ : Λ ⊆ holtDelta G Ω α β :=
    Set.insert_subset hγΔ fun _ ⟨y, _, hy⟩ => hy ▸ y.2
  have hH₁ncard : (Subtype.val '' H₁).ncard = 2 ^ (e - 1) := by
    rw [Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
    have h2e : 2 ^ e = 2 * 2 ^ (e - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hΛcard : Λ.ncard = 2 ^ (e - 1) + 1 := by
    rw [hΛdef, Set.ncard_insert_of_notMem hγH (Set.toFinite _), hH₁ncard]
  have h4e : 4 ∣ 2 ^ (e - 1) := Nat.pow_dvd_pow 2 (by omega : 2 ≤ e - 1)
  have he8 : 4 ≤ 2 ^ (e - 1) := Nat.le_of_dvd (by positivity) h4e
  have hdiffcard : Nat.card ↥(holtDelta G Ω α β \ Λ) = 2 ^ (e - 1) := by
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff hΛΔ (Set.toFinite _), hcardΔ, hΛcard, hcardd]
    have h2e : 2 ^ e = 2 * 2 ^ (e - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hR2 : IsPGroup 2 R := C.sylow.2.1.to_le hRS
  have hRΛ : R ≤ stabilizer G Λ := le_stabilizer_of_forall_smul_mem fun g hg ω hω => by
    obtain ⟨hgS, hgH⟩ := Subgroup.mem_inf.mp hg
    rcases hω with rfl | hω
    · rw [hSγ g hgS]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ((mem_stabilizer_set.mp hgH ω).mpr hω)
  have hRA : R ≤ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G Λ ⊓ stabilizer G (C.γ : Ω) :=
    le_inf (le_inf (hRS.trans hSαβ) hRΛ) (hRS.trans (C.sylow.1.trans inf_le_right))
  obtain ⟨P, hRP, hP⟩ := exists_fusionIsSylowIn_ge hR2 hRA
  have hNH : stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ ≤
      stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G Λ ⊓ stabilizer G (C.γ : Ω) := fun n hn =>
    have hnΛ := (Subgroup.mem_inf.mp hn).2
    ⟨⟨(Subgroup.mem_inf.mp hn).1, fixingSubgroup_le_stabilizer G Λ hnΛ⟩,
      (mem_fixingSubgroup_iff G).mp hnΛ _ (Set.mem_insert _ _)⟩
  have hsyl := fusionIsSylowIn_inf_of_forall_conj_mem hP hNH fun h hh n hn =>
    conj_mem_inf_fixingSubgroup (Subgroup.mem_inf.mp hh).1 hn
  have hev : Even (Nat.card ↥(holtDelta G Ω α β \ Λ)) := by
    rw [hdiffcard]
    exact (even_iff_two_dvd.mpr ((dvd_mul_right 2 2).trans h4e))
  have h2 : Nat.card ↥(holtDelta G Ω α β \ Λ) ≠ 2 := by
    rw [hdiffcard]
    omega
  have hXΛ : ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (P ⊓ (stabilizer G α ⊓ stabilizer G β ⊓
      fixingSubgroup G Λ)) ↔ δ ∈ Λ := fun δ hδ =>
    C.mem_fixSet_iff_of_fusionIsSylowIn hS hαβ hr hΛΔ hev h2 hsyl hδ
  have hX1 : P ⊓ (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ) ≠ ⊥ := fun h => by
    have hne : (holtDelta G Ω α β \ Λ).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _), ← Nat.card_coe_set_eq, hdiffcard]
      omega
    obtain ⟨δ, hδΔ, hδΛ⟩ := hne
    have hδX : δ ∈ fixSet Ω (P ⊓ (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G Λ)) := by
      rw [h]
      intro g hg
      rw [Subgroup.mem_bot.mp hg, one_smul]
    exact hδΛ ((hXΛ δ hδΔ).mp hδX)
  have hPαβ : P ≤ stabilizer G α ⊓ stabilizer G β := hP.1.trans (inf_le_left.trans inf_le_left)
  have hPH := hP.1
  refine C.exists_W_of_fusionIsSylowIn hS hαβ hr hsyl.2.1 hX1 (inf_le_left.trans hPαβ) hΛΔ hXΛ
    (by rw [hΛcard]; omega) (by rw [hΛcard]; omega) hsyl hP.2.1 hPαβ
    (fun g hg => mem_normalizer_of_forall_conj_mem
      (fun y hy => Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg (Subgroup.mem_inf.mp hy).1)
        (inv_mem hg), conj_mem_inf_fixingSubgroup (Subgroup.mem_inf.mp (hPH hg)).1
          (Subgroup.mem_inf.mp hy).2⟩)
      (fun y hy => by
        have h' := conj_mem_inf_fixingSubgroup (Subgroup.mem_inf.mp (hPH (inv_mem hg))).1
          (Subgroup.mem_inf.mp hy).2
        rw [inv_inv] at h'
        exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hg) (Subgroup.mem_inf.mp hy).1)
          hg, h'⟩)) ?_
  refine (fixSet_anti hRP).trans ?_
  rw [hFR]
  rintro ω (rfl | rfl | rfl)
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr (Set.mem_insert _ _)

theorem exists_W_of_card_ι_eq_one (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hr : Fintype.card C.D.ι = 1) :
    ∃ W : Subgroup G, IsPGroup 2 W ∧ ∃ δ₁ δ₂ δ₃ : Ω, δ₁ ∈ holtDelta G Ω α β ∧
      δ₂ ∈ holtDelta G Ω α β ∧ δ₃ ∈ holtDelta G Ω α β ∧ δ₁ ≠ δ₂ ∧ δ₁ ≠ δ₃ ∧ δ₂ ≠ δ₃ ∧
        fixSet Ω W = {α, β, δ₁, δ₂, δ₃} ∧
          ∀ [DecidablePred (· ∈ fixSet Ω W)],
            alternatingGroup (fixSet Ω W) ≤ centralizerImage Ω W := by
  have hW : ∃ W : Subgroup G, IsPGroup 2 W ∧ ∃ δ₁ δ₂ δ₃ : Ω, δ₁ ∈ holtDelta G Ω α β ∧
      δ₂ ∈ holtDelta G Ω α β ∧ δ₃ ∈ holtDelta G Ω α β ∧ δ₁ ≠ δ₂ ∧ δ₁ ≠ δ₃ ∧ δ₂ ≠ δ₃ ∧
        fixSet Ω W = {α, β, δ₁, δ₂, δ₃} := by
    obtain ⟨k, hk⟩ := C.D.odd_card_Ψc C.i₁
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hd : Fintype.card (C.D.Ψc C.i₁) % 4 = 1 := by omega
      by_cases hT : Odd (Nat.card (twoPointKernel G Ω α β))
      · by_cases htr : ∀ δ₁ ∈ holtDelta G Ω α β, δ₁ ≠ C.γ → ∀ δ₂ ∈ holtDelta G Ω α β,
            δ₂ ≠ C.γ → ∃ s ∈ C.S, s • δ₁ = δ₂
        · exact C.exists_W_of_odd_of_transitive hS hαβ hr hd hT htr
        · push Not at htr
          obtain ⟨δ₁, hδ₁, hδ₁γ, δ₂, hδ₂, hδ₂γ, hntr⟩ := htr
          exact C.exists_W_of_odd_of_not_transitive hS hαβ hr hd hT hδ₁ hδ₂ hδ₁γ hδ₂γ hntr
      · exact C.exists_W_of_not_odd hS hαβ hr hd hT
    · exact C.exists_W_of_mod_four_eq_three hαβ (by omega)
  obtain ⟨W, hWP, δ₁, δ₂, δ₃, h₁, h₂, h₃, h12, h13, h23, hF⟩ := hW
  exact ⟨W, hWP, δ₁, δ₂, δ₃, h₁, h₂, h₃, h12, h13, h23, hF, fun hx =>
    C.alternatingGroup_le_centralizerImage hS hαβ hr hWP h₁ h₂ h₃ h12 h13 h23 hF hx⟩

end AltConfig

end Main

end CFSG.Holt.H78
