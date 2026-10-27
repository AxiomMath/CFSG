module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma36

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma fzrAux_exists_fixed_of_card_mod_three {H : Type} [Group H] {S : Set H}
    [Finite S] {c : H} (hS : ∀ s ∈ S, c * s * c⁻¹ ∈ S) (hc3 : c ^ 3 = 1)
    (hmod : Nat.card S % 3 ≠ 0) : ∃ s ∈ S, c * s * c⁻¹ = s := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype S := Fintype.ofFinite S
  have hc3' : c * c * c = 1 := by rw [← hc3, pow_succ, pow_succ, pow_one]
  let f : Function.End ↥S := fun s => ⟨c * s.1 * c⁻¹, hS s.1 s.2⟩
  have hf : f ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    funext w
    apply Subtype.ext
    show c * (c * (c * (w : H) * c⁻¹) * c⁻¹) * c⁻¹ = w
    have : c * (c * (c * (w : H) * c⁻¹) * c⁻¹) * c⁻¹
        = (c * c * c) * w * (c * c * c)⁻¹ := by group
    rw [this, hc3']
    simp
  have key := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf
  have key' : Nat.card S ≡ Nat.card (Function.fixedPoints f) [MOD 3] := by
    convert key using 2
    · exact Nat.card_eq_fintype_card
    · rw [Nat.card_eq_fintype_card]
  by_contra hne
  push Not at hne
  have h0 : Nat.card (Function.fixedPoints f) = 0 := by
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨s, hs⟩ => ?_⟩
    exact hne s s.2 (congrArg Subtype.val hs)
  rw [h0] at key'
  exact hmod (by simpa [Nat.ModEq] using key')

private lemma fzrAux_conj_sq {H : Type} [Group H] {rho a : H} (hr3 : rho ^ 3 = 1) :
    rho * (rho * a * rho⁻¹) * rho⁻¹ = rho⁻¹ * a * rho := by
  have hrinv : rho⁻¹ = rho ^ 2 := by
    have h : rho * rho ^ 2 = 1 := by rw [← pow_succ', hr3]
    exact inv_eq_of_mul_eq_one_right h
  have hsq : rho * rho = rho⁻¹ := by
    rw [← pow_two]; exact hrinv.symm
  have h4 : rho⁻¹ * rho⁻¹ = rho := by
    rw [← mul_inv_rev, hsq, inv_inv]
  calc rho * (rho * a * rho⁻¹) * rho⁻¹
      = (rho * rho) * a * (rho⁻¹ * rho⁻¹) := by group
    _ = rho⁻¹ * a * rho := by rw [hsq, h4]

theorem fzr_fpf_section {M N : Subgroup G} {rho : G} (hM : IsPGroup 2 M) (hNM : N ≤ M)
    (hcomm : ∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ N) (hrN : ∀ x ∈ N, rho * x * rho⁻¹ ∈ N)
    (hr3 : rho ^ 3 = 1) (hfpf : ∀ x ∈ M, rho * x * rho⁻¹ = x → x = 1) :
    ∀ m ∈ M, rho * m * rho⁻¹ * m⁻¹ ∈ N → m ∈ N := by
  intro m hmM hnm
  classical
  set n0 : G := rho * m * rho⁻¹ * m⁻¹ with hn0def
  have hn0N : n0 ∈ N := by rw [hn0def]; exact hnm
  have hn0M : n0 ∈ M := hNM hn0N
  have hrm : rho * m * rho⁻¹ = n0 * m := by rw [hn0def]; group
  let C : Set G := {c | c ∈ M ∧ m⁻¹ * c ∈ N}
  have hC_inv : ∀ c ∈ C, rho * c * rho⁻¹ ∈ C := by
    rintro c ⟨hcM, hcN⟩
    have e1 : rho * c * rho⁻¹ = (n0 * m) * (rho * (m⁻¹ * c) * rho⁻¹) := by
      have hc_eq : c = m * (m⁻¹ * c) := by group
      have e0 : rho * c * rho⁻¹
          = (rho * m * rho⁻¹) * (rho * (m⁻¹ * c) * rho⁻¹) := by
        rw [hc_eq]; group
      rw [e0, hrm]
    have e2 : m⁻¹ * ((n0 * m) * (rho * (m⁻¹ * c) * rho⁻¹))
        = (⁅m⁻¹, n0⁆ * n0) * (rho * (m⁻¹ * c) * rho⁻¹) := by
      rw [commutatorElement_def]; group
    have hconj : m⁻¹ * (rho * c * rho⁻¹) ∈ N := by
      rw [e1, e2]
      exact N.mul_mem (N.mul_mem (hcomm m⁻¹ (M.inv_mem hmM) n0 hn0M) hn0N)
        (hrN (m⁻¹ * c) hcN)
    refine ⟨?_, hconj⟩
    rw [show rho * c * rho⁻¹ = m * (m⁻¹ * (rho * c * rho⁻¹)) by group]
    exact M.mul_mem hmM (hNM hconj)
  have hcardC : Nat.card C = Nat.card ↥N := Nat.card_congr
    { toFun := fun c => ⟨m⁻¹ * c.1, c.2.2⟩
      invFun := fun n => ⟨m * n.1, ⟨M.mul_mem hmM (hNM n.2), by
        show m⁻¹ * (m * n.1) ∈ N
        rw [← mul_assoc, inv_mul_cancel, one_mul]; exact n.2⟩⟩
      left_inv := fun c => by apply Subtype.ext; group
      right_inv := fun n => by apply Subtype.ext; group }
  obtain ⟨k, hk⟩ := (hM.to_le hNM).exists_card_eq
  have hmod : Nat.card C % 3 ≠ 0 := by
    rw [hcardC, hk]
    intro h
    have h3 : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h
    have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  obtain ⟨c₀, hc₀C, hc₀fix⟩ :=
    fzrAux_exists_fixed_of_card_mod_three hC_inv hr3 hmod
  have hc₀M : c₀ ∈ M := hc₀C.1
  have hc₀N : m⁻¹ * c₀ ∈ N := hc₀C.2
  have hc₀1 : c₀ = 1 := hfpf c₀ hc₀M hc₀fix
  have hmN : m⁻¹ ∈ N := by rw [hc₀1, mul_one] at hc₀N; exact hc₀N
  simpa using N.inv_mem hmN

theorem fzr_regular_section {M N : Subgroup G} {rho y : G}
    (hcomm : ∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ N) (hsq : ∀ a ∈ M, a ^ 2 ∈ N)
    (hrM : ∀ x ∈ M, rho * x * rho⁻¹ ∈ M) (hrN : ∀ x ∈ N, rho * x * rho⁻¹ ∈ N)
    (hr3 : rho ^ 3 = 1) (hyr : y * rho * y⁻¹ = rho⁻¹)
    (hq : ∀ m ∈ M, rho * m * rho⁻¹ * m⁻¹ ∈ N → m ∈ N) :
    ActsRegularly y N M := by
  intro x hxM hx
  classical
  set u : G := rho * x * rho⁻¹ with hu
  set x2 : G := rho⁻¹ * x * rho with hx2
  have huM : u ∈ M := by rw [hu]; exact hrM x hxM
  have hx2M : x2 ∈ M := by
    rw [hx2, ← fzrAux_conj_sq hr3]
    exact hrM u huM
  set n1 : G := ⁅y, x⁆ with hn1def
  have hn1N : n1 ∈ N := by rw [hn1def]; exact hx
  set n2 : G := rho⁻¹ * n1 * rho with hn2def
  have hn2N : n2 ∈ N := by
    have h1 : rho * n1 * rho⁻¹ ∈ N := hrN n1 hn1N
    have h2 : rho * (rho * n1 * rho⁻¹) * rho⁻¹ ∈ N := hrN _ h1
    have e : rho * (rho * n1 * rho⁻¹) * rho⁻¹ = rho⁻¹ * n1 * rho := fzrAux_conj_sq hr3
    rw [hn2def, ← e]; exact h2
  have hyrinv : y * rho⁻¹ * y⁻¹ = rho := by
    have h := congrArg Inv.inv hyr
    simpa [mul_assoc] using h
  have hxn : y * x * y⁻¹ = n1 * x := by rw [hn1def, commutatorElement_def]; group
  have hyu : y * u * y⁻¹ = n2 * x2 := by
    calc y * u * y⁻¹
        = (y * rho * y⁻¹) * (y * x * y⁻¹) * (y * rho⁻¹ * y⁻¹) := by rw [hu]; group
      _ = rho⁻¹ * (n1 * x) * rho := by rw [hyr, hxn, hyrinv]
      _ = n2 * x2 := by rw [hn2def, hx2]; group
  have hcomm_yu : ⁅y, u⁆ = n2 * x2 * u⁻¹ := by
    rw [commutatorElement_def, hyu]
  have hmM : x * u * x2 ∈ M := M.mul_mem (M.mul_mem hxM huM) hx2M
  have hmN : x * u * x2 ∈ N := by
    refine hq _ hmM ?_
    have h1 : rho * u * rho⁻¹ = x2 := by rw [hu, hx2]; exact fzrAux_conj_sq hr3
    have h2 : rho * x2 * rho⁻¹ = x := by rw [hx2]; group
    have h3 : rho * x * rho⁻¹ = u := hu.symm
    have e0 : rho * (x * u * x2) * rho⁻¹
        = (rho * x * rho⁻¹) * (rho * u * rho⁻¹) * (rho * x2 * rho⁻¹) := by group
    have e : rho * (x * u * x2) * rho⁻¹ * (x * u * x2)⁻¹ = ⁅x⁻¹, x * u * x2⁆ := by
      rw [e0, h3, h1, h2, commutatorElement_def]; group
    rw [e]
    exact hcomm x⁻¹ (M.inv_mem hxM) (x * u * x2) hmM
  have hx2sq : x2 ^ 2 ∈ N := hsq x2 hx2M
  have h1 : x * u * x2⁻¹ ∈ N := by
    have e : x * u * x2⁻¹ = (x * u * x2) * (x2 ^ 2)⁻¹ := by rw [pow_two]; group
    rw [e]; exact N.mul_mem hmN (N.inv_mem hx2sq)
  have h2 : x * ⁅y, u⁆⁻¹ = (x * u * x2⁻¹) * n2⁻¹ := by
    rw [hcomm_yu]
    have : (n2 * x2 * u⁻¹)⁻¹ = u * x2⁻¹ * n2⁻¹ := by group
    rw [this]; group
  exact ⟨u, huM, by rw [h2]; exact N.mul_mem h1 (N.inv_mem hn2N)⟩

end CFSG.OddStandard.SmallF3.FritzII
