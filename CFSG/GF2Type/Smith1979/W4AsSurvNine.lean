module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.GF2Type.Smith1979.W4As.Surv

open Module

theorem card_dvd_ncard_of_free {G α : Type*} [Group G] [MulAction G α] [Finite G] {S : Set α}
    (hfin : S.Finite) (hS : ∀ g : G, ∀ a ∈ S, g • a ∈ S)
    (hfree : ∀ g : G, ∀ a ∈ S, g • a = a → g = 1) : Nat.card G ∣ S.ncard := by
  classical
  let act : MulAction G S :=
    { smul := fun g a => ⟨g • (a : α), hS g a a.2⟩
      one_smul := fun a => Subtype.ext (one_smul G (a : α))
      mul_smul := fun g h a => Subtype.ext (mul_smul g h (a : α)) }
  have : Finite S := hfin.to_subtype
  let _ : Fintype (MulAction.orbitRel.Quotient G S) := Fintype.ofFinite _
  have hstab : ∀ a : S, MulAction.stabilizer G a = ⊥ := fun a => by
    rw [eq_bot_iff]
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg
    exact (Subgroup.mem_bot).mpr (hfree g a a.2 (congrArg Subtype.val hg))
  have horb : ∀ a : S, Nat.card (MulAction.orbit G a) = Nat.card G := fun a => by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G a), hstab a,
      ← Subgroup.index, Subgroup.index_bot]
  rw [← Nat.card_coe_set_eq, Nat.card_congr (MulAction.selfEquivSigmaOrbits G S),
    Nat.card_sigma]
  exact Finset.dvd_sum fun ω _ => (horb _).symm ▸ dvd_rfl

theorem six_le_finrank_of_orderOf_eq_nine {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {σ : V ≃ₗ[ZMod 2] V} (hσ : orderOf σ = 9) :
    6 ≤ finrank (ZMod 2) V := by
  classical
  have hfin : Finite V := Module.finite_of_finite (ZMod 2)
  let F : Submodule (ZMod 2) V :=
    LinearMap.ker (((σ ^ 3 : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - 1)
  have hF : ∀ v, v ∈ F ↔ (σ ^ 3) v = v := fun v => by
    simp [F, LinearMap.mem_ker, sub_eq_zero]
  have hFtop : F ≠ ⊤ := by
    intro htop
    have h1 : σ ^ 3 = 1 := by
      ext v
      have hv : v ∈ F := htop ▸ Submodule.mem_top
      exact (hF v).1 hv
    have h9 := orderOf_dvd_of_pow_eq_one h1
    rw [hσ] at h9
    omega
  have hlt : finrank (ZMod 2) F < finrank (ZMod 2) V := Submodule.finrank_lt hFtop
  set S : Set V := {v | (σ ^ 3) v ≠ v} with hS
  have hScompl : (F : Set V)ᶜ = S := by
    ext v
    simp [hS, hF]
  have hcardV : Nat.card V = 2 ^ finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcardF : Nat.card F = 2 ^ finrank (ZMod 2) F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hncard : (F : Set V).ncard + S.ncard = 2 ^ finrank (ZMod 2) V := by
    rw [← hScompl, Set.ncard_add_ncard_compl (F : Set V), hcardV]
  have hncardF : (F : Set V).ncard = 2 ^ finrank (ZMod 2) F := by
    rw [← hcardF, ← Nat.card_coe_set_eq]
    rfl
  have hdvd : 9 ∣ S.ncard := by
    have hZ : Nat.card (Subgroup.zpowers σ) = 9 := by rw [Nat.card_zpowers, hσ]
    have : Finite (Subgroup.zpowers σ) := Nat.finite_of_card_ne_zero (by omega)
    have h := card_dvd_ncard_of_free (G := Subgroup.zpowers σ) (α := V) (S := S)
      (Set.toFinite _) ?_ ?_
    · rwa [hZ] at h
    · rintro ⟨g, hg⟩ a ha hga
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      apply ha
      have hc : Commute (σ ^ k) (σ ^ 3) := ((Commute.refl σ).pow_right 3).zpow_left k
      have h1 : (σ ^ k) ((σ ^ 3) a) = (σ ^ k) a := by
        calc (σ ^ k) ((σ ^ 3) a) = ((σ ^ k) * σ ^ 3) a := rfl
          _ = (σ ^ 3 * σ ^ k) a := by rw [hc.eq]
          _ = (σ ^ 3) ((σ ^ k) a) := rfl
          _ = (σ ^ k) a := hga
      exact (σ ^ k).injective h1
    · rintro ⟨g, hg⟩ a ha hga
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hga' : (σ ^ k) a = a := hga
      set H := MulAction.stabilizer (V ≃ₗ[ZMod 2] V) a
      have hk : σ ^ k ∈ H := hga'
      have h9 : σ ^ (9 : ℤ) = 1 := by
        rw [zpow_ofNat, ← hσ]
        exact pow_orderOf_eq_one σ
      have hm : σ ^ ((Int.gcd k 9 : ℕ) : ℤ) ∈ H := by
        rw [Int.gcd_eq_gcd_ab k 9, zpow_add, zpow_mul, zpow_mul, h9, one_zpow, mul_one]
        exact H.zpow_mem hk _
      have hm' : (σ ^ ((Int.gcd k 9 : ℕ) : ℤ)) a = a := hm
      have hm3 : Int.gcd k 9 ∣ 3 ^ 2 := by
        rw [Int.gcd_eq_natAbs]
        exact Nat.gcd_dvd_right _ _
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hm3
      interval_cases i
      · exfalso
        apply ha
        have h1 : σ ^ ((Int.gcd k 9 : ℕ) : ℤ) = σ := by rw [hi']; simp
        rw [h1] at hm'
        simp only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply, hm']
      · exfalso
        apply ha
        have h1 : σ ^ ((Int.gcd k 9 : ℕ) : ℤ) = σ ^ 3 := by rw [hi']; simp
        rwa [h1] at hm'
      · have h9k : (9 : ℤ) ∣ k := by
          have := Int.gcd_dvd_left (a := k) (b := 9)
          rwa [hi', show (3 : ℕ) ^ 2 = 9 by norm_num] at this
        have : (orderOf σ : ℤ) ∣ k := by rwa [hσ]
        exact Subtype.ext ((orderOf_dvd_iff_zpow_eq_one.mp this).trans (Subgroup.coe_one _).symm)
  obtain ⟨a, ha⟩ : ∃ a, finrank (ZMod 2) V = finrank (ZMod 2) F + a :=
    ⟨finrank (ZMod 2) V - finrank (ZMod 2) F, by omega⟩
  have ha0 : 0 < a := by omega
  have hS2 : S.ncard = 2 ^ finrank (ZMod 2) F * (2 ^ a - 1) := by
    rw [hncardF, ha, pow_add] at hncard
    rw [Nat.mul_sub_one]
    omega
  have h9a : 9 ∣ 2 ^ a - 1 := by
    rw [hS2] at hdvd
    exact (Nat.Coprime.pow_right _ (by decide : Nat.Coprime 9 2)).dvd_of_dvd_mul_left hdvd
  by_contra hcon
  have ha6 : a < 6 := by omega
  interval_cases a <;> simp at h9a

end CFSG.GF2Type.Smith1979.W4As.Surv
