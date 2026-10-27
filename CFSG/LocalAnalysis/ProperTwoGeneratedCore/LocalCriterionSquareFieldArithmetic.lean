module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.CharAndCard

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u

variable {F : Type u} [Field F]

abbrev fixedField (sigma : RingAut F) : Subfield F :=
  FixedPoints.subfield (Subgroup.zpowers sigma) F

theorem mem_fixedField_iff (sigma : RingAut F) (c : F) :
    c ∈ fixedField sigma ↔ sigma c = c := by
  constructor
  · intro hc
    exact hc ⟨sigma, Subgroup.mem_zpowers sigma⟩
  · intro hc rho
    have hle : Subgroup.zpowers sigma ≤ MulAction.stabilizer (RingAut F) c := by
      rw [Subgroup.zpowers_le]
      exact hc
    exact hle rho.2

def ringAutPrimeEquiv (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] :
    RingAut F ≃* (F ≃ₐ[ZMod p] F) where
  toFun sigma := AlgEquiv.ofRingEquiv (fun c =>
    DFunLike.congr_fun (RingHom.ext_zmod
      (sigma.toRingHom.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) c)
  invFun := AlgEquiv.toRingEquiv
  left_inv sigma := by ext c; rfl
  right_inv sigma := by ext c; rfl
  map_mul' sigma rho := by ext c; rfl

theorem finite_field_ringAut_isCyclic [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    IsCyclic (RingAut F) := by
  let : Algebra (ZMod p) F := ZMod.algebra F p
  exact (ringAutPrimeEquiv (F := F) p).isCyclic.mpr inferInstance

theorem fixedField_card_pow_order [Finite F] (sigma : RingAut F) :
    Nat.card F = Nat.card (fixedField sigma) ^ orderOf sigma := by
  let : IsGaloisGroup (Subgroup.zpowers sigma) (fixedField sigma) F :=
    IsGaloisGroup.fixedPoints (Subgroup.zpowers sigma) F
  have hdegree : Module.finrank (fixedField sigma) F = orderOf sigma := by
    calc
      Module.finrank (fixedField sigma) F = Nat.card (Subgroup.zpowers sigma) :=
        (IsGaloisGroup.card_eq_finrank (Subgroup.zpowers sigma) (fixedField sigma) F).symm
      _ = orderOf sigma := Nat.card_zpowers sigma
  rw [← hdegree]
  exact Module.natCard_eq_pow_finrank

theorem char_two_of_card [Finite F] {n : ℕ} (hcard : Nat.card F = 2 ^ n) : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by simpa only [Fintype.card_eq_nat_card] using hcard)

theorem cyclic_involutions_eq {G : Type u} [Group G] [IsCyclic G]
    (a b : G) (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  let : Finite (Subgroup.zpowers a) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers, ha]
    decide)
  let : Finite (Subgroup.zpowers b) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers, hb]
    decide)
  have hgroups : Subgroup.zpowers a = Subgroup.zpowers b :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, ha, hb])
  have hamem : a ∈ Subgroup.zpowers b := hgroups ▸ Subgroup.mem_zpowers a
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hamem
  have ha1 : a ≠ 1 := by intro h; simp [h] at ha
  have hpow : b ^ j = 1 ∨ b ^ j = b := by
    have hmod : b ^ j = b ^ (j % 2) := by
      simpa [hb] using (zpow_mod_orderOf b j).symm
    have hrange : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hrange with hj0 | hj1
    · left; simpa [hj0] using hmod
    · right; simpa [hj1] using hmod
  exact hj.symm.trans (hpow.resolve_left (fun h => ha1 (hj.symm.trans h)))

theorem finite_field_involution_degree_and_fixed_card [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (sigma : RingAut F) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    ∃ s : ℕ, 1 ≤ s ∧ n = 2 * s ∧ Nat.card (fixedField sigma) = 2 ^ s := by
  have horder : orderOf sigma = 2 := orderOf_eq_prime hsigma hne
  have hpow := fixedField_card_pow_order sigma
  rw [horder, hcard] at hpow
  have hdiv : Nat.card (fixedField sigma) ∣ 2 ^ n := by
    rw [hpow]
    exact dvd_pow_self _ (by decide : 2 ≠ 0)
  obtain ⟨s, _hsn, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  rw [hs, ← pow_mul] at hpow
  have hn2 : n = 2 * s := by
    have := Nat.pow_right_injective (by decide : 2 ≤ 2) hpow
    omega
  refine ⟨s, by omega, hn2, hs⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
