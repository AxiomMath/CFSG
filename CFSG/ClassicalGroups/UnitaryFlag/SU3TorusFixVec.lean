module

public import CFSG.ClassicalGroups.UnitaryFlag.SU3OddOrderEigen
public import CFSG.ClassicalGroups.UnitaryFlag.SU3NonisotropicStabilizer
public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem torus_eigenvalue_pow_eq_one {K : Type} [Field K] {n : ℕ}
    {T : Subgroup (StatedSU 3 (2 ^ n) K)} (hT : Nat.card T = 2 ^ n - 1)
    {b : StatedSU 3 (2 ^ n) K} (hb : b ∈ T) {v : Fin 3 → K} {μ : K}
    (hv0 : v ≠ 0)
    (hμ : ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = μ • v) :
    μ ^ (2 ^ n - 1) = 1 := by
  have hb_pow : b ^ (2 ^ n - 1) = 1 := by
    have hdvd : orderOf b ∣ Nat.card T := T.orderOf_dvd_natCard hb
    rw [hT] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hb_pow_vec : ∀ k : ℕ,
      ((↑(b ^ k) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v =
        μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ih,
          Matrix.mulVec_smul, hμ, smul_smul, pow_succ]
  have hvec := hb_pow_vec (2 ^ n - 1)
  rw [hb_pow] at hvec
  simp only [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec] at hvec
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (funext hcon)
  have hcongr : v i = μ ^ (2 ^ n - 1) * v i := by
    simpa using congrFun hvec i
  have heq : (1 : K) * v i = μ ^ (2 ^ n - 1) * v i := by
    rw [one_mul]
    exact hcongr
  exact (mul_right_cancel₀ hi heq).symm

theorem norm_eq_one_of_mulVec_eq_smul {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {b : StatedSU 3 (2 ^ n) K} {v : Fin 3 → K} {μ : K}
    (hvv : stdHermForm h 3 v v ≠ 0)
    (hμ : ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = μ • v) :
    h.norm μ = 1 := by
  have hpres : stdHermForm h 3
      (((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v)
      (((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v) =
      stdHermForm h 3 v v := by
    simpa [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec] using
      stdHermForm_smul_smul h b v v
  have hscale : stdHermForm h 3 (μ • v) (μ • v) =
      h.norm μ * stdHermForm h 3 v v := by
    simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, UnitaryFieldData.norm]
    ring
  have hscale_eq : h.norm μ * stdHermForm h 3 v v = stdHermForm h 3 v v := by
    rw [← hscale, ← hμ]
    exact hpres
  have heq : h.norm μ * stdHermForm h 3 v v = 1 * stdHermForm h 3 v v := by
    rw [one_mul]
    exact hscale_eq
  exact mul_right_cancel₀ hvv heq

theorem eq_one_of_pow_sub_one_and_norm_eq_one {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {μ : K}
    (hpow : μ ^ (2 ^ n - 1) = 1) (hnorm : h.norm μ = 1) : μ = 1 := by
  haveI : CharP K 2 := h.charP
  have hμ_bar : h.bar μ * μ = 1 := by
    rw [mul_comm]
    simpa [UnitaryFieldData.norm] using hnorm
  have hμB : μ ^ (2 ^ n + 1) = 1 := by
    rw [pow_succ, ← h.bar_apply]
    exact hμ_bar
  have hμ2 : μ ^ 2 = 1 := by
    have hg : μ ^ Nat.gcd (2 ^ n - 1) (2 ^ n + 1) = 1 :=
      pow_gcd_eq_one.mpr ⟨hpow, hμB⟩
    have hgdvd : Nat.gcd (2 ^ n - 1) (2 ^ n + 1) ∣ 2 := by
      have h := Nat.dvd_sub (Nat.gcd_dvd_right (2 ^ n - 1) (2 ^ n + 1))
        (Nat.gcd_dvd_left (2 ^ n - 1) (2 ^ n + 1))
      have hsub : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
        have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      rwa [hsub] at h
    obtain ⟨k, hk⟩ := hgdvd
    rw [hk, pow_mul, hg, one_pow]
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  rcases mul_self_eq_one_iff.mp (by simpa [pow_two] using hμ2) with h | h
  · exact h
  · rw [h, hneg]

theorem torus_fixes_of_eigenvector {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {T : Subgroup (StatedSU 3 (2 ^ n) K)}
    (hTc : IsMulCommutative T) (hT : Nat.card T = 2 ^ n - 1)
    {a : StatedSU 3 (2 ^ n) K} (haT : a ∈ T)
    {v : Fin 3 → K}
    (hav : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    (hvv : stdHermForm h 3 v v ≠ 0)
    (hfix : ∀ w : Fin 3 → K,
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w = w →
        ∃ c : K, w = c • v) :
    ∀ b ∈ T, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v := by
  classical
  haveI : IsMulCommutative T := hTc
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hvv (by simp)
  intro b hb
  have hcomm : b * a = a * b := by
    simpa using congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : T) (⟨a, haT⟩ : T))
  have hcomm_mat : ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    simpa using congrArg (fun g : StatedSU 3 (2 ^ n) K =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hcomm
  have hb_av : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
      (((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v) =
      ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v := by
    calc
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
          (((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v)
          = (((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).mulVec v :=
            Matrix.mulVec_mulVec v _ _
      _ = (((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).mulVec v := by
            rw [← hcomm_mat]
      _ = ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
              (((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v) :=
            (Matrix.mulVec_mulVec v _ _).symm
      _ = ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v := by rw [hav]
  obtain ⟨μ, hμ⟩ := hfix _ hb_av
  have hμeq : μ = 1 :=
    eq_one_of_pow_sub_one_and_norm_eq_one h
      (torus_eigenvalue_pow_eq_one hT hb hv0 hμ)
      (norm_eq_one_of_mulVec_eq_smul h hvv hμ)
  rw [hμ, hμeq, one_smul]

theorem exists_fixVec_isL2_of_torus {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) {T : Subgroup (StatedSU 3 (2 ^ n) K)}
    (hTc : IsMulCommutative T) (hT : Nat.card T = 2 ^ n - 1) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧
      (∀ b ∈ T, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v) ∧
      (∀ w : Fin 3 → K,
        (∀ b ∈ T, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w = w) →
          ∃ c : K, w = c • v) ∧
      ∃ L : Subgroup (StatedSU 3 (2 ^ n) K),
        (∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v) ∧
        IsL2 L n := by
  classical
  let h : UnitaryFieldData 2 n K := unitaryFieldDataOfCard hK
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard_gt : 1 < Nat.card T := by
    rw [hT]
    omega
  haveI : Finite T := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp hcard_gt
  obtain ⟨aT, haT⟩ := exists_ne (1 : T)
  have ha_ne : (aT : StatedSU 3 (2 ^ n) K) ≠ 1 := by
    intro h1
    exact haT (Subtype.ext h1)
  have ha_pow : (aT : StatedSU 3 (2 ^ n) K) ^ (2 ^ n - 1) = 1 := by
    have hdvd : orderOf (aT : StatedSU 3 (2 ^ n) K) ∣ Nat.card T :=
      T.orderOf_dvd_natCard aT.2
    rw [hT] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  obtain ⟨v, e, f, t, ht, hav, hae, haf, hvv, hee, hff, hef, hev, hfv, hfix⟩ :=
    exists_hyperbolic_eigenbasis_of_pow_eq_one h ha_ne ha_pow
  have hTfix := torus_fixes_of_eigenvector h hTc hT aT.2 hav hvv hfix
  refine ⟨v, ?_, hTfix, ?_, ?_⟩
  · rintro rfl
    exact hvv (by simp)
  · intro w hw
    exact hfix w (hw (aT : StatedSU 3 (2 ^ n) K) aT.2)
  · let L : Subgroup (StatedSU 3 (2 ^ n) K) :=
      MulAction.stabilizer (StatedSU 3 (2 ^ n) K) v
    have hL : ∀ g : StatedSU 3 (2 ^ n) K,
        g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v := by
      intro g
      rw [MulAction.mem_stabilizer_iff]
      simp [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec]
    exact ⟨L, hL, isL2_of_forall_mem_iff_mulVec_eq h hn hvv hee hff hef hev hfv hL⟩

end CFSG.ClassicalGroups.UnitaryFlag

end
