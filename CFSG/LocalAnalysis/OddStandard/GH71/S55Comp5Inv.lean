module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.OddStandard.GH71.S55.C5

open Matrix

variable {K : Type} [Field K] [Finite K] {n : ℕ}

@[expose] def restrictEnd (T : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K))
    (hW : ∀ v ∈ W, T *ᵥ v ∈ W) : Function.End ↥W :=
  fun v => ⟨T *ᵥ v, hW _ v.2⟩

omit [Finite K] in
theorem restrict_pow_apply (T : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K))
    (hW : ∀ v ∈ W, T *ᵥ v ∈ W) (k : ℕ) (v : ↥W) :
    (((restrictEnd T W hW) ^ k) v : Fin n → K) = (T ^ k) *ᵥ (v : Fin n → K) := by
  induction k generalizing v with
  | zero => rw [pow_zero, pow_zero, one_mulVec]; rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, ← mulVec_mulVec]
    exact ih _

theorem fixes_of_invariant {p : ℕ} [hp : Fact p.Prime] (hQ : ¬ p ∣ Nat.card K)
    (hQ1 : ¬ p ∣ Nat.card K - 1) (hQ2 : ¬ p ∣ Nat.card K + 1) (T : Matrix (Fin n) (Fin n) K)
    (hT : T ^ p = 1) (W : Submodule K (Fin n → K)) (hW : ∀ v ∈ W, T *ᵥ v ∈ W)
    (hd : Module.finrank K W ≤ 2) : ∀ v ∈ W, T *ᵥ v = v := by
  classical
  have : Fintype K := Fintype.ofFinite K
  let L : ↥W →ₗ[K] ↥W := (toLin' T).restrict (fun v hv => by rw [toLin'_apply]; exact hW v hv)
  let φ : Function.End ↥W := restrictEnd T W hW
  have hφp : φ ^ p ^ 1 = 1 := by
    funext v
    apply Subtype.ext
    rw [pow_one, restrict_pow_apply T W hW p v, hT, one_mulVec]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq hφp
  let F : Submodule K ↥W := LinearMap.eqLocus L LinearMap.id
  have hFix : Function.fixedPoints φ = (F : Set ↥W) := by
    ext v
    simp only [SetLike.mem_coe, F, LinearMap.mem_eqLocus, LinearMap.id_apply]
    rfl
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hFix,
    Module.natCard_eq_pow_finrank (K := K)] at hmod
  have hcF : Nat.card ↥(F : Set ↥W) = Nat.card K ^ Module.finrank K F :=
    Module.natCard_eq_pow_finrank (K := K) (V := ↥F)
  rw [hcF] at hmod
  have hle : Module.finrank K F ≤ Module.finrank K W := Submodule.finrank_le F
  have hQ0 : 1 ≤ Nat.card K := Nat.card_pos
  have hFtop : F = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    by_contra hne
    have hlt : Module.finrank K F < Module.finrank K W := lt_of_le_of_ne hle hne
    have hdvd := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hQ0 hle)).mp hmod.symm
    set Q := Nat.card K
    interval_cases hd' : Module.finrank K W <;> interval_cases he : Module.finrank K F
    · exact hQ1 (by simpa using hdvd)
    · have e2 : Q ^ 2 - 1 = (Q + 1) * (Q - 1) := by simpa using Nat.pow_two_sub_pow_two Q 1
      rw [pow_zero, e2] at hdvd
      rcases (Nat.Prime.dvd_mul hp.out).mp hdvd with h | h
      · exact hQ2 h
      · exact hQ1 h
    · have e2 : Q ^ 2 - Q ^ 1 = Q * (Q - 1) := by rw [pow_one, Nat.mul_sub_one, sq]
      rw [e2] at hdvd
      rcases (Nat.Prime.dvd_mul hp.out).mp hdvd with h | h
      · exact hQ h
      · exact hQ1 h
  intro v hv
  have hvF : (⟨v, hv⟩ : ↥W) ∈ F := hFtop ▸ Submodule.mem_top
  have h1 := (LinearMap.mem_eqLocus).mp hvF
  have h2 := congrArg Subtype.val h1
  simpa [L, toLin'_apply] using h2

theorem eq_one_of_comm_involution {p : ℕ} [Fact p.Prime] (h2 : (2 : K) ≠ 0)
    (hQ : ¬ p ∣ Nat.card K) (hQ1 : ¬ p ∣ Nat.card K - 1) (hQ2 : ¬ p ∣ Nat.card K + 1)
    {T I : Matrix (Fin 3) (Fin 3) K} (hT : T ^ p = 1) (hI : I * I = 1) (hI1 : I ≠ 1)
    (hI2 : I ≠ -1) (hTI : T * I = I * T) : T = 1 := by
  let Vp : Submodule K (Fin 3 → K) := LinearMap.ker (toLin' I - LinearMap.id)
  let Vm : Submodule K (Fin 3 → K) := LinearMap.ker (toLin' I + LinearMap.id)
  have memVp : ∀ v, v ∈ Vp ↔ I *ᵥ v = v := by
    intro v
    simp only [Vp, LinearMap.mem_ker, LinearMap.sub_apply, toLin'_apply, LinearMap.id_apply,
      sub_eq_zero]
  have memVm : ∀ v, v ∈ Vm ↔ I *ᵥ v = -v := by
    intro v
    simp only [Vm, LinearMap.mem_ker, LinearMap.add_apply, toLin'_apply, LinearMap.id_apply,
      add_eq_zero_iff_eq_neg]
  have hII : ∀ v, I *ᵥ (I *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hI, one_mulVec]
  have hTI' : ∀ v, T *ᵥ (I *ᵥ v) = I *ᵥ (T *ᵥ v) := fun v => by
    rw [mulVec_mulVec, mulVec_mulVec, hTI]
  have hVpT : ∀ v ∈ Vp, T *ᵥ v ∈ Vp := by
    intro v hv
    rw [memVp] at hv ⊢
    rw [← hTI', hv]
  have hVmT : ∀ v ∈ Vm, T *ᵥ v ∈ Vm := by
    intro v hv
    rw [memVm] at hv ⊢
    rw [← hTI', hv, mulVec_neg]
  have hinf : Vp ⊓ Vm = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, memVp, memVm] at hv
    have h : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hv.1]
      rw [hv.2, neg_add_cancel]
    exact (Submodule.mem_bot K).mpr ((smul_eq_zero.mp h).resolve_left h2)
  have hVm : Vm ≠ ⊥ := by
    intro hb
    apply hI1
    apply toLin'.injective
    rw [toLin'_one]
    refine LinearMap.ext fun v => ?_
    have hw : v - I *ᵥ v ∈ Vm := by rw [memVm, mulVec_sub, hII, neg_sub]
    rw [hb, Submodule.mem_bot, sub_eq_zero] at hw
    rw [toLin'_apply, LinearMap.id_apply]
    exact hw.symm
  have hVp : Vp ≠ ⊥ := by
    intro hb
    apply hI2
    apply toLin'.injective
    rw [map_neg, toLin'_one]
    refine LinearMap.ext fun v => ?_
    have hw : I *ᵥ v + v ∈ Vp := by rw [memVp, mulVec_add, hII, add_comm]
    rw [hb, Submodule.mem_bot, add_eq_zero_iff_eq_neg] at hw
    rw [toLin'_apply, LinearMap.neg_apply, LinearMap.id_apply]
    exact hw
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq Vp Vm
  rw [hinf, finrank_bot] at hsum
  have h3 : Module.finrank K ↥(Vp ⊔ Vm) ≤ 3 :=
    (Submodule.finrank_le _).trans (Module.finrank_fin_fun K).le
  have h1p := Submodule.one_le_finrank_iff.mpr hVp
  have h1m := Submodule.one_le_finrank_iff.mpr hVm
  have hfp := fixes_of_invariant hQ hQ1 hQ2 T hT Vp hVpT (by omega)
  have hfm := fixes_of_invariant hQ hQ1 hQ2 T hT Vm hVmT (by omega)
  apply toLin'.injective
  rw [toLin'_one]
  refine LinearMap.ext fun v => ?_
  rw [toLin'_apply, LinearMap.id_apply]
  have ep : T *ᵥ (v + I *ᵥ v) = v + I *ᵥ v :=
    hfp _ ((memVp _).mpr (by rw [mulVec_add, hII, add_comm]))
  have em : T *ᵥ (v - I *ᵥ v) = v - I *ᵥ v :=
    hfm _ ((memVm _).mpr (by rw [mulVec_sub, hII, neg_sub]))
  have h : (2 : K) • (T *ᵥ v) = (2 : K) • v := by
    rw [two_smul, two_smul]
    have := congrArg₂ (· + ·) ep em
    simp only [mulVec_add, mulVec_sub] at this
    have e1 : T *ᵥ v + T *ᵥ v = T *ᵥ v + T *ᵥ (I *ᵥ v) + (T *ᵥ v - T *ᵥ (I *ᵥ v)) := by abel
    have e2 : v + v = v + I *ᵥ v + (v - I *ᵥ v) := by abel
    rw [e1, e2]
    exact this
  exact smul_right_injective _ h2 h

end CFSG.OddStandard.GH71.S55.C5
