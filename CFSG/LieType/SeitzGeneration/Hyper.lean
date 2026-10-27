module

public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LieType.Seitz.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LieType.Seitz

variable {K : Type*} [Group K]

theorem fixedPoints_anti {F F' : Subgroup (MulAut K)} (h : F ≤ F') :
    fixedPoints F' ≤ fixedPoints F :=
  fun _ hk φ hφ => hk φ (h hφ)

theorem planeClosure_eq_seitzGamma (E : Subgroup (MulAut K)) :
    planeClosure E = seitzGamma E := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro k ⟨e, he, he1, hk⟩
    have hst : e ∈ MulAction.stabilizer (MulAut K) k := by
      rw [MulAction.mem_stabilizer_iff]
      exact hk
    have hle : Subgroup.zpowers e ≤ MulAction.stabilizer (MulAut K) k :=
      Subgroup.zpowers_le.mpr hst
    have hmem : k ∈ fixedPoints (Subgroup.zpowers e) := fun φ hφ => by
      simpa using hle hφ
    have hne : Subgroup.zpowers e ≠ ⊥ := by rwa [Ne, Subgroup.zpowers_eq_bot]
    have hle2 : fixedPoints (Subgroup.zpowers e) ≤ seitzGamma E :=
      le_iSup₂_of_le (Subgroup.zpowers e) ⟨Subgroup.zpowers_le.mpr he, hne⟩ le_rfl
    exact hle2 hmem
  · refine iSup₂_le fun F hF => ?_
    intro k hk
    obtain ⟨e, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF.2
    exact mem_planeClosure_of_fixed (hF.1 e.2) (fun h => he1 (Subtype.ext h)) (hk e e.2)

theorem seitzGamma_eq_seitzHyperGamma {p : ℕ} (hp : p.Prime) {E : Subgroup (MulAut K)}
    (hE : Nat.card E = p ^ 2) : seitzGamma E = seitzHyperGamma p E := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; exact pow_ne_zero 2 hp.ne_zero)
  apply le_antisymm
  · refine iSup₂_le fun F hF => ?_
    have : Finite F :=
      Finite.of_injective (Subgroup.inclusion hF.1) (Subgroup.inclusion_injective hF.1)
    have hdvd : p ∣ Nat.card F := by
      have h1 : Nat.card F ∣ p ^ 2 := hE ▸ Subgroup.card_dvd_of_le hF.1
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp h1
      rcases i with _ | i
      · exact absurd (Subgroup.card_eq_one.mp (by simpa using hi)) hF.2
      · rw [hi]
        exact dvd_pow_self p (Nat.succ_ne_zero i)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hF'F : Subgroup.zpowers (x : MulAut K) ≤ F := Subgroup.zpowers_le.mpr x.2
    have hcard : Nat.card (Subgroup.zpowers (x : MulAut K)) = p := by
      rw [Nat.card_zpowers, ← hx]
      exact Subgroup.orderOf_coe x
    have hrel : (Subgroup.zpowers (x : MulAut K)).relIndex E = p := by
      have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers (x : MulAut K)) E
      rw [inf_of_le_left (hF'F.trans hF.1), hcard, hE] at h1
      exact Nat.eq_of_mul_eq_mul_right hp.pos (by rw [h1, sq])
    exact (fixedPoints_anti hF'F).trans
      (le_iSup₂_of_le (Subgroup.zpowers (x : MulAut K)) ⟨hF'F.trans hF.1, hrel⟩ le_rfl)
  · refine iSup₂_le fun F hF => ?_
    have hne : F ≠ ⊥ := by
      rintro rfl
      have h1 := hF.2
      rw [Subgroup.relIndex_bot_left, hE] at h1
      have h2 := hp.two_le
      nlinarith
    exact le_iSup₂_of_le F ⟨hF.1, hne⟩ le_rfl

theorem planeGen_iff_seitzHyperGamma {p : ℕ} (hp : p.Prime) {E : Subgroup (MulAut K)}
    (hE : Nat.card E = p ^ 2) : PlaneGen E ↔ seitzHyperGamma p E = ⊤ := by
  unfold PlaneGen
  rw [planeClosure_eq_seitzGamma, seitzGamma_eq_seitzHyperGamma hp hE]

end CFSG.LieType.SeitzGeneration
