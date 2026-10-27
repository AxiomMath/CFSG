module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup

open scoped Pointwise

theorem exists_conj_mem_zpowers_of_five {Y : Type*} [Group Y] [Finite Y] (E : Subgroup Y)
    (hE : ¬ 25 ∣ Nat.card E) {σ π : Y} (hσE : σ ∈ E) (hπE : π ∈ E) (hσ : orderOf σ = 5)
    (hπ : orderOf π = 5) : ∃ e ∈ E, e * σ * e⁻¹ ∈ Subgroup.zpowers π := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hpow : (5 : ℕ) ^ 2 = 25 := by decide
  have hE25 : ¬ 5 ^ 2 ∣ Nat.card E := by rw [hpow]; exact hE
  let σ' : E := ⟨σ, hσE⟩
  let π' : E := ⟨π, hπE⟩
  have hσ' : orderOf σ' = 5 := by rw [Subgroup.orderOf_mk, hσ]
  have hπ' : orderOf π' = 5 := by rw [Subgroup.orderOf_mk, hπ]
  have hcard_ne : Nat.card E ≠ 0 := by
    intro h0
    exact hE (h0.symm ▸ dvd_zero 25)
  have h5dvd : 5 ∣ Nat.card E := by
    have h := orderOf_dvd_natCard σ'
    rwa [hσ'] at h
  have hfac : (Nat.card E).factorization 5 = 1 := by
    have hp : Nat.Prime 5 := by decide
    have h1 : 1 ≤ (Nat.card E).factorization 5 :=
      (hp.pow_dvd_iff_le_factorization hcard_ne).mp (by simpa using h5dvd)
    have h2 : ¬ 2 ≤ (Nat.card E).factorization 5 := fun h =>
      hE25 ((hp.pow_dvd_iff_le_factorization hcard_ne).mpr h)
    exact le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_le h2)) h1
  let A : Subgroup E := Subgroup.zpowers σ'
  let B : Subgroup E := Subgroup.zpowers π'
  have hAcard : Nat.card A = 5 ^ (Nat.card E).factorization 5 := by
    show Nat.card (Subgroup.zpowers σ') = 5 ^ (Nat.card E).factorization 5
    rw [Nat.card_zpowers, hσ', hfac, pow_one]
  have hBcard : Nat.card B = 5 ^ (Nat.card E).factorization 5 := by
    show Nat.card (Subgroup.zpowers π') = 5 ^ (Nat.card E).factorization 5
    rw [Nat.card_zpowers, hπ', hfac, pow_one]
  let As : Sylow 5 E := Sylow.ofCard A hAcard
  let Bs : Sylow 5 E := Sylow.ofCard B hBcard
  haveI : Finite (Sylow 5 E) := Sylow.finite_of_finiteIndex As
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq E As Bs
  have heA : MulAut.conj e • A = B := by
    have h : ((e • As : Sylow 5 E) : Subgroup E) = ((Bs : Sylow 5 E) : Subgroup E) := by
      rw [he]
    simpa [As, Bs, Sylow.coe_subgroup_smul] using h
  have hmemB : e * σ' * e⁻¹ ∈ B := by
    have h : MulAut.conj e • σ' ∈ MulAut.conj e • A :=
      Subgroup.smul_mem_pointwise_smul σ' (MulAut.conj e) A (Subgroup.mem_zpowers σ')
    rw [heA] at h
    simpa [MulAut.conj_apply] using h
  refine ⟨(e : Y), e.2, ?_⟩
  have hmemY : E.subtype (e * σ' * e⁻¹) ∈ (Subgroup.zpowers π').map E.subtype :=
    Subgroup.mem_map_of_mem E.subtype hmemB
  rw [MonoidHom.map_zpowers] at hmemY
  simpa using hmemY

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
