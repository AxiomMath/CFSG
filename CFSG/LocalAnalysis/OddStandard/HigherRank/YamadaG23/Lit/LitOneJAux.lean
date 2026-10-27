module

public import CFSG.GroupTheory.OddInversion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddInversion
open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

theorem litFit_nilpotent [Finite Γ] (N : Subgroup Γ) :
    Group.IsNilpotent ↥(CFSG.fittingSubgroupOf N) := by
  have : Group.IsNilpotent (CFSG.fittingSubgroup ↥N) := inferInstance
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective)

theorem litFit_le (N : Subgroup Γ) : CFSG.fittingSubgroupOf N ≤ N :=
  Subgroup.map_subtype_le _

theorem litFit_conj {N : Subgroup Γ} {g x : Γ} (hg : g ∈ normalizer (N : Set Γ))
    (hx : x ∈ CFSG.fittingSubgroupOf N) : g * x * g⁻¹ ∈ CFSG.fittingSubgroupOf N := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  let e : N ≃* N := ((MulAut.conj g).subgroupMap N).trans (MulEquiv.subgroupCongr hmap)
  have hey : e y ∈ CFSG.fittingSubgroup ↥N := by
    have hc : (CFSG.fittingSubgroup ↥N).Characteristic := inferInstance
    rw [← Subgroup.characteristic_iff_map_eq.mp hc e]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hy
  exact Subgroup.mem_map.mpr ⟨e y, hey, rfl⟩

theorem litFit_normalizer {N : Subgroup Γ} {g : Γ} (hg : g ∈ normalizer (N : Set Γ)) :
    g ∈ normalizer (CFSG.fittingSubgroupOf N : Set Γ) := by
  intro x
  refine ⟨litFit_conj hg, fun h => ?_⟩
  have := litFit_conj ((normalizer (N : Set Γ)).inv_mem hg) h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem litFit_cent [Finite Γ] {N : Subgroup Γ} (hN : Odd (Nat.card N)) {n : Γ} (hn : n ∈ N)
    (h : ∀ f ∈ CFSG.fittingSubgroupOf N, n * f = f * n) :
    n ∈ CFSG.fittingSubgroupOf N := by
  have hsolv : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hN
  have hmem : (⟨n, hn⟩ : ↥N) ∈
      Subgroup.centralizer (CFSG.fittingSubgroup ↥N : Set ↥N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subtype.ext (h f.1 ⟨f, hf, rfl⟩).symm
  exact ⟨⟨n, hn⟩, CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hmem, rfl⟩

@[expose] def litU (N B : Subgroup Γ) : Subgroup Γ :=
  CFSG.fittingSubgroupOf N ⊓ centralizer (B : Set Γ)

@[expose] def litX (N B : Subgroup Γ) : Subgroup Γ :=
  CFSG.fittingSubgroupOf N ⊓ normalizer (litU N B : Set Γ)

theorem litU_conj {N B : Subgroup Γ} {g u : Γ} (hgN : g ∈ normalizer (N : Set Γ))
    (hgB : g ∈ normalizer (B : Set Γ)) (hu : u ∈ litU N B) : g * u * g⁻¹ ∈ litU N B := by
  refine Subgroup.mem_inf.mpr ⟨litFit_conj hgN (Subgroup.mem_inf.mp hu).1, ?_⟩
  rw [mem_centralizer_iff]
  intro b hb
  have hb' : g⁻¹ * b * g ∈ B := by
    have := conj_mem_of_mem_normalizer ((normalizer (B : Set Γ)).inv_mem hgB) hb
    simpa using this
  have hcomm := mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 _ hb'
  calc b * (g * u * g⁻¹) = g * ((g⁻¹ * b * g) * u) * g⁻¹ := by group
    _ = g * (u * (g⁻¹ * b * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * u * g⁻¹) * b := by group

theorem litU_normalizer {N B : Subgroup Γ} {g : Γ} (hgN : g ∈ normalizer (N : Set Γ))
    (hgB : g ∈ normalizer (B : Set Γ)) : g ∈ normalizer (litU N B : Set Γ) := by
  intro u
  refine ⟨litU_conj hgN hgB, fun h => ?_⟩
  have := litU_conj ((normalizer (N : Set Γ)).inv_mem hgN)
    ((normalizer (B : Set Γ)).inv_mem hgB) h
  have e : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
  rwa [e] at this

theorem litX_conj {N B : Subgroup Γ} {g x : Γ} (hgN : g ∈ normalizer (N : Set Γ))
    (hgB : g ∈ normalizer (B : Set Γ)) (hx : x ∈ litX N B) : g * x * g⁻¹ ∈ litX N B := by
  refine ⟨litFit_conj hgN hx.1, ?_⟩
  have hg := litU_normalizer hgN hgB
  exact (normalizer (litU N B : Set Γ)).mul_mem ((normalizer (litU N B : Set Γ)).mul_mem hg hx.2)
    ((normalizer (litU N B : Set Γ)).inv_mem hg)

theorem lit_two_power_fix {N : Subgroup Γ} (hN : Odd (Nat.card N)) {b x u : Γ} {k : ℕ}
    (hb : b ^ 2 ^ k = 1) (hu : u ∈ N) (hbu : b * u * b⁻¹ = u) (hx : b * x * b⁻¹ = x * u) :
    u = 1 := by
  have key : ∀ j : ℕ, b ^ j * x * (b ^ j)⁻¹ = x * u ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hpow : b * u ^ j * b⁻¹ = u ^ j := by rw [← conj_pow, hbu]
      calc b ^ (j + 1) * x * (b ^ (j + 1))⁻¹ = b * (b ^ j * x * (b ^ j)⁻¹) * b⁻¹ := by group
        _ = b * (x * u ^ j) * b⁻¹ := by rw [ih]
        _ = (b * x * b⁻¹) * (b * u ^ j * b⁻¹) := by group
        _ = x * u ^ (j + 1) := by rw [hx, hpow]; group
  have h1 : u ^ 2 ^ k = 1 := by
    have := key (2 ^ k)
    rw [hb] at this
    simpa using this.symm
  have h2 : orderOf u ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨u, hu⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (2 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hN)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h3 h2))

theorem lit_closure_two {B : Subgroup Γ}
    (hB2 : B ≤ Subgroup.closure {x | x ∈ B ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}) {S : Set Γ}
    (h : ∀ b ∈ B, (∃ k : ℕ, b ^ 2 ^ k = 1) → ∀ x ∈ S, x * b = b * x) :
    ∀ b ∈ B, ∀ x ∈ S, x * b = b * x := by
  have hle : Subgroup.closure {x | x ∈ B ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} ≤ centralizer S := by
    rw [Subgroup.closure_le]
    intro b hb
    exact mem_centralizer_iff.mpr fun x hx => h b hb.1 hb.2 x hx
  intro b hb x hx
  exact mem_centralizer_iff.mp (hle (hB2 hb)) x hx

end CFSG.OddStandard.HigherRank.YamadaG23
