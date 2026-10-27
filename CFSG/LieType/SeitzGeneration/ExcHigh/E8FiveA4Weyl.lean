module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveWeyl
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveOrbit

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSq

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootSpace CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (charVal charVal_single)

set_option linter.unusedSectionVars false


theorem isSolvable_inf_dualWeylStabilizer {z₀ z₁ : Fin Tag.E8.rank → ZMod 5}
    (hreg : ∀ α, IsRoot Tag.E8 α → charVal z₀ α = 0 → charVal z₁ α = 0 → False) :
    Group.IsSolvable ↥(dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp : IsPGroup 5 ↥(dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁) := fun g => by
    refine ⟨2, Subtype.ext ?_⟩
    have h := pow_twentyFive_eq_one hreg (Subgroup.mem_inf.1 g.2).1 (Subgroup.mem_inf.1 g.2).2
    simpa using h
  haveI := hp.isNilpotent
  infer_instance

theorem exists_orderOf_eq_five_of_fix {z₀ z₁ : Fin Tag.E8.rank → ZMod 5}
    (hreg : ∀ α, IsRoot Tag.E8 α → charVal z₀ α = 0 → charVal z₁ α = 0 → False)
    {V : WeylGroup Tag.E8} (hV1 : V ≠ 1) (hV₀ : V ∈ dualWeylStabilizer z₀)
    (hV₁ : V ∈ dualWeylStabilizer z₁) :
    ∃ y : WeylGroup Tag.E8, orderOf y = 5 ∧ y ∈ dualWeylStabilizer z₀ ∧
      y ∈ dualWeylStabilizer z₁ := by
  have h25 := pow_twentyFive_eq_one hreg hV₀ hV₁
  have hord : orderOf V ∣ 25 := orderOf_dvd_of_pow_eq_one h25
  have hV5 : 5 ∣ orderOf V := by
    have h1 : orderOf V ≠ 1 := fun h => hV1 (orderOf_eq_one_iff.1 h)
    have hle : orderOf V ≤ 25 := Nat.le_of_dvd (by norm_num) hord
    generalize orderOf V = n at hord h1 hle ⊢
    interval_cases n <;> omega
  have hpos : orderOf V ≠ 0 := (Nat.pos_of_dvd_of_pos hord (by norm_num)).ne'
  exact ⟨V ^ (orderOf V / 5), orderOf_pow_orderOf_div hpos hV5, Subgroup.pow_mem _ hV₀ _,
    Subgroup.pow_mem _ hV₁ _⟩

theorem exists_fixSet_h_of_fix {z₀ z₁ : Fin Tag.E8.rank → ZMod 5}
    (hreg : ∀ α, IsRoot Tag.E8 α → charVal z₀ α = 0 → charVal z₁ α = 0 → False)
    {y : WeylGroup Tag.E8} (hy : orderOf y = 5) (hy₀ : y ∈ dualWeylStabilizer z₀)
    (hy₁ : y ∈ dualWeylStabilizer z₁) :
    ∃ (x : WeylGroup Tag.E8) (m : ℕ), 1 ≤ m ∧ m ≤ 4 ∧ trCol x z₀ ∈ fixSet (e8FiveH m) ∧
      trCol x z₁ ∈ fixSet (e8FiveH m) := by
  obtain ⟨x, i, j, hxy, hij⟩ := exists_conj_into_P hy
  have hz₀ : trCol x z₀ ∈ fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)) := by
    rw [← hxy]
    exact (mem_fixSet_trCol x y z₀).1 hy₀
  have hz₁ : trCol x z₁ ∈ fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)) := by
    rw [← hxy]
    exact (mem_fixSet_trCol x y z₁).1 hy₁
  have hreg' : ∀ α, IsRoot Tag.E8 α → charVal (trCol x z₀) α = 0 →
      charVal (trCol x z₁) α = 0 → False := fun α hα h₀ h₁ =>
    hreg (x⁻¹ • α) (IsRoot.smul hα x⁻¹) (by rwa [charVal_trCol] at h₀)
      (by rwa [charVal_trCol] at h₁)
  by_cases hi : (i : ℕ) = 0
  ·
    exfalso
    have hj : (j : ℕ) ≠ 0 := by
      rcases hij with h | h
      · exact absurd (Fin.ext hi) h
      · exact fun h0 => h (Fin.ext h0)
    have hw : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) = e8FiveG2 ^ (j : ℕ) := by
      rw [hi, pow_zero, one_mul]
    have hjd : ¬ 5 ∣ (j : ℕ) := fun h => hj (Nat.eq_zero_of_dvd_of_lt h j.2)
    have h7 : ∀ z ∈ fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)), z 7 = 0 := fun z hz => by
      rw [congrFun (fixSet_g2_param (fixSet_subset_of_pow e8FiveG2_pow hjd hw hz)) 7]
      rfl
    exact hreg' (Pi.single 7 1) (isRoot_single _ 7) (by rw [charVal_single]; exact h7 _ hz₀)
      (by rw [charVal_single]; exact h7 _ hz₁)
  have hid : ¬ 5 ∣ (i : ℕ) := fun h => hi (Nat.eq_zero_of_dvd_of_lt h i.2)
  by_cases hj : (j : ℕ) = 0
  ·
    exfalso
    have hw : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) = (e8FiveH 0) ^ (i : ℕ) := by
      rw [hj, pow_zero, mul_one, e8FiveH, pow_zero, mul_one]
    have h0 : ∀ z ∈ fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)), z 0 = 0 := fun z hz => by
      rw [congrFun (fixSet_h0_param (fixSet_subset_of_pow (e8FiveH_pow_five 0) hid hw hz)) 0]
      rfl
    exact hreg' (Pi.single 0 1) (isRoot_single _ 0) (by rw [charVal_single]; exact h0 _ hz₀)
      (by rw [charVal_single]; exact h0 _ hz₁)
  ·
    have hex : ∀ i j : Fin 5, (i : ℕ) ≠ 0 → ∃ m : Fin 5, ((m : ℕ) * i) % 5 = j := by decide
    obtain ⟨m, hm⟩ := hex i j hi
    have hw : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) = (e8FiveH m) ^ (i : ℕ) := by
      have hc : Commute e8FiveG1 (e8FiveG2 ^ (m : ℕ)) := Commute.pow_right e8Five_comm _
      rw [e8FiveH, hc.mul_pow, ← pow_mul, pow_eq_pow_mod ((m : ℕ) * (i : ℕ)) e8FiveG2_pow, hm]
    have hm0 : (m : ℕ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul, Nat.zero_mod] at hm
      exact hj hm.symm
    have hm4 : (m : ℕ) ≤ 4 := by have := m.2; omega
    exact ⟨x, m, Nat.one_le_iff_ne_zero.2 hm0, hm4,
      fixSet_subset_of_pow (e8FiveH_pow_five m) hid hw hz₀,
      fixSet_subset_of_pow (e8FiveH_pow_five m) hid hw hz₁⟩

theorem exists_orbit_of_fix {z₀ z₁ : Fin Tag.E8.rank → ZMod 5}
    (hreg : ∀ α, IsRoot Tag.E8 α → charVal z₀ α = 0 → charVal z₁ α = 0 → False)
    {y : WeylGroup Tag.E8} (hy : orderOf y = 5) (hy₀ : y ∈ dualWeylStabilizer z₀)
    (hy₁ : y ∈ dualWeylStabilizer z₁) {a b : ZMod 5} (hab : a • z₀ + b • z₁ ≠ 0) :
    ∃ u : WeylGroup Tag.E8, ∀ v : Fin Tag.E8.rank → ℤ,
      charVal (a • z₀ + b • z₁) (u • v) =
        charVal (Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5)) v := by
  obtain ⟨x, m, hm1, hm4, hz₀, hz₁⟩ := exists_fixSet_h_of_fix hreg hy hy₀ hy₁
  have hz : trCol x (a • z₀ + b • z₁) ∈ fixSet (e8FiveH m) := by
    rw [trCol_add, trCol_smul, trCol_smul]
    exact mem_fixSet_add hz₀ hz₁ a b
  have hne : trCol x (a • z₀ + b • z₁) ≠ 0 := fun h => hab (trCol_eq_zero h)
  obtain ⟨u, hu⟩ := fixSet_e8FiveH_orbit hm1 hm4 hz hne
  refine ⟨x⁻¹ * u, fun v => ?_⟩
  rw [mul_smul, ← charVal_trCol]
  exact hu v

end CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSq
