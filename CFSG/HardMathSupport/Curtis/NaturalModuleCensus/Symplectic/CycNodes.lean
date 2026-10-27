module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.CycTwo
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.CycNodesStab
public import CFSG.Adapters.SpecialLinearPerfect

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.AGLEmbedding (CycPerfect)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom rho lam sl2Diag lam_sl2Diag)

variable {r : ℕ} {K : Type} [Field K]

theorem exists_unit_orderOf [Finite K] {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) :
    ∃ ω : Kˣ, orderOf ω = p := by
  have := Fact.mk hp
  have h : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  exact exists_prime_orderOf_dvd_card' p h

theorem range_le_perfectJoin [Finite K] (hK : 4 ≤ Nat.card K) {J : Subgroup (StatedSp r K)}
    (φ : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp r K) (h : φ.range ≤ J) :
    φ.range ≤ perfectJoin J := by
  refine le_perfectJoin h ?_
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have htop : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]

theorem torusPair_pow {p : ℕ} {ω : Kˣ} (hω : ω ^ p = 1) (i j : Fin r) :
    (Pi.mulSingle i ω * Pi.mulSingle j ω⁻¹ : Fin r → Kˣ) ^ p = 1 := by
  rw [mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, inv_pow, hω]
  simp

theorem torusPair_apply_fst {i j : Fin r} (hij : i ≠ j) (ω : Kˣ) :
    (Pi.mulSingle i ω * Pi.mulSingle j ω⁻¹ : Fin r → Kˣ) i = ω := by
  simp [hij]

theorem torusPair_apply_of_ne {i j k : Fin r} (hi : k ≠ i) (hj : k ≠ j) (ω : Kˣ) :
    (Pi.mulSingle i ω * Pi.mulSingle j ω⁻¹ : Fin r → Kˣ) k = 1 := by
  simp [hi, hj]

theorem torusPair_ne_one {p : ℕ} (hp : p.Prime) {ω : Kˣ} (hω : orderOf ω = p) {i j : Fin r}
    (hij : i ≠ j) : (Pi.mulSingle i ω * Pi.mulSingle j ω⁻¹ : Fin r → Kˣ) ≠ 1 := by
  intro h
  have h1 := congr_fun h i
  rw [torusPair_apply_fst hij] at h1
  have := hp.one_lt
  rw [Pi.one_apply] at h1
  rw [h1, orderOf_one] at hω
  omega

theorem false_of_cyc_one_three [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) {p : ℕ}
    (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hr : 3 ≤ r) {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r)
    (h1 : 1 ∉ I) (h3 : 3 ∉ I) (hcyc : CycPerfect p (flagStabilizer r K I)) : False := by
  obtain ⟨ω, hω⟩ := exists_unit_orderOf hp hpK
  have hωp : ω ^ p = 1 := hω ▸ pow_orderOf_eq_one ω
  have hp1 := hp.one_lt
  have h0r : 0 < r := by omega
  have h1r : 1 < r := by omega
  have h2r : 2 < r ∨ r = 3 := by omega
  let i0 : Fin r := ⟨0, h0r⟩
  let i1 : Fin r := ⟨1, h1r⟩
  let i2 : Fin r := ⟨2, by omega⟩
  have e01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have e02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have e12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have hH1 : (rho i0 i1 e01 : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp r K).range ≤
      flagStabilizer r K I :=
    range_rho_le_flagStabilizer hI e01 fun m hm => by
      have : m ≠ 1 := fun h => h1 (h ▸ hm)
      simp only [i0, i1]; omega
  have hd : torusHom (Pi.mulSingle i0 ω * Pi.mulSingle i1 ω⁻¹) ∈
      perfectJoin (flagStabilizer r K I) := by
    rw [← rho_sl2Diag e01]
    exact range_le_perfectJoin hK _ hH1 ⟨_, rfl⟩
  by_cases hr4 : 4 ≤ r
  · let i3 : Fin r := ⟨3, by omega⟩
    have e23 : i2 ≠ i3 := by simp [i2, i3, Fin.ext_iff]
    have e03 : i0 ≠ i3 := by simp [i0, i3, Fin.ext_iff]
    have e13 : i1 ≠ i3 := by simp [i1, i3, Fin.ext_iff]
    have hH2 : (rho i2 i3 e23 : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp r K).range ≤
        flagStabilizer r K I :=
      range_rho_le_flagStabilizer hI e23 fun m hm => by
        have : m ≠ 3 := fun h => h3 (h ▸ hm)
        simp only [i2, i3]; omega
    have hd' : torusHom (Pi.mulSingle i2 ω * Pi.mulSingle i3 ω⁻¹) ∈
        perfectJoin (flagStabilizer r K I) := by
      rw [← rho_sl2Diag e23]
      exact range_le_perfectJoin hK _ hH2 ⟨_, rfl⟩
    exact false_of_cyc_torus hp hcyc hd hd' (torusPair_pow hωp _ _) (torusPair_pow hωp _ _) hω
      (torusPair_apply_fst e01 ω) (torusPair_apply_of_ne e02 e03 ω)
      (torusPair_ne_one hp hω e23)
  · have hr3 : r = 3 := by omega
    have hH2 : (lam i2 : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp r K).range ≤
        flagStabilizer r K I :=
      range_lam_le_flagStabilizer hI fun m hm => by
        have : m ≠ 3 := fun h => h3 (h ▸ hm)
        have := hI m hm
        simp only [i2]; omega
    have hd' : torusHom (Pi.mulSingle i2 ω : Fin r → Kˣ) ∈ perfectJoin (flagStabilizer r K I) := by
      rw [← lam_sl2Diag]
      exact range_le_perfectJoin hK _ hH2 ⟨_, rfl⟩
    refine false_of_cyc_torus hp hcyc hd hd' (torusPair_pow hωp _ _) ?_ hω
      (torusPair_apply_fst e01 ω) (by simp [e02]) ?_
    · rw [← Pi.mulSingle_pow, hωp]; simp
    · intro h
      have h1 := congr_fun h i2
      simp at h1
      rw [h1, orderOf_one] at hω
      omega

theorem false_of_cyc_one_two [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) {p : ℕ}
    (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hr : 3 ≤ r) {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r)
    (h1 : 1 ∉ I) (h2 : 2 ∉ I) (hcyc : CycPerfect p (flagStabilizer r K I)) : False := by
  obtain ⟨ω, hω⟩ := exists_unit_orderOf hp hpK
  have hωp : ω ^ p = 1 := hω ▸ pow_orderOf_eq_one ω
  have hp1 := hp.one_lt
  let i0 : Fin r := ⟨0, by omega⟩
  let i1 : Fin r := ⟨1, by omega⟩
  let i2 : Fin r := ⟨2, by omega⟩
  have e01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have e02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have e12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have hH1 : (rho i0 i1 e01 : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp r K).range ≤
      flagStabilizer r K I :=
    range_rho_le_flagStabilizer hI e01 fun m hm => by
      have : m ≠ 1 := fun h => h1 (h ▸ hm)
      simp only [i0, i1]; omega
  have hH2 : (rho i1 i2 e12 : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp r K).range ≤
      flagStabilizer r K I :=
    range_rho_le_flagStabilizer hI e12 fun m hm => by
      have : m ≠ 2 := fun h => h2 (h ▸ hm)
      simp only [i1, i2]; omega
  have hd : torusHom (Pi.mulSingle i0 ω * Pi.mulSingle i1 ω⁻¹) ∈
      perfectJoin (flagStabilizer r K I) := by
    rw [← rho_sl2Diag e01]
    exact range_le_perfectJoin hK _ hH1 ⟨_, rfl⟩
  have hd' : torusHom (Pi.mulSingle i1 ω * Pi.mulSingle i2 ω⁻¹) ∈
      perfectJoin (flagStabilizer r K I) := by
    rw [← rho_sl2Diag e12]
    exact range_le_perfectJoin hK _ hH2 ⟨_, rfl⟩
  exact false_of_cyc_torus hp hcyc hd hd' (torusPair_pow hωp _ _) (torusPair_pow hωp _ _) hω
    (torusPair_apply_fst e01 ω) (torusPair_apply_of_ne e01 e02 ω)
    (torusPair_ne_one hp hω e12)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
