module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Cover3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Cover2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA.Y10F.TwA5Cover
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

private theorem omega_cube {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by rw [hω, mul_zero]
  have h' : ω ^ 3 - 1 = 0 := by linear_combination h
  exact sub_eq_zero.mp h'

private theorem omega_ne_one {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  intro h
  have h3 : (3 : F) = 0 := by
    have h' := hω
    rw [h] at h'
    norm_num at h'
    exact h'
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h1 : (1 : F) = 0 := by linear_combination h3 - h2
  exact one_ne_zero h1

private theorem omega_norm (h : UnitaryFieldData 2 n F) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    (hbar : h.bar ω = ω + 1) : h.norm ω = 1 := by
  rw [UnitaryFieldData.norm, hbar]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination hω - h2

private theorem omega_five_inv {ω : F} (hω3 : ω ^ 3 = 1) : (ω ^ 5)⁻¹ = ω := by
  have h5 : ω ^ 5 = ω ^ 2 := by
    rw [show (5 : ℕ) = 2 + 3 by norm_num, pow_add, hω3, mul_one]
  rw [h5]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, show (2 : ℕ) + 1 = 3 by norm_num, hω3])

private theorem coverDiag_vx_eq_diagFiveLast (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) :
    coverDiag h hω3 hωnorm hω1 vx = diagFiveLast h ω hωnorm := by
  apply Subtype.ext; apply Units.ext
  rw [coe_coverDiag, coe_diagFiveLast, coverEntry_vx]
  congr 1
  funext i
  fin_cases i <;> simp [diagFiveLastEntries, omega_five_inv hω3]

private theorem coverDiag_vx_mem_center (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) :
    coverDiag h hω3 hωnorm hω1 vx ∈ Subgroup.center (unitarySU 2 n F 6) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext; apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_coverDiag,
    coverEntry_vx]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

private theorem mem_centralizer_of_mem_center {X : Type} [Group X] {x : X}
    (hx : x ∈ Subgroup.center X) (S : Subgroup X) : x ∈ Subgroup.centralizer (S : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y _
  exact Subgroup.mem_center_iff.1 hx y

theorem cover_eight (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) :
    ∃ S : Subgroup (unitarySU 2 n F 6),
      IsPGroup 2 S ∧
      coverSubgroup h hω3 hωnorm hω1 ≤ Subgroup.normalizer (S : Set (unitarySU 2 n F 6)) ∧
      coverSubgroup h hω3 hωnorm hω1 ⊓
        Subgroup.centralizer (S : Set (unitarySU 2 n F 6)) =
        Subgroup.zpowers (coverDiag h hω3 hωnorm hω1 vx) := by
  have hωne0 : ω ≠ 0 := CFSG.GH74.Uniqueness.Bender.Frame.ne_zero_of_norm_eq_one hωnorm
  let ζu : Fˣ := Units.mk0 ω hωne0
  have hζu : h.norm (ζu : F) = 1 := hωnorm
  have hB : ∀ A ∈ coverSubgroup h hω3 hωnorm hω1,
      ∃ (d : Fin 6 → F) (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1)
        (m : ℕ), A = diagSU h d hd hdet ∧ d 0 = d 1 ∧ d 0 = ((ζu ^ m : Fˣ) : F) := by
    intro A hA
    change A ∈ Set.range (coverDiag h hω3 hωnorm hω1) at hA
    obtain ⟨v, rfl⟩ := hA
    refine ⟨coverEntry (ω := ω) v, coverNorm h hωnorm v, coverDet h hω3 hω1 v,
      (coverLin v 0).val, rfl, rfl, ?_⟩
    rw [coverEntry, Units.val_pow_eq_pow_val, Units.val_mk0]
  refine ⟨unitaryLineRadical h, unitaryLineRadical_isPGroup h, ?_, ?_⟩
  · intro A hA
    change A ∈ Set.range (coverDiag h hω3 hωnorm hω1) at hA
    obtain ⟨v, rfl⟩ := hA
    exact diagSU_mem_normalizer_unitaryLineRadical h (coverNorm h hωnorm v)
      (coverDet h hω3 hω1 v) rfl
  · apply le_antisymm
    · have hle := inf_centralizer_unitaryLineRadical_le_zpowers h hζu hB
      simpa [ζu, coverDiag_vx_eq_diagFiveLast h hω3 hωnorm hω1] using hle
    · rw [Subgroup.zpowers_le]
      refine ⟨?_, mem_centralizer_of_mem_center
        (coverDiag_vx_mem_center h hω3 hωnorm hω1) _⟩
      change coverDiag h hω3 hωnorm hω1 vx ∈
        Set.range (coverDiag h hω3 hωnorm hω1)
      exact ⟨vx, rfl⟩

private theorem commute_unitaryBlock_coverDiag (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) (v : Fin 4 → ZMod 3)
    {l : unitarySU 2 n F 6} (hl : l ∈ unitaryBlock h ({0, 1} : Finset (Fin 6))) :
    coverDiag h hω3 hωnorm hω1 v * l = l * coverDiag h hω3 hωnorm hω1 v := by
  apply Subtype.ext; apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_coverDiag]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : i = j
  · subst hij; ring
  · by_cases hmem : i ∈ ({0, 1} : Finset (Fin 6)) ∧ j ∈ ({0, 1} : Finset (Fin 6))
    · obtain ⟨hi, hj⟩ := hmem
      have hd : coverEntry (ω := ω) v i = coverEntry (ω := ω) v j := by
        fin_cases hi <;> fin_cases hj <;> rfl
      rw [hd]; ring
    · have hl0 : (((l : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) i j = 0 := by
        have hm := (mem_unitaryBlock h).1 hl i j
        have hnot : i ∉ ({0, 1} : Finset (Fin 6)) ∨ j ∉ ({0, 1} : Finset (Fin 6)) := by
          by_contra hcon
          push Not at hcon
          exact hmem ⟨hcon.1, hcon.2⟩
        rw [hm hnot]
        simp [Matrix.one_apply, hij]
      rw [hl0]; ring

theorem cover_e3 (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) (hn : 2 ≤ n)
    (hqd : 3 ∣ 2 ^ (2 * n) - 1) :
    GLAPLayer 3 ((⊤ : Subgroup (unitarySU 2 n F 6)) ⊓
      Subgroup.centralizer (coverSubgroupE h hω3 hωnorm hω1 :
        Set (unitarySU 2 n F 6))) ≠ ⊥ := by
  have hLq : CFSG.IsQuasisimple ↥(unitaryBlock h ({0, 1} : Finset (Fin 6))) :=
    isQuasisimple_unitaryBlock_of_card_eq_two h (by simp) hn
  have hqL : 3 ∣ Nat.card ↥(unitaryBlock h ({0, 1} : Finset (Fin 6))) :=
    dvd_card_unitaryBlock_of_card_eq_two h (by simp) Nat.prime_three hqd
  refine glaPLayer_ne_bot_of_unitaryBlock_le h Nat.prime_three ?_ ?_ hLq hqL
  · intro l hl
    refine ⟨Subgroup.mem_top l, ?_⟩
    change l ∈ Subgroup.centralizer (coverSubgroupE h hω3 hωnorm hω1 :
      Set (unitarySU 2 n F 6))
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    change e ∈ Set.range (coverDiagE h hω3 hωnorm hω1) at he
    obtain ⟨w, rfl⟩ := he
    exact commute_unitaryBlock_coverDiag h hω3 hωnorm hω1 (eExp w) hl
  · intro g hg
    obtain ⟨_, hgC⟩ := hg
    have hA : coverDiag h hω3 hωnorm hω1 vA ∈ coverSubgroupE h hω3 hωnorm hω1 := by
      change coverDiag h hω3 hωnorm hω1 vA ∈
        Set.range (coverDiagE h hω3 hωnorm hω1)
      exact ⟨wA, by rw [coverDiagE, eExp_wA]⟩
    have hB : coverDiag h hω3 hωnorm hω1 vB ∈ coverSubgroupE h hω3 hωnorm hω1 := by
      change coverDiag h hω3 hωnorm hω1 vB ∈
        Set.range (coverDiagE h hω3 hωnorm hω1)
      exact ⟨wB, by rw [coverDiagE, eExp_wB]⟩
    have hgA : g ∈ Subgroup.centralizer
        ({coverDiag h hω3 hωnorm hω1 vA} : Set (unitarySU 2 n F 6)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.mem_centralizer_iff.1 hgC _ hA
    have hgB : g ∈ Subgroup.centralizer
        ({coverDiag h hω3 hωnorm hω1 vB} : Set (unitarySU 2 n F 6)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.mem_centralizer_iff.1 hgC _ hB
    rw [centralizer_vA h hω3 hωnorm hω1] at hgA
    rw [centralizer_vB h hω3 hωnorm hω1] at hgB
    have hmem := unitaryBlockDiag_inf_le h ({0, 1, 2} : Finset (Fin 6))
      ({0, 1, 3} : Finset (Fin 6)) (Subgroup.mem_inf.2 ⟨hgA, hgB⟩)
    simpa using hmem

theorem twA5CoverWitness (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    (hn : 2 ≤ n) (hodd : Odd n) (hF : Nat.card F = (2 ^ n) ^ 2) :
    TwA5CoverWitness n p F := by
  have hn1 : 1 ≤ n := by omega
  let h : UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, hn1, by rw [hF, ← pow_mul]; congr 1; ring⟩
  obtain ⟨ω, hω, hbar⟩ := CFSG.RankThree.PartOne.SEITZQ1.q1_exists_omega h hodd
  have hω3 : ω ^ 3 = 1 := omega_cube hω
  have hω1 : ω ≠ 1 := omega_ne_one hω
  have hωnorm : h.norm ω = 1 := omega_norm h hω hbar
  have hqd : 3 ∣ 2 ^ (2 * n) - 1 := by
    have h3 : 3 ∣ 2 ^ n + 1 :=
      CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.three_dvd_pow_add_one hodd
    have hpow : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm n 2]
    have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ n) 1
    rw [hpow, hsq]
    exact dvd_mul_of_dvd_left h3 _
  have he3 := cover_e3 h hω3 hωnorm hω1 hn hqd
  obtain ⟨S, hS2, hBS, hBC⟩ := cover_eight h hω3 hωnorm hω1
  refine ⟨coverSubgroup h hω3 hωnorm hω1, coverDiag h hω3 hωnorm hω1 vx,
    coverSubgroupE h hω3 hωnorm hω1, S,
    coverDiag_vx_mem_center h hω3 hωnorm hω1, ?_, ?_,
    coverSubgroup_elem h hω3 hωnorm hω1, coverSubgroup_card h hω3 hωnorm hω1,
    coverSubgroupE_le h hω3 hωnorm hω1, coverSubgroupE_elem h hω3 hωnorm hω1,
    coverSubgroupE_card h hω3 hωnorm hω1, ?_, he3, hS2, hBS, hBC⟩
  · change coverDiag h hω3 hωnorm hω1 vx ∈ Set.range (coverDiag h hω3 hωnorm hω1)
    exact ⟨vx, rfl⟩
  · rw [coverDiag_vx_eq_diagFiveLast h hω3 hωnorm hω1]
    intro hx
    have h := congrArg (fun z : unitarySU 2 n F 6 =>
      ((z : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) 0 0) hx
    simp [coe_diagFiveLast, diagFiveLastEntries] at h
    exact hω1 h
  · change coverDiag h hω3 hωnorm hω1 vx ∈ Set.range (coverDiagE h hω3 hωnorm hω1)
    exact ⟨wx, by rw [coverDiagE, eExp_wx]⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F
