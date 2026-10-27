module

public import CFSG.GH74.GLS.Stage4.HexModelD4
public import CFSG.ClassicalInvolution.Balance.BootstrapExoticD4Sl3
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4HexLong
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4
  CFSG.Timmesfeld CFSG.Timmesfeld.RankTwo CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex
  CFSG.ClassicalInvolution.Balance CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.RankThree.PartOne.KCUnitary
open scoped MatrixGroups

theorem exists_even_hexPos_eq_g2Hex (j : Fin 6) :
    ∃ k : ℤ, CFSG.GH74.BNPair.IsRoot 6 k ∧ k % 2 = 0 ∧ g2Hex j = hexPos k := by
  fin_cases j
  · refine ⟨6, ⟨by norm_num, by norm_num⟩, by norm_num, ?_⟩
    funext i
    fin_cases i <;> simp [g2Hex, hexPos]
  · refine ⟨4, ⟨by norm_num, by norm_num⟩, by norm_num, ?_⟩
    funext i
    fin_cases i <;> simp [g2Hex, hexPos]
  · refine ⟨2, ⟨by norm_num, by norm_num⟩, by norm_num, ?_⟩
    funext i
    fin_cases i <;> simp [g2Hex, hexPos]
  · refine ⟨-6, ⟨by norm_num, by norm_num⟩, by norm_num, ?_⟩
    funext i
    fin_cases i <;> simp [g2Hex, hexPos]
  · refine ⟨-4, ⟨by norm_num, by norm_num⟩, by norm_num, ?_⟩
    funext i
    fin_cases i <;> simp [g2Hex, hexPos]
  · refine ⟨-2, ⟨by norm_num, by norm_num⟩, by norm_num, ?_⟩
    funext i
    fin_cases i <;> simp [g2Hex, hexPos]

theorem exists_g2Hex_eq_even_hexPos {k : ℤ} (hk : CFSG.GH74.BNPair.IsRoot 6 k)
    (hk2 : k % 2 = 0) : ∃ j : Fin 6, g2Hex j = hexPos k := by
  obtain ⟨hk0, hk6⟩ := hk
  have hk' : k = 2 ∨ k = 4 ∨ k = 6 ∨ k = -2 ∨ k = -4 ∨ k = -6 := by omega
  rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨2, ?_⟩
    funext i
    fin_cases i <;> simp [g2Hex, hexPos]
  · refine ⟨1, ?_⟩
    funext i
    fin_cases i <;> simp [g2Hex, hexPos]
  · refine ⟨0, ?_⟩
    funext i
    fin_cases i <;> simp [g2Hex, hexPos]
  · refine ⟨5, ?_⟩
    funext i
    fin_cases i <;> simp [g2Hex, hexPos]
  · refine ⟨4, ?_⟩
    funext i
    fin_cases i <;> simp [g2Hex, hexPos]
  · refine ⟨3, ?_⟩
    funext i
    fin_cases i <;> simp [g2Hex, hexPos]

variable {K : Type} [Field K] [Finite K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem d4RGD2_gen :
    ((⨆ i, hHat σ i) ⊔ posUnipotent (g2Shape (twistedX σ))) ⊔ (d4RGD2 σ hσ).N = ⊤ :=
  hexRGD2_gen (twistedData σ hσ)

include hσ in
theorem d4X_mem_longSub (j : Fin 6) (c : fixedField σ) :
    d4X hσ j c ∈ longSub 6 (hexGroup (twistedX σ)) := by
  obtain ⟨k, hk, hk2, hjk⟩ := exists_even_hexPos_eq_g2Hex j
  have hmem : d4X hσ j c ∈ (twistedDatum σ).rootGroup (g2Hex j) :=
    (mem_rootGroup_d4Hex_iff hσ j).2 ⟨c, rfl⟩
  refine root_le_longSub hk hk2 ?_
  show d4X hσ j c ∈ twistedRootGroup σ (hexPos k)
  rw [← hjk]
  exact hmem

include hσ in
theorem d4_longSub_quasisimple :
    CFSG.IsQuasisimple ↥(longSub 6 (hexGroup (twistedX σ))) := by
  obtain ⟨ρ, l, hl, hρ⟩ := d4_exists_sl3 hσ
  have hl0 : l 0 ≠ 0 := fun h => by
    have := hl 0
    rw [h, mul_zero] at this
    exact zero_ne_one this
  have hnt : ∃ g, ρ g ≠ 1 := ⟨tv 0 1 1, fun h => by
    rw [(hρ 1).1] at h
    have h2 := d4X_injective 0 (h.trans (d4X_zero 0).symm)
    exact hl0 (by simpa using h2)⟩
  have hSL := SpecialLinear.isQuasisimple 2 (fixedField σ) le_rfl
  have hker : ρ.ker ≤ Subgroup.center SL(3, fixedField σ) :=
    ker_le_center_of_isQuasisimple hSL hnt
  have hrange : ρ.range = longSub 6 (hexGroup (twistedX σ)) := by
    apply le_antisymm
    · have m01 : ∀ c, ρ (tv 0 1 c) ∈ longSub 6 (hexGroup (twistedX σ)) := fun c => by
        rw [(hρ c).1]
        exact d4X_mem_longSub hσ 0 _
      have m12 : ∀ c, ρ (tv 1 2 c) ∈ longSub 6 (hexGroup (twistedX σ)) := fun c => by
        rw [(hρ c).2.1]
        exact d4X_mem_longSub hσ 2 _
      have m02 : ∀ c, ρ (tv 0 2 c) ∈ longSub 6 (hexGroup (twistedX σ)) := fun c => by
        rw [(hρ c).2.2.1]
        exact d4X_mem_longSub hσ 1 _
      have m10 : ∀ c, ρ (tv 1 0 c) ∈ longSub 6 (hexGroup (twistedX σ)) := fun c => by
        rw [(hρ c).2.2.2.1]
        exact d4X_mem_longSub hσ 3 _
      have m21 : ∀ c, ρ (tv 2 1 c) ∈ longSub 6 (hexGroup (twistedX σ)) := fun c => by
        rw [(hρ c).2.2.2.2.1]
        exact d4X_mem_longSub hσ 5 _
      have m20 : ∀ c, ρ (tv 2 0 c) ∈ longSub 6 (hexGroup (twistedX σ)) := fun c => by
        rw [(hρ c).2.2.2.2.2]
        exact d4X_mem_longSub hσ 4 _
      have key : ∀ (i j : Fin 3) (c : fixedField σ), i ≠ j →
          ρ (tv i j c) ∈ longSub 6 (hexGroup (twistedX σ)) := by
        intro i j c hij
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact m01 c
        · exact m02 c
        · exact m10 c
        · exact absurd rfl hij
        · exact m12 c
        · exact m20 c
        · exact m21 c
        · exact absurd rfl hij
      rw [MonoidHom.range_eq_map, Subgroup.map_le_iff_le_comap,
        ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
          (ι := Fin 3) (K := ↥(fixedField σ)), Subgroup.closure_le]
      rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
      show ρ (Matrix.SpecialLinearGroup.transvection hij c) ∈
        longSub 6 (hexGroup (twistedX σ))
      rw [← tv_of_ne hij c]
      exact key i j c hij
    · have hrg : ∀ j : Fin 6, ∀ x ∈ (twistedDatum σ).rootGroup (g2Hex j), x ∈ ρ.range := by
        intro j x hx
        have hx' : x ∈ Set.range fun c => d4X hσ j (l j * c) := by
          rw [← twistedDatum_rootGroup_hex_eq_range hσ j (hl j)]
          exact hx
        obtain ⟨c, rfl⟩ := hx'
        fin_cases j
        · exact ⟨tv 0 1 c, (hρ c).1⟩
        · exact ⟨tv 0 2 c, (hρ c).2.2.1⟩
        · exact ⟨tv 1 2 c, (hρ c).2.1⟩
        · exact ⟨tv 1 0 c, (hρ c).2.2.2.1⟩
        · exact ⟨tv 2 0 c, (hρ c).2.2.2.2.2⟩
        · exact ⟨tv 2 1 c, (hρ c).2.2.2.2.1⟩
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨k, hk, hk2, hx⟩
      obtain ⟨j, hjk⟩ := exists_g2Hex_eq_even_hexPos hk hk2
      have hx' : x ∈ twistedRootGroup σ (hexPos k) := hx
      rw [← hjk] at hx'
      exact hrg j x hx'
  rw [← hrange]
  exact isQuasisimple_range hSL ρ hker

theorem d4_card_long {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) {k : ℤ} (hk1 : 1 ≤ k) (hk6 : k ≤ 6) (hk2 : k % 2 = 0) :
    Nat.card ↥(hexGroup (twistedX σ) k) = q := by
  have hγ : IsRoot .G2 (hexPos k) := isRoot_hexPos (by omega) (by omega)
  have hl : d43Long (hexPos k) := (d43Long_hexPos hk1 hk6).2 hk2
  exact (card_twistedRootGroup_long (sigma_three_of_card hK hσq) hγ hl).trans
    (card_fixedField_of_cube σ hq hK hσq)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
