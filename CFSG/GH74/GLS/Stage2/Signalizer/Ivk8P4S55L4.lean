module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4Tor
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4Desc
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenF
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenBT
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenT

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.LinearDescent (higher_linear_prime_semilinear_field_descent)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (innSub)

section Parity

variable {F : Type} [Field F] [Finite F]

theorem even_of_gaussianCoeff_four {q k idx : ℕ} (hq : Odd q) (hq2 : 2 ≤ q) (hk1 : 1 ≤ k)
    (hk3 : k ≤ 3) (h : (idx : ℚ) = gaussianCoeff 4 k q) : Even idx := by
  have hq1 : (q : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq2
    linarith
  have hq2' : (q : ℚ) ^ 2 - 1 ≠ 0 := by
    intro h0
    have h2 : (2 : ℚ) ≤ q := by exact_mod_cast hq2
    have : (2 : ℚ) ^ 2 ≤ (q : ℚ) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
    linarith
  have hq3 : (q : ℚ) ^ 3 - 1 ≠ 0 := by
    intro h0
    have h2 : (2 : ℚ) ≤ q := by exact_mod_cast hq2
    have : (2 : ℚ) ^ 3 ≤ (q : ℚ) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
    linarith
  have hodd : q % 2 = 1 := Nat.odd_iff.mp hq
  interval_cases k
  · have h1 : (idx : ℚ) = ((q ^ 3 + q ^ 2 + q + 1 : ℕ) : ℚ) := by
      rw [h]
      simp only [gaussianCoeff, Finset.prod_range_succ, Finset.prod_range_zero]
      push_cast
      field_simp
      ring
    have h2 : idx = q ^ 3 + q ^ 2 + q + 1 := by exact_mod_cast h1
    rw [h2, Nat.even_iff]
    simp [Nat.add_mod, Nat.pow_mod, hodd]
  · have h1 : (idx : ℚ) = (((q ^ 2 + 1) * (q ^ 2 + q + 1) : ℕ) : ℚ) := by
      rw [h]
      simp only [gaussianCoeff, Finset.prod_range_succ, Finset.prod_range_zero]
      push_cast
      field_simp
      ring
    have h2 : idx = (q ^ 2 + 1) * (q ^ 2 + q + 1) := by exact_mod_cast h1
    rw [h2, Nat.even_iff]
    simp [Nat.add_mod, Nat.pow_mod, Nat.mul_mod, hodd]
  · have h1 : (idx : ℚ) = ((q ^ 3 + q ^ 2 + q + 1 : ℕ) : ℚ) := by
      rw [h]
      simp only [gaussianCoeff, Finset.prod_range_succ, Finset.prod_range_zero]
      push_cast
      field_simp
      ring
    have h2 : idx = q ^ 3 + q ^ 2 + q + 1 := by exact_mod_cast h1
    rw [h2, Nat.even_iff]
    simp [Nat.add_mod, Nat.pow_mod, hodd]

theorem evenParabolics_l4 {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ] (hℓ : ℓ ≠ 2) :
    EvenParabolics ℓ (projectiveSL 4 F) := by
  intro S M hSM hM
  obtain ⟨M', hM', hMM'⟩ := (eq_top_or_exists_le_coatom M).resolve_left hM
  have hmem : M' ∈ maximalParabolics (projectiveSL 4 F) ℓ := ⟨hM', _, ⟨S, rfl⟩, hSM.trans hMM'⟩
  obtain ⟨W, ⟨hW0, hWt⟩, hM'W⟩ :=
    ((maximal_parabolics (K := F) (n := 4) ℓ (by norm_num)).1 ▸ hmem :
      M' ∈ projStabilizer '' {W : Submodule F (Fin 4 → F) | ⊥ < W ∧ W < ⊤})
  have hfin := Module.finrank_fin_fun F (n := 4)
  have hk1 : 1 ≤ Module.finrank F W := Submodule.one_le_finrank_iff.mpr (bot_lt_iff_ne_bot.mp hW0)
  have hk3 : Module.finrank F W ≤ 3 := by
    have h1 : Module.finrank F W < Module.finrank F (Fin 4 → F) :=
      Submodule.finrank_lt (lt_top_iff_ne_top.mp hWt)
    rw [hfin] at h1
    omega
  have hidx := (subspace_index (K := F) (n := 4) (k := Module.finrank F W) (by omega)).2 W rfl
  have hodd : Odd (Nat.card F) := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two (by rwa [ringChar.eq F ℓ]))
  have hq2 : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have hev : Even M'.index := by
    rw [← hM'W]
    exact even_of_gaussianCoeff_four hodd hq2 hk1 hk3 hidx
  exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hev).trans (Subgroup.index_dvd_of_le hMM'))

end Parity

section Outer

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem linearAutGroup_eq_range : linearAutGroup 4 F = (conjAut 4 F).range := by
  unfold linearAutGroup
  rw [← MonoidHom.coe_range]
  exact Subgroup.closure_eq _

theorem outerFalse_l4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) : OuterFalse p (projectiveSL 4 F) := by
  intro α hα hαp _ hHH
  have : Fact p.Prime := ⟨hp⟩
  have hFp : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hodd : ringChar F ≠ 2 := by rwa [ringChar.eq F p]
  have hα1 : α ≠ 1 := fun h => hα ⟨1, by simp [h]⟩
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hdesc := higher_linear_prime_semilinear_field_descent (n := 4) (K := F) (ℓ := p)
    hp hf (by norm_num) hcard
  obtain ⟨-, -, -, -, -, -, hab, -⟩ := hdesc
  have htrans := standard_automorphism_transport (K := F) (n := 4)
  have hE : α ∈ semilinearAutGroup 4 F := by
    obtain ⟨A, σ0, ε, hε, hαeq⟩ :=
      (automorphism_generation (K := F) (n := 4) (by norm_num)).2 α
    have hx : conjAut 4 F A * fieldAut 4 F σ0 ∈ semilinearAutGroup 4 F :=
      mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
        (fieldAut_mem_semilinearAutGroup σ0)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · rw [pow_zero, mul_one] at hαeq
      rw [hαeq]
      exact hx
    · rw [pow_one] at hαeq
      set x := conjAut 4 F A * fieldAut 4 F σ0 with hxdef
      set δ := dualAut 4 F with hδdef
      have hδδ : δ * δ = 1 := htrans.2.2.2.1
      have hδinv : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδδ
      have hcomm : δ * x * δ⁻¹ * x⁻¹ ∈ linearAutGroup 4 F := hab δ x
      have hsq : α * α ∈ semilinearAutGroup 4 F := by
        have h1 : α * α = x * ((δ * x * δ⁻¹ * x⁻¹) * x) := by
          rw [hαeq, hδinv]
          group
        rw [h1]
        exact mul_mem hx (mul_mem (linearAutGroup_le_semilinearAutGroup hcomm) hx)
      obtain ⟨m, hm⟩ := hpodd
      have h2 : α = (α * α) ^ (m + 1) := by
        rw [← pow_two, ← pow_mul, show 2 * (m + 1) = p + 1 by omega, pow_succ,
          (hord ▸ pow_orderOf_eq_one α : α ^ p = 1), one_mul]
      rw [h2]
      exact pow_mem hsq _
  have hD : α ∉ linearAutGroup 4 F := by
    intro hD
    rw [linearAutGroup_eq_range] at hD
    obtain ⟨A', hA'⟩ := hD
    have hodd' : Odd (orderOf (conjAut 4 F A')) := by
      rw [hA', hord]
      exact hpodd
    have hin := ka_conjAut_inner_of_odd_pl4 hodd A' hodd'
    rw [hA'] at hin
    exact hα hin
  obtain ⟨hpf, σ, -, hαh, hfix⟩ := linear_prime_descent_char (ℓ := p) (K := F) (n := 4) hp hf
    (by norm_num) hcard hp hE hD hord
  obtain ⟨h, -, hαh⟩ := hαh
  obtain ⟨e, rfl⟩ := hpf
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  have hcard' : Nat.card F = (p ^ e) ^ p := by rw [hcard, pow_mul']
  have hfix' : Nat.card (semilinearFixedSubfield σ) = p ^ e := by
    rw [hfix, Nat.mul_div_cancel_left e hp.pos]
  obtain ⟨r, c, hr, hr2, hrp, hcr, hσc⟩ := exists_torsion_moved hp hp2 he σ hcard' hfix'
  have hfsig : ∀ l : Fˣ, fieldAut 4 F σ (l4Tor l) = l4Tor (Units.map (σ : F →* F) l) :=
    fieldAut_l4Tor σ
  let T : Subgroup (projectiveSL 4 F) := ((powMonoidHom r : Fˣ →* Fˣ).ker).map l4Tor
  have hT : IsPGroup r ↥T := by
    rintro ⟨_, l, hl, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hl' : l ^ r = 1 := hl
    show (l4Tor l) ^ r ^ 1 = 1
    rw [pow_one, ← map_pow, hl', map_one]
  have hfT : ∀ x ∈ T, fieldAut 4 F σ x ∈ T := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨Units.map (σ : F →* F) l, ?_, (hfsig l).symm⟩
    have hl' : l ^ r = 1 := hl
    show (Units.map (σ : F →* F) l) ^ r = 1
    rw [← map_pow, hl', map_one]
  have hcT : l4Tor c ∈ T := ⟨c, hcr, rfl⟩
  have hne : fieldAut 4 F σ (l4Tor c) ≠ l4Tor c := by
    rw [hfsig]
    intro h'
    apply hσc
    have := l4Tor_injective h'
    exact congrArg Units.val this
  exact false_of_torus_moved hαh hr hr2 hrp hT hfT hcT hne hHH

end Outer

section Cell

theorem defData_l4 {p : ℕ} {Y : Type} [Group Y] [Finite Y] (hp : p.Prime) (hp2 : p ≠ 2)
    (h : FL4d p Y) : DefData p Y := by
  obtain ⟨f, hf, -, hlie⟩ := h
  obtain ⟨F, iF, fF, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hlie
  have : Fact p.Prime := ⟨hp⟩
  have hFp : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  exact ⟨borelTitsConcl_of_lieModel hlie (by decide), EvenParabolics.of_mulEquiv e
    (evenParabolics_l4 hp2), OuterFalse.of_mulEquiv e (outerFalse_l4 hp hp2 hf hcard)⟩

theorem def55_l4 : Def55 FL4d :=
  def55_of_defData fun _ _ _ _ hp hp2 _ h => defData_l4 hp hp2 h

end Cell

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
