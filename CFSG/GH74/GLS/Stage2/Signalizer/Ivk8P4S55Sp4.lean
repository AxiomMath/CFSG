module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Sp4Tor
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenF
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenBT
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenT

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.Classical.SteinbergBY
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (innSub)

section Parity

variable {F : Type} [Field F] [Finite F]

theorem evenParabolics_sp4 {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ] (hℓ : ℓ ≠ 2) :
    EvenParabolics ℓ (StatedProj (StatedSp 2 F)) := by
  intro S M hSM hM
  obtain ⟨M', hM', hMM'⟩ := (eq_top_or_exists_le_coatom M).resolve_left hM
  have hmem : M' ∈ spMaximalParabolics 2 F ℓ := ⟨hM', _, ⟨S, rfl⟩, hSM.trans hMM'⟩
  obtain ⟨W, hW0, hWiso, hM'W⟩ :=
    ((maximal_parabolics (K := F) (r := 2) ℓ (by norm_num)).1 ▸ hmem :
      M' ∈ {M | ∃ W : Submodule F (Fin 2 ⊕ Fin 2 → F), W ≠ ⊥ ∧
        IsTotallyIsotropic (pairedSympForm F 2) W ∧ M = projStabilizer 2 F W})
  have hidx := Odd87.index_projStabilizer_isotropic hW0 hWiso
  have hodd : Odd (Nat.card F) := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two (by rwa [ringChar.eq F ℓ]))
  have hev : Even M'.index := by
    rw [hM'W, hidx]
    exact (hodd.add_one).mul_right _
  exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hev).trans (Subgroup.index_dvd_of_le hMM'))

end Parity

section Outer

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem spLinearAutGroup_eq_range :
    spLinearAutGroup 2 F = (conjAut 2 F).range := by
  unfold spLinearAutGroup
  rw [← MonoidHom.coe_range]
  exact Subgroup.closure_eq _

theorem outerFalse_sp4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) : OuterFalse p (StatedProj (StatedSp 2 F)) := by
  intro α hα hαp _ hHH
  have : Fact p.Prime := ⟨hp⟩
  have hFp : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hodd : ringChar F ≠ 2 := by rwa [ringChar.eq F p]
  have hα1 : α ≠ 1 := fun h => hα ⟨1, by simp [h]⟩
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  obtain ⟨A, σ0, hαeq⟩ := psp4_odd_automorphism_normal_form hodd α
  have hE : α ∈ spSemilinearAutGroup 2 F := by
    rw [hαeq]
    exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
      (fieldAut_mem_spSemilinearAutGroup σ0)
  have hD : α ∉ spLinearAutGroup 2 F := by
    intro hD
    rw [spLinearAutGroup_eq_range] at hD
    obtain ⟨A', hA'⟩ := hD
    have hodd' : Odd (orderOf (conjAut 2 F A')) := by
      rw [hA', hord]
      exact hp.odd_of_ne_two hp2
    have hin := ka_conjAut_inner_of_odd hodd A' hodd'
    rw [hA'] at hin
    exact hα hin
  obtain ⟨-, -, -, -, -, -, -, -, -, hdesc⟩ :=
    symplectic_prime_semilinear_field_descent (ℓ := p) (f := f) (r := 2) hp hf (le_refl 2) hcard
  obtain ⟨hpf, σ, -, hfix, h, -, hαh⟩ := hdesc p hp α hE hD hord
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
  have hfsig : ∀ l : Fˣ, fieldAut 2 F σ (sp4Tor l) = sp4Tor (Units.map (σ : F →* F) l) :=
    fieldAut_sp4Tor σ
  let T : Subgroup (StatedProj (StatedSp 2 F)) := ((powMonoidHom r : Fˣ →* Fˣ).ker).map sp4Tor
  have hT : IsPGroup r ↥T := by
    rintro ⟨_, l, hl, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hl' : l ^ r = 1 := hl
    show (sp4Tor l) ^ r ^ 1 = 1
    rw [pow_one, ← map_pow, hl', map_one]
  have hfT : ∀ x ∈ T, fieldAut 2 F σ x ∈ T := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨Units.map (σ : F →* F) l, ?_, (hfsig l).symm⟩
    have hl' : l ^ r = 1 := hl
    show (Units.map (σ : F →* F) l) ^ r = 1
    rw [← map_pow, hl', map_one]
  have hcT : sp4Tor c ∈ T := ⟨c, hcr, rfl⟩
  have hne : fieldAut 2 F σ (sp4Tor c) ≠ sp4Tor c := by
    rw [hfsig]
    intro h'
    apply hσc
    have := sp4Tor_injective h'
    exact congrArg Units.val this
  exact false_of_torus_moved hαh hr hr2 hrp hT hfT hcT hne hHH

end Outer

section Cell

theorem defData_sp4 {p : ℕ} {Y : Type} [Group Y] [Finite Y] (hp : p.Prime) (hp2 : p ≠ 2)
    (h : FSp4d p Y) : DefData p Y := by
  obtain ⟨f, hf, hlie⟩ := h
  obtain ⟨-, F, iF, fF, hcard, ⟨e⟩⟩ := Final.lieModel_psp_unpack hlie
  have : Fact p.Prime := ⟨hp⟩
  have hFp : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  exact ⟨borelTitsConcl_of_lieModel hlie (by decide), EvenParabolics.of_mulEquiv e
    (evenParabolics_sp4 hp2), OuterFalse.of_mulEquiv e (outerFalse_sp4 hp hp2 hf hcard)⟩

theorem def55_sp4 : Def55 FSp4d :=
  def55_of_defData fun _ _ _ _ hp hp2 _ h => defData_sp4 hp hp2 h

end Cell

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
