module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Sp4

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.Classical.SteinbergBY
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (innSub)

section Transport

variable {p : ℕ} {Y Y' : Type} [Group Y] [Group Y']

theorem OuterFalseNS.of_mulEquiv (e : Y ≃* Y') (h : OuterFalseNS p Y') :
    OuterFalseNS p Y := by
  intro α hα hαp hHH
  let α' : MulAut Y' := MulAut.congr e α
  have hα'y : ∀ y : Y, α' (e y) = e (α y) := by
    intro y
    simp [α', MulAut.congr_apply]
  refine h α' ?_ ?_ ?_
  · rintro ⟨y', hy'⟩
    apply hα
    refine ⟨e.symm y', ?_⟩
    ext y
    have := congrArg (fun φ : MulAut Y' => φ (e y)) hy'
    simp only [MulAut.conj_apply, hα'y] at this
    apply e.injective
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact this
  · have : α' ^ p = MulAut.congr e (α ^ p) := (map_pow (MulAut.congr e) α p).symm
    rw [this, hαp, map_one]
  · intro r hr hr2 hrp Q' hQ' hinv x' hx'
    let Q : Subgroup Y := Q'.comap e.toMonoidHom
    have hQ : IsPGroup r ↥Q := hQ'.comap_of_injective e.toMonoidHom e.injective
    have hinvQ : ∀ x ∈ Q, α x ∈ Q := by
      intro x hx
      show e (α x) ∈ Q'
      rw [← hα'y]
      exact hinv _ hx
    have hfix := hHH r hr hr2 hrp Q hQ hinvQ
    have hmem : e.symm x' ∈ Q := by
      show e (e.symm x') ∈ Q'
      simpa using hx'
    have h1 := hfix _ hmem
    have h2 := hα'y (e.symm x')
    rw [MulEquiv.apply_symm_apply] at h2
    rw [h2, h1, MulEquiv.apply_symm_apply]

end Transport

section Outer

variable {F : Type} [Field F] [Finite F]

theorem outerFalseNS_sp4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) : OuterFalseNS p (StatedProj (StatedSp 2 F)) := by
  intro α hα hαp hHH
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

theorem outerFalseNS_of_fsp4d {p : ℕ} {Y : Type} [Group Y] (hp : p.Prime) (hp2 : p ≠ 2)
    (h : FSp4d p Y) : OuterFalseNS p Y := by
  obtain ⟨f, hf, hlie⟩ := h
  obtain ⟨-, F, iF, fF, hcard, ⟨e⟩⟩ := Final.lieModel_psp_unpack hlie
  exact OuterFalseNS.of_mulEquiv e (outerFalseNS_sp4 hp hp2 hf hcard)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
