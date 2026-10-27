module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55EL3Tor
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4Desc
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenF
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GraphAut
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenT

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (innSub exists_semilinear_of_odd_pow)

section Outer

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem linearAutGroup_three_eq_range : linearAutGroup 3 F = (conjAut 3 F).range := by
  unfold linearAutGroup
  rw [← MonoidHom.coe_range]
  exact Subgroup.closure_eq _

omit [Finite F] in
theorem conjAut_three_inner_of_det_pow3 (M : GL (Fin 3) F) (μ : Fˣ)
    (h : (M : Matrix (Fin 3) (Fin 3) F).det = (μ : F) ^ 3) :
    conjAut 3 F M ∈ innSub (projectiveSL 3 F) := by
  have hdet : GeneralLinearGroup.det M = μ ^ 3 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_pow_eq_pow_val]
  have hscal : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) μ⁻¹) = (μ⁻¹) ^ 3 := by
    ext
    simp [GeneralLinearGroup.scalar]
  set B : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * M with hB
  have hdetB : GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, hscal, hdet, ← mul_pow, inv_mul_cancel, one_pow]
  have hBmem : (B : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    have := congrArg (fun x : Fˣ => (x : F)) hdetB
    simpa using this
  let g : SpecialLinearGroup (Fin 3) F := ⟨(B : Matrix (Fin 3) (Fin 3) F), hBmem⟩
  refine ⟨proj 3 F g, ?_⟩
  rw [← conjAut_toGL]
  have hg : SpecialLinearGroup.toGL g = B := by
    ext1
    rfl
  rw [hg, hB, map_mul, conjAut_scalar, one_mul]

theorem conjAut_three_inner_of_pow_char {p : ℕ} [Fact p.Prime] [CharP F p] (A : GL (Fin 3) F)
    (h : conjAut 3 F A ^ p = 1) : conjAut 3 F A ∈ innSub (projectiveSL 3 F) := by
  have h2 : conjAut 3 F (A ^ p) * fieldAut 3 F 1 = 1 := by
    rw [map_pow, map_one, mul_one]
    exact h
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h2
  have hdet : GeneralLinearGroup.det A ^ p = c ^ 3 := by
    rw [← map_pow, ← hc]
    ext
    simp [GeneralLinearGroup.scalar]
  have hexp : ExpChar F p := ExpChar.prime Fact.out
  have hfr : Function.Injective (frobenius F p) := frobenius_inj F p
  have hfs : Function.Surjective (frobenius F p) := Finite.surjective_of_injective hfr
  obtain ⟨γ, hγ⟩ := hfs (c : F)
  have hγ0 : γ ≠ 0 := by
    intro h0
    rw [h0, frobenius_def, zero_pow (Fact.out : p.Prime).ne_zero] at hγ
    exact c.ne_zero hγ.symm
  have hdF : ((GeneralLinearGroup.det A : Fˣ) : F) ^ p = (c : F) ^ 3 := by
    have := congrArg (fun x : Fˣ => (x : F)) hdet
    simpa using this
  have hcube : (GeneralLinearGroup.det A : Fˣ) = (Units.mk0 γ hγ0) ^ 3 := by
    apply Units.ext
    apply hfr
    rw [frobenius_def, frobenius_def, hdF, Units.val_pow_eq_pow_val, Units.val_mk0, ← hγ,
      frobenius_def, ← pow_mul, ← pow_mul, mul_comm]
  refine conjAut_three_inner_of_det_pow3 A (Units.mk0 γ hγ0) ?_
  have := congrArg (fun x : Fˣ => (x : F)) hcube
  simpa [Matrix.GeneralLinearGroup.val_det_apply] using this

theorem outerFalse_l3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) : OuterFalse p (projectiveSL 3 F) := by
  intro α hα hαp _ hHH
  have : Fact p.Prime := ⟨hp⟩
  have hFp : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hα1 : α ≠ 1 := fun h => hα ⟨1, by simp [h]⟩
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hE : α ∈ semilinearAutGroup 3 F := by
    obtain ⟨A, σ0, hαeq⟩ := exists_semilinear_of_odd_pow hpodd hαp
    exact mem_semilinearAutGroup_iff.mpr ⟨A, σ0, hαeq⟩
  have hD : α ∉ linearAutGroup 3 F := by
    intro hD
    rw [linearAutGroup_three_eq_range] at hD
    obtain ⟨A', hA'⟩ := hD
    have hAp : conjAut 3 F A' ^ p = 1 := by rw [hA']; exact hαp
    have hin := conjAut_three_inner_of_pow_char A' hAp
    rw [hA'] at hin
    exact hα hin
  obtain ⟨hpf, σ, -, hαh, hfix⟩ := linear_prime_descent_char (ℓ := p) (K := F) (n := 3) hp hf
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
  have hfsig : ∀ l : Fˣ, fieldAut 3 F σ (l3Tor l) = l3Tor (Units.map (σ : F →* F) l) :=
    fieldAut_l3Tor σ
  let T : Subgroup (projectiveSL 3 F) := ((powMonoidHom r : Fˣ →* Fˣ).ker).map l3Tor
  have hT : IsPGroup r ↥T := by
    rintro ⟨_, l, hl, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hl' : l ^ r = 1 := hl
    show (l3Tor l) ^ r ^ 1 = 1
    rw [pow_one, ← map_pow, hl', map_one]
  have hfT : ∀ x ∈ T, fieldAut 3 F σ x ∈ T := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨Units.map (σ : F →* F) l, ?_, (hfsig l).symm⟩
    have hl' : l ^ r = 1 := hl
    show (Units.map (σ : F →* F) l) ^ r = 1
    rw [← map_pow, hl', map_one]
  have hcT : l3Tor c ∈ T := ⟨c, hcr, rfl⟩
  have hne : fieldAut 3 F σ (l3Tor c) ≠ l3Tor c := by
    rw [hfsig]
    intro h'
    apply hσc
    have := l3Tor_injective h'
    exact congrArg Units.val this
  exact false_of_torus_moved hαh hr hr2 hrp hT hfT hcT hne hHH

end Outer

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
