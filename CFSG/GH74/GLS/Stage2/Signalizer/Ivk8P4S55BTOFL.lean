module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOF
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.LinearDescent (higher_linear_prime_semilinear_field_descent)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (innSub)

section Outer

variable {F : Type} [Field F] [Finite F]

theorem outerFalseNS_l4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) : OuterFalseNS p (projectiveSL 4 F) := by
  intro α hα hαp hHH
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

theorem outerFalseNS_of_fl4d {p : ℕ} {Y : Type} [Group Y] (hp : p.Prime) (hp2 : p ≠ 2)
    (h : FL4d p Y) : OuterFalseNS p Y := by
  obtain ⟨f, hf, -, hlie⟩ := h
  obtain ⟨F, iF, fF, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hlie
  exact OuterFalseNS.of_mulEquiv e (outerFalseNS_l4 hp hp2 hf hcard)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
