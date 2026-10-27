module

public import CFSG.ClassicalInvolution.SmallCases.NDBE4SVert
public import CFSG.ClassicalInvolution.SmallCases.NDBE4SRes
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleFixed
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleMinus
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.RouteD.GapsOrthModel
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.NDB.ExoticModel

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77 CFSG.LieType.Universal.Spin CFSG.LieType.Universal
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.NDB.SpinVertex

variable {p : ℕ} [Fact p.Prime]

theorem orderOf_eq_two_of_isUniqueInvolution {X : Type*} [Group X] {R : Subgroup X} {x : X}
    (hx : IsUniqueInvolution R x) : orderOf x = 2 :=
  orderOf_eq_prime (by rw [sq]; exact hx.sq) hx.ne_one

theorem spin_vertex (hres : SpinOuterKleinAlpha p) (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    {t : StatedLieTag} {n : ℕ} (ht : SpinTag t n) (hadm : StatedLieAdmissible t n p e)
    {H : Type} [Group H] [Finite H] (ψ : (modelUniv t n p e Fact.out).K →* H)
    (hψ : ψ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K)
    {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    {x : (modelUniv t n p e Fact.out).K} (hx : IsUniqueInvolution R x) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ R, v * ψ r = ψ r * v) :
    (∀ y ∈ ψ.range, v * y = y * v) ∨ (∀ y ∈ ψ.range, v * ψ x * y = y * (v * ψ x)) ∨
      (alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩,
          toInducedAutOn ψ.range ⟨v, hv⟩} : Set ↥(inducedAutOn ψ.range))) = ⊥ ∧
        (Subgroup.centralizer ({v} : Set H)).comap ψ ⊔
          (Subgroup.centralizer ({v * ψ x} : Set H)).comap ψ = ⊤) := by
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have h5 : 5 ≤ Nat.card (GaloisField p e) := by rw [GaloisField.card p e he]; exact hq
  have h2 := ModelFacts.two_ne_zero_galoisField e hp2
  have hσ2 : ∀ y, MulAut.conj v (MulAut.conj v y) = y := fun y => by
    simp only [MulAut.conj_apply]
    rw [show v * (v * y * v⁻¹) * v⁻¹ = (v * v) * y * (v * v)⁻¹ by group, hv2]
    group
  have hσr : ∀ k, MulAut.conj v (ψ k) ∈ ψ.range := fun k =>
    (Subgroup.mem_normalizer_iff.mp hv (ψ k)).mp ⟨k, rfl⟩
  have hfixR : ∀ r ∈ R, MulAut.conj v (ψ r) = ψ r := fun r hr => by
    rw [MulAut.conj_apply, hvR r hr, mul_inv_cancel_right]
  have hfin : ∀ {R' : Subgroup (modelUniv t n p e Fact.out).K},
      (∀ r ∈ R', MulAut.conj v (ψ r) = ψ r) → ∀ r ∈ R', v * ψ r = ψ r * v := fun h r hr => by
    have h1 := h r hr
    rw [MulAut.conj_apply] at h1
    calc v * ψ r = v * ψ r * v⁻¹ * v := by group
      _ = ψ r * v := by rw [h1]
  have hxo := orderOf_eq_two_of_isUniqueInvolution hx
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hQuot := centralQuot_odd (p := p) (f := e) hp2 (le_refl 3) hq
    obtain ⟨i, fr, hRfr, hi⟩ := hQuot.map_mem R hR
    obtain ⟨R', hR', htw⟩ := oddTwinsExist hp2 hq hadm R hR
    have htwin := IsFundTwin.to_map _ hQuot.ker_le hQuot.perf hQuot.surj hR hR' htw
    rw [hRfr] at htwin
    have hdim : Module.finrank (GaloisField p e) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) = 7 :=
      finrank_odd p e 3
    have hR'fr := eq_swap_of_isFundTwin hodd
      (fun R₀ R₁ i₀ i₁ h₀ h₁ hc => commuting_same_involution hodd (by rw [hdim]; omega) h₀ h₁ hc)
      fr (hQuot.map_mem R' hR') htwin
    have hvR' := hfin (oddTwinFixed_spin hq hadm ψ hψ (MulAut.conj v) hσ2 hσr hR hR' htw hfixR)
    have hxθ : spinAction _ x = fr.La (-1) := by
      have h1 := invOf_eq hodd ⟨fr, hRfr, hi⟩ (hQuot.invOf hR ⟨hx.mem, hxo⟩)
      rw [h1, hi]
    have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField p e))) :=
      isPerfect_spinGroup_quadOdd h2 le_rfl
    obtain ⟨hgen, hcase⟩ := vertex hodd h5 (nondegenerate_polarBilin_quadOdd 3 _ h2)
      (range_spinAction_quadOdd h2 le_rfl) fr (by rw [hdim]) hψ
      (liftSim_quadOdd hp2 le_rfl (by omega) ψ hψ) hRfr hR'fr hx.mem hxθ hx.sq hv hv2 hvR hvR'
    rcases hcase with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, hgen⟩)
    · exact Or.inr (Or.inr ⟨hres .POmegaOdd 3 e (Or.inl ⟨rfl, rfl⟩) hp2 hq hadm H ψ hψ R hR x hx v
        hv hv2 hvR h, hgen⟩)
  · have hQuot := centralQuot_minus (p := p) (f := e) hp2 hq hadm
    obtain ⟨i, fr, hRfr, hi⟩ := hQuot.map_mem R hR
    obtain ⟨R', hR', htw⟩ := minusTwinsExist_four hp2 hq hadm R hR
    have htwin := IsFundTwin.to_map _ hQuot.ker_le hQuot.perf hQuot.surj hR hR' htw
    rw [hRfr] at htwin
    have h4 : 4 ≤ Nat.card (GaloisField p e) := by omega
    have hR'fr := eq_swap_of_isFundTwin hodd
      (fun R₀ R₁ i₀ i₁ h₀ h₁ hc =>
        quadMinus_four_same_involution hodd (minusCoeffs_irr p e) h4 h₀ h₁ hc)
      fr (hQuot.map_mem R' hR') htwin
    have hvR' := hfin (minusTwinFixed_spin hp2 hq hadm ψ hψ (MulAut.conj v) hσ2 hσr hR hR' htw
      hfixR)
    have hxθ : spinAction _ x = fr.La (-1) := by
      have h1 := invOf_eq hodd ⟨fr, hRfr, hi⟩ (hQuot.invOf hR ⟨hx.mem, hxo⟩)
      rw [h1, hi]
    have : Group.IsPerfect (spinGroup (quadMinus 4 (GaloisField p e) (minusCoeffs p e).1
        (minusCoeffs p e).2)) := isPerfect_spinGroup_quadMinus le_rfl (minusCoeffs_irr p e)
    have hdim : Module.finrank (GaloisField p e)
        (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p e) = 8 := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp
    obtain ⟨hgen, hcase⟩ := vertex hodd h5
      (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr p e))
      (range_spinAction_quadMinus le_rfl (minusCoeffs_irr p e)) fr (by rw [hdim]; omega) hψ
      (liftSim_quadMinus hp2 le_rfl (by omega) ψ hψ) hRfr hR'fr hx.mem hxθ hx.sq hv hv2 hvR hvR'
    rcases hcase with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, hgen⟩)
    · exact Or.inr (Or.inr ⟨hres .POmegaMinus 4 e (Or.inr ⟨rfl, rfl⟩) hp2 hq hadm H ψ hψ R hR x
        hx v hv hv2 hvR h, hgen⟩)

end CFSG.ClassicalInvolution.NDB.ExoticModel
