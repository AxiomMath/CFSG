module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpRadical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CatalogueBAlternatingIsometry CatalogueBSymplecticB
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace SpChain

variable {r : ℕ} {K : Type} [Field K]

theorem pairedSympForm_spMat (g : StatedSp r K) (x y : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (spMat g *ᵥ x) (spMat g *ᵥ y) = pairedSympForm K r x y := by
  rw [pairedSympForm_mulVec_of_formJ (μ := 1)
    (by rw [one_smul]; exact SymplecticTorusWeyl.mem_statedSp_iff.mp g.2), one_mul]

@[expose] def displacement (s : StatedSp r K) : Submodule K (Fin r ⊕ Fin r → K) :=
  LinearMap.range (spMat s - 1).mulVecLin

theorem sub_one_mulVec (s : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    (spMat s - 1) *ᵥ v = spMat s *ᵥ v - v := by
  rw [sub_mulVec, one_mulVec]

theorem mem_displacement {s : StatedSp r K} {w : Fin r ⊕ Fin r → K} :
    w ∈ displacement s ↔ ∃ v, spMat s *ᵥ v - v = w := by
  simp only [displacement, LinearMap.mem_range, mulVecLin_apply, sub_one_mulVec]

variable {s : StatedSp r K}

theorem pairedSympForm_spMat_left (hs : s * s = 1) (x y : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (spMat s *ᵥ x) y = pairedSympForm K r x (spMat s *ᵥ y) := by
  conv_lhs => rw [← show spMat s *ᵥ (spMat s *ᵥ y) = y by
    rw [← spMat_mul_mulVec, hs]; exact one_mulVec y]
  exact pairedSympForm_spMat s x (spMat s *ᵥ y)

theorem pairedSympForm_displacement (hs : s * s = 1) (x y : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (spMat s *ᵥ x - x) y = pairedSympForm K r x (spMat s *ᵥ y - y) := by
  rw [map_sub, LinearMap.sub_apply, map_sub, pairedSympForm_spMat_left hs]

theorem displacement_eq_zero_of_mem_orthogonal (hs : s * s = 1) {l : Fin r ⊕ Fin r → K}
    (hl : l ∈ (pairedSympForm K r).orthogonal (displacement s)) :
    spMat s *ᵥ l - l = 0 := by
  refine SymplecticFlag.pairedSympForm_nondegenerate.2 _ fun x => ?_
  rw [← pairedSympForm_displacement hs]
  exact LinearMap.BilinForm.mem_orthogonal_iff.mp hl _ (mem_displacement.mpr ⟨x, rfl⟩)

theorem commute_of_mem_flagKernel (hs : s * s = 1) {h : StatedSp r K}
    (hh : h ∈ flagKernel (displacement s) ((pairedSympForm K r).orthogonal (displacement s))) :
    h * s = s * h := by
  obtain ⟨hh1, -, hh3⟩ := hh
  refine statedSp_ext fun v => ?_
  rw [spMat_mul_mulVec, spMat_mul_mulVec]
  have h1 : spMat h *ᵥ (spMat s *ᵥ v - v) = spMat s *ᵥ v - v :=
    hh1 _ (mem_displacement.mpr ⟨v, rfl⟩)
  have h2 := displacement_eq_zero_of_mem_orthogonal hs (hh3 v)
  rw [mulVec_sub] at h1
  have h3 : spMat s *ᵥ (spMat h *ᵥ v - v) = spMat h *ᵥ v - v := by
    rw [← sub_eq_zero]
    exact h2
  rw [mulVec_sub] at h3
  linear_combination (norm := module) h1 - h3

variable [CharP K 2]

theorem displacement_sq (hs : s * s = 1) (y : Fin r ⊕ Fin r → K) :
    spMat s *ᵥ (spMat s *ᵥ y - y) - (spMat s *ᵥ y - y) = 0 := by
  have hss : spMat s *ᵥ (spMat s *ᵥ y) = y := by
    rw [← spMat_mul_mulVec, hs]; exact one_mulVec y
  rw [mulVec_sub, hss]
  have h2 : y - spMat s *ᵥ y - (spMat s *ᵥ y - y) = (2 : K) • (y - spMat s *ᵥ y) := by module
  rw [h2, CharTwo.two_eq_zero, zero_smul]

theorem isTotallyIsotropic_displacement (hs : s * s = 1) :
    IsTotallyIsotropic (pairedSympForm K r) (displacement s) := by
  intro x hx y hy
  obtain ⟨u, rfl⟩ := mem_displacement.mp hx
  obtain ⟨v, rfl⟩ := mem_displacement.mp hy
  rw [pairedSympForm_displacement hs, displacement_sq hs, map_zero]

end SpChain

open SpChain

theorem even_symplectic_inner_involution_full_centralizer_odd_core {r f : ℕ} (hr : 2 ≤ r)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f)
    (H : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hIH : inner (StatedProj (StatedSp r K)) ≤ H) {t : MulAut (StatedProj (StatedSp r K))}
    (htI : t ∈ inner (StatedProj (StatedSp r K))) (ht : orderOf t = 2) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {t}) = ⊥ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  set E := spSemilinearAutGroup r K with hEdef
  have hιinj := spInner_injective (r := r) (K := K)
  rw [← range_spInner] at htI
  obtain ⟨s, rfl⟩ := htI
  have hsord : orderOf s = 2 := by rw [← orderOf_injective _ hιinj s, ht]
  have hs : s * s = 1 := by rw [← sq, ← hsord, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hsord
    exact absurd hsord (by norm_num)
  set W := displacement s with hWdef
  set L := (pairedSympForm K r).orthogonal W with hLdef
  set R := flagKernel W L with hRdef
  have hW0 : W ≠ ⊥ := by
    intro hbot
    refine hs1 (statedSp_ext fun v => ?_)
    have h1 : spMat s *ᵥ v - v ∈ W := mem_displacement.mpr ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at h1
    rw [h1]
    exact (one_mulVec v).symm
  have hWiso := isTotallyIsotropic_displacement hs
  obtain ⟨-, hRp, hnorm, hcentEq, hcentp⟩ :=
    even_symplectic_isotropic_radical_centralizer (by omega) hf hK W hW0 hWiso
  set N := R.map (spInner r K) with hNdef
  have hnormC : ∀ α ∈ E, α * spInner r K s = spInner r K s * α →
      α ∈ Subgroup.normalizer (N : Set (MulAut (StatedProj (StatedSp r K)))) := by
    intro α hαE hαt
    obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut hαE
    have hgs : g * fieldSp r K φ s = s * g := by
      have h1 : spInner r K g * fieldAut r K φ * spInner r K s *
          (spInner r K g * fieldAut r K φ)⁻¹ = spInner r K s := by
        rw [hαt, mul_inv_cancel_right]
      rw [conj_spInner] at h1
      have h2 := hιinj h1
      calc g * fieldSp r K φ s = g * fieldSp r K φ s * g⁻¹ * g := by group
        _ = s * g := by rw [h2]
    refine hnorm g φ fun w hw => ?_
    obtain ⟨v, rfl⟩ := mem_displacement.mp hw
    refine mem_displacement.mpr ⟨semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ v, ?_⟩
    have h1 := semilinearCoordMap_mulVec_of_mul_eq hgs v
    rw [← h1, ← map_sub, semilinearCoordMap_apply]
  have hcore₀ : CFSG.oddCore ↥(H ⊓ E ⊓ Subgroup.centralizer {spInner r K s}) = ⊥ := by
    refine oddCore_eq_bot_of_centralizer (N := N) ?_ ?_ ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hIH (spInner_mem_inner h),
        spInner_mem_spSemilinearAutGroup h⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← map_mul, ← map_mul, commute_of_mem_flagKernel hs hh]
    · intro c hc n hn
      obtain ⟨⟨-, hcE⟩, hct⟩ := Subgroup.mem_inf.mp hc
      have hct' := Subgroup.mem_centralizer_singleton_iff.mp hct
      exact (Subgroup.mem_normalizer_iff.mp (hnormC c hcE hct') n).mp hn
    · intro X hXN _ hodd
      exact eq_bot_of_isPGroup_two (hRp.map (spInner r K)) hXN hodd
    · intro c hc hcN
      obtain ⟨⟨-, hcE⟩, -⟩ := Subgroup.mem_inf.mp hc
      have hmem : c ∈ E ⊓ Subgroup.centralizer (N : Set (MulAut (StatedProj (StatedSp r K)))) :=
        Subgroup.mem_inf.mpr ⟨hcE, Subgroup.mem_centralizer_iff.mpr fun n hn => (hcN n hn).symm⟩
      obtain ⟨k, hk⟩ := hcentp ⟨c, hmem⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  · obtain rfl : r = 2 := by omega
    obtain ⟨-, -, hEn, hEi⟩ :=
      CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := K)
    exact oddCore_eq_bot_of_index_le_two hEi hcore₀
  · have hEtop : E = ⊤ := (automorphism_generation (K := K) hr3).1
    rw [hEtop, inf_top_eq] at hcore₀
    exact hcore₀

end CFSG.ComponentClassification.UnbalancedCatalog
