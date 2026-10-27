module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5FusionTwoEmbedded
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OrderTwoEmbedding
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedPointModelHull

public section

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace FusionTwo

open SectionSix Involution Fusion

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Group G] [Finite G] in
theorem exists_ne_ne (hr : 3 ≤ r) (i j : Fin r) : ∃ k : Fin r, k ≠ i ∧ k ≠ j := by
  by_contra h
  push Not at h
  have h0 := h ⟨0, by omega⟩
  have h1 := h ⟨1, by omega⟩
  have h2 := h ⟨2, by omega⟩
  simp only [ne_eq, Fin.ext_iff] at h0 h1 h2
  omega

theorem productUniqueContainment (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    (hr : r ≠ 2) {i : Fin r} {a : G} (haA : a ∈ aschbacherThm5Preimage D (Abar i))
    (ha2 : orderOf a = 2) :
    ProductUniqueContainment (Subgroup.normalizer (D : Set G)) a := by
  have hyp := hC.hyp
  have hr3 := three_le hC hr
  have hne1 : ∀ x : G, orderOf x = 2 → x ≠ 1 := fun x hx h => by
    rw [h, orderOf_one] at hx
    omega
  have haC := centralizer_le_of_mem_factor hC haA (two_power_of_orderOf ha2) (hne1 a ha2)
  have haH : a ∈ Subgroup.normalizer (D : Set G) :=
    haC (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  intro t ht hcomm hne g
  obtain ⟨g₀, hg₀t⟩ := ht
  have htdef : t = g₀⁻¹ * a * g₀ := hg₀t.symm
  subst htdef
  have hcomm' : a * (g₀⁻¹ * a * g₀) = (g₀⁻¹ * a * g₀) * a := hcomm
  have htH : g₀⁻¹ * a * g₀ ∈ Subgroup.normalizer (D : Set G) :=
    haC (Subgroup.mem_centralizer_singleton_iff.mpr hcomm'.symm)
  have hg₀ := mem_of_conj_mem hin hC hr ha2 haC htH
  have ht2 : orderOf (g₀⁻¹ * a * g₀) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g₀⁻¹) a
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, ha2]
  obtain ⟨j, hj⟩ := hyp.hperm g₀⁻¹ ((Subgroup.normalizer (D : Set G)).inv_mem hg₀) i
  have htA : g₀⁻¹ * a * g₀ ∈ aschbacherThm5Preimage D (Abar j) := by
    rw [← hj]
    exact ⟨a, haA, by simp⟩
  obtain ⟨k, hki, hkj⟩ := exists_ne_ne hr3 i j
  have hbc := centralizes_mul (preimage_le D (Abar k)) haH htH
    (cross_factor_centralizes D Abar hyp.hcomm k i hki a haA)
    (cross_factor_centralizes D Abar hyp.hcomm k j hkj _ htA)
  have hb2 : orderOf (a * (g₀⁻¹ * a * g₀)) = 2 := by
    apply orderOf_eq_prime
    · have hasq : a ^ 2 = 1 := by rw [← ha2, pow_orderOf_eq_one]
      have htsq : (g₀⁻¹ * a * g₀) ^ 2 = 1 := by rw [← ht2, pow_orderOf_eq_one]
      rw [Commute.mul_pow hcomm' 2, hasq, htsq, one_mul]
    · intro h
      apply hne
      have hinv : a⁻¹ = a := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two, ← ha2, pow_orderOf_eq_one]
      exact (eq_inv_of_mul_eq_one_right h).trans hinv
  have hbC := centralizer_le_of_centralizes hC k (two_power_of_orderOf hb2) (hne1 _ hb2) hbc
  have hbH : a * (g₀⁻¹ * a * g₀) ∈ Subgroup.normalizer (D : Set G) :=
    hbC (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  constructor
  · exact mem_of_conj_mem hin hC hr hb2 hbC
  · intro hg
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hbH) hg

end FusionTwo

open FusionTwo SectionSix Involution Fusion

theorem lemma_8_2_holds (hin : SectionSevenBase) :
    ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
      {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
      Counterexample G D r Abar → r = 2 := by
  intro G _ _ D r Abar hC
  by_contra hr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hC.hyp
  have hr3 := three_le hC hr
  obtain ⟨u, v, hu, hv, huv, hne, huC, hvC, huvC⟩ := exists_good_pair hC hr3
  have hodd : ∀ K : Subgroup G, K.Normal → Odd (Nat.card K) →
      K ≤ Subgroup.normalizer (D : Set G) :=
    fun K hK hKo => normal_odd_le hu hv huv hne huC hvC huvC hK hKo
  obtain ⟨i₀, -⟩ : ∃ i : Fin r, True := ⟨⟨0, by omega⟩, trivial⟩
  obtain ⟨a', ha'⟩ := exists_prime_orderOf_dvd_card'
    (G := aschbacherThm5Preimage D (Abar i₀)) 2
    (even_iff_two_dvd.mp (SectionSix.factor_even hyp i₀))
  set a : G := (a' : G) with ha
  have ha2 : orderOf a = 2 := by rw [ha, Subgroup.orderOf_coe, ha']
  have haA : a ∈ aschbacherThm5Preimage D (Abar i₀) := a'.2
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at ha2
    omega
  have haC := centralizer_le_of_mem_factor hC haA (two_power_of_orderOf ha2) ha1
  obtain ⟨h12, h23, -⟩ := hin.theorem_3_3 (Subgroup.normalizer (D : Set G)) a ha2 hC.proper
    (mem_rightConjugate_iff_of_ne_two hin hC hr ha2 haC)
  have h2 := h12 (productUniqueContainment hin hC hr haA ha2)
  have h3 := h23 h2
  obtain ⟨⟨S, haS, hzS⟩, -⟩ := h2
  have hSH : (S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
    intro s hs
    apply haC
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzS ⟨s, hs⟩)
  rcases h3 with hlow | ⟨-, -, -, -, -, hSE, -⟩
  ·
    refine false_of_isolated hC ha2 haC ?_ hu hv huv hne huC hvC huvC
    intro g hcomm
    by_contra hneq
    have hg2 : orderOf (g * a * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ha2]
    obtain ⟨hE, hcard, -⟩ :=
      CFSG.ProperTwoGeneratedCore.commuting_distinct_involutions_four_group ha2 hg2 hcomm.symm
        hneq
    have haL : a ∈ involutionPointHull a := Subgroup.subset_closure ⟨1, by
      change (1 : G)⁻¹ * a * 1 = a
      group⟩
    have hgaL : g * a * g⁻¹ ∈ involutionPointHull a := Subgroup.subset_closure ⟨g⁻¹, by
      change g⁻¹⁻¹ * a * g⁻¹ = g * a * g⁻¹
      group⟩
    have hEL : Subgroup.zpowers a ⊔ Subgroup.zpowers (g * a * g⁻¹) ≤ involutionPointHull a :=
      sup_le (Subgroup.zpowers_le.mpr haL) (Subgroup.zpowers_le.mpr hgaL)
    have h2le := FixedPointModel.two_le_twoRank_of_le hE (by rw [hcard]) hEL
    omega
  ·
    have hLn : (involutionPointHull a).Normal := by
      rw [involutionPointHull_eq_normalClosure_zpowers]
      infer_instance
    exact no_normal_strongly_embedded hC hodd S hSH hSE

end CFSG.ComponentClassification.AschbacherTheorem5
