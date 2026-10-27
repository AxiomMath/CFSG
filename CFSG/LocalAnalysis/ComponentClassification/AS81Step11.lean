module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Basic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCriterion

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS76b

section Elements

variable {G : Type} [Group G] [Finite G]

theorem le_sup_of_le_sup_centralizer {A R T : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hT : IsElemAbelian 2 T)
    (hTR : T ≤ centralizer (R : Set G)) (hTAK : T ≤ A ⊔ centralizer (A : Set G)) :
    T ≤ A ⊔ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKA : centralizer (A : Set G) ≤ normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer _
  intro x hx
  have hxKA : x ∈ ((centralizer (A : Set G) ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hTAK hx
  rw [coe_mul_of_left_le_normalizer_right _ _ hKA, Set.mem_mul] at hxKA
  obtain ⟨k, hk, a, ha, rfl⟩ := hxKA
  have hka : k * a = a * k := (mem_centralizer_iff.mp hk a ha).symm
  have haR : ∀ r ∈ R, a * r = r * a := fun r hr =>
    (mem_centralizer_iff.mp (hR.le hr) a ha)
  have hkR : ∀ r ∈ R, k * r = r * k := by
    intro r hr
    have h1 := mem_centralizer_iff.mp (hTR hx) r hr
    have h2 := haR r hr
    calc k * r = k * a * a⁻¹ * r := by group
      _ = k * a * (a⁻¹ * r) := by group
      _ = k * a * (r * a⁻¹) := by
          rw [show a⁻¹ * r = r * a⁻¹ by
            calc a⁻¹ * r = a⁻¹ * (r * a) * a⁻¹ := by group
              _ = a⁻¹ * (a * r) * a⁻¹ := by rw [h2]
              _ = r * a⁻¹ := by group]
      _ = r * (k * a) * a⁻¹ := by rw [← mul_assoc, ← h1]
      _ = r * k := by group
  have hx2 : (k * a) * (k * a) = 1 := by
    have := hT.2 (k * a) hx
    rwa [sq] at this
  have hk2 : k ^ 2 ∈ A := by
    have : k ^ 2 = (a ^ 2)⁻¹ := by
      rw [sq, sq, eq_inv_iff_mul_eq_one]
      calc k * k * (a * a) = k * (k * a) * a := by group
        _ = k * (a * k) * a := by rw [hka]
        _ = (k * a) * (k * a) := by group
        _ = 1 := hx2
    rw [this]
    exact A.inv_mem (A.pow_mem ha 2)
  obtain ⟨y, hy, hy2, z, hz, hkyz⟩ := exists_two_mul_mem_zpowers_sq k
  have hyK : y ∈ centralizer (A : Set G) := (zpowers_le.mpr hk) hy
  have hyR : ∀ r ∈ R, y * r = r * y := by
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hy
    intro r hr
    rw [← hj]
    exact (Commute.zpow_left (hkR r hr) j).eq
  have hRC : R ≤ centralizer ((zpowers y : Subgroup G) : Set G) := by
    intro r hr
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hw
    exact (Commute.zpow_left (hyR r hr) j).eq
  have hRN : R ≤ normalizer ((zpowers y : Subgroup G) : Set G) :=
    hRC.trans (Subgroup.centralizer_le_normalizer _)
  have hsup : R ⊔ zpowers y = R :=
    hR.eq_of_le le_sup_left (sup_le hR.le (zpowers_le.mpr hyK))
      (hR.isPGroup.to_sup_of_normal_right' hy2 hRN)
  have hyR' : y ∈ R := hsup ▸ mem_sup_right (mem_zpowers y)
  have hzA : z ∈ A := (zpowers_le.mpr hk2) hz
  rw [hkyz, mul_assoc]
  exact mul_mem (mem_sup_right hyR') (mem_sup_left (A.mul_mem hzA ha))

end Elements

section Conjugate

variable {G : Type} [Group G] [Finite G]

theorem rightConjugate_le_normalizer {A R : Subgroup G} (hA : standardComponentIsStandard A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hRe : IsElemAbelian 2 R) (hR1 : R ≠ ⊥)
    {g : G} (hgc : rightConjugate R g ≤ centralizer (R : Set G)) :
    rightConjugate R g ≤ normalizer (A : Set G) := by
  obtain ⟨r, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
  intro x hx
  rw [← normalizer_centralizer_eq hA]
  refine RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded
    (tightlyEmbedded_centralizer hA) (hR.le r.2) (fun h => hr1 (Subtype.ext h))
    (hRe.2 r r.2) ?_
  exact (mem_centralizer_iff.mp (hgc hx) r r.2).symm

end Conjugate

theorem step11_of
    (h32 : Lemma32) (h33 : Lemma33Three) : Step11 := by
  intro G _ _ A hB R hR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := hB.hyp31
  have hRe : IsElemAbelian 2 R := h32 G A hA R hR
  have hNK := normalizer_centralizer_eq hA.standard
  refine ⟨hRe, ?_, fun g hg hgc => ?_⟩
  ·
    obtain ⟨g, hg, R', T, hR', hT, -, -, hcomm, -, -⟩ :=
      section3Config_of h32 h33 RankTwoFoundation.asc75Theorem4 asc08Lemma34 G A hA
    obtain ⟨c, hcK, hc⟩ := hR.exists_mem_conj hR'
    have hRg := AschbacherTheorem3.isSylowOf_rightConjugate hR g
    obtain ⟨k, hkK, hk⟩ := hRg.exists_mem_conj hT
    refine ⟨g * k⁻¹ * c, fun hmem => hg ?_, fun x hx => ?_⟩
    ·
      have hcN : c ∈ normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hcK
      have h1 : g * k⁻¹ ∈ normalizer (A : Set G) := by
        have := (normalizer (A : Set G)).mul_mem hmem ((normalizer (A : Set G)).inv_mem hcN)
        simpa [mul_assoc] using this
      have hkN : g * k * g⁻¹ ∈ normalizer (A : Set G) :=
        Subgroup.centralizer_le_normalizer _ ((mem_rightConjugate_iff _ _ _).mp hkK)
      have := (normalizer (A : Set G)).mul_mem hkN h1
      simpa [mul_assoc] using this
    ·
      rw [mem_centralizer_iff]
      intro r hr
      rw [mem_rightConjugate_iff] at hx
      have hxT : c * x * c⁻¹ ∈ T := by
        rw [hk, mem_rightConjugate_iff]
        convert hx using 1
        group
      have hrR' : c * r * c⁻¹ ∈ R' := by
        rw [hc, show c⁻¹ * (c * r * c⁻¹) * c = r by group]
        exact hr
      have hcm : (c * x * c⁻¹) * (c * r * c⁻¹) = (c * r * c⁻¹) * (c * x * c⁻¹) := by
        have := commutator_eq_bot_iff_le_centralizer.mp hcomm
        exact (mem_centralizer_iff.mp (this hxT) _ hrR').symm
      have : c * (x * r) * c⁻¹ = c * (r * x) * c⁻¹ := by
        calc c * (x * r) * c⁻¹ = (c * x * c⁻¹) * (c * r * c⁻¹) := by group
          _ = (c * r * c⁻¹) * (c * x * c⁻¹) := hcm
          _ = c * (r * x) * c⁻¹ := by group
      have h2 := congrArg (fun w => c⁻¹ * w * c) this
      have h3 : x * r = r * x := by simpa [mul_assoc] using h2
      exact h3.symm
  ·
    have hR1 : R ≠ ⊥ := isSylowOf_ne_bot_of_even hR (tightlyEmbedded_centralizer hA.standard).1
    have hRgN := rightConjugate_le_normalizer hA.standard hR hRe hR1 hgc
    have hRg := AschbacherTheorem3.isSylowOf_rightConjugate hR g
    have hRgT : IsSylowOf 2 (rightConjugate R g)
        (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)) :=
      hRg.of_le (le_inf hRg.le hRgN) inf_le_left
    have hRg1 : rightConjugate R g ≠ ⊥ := by
      intro h
      apply hR1
      rw [← Subgroup.card_eq_one, ← rightConjugate_card R g, h, Subgroup.card_bot]
    have hAK := lemma33Two_of h32 RankTwoFoundation.asc75Theorem4 asc08Lemma34 G A hA R hR g hg
      (rightConjugate R g) hRgT hRg1 (hgc.trans (Subgroup.centralizer_le_normalizer _)) hRg
    exact le_sup_of_le_sup_centralizer hR (isElemAbelian_rightConjugate hRe g) hgc hAK

end CFSG.ComponentClassification.AS81
