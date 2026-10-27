module

public import CFSG.LieType.SeitzGeneration.OmegaF2.Basic
public import CFSG.LieType.SeitzGeneration.OmegaF2.TransitA1

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.LieType.SeitzGeneration.RootPairOrth

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {k : Subfield K}
  {Q₀ : QuadraticForm k (Fin d → k)} (S : HypCoord Q)

theorem pairDet_dual_eq_zero [CharP K 2] {c₁ c₂ : Fin d → K}
    (h1 : ∀ a b : Fin d, a ∈ S.hyp → b ∈ S.hyp → b ≠ S.star a →
      pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single b 1) = 0)
    (h2 : ∀ a j : Fin d, a ∈ S.hyp → j ∈ S.hyp → j ≠ a → j ≠ S.star a →
      pairDet Q c₁ c₂ ((Pi.single a 1 : Fin d → K) + Pi.single (S.star j) 1)
        (Pi.single j 1 - Pi.single (S.star a) 1) = 0)
    {a : Fin d} (ha : a ∈ S.hyp) :
    pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single (S.star a) 1) = 0 := by
  obtain ⟨j, -, hj, -, hja, hjs, -, -, -, -⟩ := S.exists_three_T ha
  have has := S.star_mem a ha
  have hjst := S.star_mem j hj
  have hne1 : S.star j ≠ S.star (S.star a) := by
    rw [S.star_star a ha]
    exact fun h => hjs (by rw [← S.star_star j hj, h])
  have hne2 : S.star j ≠ S.star a := fun h => hja (S.star_injective hj ha h)
  have hne3 : j ≠ S.star (S.star a) := by
    rw [S.star_star a ha]
    exact hja
  have hAJ : pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single j 1) = 0 := h1 a j ha hj hjs
  have hA'J' : pairDet Q c₁ c₂ (Pi.single (S.star a) 1) (Pi.single (S.star j) 1) = 0 :=
    h1 (S.star a) (S.star j) has hjst hne1
  have hAJ' : pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single (S.star j) 1) = 0 :=
    h1 a (S.star j) ha hjst hne2
  have hA'J : pairDet Q c₁ c₂ (Pi.single (S.star a) 1) (Pi.single j 1) = 0 :=
    h1 (S.star a) j has hj hne3
  have e2 := h2 a j ha hj hja hjs
  have hexp : pairDet Q c₁ c₂ ((Pi.single a 1 : Fin d → K) + Pi.single (S.star j) 1)
      (Pi.single j 1 - Pi.single (S.star a) 1) =
      pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single j 1) -
        pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single (S.star a) 1) -
        pairDet Q c₁ c₂ (Pi.single j 1) (Pi.single (S.star j) 1) +
        pairDet Q c₁ c₂ (Pi.single (S.star a) 1) (Pi.single (S.star j) 1) := by
    unfold pairDet
    simp only [polar_add_left, polar_sub_left]
    ring
  have hpl : pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single (S.star a) 1) *
      pairDet Q c₁ c₂ (Pi.single j 1) (Pi.single (S.star j) 1) =
      pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single j 1) *
        pairDet Q c₁ c₂ (Pi.single (S.star a) 1) (Pi.single (S.star j) 1) -
      pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single (S.star j) 1) *
        pairDet Q c₁ c₂ (Pi.single (S.star a) 1) (Pi.single j 1) := by
    unfold pairDet
    ring
  have hsum : pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single (S.star a) 1) +
      pairDet Q c₁ c₂ (Pi.single j 1) (Pi.single (S.star j) 1) = 0 := by
    linear_combination hexp - e2 + hAJ + hA'J'
  have hpq : pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single (S.star a) 1) *
      pairDet Q c₁ c₂ (Pi.single j 1) (Pi.single (S.star j) 1) = 0 := by
    simp [hpl, hAJ, hA'J', hAJ', hA'J]
  have hsq : pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single (S.star a) 1) *
      pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single (S.star a) 1) = 0 := by
    linear_combination (pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single (S.star a) 1)) * hsum - hpq
  exact mul_self_eq_zero.mp hsq

theorem exists_rational_plane_pairDet_ne [CharP K 2] (hext : IsExtension k Q₀ Q)
    (hnd : (polarBilin Q).Nondegenerate) (htail : TailAnisotropic S) {c₁ c₂ : Fin d → K}
    (hc₁ : Q c₁ = 0) (hc₂ : Q c₂ = 0) (hc₁₂ : polar Q c₁ c₂ = 0)
    (hind : LinearIndependent K ![c₁, c₂]) :
    ∃ x y : Fin d → K, IsRat k x ∧ IsRat k y ∧ Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 0 ∧
      pairDet Q c₁ c₂ x y ≠ 0 := by
  classical
  by_contra hcon
  have H : ∀ x y : Fin d → K, IsRat k x → IsRat k y → Q x = 0 → Q y = 0 → polar Q x y = 0 →
      pairDet Q c₁ c₂ x y = 0 := by
    intro x y hx hy hQx hQy hxy
    by_contra hne
    exact hcon ⟨x, y, hx, hy, hQx, hQy, hxy, hne⟩
  have hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k := by
    intro a
    have h := hext (Pi.single a 1 : Fin d → k)
    rw [vecIncl_single] at h
    rw [h]
    exact (Q₀ (Pi.single a 1 : Fin d → k)).2
  have hB : ∀ x y : Fin d → K, IsBasicT S x y → pairDet Q c₁ c₂ x y = 0 := fun x y h =>
    H x y (h.isRat k hQk).1 (h.isRat k hQk).2 h.isTS.1 h.isTS.2.1 h.isTS.2.2
  have hHH : ∀ a b : Fin d, a ∈ S.hyp → b ∈ S.hyp →
      pairDet Q c₁ c₂ (Pi.single a 1) (Pi.single b 1) = 0 := by
    intro a b ha hb
    by_cases hbs : b = S.star a
    · subst hbs
      exact pairDet_dual_eq_zero S
        (fun a b ha hb hbs => hB _ _ (IsBasicT.single ha hb hbs))
        (fun a j ha hj hja hjs => hB _ _ (IsBasicT.plane ha hj hja hjs)) ha
    · exact hB _ _ (IsBasicT.single ha hb hbs)
  by_cases hall : ∀ a ∈ S.hyp, c₁ (S.star a) = 0 ∧ c₂ (S.star a) = 0
  · have hc1 : c₁ = 0 := htail c₁ (fun a ha => by
      have h := (hall (S.star a) (S.star_mem a ha)).1
      rwa [S.star_star a ha] at h) hc₁
    have h0 := hind.ne_zero 0
    simp [hc1] at h0
  · obtain ⟨a0, ha0, hne⟩ : ∃ a0, a0 ∈ S.hyp ∧
        ¬ (c₁ (S.star a0) = 0 ∧ c₂ (S.star a0) = 0) := by
      obtain ⟨a0, h⟩ := not_forall.mp hall
      exact ⟨a0, not_imp.mp h⟩
    obtain ⟨e, he_def⟩ : ∃ e : Fin d → K,
        e = c₁ (S.star a0) • c₂ - c₂ (S.star a0) • c₁ := ⟨_, rfl⟩
    have hemne : e ≠ 0 := by
      intro he0
      have hlin := LinearIndependent.pair_iff.mp hind (-(c₂ (S.star a0))) (c₁ (S.star a0))
        (by
          have hh : (-(c₂ (S.star a0))) • c₁ + c₁ (S.star a0) • c₂ = e := by
            rw [he_def]; module
          rw [hh, he0])
      exact hne ⟨hlin.2, neg_eq_zero.mp hlin.1⟩
    have hall_r : ∀ r : Fin d, polar Q (Pi.single r 1 : Fin d → K) e = 0 := by
      intro r
      have hval : polar Q (Pi.single r 1 : Fin d → K) e =
          pairDet Q c₁ c₂ (Pi.single a0 1) (Pi.single r 1) := by
        unfold pairDet
        rw [he_def]
        simp only [polar_sub_right, polar_smul_right, smul_eq_mul, S.polar_single a0 ha0]
      rw [hval]
      by_cases hr : r ∈ S.hyp
      · exact hHH a0 r ha0 hr
      · obtain ⟨j, -, hj, -, hja, hjs, -, -, -, -⟩ := S.exists_three_T ha0
        have ht := hB _ _ (IsBasicT.tail1 ha0 hj hja hjs hr)
        have hexp2 : pairDet Q c₁ c₂ (Pi.single a0 1)
            ((Pi.single j 1 : Fin d → K) + Pi.single r 1 -
              Q (Pi.single r 1) • Pi.single (S.star j) 1) =
            pairDet Q c₁ c₂ (Pi.single a0 1) (Pi.single j 1) +
              pairDet Q c₁ c₂ (Pi.single a0 1) (Pi.single r 1) -
              Q (Pi.single r 1) * pairDet Q c₁ c₂ (Pi.single a0 1) (Pi.single (S.star j) 1) := by
          unfold pairDet
          simp only [polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul]
          ring
        rw [hexp2, hHH a0 j ha0 hj, hHH a0 (S.star j) ha0 (S.star_mem j hj)] at ht
        linear_combination ht
    have he : e = 0 := hnd.2 e (fun n => by
      rw [polarBilin_apply_apply, polar_expand_left]
      exact Finset.sum_eq_zero fun r _ => by rw [hall_r r, mul_zero])
    exact hemne he

end CFSG.LieType.SeitzGeneration.OmegaF2
