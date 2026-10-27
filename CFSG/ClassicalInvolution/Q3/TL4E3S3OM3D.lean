module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3C

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Q3.TL4.OrthQ8 QuadraticMap
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem mu_eq_one_of_swap [Finite K] (hK : Nat.card K = 3) (F : Frame Q) {g : V ≃ₗ[K] V}
    (hg : ∀ a ∈ commutator SL(2, K), g * F.La a = F.La a * g) {w₀ : SL(2, K)}
    (hw₀ : w₀ * w₀ = -1)
    (hconj : ∀ b ∈ commutator SL(2, K), g * F.swap.La b * g⁻¹ = F.swap.La (w₀ * b * w₀⁻¹))
    {μ c : K} (hμ : ∀ v, Q (g v) = μ * Q v) (hc : ∀ v, g (g v) = c • v) : μ = 1 ∧ c = -1 := by
  have h2 : (2 : K) ≠ 0 := OrthQ8.two_ne_zero' hK
  have hT : ∀ a ∈ commutator SL(2, K),
      (F.swap.La w₀)⁻¹ * g * F.La a = F.La a * ((F.swap.La w₀)⁻¹ * g) := by
    intro a ha
    have hcomm : Commute (F.swap.La w₀) (F.La a) := (Frame.La_comm_La_swap F a w₀).symm
    exact (Commute.mul_left (Commute.inv_left hcomm) (show Commute g (F.La a) from hg a ha)).eq
  have hT' : ∀ a ∈ commutator SL(2, K),
      (F.swap.La w₀)⁻¹ * g * F.swap.La a = F.swap.La a * ((F.swap.La w₀)⁻¹ * g) := by
    intro b hb
    have hgb : g * F.swap.La b = F.swap.La (w₀ * b * w₀⁻¹) * g :=
      mul_inv_eq_iff_eq_mul.mp (hconj b hb)
    calc (F.swap.La w₀)⁻¹ * g * F.swap.La b
          = (F.swap.La w₀)⁻¹ * (g * F.swap.La b) := by rw [mul_assoc]
      _ = (F.swap.La w₀)⁻¹ * (F.swap.La (w₀ * b * w₀⁻¹) * g) := by rw [hgb]
      _ = (F.swap.La w₀)⁻¹ * (F.swap.La w₀ * F.swap.La b * (F.swap.La w₀)⁻¹) * g := by
          simp only [map_mul, map_inv, mul_assoc]
      _ = F.swap.La b * ((F.swap.La w₀)⁻¹ * g) := by
          simp only [mul_assoc, inv_mul_cancel_left]
  obtain ⟨l, hl⟩ := exists_smul_of_commute_Q8_swap hK F hT hT'
  obtain ⟨u, hu_def⟩ : ∃ u : V, u = F.incl 1 := ⟨_, rfl⟩
  have hu : u ∈ F.span := by rw [hu_def]; exact ⟨1, rfl⟩
  have hQu : Q u = 1 := by rw [hu_def, F.Q_incl, Matrix.det_one]
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, QuadraticMap.map_zero] at hQu
    exact zero_ne_one hQu
  have hXiso : ∀ v, Q (F.swap.La w₀ v) = Q v :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (F.swap.La_mem_orthogonalGroup w₀)
  have hgX : ∀ v, g v = F.swap.La w₀ (((F.swap.La w₀)⁻¹ * g) v) := fun v => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel_left]
  have hTu : ((F.swap.La w₀)⁻¹ * g) u = l • u := hl u hu
  have hgu : g u = l • F.swap.La w₀ u := by
    rw [hgX u, hTu, map_smul]
  have hXu : F.swap.La w₀ u ∈ F.span :=
    Frame.map_mem_span h2 (Frame.La_swap_neg_one_comm F w₀).symm hu
  have hgXu : g (F.swap.La w₀ u) = l • F.swap.La w₀ (F.swap.La w₀ u) := by
    rw [hgX (F.swap.La w₀ u), hl _ hXu, map_smul]
  have hXX : F.swap.La w₀ (F.swap.La w₀ u) = -u := by
    have e : F.swap.La w₀ (F.swap.La w₀ u) = F.swap.La (w₀ * w₀) u := by
      rw [map_mul, LinearEquiv.mul_apply]
    rw [e, hw₀, Frame.La_swap_neg_one F]
    exact (Frame.mem_span_iff_inv F h2).mp hu
  have hggu : g (g u) = (l * l) • (-u) := by
    rw [hgu, map_smul, hgXu, smul_smul, hXX]
  have h1 : c • u = (l * l) • (-u) := (hc u).symm.trans hggu
  have hcu : (c + l * l) • u = 0 := by
    rw [add_smul, h1, smul_neg, neg_add_cancel]
  have hc' : c + l * l = 0 := (smul_eq_zero.mp hcu).resolve_right hu0
  have hc2 : c = -(l * l) := by linear_combination hc'
  have hQsmul : ∀ (a : K) (x : V), Q (a • x) = a * a * Q x := fun a x => by
    rw [map_smul_eq_sq]
    ring
  have hμl : μ = l * l := by
    have h3 := hμ u
    rw [hgu, hQsmul, hXiso u, hQu] at h3
    linear_combination -h3
  have hl0 : l ≠ 0 := by
    rintro rfl
    have h0 : g u = 0 := by rw [hgu, zero_smul]
    have hu' : u = 0 := g.injective (by simp [h0])
    exact hu0 hu'
  have hll : l * l = 1 := OrthQ8.mul_self_eq_one hK hl0
  refine ⟨hμl.trans hll, ?_⟩
  rw [hc2, hll]

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3
