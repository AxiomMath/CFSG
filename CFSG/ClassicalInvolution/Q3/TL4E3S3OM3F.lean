module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3B
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3E

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4.OrthQ8 QuadraticMap
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {S : Type} [Group S]

theorem exists_mulRight_pair [Finite K] (hK : Nat.card K = 3) {F F' : Frame Q}
    {g : V ≃ₗ[K] V} (hg : ∀ a ∈ commutator SL(2, K), g * F.La a = F.La a * g)
    {w₀ : SL(2, K)}
    (hconj : ∀ b ∈ commutator SL(2, K), g * F'.La b * g⁻¹ = F'.La (w₀ * b * w₀⁻¹)) :
    ∃ P R : Matrix (Fin 2) (Fin 2) K, (∀ Y, g (F.incl Y) = F.incl (Y * P)) ∧
      ∀ Y, g (F'.incl Y) = F'.incl ((w₀ : Matrix (Fin 2) (Fin 2) K) * (Y * R)) := by
  obtain ⟨P, hP⟩ := exists_mulRight_of_commute_Q8 hK F hg
  have hT : ∀ b ∈ commutator SL(2, K),
      (F'.La w₀)⁻¹ * g * F'.La b = F'.La b * ((F'.La w₀)⁻¹ * g) := by
    intro b hb
    have h := hconj b hb
    rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul] at h
    calc (F'.La w₀)⁻¹ * g * F'.La b = (F'.La w₀)⁻¹ * (g * F'.La b) := by rw [mul_assoc]
      _ = (F'.La w₀)⁻¹ * (F'.La w₀ * F'.La b * (F'.La w₀)⁻¹ * g) := by rw [h]
      _ = F'.La b * ((F'.La w₀)⁻¹ * g) := by group
  obtain ⟨R, hR⟩ := exists_mulRight_of_commute_Q8 hK F' hT
  refine ⟨P, R, hP, fun Y => ?_⟩
  have h1 : F'.La w₀ (((F'.La w₀)⁻¹ * g) (F'.incl Y)) = g (F'.incl Y) := by simp
  rw [← h1, hR, Frame.La_apply_incl]

theorem relations {F F' : Frame Q} {g : V ≃ₗ[K] V} {w₀ : SL(2, K)} (hw₀ : w₀ * w₀ = -1)
    {P R : Matrix (Fin 2) (Fin 2) K} (hP : ∀ Y, g (F.incl Y) = F.incl (Y * P))
    (hR : ∀ Y, g (F'.incl Y) = F'.incl ((w₀ : Matrix (Fin 2) (Fin 2) K) * (Y * R)))
    {μ c : K} (hμ : ∀ v, Q (g v) = μ * Q v) (hc : ∀ v, g (g v) = c • v) :
    P * P = c • (1 : Matrix (Fin 2) (Fin 2) K) ∧
      R * R = (-c) • (1 : Matrix (Fin 2) (Fin 2) K) ∧ P.det = μ ∧ R.det = μ := by
  have hw : (w₀ : Matrix (Fin 2) (Fin 2) K) * (w₀ : Matrix (Fin 2) (Fin 2) K) = -1 := by
    have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) hw₀
    simpa using this
  have hdet : (w₀ : Matrix (Fin 2) (Fin 2) K).det = 1 := w₀.2
  have hP1 : g (F.incl 1) = F.incl P := by rw [hP, one_mul]
  have hR1 : g (F'.incl 1) = F'.incl ((w₀ : Matrix (Fin 2) (Fin 2) K) * R) := by
    rw [hR, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine F.incl_injective ?_
    have h1 := hc (F.incl 1)
    rw [hP1, hP] at h1
    rw [h1, map_smul]
  · have hmat : -(R * R) = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
      refine F'.incl_injective ?_
      have h1 := hc (F'.incl 1)
      rw [hR1, hR] at h1
      have e : (w₀ : Matrix (Fin 2) (Fin 2) K) *
          ((w₀ : Matrix (Fin 2) (Fin 2) K) * R * R) =
          ((w₀ : Matrix (Fin 2) (Fin 2) K) * (w₀ : Matrix (Fin 2) (Fin 2) K)) * (R * R) := by
        simp only [Matrix.mul_assoc]
      rw [e, hw, neg_mul, one_mul] at h1
      rw [h1, map_smul]
    rw [neg_smul, ← hmat, neg_neg]
  · have h1 := hμ (F.incl 1)
    rw [hP1, F.Q_incl, F.Q_incl, Matrix.det_one, mul_one] at h1
    exact h1
  · have h1 := hμ (F'.incl 1)
    rw [hR1, F'.Q_incl, F'.Q_incl, Matrix.det_one, mul_one, Matrix.det_mul, hdet, one_mul] at h1
    exact h1

theorem matrix_cases [Finite K] (hK : Nat.card K = 3) {P R : Matrix (Fin 2) (Fin 2) K} {μ c : K}
    (hc : c ≠ 0) (hP : P * P = c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hR : R * R = (-c) • (1 : Matrix (Fin 2) (Fin 2) K)) (hPd : P.det = μ) (hRd : R.det = μ) :
    (c = 1 ∧ (P = 1 ∨ P = -1)) ∨ (c = -1 ∧ (R = 1 ∨ R = -1)) := by
  rcases mul_self_eq_one_iff.mp (OrthQ8.mul_self_eq_one hK hc) with h1 | h1
  · left
    subst h1
    refine ⟨rfl, ?_⟩
    have hR' : R * R = -1 := by rw [hR, neg_smul, one_smul]
    have hRdet : R.det = 1 := det_eq_one_of_mul_self_eq_neg_one hK hR'
    have hP' : P * P = 1 := by rw [hP, one_smul]
    exact eq_one_or_neg_one_of_det_eq_one hK (hPd.trans (hRd.symm.trans hRdet)) hP'
  · right
    subst h1
    refine ⟨rfl, ?_⟩
    have hP' : P * P = -1 := by rw [hP, neg_smul, one_smul]
    have hPdet : P.det = 1 := det_eq_one_of_mul_self_eq_neg_one hK hP'
    have hR' : R * R = 1 := by rw [hR, neg_neg, one_smul]
    exact eq_one_or_neg_one_of_det_eq_one hK (hRd.trans (hPd.symm.trans hPdet)) hR'

theorem false_of_neg_frame [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 7 ≤ Module.finrank K V)
    {θ : ↥(orthDerived Q) →* S} (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {F F' : Frame Q} {g : V ≃ₗ[K] V} {x : MulAut S} (hx : InducedBy θ g x)
    (hF' : ∀ v, F'.La (-1) v = -F.La (-1) v)
    (hg : ∀ a ∈ commutator SL(2, K), g * F.La a = F.La a * g) {w₀ : SL(2, K)}
    (hw₀ : w₀ * w₀ = -1)
    (hconj : ∀ b ∈ commutator SL(2, K), g * F'.La b * g⁻¹ = F'.La (w₀ * b * w₀⁻¹))
    {μ c : K} (hμ : ∀ v, Q (g v) = μ * Q v) (hc : ∀ v, g (g v) = c • v)
    (hnb : ∀ C ∈ CoreAssembly.conjClass (frameMember θ F), (∀ c ∈ C, x c = c) →
      C ≠ frameMember θ F → ¬ C ≤ Subgroup.normalizer ((frameMember θ F : Subgroup S) : Set S)) :
    False := by
  have h2 : (2 : K) ≠ 0 := OrthQ8.two_ne_zero' hK
  have hgL : g * F.La (-1) = F.La (-1) * g := hg (-1) (neg_one_mem_commutator hK)
  have hc0 : c ≠ 0 := by
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro h0
    have h1 := hc v
    rw [h0, zero_smul] at h1
    have h3 : g v = 0 := g.injective (by rw [h1, map_zero])
    exact hv (g.injective (by rw [h3, map_zero]))
  obtain ⟨P, R, hP, hR⟩ := exists_mulRight_pair hK hg hconj
  obtain ⟨hPP, hRR, hPd, hRd⟩ := relations hw₀ hP hR hμ hc
  have hperp : ∀ v ∈ F.perp, g v ∈ F.perp := fun v hv => Frame.map_mem_perp h2 hgL hv
  have hspan : ∀ v ∈ F.span, g v ∈ F.span := fun v hv => Frame.map_mem_span h2 hgL hv
  have caseA : ∀ a : SL(2, K),
      (∀ Y, g (F.incl Y) = F.incl ((a : Matrix (Fin 2) (Fin 2) K) * Y)) → False := by
    intro a ha
    have hcomm : ∀ b : SL(2, K), g * F.swap.La b = F.swap.La b * g :=
      commute_swap_La_of_eqOn_La F a hperp (by
        rintro v ⟨Y, rfl⟩
        rw [Frame.La_apply_incl]
        exact ha Y)
    exact false_of_fixed_member hK hQ hn hx (G := F.swap) (fun b _ => hcomm b)
      (OrthQ8.frameMember_swap_ne hK hQ (by omega) θ hker F)
      (fun a _ b _ => Frame.La_comm_La_swap F a b) hnb
  have caseB : ∀ a : SL(2, K),
      (∀ Y, g (F'.incl Y) = F'.incl ((a : Matrix (Fin 2) (Fin 2) K) * Y)) → False := by
    intro a ha
    have hperp' : ∀ v ∈ F'.perp, g v ∈ F'.perp := fun v hv => by
      rw [perp_eq_span_of_neg h2 hF'] at hv ⊢
      exact hspan v hv
    have hcomm : ∀ b : SL(2, K), g * F'.swap.La b = F'.swap.La b * g :=
      commute_swap_La_of_eqOn_La F' a hperp' (by
        rintro v ⟨Y, rfl⟩
        rw [Frame.La_apply_incl]
        exact ha Y)
    exact false_of_fixed_frame_perp hK hQ hn hker hx (G := F'.swap)
      ((Frame.span_eq_swap_span F').trans (span_eq_perp_of_neg h2 hF')).le
      (fun b _ => hcomm b) hnb
  rcases matrix_cases hK hc0 hPP hRR hPd hRd with ⟨-, hP1 | hP1⟩ | ⟨-, hR1 | hR1⟩
  · exact caseA 1 fun Y => by
      rw [hP Y, hP1, Matrix.mul_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  · exact caseA (-1) fun Y => by
      rw [hP Y, hP1]
      simp
  · exact caseB w₀ fun Y => by
      rw [hR Y, hR1, Matrix.mul_one]
  · exact caseB (-w₀) fun Y => by
      rw [hR Y, hR1]
      simp

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3
