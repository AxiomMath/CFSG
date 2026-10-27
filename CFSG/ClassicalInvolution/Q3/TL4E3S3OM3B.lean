module

public import CFSG.ClassicalInvolution.Q3.TL4OrthQ8

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4.OrthQ8 QuadraticMap
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {S : Type} [Group S]

theorem twin_cases [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 7 ≤ Module.finrank K V)
    (θ : ↥(orthDerived Q) →* S) (hθ : Function.Surjective θ)
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)) {A : Subgroup S} {r : S}
    (hd : QuatTwinDatum A r) {F : Frame Q} (hF : A = frameMember θ F) {q : S}
    (hq : q ∈ Subgroup.centralizer ({r} : Set S)) (hne : conjSub q A ≠ A) :
    conjSub q A = frameMember θ F.swap ∨
      ∃ F' : Frame Q, conjSub q A = frameMember θ F' ∧ ∀ v, F'.La (-1) v = -F.La (-1) v := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have h2 := two_ne_zero' hK
  obtain ⟨q', rfl⟩ := hθ q
  have hO := orthDerived_le q'.2
  set F' := F.map hO with hF'
  have hmem : frameMember θ F' = conjSub (θ q') A := by
    rw [hF', frameMember_map θ F hO q'.2, hF]
  have hrF : frameInv θ F = r := by
    have hu := isUniqueInvolution_frameMember hK (by omega) θ hker F
    rw [← hF] at hu
    rcases hd.inv.unique _ hu.mem hu.sq with h | h
    · exact absurd h hu.ne_one
    · exact h
  have hθinv : θ ⟨F'.La (-1), La_neg_one_mem_orthDerived F'⟩ =
      θ ⟨F.La (-1), La_neg_one_mem_orthDerived F⟩ := by
    have h1 : (⟨F'.La (-1), La_neg_one_mem_orthDerived F'⟩ : ↥(orthDerived Q)) =
        q' * ⟨F.La (-1), La_neg_one_mem_orthDerived F⟩ * q'⁻¹ :=
      Subtype.ext (Frame.map_La F hO (-1))
    rw [h1, map_mul, map_mul, map_inv]
    have h3 : θ ⟨F.La (-1), La_neg_one_mem_orthDerived F⟩ = r := hrF
    rw [h3]
    have := Subgroup.mem_centralizer_singleton_iff.mp hq
    rw [this, mul_inv_cancel_right]
  obtain ⟨l, hl, hlv⟩ := exists_smul_of_map_eq hQ hker hθinv.symm
  rcases mul_self_eq_one_iff.mp hl with hl1 | hl1
  ·
    have hLa : F'.La (-1) = F.La (-1) :=
      LinearEquiv.ext fun v => by have := hlv v; simp only at this; rw [this, hl1, one_smul]
    have hrange := Frame.La_range_eq_or_eq_swap h2 hLa
    have hQ8 : frameQ8 F' = frameQ8 F ∨ frameQ8 F' = frameQ8 F.swap := by
      rcases hrange with h | h
      · left
        rw [frameQ8_eq, frameQ8_eq, h]
      · right
        rw [frameQ8_eq, frameQ8_eq, h]
    rcases hQ8 with h | h
    · exfalso
      apply hne
      rw [← hmem, hF]
      unfold frameMember
      rw [h]
    · left
      rw [← hmem]
      unfold frameMember
      rw [h]
  ·
    right
    refine ⟨F', hmem.symm, fun v => ?_⟩
    have := hlv v
    simp only at this
    rw [this, hl1, neg_one_smul]

section Negated

variable {F F' : Frame Q}

theorem span_eq_perp_of_neg (h2 : (2 : K) ≠ 0) (h : ∀ v, F'.La (-1) v = -F.La (-1) v) :
    F'.span = F.perp := by
  ext v
  rw [F'.mem_span_iff_inv h2, F.mem_perp_iff_fix h2, h v, neg_inj]

theorem perp_eq_span_of_neg (h2 : (2 : K) ≠ 0) (h : ∀ v, F'.La (-1) v = -F.La (-1) v) :
    F'.perp = F.span := by
  ext v
  rw [F'.mem_perp_iff_fix h2, F.mem_span_iff_inv h2, h v, neg_eq_iff_eq_neg]

theorem finrank_eq_eight_of_neg [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (h : ∀ v, F'.La (-1) v = -F.La (-1) v) : Module.finrank K V = 8 := by
  have h4 := Submodule.finrank_add_eq_of_isCompl F.isCompl_span_perp
  rw [F.finrank_span, ← span_eq_perp_of_neg h2 h, F'.finrank_span] at h4
  omega

theorem commute_La_neg_one_of_neg {g : V ≃ₗ[K] V} (h : ∀ v, F'.La (-1) v = -F.La (-1) v)
    (hg : g * F.La (-1) = F.La (-1) * g) : g * F'.La (-1) = F'.La (-1) * g := by
  refine LinearEquiv.ext fun v => ?_
  have hv := LinearEquiv.congr_fun hg v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hv ⊢
  rw [h v, h (g v), map_neg, hv]

end Negated

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3
