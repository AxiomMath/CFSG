module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue
import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA Matrix
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamUni InnDiagKind)
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU)

theorem i167CU_data {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S} {p : ℕ}
    (hp : p.Prime) (hcen : Subgroup.center S = ⊥) (hFam : FamUni labK) (hαp : α ^ p = 1)
    (hin : InnDiagKind S labK α) {J : Subgroup S} (hJ : GLAPComponent p (fixSubgroup α) J) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (d : ℕ) (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x)
      (A : GL (Fin d) K) (u : MulAut (LargeEvenProj (StatedSU d (2 ^ labK.n) K)))
      (J' : Subgroup (LargeEvenProj (StatedSU d (2 ^ labK.n) K))),
      (∀ x, τ x = x ^ 2 ^ labK.n) ∧ Nat.card K = (2 ^ labK.n) ^ 2 ∧ 3 ≤ d ∧
      (d, 2 ^ labK.n) ≠ (3, 2) ∧ A ∈ heldGU d K τ hτ ∧
      (∀ h h' : ↥(StatedSU d (2 ^ labK.n) K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
        u (LargeEvenProjMk (StatedSU d (2 ^ labK.n) K) h) =
          LargeEvenProjMk (StatedSU d (2 ^ labK.n) K) h') ∧
      u ^ p = 1 ∧ GLAPComponent p (fixSubgroup u) J' ∧ Nonempty (PQuot p J ≃* PQuot p J') := by
  obtain ⟨K, hK, hKf, d, τ, hτ, hτq, hcard, hd3, hd3n, A, u, e, hA, hαu, hgraph⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.innDiag_unitary_data hcen hFam hin
  have hdQ : (d, 2 ^ labK.n) ≠ (3, 2) := by
    intro h
    obtain ⟨hd, hQ⟩ := Prod.mk.inj h
    have h2n : 2 ≤ labK.n := hd3n hd
    have : 2 ^ 2 ≤ 2 ^ labK.n := Nat.pow_le_pow_right (by norm_num) h2n
    omega
  have hMEq : MulAut.congr e α = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ p = 1 := by
    rw [← hMEq, ← map_pow, hαp, map_one]
  have hJ' : GLAPComponent p (fixSubgroup u) (J.map e.toMonoidHom) := by
    rw [← hMEq, ← CFSG.LocalAnalysis.GLTheoremA.Y10F.fixSubgroup_map_congr e α]
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff hp e.injective).mpr hJ
  have hkerbot : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
  have hequiv : Nonempty (PQuot p J ≃* PQuot p (J.map e.toMonoidHom)) := by
    refine nonempty_pQuot_equiv_map hp (ψ := e.toMonoidHom) ?_ J
    rw [hkerbot, Subgroup.card_bot]
    exact hp.not_dvd_one
  exact ⟨K, hK, hKf, d, τ, hτ, A, u, J.map e.toMonoidHom, hτq, hcard, hd3, hdQ, hA, hgraph, hpow,
    hJ', hequiv⟩

end CFSG.LocalAnalysis.GLTheoremA.I167

end
