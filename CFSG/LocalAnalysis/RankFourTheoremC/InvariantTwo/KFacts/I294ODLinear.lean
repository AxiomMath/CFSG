module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODTransport
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODMatrix
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODMonoMat
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODTorus
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODLinLift
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverLie
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Open CFSG.Assembly.LowTwoRank I294OD

theorem odFamily_linear {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpn : p ∣ n) (hn0 : 0 < n) (hpK : p ∣ Nat.card K - 1) :
    ODFamily p n (conjAut n K) (GeneralLinearGroup.det (n := Fin n) (R := K))
      (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range := by
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd hn0 hpn)
  have hn3 : 3 ≤ n := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have key : ∀ B : GL (Fin n) K,
      B ^ p ∈ (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range →
      (∀ w ∈ (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range, w ^ p ≠ B ^ p) →
      ∃ ζ : K, (∀ b : K, b ^ p ≠ ζ) ∧
        (B : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) ζ := by
    rintro B ⟨c, hc⟩ hnp
    refine ⟨(c : K), fun b hb => ?_, ?_⟩
    · have hb0 : b ≠ 0 := by
        rintro rfl
        have : (c : K) = 0 := by rw [← hb]; exact zero_pow hp.ne_zero
        exact c.ne_zero this
      refine hnp (GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0)) ⟨_, rfl⟩ ?_
      rw [← hc, ← map_pow]
      congr 1
      exact Units.ext (by simpa using hb)
    · have h1 := congrArg Units.val hc
      rw [GeneralLinearGroup.coe_scalar] at h1
      rw [h1, Units.val_pow_eq_pow_val]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩ B
    exact (l212in_scalar_comm B c).symm
  · intro B
    rw [MonoidHom.mem_range]
    constructor
    · intro h
      exact (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn3 B).1 h
    · rintro ⟨c, rfl⟩
      exact conjAut_scalar c
  · intro w
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, by rw [l212in_det_scalar]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨_, ⟨c, rfl⟩, l212in_det_scalar c⟩
  · exact fun α β => l212in_comm_mem_range_conjAut hn3 α β
  · exact fun B h => l212in_conjAut_mem_inner B h
  · intro ℓ
    obtain ⟨s, rfl⟩ := proj_surjective n K ℓ
    refine ⟨SpecialLinearGroup.toGL s, ?_, l212in_conjAut_toGL s⟩
    have h : SpecialLinearGroup.toGL s ∈
        (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := ⟨s, rfl⟩
    rw [SpecialLinearGroup.range_toGL_eq_ker_det] at h
    exact h
  · exact fun α => od_lin_lift hn3 α
  · intro B hB
    have hA : (B : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
      have := congrArg Units.val hB
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    obtain ⟨f, hfi, hfc, hfs⟩ := torus_commuting hp hn5 hpK hA
    refine ⟨(proj n K).comp f, ?_, fun a => ?_⟩
    · rw [injective_iff_map_eq_one]
      intro x hx
      exact (injective_iff_map_eq_one f).1 hfi x (hfs x (proj_eq_one_iff.1 hx))
    · rw [MonoidHom.comp_apply, conjAut_proj]
      congr 1
      refine Subtype.ext ((coe_slConjugation B (f a)).trans ?_)
      calc (B : Matrix (Fin n) (Fin n) K) * (f a : Matrix (Fin n) (Fin n) K) *
            ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          = ((f a : Matrix (Fin n) (Fin n) K) * B) *
              ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
            rw [hfc a]
        _ = (f a : Matrix (Fin n) (Fin n) K) := by
            rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  · intro hn B hBZ hBnp
    obtain ⟨ζ, hζ, hM⟩ := key B hBZ hBnp
    obtain ⟨P, Q, N, π, hPQ, hQP, hMP, hN⟩ := exists_monomial_matrices hp hζ hM
    obtain ⟨T, hT, hcard, hnorm⟩ := torus_normalized hp hpK hn hPQ hQP hMP hN
    refine ⟨T.map (proj n K), IsElemAbelian.map hT _, hcard, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨g', hg', hgg'⟩ := hnorm g hg
    refine ⟨g', hg', ?_⟩
    rw [conjAut_proj]
    congr 1
    refine Subtype.ext (Eq.symm ((coe_slConjugation B g).trans ?_))
    calc (B : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = ((g' : Matrix (Fin n) (Fin n) K) * B) *
            ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [hgg']
      _ = (g' : Matrix (Fin n) (Fin n) K) := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  · intro hnp B hBZ hBnp c hc
    subst hnp
    obtain ⟨ζ, hζ, hM⟩ := key B hBZ hBnp
    have hdet := det_eq_of_pow_eq hp hp2 hζ hM
    refine hζ (c : K) ?_
    rw [← hdet, ← GeneralLinearGroup.val_det_apply, hc, Units.val_pow_eq_pow_val]
  · intro hnp A B hBZ hBnp hAB hAp
    subst hnp
    obtain ⟨ζ, hζ, hM⟩ := key B hBZ hBnp
    have hA : (A : Matrix (Fin n) (Fin n) K) ^ n = 1 := by
      have := congrArg Units.val hAp
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    have hAB' : (A : Matrix (Fin n) (Fin n) K) * B = B * A := by
      have := congrArg Units.val hAB
      rwa [Units.val_mul, Units.val_mul] at this
    obtain ⟨μ, hμ⟩ := scalar_of_commute hp hpK hζ hM hA hAB'
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      have h1 : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          = 1 := Units.mul_inv A
      rw [hμ] at h1
      simp at h1
    exact ⟨Units.mk0 μ hμ0, Units.ext (by rw [GeneralLinearGroup.coe_scalar, hμ]; rfl)⟩

theorem od_linear_false {p n : ℕ} [hpp : Fact p.Prime] (hp5 : 5 ≤ p) {X : Type} [Group X]
    [Finite X] (L : Subgroup X) [L.Normal] (hnab : ∃ a b : L, a * b ≠ b * a)
    (hcen : centralizer (L : Set X) = ⊥) {D : Subgroup X} (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) {z g : X} (hz : z ∈ D) (hz1 : z ≠ 1)
    (hg : CFSG.LocalAnalysis.RankThreeTheoremC.IsPlaneDiagonal p D z g) {x : X} (hxD : x ∈ D)
    (hx1 : x ≠ 1) (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) {K : Type}
    [Field K] [Finite K] (hpn : p ∣ n) (hpK : p ∣ Nat.card K - 1)
    (e : L ≃* StatedProj (StatedSL n K)) : False := by
  have hp : p.Prime := hpp.out
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · obtain ⟨a, b, hab⟩ := hnab
      haveI : Nontrivial L := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
      haveI : Subsingleton (StatedProj (StatedSL 0 K)) := inferInstance
      exact absurd e.injective.subsingleton (not_subsingleton _)
    · exact hn0
  let e' : L ≃* projectiveSL n K := e.trans (l212in_projectiveSLEquivStated n K).symm
  exact od_core ((odFamily_linear hp hp5 hpn hn0 hpK).transport e'.symm) hp5 hpn hn0 hcen hD
    hDcard hz hz1 hg hxD hx1 hx2

end CFSG.LocalAnalysis.RankFourTheoremC
