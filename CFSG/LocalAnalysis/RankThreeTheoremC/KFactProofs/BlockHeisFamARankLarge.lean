module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamTransfer
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamTorus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.LocalAnalysis.RankFourTheoremC

theorem heisAR_not_dvd_card_scalars {K : Type} [Field K] [Finite K] {n p : ℕ}
    [hp : Fact p.Prime] (hn : 0 < n) (hg : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) := by
  intro hd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨c, hc⟩ : ((z : StatedSL n K) : GL (Fin n) K) ∈ StatedScalars (Fin n) K := z.2
  have hdet : (Matrix.GeneralLinearGroup.det ((z : StatedSL n K) : GL (Fin n) K) : K) = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSL (z : StatedSL n K).2
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hcn : c ^ n = 1 := Units.ext (by simpa using hdet)
  have hscal : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin n) (R := K)) := by
    intro a b hab
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) hab
    exact Units.ext (by simpa [Matrix.GeneralLinearGroup.scalar] using this)
  have hzp : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  have hcp : c ^ p = 1 := by
    apply hscal
    rw [map_pow, map_one, hc]
    exact congrArg (fun w : (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) =>
      ((w : StatedSL n K) : GL (Fin n) K)) hzp
  have hc1 : c ≠ 1 := by
    intro h
    apply (hz ▸ (hp.out.one_lt.ne' : p ≠ 1) : orderOf z ≠ 1)
    have : z = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [← hc, h, map_one]
      rfl
    rw [this, orderOf_one]
  have hord : orderOf c = p := orderOf_eq_prime hcp hc1
  apply hg
  refine Nat.dvd_gcd ?_ ?_
  · rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hcn
  · rw [← hord, ← Nat.card_units]
    exact orderOf_dvd_natCard c

theorem heisAR_four_le_pRank {K : Type} [Field K] [Finite K] {n p : ℕ} [hp : Fact p.Prime]
    (hpK : ¬ p ∣ Nat.card K) (hg : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) {e : ℕ} (he : 0 < e)
    (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) (h5 : 5 * e ≤ n) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n K))) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hn : 0 < n := by
    have := Nat.mul_pos (by omega : 0 < 5) he
    omega
  let ψ : GL (Fin n) K ≃* (Module.End K (Fin n → K))ˣ := Matrix.GeneralLinearGroup.toLin
  have hfr : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have h5GL : 5 ≤ CFSG.Open.pRank p (⊤ : Subgroup (GL (Fin n) K)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 ψ]
    exact le_pRank_GL (V := Fin n → K) hpK he hpe (r := 5) (by rw [hfr]; exact h5)
  have h3 := pRank_le_pRank_inf_ker_add_one (p := p)
    (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ) ⊤
  rw [top_inf_eq, ← CFSG.Open.StatedAPI.statedSL_eq_ker_det] at h3
  obtain ⟨E, hEle, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 (StatedSL n K)
  obtain ⟨F, hF, hFcard, -⟩ := exists_isElemAbelian_subgroupOf hE (StatedSL n K)
  have hFm : Nat.card F = p ^ CFSG.Open.pRank p (StatedSL n K) := by
    rw [hFcard, inf_eq_left.2 hEle, hEcard]
  have h4 := le_pRank_centralizer_quotient ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))
    (heisAR_not_dvd_card_scalars hn hg) hF hFm (y := 1) (fun f _ => by rw [mul_one, one_mul])
  have h4' : CFSG.Open.pRank p (StatedSL n K) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n K))) :=
    h4.trans (CFSG.SectionRank.pRank_mono hp1 le_top)
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
