module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrthGlue
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrthBlock
import CFSG.RankThree.PartOne.AUTSL.OmegaDickson

public section

open Matrix Module CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrth

open CFSG.HardMathSupport.Curtis CFSG.HardMathSupport.Curtis.Coordinator

section Inner

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) [CharP K 2]
  (hQ : ∃ v, Q v ≠ 0)

theorem exists_omegaLin_eq_of_mem_orthDerived {φ : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hφ : φ ∈ orthDerived Q) : ∃ e : matrixProjectiveDerived Q, omegaLin Q hQ e = φ := by
  rw [← CFSG.RankThree.PartOne.AUTSL.map_matrixDerived_linearIso (Q := Q)] at hφ
  obtain ⟨A, hA, rfl⟩ := hφ
  refine ⟨matrixProjectiveProjection Q ⟨A, hA⟩, LinearEquiv.ext fun v => ?_⟩
  rw [omegaLin_apply]
  rw [omegaMat, omegaRep_proj]
  rfl

theorem oddOrderIsometry_omegaLin {p : ℕ} (hpK : (p : K) ≠ 0)
    (hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0) (y : matrixProjectiveDerived Q)
    (hyp : y ^ p = 1) : OddOrderIsometry Q p (omegaLin Q hQ y) where
  mem := by
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => ?_
    exact (mem_matrixIsometries_iff Q _).1 (omegaRep_mem_isometries Q hQ y) v
  pow_eq_one := by rw [← map_pow, hyp, map_one]
  cast_ne_zero := hpK
  regular := hreg

end Inner

variable {K : Type} [Field K] [Finite K] {n f : ℕ} {Q : QuadraticForm K (Fin (2 * n) → K)}

theorem orth_inner_false (h : OrthCellData Q f) {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : ¬ r ∣ p - 1)
    (Ē : Subgroup (matrixProjectiveDerived Q)) (hE : CFSG.Open.IsElemAbelian p Ē)
    (hcard : Nat.card Ē = p ^ 4) (y : matrixProjectiveDerived Q) (hyp : y ^ p = 1)
    (hyE : ∀ e ∈ Ē, y * e * y⁻¹ = e)
    (hsolv : Group.IsSolvable ↥(autFix (MulAut.conj y)))
    (g : similarityPairs Q) (k : ℕ) (hγ : matrixProjectiveConjugationHom Q g ^ r ^ k = 1)
    (hγE : ∀ e ∈ Ē, matrixProjectiveConjugationHom Q g e ∈ Ē)
    (hcomm : matrixProjectiveConjugationHom Q g * MulAut.conj y =
      MulAut.conj y * matrixProjectiveConjugationHom Q g)
    (hnt : ∃ e ∈ Ē, matrixProjectiveConjugationHom Q g e ≠ e) : False := by
  classical
  have : CharP K 2 := h.charP_two
  have hQ := h.exists_ne_zero
  have hfix : matrixProjectiveConjugationHom Q g y = y :=
    fixes_of_comm_conj h.center_eq_bot _ y hcomm
  by_cases hy1 : y = 1
  · subst hy1
    obtain ⟨hsimple, a, b, hab⟩ := h.simple_nonabelian
    have htop : autFix (MulAut.conj (1 : matrixProjectiveDerived Q)) = ⊤ := by
      ext z
      simp [mem_autFix]
    rw [htop] at hsolv
    have hs : Group.IsSolvable (matrixProjectiveDerived Q) :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv (G := matrixProjectiveDerived Q)).toMonoidHom)
        (Subgroup.topEquiv (G := matrixProjectiveDerived Q)).surjective
    have := hsimple
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hs) a b)
  · have hσ : g.val.right ^ r ^ k = 1 := right_pow_eq_one_of_gates Q h.gates g _ hγ
    obtain ⟨hh, hmem, -, hmult⟩ := exists_big_primary_factor_of_pair Q hQ h.card_eq hp hp2 hr hr5
      hrp Ē hE hcard y hyp hyE g k hγ hσ hγE hfix hnt
    have hpK : (p : K) ≠ 0 := by
      intro h0
      rw [CharP.cast_eq_zero_iff K 2] at h0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0).symm
    have hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0 := fun v hv =>
      h.nondegenerate.1 v (fun w => by simpa using hv w)
    have hx := oddOrderIsometry_omegaLin Q hQ hpK hreg y hyp
    have hns := Coordinator.SPLCell.not_isSolvable_isometryCentralizer_of_mult hx hmem hmult
    apply hns
    let H : Subgroup ((Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) :=
      isometryCentralizer Q (omegaLin Q hQ y) ⊓ orthDerived Q
    let N : Subgroup (matrixProjectiveDerived Q) := H.comap (omegaLin Q hQ)
    have hNle : N ≤ autFix (MulAut.conj y) := by
      intro a ha
      have hc := ((inf_le_left : H ≤ _) ha : omegaLin Q hQ a ∈
        isometryCentralizer Q (omegaLin Q hQ y))
      have hc' : omegaLin Q hQ y * omegaLin Q hQ a = omegaLin Q hQ a * omegaLin Q hQ y :=
        ((Subgroup.mem_inf.1 hc).2 : omegaLin Q hQ a ∈ Subgroup.centralizer {omegaLin Q hQ y}) _
          rfl
      have : y * a = a * y := omegaLin_injective Q hQ (by rw [map_mul, map_mul]; exact hc')
      rw [mem_autFix, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
      exact this
    have hNs : Group.IsSolvable N :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNle)
        (Subgroup.inclusion_injective hNle)
    refine Group.isSolvable_of_surjective (f := (omegaLin Q hQ).subgroupComap H) ?_
    rintro ⟨φ, hφ⟩
    obtain ⟨e, he⟩ := exists_omegaLin_eq_of_mem_orthDerived Q hQ (Subgroup.mem_inf.1 hφ).2
    exact ⟨⟨e, by change omegaLin Q hQ e ∈ H; rw [he]; exact hφ⟩, Subtype.ext he⟩

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrth
