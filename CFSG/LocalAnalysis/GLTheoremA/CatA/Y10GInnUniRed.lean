module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamUni InnDiagUni)
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin (LinLabelDict)

theorem innDiagUni_of_pieces (hScal : UniScalar) (hP2 : LinLabelDict) (hP3 : UniLabelDict) :
    InnDiagUni := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hin hα hlabJ hJ
  obtain ⟨K, hK, hKf, d, τ, hτ, hτq, hcard, hd3, hd3n, A, u, e, hA, hαu, hgraph⟩ :=
    innDiag_unitary_data hcen hFam hin
  have h2 : (2 : K) = 0 := two_eq_zero_of_card hcard
  have hMEq : MulAut.congr e α = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ p = 1 := by
    rw [← hMEq, ← map_pow, hα, map_one]
  have hJ' : GLAPComponent p (fixSubgroup u) (J.map e.toMonoidHom) := by
    rw [← hMEq, ← fixSubgroup_map_congr]
    exact (glaPComponent_map_iff hp e.injective).mpr hJ
  have hlabJ' : HasLabel ↥(J.map e.toMonoidHom) (fun l : GLALabel => l = labJ) :=
    hasLabel_transport e hlabJ
  have hdQ : (d, 2 ^ labK.n) ≠ (3, 2) := by
    intro h
    obtain ⟨hd, hQ⟩ := Prod.mk.inj h
    have h2n : 2 ≤ labK.n := hd3n hd
    have : 2 ^ 2 ≤ 2 ^ labK.n := Nat.pow_le_pow_right (by norm_num) h2n
    omega
  have hcanK : (canonLabel labK).n = labK.n := by
    rcases hFam with ht | ⟨ht, hr⟩
    · simp [canonLabel, ht]
    · simp [canonLabel, ht, hr]
  rcases pComponent_psu_fixed hScal hτ hτq hcard h2 (by omega) hdQ A hA hp hp2 u hgraph hpow
      (J.map e.toMonoidHom) hJ' with
    ⟨a, dd, E, hE, hEf, τ', hτ', ha2, hτ'Q, hcardE, ⟨φ⟩⟩ |
    ⟨b, ee, E, hE, hEf, hb2, hcardE, ⟨φ⟩⟩
  ·
    have hτ'm : ∀ x : E, τ' x = x ^ 2 ^ (labK.n * dd) := by
      intro x
      rw [pow_mul]
      exact hτ'Q x
    have hcardm : Nat.card E = (2 ^ (labK.n * dd)) ^ 2 := by
      rw [pow_mul]
      exact hcardE
    have hlab : (canonLabel labJ).n = labK.n * dd :=
      hP3 ↥(J.map e.toMonoidHom) labJ a (labK.n * dd) E τ' hτ' ha2 hτ'm hcardm hlabJ' ⟨φ⟩
    show (canonLabel labK).n ∣ (canonLabel labJ).n
    rw [hcanK, hlab]
    exact Dvd.intro dd rfl
  ·
    have hcardm : Nat.card E = 2 ^ (labK.n * (2 * ee)) := by
      rw [pow_mul]
      exact hcardE
    have hcanon := hP2 ↥(J.map e.toMonoidHom) labJ b (labK.n * (2 * ee)) E hb2 hcardm hlabJ' ⟨φ⟩
    have hlab : (canonLabel labJ).n = labK.n * (2 * ee) := by
      rw [hcanon]
    show (canonLabel labK).n ∣ (canonLabel labJ).n
    rw [hcanK, hlab]
    exact Dvd.intro _ rfl

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

end
