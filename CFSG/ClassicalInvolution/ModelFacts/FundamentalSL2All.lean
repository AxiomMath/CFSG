module

public import CFSG.ClassicalInvolution.AschTight.S19QFund

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {t : StatedLieTag} {n e : ℕ} (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) {R : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D) :
    Nonempty (↥R ≃* SL(2, GaloisField p e)) ∨
      (t = .trialityD4 ∧ Nonempty (↥R ≃* SL(2, GaloisField p (3 * e)))) := by
  have he : 1 ≤ e := hadm.2.1
  have hRmem := hR
  obtain ⟨g, γ, hγ, hRg⟩ := hR
  rcases hγ with hlong | ⟨ht, hroot⟩ | ⟨ht, hroot⟩
  · exact Or.inl (hRg ▸ fundamentalSL2_of_isFundTag hp2 hfund hadm g γ hlong)
  · subst ht
    have hR' : R ∈ Generic.fundamentalSubgroups .G2
        (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e)) := hRmem
    exact Or.inl
      (CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q.nonempty_equiv_sl2_fund_g2 hR')
  · subst ht
    obtain ⟨F, hF, hFin, hcard, ⟨φ⟩⟩ :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q.exists_equiv_sl2_fund_d4 hadm hRmem
    rcases hcard with hcard | hcard
    · obtain ⟨eF⟩ := nonempty_ringEquiv_of_natCard_eq (F := F) (F' := GaloisField p e) (by
        rw [hcard, GaloisField.card p e (by omega)])
      exact Or.inl ⟨φ.trans (slMapEquiv eF)⟩
    · obtain ⟨eF⟩ := nonempty_ringEquiv_of_natCard_eq (F := F)
        (F' := GaloisField p (3 * e)) (by
          rw [hcard, GaloisField.card p (3 * e) (by omega)])
      exact Or.inr ⟨rfl, ⟨φ.trans (slMapEquiv eF)⟩⟩

end CFSG.ClassicalInvolution.ModelFacts
