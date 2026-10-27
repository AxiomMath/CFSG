module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCLab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCOrd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsUni
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU heldGU)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

theorem innDiag_unitary_data_six {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (ht : labK.tag = .twA) (hr : labK.rank = 5)
    (hin : InnDiagKind S labK α) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x),
      (∀ x, τ x = x ^ 2 ^ labK.n) ∧ Nat.card K = (2 ^ labK.n) ^ 2 ∧
      ∃ (A : GL (Fin 6) K) (u : MulAut (LargeEvenProj (StatedSU 6 (2 ^ labK.n) K)))
        (e : S ≃* LargeEvenProj (StatedSU 6 (2 ^ labK.n) K)),
        A ∈ heldGU 6 K τ hτ ∧ (∀ l : S, e (α l) = u (e l)) ∧
        ∀ h h' : ↥(StatedSU 6 (2 ^ labK.n) K), (h' : GL (Fin 6) K) = A * (h : GL (Fin 6) K) * A⁻¹ →
          u (LargeEvenProjMk (StatedSU 6 (2 ^ labK.n) K) h) =
            LargeEvenProjMk (StatedSU 6 (2 ^ labK.n) K) h' := by
  unfold InnDiagKind at hin
  obtain ⟨_, lab', hlam, hraw⟩ := hin
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  obtain ⟨tag, rank, n⟩ := labK
  dsimp only at ht hr
  subst ht hr
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  simp only at hraw
  unfold LargeEvenRecipeUnitary at hraw
  obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
  obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
  obtain ⟨A₀, hA₀, hAu⟩ := hu
  obtain ⟨τ, hτ, hτq, A, e, hA, hαu, hgraph⟩ := unitary_marking_data hcen hcard θ u A₀ hA₀ hAu hind
  exact ⟨K, hK, hKf, τ, hτ, hτq, hcard, A, u, e, hA, hαu, hgraph⟩


theorem negB_inn (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S] {p : ℕ} {α : MulAut S}
    {J : Subgroup S} {labK labJ : GLALabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (ht : labK.tag = .twA) (hr : labK.rank = 5)
    (hin : InnDiagKind S labK α) (hα : α ^ p = 1)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : GLAPComponent p (fixSubgroup α) J) :
    labJ.tag ≠ .B ∧ labJ.tag ≠ .C ∧ labJ.tag ≠ .D := by
  obtain ⟨K, hK, hKf, τ, hτ, hτq, hcard, A, u, e, hA, hαu, hgraph⟩ :=
    innDiag_unitary_data_six hcen ht hr hin
  have h2 : (2 : K) = 0 := two_eq_zero_of_card hcard
  have hn : 1 ≤ labK.n := by
    by_contra hn0
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hcard, show labK.n = 0 by omega] at h1
    norm_num at h1
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
  have hdQ : ((6 : ℕ), 2 ^ labK.n) ≠ (3, 2) := by
    intro h
    have := (Prod.mk.inj h).1
    omega
  rcases pComponent_psu_fixed uniScalar_holds hτ hτq hcard h2 (by norm_num) hdQ A hA hp hp2 u
      hgraph hpow (J.map e.toMonoidHom) hJ' with
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
    rcases uniLabel_cases hRig τ' hτ' ha2 hτ'm hcardm hlabJ' ⟨φ⟩ with h | h
    · exact not_bcd_of_canon_twA h
    · by_contra hbcd
      obtain ⟨-, -, h13⟩ := bcd_of_canon_A h hbcd
      omega
  ·
    have hcardm : Nat.card E = 2 ^ (labK.n * (2 * ee)) := by
      rw [pow_mul]
      exact hcardE
    have hcanon := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig _ labJ b
      (labK.n * (2 * ee)) E hb2 hcardm hlabJ' ⟨φ⟩
    by_contra hbcd
    obtain ⟨-, -, hb3⟩ := bcd_of_canon_A hcanon hbcd
    have hb4 : b = 4 := by omega
    subst hb4
    have hee : 1 ≤ ee := by
      by_contra hee0
      have h1 : 1 < Nat.card E := Finite.one_lt_card
      rw [hcardE, show ee = 0 by omega] at h1
      norm_num at h1
    exact no_psl_four_in_psu_six hn hee hcard hcardE (J.map e.toMonoidHom) φ


theorem i14NegPieceB_of (hRig : GGLabelRigidInput) (hFld : FldUni) :
    CFSG.LocalAnalysis.GLTheoremA.Y10F.I14NegPieceB := by
  intro S _ _ p α J labK labJ hp hp2 hcen hlabK hlabJ hα hJ hK5
  have hFam : FamUni labK := Or.inl hK5.1
  rcases ClsUni_holds S p α labK hFam hp hp2 hcen hlabK hα with hin | hfld
  · exact negB_inn hRig hp hp2 hcen hK5.1 hK5.2 hin hα hlabJ hJ
  · obtain ⟨-, htag, hrank⟩ := hFld S p α J labK labJ hFam hp hp2 hcen hfld hα hlabJ hJ
    have hcK : canonLabel labK = labK := by simp [canonLabel, hK5.1]
    rw [hcK] at htag hrank
    have hc : canonLabel labJ = ⟨.twA, labK.rank, (canonLabel labJ).n⟩ := by
      rcases hcl : canonLabel labJ with ⟨t', r', n'⟩
      rw [hcl] at htag hrank
      simp only at htag hrank ⊢
      rw [← htag, ← hrank, hK5.1]
    exact not_bcd_of_canon_twA hc

end CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC
