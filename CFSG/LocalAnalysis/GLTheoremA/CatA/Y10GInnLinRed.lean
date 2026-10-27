module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue
public import CFSG.Assembly.GL83StatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.Assembly (largeEvenSLGroup_eq_statedSL)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamLin InnDiagKind InnDiagLin)
open CFSG.LieType.SemisimpleCentralizers.Held (SLComponentsTrivial)

theorem linear_marking_of_eq {S : Type} [Group S] {d : ℕ} {K : Type} [Field K] {H : Subgroup (GL (Fin d) K)}
    (hH : H = StatedSL d K) (hcen : Subgroup.center S = ⊥) {α : MulAut S}
    (θ : S ⧸ Subgroup.center S ≃* LargeEvenProj H)
    (u : MulAut (LargeEvenProj H)) (A : GL (Fin d) K)
    (hA : ∀ h h' : ↥H, (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk H h) = LargeEvenProjMk H h')
    (hind : ∀ l l' : S, l' = α l → u (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l')) :
    ∃ (A : GL (Fin d) K) (u : MulAut (LargeEvenProj (StatedSL d K)))
      (e : S ≃* LargeEvenProj (StatedSL d K)),
      (∀ l : S, e (α l) = u (e l)) ∧
      (∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
        u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h') := by
  subst hH
  let e0 : S ≃* LargeEvenProj (StatedSL d K) :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans θ
  refine ⟨A, u, e0, fun l => ?_, hA⟩
  exact (hind l (α l) rfl).symm

theorem innDiag_linear_data {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hFam : FamLin labK) (hin : InnDiagKind S labK α) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (d : ℕ), 1 ≤ d ∧ Nat.card K = 2 ^ (canonLabel labK).n ∧
      ∃ (A : GL (Fin d) K) (u : MulAut (LargeEvenProj (StatedSL d K)))
        (e : S ≃* LargeEvenProj (StatedSL d K)),
        (∀ l : S, e (α l) = u (e l)) ∧
        (∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
          u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h') := by
  unfold InnDiagKind at hin
  obtain ⟨_, lab', _, hraw⟩ := hin
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  rcases hFam with ht | ⟨ht, hr⟩ | ⟨ht, hr⟩
  ·
    unfold LargeEvenRawDatum at hraw
    simp only [ht] at hraw
    unfold LargeEvenRecipeLinear at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    obtain ⟨A, -, hA⟩ := hu
    have hc : (canonLabel labK).n = labK.n := by simp [canonLabel, ht]
    obtain ⟨A', u', e', hα', hg'⟩ := linear_marking_of_eq (H := LargeEvenSLGroup (Fin (labK.rank + 1)) K)
      (largeEvenSLGroup_eq_statedSL (K := K) (labK.rank + 1)) hcen θ u A hA hind
    exact ⟨K, hK, hKf, labK.rank + 1, by omega, by rw [hc]; exact hcard, A', u', e', hα', hg'⟩
  ·
    unfold LargeEvenRawDatum at hraw
    simp only [ht, hr, if_true] at hraw
    unfold LargeEvenRecipeLinear at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    obtain ⟨A, -, hA⟩ := hu
    have hc : (canonLabel labK).n = labK.n := by simp [canonLabel, ht, hr]
    obtain ⟨A', u', e', hα', hg'⟩ := linear_marking_of_eq (H := LargeEvenSLGroup (Fin 4) K)
      (largeEvenSLGroup_eq_statedSL (K := K) 4) hcen θ u A hA hind
    exact ⟨K, hK, hKf, 4, by norm_num, by rw [hc]; exact hcard, A', u', e', hα', hg'⟩
  ·
    unfold LargeEvenRawDatum at hraw
    simp only [ht, hr, if_true] at hraw
    unfold LargeEvenRecipeLinear at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    obtain ⟨A, -, hA⟩ := hu
    have hc : (canonLabel labK).n = 2 * labK.n := by simp [canonLabel, ht, hr]
    obtain ⟨A', u', e', hα', hg'⟩ := linear_marking_of_eq (H := LargeEvenSLGroup (Fin 2) K)
      (largeEvenSLGroup_eq_statedSL (K := K) 2) hcen θ u A hA hind
    refine ⟨K, hK, hKf, 2, by norm_num, ?_, A', u', e', hα', hg'⟩
    rw [hc, hcard, ← pow_mul, mul_comm]

theorem innDiagLin_of_pieces (hSL : SLComponentsTrivial) (hP1 : LinPCompIsComp) (hP2 : LinLabelDict) :
    InnDiagLin := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hin hα hlabJ hJ
  obtain ⟨K, hK, hKf, d, hd, hcard, A, u, e, hαu, hgraph⟩ := innDiag_linear_data hcen hFam hin
  have hn : 1 ≤ (canonLabel labK).n := by
    rcases Nat.eq_zero_or_pos (canonLabel labK).n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hcard
      have : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h0
  have h2 : (2 : K) = 0 := by
    haveI := Fintype.ofFinite K
    obtain ⟨q, hq, n, hqp, hqcard⟩ := FiniteField.card' K
    rw [Nat.card_eq_fintype_card, hqcard] at hcard
    have hdvd : q ∣ 2 ^ (canonLabel labK).n := by
      rw [← hcard]
      exact dvd_pow_self q (PNat.ne_zero n)
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
    subst hq2
    exact_mod_cast CharP.cast_eq_zero K 2
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
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨φ⟩⟩ :=
    pComponent_psl_fixed hSL hP1 h2 hd A hp hp2 u hgraph hpow (J.map e.toMonoidHom) hJ'
  have hEcard : Nat.card E = 2 ^ ((canonLabel labK).n * Module.finrank K E) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := E), hcard, ← pow_mul]
  have hcanon := hP2 ↥(J.map e.toMonoidHom) labJ a _ E ha hEcard hlabJ' ⟨φ⟩
  show (canonLabel labK).n ∣ (canonLabel labJ).n
  rw [hcanon]
  exact Dvd.intro _ rfl

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

end
