module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyStep

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false


section Lang

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
  {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)

include hFr hΦ hn

theorem LangSetup.step_prod_Hchar (δ : Fin τ.rank → ℤ) (v : Lˣ) (N : ℕ) :
    S.D.step (rootDiagUnit τ (∏ j ∈ Finset.range N, Hchar ((w ^ j) • δ) (v ^ S.D.q ^ j))) =
      rootDiagUnit τ (∏ j ∈ Finset.range N,
        Hchar ((w ^ (j + 1)) • δ) (v ^ S.D.q ^ (j + 1))) := by
  induction N with
  | zero => simp [rootDiagUnit_one]
  | succ N ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, rootDiagUnit_mul, rootDiagUnit_mul,
      map_mul, ih]
    congr 1
    have := S.step_Hel hFr hΦ hn ((w ^ N) • δ) (v ^ S.D.q ^ N)
    unfold Hel at this
    rw [this, pow_succ' w N, mul_smul]
    simp only [← pow_mul, pow_succ]

theorem LangSetup.exists_lang_Hchar (hτ : SimplyLacedTag τ) {δ : Fin τ.rank → ℤ}
    (hδ : IsRoot τ δ) {N : ℕ} (hN : 0 < N) (hwN : (w ^ N) • δ = δ) (u : Lˣ)
    {Θ : Set (Fin τ.rank → ℤ)} (hΘ : ∀ j : ℕ, (w ^ j) • δ ∈ Θ ∧ -((w ^ j) • δ) ∈ Θ) :
    ∃ b b' : Fin τ.rank → Lˣ, S.D.step (rootDiagUnit τ b) = rootDiagUnit τ b' ∧
      b * b'⁻¹ = Hchar δ u ∧ rootDiagUnit τ b ∈ rootSpan τ L Θ := by
  have hq2 : 2 ≤ S.D.q := S.hqpow.1.one_lt
  have hqN : 0 < S.D.q ^ N - 1 := by
    have : 1 < S.D.q ^ N := Nat.one_lt_pow hN.ne' (by omega)
    omega
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((u⁻¹ : Lˣ) : L) hqN
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hqN.ne'] at hz
    exact (Units.ne_zero _) hz.symm
  set v : Lˣ := Units.mk0 z hz0 with hv
  have hvu : v ^ (S.D.q ^ N - 1) = u⁻¹ := Units.ext (by simpa [hv] using hz)
  refine ⟨∏ j ∈ Finset.range N, Hchar ((w ^ j) • δ) (v ^ S.D.q ^ j),
    ∏ j ∈ Finset.range N, Hchar ((w ^ (j + 1)) • δ) (v ^ S.D.q ^ (j + 1)),
    S.step_prod_Hchar hFr hΦ hn δ v N, ?_, ?_⟩
  ·
    have h1 := Finset.prod_range_succ (fun j => Hchar ((w ^ j) • δ) (v ^ S.D.q ^ j)) N
    have h2 := Finset.prod_range_succ' (fun j => Hchar ((w ^ j) • δ) (v ^ S.D.q ^ j)) N
    rw [h1] at h2
    have h3 : Hchar ((w ^ N) • δ) (v ^ S.D.q ^ N) = Hchar δ (v ^ S.D.q ^ N) := by rw [hwN]
    simp only [pow_zero, one_smul, pow_one] at h2
    rw [h3] at h2
    have h4 : (∏ j ∈ Finset.range N, Hchar ((w ^ j) • δ) (v ^ S.D.q ^ j)) *
        (∏ j ∈ Finset.range N, Hchar ((w ^ (j + 1)) • δ) (v ^ S.D.q ^ (j + 1)))⁻¹ =
        Hchar δ v * (Hchar δ (v ^ S.D.q ^ N))⁻¹ := by
      simp only [← div_eq_mul_inv]
      exact div_eq_div_iff_mul_eq_mul.2 (by rw [h2, mul_comm])
    have hinv : ∀ g : Lˣ, (Hchar δ g)⁻¹ = Hchar (τ := τ) δ g⁻¹ := fun g => by
      have := Hchar_pow (τ := τ) δ g (-1)
      simpa using this
    have hpow : v ^ S.D.q ^ N = v ^ (S.D.q ^ N - 1) * v := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h4, hinv, Hchar_mul]
    congr 1
    rw [hpow, mul_inv_rev, mul_inv_cancel_left, hvu, inv_inv]
  · have key : ∀ n : ℕ, rootDiagUnit τ
        (∏ j ∈ Finset.range n, Hchar ((w ^ j) • δ) (v ^ S.D.q ^ j)) ∈ rootSpan τ L Θ := by
      intro n
      induction n with
      | zero => simp [rootDiagUnit_one, one_mem]
      | succ n ih =>
        rw [Finset.prod_range_succ, rootDiagUnit_mul]
        refine mul_mem ih ?_
        have hr : IsRoot τ ((w ^ n) • δ) := (isRoot_smul_iff _).2 hδ
        have hsub : ({(w ^ n) • δ, -((w ^ n) • δ)} : Set (Fin τ.rank → ℤ)) ⊆ Θ := by
          intro x hx
          rcases hx with rfl | rfl
          · exact (hΘ n).1
          · exact (hΘ n).2
        exact rootSpan_mono hsub (Hel_root_mem_rootSpan hτ hr _)
    exact key N

end Lang

end CFSG.HardMathSupport.Timmesfeld.LangTorus
