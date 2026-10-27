module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.TwelveD4Torus

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

set_option linter.unusedSectionVars false


theorem e8T12_comb_arith {p : ℕ} (hp : p.Prime) {q : ℤ} (hΦ : (p : ℤ) ∣ q ^ 4 - q ^ 2 + 1)
    {b₀ b₁ b₂ b₃ lam : Fin Tag.E8.rank → ℤ} {M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ}
    (R1 : ∀ j, ∑ i, b₀ i * M i j = b₁ j) (R2 : ∀ j, ∑ i, b₁ i * M i j = b₂ j)
    (R3 : ∀ j, ∑ i, b₂ i * M i j = b₃ j) (R4 : ∀ j, ∑ i, b₃ i * M i j = b₂ j - b₀ j)
    (L0 : ∑ i, lam i * b₀ i = 0) (L1 : ∑ i, lam i * b₁ i = 0) (L2 : ∑ i, lam i * b₂ i = 0)
    (L3 : ∑ i, lam i * b₃ i = 1) :
    (∀ j, (p : ℤ) ∣ (∑ i, ((q ^ 3 - q) * b₀ i + (q ^ 2 - 1) * b₁ i + q * b₂ i + 1 * b₃ i) *
        M i j) - q * ((q ^ 3 - q) * b₀ j + (q ^ 2 - 1) * b₁ j + q * b₂ j + 1 * b₃ j)) ∧
      ∃ i, ¬ (p : ℤ) ∣ (q ^ 3 - q) * b₀ i + (q ^ 2 - 1) * b₁ i + q * b₂ i + 1 * b₃ i := by
  refine ⟨fun j => ?_, ?_⟩
  · have h1 : ∑ i, ((q ^ 3 - q) * b₀ i + (q ^ 2 - 1) * b₁ i + q * b₂ i + 1 * b₃ i) * M i j =
        (q ^ 3 - q) * ∑ i, b₀ i * M i j + (q ^ 2 - 1) * ∑ i, b₁ i * M i j +
          q * ∑ i, b₂ i * M i j + 1 * ∑ i, b₃ i * M i j := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : (∑ i, ((q ^ 3 - q) * b₀ i + (q ^ 2 - 1) * b₁ i + q * b₂ i + 1 * b₃ i) * M i j) -
        q * ((q ^ 3 - q) * b₀ j + (q ^ 2 - 1) * b₁ j + q * b₂ j + 1 * b₃ j) =
        -(q ^ 4 - q ^ 2 + 1) * b₀ j := by
      rw [h1, R1 j, R2 j, R3 j, R4 j]
      ring
    rw [h2]
    exact Dvd.dvd.mul_right (Dvd.dvd.neg_right hΦ) _
  · by_contra hcon
    have hall : ∀ i, (p : ℤ) ∣ (q ^ 3 - q) * b₀ i + (q ^ 2 - 1) * b₁ i + q * b₂ i + 1 * b₃ i :=
      fun i => by
        by_contra h
        exact hcon ⟨i, h⟩
    have h1 : (p : ℤ) ∣ ∑ i, lam i * ((q ^ 3 - q) * b₀ i + (q ^ 2 - 1) * b₁ i + q * b₂ i +
        1 * b₃ i) := Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (hall i) _
    have h2 : ∑ i, lam i * ((q ^ 3 - q) * b₀ i + (q ^ 2 - 1) * b₁ i + q * b₂ i + 1 * b₃ i) =
        (q ^ 3 - q) * ∑ i, lam i * b₀ i + (q ^ 2 - 1) * ∑ i, lam i * b₁ i +
          q * ∑ i, lam i * b₂ i + 1 * ∑ i, lam i * b₃ i := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, L0, L1, L2, L3] at h1
    simp only [mul_zero, zero_add, mul_one] at h1
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)

theorem e8T12_exists_order_p_mem_D4 {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    {ζ : Lˣ} (hζ : orderOf ζ = p) {n : ModGL Tag.E8 L} {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) (hΦ : (q : ZMod p) ^ 4 - (q : ZMod p) ^ 2 + 1 = 0)
    (hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples e8T12V Fr).map (rootDiagUnitHom Tag.E8 L))
    {c : D4Cert} (hc : c ∈ e8T12D4Certs) :
    ∃ d ∈ rootSpan Tag.E8 L (classSetL e8T12Rows c.cls) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr)), orderOf d = p := by
  obtain ⟨⟨_, y, lam⟩, -, -, hgood⟩ := e8T12_d4_data_check c hc
  change E8T12D4Good c.w y lam at hgood
  obtain ⟨R1, R2, R3, R4, L0, L1, L2, L3⟩ := hgood
  have hSig := (D4Cert.sound (e8T12_d4_good c hc)).1
  have hΦ' : (p : ℤ) ∣ (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_
    push_cast
    exact hΦ
  rw [e8T12V_eq] at hT
  obtain ⟨hW, hnz⟩ := e8T12_comb_arith hp hΦ' (M := toMat Tag.E8.rank e8T12VList) R1 R2 R3 R4
    L0 L1 L2 L3
  set u : Fin 4 → ℤ := fun k => ((q : ℤ) ^ 3 - q) * y 0 k + ((q : ℤ) ^ 2 - 1) * y 1 k +
    q * y 2 k + 1 * y 3 k with hu
  have he : ∀ i, e8T12D4Exp c.w u i = ((q : ℤ) ^ 3 - q) * e8T12D4Exp c.w (y 0) i +
      ((q : ℤ) ^ 2 - 1) * e8T12D4Exp c.w (y 1) i + q * e8T12D4Exp c.w (y 2) i +
      1 * e8T12D4Exp c.w (y 3) i := fun i => e8T12_D4Exp_comb c.w _ _ _ _ y i
  have hS : ∀ k, e8T12D4Gamma c.w k ∈ classSetL e8T12Rows c.cls ∧
      -e8T12D4Gamma c.w k ∈ classSetL e8T12Rows c.cls := fun k => by
    rw [hSig]
    exact e8T12_D4Gamma_mem c.w k
  refine ⟨rootDiagUnit Tag.E8 (fun i => ζ ^ e8T12D4Exp c.w u i), ⟨?_, ?_⟩, ?_⟩
  · exact e8T12_rootDiagUnit_mem_rootSpan ζ (e8T12D4Gamma c.w) (e8T12_isRoot_D4Gamma c.w) hS u
  · refine mem_twistedFixedPoints.2 (mem_twistedTorusOf.1
      (e8T12_rootDiagUnit_mem_twistedTorus hζ hFr hT (e8T12D4Exp c.w u) fun j => ?_)).2
    simp only [he]
    exact hW j
  · refine e8T12_orderOf_rootDiagUnit hp hζ _ ?_
    obtain ⟨i, hi⟩ := hnz
    exact ⟨i, by simpa only [he] using hi⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
