module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269Six4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269Six3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I269Six

open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.Fischer
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo (hF4)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open scoped commutatorElement

theorem T1_bot {Ê J : Subgroup M6} (hperf : ⁅J, J⁆ = J)
    (hcomm : ∀ h ∈ Ê, ∀ k ∈ Ê, ⁅h, k⁆ ∈ Zs) (hcube : ∀ h ∈ Ê, h ^ 3 ∈ Zs)
    (hcard : 9 < Nat.card Ê) (hJ : ∀ u ∈ J, ∀ h ∈ Ê, u * h = h * u)
    {d : Fin 6 → F4} {D : M6} (hDd : mM6 D = Matrix.diagonal d) (hDÊ : D ∈ Ê)
    {l : F4} {i1 i2 : Fin 6} (hne : i1 ≠ i2) (hS : ∀ i, i ≠ i1 → i ≠ i2 → d i = l)
    (h1 : d i1 ≠ l) (h2 : d i2 ≠ l) (h12 : d i1 ≠ d i2) : J = ⊥ := by
  have htr := trace_diag_ne_zero d l i1 i2 hne hS h12
  have hcD := commute_D hcomm hDd hDÊ htr
  have hblock : ∀ h ∈ Ê, ∀ i j, d i ≠ d j → mM6 h i j = 0 := fun h hh =>
    fun i j hij => zero_of_commute_diag (hcD h hh) hij
  have hd1 : ∀ j, j ≠ i1 → d j ≠ d i1 := by
    intro j hj
    by_cases hj2 : j = i2
    · subst hj2; exact h12.symm
    · rw [hS j hj hj2]; exact fun e => h1 e.symm
  have hd2 : ∀ j, j ≠ i2 → d j ≠ d i2 := by
    intro j hj
    by_cases hj1 : j = i1
    · subst hj1; exact h12
    · rw [hS j hj1 hj]; exact fun e => h2 e.symm
  obtain ⟨y, hyÊ, hNS⟩ := exists_nonscalar hne hS h1 h2 h12 hblock hcard
  have hcy := cube_one (l := l) (i1 := i1) (i2 := i2) hcube hblock hd1 y hyÊ
  have hcy2 := cube_one (l := l) (i1 := i2) (i2 := i1) hcube hblock hd2 y hyÊ
  set Y : Matrix (Fin 6) (Fin 6) F4 := mM6 y with hYdef
  set a := Y i1 i1 with ha_def
  set b := Y i2 i2 with hb_def
  have ha3 : a ^ 3 = 1 := hcy.2
  have hb3 : b ^ 3 = 1 := hcy2.2
  have ha0 : a ≠ 0 := by rintro h0; rw [h0] at ha3; simp at ha3
  have hb0 : b ≠ 0 := by rintro h0; rw [h0] at hb3; simp at hb3
  obtain ⟨x1, x2, hx12, hx1, hx2, hs1, hs2⟩ := exists_two_small Y hne
  let δ : Fin 6 → F4 := fun i => if i = i1 then x1 / a else if i = i2 then x2 / b else 1
  have hδ0 : ∀ i, δ i ≠ 0 := by
    intro i
    simp only [δ]
    split_ifs
    · exact div_ne_zero hx1 ha0
    · exact div_ne_zero hx2 hb0
    · exact one_ne_zero
  have hδ3 : ∀ i, δ i ^ 3 = 1 := by
    intro i
    simp only [δ]
    split_ifs
    · rw [div_pow, f4_cube x1 hx1, f4_cube a ha0, div_one]
    · rw [div_pow, f4_cube x2 hx2, f4_cube b hb0, div_one]
    · exact one_pow 3
  have hδconst : ∀ i j, d i = d j → δ i = δ j := by
    intro i j hij
    by_cases hi : i = j
    · rw [hi]
    have hi1 : i ≠ i1 := by
      rintro rfl; exact hd1 j (fun e => hi e.symm) hij.symm
    have hi2 : i ≠ i2 := by
      rintro rfl; exact hd2 j (fun e => hi e.symm) hij.symm
    have hj1 : j ≠ i1 := by
      rintro rfl; exact hd1 i hi hij
    have hj2 : j ≠ i2 := by
      rintro rfl; exact hd2 i hi hij
    simp only [δ, if_neg hi1, if_neg hi2, if_neg hj1, if_neg hj2]
  set Δ : GL (Fin 6) F4 := dGL δ hδ0 with hΔ
  have hΔU : Δ ∈ primeFormUnitary hF4 (idGram F4 6) := dGL_mem_UG δ hδ0 hδ3
  set Ŷ : GL (Fin 6) F4 := (y : GL (Fin 6) F4) * Δ with hŶ
  have hŶU : Ŷ ∈ primeFormUnitary hF4 (idGram F4 6) := mul_mem (mem_UG_of_M6 y) hΔU
  have hyΔ : (y : GL (Fin 6) F4) * Δ = Δ * (y : GL (Fin 6) F4) := by
    apply Units.ext
    simp only [Units.val_mul, hΔ, dGL_val]
    exact commute_diag_of_block (hcD y hyÊ) hδconst
  have hΔ3 : Δ ^ 3 = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, hΔ, dGL_val, Units.val_one]
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hδ3 i
  have hŶ3 : Ŷ ^ 3 = 1 := by
    have hc : Commute (y : GL (Fin 6) F4) Δ := hyΔ
    rw [hŶ, hc.mul_pow, hcy.1, hΔ3, mul_one]
  have hJŶ : ∀ u ∈ J, (u : GL (Fin 6) F4) * Ŷ = Ŷ * (u : GL (Fin 6) F4) := by
    intro u hu
    have huy : (u : GL (Fin 6) F4) * (y : GL (Fin 6) F4) = (y : GL (Fin 6) F4) * (u : GL (Fin 6) F4) :=
      congrArg Subtype.val (hJ u hu y hyÊ)
    have huD : (u : GL (Fin 6) F4) * (D : GL (Fin 6) F4) = (D : GL (Fin 6) F4) * (u : GL (Fin 6) F4) :=
      congrArg Subtype.val (hJ u hu D hDÊ)
    have huΔ : (u : GL (Fin 6) F4) * Δ = Δ * (u : GL (Fin 6) F4) := by
      apply Units.ext
      simp only [Units.val_mul, hΔ, dGL_val]
      have hMu : mM6 u * Matrix.diagonal d = Matrix.diagonal d * mM6 u := by
        rw [← hDd]
        have := congrArg Units.val huD
        simpa [mM6, Units.val_mul] using this
      exact commute_diag_of_block hMu hδconst
    rw [hŶ, ← mul_assoc, huy, mul_assoc, huΔ, ← mul_assoc]
  have hM : ((Ŷ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = Y * Matrix.diagonal δ := by
    rw [hŶ, Units.val_mul, hΔ, dGL_val]
  have hrow : ∀ (w : Fin 6 → F4) (i : Fin 6), (∀ j, j ≠ i → Y i j = 0) →
      Y.mulVec w i = Y i i * w i := by
    intro w i hi
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
    · intro j _ hj; rw [hi j hj, zero_mul]
    · intro hi'; exact absurd (Finset.mem_univ i) hi'
  have hMv : ∀ v, ((Ŷ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec v =
      Y.mulVec (fun i => δ i * v i) := by
    intro v
    rw [hM, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact Matrix.mulVec_diagonal δ v i
  have hY1 : ∀ j, j ≠ i1 → Y i1 j = 0 := fun j hj => hblock y hyÊ i1 j (hd1 j hj).symm
  have hY2 : ∀ j, j ≠ i2 → Y i2 j = 0 := fun j hj => hblock y hyÊ i2 j (hd2 j hj).symm
  have r1 : ∀ v : Fin 6 → F4, ((Ŷ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec v i1 = x1 * v i1 := by
    intro v
    rw [hMv, hrow _ i1 hY1]
    simp only [δ, if_pos rfl]
    change a * (x1 / a * v i1) = x1 * v i1
    field_simp
  have r2 : ∀ v : Fin 6 → F4, ((Ŷ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec v i2 = x2 * v i2 := by
    intro v
    rw [hMv, hrow _ i2 hY2]
    simp only [δ, if_neg hne.symm, if_pos rfl]
    change b * (x2 / b * v i2) = x2 * v i2
    field_simp
  have hMY : ∀ v : Fin 6 → F4, v i1 = 0 → v i2 = 0 →
      ((Ŷ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec v = Y.mulVec v := by
    intro v hv1 hv2
    rw [hMv]
    congr 1
    funext i
    by_cases hi1 : i = i1
    · subst hi1; simp [hv1]
    by_cases hi2 : i = i2
    · subst hi2; simp [hv2]
    simp [δ, hi1, hi2]
  have hrk : ∀ c : F4, 3 ≤ (((Ŷ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) -
      Matrix.scalar (Fin 6) c).rank := by
    intro c
    apply three_le_rank
    by_cases hc1 : c = x1
    · rw [hc1]; exact finrank_ker_le_three_x1 hne hx12 r2 r1 hMY hs1
    · by_cases hc2 : c = x2
      · rw [hc2]; exact finrank_ker_le_three_x2 hne hx12 r1 r2 hMY hs2
      · exact finrank_ker_le_three hne hx12 r1 r2 hMY hNS hc1 hc2
  exact bot_of_perfect_rank hperf hŶU hŶ3 hJŶ hrk

end CFSG.LocalAnalysis.GLTheoremA.I269Six

end
