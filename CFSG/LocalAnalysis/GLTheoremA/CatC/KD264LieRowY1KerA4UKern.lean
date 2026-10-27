module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4UPsl
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4UBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.GLTheoremA.KD264LieA4

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def psiU (h : UnitaryFieldData p f K) :
    unitarySU p f K 2 →* StatedProj (unitarySU p f K 4) :=
  (piU K p f).comp (embU h)

theorem psiU_injective (h : UnitaryFieldData p f K) :
    Function.Injective (psiU h) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  obtain ⟨u, hu⟩ := scalar_of_piU_eq_one hB
  have hmat : embM ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.scalar (Fin 4) (u : K) := by
    have := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) hu
    rw [Matrix.GeneralLinearGroup.coe_scalar] at this
    exact this
  have hu1 : (u : K) = 1 := by
    have h22 := congrFun (congrFun hmat 2) 2
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h22
    simp only [embM] at h22
    simpa using h22.symm
  have hB1 : ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    apply eq_one_of_embM_eq_one
    rw [hmat, hu1]
    ext i j
    simp [Matrix.scalar_apply]
  apply Subtype.ext
  apply Units.ext
  exact hB1

theorem embU_comm_F0U (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1)
    (B : unitarySU p f K 2) {x : unitarySU p f K 4} (hx : x ∈ F0U h hdiv) :
    embU h B * x = x * embU h B := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
  have hd01 : d.1 0 = d.1 1 := hd
  apply Subtype.ext
  apply Units.ext
  show embM ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * diagM K d.1 =
    diagM K d.1 * embM ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  unfold diagM
  exact embM_mul_diagonal _ _ (by simp only [hd01])

theorem exists_sq_ne_one_of_card (F : Type) [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Fintype F := Fintype.ofFinite F
  have hsub : (Finset.univ : Finset F) ⊆ ({0, 1, -1} : Finset F) := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have h2 := hcon a ha
      rw [pow_two] at h2
      rcases mul_self_eq_one_iff.mp h2 with h1 | h1
      · simp [h1]
      · simp [h1]
  have h1 := Finset.card_le_card hsub
  have h3 : ({0, 1, -1} : Finset F).card ≤ 3 := Finset.card_le_three
  rw [Finset.card_univ] at h1
  rw [Nat.card_eq_fintype_card] at h4
  omega

theorem isQuasisimple_SL2_field (F : Type) [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨a, ha0, ha2⟩ := exists_sq_ne_one_of_card F h4
  exact ⟨Matrix.SL2.commutator_eq_top ha0 ha2,
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' ⟨a, ha0, ha2⟩⟩

theorem sq_eq_one_of_mem_center_SL2 (F : Type) [Field F] {c : Matrix.SpecialLinearGroup (Fin 2) F}
    (hc : c ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) : c ^ 2 = 1 := by
  obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  simp only [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrc, ← map_pow, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem A0U_pow_three (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) : A0U h hdiv hζ ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show ((A0GL hζ ^ 3 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
  rw [Units.val_pow_eq_pow_val, show ((A0GL hζ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    Matrix.diagonal ![ζ, ζ ^ 2] from rfl, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simpa using hζ.pow_eq_one
  · have h6 : (ζ ^ 2) ^ 3 = 1 := by
      calc (ζ ^ 2) ^ 3 = (ζ ^ 3) ^ 2 := by ring
        _ = 1 := by rw [hζ.pow_eq_one, one_pow]
    simpa using h6

theorem A0U_ne_one (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) : A0U h hdiv hζ ≠ 1 := by
  intro h1
  have h00 := congrArg (fun g : unitarySU p f K 2 => ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) h1
  have hζ1 : ζ ≠ 1 := by
    simpa using hζ.pow_ne_one_of_pos_of_lt (l := 1) one_ne_zero (by norm_num)
  apply hζ1
  simpa [A0U, A0GL] using h00

theorem kerConcl_diagonalU [Finite K] (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {F : Type} [Field F] [Finite F]
    (eSL : Matrix.SpecialLinearGroup (Fin 2) F ≃* unitarySU p f K 2) (hF : 4 ≤ Nat.card F) :
    KerConcl ((DiagSU h hdiv).map (piU K p f)) := by
  unfold KerConcl
  let g : F0U h hdiv →* StatedProj (unitarySU p f K 4) := (piU K p f).comp (F0U h hdiv).subtype
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (piU_injOn_F0U h hdiv x.1 x.2 hx)
  have hHC : (psiU h).range ≤
      Subgroup.centralizer (g.range : Set (StatedProj (unitarySU p f K 4))) := by
    intro c hc
    obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hc
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hs
    show piU K p f x.1 * piU K p f (embU h B) = piU K p f (embU h B) * piU K p f x.1
    rw [← map_mul, ← map_mul, embU_comm_F0U h hdiv B x.2]
  refine ⟨g.range, ?_, ?_, (psiU h).range, hHC, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    exact Subgroup.mem_map.mpr ⟨x.1, F0U_le_DiagSU h hdiv x.2, rfl⟩
  · rw [Nat.card_congr (MonoidHom.ofInjective hginj).symm.toEquiv]
    exact card_F0U h hdiv hζ
  · refine CFSG.Open.IsSubnormal.step hHC ?_ (CFSG.Open.IsSubnormal.refl _)
    constructor
    intro n hn c
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨B, hB⟩ := MonoidHom.mem_range.mp hn
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (c : StatedProj (unitarySU p f K 4))
    have hy' : piU K p f y = (c : StatedProj (unitarySU p f K 4)) := hy
    have hc := Subgroup.mem_centralizer_iff.mp c.2 (piU K p f (tEltU h hdiv hζ))
      (MonoidHom.mem_range.mpr ⟨⟨tEltU h hdiv hζ, tEltU_mem h hdiv hζ⟩, rfl⟩)
    rw [← hy'] at hc
    have hyt : y * tEltU h hdiv hζ = tEltU h hdiv hζ * y :=
      comm_of_piU_comm h (F0U_pow_three h hdiv (tEltU_mem h hdiv hζ)) hc.symm
    have hcomm : ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        Matrix.diagonal ![1, 1, ζ, ζ ^ 2] = Matrix.diagonal ![1, 1, ζ, ζ ^ 2] *
          ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      have hm := congrArg (fun z : unitarySU p f K 4 =>
        ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hyt
      simp only [Subgroup.coe_mul, Units.val_mul] at hm
      rw [← tEltU_matrix h hdiv hζ]
      exact hm
    obtain ⟨B', hB'⟩ := embU_conj_mem h hζ y.2 hcomm B
    have hB'' : embU h B' = y * embU h B * y⁻¹ :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]; exact hB')
    refine MonoidHom.mem_range.mpr ⟨B', ?_⟩
    show piU K p f (embU h B') = _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hB, ← hy']
    show piU K p f (embU h B') = piU K p f y * piU K p f (embU h B) * (piU K p f y)⁻¹
    rw [hB'', map_mul, map_mul, map_inv]
  · have eH : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(psiU h).range :=
      eSL.trans (MonoidHom.ofInjective (psiU_injective h))
    exact isQuasisimple_equiv eH (isQuasisimple_SL2_field F hF)
  · have eH : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(psiU h).range :=
      eSL.trans (MonoidHom.ofInjective (psiU_injective h))
    rw [← card_quotient_center_equiv eH]
    set a0 := eSL.symm (A0U h hdiv hζ) with ha0def
    have ha3 : a0 ^ 3 = 1 := by
      rw [ha0def, ← map_pow, A0U_pow_three h hdiv hζ, map_one]
    have hnc : a0 ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      intro hc
      have hsq := sq_eq_one_of_mem_center_SL2 F hc
      have hA2 : A0U h hdiv hζ ^ 2 = 1 := by
        have h1 : eSL a0 ^ 2 = 1 := by rw [← map_pow, hsq, map_one]
        rwa [ha0def, MulEquiv.apply_symm_apply] at h1
      have hA1 : A0U h hdiv hζ = 1 := by
        have h3 := A0U_pow_three h hdiv hζ
        calc A0U h hdiv hζ = (A0U h hdiv hζ) ^ 3 * ((A0U h hdiv hζ) ^ 2)⁻¹ := by group
          _ = 1 := by rw [h3, hA2, inv_one, mul_one]
      exact A0U_ne_one h hdiv hζ hA1
    have hq1 : QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) a0 ≠ 1 :=
      fun hq => hnc ((QuotientGroup.eq_one_iff a0).mp hq)
    have hq3 : (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) a0) ^ 3
        = 1 := by
      rw [← map_pow, ha3, map_one]
    have hord := orderOf_eq_prime hq3 hq1
    have hdvd := orderOf_dvd_natCard
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) a0)
    rwa [hord] at hdvd

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
