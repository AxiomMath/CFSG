module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.GraphFree
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.GraphEven
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.Select.Borel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RepNontriv
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SpecialLinear
open scoped MatrixGroups

theorem psl_linear_core {m f r : ℕ} (hm : 5 ≤ m) (hr : r.Prime) (hr2 : r ≠ 2) (hrm : r ∣ m)
    (hrq : r ∣ 2 ^ f - 1) :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
      ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
        (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K) W),
        ρ.IsIrreducible →
        (∀ g, ρ g = 1 → g ∈ LinearFlag.scalars m K) →
        (∀ (c : Kˣ) (hc : c ^ m = 1), c ^ r = 1 →
          ρ (LinearFlag.scalarElement c hc) = 1) →
        ∀ A : Subgroup (W ≃ₗ[ZMod 2] W), A ≠ ⊥ → CFSG.IsElementaryAbelian 2 ↥A →
          (∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w) →
          (∀ a ∈ A, ∀ x, ∃ y, ∀ w, a (ρ x w) = ρ y (a w)) →
          Nat.card ↥A * Nat.card {w : W // ∀ a ∈ A, a w = w} < Nat.card W := by
  classical
  intro K _ _ _ hK W _ _ _ ρ hirr hker hscal A hA1 hAel hquad hint
  by_contra hnot
  push Not at hnot
  obtain ⟨D, hDA, hD1, hoffD, hbest, hered⟩ :=
    exists_best_le (W := W) hA1 hAel hnot
  have hcommA := commute_of_mem_offender (m := m) (by omega : 3 ≤ m) hirr hA1 hAel hquad hint hnot
  have hcommD : ∀ d ∈ D, ∀ g : W →ₗ[ZMod 2] W,
      (∀ h, g ∘ₗ ρ h = ρ h ∘ₗ g) →
      (d : W →ₗ[ZMod 2] W) ∘ₗ g = g ∘ₗ (d : W →ₗ[ZMod 2] W) :=
    fun d hd => hcommA d (hDA hd)
  have hDel : CFSG.IsElementaryAbelian 2 ↥D := hAel.of_le hDA
  have hquadD : ∀ a ∈ D, ∀ b ∈ D, ∀ w, b (a w - w) = a w - w :=
    fun a ha b hb => hquad a (hDA ha) b (hDA hb)
  obtain ⟨x, hx⟩ := exists_borel_conj (by omega : 3 ≤ m) hker hint hAel D hDA
  let ρ' : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K) W :=
    ρ.comp (MulAut.conj x).toMonoidHom
  have hρ' : ∀ g, ρ' g = ρ (x * g * x⁻¹) := by
    intro g
    change ρ ((MulAut.conj x) g) = _
    rw [MulAut.conj_apply]
  have hρback : ∀ g, ρ' (x⁻¹ * g * x) = ρ g := by
    intro g
    rw [hρ' (x⁻¹ * g * x)]
    congr 1
    group
  have hirr' : ρ'.IsIrreducible := by
    have hnt : Nontrivial W :=
      ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).1
    rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
    refine ⟨hnt, fun U hU => ?_⟩
    have hUρ : ∀ g, ∀ u ∈ U, ρ g u ∈ U := by
      intro g u hu
      rw [← hρback g]
      exact hU (x⁻¹ * g * x) u hu
    exact ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).2 U hUρ
  have hker' : ∀ g, ρ' g = 1 → g ∈ LinearFlag.scalars m K := by
    intro g hg
    rw [LinearFlag.scalars_eq_center]
    have hg' : ρ (x * g * x⁻¹) = 1 := by
      rw [← hρ' g]
      exact hg
    have hc : x * g * x⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K) := by
      rw [← LinearFlag.scalars_eq_center]
      exact hker (x * g * x⁻¹) hg'
    have hconj :=
      (inferInstance : (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K)).Normal).conj_mem
        (x * g * x⁻¹) hc x⁻¹
    have hconj' : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
    rwa [hconj'] at hconj
  have hscal' : ∀ (c : Kˣ) (hc : c ^ m = 1), c ^ r = 1 →
      ρ' (LinearFlag.scalarElement c hc) = 1 := by
    intro c hc hcr
    have hcent : LinearFlag.scalarElement c hc ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K) :=
      LinearFlag.scalars_le_center m K (LinearFlag.scalarElement_mem_scalars c hc)
    have hxscalar : x * LinearFlag.scalarElement c hc =
        LinearFlag.scalarElement c hc * x :=
      (Subgroup.mem_center_iff.mp hcent) x
    have hx1 : x * LinearFlag.scalarElement c hc * x⁻¹ =
        LinearFlag.scalarElement c hc := by
      rw [hxscalar]
      group
    rw [hρ' (LinearFlag.scalarElement c hc), hx1]
    exact hscal c hc hcr
  have hcomm' : ∀ d ∈ D, ∀ g : W →ₗ[ZMod 2] W,
      (∀ h, g ∘ₗ ρ' h = ρ' h ∘ₗ g) →
      (d : W →ₗ[ZMod 2] W) ∘ₗ g = g ∘ₗ (d : W →ₗ[ZMod 2] W) := by
    intro d hd g hg
    refine hcommD d hd g (fun h => ?_)
    rw [← hρback h]
    exact hg (x⁻¹ * h * x)
  have hcompat' : ∀ d ∈ D, ∃ B : GL (Fin m) K, IsUpperGL B ∧
      ∃ (τ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧ ∀ g w,
        d (ρ' g w) = ρ' (borelStd m K B τ ε g) (d w) := by
    intro d hd
    obtain ⟨B, hB, τ, ε, hε, h⟩ := hx d hd
    refine ⟨B, hB, τ, ε, hε, fun g w => ?_⟩
    simpa only [hρ' g, hρ' (borelStd m K B τ ε g)] using h g w
  have hcompatD : ∀ d ∈ D, ∃ B : GL (Fin m) K, IsUpperGL B ∧
      ∃ (τ : K ≃+* K) (ε : ℕ), ∀ g w,
        d (ρ' g w) = ρ' (borelStd m K B τ ε g) (d w) := by
    intro d hd
    obtain ⟨B, hB, τ, ε, -, h⟩ := hcompat' d hd
    exact ⟨B, hB, τ, ε, h⟩
  have hne' : ∃ g, ρ' g ≠ 1 := by
    by_contra h
    push Not at h
    have hρtriv : ∀ g, ρ g = 1 := by
      intro g
      have h1 := h (x⁻¹ * g * x)
      rwa [hρback g] at h1
    obtain ⟨e⟩ :=
      @CFSG.LocalAnalysis.RankThreeUC.S15.equiv_trivial_of_trivial_isIrreducible
        (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K) _ _ W _ _
        (Module.Finite.of_finite) ρ hirr hρtriv
    let E := e.toLinearEquiv
    have hGL : ∀ a : W ≃ₗ[ZMod 2] W, a = 1 := by
      intro a
      let v : W := E.symm 1
      have hv : v ≠ 0 := by
        intro h0
        have h1 : E v = 1 := E.apply_symm_apply 1
        rw [h0, map_zero] at h1
        exact zero_ne_one h1
      have hav : a v = v := by
        have hne : E (a v) ≠ 0 := by
          intro h0
          have hav0 : a v = 0 := E.injective (by rw [h0, map_zero])
          exact hv (a.injective (by simpa using hav0))
        have h01 : E (a v) = 0 ∨ E (a v) = 1 :=
          CFSG.GroupTheory.GLnTwoSplitting.zmod_two_eq_zero_or_one _
        rcases h01 with h0 | h1
        · exact absurd h0 hne
        · apply E.injective
          rw [h1]
          exact (E.apply_symm_apply 1).symm
      apply LinearEquiv.ext
      intro w
      have hw : w = (E w) • v := by
        apply E.injective
        rw [map_smul, E.apply_symm_apply]
        simp
      calc a w = a ((E w) • v) := congrArg a hw
        _ = (E w) • a v := map_smul a _ _
        _ = (E w) • v := by rw [hav]
        _ = w := hw.symm
    apply hA1
    rw [Subgroup.eq_bot_iff_forall]
    intro a _
    exact hGL a
  have hf1 : 1 ≤ f := by
    by_contra hf0
    have hf : f = 0 := by omega
    subst f
    norm_num at hK
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hf2 : 2 ≤ f := by
    by_contra hf2
    have hf : f = 1 := by omega
    subst f
    norm_num at hrq
    exact hr.ne_one hrq
  have hFintype : Fintype K := Fintype.ofFinite K
  have hKF : Fintype.card K = 2 ^ f := by
    rw [Fintype.card_eq_nat_card]
    exact hK
  have hK4 : 4 ≤ Fintype.card K := by
    rw [hKF]
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) hf2
    norm_num at hpow ⊢
    exact hpow
  by_cases hgraph : ∃ d ∈ D, ∃ B : GL (Fin m) K, IsUpperGL B ∧ ∃ τ : K ≃+* K,
      ∀ g w, d (ρ' g w) = ρ' (borelStd m K B τ 1 g) (d w)
  · obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
    · have hk3 : 3 ≤ k := by omega
      set j := k - 3 with hj
      have hmj : m = 2 * j + 6 := by omega
      clear hk
      subst m
      exact graph_even_false j hK4 ρ' hirr' hne' D hDel hquadD hcomm' hcompatD hgraph hered
    · have hk2 : 2 ≤ k := by omega
      set j := k - 1 with hj
      have hmj : m = 2 * j + 3 := by omega
      clear hk
      subst m
      exact graph_odd_false j hK4 ρ' hirr' hne' D hDel hquadD hcomm' hcompatD hgraph hered
  · have hcompat0 : ∀ d ∈ D, ∃ B : GL (Fin m) K, IsUpperGL B ∧
        ∃ τ : K ≃+* K, ∀ g w,
          d (ρ' g w) = ρ' (borelStd m K B τ 0 g) (d w) := by
      intro d hd
      obtain ⟨B, hB, τ, ε, hε, h⟩ := hcompat' d hd
      have hε0 : ε = 0 := by
        by_contra hne
        have hε1 : ε = 1 := by omega
        exact hgraph ⟨d, hd, B, hB, τ, by simpa [hε1] using h⟩
      refine ⟨B, hB, τ, fun g w => ?_⟩
      simpa [hε0] using h g w
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
    · have hk3 : 3 ≤ k := by omega
      set j := k - 3 with hj
      have hmj : m = 2 * j + 6 := by omega
      clear hk
      subst m
      have hrn : r ∣ (2 * j + 5) + 1 := by simpa using hrm
      exact graph_free_false (n := 2 * j + 5) (by omega) hKF hr hr2 hrn hrq ρ' hirr' hne'
        hker' hscal' D hD1 hDel hquadD hcomm' hcompat0 hoffD hbest hered
    · have hk2 : 2 ≤ k := by omega
      set j := k - 1 with hj
      have hmj : m = 2 * j + 3 := by omega
      clear hk
      subst m
      have hrn : r ∣ (2 * j + 2) + 1 := by simpa using hrm
      exact graph_free_false (n := 2 * j + 2) (by omega) hKF hr hr2 hrn hrq ρ' hirr' hne'
        hker' hscal' D hD1 hDel hquadD hcomm' hcompat0 hoffD hbest hered

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
