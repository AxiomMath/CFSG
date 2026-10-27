module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSocle
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorU
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitFour

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.HarrisLit.Hin

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem isComponentOf_map_conj_of_normal (hZ : center Y = ⊥) {τ : MulAut Y} {L : Subgroup Y}
    (hLC : L ≤ fixedPoints τ) (hLn : ∀ c ∈ fixedPoints τ, ∀ l ∈ L, c * l * c⁻¹ ∈ L)
    (hq : IsQuasisimple ↥L) :
    Assembly.IsComponentOf (L.map (MulAut.conj : Y →* MulAut Y))
      (centralizer ({τ} : Set (MulAut Y))) := by
  set L' := L.map (MulAut.conj : Y →* MulAut Y)
  set W := (MulAut.conj : Y →* MulAut Y).range
  set CA := centralizer ({τ} : Set (MulAut Y))
  have hL'CA : L' ≤ CA := by
    rintro _ ⟨l, hl, rfl⟩
    exact (conj_mem_centralizer_iff hZ τ l).mpr (hLC hl)
  have hL'W : L' ≤ W := map_le_range _ _
  have hn1 : (L'.subgroupOf (W ⊓ CA)).Normal := by
    rw [normal_subgroupOf_iff (le_inf hL'W hL'CA)]
    rintro _ k ⟨l, hl, rfl⟩ ⟨⟨y, rfl⟩, hy⟩
    have hyC : y ∈ fixedPoints τ := (conj_mem_centralizer_iff hZ τ y).mp hy
    refine ⟨y * l * y⁻¹, hLn y hyC l hl, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hn2 : ((W ⊓ CA).subgroupOf CA).Normal := by
    rw [normal_subgroupOf_iff inf_le_right]
    rintro h k ⟨hW, hCA⟩ hk
    exact ⟨(OuterAutomorphisms.inner_normal Y).conj_mem h hW k,
      CA.mul_mem (CA.mul_mem hk hCA) (CA.inv_mem hk)⟩
  have hsn : Assembly.IsSubnormal L' CA :=
    .step (le_inf hL'W hL'CA) hn1 (.step inf_le_right hn2 (.refl CA))
  have hq' : IsQuasisimple ↥L' := LocalCores.isQuasisimple_of_mulEquiv
    (L.equivMapOfInjective _ (conj_injective_of_center hZ)) hq
  exact ⟨hL'CA, hsn, (AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq'⟩

omit [Finite Y] in
theorem lieModel_map_conj (hZ : center Y = ⊥) {L : Subgroup Y} {p m : ℕ}
    (hLm : Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 2 p m) :
    Blueprint.LieModel (↥(L.map (MulAut.conj : Y →* MulAut Y)) ⧸
      center ↥(L.map (MulAut.conj : Y →* MulAut Y))) .PSL 2 p m ∧
      Nat.card ↥(center ↥(L.map (MulAut.conj : Y →* MulAut Y))) = Nat.card ↥(center ↥L) := by
  let eL : ↥L ≃* ↥(L.map (MulAut.conj : Y →* MulAut Y)) :=
    L.equivMapOfInjective _ (conj_injective_of_center hZ)
  have hc : (center ↥L).map (eL : ↥L →* ↥(L.map (MulAut.conj : Y →* MulAut Y))) =
      center ↥(L.map (MulAut.conj : Y →* MulAut Y)) := Subgroup.map_center_eq eL
  refine ⟨lieModel_psl2_of_mulEquiv (QuotientGroup.congr _ _ eL hc).symm hLm, ?_⟩
  rw [← hc, Subgroup.card_map_of_injective eL.injective]

theorem false_of_psl_ge_five_of_component [IsSimpleGroup Y] (hnab : ∃ a b : Y, a * b ≠ b * a)
    {n ℓ e : ℕ} (hn : 5 ≤ n) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hY : Assembly.LowTwoRank.StatedClassicalModel Y .PSL n ℓ e) {p m : ℕ} (hp2 : p ≠ 2)
    {τ : MulAut Y} (hτ : orderOf τ = 2) {L : Subgroup Y} (hLC : L ≤ fixedPoints τ)
    (hLn : ∀ c ∈ fixedPoints τ, ∀ l ∈ L, c * l * c⁻¹ ∈ L) (hq : IsQuasisimple ↥L)
    (hLm : Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 2 p m)
    (hodd : Odd (Nat.card ↥(center ↥L))) : False := by
  classical
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, hWn, -, -, hWC, -⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  have hF := CatLeaf.generalizedFitting_mulAut_eq_range hnab
  obtain ⟨⟨-, he, -⟩, k, _, _, hk, ⟨φ₀⟩⟩ := hY
  let φ : ↥(generalizedFitting (MulAut Y)) ≃* projectiveSL n k :=
    eW.symm.trans (φ₀.trans
      ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n k).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k)))
  have hZP := OddSelector.center_projectiveSL_eq_bot (k := k) (by omega : 3 ≤ n)
  obtain ⟨ρ, hinj, hρW, -, -⟩ := OutcomeLocal.socle_extension hWC φ hZP
  set L' := L.map (MulAut.conj : Y →* MulAut Y) with hL'
  have hL'W : L' ≤ generalizedFitting (MulAut Y) := hF ▸ map_le_range _ _
  obtain ⟨-, -, -, hL₁⟩ :=
    OddSelector.socle_images φ hinj hρW hL'W (isComponentOf_map_conj_of_normal hZ hLC hLn hq)
  obtain ⟨hLm', hcard⟩ := lieModel_map_conj hZ hLm
  have hsrc : Assembly.LowTwoRank.StatedClassicalModel (↥L' ⧸ center ↥L') .PSL 2 p m ∨
      Nonempty (↥L' ⧸ center ↥L' ≃* alternatingGroup (Fin 7)) ∨
      Assembly.LowTwoRank.StatedClassicalModel (↥L' ⧸ center ↥L') .PSL 3 2 2 :=
    Or.inl (statedPSL2_of_lieModel hLm')
  have hrank : Assembly.LowTwoRank.StatedClassicalModel (↥L' ⧸ center ↥L') .PSL 2 p m →
      2 ≤ CFSG.pRank 2 L' ∨ Odd (Nat.card (center ↥L')) :=
    fun _ => Or.inr (by rw [hcard]; exact hodd)
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) (n := n) (by omega)
  obtain ⟨B, σ, ε, hε, hρa⟩ := hform (ρ τ)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hρa
      obtain ⟨-, -, -, hm4⟩ := OddSelector.inner_case_reduction hτ (by omega) hℓ hℓ2 he hk hinj
        hL₁ hρa hp2 hsrc hrank
      omega
    · exact OddSelector.field_case_false hτ (by omega) hℓ hℓ2 he hk hinj hL₁ hσ hρa hp2 hsrc
  · rw [pow_one] at hρa
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hρa
      have hα2 : (conjAut n k B * dualAut n k) ^ 2 = 1 := by
        rw [← hρa, ← map_pow, ← hτ, pow_orderOf_eq_one, map_one]
      rcases OddSelector.transpose_eq_or_eq_neg_of_pureGraph (by omega) B hα2 with hB | hB
      · exact OddSelector.orthogonal_case_false hn hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc
      · exact OddSelector.symplectic_case_false (by omega) hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc
    · exact OddSelector.graph_field_case_false hτ (by omega) hℓ hℓ2 he hk hinj hL₁ hσ hρa hp2
        hsrc

theorem false_of_psu_ge_five_of_component [IsSimpleGroup Y] (hnab : ∃ a b : Y, a * b ≠ b * a)
    {n ℓ e : ℕ} (hn : 5 ≤ n) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hY : Assembly.LowTwoRank.StatedClassicalModel Y .PSU n ℓ e) {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 1 ≤ m) (h5 : 5 ≤ p ^ m) {τ : MulAut Y} (hτ : orderOf τ = 2)
    {L : Subgroup Y} (hLC : L ≤ fixedPoints τ)
    (hLn : ∀ c ∈ fixedPoints τ, ∀ l ∈ L, c * l * c⁻¹ ∈ L) (hq : IsQuasisimple ↥L)
    (hLm : Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 2 p m)
    (hodd : Odd (Nat.card ↥(center ↥L))) : False := by
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, hWn, hWs, hWnab, hWC, -⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  have hF := CatLeaf.generalizedFitting_mulAut_eq_range hnab
  have hM : Blueprint.LieModel ↥(generalizedFitting (MulAut Y)) .PSU n ℓ e :=
    LieType.CurtisTits.lieModel_of_mulEquiv eW (Or.inl ⟨by simp [Blueprint.classicalTags], hY⟩)
  have hL'W : L.map (MulAut.conj : Y →* MulAut Y) ≤ generalizedFitting (MulAut Y) :=
    hF ▸ map_le_range _ _
  obtain ⟨hLm', hcard⟩ := lieModel_map_conj hZ hLm
  have hsrc : RestrictedStd.SmallSource (L.map (MulAut.conj : Y →* MulAut Y)) :=
    Or.inl ⟨p, m, hp, hp2, hm, h5, hLm', by rw [hcard]; exact hodd⟩
  exact OddClassSelector.su_family_false hWs hWnab hWC hτ hL'W
    (isComponentOf_map_conj_of_normal hZ hLC hLn hq) hsrc hℓ hℓ2 he hn hM

end CFSG.ComponentClassification.HarrisLit.N36
