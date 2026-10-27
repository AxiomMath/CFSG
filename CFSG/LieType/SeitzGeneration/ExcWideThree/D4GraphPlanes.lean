module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNFDefs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4GraphFieldNF
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Families

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.Fischer CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

section GraphPlanes


theorem exists_inner_ne_one_of_graph {K : Type} [Field K] [Finite K]
    {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} [hE : CFSG.IsElementaryAbelian 3 ↥E]
    (hEc : Nat.card ↥E = 3 ^ 2)
    (hG : ∀ α ∈ E, α ∉ innerAut (adjointGroup Tag.D4 K) →
      D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1)
    {β : MulAut ↥(adjointGroup Tag.D4 K)} (hβE : β ∈ E) {ε₀ : ℕ}
    (hε₀ : ε₀ = 1 ∨ ε₀ = 2) (hβ : HasNF β ε₀ 1) :
    ∃ ι ∈ E, ι ≠ 1 ∧ ι ∈ inner (adjointGroup Tag.D4 K) := by
  classical
  have hβ3 : β ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian β hβE
  obtain ⟨x, hxE, hxβ⟩ : ∃ x ∈ E, x ∉ Subgroup.zpowers β := by
    by_contra h
    push Not at h
    have hle : E ≤ Subgroup.zpowers β := fun x hx => h x hx
    have h1 : Nat.card E ∣ Nat.card (Subgroup.zpowers β) := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, hEc] at h1
    have h2 := h1.trans (orderOf_dvd_of_pow_eq_one hβ3)
    have h3 := Nat.le_of_dvd (by norm_num) h2
    norm_num at h3
  have hx3 : x ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian x hxE
  by_cases hxin : x ∈ inner (adjointGroup Tag.D4 K)
  · exact ⟨x, hxE, fun h => hxβ (h ▸ one_mem _), hxin⟩
  obtain ⟨g, a, σ, ε, hε, hσ3, ⟨hε0, hσ1⟩, hxeq⟩ := hG x hxE hxin
  subst hσ1
  have hxNF : HasNF x ε 1 := ⟨g, a, hxeq⟩
  obtain ⟨y, hyE, hyNF, hyβ⟩ : ∃ y ∈ E, HasNF y 0 1 ∧ (y = 1 → x ∈ Subgroup.zpowers β) := by
    by_cases hεε : ε₀ = ε
    · refine ⟨β * (x * x), E.mul_mem hβE (E.mul_mem hxE hxE), ?_, ?_⟩
      · have h := hβ.mul (hxNF.mul hxNF)
        have h' := h.mod_three
        rw [show (ε₀ + (ε + ε)) % 3 = 0 by omega] at h'
        simpa only [mul_one] using h'
      · intro hy
        have h1 : x * x = β⁻¹ := eq_inv_of_mul_eq_one_right hy
        have h2 : x = β⁻¹ * β⁻¹ := by
          have h3 : x * (x * x) = 1 := by rw [← pow_three]; exact hx3
          calc x = 1 * x := (one_mul x).symm
            _ = x * (x * x) * x := by rw [h3]
            _ = x * x * (x * x) := by group
            _ = β⁻¹ * β⁻¹ := by rw [h1]
        rw [h2]
        exact mul_mem (Subgroup.inv_mem _ (Subgroup.mem_zpowers β))
          (Subgroup.inv_mem _ (Subgroup.mem_zpowers β))
    · refine ⟨β * x, E.mul_mem hβE hxE, ?_, ?_⟩
      · have h' := (hβ.mul hxNF).mod_three
        have h3 : ε₀ + ε = 3 := by omega
        rw [h3, show 3 % 3 = 0 from rfl] at h'
        simpa only [mul_one] using h'
      · intro hy
        have h1 : x = β⁻¹ := eq_inv_of_mul_eq_one_right hy
        rw [h1]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers β)
  obtain ⟨g', a', hy⟩ := hyNF
  have hy3 : y ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian y hyE
  refine ⟨y, hyE, fun h => hxβ (hyβ h), ?_⟩
  rw [hy]
  exact mem_inner_of_normal_form_one g' a' (hy ▸ hy3)

end GraphPlanes

section Statements


@[expose] def D4ThreeGraphPlanesOdd : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 5 ≤ ringChar K →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (adjointGroup Tag.D4 K) →
      (∀ α ∈ E, α ∉ innerAut (adjointGroup Tag.D4 K) →
        D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) →
      Subgroup.closure (fixUnion E) = ⊤

@[expose] def D4ThreeGraphPlanesEven : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K = 2 →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (adjointGroup Tag.D4 K) →
      (∀ α ∈ E, α ∉ innerAut (adjointGroup Tag.D4 K) →
        D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) →
      Subgroup.closure (fixUnion E) = ⊤

theorem d4ThreeGraphPlanes_of_odd_even (ho : D4ThreeGraphPlanesOdd) (he : D4ThreeGraphPlanesEven) :
    D4ThreeGraphPlanes := by
  intro K _ _ hK3 E hE hc hout hG
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, -⟩ := FiniteField.card K (ringChar K)
  have h2 := hpr.two_le
  have h4 : ringChar K ≠ 4 := fun h => by rw [h] at hpr; exact absurd hpr (by norm_num)
  by_cases hp2 : ringChar K = 2
  · exact he K hp2 E hE hc hout hG
  · exact ho K (by omega) E hE hc hout hG

@[expose] def D4GraphPairGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 5 ≤ ringChar K →
    ∀ α : MulAut ↥(adjointGroup Tag.D4 K), α ^ 3 = 1 →
      (D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) →
      ∀ x : ↥(adjointGroup Tag.D4 K), x ^ 3 = 1 → x ≠ 1 → α x = x →
        Subgroup.closure ((Subgroup.centralizer ({x} : Set ↥(adjointGroup Tag.D4 K)) :
          Set ↥(adjointGroup Tag.D4 K)) ∪ (fixedSubgroup α : Set ↥(adjointGroup Tag.D4 K))) = ⊤

theorem d4ThreeGraphPlanesOdd_of_pair (h : D4GraphPairGen) : D4ThreeGraphPlanesOdd := by
  intro K _ _ hK5 E hE hc hout hG
  classical
  haveI : CFSG.IsElementaryAbelian 3 ↥E := hE
  have hZ : Subgroup.center ↥(adjointGroup Tag.D4 K) = ⊥ := center_adjointGroup_eq_bot
  have hinj : Function.Injective (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
      MulAut ↥(adjointGroup Tag.D4 K)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center ↥(adjointGroup Tag.D4 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 K) => φ y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = g * (g⁻¹ * y * g) := by group
        _ = g * y := by
          have h2 : g * y * g⁻¹ = y := this
          have h3 : g⁻¹ * y * g = y := by
            calc g⁻¹ * y * g = g⁻¹ * (g * y * g⁻¹) * g := by rw [h2]
              _ = y := by group
          rw [h3]
    rw [hZ] at hgc
    exact hgc
  obtain ⟨β, hβE, hβout⟩ : ∃ β ∈ E, β ∉ innerAut (adjointGroup Tag.D4 K) := by
    by_contra hcon
    push Not at hcon
    exact hout hcon
  have hβ3 : β ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian β hβE
  have hβ1 : β ≠ 1 := fun h' => hβout (h' ▸ one_mem _)
  obtain ⟨g, a, σ, ε, hε, hσ3, ⟨hε0, hσ1⟩, hβeq⟩ := hG β hβE hβout
  subst hσ1
  have hβNF : HasNF β ε 1 := ⟨g, a, hβeq⟩
  obtain ⟨ι, hιE, hι1, hιin⟩ := exists_inner_ne_one_of_graph hc hG hβE (by omega) hβNF
  obtain ⟨x, rfl⟩ := hιin
  have hι3 : MulAut.conj x ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian _ hιE
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, hι3, map_one])
  have hx1 : x ≠ 1 := fun h' => hι1 (by rw [h', map_one])
  have hβx : β x = x := by
    have h1 := elemAb_comm hE _ hβE _ hιE
    have h2 : β * MulAut.conj x * β⁻¹ = MulAut.conj (β x) := by
      ext y
      simp [MulAut.mul_apply, MulAut.conj_apply]
    apply hinj
    rw [← h2, h1, mul_inv_cancel_right]
  have hpair := h K hK5 β hβ3 ⟨g, a, 1, ε, hε, hσ3, ⟨hε0, rfl⟩, hβeq⟩ x hx3 hx1 hβx
  rw [eq_top_iff]
  rw [eq_top_iff] at hpair
  refine hpair.trans (Subgroup.closure_le _ |>.2 ?_)
  rintro w (hw | hw)
  · refine Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hιE hι1 ?_)
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hw
    show x * w * x⁻¹ = w
    rw [← h1, mul_inv_cancel_right]
  · exact Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hβE hβ1 hw)

end Statements

end CFSG.LieType.SeitzGeneration.ExcWideThree
