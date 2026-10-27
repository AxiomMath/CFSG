module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisPeel
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Module CFSG.RankThree.PartOne.KCLinPlane

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem eq_top_of_peel [FiniteDimensional K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (f : ι → Module.End K V) (hidem : ∀ i, f i * f i = f i)
    (horth : ∀ i j, i ≠ j → f i * f j = 0) (hsum : ∑ i, f i = 1)
    (hdim : ∀ i, 2 ≤ finrank K (LinearMap.range (f i))) (G : Subgroup (V ≃ₗ[K] V))
    (hG : ∀ g ∈ G, LinearEquiv.det g = 1) (hsupp : ∀ i, suppGroup (f i) ≤ G)
    (hx : ∀ r s, r ≠ s → ∃ j, j ≠ r ∧ j ≠ s ∧ ∃ x ∈ G, ∃ β : Module.End K V,
      (∀ v, x v = v + β v) ∧ (∀ v, β (β v) = 0) ∧ (∀ v, f r (β (f j v)) = β (f j v)) ∧
      (∀ v, f j (β v) = f j (β (f s v))) ∧ ∃ a, f j a = a ∧ ∃ α : Module.Dual K V,
        (∀ v, α (f j v) = α v) ∧ α a = 0 ∧ β a ≠ 0 ∧ ∃ u, α (β u) ≠ 0) :
    ∀ g : V ≃ₗ[K] V, LinearEquiv.det g = 1 → g ∈ G := by
  classical
  have hidem' : ∀ i v, f i (f i v) = f i v := fun i v => idem_apply (hidem i) v
  have horth' : ∀ i j, i ≠ j → ∀ v, f i (f j v) = 0 := fun i j hij v => orth_apply (horth i j hij) v
  let e : Option ι → Module.End K V := fun o => o.elim 0 f
  have he_none : e none = 0 := rfl
  have he_some : ∀ i, e (some i) = f i := fun _ => rfl
  have hidemE : ∀ i, e i * e i = e i := by
    rintro (_ | i)
    · rw [he_none, mul_zero]
    · rw [he_some]; exact hidem i
  have horthE : ∀ i j, i ≠ j → e i * e j = 0 := by
    rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · rw [he_none, zero_mul]
    · rw [he_none, mul_zero]
    · rw [he_some, he_some]
      exact horth i j (fun h => hij (congrArg some h))
  have hsumE : ∑ i, e i = 1 := by
    rw [Fintype.sum_option, he_none, zero_add]
    simpa only [he_some] using hsum
  set A : Finset (Option ι) := Finset.univ.filter (fun o => o ≠ none) with hA
  have hzA : (none : Option ι) ∉ A := by simp [hA]
  have hmemA : ∀ i : ι, some i ∈ A := fun i => by simp [hA]
  have hAne : A.Nonempty := ⟨some (Classical.arbitrary ι), hmemA _⟩
  have hinact : ∀ i, i ≠ none → i ∉ A → e i = 0 := by
    intro i hi hiA
    exact absurd (by simp [hA, hi]) hiA
  have hdimE : ∀ i ∈ A, 2 ≤ finrank K (LinearMap.range (e i)) := by
    rintro (_ | i) hi
    · exact absurd hi hzA
    · exact hdim i
  have hsuppE : ∀ i ∈ A, suppGroup (e none + e i) ≤ G := by
    rintro (_ | i) hi
    · exact absurd hi hzA
    · rw [he_none, zero_add, he_some]; exact hsupp i
  have hmixE : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∃ β : Module.End K V, e i * β = β ∧ β * e j = β ∧
      β ≠ 0 ∧ ∃ u ∈ G, ∀ v, u v = v + β v := by
    rintro (_ | r) hi (_ | s) hj hij
    · exact absurd hi hzA
    · exact absurd hi hzA
    · exact absurd hj hzA
    have hrs : r ≠ s := fun h => hij (by rw [h])
    obtain ⟨j, hjr, hjs, x, hxG, β, hxβ, hββ, hβ1, hβ2, a, ha, α, hα, hαa, hβa, hαβ⟩ := hx r s hrs
    obtain ⟨w, hw, hw0, φ, hφ, hφ0, hTv⟩ := exists_mixing_of_homog f hidem' horth' hdim hsupp hjr hjs
      hrs hxG hxβ hββ hβ1 hβ2 ha hα hαa hβa hαβ
    obtain ⟨-, u, hu, huv⟩ := hTv
    refine ⟨φ.smulRight w, ?_, ?_, ?_, u, hu, fun v => ?_⟩
    · refine LinearMap.ext fun v => ?_
      change f r (φ v • w) = φ v • w
      rw [map_smul, hw]
    · refine LinearMap.ext fun v => ?_
      change φ (f s v) • w = φ v • w
      rw [hφ]
    · intro h0
      obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hφ0 (LinearMap.ext hcon)
      have := LinearMap.congr_fun h0 v
      exact hw0 ((smul_eq_zero.1 this).resolve_left hv)
    · rw [huv]
      rfl
  exact generation_of_blocks e hidemE horthE hsumE none A hzA hAne hinact hdimE G hG hsuppE hmixE

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
