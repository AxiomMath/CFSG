module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthEigen
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Block

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ClassicalInvolution.ModelFacts

section Field

variable {K : Type} [Field K] [Finite K]

theorem eq_one_or_eq_neg_one_of_card_three (hK : Nat.card K = 3) {x : K} (hx : x ≠ 0) :
    x = 1 ∨ x = -1 := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rw [← Nat.card_eq_fintype_card, hK] at h
  have h2 : (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h | h
  · left
    linear_combination h
  · right
    linear_combination h

theorem mul_self_ne_neg_one_of_card_three (hK : Nat.card K = 3) (c : K) : c * c ≠ -1 := by
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  intro h
  by_cases hc : c = 0
  · rw [hc, zero_mul] at h
    exact one_ne_zero (by linear_combination h : (1 : K) = 0)
  · rcases eq_one_or_eq_neg_one_of_card_three hK hc with rfl | rfl
    · exact h2 (by linear_combination h)
    · exact h2 (by linear_combination h)

theorem not_isSquare_neg_one_of_card_three (hK : Nat.card K = 3) : ¬ IsSquare (-1 : K) := by
  rintro ⟨c, hc⟩
  exact mul_self_ne_neg_one_of_card_three hK c hc.symm

theorem add_eq_zero_or_of_card_three (hK : Nat.card K = 3) {a b c : K} (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) : a + b = 0 ∨ a + c = 0 ∨ a + b + c = 0 := by
  obtain ⟨h3, -⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  rcases eq_one_or_eq_neg_one_of_card_three hK ha with rfl | rfl <;>
  rcases eq_one_or_eq_neg_one_of_card_three hK hb with rfl | rfl <;>
  rcases eq_one_or_eq_neg_one_of_card_three hK hc with rfl | rfl
  · exact Or.inr (Or.inr (by linear_combination h3))
  · exact Or.inr (Or.inl (by ring))
  · exact Or.inl (by ring)
  · exact Or.inl (by ring)
  · exact Or.inl (by ring)
  · exact Or.inl (by ring)
  · exact Or.inr (Or.inl (by ring))
  · exact Or.inr (Or.inr (by linear_combination -h3))

end Field

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_singular_of_three_le_finrank [Finite K] [FiniteDimensional K V]
    (hK : Nat.card K = 3) (W : Submodule K V) (h3 : 3 ≤ finrank K W) :
    ∃ v ∈ W, v ≠ 0 ∧ Q v = 0 := by
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  let _ : Invertible (2 : K) := invertibleOfNonzero h2
  have hsymm : (polarBilin (Q.comp W.subtype)).IsSymm := ⟨fun x y => by
    simp only [polarBilin_apply_apply]
    exact polar_comm _ x y⟩
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  have ho : ∀ i j, i ≠ j → polar Q (b i : V) (b j : V) = 0 := fun i j hij => by
    have h := hb hij
    change polarBilin (Q.comp W.subtype) (b i) (b j) = 0 at h
    rwa [polarBilin_apply_apply, polar_comp_subtype_apply] at h
  set i₀ : Fin (finrank K W) := ⟨0, by omega⟩
  set i₁ : Fin (finrank K W) := ⟨1, by omega⟩
  set i₂ : Fin (finrank K W) := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h => by simp [i₀, i₁, Fin.ext_iff] at h
  have h02 : i₀ ≠ i₂ := fun h => by simp [i₀, i₂, Fin.ext_iff] at h
  have h12 : i₁ ≠ i₂ := fun h => by simp [i₁, i₂, Fin.ext_iff] at h
  have hne : ∀ v : W, b.repr v i₀ = 1 → (v : V) ≠ 0 := fun v h1 h0 => by
    have h' : v = 0 := Subtype.ext h0
    rw [h', map_zero, Finsupp.zero_apply] at h1
    exact zero_ne_one h1
  have hr0 : b.repr (b i₀) i₀ = 1 := by rw [b.repr_self, Finsupp.single_eq_same]
  have hr : ∀ i, i₀ ≠ i → b.repr (b i) i₀ = 0 := fun i hi => by
    simp [b.repr_self, hi]
  have hsing : ∀ i, Q (b i : V) = 0 → ∃ v ∈ W, v ≠ 0 ∧ Q v = 0 := fun i hi =>
    ⟨b i, (b i).2, fun h => b.ne_zero i (Subtype.ext h), hi⟩
  by_cases hq₀ : Q (b i₀ : V) = 0
  · exact hsing i₀ hq₀
  by_cases hq₁ : Q (b i₁ : V) = 0
  · exact hsing i₁ hq₁
  by_cases hq₂ : Q (b i₂ : V) = 0
  · exact hsing i₂ hq₂
  rcases add_eq_zero_or_of_card_three hK hq₀ hq₁ hq₂ with h | h | h
  · refine ⟨((b i₀ + b i₁ : W) : V), (b i₀ + b i₁).2, hne _ ?_, ?_⟩
    · rw [map_add, Finsupp.add_apply, hr0, hr _ h01, add_zero]
    · rw [Submodule.coe_add, QuadraticMap.map_add Q, ho _ _ h01, add_zero, h]
  · refine ⟨((b i₀ + b i₂ : W) : V), (b i₀ + b i₂).2, hne _ ?_, ?_⟩
    · rw [map_add, Finsupp.add_apply, hr0, hr _ h02, add_zero]
    · rw [Submodule.coe_add, QuadraticMap.map_add Q, ho _ _ h02, add_zero, h]
  · refine ⟨((b i₀ + b i₁ + b i₂ : W) : V), (b i₀ + b i₁ + b i₂).2, hne _ ?_, ?_⟩
    · rw [map_add, map_add, Finsupp.add_apply, Finsupp.add_apply, hr0, hr _ h01, hr _ h02,
        add_zero, add_zero]
    · rw [Submodule.coe_add, Submodule.coe_add, QuadraticMap.map_add Q, QuadraticMap.map_add Q,
        polar_add_left, ho _ _ h01, ho _ _ h02, ho _ _ h12, add_zero, add_zero, add_zero, h]

theorem polar_eq_zero_of_forall_eq_zero {U : Submodule K V} (hU : ∀ x ∈ U, Q x = 0) {x y : V}
    (hx : x ∈ U) (hy : y ∈ U) : polar Q x y = 0 := by
  rw [QuadraticMap.polar, hU _ (U.add_mem hx hy), hU x hx, hU y hy, sub_zero, sub_zero]

theorem exists_add_of_isCompl' {W W' : Submodule K V} (hc : IsCompl W W') (x : V) :
    ∃ u ∈ W, ∃ w ∈ W', u + w = x :=
  Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top)

theorem polarNondegOn_of_isCompl (hQ : (polarBilin Q).Nondegenerate) {W W' : Submodule K V}
    (hc : IsCompl W W') (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0) : PolarNondegOn Q W := by
  intro x hx hxW
  apply eq_zero_of_polar_eq_zero hQ
  intro y
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_of_isCompl' hc y
  rw [polar_add_right, hxW u hu, horth x hx w hw, add_zero]

theorem two_mul_finrank_le_of_isCompl [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {W W' : Submodule K V} (hc : IsCompl W W') (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0)
    {U : Submodule K V} (hUW : U ≤ W) (hU : ∀ x ∈ U, Q x = 0) :
    2 * finrank K U ≤ finrank K W := by
  have hQW := nondegenerate_comp_subtype hQ hc horth
  set U' : Submodule K W := U.comap W.subtype with hU'
  have hdim : finrank K U' = finrank K U :=
    (Submodule.comapSubtypeEquivOfLe hUW).finrank_eq
  have hle : U' ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q.comp W.subtype)) U' :=
    fun w hw => (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun u hu => by
      change polarBilin (Q.comp W.subtype) u w = 0
      rw [polarBilin_apply_apply, polar_comp_subtype_apply]
      exact polar_eq_zero_of_forall_eq_zero hU hu hw
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQW] at h1
  have h2 := Submodule.finrank_le U'
  omega

theorem le_sup_inf_of_invariant {i : V ≃ₗ[K] V} (h2 : (2 : K) ≠ 0) (hii : i * i = 1)
    {S : Submodule K V} (hS : ∀ v ∈ S, i v ∈ S) :
    S ≤ (S ⊓ plusSp i) ⊔ (S ⊓ minusSp i) := by
  intro v hv
  rw [← projP_add_projM h2 (i := i) v]
  refine Submodule.add_mem_sup ⟨?_, projP_mem hii v⟩ ⟨?_, projM_mem hii v⟩
  · rw [projP_apply]
    exact S.smul_mem _ (S.add_mem hv (hS v hv))
  · rw [projM_apply]
    exact S.smul_mem _ (S.sub_mem hv (hS v hv))

theorem two_mul_finrank_inf_eq [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (h2 : (2 : K) ≠ 0) {i : V ≃ₗ[K] V} (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hii : i * i = 1) {S : Submodule K V} (hS : ∀ v ∈ S, i v ∈ S) (hts : ∀ x ∈ S, Q x = 0)
    (hdim : 2 * finrank K S = finrank K V) :
    2 * finrank K ↥(S ⊓ plusSp i) = finrank K (plusSp i) ∧
      2 * finrank K ↥(S ⊓ minusSp i) = finrank K (minusSp i) := by
  have hc := isCompl_plusSp_minusSp h2 hii
  have horth : ∀ u ∈ plusSp i, ∀ w ∈ minusSp i, polar Q u w = 0 :=
    fun u hu w hw => polar_plusSp_minusSp h2 hi hu hw
  have horth' : ∀ u ∈ minusSp i, ∀ w ∈ plusSp i, polar Q u w = 0 := fun u hu w hw => by
    rw [polar_comm]
    exact horth w hw u hu
  have h1 := two_mul_finrank_le_of_isCompl hQ hc horth (U := S ⊓ plusSp i) inf_le_right
    (fun x hx => hts x hx.1)
  have h1' := two_mul_finrank_le_of_isCompl hQ hc.symm horth' (U := S ⊓ minusSp i) inf_le_right
    (fun x hx => hts x hx.1)
  have h3 := Submodule.finrank_mono (le_sup_inf_of_invariant h2 hii hS)
  have h4 := Submodule.finrank_add_le_finrank_add_finrank (S ⊓ plusSp i) (S ⊓ minusSp i)
  have h5 := Submodule.finrank_add_eq_of_isCompl hc
  omega

end CFSG.ClassicalInvolution.Q3.Q3T
