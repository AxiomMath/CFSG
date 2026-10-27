module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCSpFull CFSG.LocalAnalysis.ComponentInitial

open scoped Classical

variable {r : ℕ} {K : Type} [Field K]

theorem spForm_self (v : Fin r ⊕ Fin r → K) : spForm r K v v = 0 :=
  (spForm_isAlt (r := r) (K := K)).self_eq_zero v

theorem spForm_comm_neg (u v : Fin r ⊕ Fin r → K) : spForm r K u v = - spForm r K v u :=
  ((spForm_isAlt (r := r) (K := K)).neg_eq v u).symm

theorem spForm_spEnd_spEnd' (g : StatedSp r K) (y z : Fin r ⊕ Fin r → K) :
    spForm r K (spEnd g y) (spEnd g z) = spForm r K y z :=
  mem_sesqUnitaryGroup.mp (spLin_mem g) y z

theorem spEnd_spEnd_inv_apply' (g : StatedSp r K) (y : Fin r ⊕ Fin r → K) :
    spEnd g (spEnd g⁻¹ y) = y := by
  rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one, Module.End.one_apply]

theorem conj_spTransvection' (g : StatedSp r K) (v : Fin r ⊕ Fin r → K) (t : K) :
    g * spTransvection v t * g⁻¹ = spTransvection (spEnd g v) t := by
  apply spLin_injective
  rw [map_mul, map_mul]
  refine Units.ext (LinearMap.ext fun y => ?_)
  simp only [Units.val_mul, Module.End.mul_apply]
  change spEnd g (spEnd (spTransvection v t) (spEnd g⁻¹ y)) =
    spEnd (spTransvection (spEnd g v) t) y
  rw [spEnd_spTransvection, spEnd_spTransvection, map_add, map_smul, spEnd_spEnd_inv_apply']
  congr 3
  conv_rhs => rw [← spEnd_spEnd_inv_apply' g y]
  exact (spForm_spEnd_spEnd' g _ v).symm

theorem charP_two_of_card (hK : Nat.card K = 2) : CharP K 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK]; simp)

theorem two_eq_zero_of_card (hK : Nat.card K = 2) : (2 : K) = 0 := by
  have := charP_two_of_card hK
  exact CharP.cast_eq_zero K 2

theorem eq_zero_or_one_of_card (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  by_contra hcon
  push Not at hcon
  have h3 : ({0, 1, c} : Finset K).card = 3 :=
    Finset.card_eq_three.mpr ⟨0, 1, c, zero_ne_one, hcon.1.symm, hcon.2.symm, rfl⟩
  have := Finset.card_le_univ ({0, 1, c} : Finset K)
  omega

section Comm

variable {x A : StatedSp r K}

theorem spEnd_mem_span_of_commute (hK : Nat.card K = 2)
    (hcomm : ∀ g ∈ ⁅spFixedFactor x, spFixedFactor x⁆, A * g = g * A)
    {v v' : Fin r ⊕ Fin r → K} (hv : spEnd x v = v) (hv' : spEnd x v' = v')
    (hvv' : spForm r K v v' = 1) :
    ∃ a b : K, spEnd A v = a • v + b • v' := by
  have h2 := two_eq_zero_of_card hK
  have hvs : spEnd x (v + v') = v + v' := by rw [map_add, hv, hv']
  set h := spTransvection (v + v') (1 : K) with hh
  set tv := spTransvection v (1 : K) with htv
  have hhF : h ∈ spFixedFactor x := spTransvection_mem_spFixedFactor hvs 1
  have htF : tv ∈ spFixedFactor x := spTransvection_mem_spFixedFactor hv 1
  have hhv : spEnd h v = v' := by
    rw [hh, spEnd_spTransvection, map_add ((spForm r K) v) v v']
    have e1 : spForm r K v v = 0 := spForm_self v
    rw [e1, hvv']
    simp only [zero_add, one_mul, one_smul]
    have : v + (v + v') = (2 : K) • v + v' := by rw [two_smul]; abel
    rw [this, h2, zero_smul, zero_add]
  have hconj := conj_spTransvection' h v (1 : K)
  rw [hhv] at hconj
  have hcF : h * tv * h⁻¹ * tv⁻¹ ∈ ⁅spFixedFactor x, spFixedFactor x⁆ :=
    Subgroup.commutator_mem_commutator hhF htF
  have hAc := hcomm _ hcF
  have hAc' : ∀ z, spEnd A (spEnd (h * tv * h⁻¹ * tv⁻¹) z) =
      spEnd (h * tv * h⁻¹ * tv⁻¹) (spEnd A z) := fun z => by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← spEnd_mul, ← spEnd_mul, hAc]
  have hceq : h * tv * h⁻¹ * tv⁻¹ = spTransvection v' (1 : K) * spTransvection v (-1 : K) := by
    rw [hconj, htv, spTransvection_inv]
  have hcz : ∀ z, spEnd (h * tv * h⁻¹ * tv⁻¹) z =
      (z + (-1 * spForm r K z v) • v) +
        (1 * spForm r K (z + (-1 * spForm r K z v) • v) v') • v' := fun z => by
    rw [hceq, spEnd_mul, Module.End.mul_apply, spEnd_spTransvection, spEnd_spTransvection]
  have hspan : ∀ z, ∃ a b : K, spEnd (h * tv * h⁻¹ * tv⁻¹) z = z + a • v + b • v' := fun z => by
    refine ⟨-1 * spForm r K z v, 1 * spForm r K (z + (-1 * spForm r K z v) • v) v', ?_⟩
    rw [hcz]
  have hcv : spEnd (h * tv * h⁻¹ * tv⁻¹) v = v + v' := by
    rw [hcz]
    simp [spForm_self v, hvv']
  have hcv' : spEnd (h * tv * h⁻¹ * tv⁻¹) v' = v' + v + v' := by
    rw [hcz]
    have e1 : spForm r K v' v = -1 := by rw [spForm_comm_neg, hvv']
    have e2 : spForm r K v' v' = 0 := spForm_self v'
    simp [e1, e2, hvv']
  set c := h * tv * h⁻¹ * tv⁻¹ with hcdef
  obtain ⟨a₁, b₁, hA1⟩ : ∃ a b : K, spEnd A v' = a • v + b • v' := by
    obtain ⟨a, b, hab⟩ := hspan (spEnd A v)
    refine ⟨a, b, ?_⟩
    have h1 : spEnd A v' = spEnd c (spEnd A v) - spEnd A v := by
      rw [← hAc', hcv, map_add]
      abel
    rw [h1, hab]
    abel
  obtain ⟨a₂, b₂, hA2⟩ : ∃ a b : K, spEnd A v + spEnd A v' = a • v + b • v' := by
    obtain ⟨a, b, hab⟩ := hspan (spEnd A v')
    refine ⟨a, b, ?_⟩
    have h1 : spEnd A v + spEnd A v' = spEnd c (spEnd A v') - spEnd A v' := by
      rw [← hAc', hcv', map_add, map_add]
      abel
    rw [h1, hab]
    abel
  refine ⟨a₂ - a₁, b₂ - b₁, ?_⟩
  have : spEnd A v = (spEnd A v + spEnd A v') - spEnd A v' := by abel
  rw [this, hA2, hA1]
  module

theorem spEnd_injective (A : StatedSp r K) {u : Fin r ⊕ Fin r → K} (h : spEnd A u = 0) :
    u = 0 := by
  have := spEnd_spEnd_inv_apply' A⁻¹ u
  rw [inv_inv, h, map_zero] at this
  exact this.symm

theorem spEnd_eq_of_commute (hK : Nat.card K = 2)
    (hcomm : ∀ g ∈ ⁅spFixedFactor x, spFixedFactor x⁆, A * g = g * A)
    (hW : ((spForm r K).restrict (LinearMap.ker (spEnd x - 1))).Nondegenerate)
    (h3 : 3 ≤ finrank K (LinearMap.ker (spEnd x - 1)))
    {u : Fin r ⊕ Fin r → K} (hu : spEnd x u = u) : spEnd A u = u := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  by_cases hu0 : u = 0
  · rw [hu0, map_zero]
  set W := LinearMap.ker (spEnd x - 1) with hWdef
  have hmemW : ∀ w, w ∈ W ↔ spEnd x w = w := fun w => mem_ker_sub_one_iff
  have huW : u ∈ W := (hmemW u).2 hu
  obtain ⟨v₁, hv₁W, hv₁⟩ : ∃ v₁ ∈ W, spForm r K u v₁ = 1 := by
    by_contra hcon
    push Not at hcon
    have : (⟨u, huW⟩ : W) = 0 := hW.1 ⟨u, huW⟩ fun w => by
      by_contra hne
      have hne : spForm r K u w ≠ 0 := hne
      refine hcon ((spForm r K u w)⁻¹ • (w : Fin r ⊕ Fin r → K)) (W.smul_mem _ w.2) ?_
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne]
    exact hu0 (congrArg Subtype.val this)
  obtain ⟨z, hzW, hzu, hz⟩ : ∃ z ∈ W, spForm r K u z = 0 ∧ z ∉ Submodule.span K {u} := by
    by_contra hcon
    push Not at hcon
    let f : W →ₗ[K] K := (spForm r K u).domRestrict W
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 : finrank K (LinearMap.range f) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range f)
      simpa using this
    have h3' : finrank K (LinearMap.ker f) ≤ 1 := by
      have hle : (LinearMap.ker f).map W.subtype ≤ Submodule.span K {u} := by
        rintro _ ⟨w, hw, rfl⟩
        exact hcon w w.2 (by simpa [f] using hw)
      have e : finrank K ((LinearMap.ker f).map W.subtype) = finrank K (LinearMap.ker f) :=
        LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ W.injective_subtype _).symm
      rw [← e]
      refine (Submodule.finrank_mono hle).trans ?_
      exact (finrank_span_singleton hu0).le
    omega
  have hv₁x : spEnd x v₁ = v₁ := (hmemW v₁).1 hv₁W
  have hzx : spEnd x z = z := (hmemW z).1 hzW
  obtain ⟨a, b, hab⟩ := spEnd_mem_span_of_commute hK hcomm hu hv₁x hv₁
  have hv₂x : spEnd x (v₁ + z) = v₁ + z := by rw [map_add, hv₁x, hzx]
  have hv₂ : spForm r K u (v₁ + z) = 1 := by
    rw [map_add, hv₁, hzu, add_zero]
  obtain ⟨a', b', hab'⟩ := spEnd_mem_span_of_commute hK hcomm hu hv₂x hv₂
  have hbb : b = b' := by
    have e := congrArg (spForm r K u) (hab.symm.trans hab')
    simp only [map_add, map_smul, smul_eq_mul, spForm_self u, hv₁, hzu] at e
    simpa using e
  subst hbb
  have hb0 : b = 0 := by
    by_contra hb
    apply hz
    have e : (a - a') • u = b • z := by
      have e0 := hab.symm.trans hab'
      rw [smul_add, ← add_assoc] at e0
      have : (a • u + b • v₁) - (a' • u + b • v₁ + b • z) = 0 := by rw [e0]; simp
      rw [sub_smul]
      have h2 : a • u - a' • u - b • z = 0 := by
        rw [← this]; abel
      exact sub_eq_zero.1 h2
    have : z = (b⁻¹ * (a - a')) • u := by
      rw [mul_smul, e, smul_smul, inv_mul_cancel₀ hb, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have hAu : spEnd A u = a • u := by rw [hab, hb0]; simp
  have hane : a ≠ 0 := by
    intro ha0
    apply hu0
    refine spEnd_injective A ?_
    rw [hAu, ha0, zero_smul]
  rcases eq_zero_or_one_of_card hK a with h | h
  · exact absurd h hane
  · rw [hAu, h, one_smul]

end Comm

end CFSG.HardMathSupport.Timmesfeld.CrossChar
