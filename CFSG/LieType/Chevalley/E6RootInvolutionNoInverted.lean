module

public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.TwistMap

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint Polynomial

theorem iform_permLattice_E6 (x y : Fin TwistTag.E6.tag.rank → ℤ) :
    iform (permLattice TwistTag.E6.perm x) (permLattice TwistTag.E6.perm y) = iform x y := by
  have hS : ∀ i j, TwistTag.E6.tag.symmetrizedCartan (TwistTag.E6.perm i) (TwistTag.E6.perm j) =
      TwistTag.E6.tag.symmetrizedCartan i j := by
    intro i j
    have h1 : TwistTag.E6.tag.symmetrizedCartan = TwistTag.E6.tag.cartan := by
      change Tag.E6.symmetrizer * Tag.E6.cartan = Tag.E6.cartan
      rw [show Tag.E6.symmetrizer = 1 from rfl, one_mul]
    rw [h1]
    exact TwistTag.cartan_perm _ i j
  simp only [iform, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp TwistTag.E6.perm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp TwistTag.E6.perm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hS]

theorem height_reflect_eq
    {τ : Tag} (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    height (reflect τ i v) = height v - ∑ j, τ.cartan i j * v j := by
  rw [show reflect τ i v = v - (∑ j, τ.cartan i j * v j) • Pi.single i 1 from rfl, height_sub,
    height_zsmul, height_single, mul_one]

theorem iform_eq_sum_single
    {τ : Tag} (x y : Fin τ.rank → ℤ) :
    iform x y = ∑ j, x j * iform (Pi.single j 1) y := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [iform_finset_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (Pi.single j (x j) : Fin τ.rank → ℤ) = x j • Pi.single j 1 := by
    ext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp [hk]
  rw [e, iform_smul_left]

theorem E6_root_involution_without_inverted_roots
    (w : WeylGroup TwistTag.E6.tag)
    (h2 : ∀ v, w • permLattice TwistTag.E6.perm (w • permLattice TwistTag.E6.perm v) = v)
    (hno : ∀ β, IsRoot TwistTag.E6.tag β → w • permLattice TwistTag.E6.perm β ≠ -β) :
    ∃ u : WeylGroup TwistTag.E6.tag, ∀ v,
      u • (w • permLattice TwistTag.E6.perm (u⁻¹ • v)) = permLattice TwistTag.E6.perm v := by
  classical
  set ρ := TwistTag.E6.perm with hρ
  let ρhom : (Fin TwistTag.E6.tag.rank → ℤ) →+ (Fin TwistTag.E6.tag.rank → ℤ) :=
    { toFun := permLattice ρ
      map_zero' := rfl
      map_add' := permLattice_add ρ }
  let whom : (Fin TwistTag.E6.tag.rank → ℤ) →+ (Fin TwistTag.E6.tag.rank → ℤ) :=
    { toFun := fun v => w • v
      map_zero' := smul_zero w
      map_add' := smul_add w }
  let ω := whom.comp ρhom
  have hωv : ∀ v, ω v = w • permLattice ρ v := fun v => rfl
  have hωω : ∀ v, ω (ω v) = v := h2
  have hωiso : ∀ x y, iform (ω x) (ω y) = iform x y := fun x y => by
    rw [hωv, hωv, iform_smul, iform_permLattice_E6]
  have hωadj : ∀ x y, iform (ω x) y = iform x (ω y) := fun x y => by
    calc iform (ω x) y = iform (ω x) (ω (ω y)) := by rw [hωω]
      _ = iform x (ω y) := hωiso x (ω y)
  set c : (Fin TwistTag.E6.tag.rank → ℤ) → Fin TwistTag.E6.tag.rank → ℤ := fun β j =>
    iform (Pi.single j 1 + ω (Pi.single j 1)) β with hc
  have hcoef : ∀ β, IsRoot TwistTag.E6.tag β → ∃ j, c β j ≠ 0 := by
    intro β hβ
    by_contra hall
    push Not at hall
    apply hno β hβ
    have h0 : ∀ j, iform (Pi.single j 1) (β + ω β) = 0 := fun j => by
      rw [iform_add_right, ← hωadj, ← iform_add_left]
      exact hall j
    have hz : β + ω β = 0 := by
      by_contra hne
      have hpos := iform_self_pos hne
      rw [iform_eq_sum_single, Finset.sum_eq_zero fun j _ => by rw [h0 j, mul_zero]] at hpos
      exact lt_irrefl 0 hpos
    rw [← hωv]
    exact eq_neg_of_add_eq_zero_right hz
  let P : (Fin TwistTag.E6.tag.rank → ℤ) → ℤ[X] := fun β =>
    ∑ j : Fin TwistTag.E6.tag.rank, C (c β j) * X ^ (j : ℕ)
  have hPcoeff : ∀ β (j : Fin TwistTag.E6.tag.rank), (P β).coeff j = c β j := by
    intro β j
    simp only [P, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      exact ite_eq_right_iff.2 fun h => absurd (Fin.ext h.symm) hb
    · simp
  have hP0 : ∀ β, IsRoot TwistTag.E6.tag β → P β ≠ 0 := by
    intro β hβ h0
    obtain ⟨j, hj⟩ := hcoef β hβ
    apply hj
    rw [← hPcoeff, h0, coeff_zero]
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
    ((rootFinset TwistTag.E6.tag).biUnion fun β => (P β).roots.toFinset)
  set h : Fin TwistTag.E6.tag.rank → ℤ :=
    ∑ j : Fin TwistTag.E6.tag.rank, t ^ (j : ℕ) • (Pi.single j 1 + ω (Pi.single j 1)) with hhdef
  have hωh : ω h = h := by
    rw [hhdef, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_add, hωω, add_comm]
  have hreg : ∀ β, IsRoot TwistTag.E6.tag β → iform h β ≠ 0 := by
    intro β hβ h0
    have hev : (P β).eval t = iform h β := by
      simp only [P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, hhdef,
        iform_finset_sum_left, iform_smul_left, hc]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    apply ht
    rw [Finset.mem_biUnion]
    refine ⟨β, mem_rootFinset.2 hβ, ?_⟩
    rw [Multiset.mem_toFinset, mem_roots (hP0 β hβ), IsRoot.def, hev, h0]
  have : Fintype (WeylGroup TwistTag.E6.tag) := Fintype.ofFinite _
  obtain ⟨u, -, hu⟩ := Finset.exists_max_image Finset.univ (fun u : WeylGroup TwistTag.E6.tag =>
    height (u • h)) Finset.univ_nonempty
  set h' := u • h with hh'
  have hreg' : ∀ β, IsRoot TwistTag.E6.tag β → iform h' β ≠ 0 := by
    intro β hβ
    have e : iform h' β = iform h (u⁻¹ • β) := by
      rw [hh', ← iform_smul u⁻¹, inv_smul_smul]
    rw [e]
    exact hreg _ (IsRoot.smul hβ u⁻¹)
  have hdom : ∀ i, 0 < iform (Pi.single i 1) h' := by
    intro i
    have hle := hu (simple TwistTag.E6.tag i * u) (Finset.mem_univ _)
    rw [mul_smul, ← hh', simple_smul, height_reflect_eq] at hle
    have hsum : 0 ≤ ∑ j, TwistTag.E6.tag.cartan i j * h' j := by omega
    have hpos := symmetrizer_pos TwistTag.E6.tag i
    have hne := hreg' _ (isRoot_single TwistTag.E6.tag i)
    rw [iform_comm] at hne
    rw [iform_single_left] at hne ⊢
    rcases (mul_nonneg hpos.le hsum).lt_or_eq with h1 | h1
    · exact h1
    · exact absurd h1.symm hne
  have hposroot : ∀ β, IsRoot TwistTag.E6.tag β → 0 < height β → 0 < iform β h' := by
    intro β hβ hht
    rcases hβ.nonneg_or_nonpos with hnn | hnp
    · rw [iform_eq_sum_single]
      have hex : ∃ j, 0 < β j := by
        by_contra hall
        push Not at hall
        have : height β ≤ 0 := Finset.sum_nonpos fun j _ => hall j
        omega
      obtain ⟨j, hj⟩ := hex
      exact Finset.sum_pos' (fun k _ => mul_nonneg (hnn k) (hdom k).le)
        ⟨j, Finset.mem_univ _, mul_pos hj (hdom j)⟩
    · have : height β ≤ 0 := Finset.sum_nonpos fun j _ => hnp j
      omega
  have hheight : ∀ β, IsRoot TwistTag.E6.tag β → height β ≠ 0 := by
    intro β hβ h0
    rcases hβ.nonneg_or_nonpos with hnn | hnp
    · exact hβ.ne_zero (funext fun j =>
        (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hnn k).1 h0 j (Finset.mem_univ _))
    · exact hβ.ne_zero (funext fun j =>
        (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hnp k).1 h0 j (Finset.mem_univ _))
  have hsign : ∀ β, IsRoot TwistTag.E6.tag β → (0 < height β ↔ 0 < iform β h') := by
    intro β hβ
    refine ⟨hposroot β hβ, fun hp => ?_⟩
    by_contra hneg
    have hn : 0 < height (-β) := by
      have := hheight β hβ
      rw [height_neg]
      omega
    have := hposroot (-β) (IsRoot.neg hβ) hn
    have hneg' : iform (-β) h' = -iform β h' := by simp [iform, Finset.sum_neg_distrib]
    rw [hneg'] at this
    omega
  set w' := u * w * weylTwist TwistTag.E6 u⁻¹ with hw'
  have hδ : ∀ v, u • ω (u⁻¹ • v) = w' • permLattice ρ v := fun v => by
    rw [hωv, ← weylTwist_smul_permLattice, hw', mul_smul, mul_smul]
  have hδh : u • ω (u⁻¹ • h') = h' := by rw [hh', inv_smul_smul, hωh]
  have hδiso : ∀ x y, iform (u • ω (u⁻¹ • x)) (u • ω (u⁻¹ • y)) = iform x y := fun x y => by
    rw [iform_smul, hωiso, ← iform_smul u, smul_inv_smul, smul_inv_smul]
  have hw'1 : w' = 1 := by
    have hinv : inversionSet w' = ∅ := by
      ext γ
      simp only [inversionSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hγ, hγpos, -, hneg⟩
      set γ' := permLattice ρ.symm γ with hγ'
      have hγ'root : IsRoot TwistTag.E6.tag γ' := hγ.permLattice (cartan_perm_symm
        TwistTag.E6.cartan_perm)
      have hγeq : permLattice ρ γ' = γ := permLattice_permLattice_symm ρ γ
      have hγ'pos : 0 < height γ' := by rw [hγ', height_permLattice]; exact hγpos
      have h1 := (hsign γ' hγ'root).1 hγ'pos
      have h2' : iform (u • ω (u⁻¹ • γ')) h' = iform γ' h' := by
        conv_lhs => rw [← hδh]
        exact hδiso γ' h'
      rw [hδ, hγeq] at h2'
      have h3 : 0 < height (w' • γ) := by
        rw [hsign _ (IsRoot.smul hγ w'), h2']
        exact h1
      omega
    have hl := (weyl_inversion_length TwistTag.E6.tag).1 w'
    rw [hinv, Set.ncard_empty] at hl
    exact (coxeterSystem TwistTag.E6.tag).length_eq_zero_iff.1 hl
  refine ⟨u, fun v => ?_⟩
  have := hδ v
  rw [hw'1, one_smul, hωv] at this
  exact this

end CFSG.LieType.Chevalley
