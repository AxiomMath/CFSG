module

public import CFSG.LieType.Chevalley.LangWeylChamberStabilizers
public import CFSG.LieType.Chevalley.E6RootInvolutionNoInverted

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem RootSpace CFSG.LieType.Steinberg.Adjoint
  Polynomial

variable {τ : Tag}

theorem exists_inner_ofLattice_eq_iform
    (τ : Tag) :
    ∃ c : ℝ, 0 < c ∧ ∀ u v : Fin τ.rank → ℤ,
      inner ℝ (ofLattice u) (ofLattice v) = c * (iform u v : ℝ) := by
  obtain ⟨c, hc, h⟩ := exists_inner_eq_smul τ
  refine ⟨c, hc, fun u v => ?_⟩
  rw [h]
  congr 1
  simp only [ofLattice_apply, iform, Int.cast_sum, Int.cast_mul]

@[expose] def invertedRootsOf
    (w : WeylGroup τ) : Set (Fin τ.rank → ℤ) :=
  {β | IsRoot τ β ∧ w • β = -β}

theorem invertedRootsOf_finite
    (w : WeylGroup τ) : (invertedRootsOf w).Finite :=
  (finite_setOf_isRoot _).subset fun _ hβ => hβ.1

theorem exists_isRoot_smul_eq_neg_of_involution
    {w : WeylGroup τ} (hw2 : w * w = 1)
    (hw : w ≠ 1) : ∃ β, IsRoot τ β ∧ w • β = -β := by
  classical
  by_contra hno
  push Not at hno
  have hww : ∀ v : Fin τ.rank → ℤ, w • (w • v) = v := fun v => by
    rw [← mul_smul, hw2, one_smul]
  have hadj : ∀ x y : Fin τ.rank → ℤ, iform (w • x) y = iform x (w • y) := fun x y => by
    calc iform (w • x) y = iform (w • x) (w • (w • y)) := by rw [hww]
      _ = iform x (w • y) := iform_smul w x (w • y)
  set c : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ := fun β j =>
    iform (Pi.single j 1 + w • (Pi.single j 1 : Fin τ.rank → ℤ)) β with hc
  have hcoef : ∀ β, IsRoot τ β → ∃ j, c β j ≠ 0 := by
    intro β hβ
    by_contra hall
    push Not at hall
    apply hno β hβ
    have h0 : ∀ j, iform (Pi.single j 1) (β + w • β) = 0 := fun j => by
      rw [iform_add_right, ← hadj, ← iform_add_left]
      exact hall j
    have hz : β + w • β = 0 := by
      by_contra hne
      have hpos := iform_self_pos hne
      rw [iform_eq_sum_single, Finset.sum_eq_zero fun j _ => by rw [h0 j, mul_zero]] at hpos
      exact lt_irrefl 0 hpos
    exact eq_neg_of_add_eq_zero_right hz
  let P : (Fin τ.rank → ℤ) → ℤ[X] := fun β => ∑ j : Fin τ.rank, C (c β j) * X ^ (j : ℕ)
  have hPcoeff : ∀ β (j : Fin τ.rank), (P β).coeff j = c β j := by
    intro β j
    simp only [P, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      exact ite_eq_right_iff.2 fun h => absurd (Fin.ext h.symm) hb
    · simp
  have hP0 : ∀ β, IsRoot τ β → P β ≠ 0 := by
    intro β hβ h0
    obtain ⟨j, hj⟩ := hcoef β hβ
    apply hj
    rw [← hPcoeff, h0, coeff_zero]
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
    ((rootFinset τ).biUnion fun β => (P β).roots.toFinset)
  set h : Fin τ.rank → ℤ :=
    ∑ j : Fin τ.rank, t ^ (j : ℕ) • (Pi.single j 1 + w • (Pi.single j 1 : Fin τ.rank → ℤ))
    with hhdef
  have hwh : w • h = h := by
    rw [hhdef, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm, smul_add, hww, add_comm]
  have hreg : ∀ β, IsRoot τ β → iform h β ≠ 0 := by
    intro β hβ h0
    have hev : (P β).eval t = iform h β := by
      simp only [P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, hhdef,
        iform_finset_sum_left, iform_smul_left, hc]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    apply ht
    rw [Finset.mem_biUnion]
    refine ⟨β, mem_rootFinset.2 hβ, ?_⟩
    rw [Multiset.mem_toFinset, mem_roots (hP0 β hβ), IsRoot.def, hev, h0]
  obtain ⟨c0, hc0, hinner⟩ := exists_inner_ofLattice_eq_iform τ
  have hstab : w ∈ weylStabilizer τ (ofLattice h) := by
    change weylAct τ w (ofLattice h) = ofLattice h
    rw [weylAct_ofLattice, hwh]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2 (ofLattice h)] at hstab
  have hempty : {s | ∃ α, IsRoot τ α ∧ inner ℝ (ofLattice α) (ofLattice h) = 0 ∧
      s = rootReflection α} = (∅ : Set (WeylGroup τ)) := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨α, hα, h0, -⟩
    rw [hinner, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact hc0.ne' h0
    · apply hreg α hα
      rw [iform_comm]
      exact_mod_cast h0
  rw [hempty, Subgroup.closure_empty, Subgroup.mem_bot] at hstab
  exact hw hstab

theorem invertedRoots_reflection_subset_general
    {w : WeylGroup τ}
    (hww : ∀ v : Fin τ.rank → ℤ, w • (w • v) = v) {β : Fin τ.rank → ℤ} (hβr : IsRoot τ β)
    (hwβ : w • β = -β) {γ : Fin τ.rank → ℤ} (hγeq : (rootReflection β * w) • γ = -γ) :
    w • γ = -γ ∧ iform γ β = 0 ∧ γ ≠ β := by
  have hadj : ∀ x y : Fin τ.rank → ℤ, iform (w • x) y = iform x (w • y) := fun x y => by
    calc iform (w • x) y = iform (w • x) (w • (w • y)) := by rw [hww]
      _ = iform x (w • y) := iform_smul w x (w • y)
  have hneg : ∀ x y : Fin τ.rank → ℤ, iform x (-y) = -iform x y := fun x y => by
    simp [iform, Finset.sum_neg_distrib]
  rw [mul_smul] at hγeq
  have hsβ : ∀ x, iform (rootReflection β • x) β = -iform x β := fun x => by
    calc iform (rootReflection β • x) β =
          iform (rootReflection β • x) (rootReflection β • (rootReflection β • β)) := by
          rw [← mul_smul, rootReflection_mul_self hβr, one_smul]
      _ = -iform x β := by rw [iform_smul, rootReflection_smul_self hβr, hneg]
  have h0 : iform γ β = 0 := by
    have e1 := hsβ (w • γ)
    rw [hγeq, hadj, hwβ, hneg] at e1
    have e2 : iform (-γ) β = -iform γ β := by
      rw [iform_comm, hneg, iform_comm]
    rw [e2] at e1
    linarith
  have h0' : iform β (w • γ) = 0 := by
    rw [iform_comm, hadj, hwβ, hneg, h0, neg_zero]
  rw [rootReflection_smul_of_iform_eq_zero hβr h0'] at hγeq
  refine ⟨hγeq, h0, fun hγβ => ?_⟩
  subst hγβ
  have := iform_self_pos_of_isRoot hβr
  rw [h0] at this
  exact lt_irrefl 0 this


theorem rootReflection_commute_of_iform_eq_zero
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hγ : IsRoot τ γ) (h0 : iform β γ = 0) :
    Commute (rootReflection β) (rootReflection γ) := by
  have e := rootReflection_smul_root (rootReflection β) hγ
  rw [rootReflection_smul_of_iform_eq_zero hβ h0] at e
  have e2 : rootReflection β * rootReflection γ = rootReflection γ * rootReflection β := by
    calc rootReflection β * rootReflection γ =
          (rootReflection β * rootReflection γ * (rootReflection β)⁻¹) * rootReflection β := by
          group
      _ = rootReflection γ * rootReflection β := by rw [← e]
  exact e2

@[expose] def minusSpace
    (w : WeylGroup τ) : Submodule ℝ (RootSpace τ) :=
  LinearMap.ker (weylLinear τ w + LinearMap.id)

theorem mem_minusSpace
    {w : WeylGroup τ} {x : RootSpace τ} :
    x ∈ minusSpace w ↔ weylAct τ w x = -x := by
  rw [minusSpace, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, weylAct_apply,
    add_eq_zero_iff_eq_neg]

theorem exceptional_Lang_Weyl_involution_orthogonal_reflections
    (τ : Tag) (w : WeylGroup τ)
    (hw : w ^ 2 = 1) :
    ∃ βs : List (Fin τ.rank → ℤ), βs.length ≤ τ.rank ∧ (∀ β ∈ βs, IsRoot τ β) ∧
      βs.Pairwise (fun β γ => iform β γ = 0) ∧ w = (βs.map rootReflection).prod ∧
      (Submodule.span ℝ (ofLattice '' {β | β ∈ βs}) : Set (RootSpace τ)) =
        {x | weylAct τ w x = -x} ∧
      βs.Pairwise (fun β γ => Commute (rootReflection β) (rootReflection γ)) ∧
      (w = 1 → βs = []) := by
  classical
  obtain ⟨c0, hc0, hinner⟩ := exists_inner_ofLattice_eq_iform τ
  have claim : ∀ (n : ℕ) (w : WeylGroup τ), w * w = 1 → (invertedRootsOf w).ncard = n →
      ∃ βs : List (Fin τ.rank → ℤ), (∀ β ∈ βs, IsRoot τ β ∧ w • β = -β) ∧
        βs.Pairwise (fun β γ => iform β γ = 0) ∧ w = (βs.map rootReflection).prod ∧
        Submodule.span ℝ (ofLattice '' {β | β ∈ βs}) = minusSpace w := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hw2 hn
      by_cases hw1 : w = 1
      · subst hw1
        refine ⟨[], by simp, List.Pairwise.nil, by simp, ?_⟩
        have he : ofLattice '' {β : Fin τ.rank → ℤ | β ∈ ([] : List (Fin τ.rank → ℤ))} = ∅ := by
          simp
        rw [he, Submodule.span_empty]
        refine (eq_bot_iff.2 fun x hx => ?_).symm
        rw [mem_minusSpace, map_one, LinearIsometryEquiv.coe_one, id] at hx
        rw [Submodule.mem_bot]
        have h2 : (2 : ℝ) • x = 0 := by
          rw [two_smul]
          nth_rewrite 1 [hx]
          exact neg_add_cancel x
        exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
      obtain ⟨β, hβ, hwβ⟩ := exists_isRoot_smul_eq_neg_of_involution hw2 hw1
      have hww : ∀ v : Fin τ.rank → ℤ, w • (w • v) = v := fun v => by
        rw [← mul_smul, hw2, one_smul]
      have hcomm : rootReflection β * w = w * rootReflection β := by
        have e := rootReflection_smul_root w hβ
        rw [hwβ, rootReflection_neg hβ] at e
        calc rootReflection β * w = w * rootReflection β * w⁻¹ * w := by rw [← e]
          _ = w * rootReflection β := by group
      obtain ⟨w₁, hw₁⟩ : ∃ w₁, w₁ = rootReflection β * w := ⟨_, rfl⟩
      have hw₁2 : w₁ * w₁ = 1 := by
        calc w₁ * w₁ = rootReflection β * (w * rootReflection β) * w := by rw [hw₁]; group
          _ = rootReflection β * (rootReflection β * w) * w := by rw [hcomm]
          _ = (rootReflection β * rootReflection β) * (w * w) := by group
          _ = 1 := by rw [rootReflection_mul_self hβ, hw2, one_mul]
      have hsub : ∀ γ ∈ invertedRootsOf w₁, γ ∈ invertedRootsOf w ∧ iform γ β = 0 ∧ γ ≠ β :=
        fun γ hγ => by
          obtain ⟨h1, h2, h3⟩ := invertedRoots_reflection_subset_general hww hβ hwβ
            (by rw [← hw₁]; exact hγ.2)
          exact ⟨⟨hγ.1, h1⟩, h2, h3⟩
      have hlt : (invertedRootsOf w₁).ncard < n := by
        rw [← hn]
        refine Set.ncard_lt_ncard ⟨fun γ hγ => (hsub γ hγ).1, fun h => ?_⟩
          (invertedRootsOf_finite w)
        exact (hsub β (h ⟨hβ, hwβ⟩)).2.2 rfl
      obtain ⟨γs, hγs, hpair, hprod, hspan⟩ := ih _ hlt w₁ hw₁2 rfl
      have hγw : ∀ γ ∈ γs, IsRoot τ γ ∧ w • γ = -γ ∧ iform γ β = 0 := fun γ hγ => by
        obtain ⟨⟨h1, h2⟩, h3, -⟩ := hsub γ (hγs γ hγ)
        exact ⟨h1, h2, h3⟩
      refine ⟨β :: γs, ?_, ?_, ?_, ?_⟩
      · intro γ hγ
        rcases List.mem_cons.1 hγ with rfl | hγ
        · exact ⟨hβ, hwβ⟩
        · exact ⟨(hγw γ hγ).1, (hγw γ hγ).2.1⟩
      · refine List.Pairwise.cons (fun γ hγ => ?_) hpair
        rw [iform_comm]
        exact (hγw γ hγ).2.2
      · rw [List.map_cons, List.prod_cons, ← hprod, hw₁, ← mul_assoc,
          rootReflection_mul_self hβ, one_mul]
      ·
        have hins : ofLattice '' {γ | γ ∈ β :: γs} =
            insert (ofLattice β) (ofLattice '' {γ | γ ∈ γs}) := by
          ext x
          simp only [List.mem_cons, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff]
          constructor
          · rintro ⟨γ, rfl | hγ, rfl⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨γ, hγ, rfl⟩
          · rintro (rfl | ⟨γ, hγ, rfl⟩)
            · exact ⟨β, Or.inl rfl, rfl⟩
            · exact ⟨γ, Or.inr hγ, rfl⟩
        have hββ : inner ℝ (ofLattice β) (ofLattice β) ≠ 0 := by
          rw [hinner]
          exact mul_ne_zero hc0.ne' (by exact_mod_cast (iform_self_pos_of_isRoot hβ).ne')
        rw [hins, Submodule.span_insert]
        refine le_antisymm ?_ ?_
        · refine sup_le ?_ ?_
          · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_minusSpace,
              weylAct_ofLattice, hwβ, ofLattice_neg]
          · rw [hspan]
            intro x hx
            rw [mem_minusSpace] at hx ⊢
            have h1 : weylAct τ w x = weylAct τ (rootReflection β) (weylAct τ w₁ x) := by
              rw [← weylAct_mul_apply, hw₁, ← mul_assoc, rootReflection_mul_self hβ, one_mul]
            have hxβ : inner ℝ (ofLattice β) x = 0 := by
              have e1 : inner ℝ (ofLattice β) x =
                  inner ℝ (weylAct τ w₁ (ofLattice β)) (weylAct τ w₁ x) :=
                (LinearIsometryEquiv.inner_map_map _ _ _).symm
              have e2 : weylAct τ w₁ (ofLattice β) = ofLattice β := by
                rw [weylAct_ofLattice, hw₁, mul_smul, hwβ, smul_neg,
                  rootReflection_smul_self hβ, neg_neg]
              rw [e2, hx, inner_neg_right] at e1
              linarith
            rw [h1, hx, map_neg, weylAct_rootReflection hβ, hxβ, mul_zero, zero_div, zero_smul,
              sub_zero]
        · intro x hx
          rw [mem_minusSpace] at hx
          set cx := inner ℝ (ofLattice β) x / inner ℝ (ofLattice β) (ofLattice β) with hcx
          set x' := x - cx • ofLattice β with hx'
          have hx'β : inner ℝ (ofLattice β) x' = 0 := by
            rw [hx', inner_sub_right, real_inner_smul_right, hcx, div_mul_cancel₀ _ hββ, sub_self]
          have hwx' : weylAct τ w x' = -x' := by
            rw [hx', map_sub, map_smul, hx, weylAct_ofLattice, hwβ, ofLattice_neg]
            module
          have hx'mem : x' ∈ minusSpace w₁ := by
            rw [mem_minusSpace, hw₁, weylAct_mul_apply, hwx', map_neg,
              weylAct_rootReflection hβ, hx'β, mul_zero, zero_div, zero_smul, sub_zero]
          rw [← hspan] at hx'mem
          have hβmem : cx • ofLattice β ∈ Submodule.span ℝ {ofLattice β} :=
            Submodule.smul_mem _ _ (Submodule.subset_span rfl)
          have : x = cx • ofLattice β + x' := by rw [hx']; abel
          rw [this]
          exact Submodule.add_mem_sup hβmem hx'mem
  obtain ⟨βs, hβs, hpair, hprod, hspan⟩ := claim _ w (by rw [← sq]; exact hw) rfl
  have hroots : ∀ β ∈ βs, IsRoot τ β := fun β hβ => (hβs β hβ).1
  refine ⟨βs, ?_, hroots, hpair, hprod, ?_, ?_, ?_⟩
  ·
    set v : Fin βs.length → RootSpace τ := fun j => ofLattice (βs.get j) with hv
    have hli : LinearIndependent ℝ v := by
      refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun j => ?_) fun i j hij => ?_
      · rw [hv]
        intro h0
        exact (hroots _ (List.get_mem _ _)).ne_zero (ofLattice_injective (h0.trans
          ofLattice_zero.symm))
      · rw [hv]
        simp only
        rw [hinner]
        have hp := List.pairwise_iff_get.1 hpair
        rcases lt_or_gt_of_ne hij with h | h
        · rw [hp i j h, Int.cast_zero, mul_zero]
        · rw [iform_comm, hp j i h, Int.cast_zero, mul_zero]
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin, Module.finrank_eq_card_basis (basis τ), Fintype.card_fin] at this
  · rw [hspan]
    ext x
    rw [SetLike.mem_coe, mem_minusSpace, Set.mem_ofPred_eq]
  · exact hpair.imp_of_mem fun {β γ} hβ hγ h0 =>
      rootReflection_commute_of_iform_eq_zero (hroots β hβ) (hroots γ hγ) h0
  · rintro rfl
    rcases βs with _ | ⟨β, βs⟩
    · rfl
    · exfalso
      obtain ⟨hβ, hβneg⟩ := hβs β (List.mem_cons_self)
      rw [one_smul, eq_neg_iff_add_eq_zero, ← two_smul ℤ β] at hβneg
      exact hβ.ne_zero ((smul_eq_zero.1 hβneg).resolve_left two_ne_zero)

end CFSG.LieType.Chevalley
