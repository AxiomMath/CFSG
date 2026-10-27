module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassKillBasic
public import CFSG.LieType.Chevalley.ParabolicRadicalSelfCentralizing

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped commutatorElement

variable {τ : Tag}

variable {K : Type} [Field K]


theorem classKill_comm_perp [CharP K 2] {J : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∈ J)
    (hstr : ∀ δ ∈ parabolicPosRoots τ J, ¬ IsRoot τ (δ + (2 : ℤ) • Pi.single i 1))
    (c : K) {z : ModGL τ K} (hz : z ∈ rootSpan τ K (classKillPerp τ J i)) :
    pinnedX τ K (Pi.single i 1) c * z = z * pinnedX τ K (Pi.single i 1) c := by
  have hle : rootSpan τ K (classKillPerp τ J i) ≤
      Subgroup.centralizer {pinnedX τ K (Pi.single i 1) c} := by
    rw [rootSpan_eq_closure, Subgroup.closure_le]
    rintro _ ⟨γ, hγ, g, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hγΨ := classKillPerp_subset hγ
    have hne : Pi.single i 1 ≠ γ := fun h => hγΨ.2 h.symm
    have hne' : Pi.single i 1 ≠ -γ := by
      intro h
      have hh := hγ.1.2.2
      rw [show γ = -Pi.single i 1 by rw [h, neg_neg], height_neg, height_single] at hh
      omega
    obtain ⟨L, -, hnil, -, hform⟩ := classKill_commutator_factors (R := K) CharTwo.two_eq_zero
      (isRoot_single τ i) hγ.1.2.1 hne hne'
    have hL : L = [] := hnil (by
      rw [add_comm]
      exact (not_isRoot_add_sub_of_classKillPair hi hstr hγ.1 hγ.2).1)
    have h1 := hform c g
    rw [hL, List.map_nil, List.prod_nil] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  exact Subgroup.mem_centralizer_iff.1 (hle hz) _ rfl

theorem classKill_comm_add_single [CharP K 2] {J : Set (Fin τ.rank)} {i : Fin τ.rank}
    (hi : i ∈ J) (hstr : ∀ δ ∈ parabolicPosRoots τ J, ¬ IsRoot τ (δ + (2 : ℤ) • Pi.single i 1))
    {δ : Fin τ.rank → ℤ} (hδ : δ ∈ parabolicPosRoots τ J \ {Pi.single i 1})
    (hδa : IsRoot τ (δ + Pi.single i 1)) (c e : K) :
    pinnedX τ K (Pi.single i 1) c * pinnedX τ K (δ + Pi.single i 1) e =
      pinnedX τ K (δ + Pi.single i 1) e * pinnedX τ K (Pi.single i 1) c := by
  have hε := classKill_add_smul_single_mem (m := 1) hi hδ (by simpa using hδa)
  rw [one_smul] at hε
  have hne : Pi.single i 1 ≠ δ + Pi.single i 1 := by
    intro h
    have h0 : δ = 0 := by
      have := congrArg (· - Pi.single i 1) h
      simpa using this.symm
    have := hδ.1.2.2
    rw [h0] at this
    simp [height] at this
  have hne' : Pi.single i 1 ≠ -(δ + Pi.single i 1) := by
    intro h
    have hh := hε.1.2.2
    rw [(neg_eq_iff_eq_neg.2 h).symm, height_neg, height_single] at hh
    omega
  obtain ⟨L, -, hnil, -, hform⟩ := classKill_commutator_factors (R := K) CharTwo.two_eq_zero
    (isRoot_single τ i) hδa hne hne'
  have hL : L = [] := hnil (by
    have h2 : Pi.single i 1 + (δ + Pi.single i 1) = δ + (2 : ℤ) • Pi.single i 1 := by
      rw [two_smul]
      abel
    rw [h2]
    exact hstr δ hδ.1)
  have h1 := hform c e
  rw [hL, List.map_nil, List.prod_nil] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem classKill_conj_bottom [CharP K 2] {J : Set (Fin τ.rank)} {i : Fin τ.rank}
    (hstr : ∀ δ ∈ parabolicPosRoots τ J, ¬ IsRoot τ (δ + (2 : ℤ) • Pi.single i 1))
    {R' : Set (Fin τ.rank → ℤ)}
    (hnorm : ∀ v ∈ rootSpan τ K (parabolicPosRoots τ J), ∀ m ∈ rootSpan τ K R',
      v * m * v⁻¹ ∈ rootSpan τ K R')
    {δ : Fin τ.rank → ℤ} (hδ : δ ∈ parabolicPosRoots τ J \ {Pi.single i 1})
    (hδa : IsRoot τ (δ + Pi.single i 1)) (hδs : ¬ IsRoot τ (δ - Pi.single i 1))
    (hR' : ∀ p q : ℕ, 1 ≤ p → 2 ≤ q → IsRoot τ (p • Pi.single i 1 + q • δ) →
      p • Pi.single i 1 + q • δ ∈ R') (c g : K) :
    (pinnedX τ K (δ + Pi.single i 1) (c * g) * pinnedX τ K δ g)⁻¹ *
        (pinnedX τ K (Pi.single i 1) c * pinnedX τ K δ g * pinnedX τ K (Pi.single i 1) c) ∈
      rootSpan τ K R' := by
  have hδr : IsRoot τ δ := hδ.1.2.1
  have hδne : δ ≠ Pi.single i 1 := hδ.2
  have hδne' : δ ≠ -Pi.single i 1 := by
    intro h
    have hh := hδ.1.2.2
    rw [h, height_neg, height_single] at hh
    omega
  have hne : Pi.single i 1 ≠ δ := fun h => hδne h.symm
  have hne' : Pi.single i 1 ≠ -δ := fun h => hδne' (by rw [h, neg_neg])
  obtain ⟨L, hLf, -, hcons, hform⟩ := classKill_commutator_factors (R := K) CharTwo.two_eq_zero
    (isRoot_single τ i) hδr hne hne'
  obtain ⟨f, L', rfl, hf1, hf2, hL', hC⟩ := hcons (by rwa [add_comm])
  have hC1 : (f.2.2.2 : K) = 1 := hC hδs
  set P := (L'.map fun f => pinnedX τ K (f.1 • Pi.single i 1 + f.2.1 • δ)
    ((f.2.2.2 : K) * c ^ f.1 * g ^ f.2.1)).prod with hPdef
  have hP : P ∈ rootSpan τ K R' := by
    refine classKill_list_prod_mem L' _ _ fun h hh => ?_
    obtain ⟨hp1, hq1, hr⟩ := hLf h (List.mem_cons_of_mem _ hh)
    by_cases hq : h.2.1 = 1
    · exfalso
      have hp2 : h.1 ≠ 1 := fun hp => hL' h hh ⟨hp, hq⟩
      refine classKill_not_isRoot_add_smul_single hδr hδne hδne' (hstr δ hδ.1)
        (m := (h.1 : ℤ)) (by omega) ?_
      rw [hq, one_smul, add_comm, ← natCast_zsmul] at hr
      exact hr
    · exact hR' _ _ hp1 (by omega) hr
  have hcomm := hform c g
  simp only [List.map_cons, List.prod_cons, hf1, hf2, one_smul, pow_one, hC1, one_mul] at hcomm
  rw [← hPdef] at hcomm
  have hAinv : (pinnedX τ K (Pi.single i 1) c)⁻¹ = pinnedX τ K (Pi.single i 1) c := by
    rw [pinnedX_neg, CharTwo.neg_eq]
  have e1 : pinnedX τ K (Pi.single i 1) c * pinnedX τ K δ g * pinnedX τ K (Pi.single i 1) c =
      ⁅pinnedX τ K (Pi.single i 1) c, pinnedX τ K δ g⁆ * pinnedX τ K δ g := by
    rw [commutatorElement_def, hAinv]
    group
  rw [e1, hcomm, add_comm (Pi.single i 1) δ]
  have e2 : (pinnedX τ K (δ + Pi.single i 1) (c * g) * pinnedX τ K δ g)⁻¹ *
      (pinnedX τ K (δ + Pi.single i 1) (c * g) * P * pinnedX τ K δ g) =
      (pinnedX τ K δ g)⁻¹ * P * (pinnedX τ K δ g)⁻¹⁻¹ := by
    group
  rw [e2]
  exact hnorm _ (inv_mem (classKill_pinnedX_mem hδ.1 g)) _ hP

theorem classKill_step_perp {J : Set (Fin τ.rank)} {i : Fin τ.rank} {R : Set (Fin τ.rank → ℤ)}
    (hR : ClassKillAdmissible τ J i R) {δ : Fin τ.rank → ℤ} (hδR : δ ∈ R)
    (hM1 : ∀ δ' ∈ R, classKillDeg i δ ≤ classKillDeg i δ')
    (hM2 : ∀ δ' ∈ R, classKillDeg i δ' = classKillDeg i δ → δ i ≤ δ' i)
    (hδa : ¬ IsRoot τ (δ + Pi.single i 1)) (hsub : ¬ IsRoot τ (δ - Pi.single i 1))
    {z n : ModGL τ K} (hz : z ∈ rootSpan τ K (classKillPerp τ J i)) (hn : n ∈ rootSpan τ K R) :
    ∃ R' : Set (Fin τ.rank → ℤ), ClassKillAdmissible τ J i R' ∧ R'.ncard < R.ncard ∧
      ∃ z' ∈ rootSpan τ K (classKillPerp τ J i), ∃ n' ∈ rootSpan τ K R', z * n = z' * n' := by
  have hδΨ := hR.subset hδR
  have hδJ : δ ∈ parabolicPosRoots τ J := hδΨ.1
  have hδr : IsRoot τ δ := hδJ.2.1
  have hδne' : δ ≠ -Pi.single i 1 := by
    intro h
    have hh := hδJ.2.2
    rw [h, height_neg, height_single] at hh
    omega
  have hRpos : ∀ β ∈ R, IsRoot τ β ∧ 0 < height β := fun β hβ => (hR.subset hβ).1.2
  have hRclosed : ∀ β ∈ R, ∀ γ ∈ R, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ R := fun β hβ γ hγ a b ha hb hr =>
    hR.ideal β (hR.subset hβ).1 γ hγ a b ha hb hr
  have hfin : R.Finite := (finite_setOf_isRoot τ).subset fun β hβ => (hRpos β hβ).1
  have hpair : classKillPair i δ = 0 := classKillPair_eq_zero hδr hδΨ.2 hδne' hδa hsub
  have hδperp : δ ∈ classKillPerp τ J i := ⟨hδJ, hpair⟩
  have hR' : ClassKillAdmissible τ J i (R \ {δ}) := by
    refine ⟨fun x hx => hR.subset hx.1, fun γ hγ δ' hδ' a b ha hb hr => ?_,
      fun δ' hδ' hr => ?_⟩
    · refine ⟨hR.ideal γ hγ δ' hδ'.1 a b ha hb hr, fun h => ?_⟩
      have heq : a • γ + b • δ' = δ + (0 : ℤ) • Pi.single i 1 := by
        rw [zero_smul, add_zero]; exact Set.mem_singleton_iff.1 h
      have := (classKill_eq_of_combo hR hM1 hM2 hγ hδ'.1 ha hb (by norm_num) heq).2
      norm_num at this
    · refine ⟨hR.down δ' hδ'.1 hr, fun h => ?_⟩
      have h' : δ' = δ + Pi.single i 1 := by rw [← Set.mem_singleton_iff.1 h]; abel
      exact hδa (h' ▸ (hR.subset hδ'.1).1.2.1)
  refine ⟨R \ {δ}, hR', Set.ncard_sdiff_singleton_lt_of_mem hδR hfin, ?_⟩
  obtain ⟨d, hd⟩ := classKill_split hRpos hRclosed ![δ] (fun a b _ => Subsingleton.elim a b)
    (fun j => by fin_cases j; exact hδR) hn
  rw [Matrix.range_cons_empty] at hd
  have hprod : (List.ofFn fun j => pinnedX τ K (![δ] j) (d j)).prod = pinnedX τ K δ (d 0) := by
    rw [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    rfl
  rw [hprod] at hd
  exact ⟨z * pinnedX τ K δ (d 0), mul_mem hz (classKill_pinnedX_mem hδperp _), _, hd,
    by group⟩

theorem classKill_step_bottom [CharP K 2] {J : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∈ J)
    (hstr : ∀ δ ∈ parabolicPosRoots τ J, ¬ IsRoot τ (δ + (2 : ℤ) • Pi.single i 1))
    {c : K} (hc : c ≠ 0) {R : Set (Fin τ.rank → ℤ)}
    (hR : ClassKillAdmissible τ J i R) {δ : Fin τ.rank → ℤ} (hδR : δ ∈ R)
    (hM1 : ∀ δ' ∈ R, classKillDeg i δ ≤ classKillDeg i δ')
    (hM2 : ∀ δ' ∈ R, classKillDeg i δ' = classKillDeg i δ → δ i ≤ δ' i)
    (hδa : IsRoot τ (δ + Pi.single i 1)) (hsub : ¬ IsRoot τ (δ - Pi.single i 1))
    {z n : ModGL τ K} (hz : z ∈ rootSpan τ K (classKillPerp τ J i)) (hn : n ∈ rootSpan τ K R)
    (hcoc : pinnedX τ K (Pi.single i 1) c * (z * n) * pinnedX τ K (Pi.single i 1) c =
      (z * n)⁻¹) :
    ∃ R' : Set (Fin τ.rank → ℤ), ClassKillAdmissible τ J i R' ∧ R'.ncard < R.ncard ∧
      ∃ p ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}),
        ∃ n'' ∈ rootSpan τ K R',
          pinnedX τ K (Pi.single i 1) c * p * pinnedX τ K (Pi.single i 1) c * (z * n) * p⁻¹ =
            z * n'' := by
  have hAA : pinnedX τ K (Pi.single i 1) c * pinnedX τ K (Pi.single i 1) c = 1 :=
    classKill_pinnedX_mul_self _ _
  have hαJ : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ parabolicPosRoots τ J := by
    refine ⟨⟨isRoot_single τ i, fun l hl => ?_⟩, isRoot_single τ i, by rw [height_single]; omega⟩
    have hli : l ≠ i := fun h => hl (h ▸ hi)
    simp [Pi.single_eq_of_ne hli]
  have hAV : pinnedX τ K (Pi.single i 1) c ∈ rootSpan τ K (parabolicPosRoots τ J) :=
    classKill_pinnedX_mem hαJ c
  have hzV : z ∈ rootSpan τ K (parabolicPosRoots τ J) :=
    classKill_rootSpan_mono (fun δ hδ => hδ.1) hz
  have hzU : z ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}) :=
    classKill_rootSpan_mono classKillPerp_subset hz
  have hRpos : ∀ β ∈ R, IsRoot τ β ∧ 0 < height β := fun β hβ => (hR.subset hβ).1.2
  have hRclosed : ∀ β ∈ R, ∀ γ ∈ R, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ R := fun β hβ γ hγ a b ha hb hr =>
    hR.ideal β (hR.subset hβ).1 γ hγ a b ha hb hr
  have hfin : R.Finite := (finite_setOf_isRoot τ).subset fun β hβ => (hRpos β hβ).1
  have hδΨ := hR.subset hδR
  have hδJ : δ ∈ parabolicPosRoots τ J := hδΨ.1
  have hδr : IsRoot τ δ := hδJ.2.1
  have hδne : δ ≠ Pi.single i 1 := hδΨ.2
  have hε : δ + Pi.single i 1 ∈ R := by
    have h := hR.ideal _ hαJ δ hδR 1 1 le_rfl le_rfl
      (by rw [one_smul, one_smul, add_comm]; exact hδa)
    rwa [one_smul, one_smul, add_comm] at h
  have hεΨ := hR.subset hε
  have hδε : δ ≠ δ + Pi.single i 1 := fun h => by
    have := congrFun h i
    simp at this
  have hR' : ClassKillAdmissible τ J i (R \ {δ, δ + Pi.single i 1}) := by
    refine ⟨fun x hx => hR.subset hx.1, fun γ hγ δ' hδ' a b ha hb hr => ?_,
      fun δ' hδ' hr => ?_⟩
    · refine ⟨hR.ideal γ hγ δ' hδ'.1 a b ha hb hr, fun h => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · have heq : a • γ + b • δ' = δ + (0 : ℤ) • Pi.single i 1 := by
          rw [zero_smul, add_zero]; exact h
        have := (classKill_eq_of_combo hR hM1 hM2 hγ hδ'.1 ha hb (by norm_num) heq).2
        norm_num at this
      · have heq : a • γ + b • δ' = δ + (1 : ℤ) • Pi.single i 1 := by
          rw [one_smul]; exact h
        have := (classKill_eq_of_combo hR hM1 hM2 hγ hδ'.1 ha hb le_rfl heq).1
        exact hδ'.2 (Or.inl this)
    · refine ⟨hR.down δ' hδ'.1 hr, fun h => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · exact hδ'.2 (Or.inr (Set.mem_singleton_iff.2 (by rw [← h]; abel)))
      · have h' : δ' = δ + (2 : ℤ) • Pi.single i 1 := by
          rw [two_smul, ← add_assoc, ← h]; abel
        exact hstr δ hδJ (h' ▸ (hR.subset hδ'.1).1.2.1)
  set R' := R \ {δ, δ + Pi.single i 1} with hR'def
  refine ⟨R', hR', Set.ncard_lt_ncard (LE.le.ssubset_of_mem_notMem Set.sdiff_subset
    hδR (fun h => h.2 (Or.inl rfl))) hfin, ?_⟩
  have hR'sub : R' ⊆ parabolicPosRoots τ J := fun x hx => (hR'.subset hx).1
  have hR'pos : ∀ β ∈ R', IsRoot τ β ∧ 0 < height β := fun β hβ => (hR'.subset hβ).1.2
  have hR'closed : ∀ β ∈ R', ∀ γ ∈ R', ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • β + b • γ) → a • β + b • γ ∈ R' := fun β hβ γ hγ a b ha hb hr =>
    hR'.ideal β (hR'.subset hβ).1 γ hγ a b ha hb hr
  have hnorm' : ∀ v ∈ rootSpan τ K (parabolicPosRoots τ J), ∀ m ∈ rootSpan τ K R',
      v * m * v⁻¹ ∈ rootSpan τ K R' := fun v hv m hm =>
    classKill_conj_mem hR'sub hR'.ideal hv hm
  have hNV : rootSpan τ K R' ≤ rootSpan τ K (parabolicPosRoots τ J) :=
    classKill_rootSpan_mono hR'sub
  have hbig : ∀ ε ∈ R, classKillDeg i δ < classKillDeg i ε → ε ∈ R' := by
    intro ε hε' hlt
    refine ⟨hε', fun h => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact lt_irrefl _ hlt
    · rw [classKillDeg_add_single] at hlt
      exact lt_irrefl _ hlt
  have hβδ : ∀ γ ∈ parabolicPosRoots τ J \ {Pi.single i 1}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • γ + b • δ) → a • γ + b • δ ∈ R' := by
    intro γ hγ a b ha hb hr
    refine hbig _ (hR.ideal γ hγ.1 δ hδR a b ha hb hr) ?_
    rw [classKillDeg_add, classKillDeg_nsmul, classKillDeg_nsmul]
    have h1 := one_le_classKillDeg (i := i) hγ.1.2.1 hγ.1.2.2 hγ.2
    have h2 := one_le_classKillDeg (i := i) hδr hδJ.2.2 hδne
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hβε : ∀ γ ∈ parabolicPosRoots τ J \ {Pi.single i 1}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • γ + b • (δ + Pi.single i 1)) →
        a • γ + b • (δ + Pi.single i 1) ∈ R' := by
    intro γ hγ a b ha hb hr
    refine hbig _ (hR.ideal γ hγ.1 _ hε a b ha hb hr) ?_
    rw [classKillDeg_add, classKillDeg_nsmul, classKillDeg_nsmul, classKillDeg_add_single]
    have h1 := one_le_classKillDeg (i := i) hγ.1.2.1 hγ.1.2.2 hγ.2
    have h2 := one_le_classKillDeg (i := i) hδr hδJ.2.2 hδne
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hq2 : ∀ p q : ℕ, 1 ≤ p → 2 ≤ q → IsRoot τ (p • Pi.single i 1 + q • δ) →
      p • Pi.single i 1 + q • δ ∈ R' := by
    intro p q hp hq hr
    refine hbig _ (hR.ideal _ hαJ δ hδR p q hp (by omega) hr) ?_
    rw [classKillDeg_add, classKillDeg_nsmul, classKillDeg_nsmul, classKillDeg_single]
    have h2 := one_le_classKillDeg (i := i) hδr hδJ.2.2 hδne
    have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hinj : Function.Injective ![δ, δ + Pi.single i 1] := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd hab hδε
    · exact absurd hab.symm hδε
    · rfl
  obtain ⟨d, hd⟩ := classKill_split hRpos hRclosed ![δ, δ + Pi.single i 1] hinj
    (fun j => by fin_cases j; exacts [hδR, hε]) hn
  rw [Matrix.range_cons_cons_empty] at hd
  have hprod : (List.ofFn fun j => pinnedX τ K (![δ, δ + Pi.single i 1] j) (d j)).prod =
      pinnedX τ K δ (d 0) * pinnedX τ K (δ + Pi.single i 1) (d 1) := by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_cons,
      List.prod_nil, mul_one]
    rfl
  rw [hprod] at hd
  set n' := (pinnedX τ K δ (d 0) * pinnedX τ K (δ + Pi.single i 1) (d 1))⁻¹ * n with hn'def
  have hn_eq : n = pinnedX τ K δ (d 0) * pinnedX τ K (δ + Pi.single i 1) (d 1) * n' := by
    rw [hn'def]
    group
  have hYV : ∀ g : K, pinnedX τ K δ g ∈ rootSpan τ K (parabolicPosRoots τ J) :=
    classKill_pinnedX_mem hδJ
  have hXV : ∀ e : K,
      pinnedX τ K (δ + Pi.single i 1) e ∈ rootSpan τ K (parabolicPosRoots τ J) :=
    classKill_pinnedX_mem hεΨ.1
  have hYU : ∀ g : K,
      pinnedX τ K δ g ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}) :=
    classKill_pinnedX_mem hδΨ
  have hXU : ∀ e : K, pinnedX τ K (δ + Pi.single i 1) e ∈
      rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}) :=
    classKill_pinnedX_mem hεΨ
  have hAz := classKill_comm_perp hi hstr c hz
  have hconjY := classKill_conj_bottom hstr hnorm' hδΨ hδa hsub hq2 c
  have hAX := classKill_comm_add_single hi hstr hδΨ hδa c
  have hAXA : ∀ e : K, (pinnedX τ K (δ + Pi.single i 1) e)⁻¹ *
      (pinnedX τ K (Pi.single i 1) c * pinnedX τ K (δ + Pi.single i 1) e *
        pinnedX τ K (Pi.single i 1) c) ∈ rootSpan τ K R' := fun e => by
    rw [hAX e, mul_assoc, hAA, mul_one, inv_mul_cancel]
    exact one_mem _
  have hcoc' : pinnedX τ K (Pi.single i 1) c *
      (z * (pinnedX τ K δ (d 0) * pinnedX τ K (δ + Pi.single i 1) (d 1) * n')) *
      pinnedX τ K (Pi.single i 1) c =
      (z * (pinnedX τ K δ (d 0) * pinnedX τ K (δ + Pi.single i 1) (d 1) * n'))⁻¹ := by
    rw [← hn_eq]
    exact hcoc
  have hzzw := classKill_rel_cocycle hNV hnorm' hAV hzV (hYV (d 0)) (hXV (d 1)) (hXV (c * d 0))
    hd hAA hAz (classKill_pinnedX_mul_self _ _) (classKill_pinnedX_mul_self _ _)
    (hconjY (d 0)) (hAXA (d 1))
    (classKill_commutator_mem hnorm' hδJ hβδ hzU (d 0))
    (classKill_commutator_mem hnorm' hεΨ.1 hβε hzU (d 1))
    (classKill_commutator_mem hnorm' hδJ hβδ (hXU (d 1)) (d 0)) hcoc'
  have hzzR : z * z ∈ rootSpan τ K R := by
    have e : z * z = (z * z * pinnedX τ K (δ + Pi.single i 1) (c * d 0)) *
        (pinnedX τ K (δ + Pi.single i 1) (c * d 0))⁻¹ := by group
    rw [e]
    exact mul_mem (classKill_rootSpan_mono Set.sdiff_subset hzzw)
      (inv_mem (classKill_pinnedX_mem hε _))
  have hzz' : z * z ∈ rootSpan τ K R' := by
    have h := classKill_rootSpan_inf_le_inter (S := classKillPerp τ J i) (T := R)
      (fun β hβ => hβ.1.2) classKillPerp_closed hRpos hRclosed (mul_mem hz hz) hzzR
    refine classKill_rootSpan_mono ?_ h
    rintro x ⟨hxP, hxR⟩
    refine ⟨hxR, fun h => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact (not_isRoot_add_sub_of_classKillPair hi hstr hxP.1 hxP.2).1 hδa
    · have h2 := (not_isRoot_add_sub_of_classKillPair hi hstr hxP.1 hxP.2).2
      rw [add_sub_cancel_right] at h2
      exact h2 hδr
  have hXN : pinnedX τ K (δ + Pi.single i 1) (c * d 0) ∈ rootSpan τ K R' := by
    have e : pinnedX τ K (δ + Pi.single i 1) (c * d 0) =
        (z * z)⁻¹ * (z * z * pinnedX τ K (δ + Pi.single i 1) (c * d 0)) := by group
    rw [e]
    exact mul_mem (inv_mem hzz') hzzw
  have hcd : c * d 0 = 0 := by
    by_contra hne
    have := mem_of_pinnedX_mem_rootSpan hR'pos hR'closed hεΨ.1.2 hne hXN
    exact this.2 (Or.inr rfl)
  have hd0 : d 0 = 0 := (mul_eq_zero.1 hcd).resolve_left hc
  have hcg : c * (d 1 * c⁻¹) = d 1 := by
    rw [mul_comm (d 1), ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have h1k : (pinnedX τ K (δ + Pi.single i 1) (d 1) * pinnedX τ K δ (d 1 * c⁻¹))⁻¹ *
      (pinnedX τ K (Pi.single i 1) c * pinnedX τ K δ (d 1 * c⁻¹) *
        pinnedX τ K (Pi.single i 1) c) ∈ rootSpan τ K R' := by
    have := hconjY (d 1 * c⁻¹)
    rwa [hcg] at this
  have hkill := classKill_rel_kill hNV hnorm' hAV hzV (hYV (d 1 * c⁻¹)) (hXV (d 1)) hd
    (classKill_pinnedX_mul_self _ _) h1k
    (classKill_commutator_mem hnorm' hδJ hβδ hzU (d 1 * c⁻¹))
    (classKill_commutator_mem hnorm' hεΨ.1 hβε hzU (d 1))
    (classKill_commutator_mem hnorm' hεΨ.1 hβε (hYU (d 1 * c⁻¹)) (d 1))
  have hn2 : n = pinnedX τ K (δ + Pi.single i 1) (d 1) * n' := by
    rw [hn_eq, hd0, pinnedX_zero, one_mul]
  refine ⟨pinnedX τ K δ (d 1 * c⁻¹), hYU _, z⁻¹ * (pinnedX τ K (Pi.single i 1) c *
    pinnedX τ K δ (d 1 * c⁻¹) * pinnedX τ K (Pi.single i 1) c * (z * n) *
      (pinnedX τ K δ (d 1 * c⁻¹))⁻¹), by rw [hn2]; exact hkill, ?_⟩
  rw [mul_inv_cancel_left]

theorem classKill_core [CharP K 2] {J : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∈ J)
    (hstr : ∀ δ ∈ parabolicPosRoots τ J, ¬ IsRoot τ (δ + (2 : ℤ) • Pi.single i 1))
    {c : K} (hc : c ≠ 0) (k : ℕ) :
    ∀ R : Set (Fin τ.rank → ℤ), R.ncard = k → ClassKillAdmissible τ J i R →
      ∀ z ∈ rootSpan τ K (classKillPerp τ J i), ∀ n ∈ rootSpan τ K R,
        pinnedX τ K (Pi.single i 1) c * (z * n) * pinnedX τ K (Pi.single i 1) c = (z * n)⁻¹ →
        ∃ p ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}),
          pinnedX τ K (Pi.single i 1) c * p * pinnedX τ K (Pi.single i 1) c * (z * n) * p⁻¹ ∈
            rootSpan τ K (classKillPerp τ J i) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro R hRk hR z hz n hn hcoc
  have hAA : pinnedX τ K (Pi.single i 1) c * pinnedX τ K (Pi.single i 1) c = 1 :=
    classKill_pinnedX_mul_self _ _
  rcases R.eq_empty_or_nonempty with hR0 | hRne
  · subst hR0
    have hn1 : n = 1 := by
      have hbot : rootSpan τ K (∅ : Set (Fin τ.rank → ℤ)) = ⊥ :=
        iSup₂_eq_bot.2 fun β hβ => absurd hβ (Set.notMem_empty β)
      rw [hbot, Subgroup.mem_bot] at hn
      exact hn
    refine ⟨1, one_mem _, ?_⟩
    rw [hn1, mul_one, mul_one, inv_one, mul_one, hAA, one_mul]
    exact hz
  obtain ⟨δ, hδR, hM1, hM2⟩ := classKill_exists_min hR hRne
  have hsub : ¬ IsRoot τ (δ - Pi.single i 1) := by
    intro h
    have hmem := hR.down δ hδR h
    have hdeg : classKillDeg i (δ - Pi.single i 1) = classKillDeg i δ := by
      rw [sub_eq_add_neg, ← neg_one_smul ℤ (Pi.single i 1 : Fin τ.rank → ℤ),
        classKillDeg_add_smul_single]
    have := hM2 _ hmem hdeg
    simp at this
  by_cases hδa : IsRoot τ (δ + Pi.single i 1)
  · obtain ⟨R', hR', hcard, p, hp, n'', hn'', heq⟩ :=
      classKill_step_bottom hi hstr hc hR hδR hM1 hM2 hδa hsub hz hn hcoc
    have hcoc'' : pinnedX τ K (Pi.single i 1) c * (z * n'') * pinnedX τ K (Pi.single i 1) c =
        (z * n'')⁻¹ := by
      rw [← heq]
      exact classKill_tw_cocycle hAA hcoc
    obtain ⟨p', hp', hres⟩ := ih _ (hRk ▸ hcard) R' rfl hR' z hz n'' hn'' hcoc''
    refine ⟨p' * p, mul_mem hp' hp, ?_⟩
    rw [← classKill_tw_comp hAA, heq]
    exact hres
  · obtain ⟨R', hR', hcard, z', hz', n', hn', heq⟩ :=
      classKill_step_perp hR hδR hM1 hM2 hδa hsub hz hn
    rw [heq] at hcoc ⊢
    exact ih _ (hRk ▸ hcard) R' rfl hR' z' hz' n' hn' hcoc

theorem exists_conj_eq_mul_of_classKillPerp [CharP K 2] (J : Set (Fin τ.rank)) {i : Fin τ.rank}
    (hi : i ∈ J)
    (hstr : ∀ δ ∈ parabolicPosRoots τ J, ¬ IsRoot τ (δ + (2 : ℤ) • Pi.single i 1))
    {c : K} (hc : c ≠ 0) {u : ModGL τ K}
    (hu : u ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}))
    (h2 : (pinnedX τ K (Pi.single i 1) c * u) ^ 2 = 1) :
    ∃ p ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}),
      ∃ u'' ∈ rootSpan τ K (classKillPerp τ J i),
        p * (pinnedX τ K (Pi.single i 1) c * u) * p⁻¹ = pinnedX τ K (Pi.single i 1) c * u'' := by
  have hAA : pinnedX τ K (Pi.single i 1) c * pinnedX τ K (Pi.single i 1) c = 1 :=
    classKill_pinnedX_mul_self _ _
  have hcoc : pinnedX τ K (Pi.single i 1) c * (1 * u) * pinnedX τ K (Pi.single i 1) c =
      (1 * u)⁻¹ := by
    rw [one_mul]
    have h2' : pinnedX τ K (Pi.single i 1) c * u * (pinnedX τ K (Pi.single i 1) c * u) = 1 := by
      rw [← pow_two]
      exact h2
    calc pinnedX τ K (Pi.single i 1) c * u * pinnedX τ K (Pi.single i 1) c
        = pinnedX τ K (Pi.single i 1) c * u * (pinnedX τ K (Pi.single i 1) c * u) * u⁻¹ := by
          group
      _ = u⁻¹ := by rw [h2', one_mul]
  obtain ⟨p, hp, hres⟩ := classKill_core hi hstr hc _ _ rfl (classKillAdmissible_top hi) 1
    (one_mem _) u hu hcoc
  refine ⟨p, hp, _, hres, ?_⟩
  calc p * (pinnedX τ K (Pi.single i 1) c * u) * p⁻¹
      = pinnedX τ K (Pi.single i 1) c * pinnedX τ K (Pi.single i 1) c * p *
          (pinnedX τ K (Pi.single i 1) c * u) * p⁻¹ := by rw [hAA, one_mul]
    _ = pinnedX τ K (Pi.single i 1) c * (pinnedX τ K (Pi.single i 1) c * p *
          pinnedX τ K (Pi.single i 1) c * (1 * u) * p⁻¹) := by group

theorem exists_conj_eq_mul_of_perp [CharP K 2] (J : Set (Fin τ.rank)) {i : Fin τ.rank}
    (hi : i ∈ J)
    (hstr : ∀ δ ∈ parabolicPosRoots τ J, ¬ IsRoot τ (δ + (2 : ℤ) • Pi.single i 1))
    {c : K} (hc : c ≠ 0) {u : ModGL τ K}
    (hu : u ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}))
    (h2 : (pinnedX τ K (Pi.single i 1) c * u) ^ 2 = 1) :
    ∃ p ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}),
      ∃ u'' ∈ rootSpan τ K {δ ∈ parabolicPosRoots τ J |
          ¬ IsRoot τ (δ + Pi.single i 1) ∧ ¬ IsRoot τ (δ - Pi.single i 1)},
        p * (pinnedX τ K (Pi.single i 1) c * u) * p⁻¹ = pinnedX τ K (Pi.single i 1) c * u'' := by
  obtain ⟨p, hp, u'', hu'', heq⟩ := exists_conj_eq_mul_of_classKillPerp J hi hstr hc hu h2
  refine ⟨p, hp, u'', classKill_rootSpan_mono ?_ hu'', heq⟩
  intro δ hδ
  exact ⟨hδ.1, not_isRoot_add_sub_of_classKillPair hi hstr hδ.1 hδ.2⟩

theorem commute_pinnedX_of_mem_classKillPerp [CharP K 2] {J : Set (Fin τ.rank)} {i : Fin τ.rank}
    (hi : i ∈ J)
    (hstr : ∀ δ ∈ parabolicPosRoots τ J, ¬ IsRoot τ (δ + (2 : ℤ) • Pi.single i 1))
    {z : ModGL τ K} (hz : z ∈ rootSpan τ K (classKillPerp τ J i)) (c' : K) :
    pinnedX τ K (Pi.single i 1) c' * z = z * pinnedX τ K (Pi.single i 1) c' ∧
      pinnedX τ K (-Pi.single i 1) c' * z = z * pinnedX τ K (-Pi.single i 1) c' := by
  refine ⟨classKill_comm_perp hi hstr c' hz, ?_⟩
  have hle : rootSpan τ K (classKillPerp τ J i) ≤
      Subgroup.centralizer {pinnedX τ K (-Pi.single i 1) c'} := by
    rw [rootSpan_eq_closure, Subgroup.closure_le]
    rintro _ ⟨γ, hγ, g, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hγΨ := classKillPerp_subset hγ
    have hne : -Pi.single i 1 ≠ γ := by
      intro h
      have hh := hγ.1.2.2
      rw [← h, height_neg, height_single] at hh
      omega
    have hne' : -Pi.single i 1 ≠ -γ := fun h => hγΨ.2 (neg_injective h).symm
    obtain ⟨L, -, hnil, -, hform⟩ := classKill_commutator_factors (R := K) CharTwo.two_eq_zero
      (IsRoot.neg (isRoot_single τ i)) hγ.1.2.1 hne hne'
    have hL : L = [] := hnil (by
      rw [neg_add_eq_sub]
      exact (not_isRoot_add_sub_of_classKillPair hi hstr hγ.1 hγ.2).2)
    have h1 := hform c' g
    rw [hL, List.map_nil, List.prod_nil] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  exact Subgroup.mem_centralizer_iff.1 (hle hz) _ rfl

theorem exists_conj_eq_mul_of_classKillPerp_sq [CharP K 2] (J : Set (Fin τ.rank))
    {i : Fin τ.rank} (hi : i ∈ J)
    (hstr : ∀ δ ∈ parabolicPosRoots τ J, ¬ IsRoot τ (δ + (2 : ℤ) • Pi.single i 1))
    {c : K} (hc : c ≠ 0) {u : ModGL τ K}
    (hu : u ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}))
    (h2 : (pinnedX τ K (Pi.single i 1) c * u) ^ 2 = 1) :
    ∃ p ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}),
      ∃ u'' ∈ rootSpan τ K (classKillPerp τ J i), u'' ^ 2 = 1 ∧
        p * (pinnedX τ K (Pi.single i 1) c * u) * p⁻¹ = pinnedX τ K (Pi.single i 1) c * u'' := by
  obtain ⟨p, hp, u'', hu'', heq⟩ := exists_conj_eq_mul_of_classKillPerp J hi hstr hc hu h2
  refine ⟨p, hp, u'', hu'', ?_, heq⟩
  have hA := classKill_comm_perp hi hstr c hu''
  have hAA : pinnedX τ K (Pi.single i 1) c * pinnedX τ K (Pi.single i 1) c = 1 :=
    classKill_pinnedX_mul_self _ _
  have ht : (pinnedX τ K (Pi.single i 1) c * u'') ^ 2 = 1 := by
    rw [← heq, conj_pow, h2, mul_one, mul_inv_cancel]
  calc u'' ^ 2 = pinnedX τ K (Pi.single i 1) c * pinnedX τ K (Pi.single i 1) c * (u'' * u'') := by
        rw [hAA, one_mul, sq]
    _ = pinnedX τ K (Pi.single i 1) c * (pinnedX τ K (Pi.single i 1) c * u'') * u'' := by group
    _ = pinnedX τ K (Pi.single i 1) c * (u'' * pinnedX τ K (Pi.single i 1) c) * u'' := by
        rw [hA]
    _ = pinnedX τ K (Pi.single i 1) c * u'' * (pinnedX τ K (Pi.single i 1) c * u'') := by group
    _ = 1 := by rw [← sq, ht]

theorem exists_conj_eq_mul_of_classKillPerp_longSimple [CharP K 2] (J : Set (Fin τ.rank))
    {i : Fin τ.rank} (hi : i ∈ J) (hlong : i ∈ classKillLongSimple τ)
    {c : K} (hc : c ≠ 0) {u : ModGL τ K}
    (hu : u ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}))
    (h2 : (pinnedX τ K (Pi.single i 1) c * u) ^ 2 = 1) :
    ∃ p ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}),
      ∃ u'' ∈ rootSpan τ K (classKillPerp τ J i), u'' ^ 2 = 1 ∧
        p * (pinnedX τ K (Pi.single i 1) c * u) * p⁻¹ = pinnedX τ K (Pi.single i 1) c * u'' :=
  exists_conj_eq_mul_of_classKillPerp_sq J hi (classKill_hstr_of_mem_longSimple hlong J) hc hu h2

end CFSG.SeitzReduction
