module

public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralCentralizer
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.TrialityFold
open scoped Pointwise

section Folded

theorem foldChar_pow_eq_one_gen {G : Type*} [CommGroup G] {A B : G} {p : ℕ} (hA : A ^ p = 1)
    (hB : B ^ p = 1) (μ : ℤ × ℤ) : foldChar A B μ ^ p = 1 := by
  rw [foldChar, mul_pow, ← zpow_natCast, ← zpow_natCast (B ^ μ.2), ← zpow_mul, ← zpow_mul,
    mul_comm μ.1, mul_comm μ.2, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hA, hB, one_zpow,
    one_zpow, one_mul]

theorem eq_one_of_foldChar_long {G : Type*} [CommGroup G] {A B : G} (hA : A ^ 3 = 1)
    (hB : B ^ 3 = 1) {μ : ℤ × ℤ} (h1 : μ.1 % 3 = 0) (h2 : μ.2 % 3 ≠ 0)
    (hμ : foldChar A B μ = 1) : B = 1 := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, μ.1 = 3 * k := ⟨μ.1 / 3, by omega⟩
  have hA3 : A ^ (3 : ℤ) = 1 := by exact_mod_cast hA
  have hAμ : A ^ μ.1 = 1 := by rw [hk, zpow_mul, hA3, one_zpow]
  have hBμ : B ^ μ.2 = 1 := by
    have h := hμ
    rw [foldChar, hAμ, one_mul] at h
    exact h
  exact eq_one_of_pow_prime_of_zpow Nat.prime_three hB hBμ (by omega)

theorem false_of_det3 {G : Type*} [CommGroup G] {A B : G} (hB : B ^ 3 = 1) (hB1 : B ≠ 1)
    {x y : ℤ × ℤ} (hx : foldChar A B x = 1) (hy : foldChar A B y = 1)
    (hnd : ¬ ((3 : ℕ) : ℤ) ∣ (x.1 * y.2 - x.2 * y.1)) : False :=
  hB1 (eq_one_of_pow_prime_of_zpow Nat.prime_three hB (foldChar_det hx hy).2 hnd)

theorem not_dvd_three_of_emod {d : ℤ} (h : d % 3 ≠ 0) : ¬ ((3 : ℕ) : ℤ) ∣ d := by omega

theorem long_check : ∀ r ∈ g2FoldRoots, ∀ s ∈ g2FoldRoots,
    (r.1 * s.2 - r.2 * s.1 = 3 ∨ r.1 * s.2 - r.2 * s.1 = -3) → r.1 % 3 = 0 ∧ r.2 % 3 ≠ 0 := by
  decide

theorem fold_eq_or_neg3 {G : Type*} [CommGroup G] {A B : G} (hA : A ^ 3 = 1) (hB : B ^ 3 = 1)
    (hB1 : B ≠ 1) {μ ν : ℤ × ℤ} (hμ : μ ∈ g2FoldRoots) (hν : ν ∈ g2FoldRoots)
    (hμ1 : foldChar A B μ = 1) (hν1 : foldChar A B ν = 1) : ν = μ ∨ ν = -μ := by
  rcases det_check μ hμ ν hν with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h
    · exact false_of_det3 hB hB1 hμ1 hν1 (by rw [h]; omega)
    · exact false_of_det3 hB hB1 hμ1 hν1 (by rw [h]; omega)
    · have := long_check μ hμ ν hν (Or.inl h)
      exact hB1 (eq_one_of_foldChar_long hA hB this.1 this.2 hμ1)
    · exact false_of_det3 hB hB1 hμ1 hν1 (by rw [h]; omega)
    · exact false_of_det3 hB hB1 hμ1 hν1 (by rw [h]; omega)
    · have := long_check μ hμ ν hν (Or.inr h)
      exact hB1 (eq_one_of_foldChar_long hA hB this.1 this.2 hμ1)

theorem foldChar_eq_one_of_neg3 {G : Type*} [CommGroup G] {A B : G} (hA : A ^ 3 = 1)
    (hB : B ^ 3 = 1) {μ : ℤ × ℤ} (h : foldChar A B (-μ) = foldChar A B μ) :
    foldChar A B μ = 1 := by
  rw [foldChar_neg] at h
  have h2 : foldChar A B μ ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    nth_rewrite 1 [← h]
    exact inv_mul_cancel _
  exact eq_one_of_pow_prime_of_zpow Nat.prime_three (foldChar_pow_eq_one_gen hA hB μ) h2 (by omega)

theorem weylCands_classify3 : ∀ P ∈ weylCands, P = ((1, 0), (0, 1)) ∨
    ((P.1 - (1, 0)).1 % 3 = 0 ∧ (P.1 - (1, 0)).2 % 3 ≠ 0) ∨
    ((P.1 - (1, 0)).1 * (P.2 - (0, 1)).2 - (P.1 - (1, 0)).2 * (P.2 - (0, 1)).1) % 3 ≠ 0 ∨
    (P ≠ ((-1, 0), (0, -1)) ∧ ∃ μ ∈ g2FoldRoots, applyP P μ = -μ) := by
  decide

end Folded

section Group


variable {K : Type} [Field K] {a : Fin TwistTag.D4.tag.rank → Kˣ} {A B : Kˣ}

theorem foldPair_cases_of_stabilizer3 (h0 : a i0 = A) (h1 : a i1 = A) (h2 : a i2 = B)
    (h3 : a i3 = A) (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) (hB1 : B ≠ 1)
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4)
    (hwa : w ∈ rootCharStabilizer a) :
    w = 1 ∨ (foldPair w ≠ ((1, 0), (0, 1)) ∧ foldPair w ≠ ((-1, 0), (0, -1)) ∧
      ∃ μ ∈ g2FoldRoots, applyP (foldPair w) μ = -μ ∧ foldChar A B μ = 1) := by
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  right
  have hid : foldPair w ≠ ((1, 0), (0, 1)) := fun h => hw1 (eq_one_of_foldPair hw h)
  have hx := foldChar_foldPair_sub h0 h1 h2 h3 hwa i0
  have hy := foldChar_foldPair_sub h0 h1 h2 h3 hwa i2
  rw [fold_single0] at hx
  rw [fold_single2] at hy
  rcases weylCands_classify3 _ (foldPair_mem hw) with hP | ⟨hl1, hl2⟩ | hdet |
    ⟨hneg, μ, hμ, hμneg⟩
  · exact absurd hP hid
  · exact absurd (eq_one_of_foldChar_long hA hB hl1 hl2 hx) hB1
  · exact (false_of_det3 hB hB1 hx hy (not_dvd_three_of_emod hdet)).elim
  · refine ⟨hid, hneg, μ, hμ, hμneg, foldChar_eq_one_of_neg3 hA hB ?_⟩
    have h := hwa (μ.1 • (Pi.single i0 1 : Fin TwistTag.D4.tag.rank → ℤ) + μ.2 • Pi.single i2 1)
    rw [rootChar_eq_foldChar h0 h1 h2 h3, rootChar_eq_foldChar h0 h1 h2 h3, fold_smul hw,
      fold_comb, hμneg] at h
    exact h

theorem rootCharKernel_cases3 (h0 : a i0 = A) (h1 : a i1 = A) (h2 : a i2 = B) (h3 : a i3 = A)
    (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) (hB1 : B ≠ 1) :
    rootCharKernel a = ∅ ∨ ∃ α, IsRoot TwistTag.D4.tag α ∧ 0 < height α ∧
      rootCharKernel a = (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ∪
        -(TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) := by
  rcases (rootCharKernel a).eq_empty_or_nonempty with h | ⟨β, hβ⟩
  · exact Or.inl h
  right
  obtain ⟨hβr, hβ1⟩ := (mem_rootCharKernel_iff h0 h1 h2 h3).1 hβ
  obtain ⟨α, hαr, hαpos, hα1⟩ : ∃ α, IsRoot TwistTag.D4.tag α ∧ 0 < height α ∧
      foldChar A B (fold α) = 1 := by
    rcases lt_or_gt_of_ne hβr.height_ne_zero with hneg | hpos
    · refine ⟨-β, IsRoot.neg hβr, ?_, ?_⟩
      · rw [height_neg]
        omega
      · rw [fold_neg, foldChar_neg, hβ1, inv_one]
    · exact ⟨β, hβr, hpos, hβ1⟩
  refine ⟨α, hαr, hαpos, Set.ext fun γ => ?_⟩
  rw [mem_rootCharKernel_iff h0 h1 h2 h3, Set.mem_union, Set.mem_neg, Finset.mem_coe,
    Finset.mem_coe]
  constructor
  · rintro ⟨hγr, hγ1⟩
    rcases fold_eq_or_neg3 hA hB hB1 (fold_mem_of_isRoot hαr) (fold_mem_of_isRoot hγr) hα1
      hγ1 with h | h
    · exact Or.inl (mem_diagramOrbit_of_fold_eq hαr hγr h)
    · exact Or.inr (mem_diagramOrbit_of_fold_eq hαr (IsRoot.neg hγr) (by rw [fold_neg, h, neg_neg]))
  · rintro (h | h)
    · exact ⟨TwistTag.D4.isRoot_of_mem_diagramOrbit hαr h,
        by rw [fold_eq_of_mem_diagramOrbit h, hα1]⟩
    · have hγ := IsRoot.neg (TwistTag.D4.isRoot_of_mem_diagramOrbit hαr h)
      rw [neg_neg] at hγ
      refine ⟨hγ, ?_⟩
      rw [← neg_neg γ, fold_neg, foldChar_neg, fold_eq_of_mem_diagramOrbit h, hα1, inv_one]

theorem rootCharStabilizer_cases3 (h0 : a i0 = A) (h1 : a i1 = A) (h2 : a i2 = B)
    (h3 : a i3 = A) (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) (hB1 : B ≠ 1)
    {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) (hwa : w ∈ rootCharStabilizer a) :
    w = 1 ∨ ((rootCharKernel a).Nonempty ∧ ∀ v ∈ relWeylTwist TwistTag.D4,
      ∀ b : Fin TwistTag.D4.foldedTag.rank, (∀ i ∈ TwistTag.D4.orbit b,
        v • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ rootCharKernel a) →
        w = v * TwistTag.D4.orbitReflection b * v⁻¹) := by
  rcases foldPair_cases_of_stabilizer3 h0 h1 h2 h3 hA hB hB1 hw hwa with
    hw1 | ⟨hid, hneg, μ, hμ, hμneg, hμ1⟩
  · exact Or.inl hw1
  right
  obtain ⟨β, hβr, hβμ⟩ := exists_isRoot_fold_eq hμ
  refine ⟨⟨β, (mem_rootCharKernel_iff h0 h1 h2 h3).2 ⟨hβr, by rw [hβμ, hμ1]⟩⟩,
    fun v hv b hvb => ?_⟩
  have hi : TwistTag.D4.orbitMin b ∈ TwistTag.D4.orbit b := TwistTag.D4.orbitMin_mem b
  obtain ⟨hvr, hv1⟩ := (mem_rootCharKernel_iff h0 h1 h2 h3).1 (hvb _ hi)
  set μ₀ := fold (v • (Pi.single (TwistTag.D4.orbitMin b) 1 : Fin TwistTag.D4.tag.rank → ℤ))
    with hμ₀def
  have hμ₀ : μ₀ ∈ g2FoldRoots := fold_mem_of_isRoot hvr
  have hwμ₀ : applyP (foldPair w) μ₀ = -μ₀ := by
    rcases fold_eq_or_neg3 hA hB hB1 hμ hμ₀ hμ1 hv1 with h | h
    · rw [h, hμneg]
    · rw [h, applyP_neg, hμneg, neg_neg]
  set x := v * TwistTag.D4.orbitReflection b * v⁻¹ with hx
  have hxW : x ∈ relWeylTwist TwistTag.D4 :=
    mul_mem (mul_mem hv (TwistTag.D4.orbitReflection_mem b)) (inv_mem hv)
  have hxa : x ∈ rootCharStabilizer a := by
    refine kernelReflectionGroup_le a ?_
    rw [hx, ← MulAut.conj_apply, TwistTag.orbitReflection, CoxeterSystem.wordProd,
      map_list_prod]
    refine list_prod_mem fun y hy => ?_
    rw [List.map_map, List.mem_map] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    exact Subgroup.subset_closure
      ⟨v, j, hvb j ((TwistTag.D4.mem_orbitWord).1 hj), MulAut.conj_apply _ _⟩
  have hx1 : x ≠ 1 := fun h => TwistTag.D4.orbitReflection_ne_one b
    (mul_eq_left.1 (mul_inv_eq_one.1 h))
  rcases foldPair_cases_of_stabilizer3 h0 h1 h2 h3 hA hB hB1 hxW hxa with
    hx1' | ⟨hxid, hxneg, -⟩
  · exact absurd hx1' hx1
  have hxμ₀ : applyP (foldPair x) μ₀ = -μ₀ := by
    rw [hμ₀def, ← fold_smul hxW, hx, mul_smul, mul_smul, inv_smul_smul,
      TwistTag.D4.orbitReflection_smul_single hi, smul_neg, fold_neg]
  exact foldPair_injective hw hxW (weylCands_refl_unique _ (foldPair_mem hw) _
    (foldPair_mem hxW) μ₀ hμ₀ ⟨hid, hxid, hneg, hxneg, hwμ₀, hxμ₀⟩)

end Group

section Triality

variable {K : Type} [Field K] (σ : K ≃+* K)


theorem triality_toral_centralizer_cases3 {a : Fin TwistTag.D4.tag.rank → Kˣ} {A B : Kˣ}
    (h0 : a i0 = A) (h1 : a i1 = A) (h2 : a i2 = B) (h3 : a i3 = A) (hA : A ^ 3 = 1)
    (hB : B ^ 3 = 1) (hB1 : B ≠ 1) :
    (rootCharKernel a = ∅ ∧
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
          Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag a} =
        graphFixedRootTorus TwistTag.D4 K σ.toRingHom) ∨
    (∃ v ∈ relWeylTwist TwistTag.D4, ∃ b : Fin TwistTag.D4.foldedTag.rank,
      rootCharKernel a = fixedOrbitImage TwistTag.D4 v b ∪ -fixedOrbitImage TwistTag.D4 v b ∧
      (∀ β ∈ fixedOrbitImage TwistTag.D4 v b, 0 < height β) ∧
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
          Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag a} =
        graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊔
          graphFixedRootPair TwistTag.D4 K σ.toRingHom (fixedOrbitImage TwistTag.D4 v b) ∧
      ((graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
          Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag a} : Subgroup _) :
            Set (ModGL TwistTag.D4.tag K)) =
        (graphFixedRootTorus TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) *
          (graphFixedRootPair TwistTag.D4 K σ.toRingHom (fixedOrbitImage TwistTag.D4 v b) :
            Set (ModGL TwistTag.D4.tag K))) := by
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set H := graphFixedRootTorus TwistTag.D4 K σ.toRingHom with hH
  set d := rootDiagUnit TwistTag.D4.tag a with hd
  have hHle : H ≤ C ⊓ Subgroup.centralizer {d} := fun h hh =>
    Subgroup.mem_inf.2 ⟨graphFixedRootTorus_le _ _ _ hh, conj_eq_iff_mem_centralizer.1
      (conj_rootDiagUnit_of_mem_torusGroup a
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1)⟩
  rcases rootCharKernel_cases3 h0 h1 h2 h3 hA hB hB1 with hker | ⟨α, hαr, hαpos, hker⟩
  ·
    refine Or.inl ⟨hker, le_antisymm (fun g hg => ?_) hHle⟩
    obtain ⟨w, hwρ, hwa, h, hh, u, hu, v, hv, rfl⟩ :=
      graphFixed_toral_centralizer_Bruhat_factors TwistTag.D4 K σ a (Subgroup.mem_inf.1 hg).1
        (Subgroup.mem_inf.1 hg).2
    have hw1 : w = 1 := by
      rcases rootCharStabilizer_cases3 h0 h1 h2 h3 hA hB hB1 hwρ hwa with h1' | ⟨hne, -⟩
      · exact h1'
      · exact absurd hker (Set.nonempty_iff_ne_empty.1 hne)
    have hbot : ∀ S : Set (Fin TwistTag.D4.tag.rank → ℤ),
        rootSpan TwistTag.D4.tag K (rootCharKernel a ∩ S) = ⊥ := fun S => by
      rw [hker, Set.empty_inter]
      simp [rootSpan]
    rw [hbot, bot_inf_eq, Subgroup.mem_bot] at hu hv
    rw [hu, hv, hw1, canonicalRep_one, mul_one, mul_one, mul_one]
    exact hh
  ·
    right
    obtain ⟨v₀, hv₀, b, hO⟩ := TwistTag.D4.exists_diagramOrbit_eq hαr
    have hOset : (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) =
        fixedOrbitImage TwistTag.D4 v₀ b := by
      rw [hO, Finset.coe_image]
      rfl
    rw [hOset] at hker
    set O := fixedOrbitImage TwistTag.D4 v₀ b with hOdef
    set Q := graphFixedRootPair TwistTag.D4 K σ.toRingHom O with hQdef
    have hOpos : ∀ β ∈ O, 0 < height β := fun β hβ => by
      rw [← hOset] at hβ
      rw [TwistTag.D4.height_of_mem_diagramOrbit hβ]
      exact hαpos
    have hOroot : ∀ β ∈ O, IsRoot TwistTag.D4.tag β := fun β hβ =>
      isRoot_of_mem_fixedOrbitImage hβ
    have hOker : O ⊆ rootCharKernel a := fun β hβ => by
      rw [hker]
      exact Or.inl hβ
    have hnegOker : -O ⊆ rootCharKernel a := fun β hβ => by
      rw [hker]
      exact Or.inr hβ
    have hQrange := range_orbitConjRankOneHom (K := K) (σ := σ.toRingHom) hv₀ b
    have hQC : Q ≤ C := by
      rw [hQdef, ← hQrange]
      rintro _ ⟨g, rfl⟩
      exact orbitConjRankOneHom_mem_graphFixedRootGroup hv₀ b g
    have hQd : Q ≤ Subgroup.centralizer {d} :=
      sup_le (inf_le_left.trans (rootSpan_le_centralizer a hOker))
        (inf_le_left.trans (rootSpan_le_centralizer a hnegOker))
    have hpos : ∀ S : Set (Fin TwistTag.D4.tag.rank → ℤ),
        S ⊆ {β | IsRoot TwistTag.D4.tag β ∧ 0 < height β} → rootCharKernel a ∩ S ⊆ O := by
      intro S hS β ⟨hβk, hβS⟩
      rw [hker] at hβk
      rcases hβk with h | h
      · exact h
      · exfalso
        have h1 := hOpos _ (Set.mem_neg.1 h)
        have h2 := (hS hβS).2
        rw [height_neg] at h1
        omega
    have hle : C ⊓ Subgroup.centralizer {d} ≤ H ⊔ Q := by
      intro g hg
      obtain ⟨w, hwρ, hwa, h, hh, u, hu, v, hv, rfl⟩ :=
        graphFixed_toral_centralizer_Bruhat_factors TwistTag.D4 K σ a (Subgroup.mem_inf.1 hg).1
          (Subgroup.mem_inf.1 hg).2
      have huQ : u ∈ Q := Subgroup.mem_sup_left (Subgroup.mem_inf.2
        ⟨rootSpan_mono (hpos _ fun β hβ => hβ) (Subgroup.mem_inf.1 hu).1,
          (Subgroup.mem_inf.1 hu).2⟩)
      have hvQ : v ∈ Q := Subgroup.mem_sup_left (Subgroup.mem_inf.2
        ⟨rootSpan_mono (hpos _ fun β hβ => ⟨hβ.1, hβ.2.1⟩) (Subgroup.mem_inf.1 hv).1,
          (Subgroup.mem_inf.1 hv).2⟩)
      have hnw : canonicalRep (coxeterSystem TwistTag.D4.tag) K w ∈ H ⊔ Q := by
        rcases rootCharStabilizer_cases3 h0 h1 h2 h3 hA hB hB1 hwρ hwa with hw1 | ⟨-, hw⟩
        · rw [hw1, canonicalRep_one]
          exact one_mem _
        · rw [hw v₀ hv₀ b fun i hi => hOker ⟨i, hi, rfl⟩]
          obtain ⟨h', hh', he⟩ := exists_canonicalRep_eq_mul_orbitConjRankOneHom
            (K := K) (σ := σ.toRingHom) hv₀ b
          rw [he]
          refine mul_mem (Subgroup.mem_sup_left hh') (Subgroup.mem_sup_right ?_)
          rw [hQdef, ← hQrange]
          exact ⟨_, rfl⟩
      exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right huQ))
        hnw) (Subgroup.mem_sup_right hvQ)
    have heq : C ⊓ Subgroup.centralizer {d} = H ⊔ Q :=
      le_antisymm hle (sup_le hHle (le_inf hQC hQd))
    refine ⟨v₀, hv₀, b, hker, hOpos, heq, ?_⟩
    rw [heq]
    exact Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (graphFixedRootTorus_le_normalizer hOroot)

end Triality

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
