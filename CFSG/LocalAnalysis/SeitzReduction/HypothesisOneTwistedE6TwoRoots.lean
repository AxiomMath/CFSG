module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInnerRoots

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem coPair_permLattice {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    coPair τ i (permLattice π v) = coPair τ (π.symm i) v := by
  unfold coPair permLattice
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [← hπ (π.symm i) j, Equiv.apply_symm_apply]

theorem twistedE6_perm_symm_apply (i : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.perm.symm i = TwistTag.E6.perm i := by
  revert i
  decide

theorem twistedE6_perm_perm (i : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.perm (TwistTag.E6.perm i) = i := by
  revert i
  decide

theorem permLattice_twistedE6_perm_perm (v : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm v) = v := by
  funext j
  simp only [permLattice, Function.comp_apply, twistedE6_perm_symm_apply, twistedE6_perm_perm]

theorem coPair_permLattice_twistedE6 (i : Fin TwistTag.E6.tag.rank)
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    coPair TwistTag.E6.tag i (permLattice TwistTag.E6.perm v) =
      coPair TwistTag.E6.tag (TwistTag.E6.perm i) v := by
  rw [coPair_permLattice TwistTag.E6.cartan_perm, twistedE6_perm_symm_apply]

theorem isRoot_permLattice_twistedE6_iff {v : Fin TwistTag.E6.tag.rank → ℤ} :
    IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm v) ↔ IsRoot TwistTag.E6.tag v := by
  refine ⟨fun h => ?_, fun h => h.permLattice TwistTag.E6.cartan_perm⟩
  rw [← permLattice_twistedE6_perm_perm v]
  exact h.permLattice TwistTag.E6.cartan_perm

@[expose] def twistedE6TwoVecB (u v : Fin TwistTag.E6.tag.rank → ℤ) : Bool :=
  List.ofFn u == List.ofFn v

theorem twistedE6TwoVecB_iff {u v : Fin TwistTag.E6.tag.rank → ℤ} :
    twistedE6TwoVecB u v = true ↔ u = v := by
  rw [twistedE6TwoVecB, beq_iff_eq, List.ofFn_inj]

@[expose] def twistedE6TwoRootB (v : Fin TwistTag.E6.tag.rank → ℤ) : Bool :=
  (List.range TwistTag.E6.tag.rootCertificate.roots.length).any fun k =>
    twistedE6TwoVecB (TwistTag.E6.tag.rootCertificate.root k) v

theorem isRoot_iff_twistedE6TwoRootB
    {v : Fin TwistTag.E6.tag.rank → ℤ} :
    IsRoot TwistTag.E6.tag v ↔ twistedE6TwoRootB v = true := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check TwistTag.E6.tag)]
  simp only [twistedE6TwoRootB, List.any_eq_true, List.mem_range, twistedE6TwoVecB_iff]

@[expose] def twistedE6TwoExp (i : Fin TwistTag.E6.tag.rank) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    ℤ :=
  coPair TwistTag.E6.tag i v + 2 * coPair TwistTag.E6.tag (TwistTag.E6.perm i) v

@[expose] def twistedE6TwoTorusCheck : Bool :=
  (List.range TwistTag.E6.tag.rootCertificate.roots.length).all fun k =>
    twistedE6TwoVecB (permLattice TwistTag.E6.perm (TwistTag.E6.tag.rootCertificate.root k))
        (TwistTag.E6.tag.rootCertificate.root k) ||
      ([⟨0, by decide⟩, ⟨2, by decide⟩] : List (Fin TwistTag.E6.tag.rank)).any fun i =>
        decide (twistedE6TwoExp i (TwistTag.E6.tag.rootCertificate.root k) % 3 ≠ 0) &&
          decide (twistedE6TwoExp i
            (permLattice TwistTag.E6.perm (TwistTag.E6.tag.rootCertificate.root k)) % 3 ≠ 0)

theorem twistedE6TwoTorusCheck_eq_true : twistedE6TwoTorusCheck = true := by decide +kernel

theorem exists_twistedE6TwoTorusIndex
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (hργ : permLattice TwistTag.E6.perm γ ≠ γ) :
    ∃ i ∈ ([⟨0, by decide⟩, ⟨2, by decide⟩] : List (Fin TwistTag.E6.tag.rank)),
      twistedE6TwoExp i γ % 3 ≠ 0 ∧ twistedE6TwoExp i (permLattice TwistTag.E6.perm γ) % 3 ≠ 0 := by
  have h := twistedE6TwoTorusCheck_eq_true
  obtain ⟨k, hk, rfl⟩ :=
    RootCertificate.exists_root_eq (Tag.rootCertificate_check TwistTag.E6.tag) hγ
  simp only [twistedE6TwoTorusCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, twistedE6TwoVecB_iff] at h
  rcases h k hk with h1 | ⟨i, hi, h2⟩
  · exact absurd h1 hργ
  · exact ⟨i, hi, h2⟩

theorem coPair_e6HighestRoot_of_mem {i : Fin TwistTag.E6.tag.rank}
    (hi : i ∈ ([⟨0, by decide⟩, ⟨2, by decide⟩] : List (Fin TwistTag.E6.tag.rank))) :
    coPair TwistTag.E6.tag i e6HighestRoot = 0 ∧
      coPair TwistTag.E6.tag (TwistTag.E6.perm i) e6HighestRoot = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> decide

@[expose] def twistedE6TwoDecompOK (δ ε : Fin TwistTag.E6.tag.rank → ℤ) : Bool :=
  twistedE6TwoRootB δ && twistedE6TwoRootB ε && twistedE6TwoRootB (δ + ε) &&
    twistedE6TwoVecB (permLattice TwistTag.E6.perm (δ + ε)) (δ + ε) &&
    !twistedE6TwoVecB (permLattice TwistTag.E6.perm δ) δ &&
    !twistedE6TwoVecB (permLattice TwistTag.E6.perm ε) ε &&
    !twistedE6TwoRootB (δ + e6HighestRoot) && !twistedE6TwoRootB (ε + e6HighestRoot) &&
    !twistedE6TwoVecB δ ε &&
    !twistedE6TwoRootB (δ + permLattice TwistTag.E6.perm ε) &&
    !twistedE6TwoVecB (δ + permLattice TwistTag.E6.perm ε) 0 &&
    !twistedE6TwoVecB δ (permLattice TwistTag.E6.perm ε) &&
    !twistedE6TwoRootB (δ + ε + δ) && !twistedE6TwoRootB (δ + ε + ε) &&
    !twistedE6TwoVecB (δ + ε) (-δ) && !twistedE6TwoVecB (δ + ε) (-ε)

@[expose] def twistedE6TwoDecomp :
    List ((Fin TwistTag.E6.tag.rank → ℤ) × (Fin TwistTag.E6.tag.rank → ℤ)) :=
  [(![0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, -1, 0]),
    (![0, 1, 0, 1, 1, 0], ![0, 0, 0, -1, -1, 0]),
    (![0, 1, 0, 1, 1, 0], ![0, 0, 0, 0, -1, 0]),
    (![0, 0, 0, 0, 1, 0], ![0, 0, 1, 1, 0, 0]),
    (![0, 0, 0, 0, 1, 0], ![0, 1, 1, 1, 0, 0]),
    (![0, 0, 0, 1, 1, 0], ![0, 1, 1, 1, 0, 0]),
    (![0, 0, 0, 0, 0, 1], ![1, 0, 1, 1, 1, 0]),
    (![0, 0, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 0]),
    (![0, 0, 0, 0, 0, 1], ![1, 1, 1, 2, 1, 0]),
    (![0, 0, 0, 0, 1, 0], ![1, 1, 2, 2, 1, 1]),
    (![0, 0, 0, 1, 1, 0], ![1, 1, 2, 2, 1, 1]),
    (![0, 1, 0, 1, 1, 0], ![1, 1, 2, 2, 1, 1])]

@[expose] def twistedE6TwoDecompCheck : Bool :=
  (twistedE6TwoDecomp.all fun p => twistedE6TwoDecompOK p.1 p.2) &&
    (List.range TwistTag.E6.tag.rootCertificate.roots.length).all fun k =>
      decide (height (TwistTag.E6.tag.rootCertificate.root k) ≤ 0) ||
        !twistedE6TwoVecB (permLattice TwistTag.E6.perm (TwistTag.E6.tag.rootCertificate.root k))
          (TwistTag.E6.tag.rootCertificate.root k) ||
        twistedE6TwoDecomp.any fun p => twistedE6TwoVecB (p.1 + p.2)
          (TwistTag.E6.tag.rootCertificate.root k)

theorem twistedE6TwoDecompCheck_eq_true : twistedE6TwoDecompCheck = true := by decide +kernel

theorem exists_twistedE6TwoDecomp
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) (hpos : 0 < height γ)
    (hργ : permLattice TwistTag.E6.perm γ = γ) :
    ∃ δ ε : Fin TwistTag.E6.tag.rank → ℤ, δ + ε = γ ∧
      (IsRoot TwistTag.E6.tag δ ∧ permLattice TwistTag.E6.perm δ ≠ δ ∧
        ¬IsRoot TwistTag.E6.tag (δ + e6HighestRoot)) ∧
      (IsRoot TwistTag.E6.tag ε ∧ permLattice TwistTag.E6.perm ε ≠ ε ∧
        ¬IsRoot TwistTag.E6.tag (ε + e6HighestRoot)) ∧
      δ ≠ ε ∧ ¬IsRoot TwistTag.E6.tag (δ + permLattice TwistTag.E6.perm ε) ∧
      δ + permLattice TwistTag.E6.perm ε ≠ 0 ∧ δ ≠ permLattice TwistTag.E6.perm ε ∧
      ¬IsRoot TwistTag.E6.tag (δ + ε + δ) ∧ ¬IsRoot TwistTag.E6.tag (δ + ε + ε) ∧
      δ + ε ≠ -δ ∧ δ + ε ≠ -ε := by
  have h := twistedE6TwoDecompCheck_eq_true
  obtain ⟨k, hk, rfl⟩ :=
    RootCertificate.exists_root_eq (Tag.rootCertificate_check TwistTag.E6.tag) hγ
  simp only [twistedE6TwoDecompCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.any_eq_true] at h
  obtain ⟨hOK, hcov⟩ := h
  rcases hcov k hk with (h1 | h1) | ⟨p, hp, hpk⟩
  · exact absurd h1 (not_le.2 hpos)
  · rw [Bool.eq_false_iff, ne_eq, twistedE6TwoVecB_iff] at h1
    exact absurd hργ h1
  · rw [twistedE6TwoVecB_iff] at hpk
    have hp' := hOK p hp
    simp only [twistedE6TwoDecompOK, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
      ne_eq, twistedE6TwoVecB_iff, ← isRoot_iff_twistedE6TwoRootB, and_assoc] at hp'
    obtain ⟨h1, h2, -, -, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hp'
    exact ⟨p.1, p.2, hpk, ⟨h1, h5, h7⟩, ⟨h2, h6, h8⟩, h9, h10, h11, h12, h13, h14, h15, h16⟩

end CFSG.SeitzReduction
