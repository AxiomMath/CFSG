module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompKac
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacD

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint TwE6UniqAbs CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups Matrix

namespace TwE6InnerAbs

set_option maxRecDepth 100000

@[expose] def lA5a : Fin 5 → Option (Fin Tag.E6.rank) :=
  (![some 0, some 2, some 3, some 4, some 5] : Fin 5 → Option (Fin 6))

@[expose] def lA5b : Fin 5 → Option (Fin Tag.E6.rank) :=
  (![none, some 1, some 3, some 4, some 5] : Fin 5 → Option (Fin 6))

@[expose] def lA5c : Fin 5 → Option (Fin Tag.E6.rank) :=
  (![some 0, some 2, some 3, some 1, none] : Fin 5 → Option (Fin 6))

@[expose] def lD4 : Fin 4 → Option (Fin Tag.E6.rank) :=
  (![some 1, some 3, some 2, some 4] : Fin 4 → Option (Fin 6))

theorem lA5a_chk : Function.Injective lA5a ∧
    (∀ c d : Fin 5, iform (e6ExtVec (lA5a c)) (e6ExtVec (lA5a d)) = chainGram c d) ∧
    ∀ (c : Fin 5) (h : c.val + 1 < 5),
      (nodeIdx (lA5a c), nodeIdx (lA5a ⟨c.val + 1, h⟩)) ∈ e6EdgeIdx := by
  decide +kernel

theorem lA5b_chk : Function.Injective lA5b ∧
    (∀ c d : Fin 5, iform (e6ExtVec (lA5b c)) (e6ExtVec (lA5b d)) = chainGram c d) ∧
    ∀ (c : Fin 5) (h : c.val + 1 < 5),
      (nodeIdx (lA5b c), nodeIdx (lA5b ⟨c.val + 1, h⟩)) ∈ e6EdgeIdx := by
  decide +kernel

theorem lA5c_chk : Function.Injective lA5c ∧
    (∀ c d : Fin 5, iform (e6ExtVec (lA5c c)) (e6ExtVec (lA5c d)) = chainGram c d) ∧
    ∀ (c : Fin 5) (h : c.val + 1 < 5),
      (nodeIdx (lA5c c), nodeIdx (lA5c ⟨c.val + 1, h⟩)) ∈ e6EdgeIdx := by
  decide +kernel

theorem d4_hgram : ∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i →
    iform (e6ExtVec (lD4 i)) (e6ExtVec (lD4 j)) = 0 := by
  decide +kernel

theorem d4_hE : ∀ i j : Fin 4, edgeD 4 i j → (nodeIdx (lD4 i), nodeIdx (lD4 j)) ∈ e6EdgeIdx := by
  decide +kernel

theorem range_lA5a_iff : ∀ y : Option (Fin Tag.E6.rank), (∃ i, lA5a i = y) ↔ y ∈ sA5a := by
  decide +kernel

theorem range_lA5b_iff : ∀ y : Option (Fin Tag.E6.rank), (∃ i, lA5b i = y) ↔ y ∈ sA5b := by
  decide +kernel

theorem range_lA5c_iff : ∀ y : Option (Fin Tag.E6.rank), (∃ i, lA5c i = y) ↔ y ∈ sA5c := by
  decide +kernel

theorem range_lD4_iff : ∀ y : Option (Fin Tag.E6.rank), (∃ i, lD4 i = y) ↔ y ∈ sD4 := by
  decide +kernel

theorem range_lA5a : (Set.range lA5a : Set (Option (Fin Tag.E6.rank))) =
    (↑sA5a : Set (Option (Fin Tag.E6.rank))) :=
  Set.ext fun y => range_lA5a_iff y

theorem range_lA5b : (Set.range lA5b : Set (Option (Fin Tag.E6.rank))) =
    (↑sA5b : Set (Option (Fin Tag.E6.rank))) :=
  Set.ext fun y => range_lA5b_iff y

theorem range_lA5c : (Set.range lA5c : Set (Option (Fin Tag.E6.rank))) =
    (↑sA5c : Set (Option (Fin Tag.E6.rank))) :=
  Set.ext fun y => range_lA5c_iff y

theorem range_lD4 : (Set.range lD4 : Set (Option (Fin Tag.E6.rank))) =
    (↑sD4 : Set (Option (Fin Tag.E6.rank))) :=
  Set.ext fun y => range_lD4_iff y

section Fam



theorem image_rootsOf_eq_rootsOfFam {τ : Tag} (K : KacData τ) (v : WeylGroup τ)
    (s : Set (Option (Fin τ.rank))) :
    (fun α => v • α) '' K.rootsOf s = rootsOfFam (fun x => v • K.extRoot x) s := by
  have hsmulcombo : ∀ n' : Option (Fin τ.rank) → ℕ,
      v • K.combo n' = ∑ x, (n' x : ℤ) • (v • K.extRoot x) := by
    intro n'
    unfold KacData.combo
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => smul_comm v ((n' x : ℕ) : ℤ) (K.extRoot x)
  ext γ
  constructor
  · rintro ⟨γ₀, ⟨hr0, n', hn', hγ⟩, rfl⟩
    refine ⟨IsRoot.smul hr0 v, n', hn', ?_⟩
    rcases hγ with rfl | rfl
    · exact Or.inl (hsmulcombo n')
    · exact Or.inr (by show v • (-K.combo n') = _; rw [smul_neg, hsmulcombo])
  · rintro ⟨hr, n', hn', hγ⟩
    refine ⟨v⁻¹ • γ, ⟨IsRoot.smul hr v⁻¹, n', hn', ?_⟩, smul_inv_smul v γ⟩
    rcases hγ with rfl | rfl
    · left
      rw [← hsmulcombo, inv_smul_smul]
    · right
      rw [smul_neg, ← hsmulcombo, inv_smul_smul]

end Fam

section Frames


theorem frame_of_path6 {L : Type} [Field L] {m : ℕ} {l : Fin m → Option (Fin Tag.E6.rank)}
    (hl : Function.Injective l)
    (hG : ∀ c d, iform (e6ExtVec (l c)) (e6ExtVec (l d)) = chainGram c d)
    (hE : ∀ (c : Fin m) (h : (c : ℕ) + 1 < m),
      (nodeIdx (l c), nodeIdx (l ⟨c + 1, h⟩)) ∈ e6EdgeIdx) (v : WeylGroup Tag.E6) :
    ∃ (ψ : SL(m + 1, L) →* ModGL Tag.E6 L)
      (σ : Fin (m + 1) → Fin (m + 1) → Fin Tag.E6.rank → ℤ),
      IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2) ∧
        frameRoots σ = (fun α => v • α) '' kacE6.rootsOf (Set.range l) := by
  obtain ⟨ψ, σ, hψ, hσ⟩ := exists_frame_of_path (L := L) (Or.inr (Or.inl rfl)) kacE6 hl
    (fun c d => by
      rw [kacE6_extRoot]
      exact hG c d)
    (fun c h => e6_frames _ _ (hE c h)) v
  exact ⟨ψ, σ, hψ, fun a b hab =>
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl))
      (hψ.isRoot a b hab), hσ⟩

theorem frame_of_A5 {L : Type} [Field L] {C : Finset (Option (Fin Tag.E6.rank))}
    (hC : C = sA5a ∨ C = sA5b ∨ C = sA5c) (v : WeylGroup Tag.E6) :
    ∃ (ψ : SL(5 + 1, L) →* ModGL Tag.E6 L)
      (σ : Fin (5 + 1) → Fin (5 + 1) → Fin Tag.E6.rank → ℤ),
      IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2) ∧
        frameRoots σ = (fun α => v • α) '' kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank))) := by
  rcases hC with h | h | h
  · obtain ⟨ψ, σ, hψ, hn, hr⟩ := frame_of_path6 (L := L) lA5a_chk.1 lA5a_chk.2.1 lA5a_chk.2.2 v
    exact ⟨ψ, σ, hψ, hn, by rw [h, ← range_lA5a]; exact hr⟩
  · obtain ⟨ψ, σ, hψ, hn, hr⟩ := frame_of_path6 (L := L) lA5b_chk.1 lA5b_chk.2.1 lA5b_chk.2.2 v
    exact ⟨ψ, σ, hψ, hn, by rw [h, ← range_lA5b]; exact hr⟩
  · obtain ⟨ψ, σ, hψ, hn, hr⟩ := frame_of_path6 (L := L) lA5c_chk.1 lA5c_chk.2.1 lA5c_chk.2.2 v
    exact ⟨ψ, σ, hψ, hn, by rw [h, ← range_lA5c]; exact hr⟩

end Frames


section D4


theorem d4_frames {F : Type} [Field F] (v : WeylGroup Tag.E6) :
    ∀ c d : Fin 4, edgeD 4 c d → ∃ θ : SL(3, F) →* ModGL Tag.E6 F,
      θ.comp (blockSL F 3 2 0 (by omega)) =
          rootSL2 Tag.E6 F ((fun x => v • kacE6.extRoot x) (lD4 c)) ∧
        θ.comp (blockSL F 3 2 1 (by omega)) =
          rootSL2 Tag.E6 F ((fun x => v • kacE6.extRoot x) (lD4 d)) :=
  treeFrames kacE6 (fun {F} _ x y h => e6_frames x y h) v lD4 (edgeD 4) d4_hE

end D4


@[expose] def d4Eps : Fin 4 → Fin Tag.E6.rank → ℤ :=
  (![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 1, 2, 1, 0]] :
    Fin 4 → Fin 6 → ℤ)

@[expose] def reflV (ε x : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  x - (2 * iform ε x / iform ε ε) • ε

theorem d4Eps_mem : ∀ j, d4Eps j ∈ R6 ∧ kacTest θ6 sD4 (d4Eps j) := by
  decide +kernel

theorem d4_neg_check : ∀ γ ∈ R6, kacTest θ6 sD4 γ →
    reflV (d4Eps 0) (reflV (d4Eps 1) (reflV (d4Eps 2) (reflV (d4Eps 3) γ))) = -γ := by
  decide +kernel

section Twist


theorem twistInner_neg_D4 (v : WeylGroup Tag.E6)
    {σ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hσ : ∀ γ, σ γ = -γ) :
    twistInner ((fun α => v • α) '' kacE6.rootsOf (↑sD4 : Set (Option (Fin Tag.E6.rank)))) σ := by
  classical
  have hC : ∃ x, x ∉ sD4 := ⟨none, by decide⟩
  have hroot : ∀ j, IsRoot Tag.E6 (d4Eps j) := fun j => isRoot_of_mem_R6 (d4Eps_mem j).1
  have hmem : ∀ j, d4Eps j ∈ kacE6.rootsOf (↑sD4 : Set (Option (Fin Tag.E6.rank))) := fun j =>
    (mem_rootsOf_iff kacE6 facts_E6 hC).2 ⟨hroot j, (d4Eps_mem j).2⟩
  set u₀ : WeylGroup Tag.E6 := rootReflection (d4Eps 0) * rootReflection (d4Eps 1) *
    rootReflection (d4Eps 2) * rootReflection (d4Eps 3) with hu₀
  have hu₀neg : ∀ γ ∈ kacE6.rootsOf (↑sD4 : Set (Option (Fin Tag.E6.rank))), u₀ • γ = -γ := by
    intro γ hγ
    obtain ⟨hr, hk⟩ := (mem_rootsOf_iff kacE6 facts_E6 hC).1 hγ
    have h := d4_neg_check γ (mem_R6_of_isRoot hr) hk
    rw [hu₀, mul_smul, mul_smul, mul_smul, rootReflection_smul (hroot 3),
      rootReflection_smul (hroot 2), rootReflection_smul (hroot 1), rootReflection_smul (hroot 0)]
    exact h
  refine ⟨v * u₀ * v⁻¹, ?_, ?_⟩
  · have hr : ∀ j, v * rootReflection (d4Eps j) * v⁻¹ ∈ Subgroup.closure
        {s : WeylGroup Tag.E6 | ∃ γ ∈ (fun α => v • α) '' kacE6.rootsOf
          (↑sD4 : Set (Option (Fin Tag.E6.rank))), s = rootReflection γ} := fun j => by
      rw [← rootReflection_smul_root v (hroot j)]
      exact Subgroup.subset_closure ⟨v • d4Eps j, ⟨d4Eps j, hmem j, rfl⟩, rfl⟩
    have e : v * u₀ * v⁻¹ = (v * rootReflection (d4Eps 0) * v⁻¹) *
        (v * rootReflection (d4Eps 1) * v⁻¹) * (v * rootReflection (d4Eps 2) * v⁻¹) *
          (v * rootReflection (d4Eps 3) * v⁻¹) := by
      rw [hu₀]
      group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (hr 0) (hr 1)) (hr 2)) (hr 3)
  · intro γ hγ
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    show σ (v • γ₀) = (v * u₀ * v⁻¹) • (v • γ₀)
    rw [hσ, mul_smul, mul_smul, inv_smul_smul, hu₀neg γ₀ hγ₀, smul_neg]

end Twist

end TwE6InnerAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
