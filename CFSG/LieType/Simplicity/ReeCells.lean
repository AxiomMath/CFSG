module

public import CFSG.LieType.Simplicity.ParabolicCells
public import CFSG.LieType.Ree.ReeHolds
public import CFSG.LieType.Ree.TitsWeyl

public section

namespace CFSG.LieType.Simplicity

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree ReeTag

section Cells

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem exists_reeFixed_nrep_mul_mul_nrep_eq
    {v v' : WeylGroup t.tag} (hv : v ∈ t.relWeylRee)
    (hv' : v' ∈ t.relWeylRee)
    (hlen : (coxeterSystem t.tag).length (v * v') =
      (coxeterSystem t.tag).length v + (coxeterSystem t.tag).length v')
    {b : adjointGroup t.tag K} (hb : b ∈ (nativeData t.tag K).B) (hbF : b ∈ reeFixed t K a) :
    ∃ b₁ ∈ (nativeData t.tag K).B, b₁ ∈ reeFixed t K a ∧ ∃ b₂ ∈ (nativeData t.tag K).B,
      b₂ ∈ reeFixed t K a ∧
        nrep t.tag K v * b * nrep t.tag K v' = b₁ * nrep t.tag K (v * v') * b₂ := by
  have hg : nrep t.tag K v * b * nrep t.tag K v' ∈ reeFixed t K a :=
    mul_mem (mul_mem (nrep_mem_reeFixed t K a hv) hbF) (nrep_mem_reeFixed t K a hv')
  obtain ⟨b₁, hb₁, b₂, hb₂, h⟩ := exists_nrep_mul_mul_nrep_eq hlen hb
  obtain ⟨w, -, c₁, hc₁, hc₁F, c₂, hc₂, hc₂F, h'⟩ := reeFixed_bruhat t K a _ hg
  have hw : w = v * v' := by
    have := nativeData_weylHom_eq_of_mul_eq ⟨nrep t.tag K w, nrep_mem_monomialGroup _ _ w⟩
      ⟨nrep t.tag K (v * v'), nrep_mem_monomialGroup _ _ _⟩ hc₁ hc₂ hb₁ hb₂ (h'.symm.trans h)
    rwa [weylHom_nrep, weylHom_nrep] at this
  subst hw
  exact ⟨c₁, hc₁, hc₁F, c₂, hc₂, hc₂F, h'⟩

end Cells

@[expose] def orbitParabolicWords : (t : ReeTag) → Fin t.tag.rank → List (List (Fin t.tag.rank))
  | .G2 => (fun _ => [[], [0], [1], [0, 1], [1, 0], [0, 1, 0], [1, 0, 1], [0, 1, 0, 1],
      [1, 0, 1, 0], [0, 1, 0, 1, 0], [1, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1]] :
        Fin 2 → List (List (Fin 2)))
  | .F4 => (![[[], [0], [3], [0, 3]],
      [[], [1], [2], [1, 2], [2, 1], [1, 2, 1], [2, 1, 2], [1, 2, 1, 2]],
      [[], [1], [2], [1, 2], [2, 1], [1, 2, 1], [2, 1, 2], [1, 2, 1, 2]],
      [[], [0], [3], [0, 3]]] : Fin 4 → List (List (Fin 4)))

theorem nil_mem_orbitParabolicWords (t : ReeTag) (i : Fin t.tag.rank) :
    [] ∈ orbitParabolicWords t i := by
  revert i
  cases t <;> decide

theorem orbitParabolicWords_closed (t : ReeTag) :
    ∀ i : Fin t.tag.rank, ∀ j ∈ [i, t.perm i], ∀ ω ∈ orbitParabolicWords t i,
      ∃ ω' ∈ orbitParabolicWords t i, ∀ k : Fin t.tag.rank,
        (j :: ω).foldr (reflect t.tag) (Pi.single k 1) =
          ω'.foldr (reflect t.tag) (Pi.single k 1) := by
  cases t <;> decide +kernel

theorem orbitParabolicWords_fixed (t : ReeTag) :
    ∀ i : Fin t.tag.rank, ∀ ω ∈ orbitParabolicWords t i,
      (∀ k : Fin t.tag.rank, (ω.map t.perm).foldr (reflect t.tag) (Pi.single k 1) =
        ω.foldr (reflect t.tag) (Pi.single k 1)) →
      (∀ k : Fin t.tag.rank, ω.foldr (reflect t.tag) (Pi.single k 1) = Pi.single k 1) ∨
        ∀ k : Fin t.tag.rank, ω.foldr (reflect t.tag) (Pi.single k 1) =
          (t.reeOrbitWord i).foldr (reflect t.tag) (Pi.single k 1) := by
  cases t <;> decide +kernel

theorem isReduced_reeOrbitWord
    (t : ReeTag) (i : Fin t.tag.rank) :
    (coxeterSystem t.tag).IsReduced (t.reeOrbitWord i) :=
  isReduced_of_reducedCheck (by revert i; cases t <;> decide +kernel)

theorem mem_of_mem_reeOrbitWord (t : ReeTag) :
    ∀ i : Fin t.tag.rank, ∀ j ∈ t.reeOrbitWord i, j = i ∨ j = t.perm i := by
  cases t <;> decide

theorem blockElt_ne_one
    (t : ReeTag) (i : Fin t.tag.rank) : t.blockElt i ≠ 1 := by
  intro h
  have h1 := (isReduced_reeOrbitWord t i).eq
  have h2 := t.reeOrbitWord_ne_nil i
  change (coxeterSystem t.tag).length (t.blockElt i) = _ at h1
  rw [h, (coxeterSystem t.tag).length_one] at h1
  omega

theorem exists_mem_orbitParabolicWords
    {t : ReeTag} {i : Fin t.tag.rank} {w : WeylGroup t.tag}
    (hw : w ∈ Subgroup.closure (simple t.tag '' {i, t.perm i})) :
    ∃ ω ∈ orbitParabolicWords t i, w = (coxeterSystem t.tag).wordProd ω := by
  have key : ∀ j ∈ ({i, t.perm i} : Set (Fin t.tag.rank)), ∀ ω ∈ orbitParabolicWords t i,
      ∃ ω' ∈ orbitParabolicWords t i,
        simple t.tag j * (coxeterSystem t.tag).wordProd ω = (coxeterSystem t.tag).wordProd ω' := by
    intro j hj ω hω
    have hj' : j ∈ [i, t.perm i] := by
      rcases hj with rfl | hj
      · exact List.mem_cons_self
      · rw [Set.mem_singleton_iff.1 hj]
        exact List.mem_cons_of_mem _ List.mem_cons_self
    obtain ⟨ω', hω', h⟩ := orbitParabolicWords_closed t i j hj' ω hω
    refine ⟨ω', hω', ext_single fun k => ?_⟩
    rw [← CoxeterSystem.wordProd_cons, CFSG.LieType.Ree.wordProd_smul,
      CFSG.LieType.Ree.wordProd_smul]
    exact h k
  induction hw using Subgroup.closure_induction_left with
  | one => exact ⟨[], nil_mem_orbitParabolicWords t i, rfl⟩
  | mul_left x hx y _ ih =>
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨ω, hω, rfl⟩ := ih
    obtain ⟨ω', hω', h⟩ := key j hj ω hω
    exact ⟨ω', hω', h⟩
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨ω, hω, rfl⟩ := ih
    obtain ⟨ω', hω', h⟩ := key j hj ω hω
    exact ⟨ω', hω', by rw [(coxeterSystem t.tag).inv_simple]; exact h⟩

theorem eq_one_or_eq_blockElt
    {t : ReeTag} {i : Fin t.tag.rank} {w : WeylGroup t.tag}
    (hw : w ∈ Subgroup.closure (simple t.tag '' {i, t.perm i})) (hδ : t.weylPerm w = w) :
    w = 1 ∨ w = t.blockElt i := by
  obtain ⟨ω, hω, rfl⟩ := exists_mem_orbitParabolicWords hw
  have hfix : ∀ k : Fin t.tag.rank, (ω.map t.perm).foldr (reflect t.tag) (Pi.single k 1) =
      ω.foldr (reflect t.tag) (Pi.single k 1) := fun k => by
    rw [← CFSG.LieType.Ree.wordProd_smul, ← CFSG.LieType.Ree.wordProd_smul, ← weylPerm_wordProd,
      hδ]
  rcases orbitParabolicWords_fixed t i ω hω hfix with h | h
  · refine .inl (ext_single fun k => ?_)
    rw [CFSG.LieType.Ree.wordProd_smul, one_smul]
    exact h k
  · refine .inr (ext_single fun k => ?_)
    rw [CFSG.LieType.Ree.wordProd_smul, CFSG.LieType.Ree.wordProd_smul]
    exact h k

section RankOne

variable (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

omit [CharP K t.prime] in
theorem nrep_blockElt_mem_closure
    (i : Fin t.tag.rank) :
    nrep t.tag K (t.blockElt i) ∈ Subgroup.closure (((nativeData t.tag K).B :
      Set (adjointGroup t.tag K)) ∪ weylElement t.tag K '' {i, t.perm i}) := by
  rw [blockElt, nrep_eq_prod t.tag K (isReduced_reeOrbitWord t i)]
  refine list_prod_mem fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  refine Subgroup.subset_closure (.inr ⟨j, ?_, rfl⟩)
  rcases mem_of_mem_reeOrbitWord t i j hj with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

theorem exists_nrep_blockElt_eq
    (i : Fin t.tag.rank) :
    ∃ u ∈ (nativeData t.tag K).U, u ∈ reeFixed t K a ∧
      ∃ b₁ ∈ (nativeData t.tag K).B, b₁ ∈ reeFixed t K a ∧ ∃ b₂ ∈ (nativeData t.tag K).B,
        b₂ ∈ reeFixed t K a ∧ nrep t.tag K (t.blockElt i) =
          b₁ * (nrep t.tag K (t.blockElt i) * u * (nrep t.tag K (t.blockElt i))⁻¹) * b₂ := by
  have hri : t.blockElt i ∈ t.relWeylRee := reeOrbitWord_mem t i
  obtain ⟨u, hu, huF, hnu⟩ := reeFixed_hUw t K a _ hri (blockElt_ne_one t i)
  refine ⟨u, hu, huF, ?_⟩
  set n := nrep t.tag K (t.blockElt i) with hn
  have hnF : n ∈ reeFixed t K a := nrep_mem_reeFixed t K a hri
  have hxF : n * u * n⁻¹ ∈ reeFixed t K a := mul_mem (mul_mem hnF huF) (inv_mem hnF)
  have hnJ := nrep_blockElt_mem_closure t K i
  rw [← hn] at hnJ
  have hxJ : n * u * n⁻¹ ∈ Subgroup.closure (((nativeData t.tag K).B :
      Set (adjointGroup t.tag K)) ∪ weylElement t.tag K '' {i, t.perm i}) :=
    mul_mem (mul_mem hnJ (Subgroup.subset_closure (.inl ((nativeData t.tag K).U_le_B hu))))
      (inv_mem hnJ)
  obtain ⟨m, hmJ, b₁, hb₁, b₂, hb₂, hx₁⟩ := exists_mem_doubleCoset_of_mem_closure _ hxJ
  obtain ⟨w, hw, c₁, hc₁, hc₁F, c₂, hc₂, hc₂F, hx₂⟩ := reeFixed_bruhat t K a _ hxF
  have hmw : weylHom t.tag K m = w := by
    have := nativeData_weylHom_eq_of_mul_eq m ⟨nrep t.tag K w, nrep_mem_monomialGroup _ _ w⟩
      hb₁ hb₂ hc₁ hc₂ (hx₁.symm.trans hx₂)
    rwa [weylHom_nrep] at this
  rw [hmw] at hmJ
  rcases eq_one_or_eq_blockElt hmJ ((mem_relWeylRee t).1 hw) with rfl | rfl
  ·
    exfalso
    obtain ⟨k, hk⟩ := (nativeRootSubgroups t.tag K).isPGroup_U t.prime ⟨u, hu⟩
    have hk' : u ^ t.prime ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine hnu ((nativeRootSubgroups t.tag K).mem_U_of_pow_eq_one t.prime (k := k) ?_ ?_)
    · rw [hx₂, nrep_one, mul_one]
      exact mul_mem hc₁ hc₂
    · rw [conj_pow, hk', mul_one, mul_inv_cancel]
  · refine ⟨c₁⁻¹, inv_mem hc₁, inv_mem hc₁F, c₂⁻¹, inv_mem hc₂, inv_mem hc₂F, ?_⟩
    rw [hx₂, ← hn]
    group

variable {t K a}

theorem mem_closure_of_mem_reeFixed
    {g : adjointGroup t.tag K} (hg : g ∈ reeFixed t K a) :
    g ∈ Subgroup.closure ({b | b ∈ (nativeData t.tag K).B ∧ b ∈ reeFixed t K a} ∪
      Set.range fun i => nrep t.tag K (t.blockElt i)) := by
  set Q := Subgroup.closure ({b | b ∈ (nativeData t.tag K).B ∧ b ∈ reeFixed t K a} ∪
    Set.range fun i => nrep t.tag K (t.blockElt i))
  have hB₀ : ∀ b ∈ (nativeData t.tag K).B, b ∈ reeFixed t K a → b ∈ Q :=
    fun b hb hbF => Subgroup.subset_closure (.inl ⟨hb, hbF⟩)
  have hH : ∀ w₁ w₂ : WeylGroup t.tag, w₁ ∈ t.relWeylRee → w₂ ∈ t.relWeylRee →
      (nrep t.tag K w₁ * nrep t.tag K w₂)⁻¹ * nrep t.tag K (w₁ * w₂) ∈ Q := by
    intro w₁ w₂ h₁ h₂
    have hN : (nrep t.tag K w₁ * nrep t.tag K w₂)⁻¹ * nrep t.tag K (w₁ * w₂) ∈
        monomialGroup t.tag K :=
      mul_mem (inv_mem (mul_mem (nrep_mem_monomialGroup _ _ _) (nrep_mem_monomialGroup _ _ _)))
        (nrep_mem_monomialGroup _ _ _)
    have hk : weylHom t.tag K ⟨_, hN⟩ = 1 := by
      have e : (⟨_, hN⟩ : monomialGroup t.tag K) =
          (⟨nrep t.tag K w₁, nrep_mem_monomialGroup _ _ _⟩ *
            ⟨nrep t.tag K w₂, nrep_mem_monomialGroup _ _ _⟩)⁻¹ *
              ⟨nrep t.tag K (w₁ * w₂), nrep_mem_monomialGroup _ _ _⟩ :=
        Subtype.ext (by simp)
      rw [e, map_mul, map_inv, map_mul, weylHom_nrep, weylHom_nrep, weylHom_nrep, inv_mul_cancel]
    exact hB₀ _ ((nativeData t.tag K).H_le_B
      ((RootGroupData.mem_H_iff (D := nativeData t.tag K)).2 ⟨⟨_, hN⟩, hk, rfl⟩))
      (mul_mem (inv_mem (mul_mem (nrep_mem_reeFixed t K a h₁) (nrep_mem_reeFixed t K a h₂)))
        (nrep_mem_reeFixed t K a (mul_mem h₁ h₂)))
  have hle : Subgroup.closure (Set.range t.blockElt) ≤ t.relWeylRee :=
    (Subgroup.closure_le _).2 (Set.range_subset_iff.2 fun i => reeOrbitWord_mem t i)
  have hn : ∀ w ∈ Subgroup.closure (Set.range t.blockElt), nrep t.tag K w ∈ Q := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Subgroup.subset_closure (.inr ⟨i, rfl⟩)
    | one =>
      rw [nrep_one]
      exact one_mem _
    | mul x y hx hy ihx ihy =>
      have e : nrep t.tag K (x * y) = nrep t.tag K x * nrep t.tag K y *
          ((nrep t.tag K x * nrep t.tag K y)⁻¹ * nrep t.tag K (x * y)) := by group
      rw [e]
      exact mul_mem (mul_mem ihx ihy) (hH x y (hle hx) (hle hy))
    | inv x hx ihx =>
      have h := hH x x⁻¹ (hle hx) (inv_mem (hle hx))
      rw [mul_inv_cancel, nrep_one, mul_one] at h
      have e : nrep t.tag K x⁻¹ =
          (nrep t.tag K x)⁻¹ * (nrep t.tag K x * nrep t.tag K x⁻¹)⁻¹⁻¹ := by group
      rw [e]
      exact mul_mem (inv_mem ihx) (inv_mem h)
  obtain ⟨w, hw, b₁, hb₁, hb₁F, b₂, hb₂, hb₂F, rfl⟩ := reeFixed_bruhat t K a g hg
  exact mul_mem (mul_mem (hB₀ b₁ hb₁ hb₁F)
    (hn w (mem_closure_blockElt _ w rfl ((mem_relWeylRee t).1 hw)))) (hB₀ b₂ hb₂ hb₂F)

end RankOne

end CFSG.LieType.Simplicity
