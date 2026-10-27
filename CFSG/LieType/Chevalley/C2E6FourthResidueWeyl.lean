module

public import CFSG.LieType.Chevalley.C2E6FourthResidueFlags

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FourthResidue

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def natPerm : Fin 4 → Equiv.Perm (Fin 4 ⊕ Fin 4) :=
  ![Equiv.sumCongr (Equiv.swap 0 1) (Equiv.swap 0 1),
    Equiv.sumCongr (Equiv.swap 1 2) (Equiv.swap 1 2),
    Equiv.sumCongr (Equiv.swap 2 3) (Equiv.swap 2 3),
    Equiv.swap (.inl 2) (.inr 3) * Equiv.swap (.inl 3) (.inr 2)]

theorem natPerm_inr : ∀ (k : Fin 4) (x : Fin 4),
    natPerm k (Sum.inr x) = (natPerm k (Sum.inl x)).swap := by
  decide

theorem weylPerm_eq_natPerm (k : Fin 4) :
    OrthogonalSplit.weylPerm (K := K) (by norm_num) k = natPerm k := by
  have hinl : ∀ x, OrthogonalSplit.weylPerm (K := K) (by norm_num) k (.inl x) =
      natPerm k (.inl x) := by
    fin_cases k
    · intro x
      rw [weylPerm_inl_of_lt _ (by decide)]
      revert x
      decide
    · intro x
      rw [weylPerm_inl_of_lt _ (by decide)]
      revert x
      decide
    · intro x
      rw [weylPerm_inl_of_lt _ (by decide)]
      revert x
      decide
    · intro x
      rw [weylPerm_inl_of_not_lt _ (by decide)]
      revert x
      decide
  refine Equiv.ext fun c => ?_
  rcases c with x | x
  · exact hinl x
  · rw [show (Sum.inr x : Fin 4 ⊕ Fin 4) = (Sum.inl x).swap from rfl, weylPerm_swap, hinl]
    exact (natPerm_inr k x).symm

theorem weylElt_single (k : Fin 4) (c : Fin 4 ⊕ Fin 4) :
    OrthogonalSplit.weylElt 4 K k (Pi.single c 1) = Pi.single (natPerm k c) 1 := by
  obtain ⟨a, b, -, -, h⟩ := exists_weylElt_autMat (K := K) (r := 4) (by norm_num) k
  have hσ : Equiv.swap a b * Equiv.swap a.swap b.swap = natPerm k := by
    rw [← monoPermFun_weylElt (by norm_num) k h]
    exact weylPerm_eq_natPerm k
  have hμ : ∀ s : Fin 4 ⊕ Fin 4,
      (((if s = a ∨ s = a.swap then (-1 : Kˣ) else 1 : Kˣ)) : K) = 1 := by
    intro s
    split_ifs
    · rw [Units.val_neg, Units.val_one, CharTwo.neg_eq]
    · rfl
  rw [apply_single_of_autMat h, hσ, hμ, one_smul]

theorem orbitWord_zero : TwistTag.E6.orbitWord (foldedIndex 0) =
    ([⟨1, by decide⟩] : List (Fin TwistTag.E6.tag.rank)) := by
  decide

theorem nativeRefl_zero_eq
    : nativeRefl 0 = (coxeterSystem Tag.E6).simple (jD 0) := by
  rw [nativeRefl_eq, TwistTag.orbitReflection, orbitWord_zero, CoxeterSystem.wordProd_singleton]
  rfl

theorem nativeRefl_one_eq
    : nativeRefl 1 = (coxeterSystem Tag.E6).simple (jD 1) :=
  (nativeRefl_eq 1).trans orbitReflection_one

theorem nativeRefl_two_eq
    : nativeRefl 2 =
    (coxeterSystem Tag.E6).simple (jD 2) * (coxeterSystem Tag.E6).simple (jD 3) :=
  (nativeRefl_eq 2).trans orbitReflection_two

theorem castSucc_mem_fourthJ (i : Fin 3) : i.castSucc ∈ fourthJ := by
  fin_cases i <;> simp [fourthJ]

abbrev natLevi
    (i : Fin 3) : stdLevi fourthJ :=
  ⟨nativeRep i.castSucc, nativeRep_mem_stdLevi (castSucc_mem_fourthJ i)⟩

@[expose] def psiNat : Fin 3 → ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
  ![OrthogonalSplit.weylElt 4 K 0, OrthogonalSplit.weylElt 4 K 1,
    OrthogonalSplit.weylElt 4 K 2 * OrthogonalSplit.weylElt 4 K 3]

theorem psiD_congr
    {x y : ModGL Tag.E6 K} (hx : x ∈ groupD) (hy : y ∈ groupD) (e : x = y) :
    psiD ⟨x, hx⟩ = psiD ⟨y, hy⟩ := by
  subst e
  rfl

theorem psiL_natLevi_zero
    : psiL (natLevi 0) = OrthogonalSplit.weylElt 4 K 0 := by
  have e : ((natLevi 0 : stdLevi fourthJ) : ModGL Tag.E6 K) =
      canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).simple (jD 0)) := by
    change canonicalRep _ K (nativeRefl 0) = _
    rw [nativeRefl_zero_eq]
  rw [psiL_apply]
  exact (psiD_congr _ _ e).trans (psiD_canonicalRep_simple 0)

theorem psiL_natLevi_one
    : psiL (natLevi 1) = OrthogonalSplit.weylElt 4 K 1 := by
  have e : ((natLevi 1 : stdLevi fourthJ) : ModGL Tag.E6 K) =
      canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).simple (jD 1)) := by
    change canonicalRep _ K (nativeRefl 1) = _
    rw [nativeRefl_one_eq]
  rw [psiL_apply]
  exact (psiD_congr _ _ e).trans (psiD_canonicalRep_simple 1)

theorem psiL_natLevi_two :
    psiL (natLevi 2) = OrthogonalSplit.weylElt 4 K 2 * OrthogonalSplit.weylElt 4 K 3 := by
  have e : ((natLevi 2 : stdLevi fourthJ) : ModGL Tag.E6 K) =
      ((⟨_, canonicalRep_simple_mem_groupD 2⟩ * ⟨_, canonicalRep_simple_mem_groupD 3⟩ : groupD) :
        ModGL Tag.E6 K) := by
    change canonicalRep _ K (nativeRefl 2) = _
    rw [nativeRefl_two_eq, canonicalRep_mul_charTwo]
    rfl
  rw [psiL_apply, psiD_congr _ (Subgroup.mul_mem _ (canonicalRep_simple_mem_groupD 2)
    (canonicalRep_simple_mem_groupD 3)) e]
  change psiD (⟨_, canonicalRep_simple_mem_groupD 2⟩ * ⟨_, canonicalRep_simple_mem_groupD 3⟩) = _
  rw [map_mul, psiD_canonicalRep_simple, psiD_canonicalRep_simple]

theorem psiL_natLevi
    (i : Fin 3) : psiL (natLevi i) = psiNat i := by
  fin_cases i
  exacts [psiL_natLevi_zero, psiL_natLevi_one, psiL_natLevi_two]

@[expose] def hypPerm : Fin 3 → Equiv.Perm (Fin 3 ⊕ Fin 3) :=
  ![Equiv.sumCongr (Equiv.swap 0 1) (Equiv.swap 0 1),
    Equiv.sumCongr (Equiv.swap 1 2) (Equiv.swap 1 2), Equiv.swap (.inl 2) (.inr 2)]

theorem natPerm_map_castSucc : ∀ (i : Fin 3) (c : Fin 3 ⊕ Fin 3),
    (![natPerm 0, natPerm 1, natPerm 2 * natPerm 3] : Fin 3 → Equiv.Perm (Fin 4 ⊕ Fin 4)) i
      (Sum.map Fin.castSucc Fin.castSucc c) = Sum.map Fin.castSucc Fin.castSucc (hypPerm i c) := by
  decide

theorem psiNat_single (i : Fin 3) (c : Fin 3 ⊕ Fin 3) :
    psiNat i (Pi.single (Sum.map Fin.castSucc Fin.castSucc c) 1) =
      Pi.single (Sum.map Fin.castSucc Fin.castSucc (hypPerm i c)) 1 := by
  rw [← natPerm_map_castSucc]
  fin_cases i
  · exact weylElt_single 0 _
  · exact weylElt_single 1 _
  · change OrthogonalSplit.weylElt 4 K 2 (OrthogonalSplit.weylElt 4 K 3 _) = _
    rw [weylElt_single, weylElt_single]
    rfl

theorem rhoMinus_natLevi_hypVec
    (i : Fin 3) (c : Fin 3 ⊕ Fin 3) :
    rhoMinus (natLevi i) (hypVec (ZMod 2) (Fin 2 → ZMod 2) c) =
      hypVec (ZMod 2) (Fin 2 → ZMod 2) (hypPerm i c) := by
  apply embed_injective
  rw [embed_rhoMinus, embed_hypVec, embed_hypVec, psiL_natLevi, psiNat_single]

theorem hypVec_mem_tailFlag_iff {k : ℕ} {c : Fin 3 ⊕ Fin 3} :
    hypVec (ZMod 2) (Fin 2 → ZMod 2) c ∈ tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k ↔
      ∃ j : Fin 3, (j : ℕ) < k ∧ c = .inl j := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := mem_flag.mp (mem_tailFlag_iff.mp h).1
    rcases c with j | j
    · refine ⟨j, ?_, rfl⟩
      by_contra hj
      have := h2 j (by omega)
      simp [hypVec] at this
    · have := h1 j
      simp [hypVec] at this
  · rintro ⟨j, hj, rfl⟩
    exact Submodule.subset_span ⟨j, hj, rfl⟩

theorem map_tailFlag_eq_of_hypVec {g : V0 ≃ₗ[ZMod 2] V0} {π : Equiv.Perm (Fin 3 ⊕ Fin 3)}
    (hg : ∀ c, g (hypVec (ZMod 2) (Fin 2 → ZMod 2) c) = hypVec (ZMod 2) (Fin 2 → ZMod 2) (π c))
    {k : ℕ} (hπ : ∀ j : Fin 3, (j : ℕ) < k → ∃ j' : Fin 3, (j' : ℕ) < k ∧ π (.inl j) = .inl j') :
    (tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k).map (g : V0 →ₗ[ZMod 2] V0) =
      tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq _ _)
  rw [tailFlag, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
  obtain ⟨j', hj', e⟩ := hπ j hj
  rw [LinearEquiv.coe_coe, hg, e]
  exact Submodule.subset_span ⟨j', hj', rfl⟩

theorem map_tailFlag_ne_of_hypVec {g : V0 ≃ₗ[ZMod 2] V0} {π : Equiv.Perm (Fin 3 ⊕ Fin 3)}
    (hg : ∀ c, g (hypVec (ZMod 2) (Fin 2 → ZMod 2) c) = hypVec (ZMod 2) (Fin 2 → ZMod 2) (π c))
    {k : ℕ} {j : Fin 3} (hj : (j : ℕ) < k)
    (hπ : ∀ j' : Fin 3, (j' : ℕ) < k → π (.inl j) ≠ .inl j') :
    (tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k).map (g : V0 →ₗ[ZMod 2] V0) ≠
      tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k := by
  intro h
  have hmem : g (hypVec (ZMod 2) (Fin 2 → ZMod 2) (.inl j)) ∈
      tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k := by
    rw [← h]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, hj, rfl⟩)
  rw [hg, hypVec_mem_tailFlag_iff] at hmem
  obtain ⟨j', hj', e⟩ := hmem
  exact hπ j' hj' e

theorem hypPerm_fix : ∀ i k : Fin 3, k ≠ i → ∀ j : Fin 3, (j : ℕ) < k + 1 →
    ∃ j' : Fin 3, (j' : ℕ) < k + 1 ∧ hypPerm i (.inl j) = .inl j' := by
  decide

theorem hypPerm_move : ∀ (i : Fin 3) (j' : Fin 3), (j' : ℕ) < i + 1 →
    hypPerm i (.inl i) ≠ .inl j' := by
  decide

theorem map_baseFlag_natLevi
    {i k : Fin 3} (hk : k ≠ i) :
    (baseFlag k).map (rhoMinus (natLevi i) : V0 →ₗ[ZMod 2] V0) = baseFlag k :=
  map_tailFlag_eq_of_hypVec (rhoMinus_natLevi_hypVec i) (hypPerm_fix i k hk)

theorem map_baseFlag_natLevi_ne
    (i : Fin 3) :
    (baseFlag i).map (rhoMinus (natLevi i) : V0 →ₗ[ZMod 2] V0) ≠ baseFlag i :=
  map_tailFlag_ne_of_hypVec (rhoMinus_natLevi_hypVec i) (j := i) (by omega) (hypPerm_move i)

end CFSG.LieType.Chevalley.C2E6Std.FourthResidue
