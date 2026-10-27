module

public import CFSG.LargeExtraspecial.A2ModCfgARS
public import CFSG.LargeExtraspecial.A2ModCfg
public import CFSG.Timmesfeld.ARS.Induction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module Matrix CFSG.RankThree.OrthogonalInvolutions CFSG.Timmesfeld.ARS CFSG.LieType
  CFSG.LieType.Universal
open CFSG.Timmesfeld (sroot edgeD)

variable {X : Type} [Group X] {R : Set (Subgroup X)} {D : Set X}


theorem exists_isLeviNode_of_isConfig_D [Finite X] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d) (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    {m : ℕ} (hm : 3 ≤ m) {A B : Fin (m + 1) → Subgroup X}
    (hX : IsConfig R (edgeD (m + 1)) A B) (hgen : ⨆ j, (A j ⊔ B j) = ⊤) :
    ∃ (Ψ : SpecialLinearGroup (Fin (m + 1)) (ZMod 2) →* X) (a b : X),
      IsLeviNode D Ψ a b ∧ Ψ.range ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b = ⊤ := by
  choose gA hgA hA using fun j => hRD (A j) (hX.memA j)
  choose gB hgB hB using fun j => hRD (B j) (hX.memB j)
  have hchain : IsConfig R (CFSG.Timmesfeld.ARS.edgeA m) (A ∘ Fin.castSucc) (B ∘ Fin.castSucc) :=
    isConfig_comp hX (Fin.castSucc_injective m) fun i j => by
      simp only [CFSG.Timmesfeld.ARS.edgeA, edgeD, Fin.val_castSucc]
      omega
  obtain ⟨Ψ, hΨA, hΨB⟩ :=
    exists_levi_zmodTwo hR hiso (card_eq_two_of_forall_eq_zpowers hR hRD) hm hchain
  have hvA : ∀ j : Fin m, Ψ (elemTv j.castSucc j.succ) = gA j.castSucc := fun j =>
    map_elemTv_castSucc_succ Ψ j (mul_self_and_ne_one_of_mem hR (hX.memA _) (hA _)).2
      ((hΨA j).trans (hA _))
  have hvB : ∀ j : Fin m, Ψ (elemTv j.succ j.castSucc) = gB j.castSucc := fun j =>
    map_elemTv_succ_castSucc Ψ j (mul_self_and_ne_one_of_mem hR (hX.memB _) (hB _)).2
      ((hΨB j).trans (hB _))
  have hlast : ∀ j : Fin m, ¬ edgeD (m + 1) (Fin.last m) j.castSucc := fun j h => by
    simp only [edgeD, Fin.val_last, Fin.val_castSucc] at h
    omega
  have hedge : ∀ j : Fin m, j.val + 2 = m → edgeD (m + 1) j.castSucc (Fin.last m) := fun j hj =>
    Or.inr ⟨by simp only [Fin.val_castSucc]; omega, by simp⟩
  have hnonadj : ∀ j : Fin m, j.val + 2 ≠ m → ¬ edgeD (m + 1) j.castSucc (Fin.last m) :=
    fun j hj h => by
      simp only [edgeD, Fin.val_last, Fin.val_castSucc] at h
      omega
  have hca : ∀ j : Fin m, Commute (gA (Fin.last m)) (gB j.castSucc) := by
    intro j
    by_cases hj : j.val + 2 = m
    · obtain ⟨-, c, -⟩ := hX.edge _ _ (hedge j hj)
      exact (c _ (mem_of_eq_zpowers (hB _)) _ (mem_of_eq_zpowers (hA _))).symm
    · exact (hX.nonadj _ _ (Fin.castSucc_lt_last j).ne' (hlast j) (hnonadj j hj)).2.1 _
        (mem_of_eq_zpowers (hA _)) _ (mem_of_eq_zpowers (hB _))
  have hcb : ∀ j : Fin m, Commute (gB (Fin.last m)) (gA j.castSucc) := by
    intro j
    by_cases hj : j.val + 2 = m
    · obtain ⟨-, -, -, c, -⟩ := hX.edge _ _ (hedge j hj)
      exact (c _ (mem_of_eq_zpowers (hA _)) _ (mem_of_eq_zpowers (hB _))).symm
    · exact (hX.nonadj _ _ (Fin.castSucc_lt_last j).ne' (hlast j) (hnonadj j hj)).2.2.1 _
        (mem_of_eq_zpowers (hB _)) _ (mem_of_eq_zpowers (hA _))
  have hcoll := fun (j : Fin m) (hj : j.val + 2 = m) =>
    mul_mem_of_isConfig_adj hR hiso hX (isRootedTree_D (by omega)) hDc (hedge j hj) (hA _)
      (hB _) (hA _) (hB _) (hgA _) (hgB _) (hgB _)
  have h01 : (⟨0, by omega⟩ : Fin m).castSucc ≠ (⟨0, by omega⟩ : Fin m).succ :=
    Fin.castSucc_lt_succ.ne
  refine ⟨Ψ, gA (Fin.last m), gB (Fin.last m),
    ⟨map_mem_of_elemTv_mem hDc Ψ h01 (by rw [hvA]; exact hgA _), hgA _, hgB _, ?_, ?_, ?_, ?_⟩,
    ?_⟩
  · intro i j hij
    obtain ⟨j', rfl, rfl⟩ : ∃ j' : Fin m, j'.succ = i ∧ j'.castSucc = j :=
      ⟨⟨j.val, by omega⟩, Fin.ext (by simp; omega), Fin.ext rfl⟩
    rw [hvB]
    exact hca j'
  · intro i j hij
    obtain ⟨j', rfl, rfl⟩ : ∃ j' : Fin m, j'.castSucc = i ∧ j'.succ = j :=
      ⟨⟨i.val, by omega⟩, Fin.ext rfl, Fin.ext (by simp; omega)⟩
    rw [hvA]
    exact hcb j'
  · intro i j hi hj
    obtain ⟨j', rfl, rfl⟩ : ∃ j' : Fin m, j'.succ = i ∧ j'.castSucc = j :=
      ⟨⟨j.val, by omega⟩, Fin.ext (by simp; omega), Fin.ext rfl⟩
    rw [hvB]
    exact (hcoll j' (by simp at hj; omega)).1
  · intro i j hi hj
    obtain ⟨j', rfl, rfl⟩ : ∃ j' : Fin m, j'.castSucc = i ∧ j'.succ = j :=
      ⟨⟨i.val, by omega⟩, Fin.ext rfl, Fin.ext (by simp; omega)⟩
    rw [hvA]
    exact (hcoll j' (by simp at hi; omega)).2.1
  · rw [eq_top_iff, ← hgen]
    refine iSup_le fun j => ?_
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · refine sup_le ?_ ?_
      · exact (hΨA j').symm.le.trans
          ((Subgroup.map_le_range Ψ _).trans (le_sup_left.trans le_sup_left))
      · exact (hΨB j').symm.le.trans
          ((Subgroup.map_le_range Ψ _).trans (le_sup_left.trans le_sup_left))
    · rw [hA, hB]
      exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem typeD_finrank_commSpaceOf_eq [Finite X] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d) (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) {k : ℕ} (hk : 5 ≤ k) (hX : HasGenConfig R (edgeD k)) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) = 2 * k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨A, B, hX, hgen⟩ := hX
  obtain ⟨Ψ, a, b, hL, htop⟩ :=
    exists_isLeviNode_of_isConfig_D hR hiso hRD hDc (by omega) hX hgen
  rw [← htop]
  exact hL.finrank_commSpaceOf_eq hA hk

theorem typeD_irreducible [Finite X] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hZ : Subgroup.center X = ⊥) (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d)
    (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hA : A2Action D Q ρ) {k : ℕ} (hk : 5 ≤ k)
    (hX : HasGenConfig R (edgeD k))
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤) :
    finrank (ZMod 2) V = 2 * k ∧ CFSG.Blueprint.LieModel X .POmegaPlus k 2 1 := by
  have h := typeD_finrank_commSpaceOf_eq hR hiso hRD hDc hA hk hX
  obtain ⟨A, B, hX', hgen⟩ := hX
  obtain ⟨d, hd, -⟩ := hRD _ (hX'.memA ⟨0, by omega⟩)
  rw [hA.commSpaceOf_top_eq_top hd hirr, finrank_top] at h
  obtain ⟨f, -, hcard, hmod⟩ := hX'.lieModel_D hR hiso hZ (by omega) hgen
  obtain rfl : f = 1 := by
    have h2 := hcard _ (hX'.memA ⟨0, by omega⟩)
    rw [card_eq_two_of_forall_eq_zpowers hR hRD _ (hX'.memA _)] at h2
    exact Nat.pow_right_injective le_rfl (h2.symm.trans (pow_one 2).symm)
  exact ⟨h, hmod⟩

theorem typeD_four_finrank_commSpaceOf_le [Finite X] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d) (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) (hX : HasGenConfig R (edgeD 4)) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 9 := by
  obtain ⟨A, B, hX, hgen⟩ := hX
  obtain ⟨Ψ, a, b, hL, htop⟩ :=
    exists_isLeviNode_of_isConfig_D (m := 3) hR hiso hRD hDc le_rfl hX hgen
  rw [← htop]
  exact hL.finrank_commSpaceOf_le hA rfl

theorem typeD_four_finrank_le [Finite X] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d) (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) (hX : HasGenConfig R (edgeD 4))
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤) :
    finrank (ZMod 2) V ≤ 9 := by
  have h := typeD_four_finrank_commSpaceOf_le hR hiso hRD hDc hA hX
  obtain ⟨A, B, hX', -⟩ := hX
  obtain ⟨d, hd, -⟩ := hRD _ (hX'.memA 0)
  rwa [hA.commSpaceOf_top_eq_top hd hirr, finrank_top] at h

end CFSG.LargeExtraspecial.A2Mod
