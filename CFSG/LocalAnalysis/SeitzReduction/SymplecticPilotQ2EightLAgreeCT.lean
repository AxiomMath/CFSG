module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightLinearRow

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.LieType.Universal.SpecialLinear (fundamentalRootSubgroup)
open scoped MatrixGroups

@[expose] def q2EightPerm : Fin 8 ≃ Fin 8 where
  toFun := ![0, 1, 2, 4, 5, 3, 6, 7]
  invFun := ![0, 1, 2, 5, 3, 4, 6, 7]
  left_inv := by decide
  right_inv := by decide

theorem exists_plane_eightPerm_numeric : ∀ a b : Fin 7, ∃ k : Fin 4,
    (q2EightPerm a.castSucc).val / 2 ≠ k.val ∧ (q2EightPerm a.succ).val / 2 ≠ k.val ∧
      (q2EightPerm b.castSucc).val / 2 ≠ k.val ∧ (q2EightPerm b.succ).val / 2 ≠ k.val := by
  decide

@[expose] def q2EightCoord {m : ℕ} (h : m + 1 = 2 * 4 + 0) : Fin (m + 1) ≃ Fin (2 * 4 + 0) :=
  (finCongr h).trans q2EightPerm

variable {K : Type} [Field K]

@[expose] noncomputable def q2EightCastSL {m : ℕ} (h : m + 1 = 2 * 4 + 0) :
    SpecialLinearGroup (Fin (m + 1)) K ≃* SpecialLinearGroup (Fin (2 * 4 + 0)) K :=
  LinearPilot.reindexSpecialLinear (q2EightCoord h)

theorem q2EightCastSL_transvection {m : ℕ} (h : m + 1 = 2 * 4 + 0) {i j : Fin (m + 1)}
    (hij : i ≠ j) (c : K) :
    q2EightCastSL h (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection ((q2EightCoord h).injective.ne hij) c := by
  apply Subtype.ext
  change reindex (q2EightCoord h) (q2EightCoord h) (Matrix.transvection i j c) =
    Matrix.transvection (q2EightCoord h i) (q2EightCoord h j) c
  ext a b
  simp only [reindex_apply, submatrix_apply, Matrix.transvection, Matrix.add_apply,
    Matrix.one_apply, single_apply, Equiv.eq_symm_apply, Equiv.apply_symm_apply]

theorem exists_plane_notMem_eightPerm {m : ℕ} (h : m + 1 = 2 * 4 + 0) (J : Finset (Fin m))
    (hJ : J.card ≤ 2) :
    ∃ k : Fin 4, ∀ j ∈ J, q2EightCoord h j.castSucc ∉ planeCoordsQ2 0 {k} ∧
      q2EightCoord h j.succ ∉ planeCoordsQ2 0 {k} := by
  have hm : m = 7 := by omega
  subst hm
  have hc : ∀ j : Fin 7, q2EightCoord h j.castSucc = q2EightPerm j.castSucc := fun j => rfl
  have hs : ∀ j : Fin 7, q2EightCoord h j.succ = q2EightPerm j.succ := fun j => rfl
  have key : ∀ a b : Fin 7, ∃ k : Fin 4, ∀ j : Fin 7, (j = a ∨ j = b) →
      q2EightCoord h j.castSucc ∉ planeCoordsQ2 0 {k} ∧
        q2EightCoord h j.succ ∉ planeCoordsQ2 0 {k} := by
    intro a b
    obtain ⟨k, hka⟩ := exists_plane_eightPerm_numeric a b
    refine ⟨k, fun j hj => ?_⟩
    rcases hj with rfl | rfl
    · exact ⟨notMem_planeCoordsQ2_four (Or.inl (by rw [hc]; exact hka.1)),
        notMem_planeCoordsQ2_four (Or.inl (by rw [hs]; exact hka.2.1))⟩
    · exact ⟨notMem_planeCoordsQ2_four (Or.inl (by rw [hc]; exact hka.2.2.1)),
        notMem_planeCoordsQ2_four (Or.inl (by rw [hs]; exact hka.2.2.2))⟩
  rcases Nat.lt_or_ge J.card 2 with hlt | hge
  · rcases Nat.lt_or_ge J.card 1 with h0 | h1
    · have hJe : J = ∅ := Finset.card_eq_zero.1 (by omega)
      subst hJe
      exact ⟨0, fun j hj => by simp at hj⟩
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 (show J.card = 1 by omega)
      obtain ⟨k, hk⟩ := key a a
      exact ⟨k, fun j hj => hk j (Or.inl (Finset.mem_singleton.1 hj))⟩
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (show J.card = 2 by omega)
    obtain ⟨k, hk⟩ := key a b
    exact ⟨k, fun j hj => hk j (by simpa using hj)⟩

theorem map_levi_le_q2Block_eightPerm {m : ℕ} (h : m + 1 = 2 * 4 + 0) {J : Finset (Fin m)}
    {k : Fin 4} (hk : ∀ j ∈ J, q2EightCoord h j.castSucc ∉ planeCoordsQ2 0 {k} ∧
      q2EightCoord h j.succ ∉ planeCoordsQ2 0 {k}) :
    (CFSG.LieType.Universal.SpecialLinear.levi m K J).map (q2EightCastSL h).toMonoidHom ≤
      q2Block 0 K {k} := by
  rw [CFSG.LieType.Universal.SpecialLinear.levi, Subgroup.map_iSup]
  refine iSup_le fun j => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hj => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun s => ?_
  rintro _ ⟨x, hx, rfl⟩
  have hk' := hk j hj
  cases s
  · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ x).1 hx
    rw [MulEquiv.coe_toMonoidHom, q2EightCastSL_transvection]
    exact LinearPilot.transvection_mem_blockSpecialLinear _ (Finset.mem_compl.2 hk'.2)
      (Finset.mem_compl.2 hk'.1) c
  · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ x).1 hx
    rw [MulEquiv.coe_toMonoidHom, q2EightCastSL_transvection]
    exact LinearPilot.transvection_mem_blockSpecialLinear _ (Finset.mem_compl.2 hk'.1)
      (Finset.mem_compl.2 hk'.2) c

theorem blockSpecialLinear_le_map_levi_eightPerm {m : ℕ} (h : m + 1 = 2 * 4 + 0) (j : Fin m) :
    blockSpecialLinear ({q2EightCoord h j.castSucc, q2EightCoord h j.succ} :
        Finset (Fin (2 * 4 + 0))) ≤
      (CFSG.LieType.Universal.SpecialLinear.levi m K {j}).map (q2EightCastSL h).toMonoidHom := by
  rw [LinearPilot.blockSpecialLinear_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, i', hii, c, hi, hi', rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hi'
  have hlevi : ∀ s : Bool, fundamentalRootSubgroup m K j s ≤
      CFSG.LieType.Universal.SpecialLinear.levi m K {j} := fun s =>
    le_iSup_of_le j (le_iSup_of_le (Finset.mem_singleton_self j)
      (le_iSup (fun s => fundamentalRootSubgroup m K j s) s))
  rcases hi with rfl | rfl <;> rcases hi' with rfl | rfl
  · exact absurd rfl hii
  · refine ⟨SpecialLinearGroup.transvection
      (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne c,
      hlevi true (CFSG.LieType.Universal.SpecialLinear.transvection_mem_rootSubgroup _ c), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, q2EightCastSL_transvection]
  · refine ⟨SpecialLinearGroup.transvection
      (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne' c,
      hlevi false (CFSG.LieType.Universal.SpecialLinear.transvection_mem_rootSubgroup _ c), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, q2EightCastSL_transvection]
  · exact absurd rfl hii

section Commute

variable {G : Type} [Group G] {L : Subgroup G} {hK : Nat.card K = 2} {e : L ≃* StatedSp 4 K}

theorem commute_productPiece_of_nsLinParamAgree_even (P : ∀ k : Fin 4, NsLinParam hK 0 e k)
    (hagree : NsLinParamAgree P) :
    ∀ x ∈ blockSpecialLinear ({ctF 4 0 0, ctE 4 0 1} : Finset (Fin (2 * 4 + 0))),
      ∀ y ∈ blockSpecialLinear ({ctF 4 0 2, ctE 4 0 3} : Finset (Fin (2 * 4 + 0))),
      ∀ (hx : x ∈ q2Block 0 K {2}) (hy : y ∈ q2Block 0 K {0}),
        Commute ((P 2).Φ ⟨x, hx⟩) ((P 0).Φ ⟨y, hy⟩) := by
  classical
  intro x hx y hy hx2 hy0
  have hm : (7 : ℕ) + 1 = 2 * 4 + 0 := rfl
  choose kJ hkJ using fun (J : {J : Finset (Fin 7) // J.card ≤ 2}) =>
    exists_plane_notMem_eightPerm hm J.1 J.2
  have hKle : ∀ (J : {J : Finset (Fin 7) // J.card ≤ 2}) (z : SpecialLinearGroup (Fin (7 + 1)) K),
      z ∈ (CFSG.LieType.Universal.SpecialLinear.rootDatum 7 K).leviAmalgam J →
        q2EightCastSL hm z ∈ q2Block 0 K {kJ J} := by
    intro J z hzJ
    have hz : z ∈ CFSG.LieType.Universal.SpecialLinear.levi 7 K J.1 := by
      rw [← CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
      exact hzJ
    exact map_levi_le_q2Block_eightPerm hm (hkJ J) ⟨z, hz, rfl⟩
  set φ : ∀ J : {J : Finset (Fin 7) // J.card ≤ 2},
      (CFSG.LieType.Universal.SpecialLinear.rootDatum 7 K).leviAmalgam J →* G := fun J =>
    (P (kJ J)).Φ.comp (((q2EightCastSL hm).toMonoidHom.comp (Subgroup.subtype _)).codRestrict _
      fun z => hKle J z z.2) with hφ
  have hcomp : CFSG.LieType.CurtisTits.IsCompatible
      (CFSG.LieType.Universal.SpecialLinear.rootDatum 7 K).leviAmalgam φ := by
    intro I J _ z w hzw
    change (P (kJ I)).Φ ⟨q2EightCastSL hm z, hKle I z z.2⟩ =
      (P (kJ J)).Φ ⟨q2EightCastSL hm w, hKle J w w.2⟩
    have hz' : q2EightCastSL hm (z : SpecialLinearGroup (Fin (7 + 1)) K) ∈ q2Block 0 K {kJ J} :=
      hzw ▸ hKle J w w.2
    rw [hagree (kJ I) (kJ J) _ (hKle I z z.2) hz']
    congr 2
    rw [hzw]
  obtain ⟨ψ, hψ, -⟩ :=
    CFSG.LieType.CurtisTits.isUniversalCompletion_specialLinear.{0} 7 K G φ hcomp
  have hψ' : ∀ (J : {J : Finset (Fin 7) // J.card ≤ 2})
      (w : SpecialLinearGroup (Fin (2 * 4 + 0)) K),
      w ∈ (CFSG.LieType.Universal.SpecialLinear.levi 7 K J.1).map (q2EightCastSL hm).toMonoidHom →
      ∀ (k : Fin 4) (hw : w ∈ q2Block 0 K {k}),
        ψ ((q2EightCastSL hm).symm w) = (P k).Φ ⟨w, hw⟩ := by
    rintro J _ ⟨z, hz, rfl⟩ k hw
    have hz' : z ∈ (CFSG.LieType.Universal.SpecialLinear.rootDatum 7 K).leviAmalgam J := by
      have h1 : z ∈ CFSG.LieType.CurtisTits.levi
          (CFSG.LieType.Universal.SpecialLinear.rootGroup 7 K) J.1 := by
        rw [CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
        exact hz
      exact h1
    have h1 := hψ J ⟨z, hz'⟩
    change ψ z = (P (kJ J)).Φ ⟨q2EightCastSL hm z, hKle J z hz'⟩ at h1
    change ψ ((q2EightCastSL hm).symm (q2EightCastSL hm z)) = (P k).Φ ⟨q2EightCastSL hm z, hw⟩
    rw [MulEquiv.symm_apply_apply, h1]
    exact hagree _ _ _ _ _
  have hlevi_mono : ∀ {I I' : Finset (Fin 7)}, I ⊆ I' →
      CFSG.LieType.Universal.SpecialLinear.levi 7 K I ≤
        CFSG.LieType.Universal.SpecialLinear.levi 7 K I' :=
    fun h => biSup_mono fun j hj => h hj
  have hxJ : x ∈ (CFSG.LieType.Universal.SpecialLinear.levi 7 K ({1} : Finset (Fin 7))).map
      (q2EightCastSL hm).toMonoidHom := by
    refine blockSpecialLinear_le_map_levi_eightPerm hm 1 ?_
    have e1 : ({ctF 4 0 0, ctE 4 0 1} : Finset (Fin (2 * 4 + 0))) =
        {q2EightCoord hm (1 : Fin 7).castSucc, q2EightCoord hm (1 : Fin 7).succ} := by
      rw [show ctF 4 0 0 = q2EightCoord hm (1 : Fin 7).castSucc from Fin.ext rfl,
        show ctE 4 0 1 = q2EightCoord hm (1 : Fin 7).succ from Fin.ext rfl]
    rw [← e1]
    exact hx
  have hyJ : y ∈ (CFSG.LieType.Universal.SpecialLinear.levi 7 K ({4, 5} : Finset (Fin 7))).map
      (q2EightCastSL hm).toMonoidHom := by
    have e5 : ctF 4 0 2 = q2EightCoord hm (4 : Fin 7).castSucc := Fin.ext rfl
    have e3 : q2EightCoord hm (4 : Fin 7).succ = q2EightCoord hm (5 : Fin 7).castSucc :=
      Fin.ext rfl
    have e6 : ctE 4 0 3 = q2EightCoord hm (5 : Fin 7).succ := Fin.ext rfl
    have v5 : (ctF 4 0 2).val = 5 := rfl
    have v3 : (q2EightCoord hm (4 : Fin 7).succ).val = 3 := rfl
    have v6 : (ctE 4 0 3).val = 6 := rfl
    have hne1 : ctF 4 0 2 ≠ ctE 4 0 3 := fun h => by
      have := congrArg Fin.val h
      omega
    have hne2 : ctF 4 0 2 ≠ q2EightCoord hm (4 : Fin 7).succ := fun h => by
      have := congrArg Fin.val h
      omega
    have hne3 : q2EightCoord hm (4 : Fin 7).succ ≠ ctE 4 0 3 := fun h => by
      have := congrArg Fin.val h
      omega
    have h1 := (blockSpecialLinear_pair_le_sup_of_ne hne1 hne2 hne3) hy
    have h2 : blockSpecialLinear ({ctF 4 0 2, q2EightCoord hm (4 : Fin 7).succ} :
          Finset (Fin (2 * 4 + 0))) ⊔
        blockSpecialLinear ({q2EightCoord hm (4 : Fin 7).succ, ctE 4 0 3} :
          Finset (Fin (2 * 4 + 0))) ≤
        (CFSG.LieType.Universal.SpecialLinear.levi 7 K ({4, 5} : Finset (Fin 7))).map
          (q2EightCastSL hm).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [e5]
        exact (blockSpecialLinear_le_map_levi_eightPerm hm 4).trans
          (map_mono (hlevi_mono (by simp)))
      · rw [e3, e6]
        exact (blockSpecialLinear_le_map_levi_eightPerm hm 5).trans
          (map_mono (hlevi_mono (by simp)))
    exact h2 h1
  have hψx := hψ' ⟨{1}, by simp⟩ x hxJ 2 hx2
  have hψy := hψ' ⟨{4, 5}, by decide⟩ y hyJ 0 hy0
  have hdisj : Disjoint ({ctF 4 0 0, ctE 4 0 1} : Finset (Fin (2 * 4 + 0)))
      {ctF 4 0 2, ctE 4 0 3} := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with h | h <;>
      · have := congrArg Fin.val h
        simp at this
  have hxy := LinearPilot.commute_blockSpecialLinear_of_disjoint hdisj hx hy
  rw [Commute, SemiconjBy, ← hψx, ← hψy, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hxy.eq]

end Commute

@[expose] def SpTwoLinearEvenEightAlignInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, NsKindSp e t k .linearEven) →
      ∃ P : ∀ k : Fin 4, NsLinParam hK 0 e k, NsLinParamAgree P

theorem spTwoLinearEvenEightAgreeInput_of_align (h : SpTwoLinearEvenEightAlignInput) :
    SpTwoLinearEvenEightAgreeInput := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot
  obtain ⟨P, hP⟩ := h G L hset K hK e t ht hKt hroot
  exact ⟨P, hP, commute_productPiece_of_nsLinParamAgree_even P hP⟩

end CFSG.SeitzReduction.SymplecticPilot
