module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabTorus
public import CFSG.ClassicalInvolution.Phan.PhanDn.PanelParabLe
public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamilyGood
public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelCommute
public import CFSG.LieType.Universal.Spin.Roots.TypeD
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Phan.PhanDn.ChamberMoves
public import CFSG.LocalAnalysis.StandardType.PhanEBridgeGeom

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.StandardType CFSG.StandardType.QTwo

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

@[expose] noncomputable def qTwoForkSwap (m : ℕ) (hm : 3 ≤ m) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 1)) (Fin.last m)

@[simp] theorem qTwoForkSwap_apply_penultimate (m : ℕ) (hm : 3 ≤ m) :
    qTwoForkSwap m hm (⟨m - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := by
  rw [qTwoForkSwap]
  exact Equiv.swap_apply_left _ _

@[simp] theorem qTwoForkSwap_apply_last (m : ℕ) (hm : 3 ≤ m) :
    qTwoForkSwap m hm (Fin.last m) = (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
  rw [qTwoForkSwap]
  exact Equiv.swap_apply_right _ _

theorem qTwoForkSwap_apply_of_ne (m : ℕ) (hm : 3 ≤ m) {i : Fin (m + 1)}
    (hi₁ : i ≠ (⟨m - 1, by omega⟩ : Fin (m + 1))) (hi₂ : i ≠ Fin.last m) :
    qTwoForkSwap m hm i = i := by
  rw [qTwoForkSwap]
  exact Equiv.swap_apply_of_ne_of_ne hi₁ hi₂

@[simp] theorem qTwoForkSwap_apply_apply (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1)) :
    qTwoForkSwap m hm (qTwoForkSwap m hm i) = i := by
  by_cases hi₁ : i = (⟨m - 1, by omega⟩ : Fin (m + 1))
  · subst hi₁
    rw [qTwoForkSwap_apply_penultimate, qTwoForkSwap_apply_last]
  · by_cases hi₂ : i = Fin.last m
    · subst hi₂
      rw [qTwoForkSwap_apply_last, qTwoForkSwap_apply_penultimate]
    · rw [qTwoForkSwap_apply_of_ne m hm hi₁ hi₂,
        qTwoForkSwap_apply_of_ne m hm hi₁ hi₂]

private theorem qTwoForkSwap_edge_iff (m : ℕ) (hm : 3 ≤ m) (i j : Fin (m + 1)) :
    (((qTwoForkSwap m hm j).val = (qTwoForkSwap m hm i).val + 1 ∧
          (qTwoForkSwap m hm j).val ≤ m - 1) ∨
        ((qTwoForkSwap m hm i).val = (qTwoForkSwap m hm j).val + 1 ∧
          (qTwoForkSwap m hm i).val ≤ m - 1) ∨
        ((qTwoForkSwap m hm i).val + 2 = m ∧ (qTwoForkSwap m hm j).val = m) ∨
        ((qTwoForkSwap m hm j).val + 2 = m ∧ (qTwoForkSwap m hm i).val = m)) ↔
      ((j.val = i.val + 1 ∧ j.val ≤ m - 1) ∨
        (i.val = j.val + 1 ∧ i.val ≤ m - 1) ∨
        (i.val + 2 = m ∧ j.val = m) ∨ (j.val + 2 = m ∧ i.val = m)) := by
  let a : Fin (m + 1) := ⟨m - 1, by omega⟩
  let b : Fin (m + 1) := Fin.last m
  have hs : qTwoForkSwap m hm = Equiv.swap a b := rfl
  rw [hs]
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    by_cases hja : j = a <;> by_cases hjb : j = b <;>
    simp [Equiv.swap_apply_def, hia, hib, hja, hjb, a, b] <;> omega

theorem qTwoForkSwap_coxeter (m : ℕ) (hm : 3 ≤ m) (i j : Fin (m + 1)) :
    CFSG.StandardType.ggCoxeterMatrixD (m + 1)
        (qTwoForkSwap m hm i) (qTwoForkSwap m hm j) =
      CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j := by
  by_cases hij : i = j
  · subst hij
    rw [qtwoLabel_self (m + 1) (qTwoForkSwap m hm i), qtwoLabel_self (m + 1) i]
  · have hsij : qTwoForkSwap m hm i ≠ qTwoForkSwap m hm j := fun h =>
      hij ((qTwoForkSwap m hm).injective h)
    rcases ggCoxeterMatrixD_two_or_three i j hij with h2 | h3
    · have h2' : CFSG.StandardType.ggCoxeterMatrixD (m + 1)
          (qTwoForkSwap m hm i) (qTwoForkSwap m hm j) = 2 := by
        rw [qtwoLabel_two_iff hm _ _ hsij, qTwoForkSwap_edge_iff]
        exact (qtwoLabel_two_iff hm i j hij).mp h2
      rw [h2, h2']
    · have h3' : CFSG.StandardType.ggCoxeterMatrixD (m + 1)
          (qTwoForkSwap m hm i) (qTwoForkSwap m hm j) = 3 := by
        rw [qtwoLabel_three_iff hm _ _, qTwoForkSwap_edge_iff]
        exact (qtwoLabel_three_iff hm i j).mp h3
      rw [h3, h3']

theorem qTwoShape_forkSwap (m : ℕ) (hm : 3 ≤ m) {C : Set (Fin (m + 1))}
    (hC : C ∈ qTwoShape (CFSG.StandardType.ggCoxeterMatrixD (m + 1))) :
    qTwoForkSwap m hm '' C ∈ qTwoShape (CFSG.StandardType.ggCoxeterMatrixD (m + 1)) := by
  let s := qTwoForkSwap m hm
  change s '' C ∈ qTwoShape (CFSG.StandardType.ggCoxeterMatrixD (m + 1))
  refine ⟨?_, ?_⟩
  · intro huniv
    apply hC.1
    apply Set.eq_univ_of_forall
    intro x
    have hx : s x ∈ s '' C := by rw [huniv]; exact Set.mem_univ _
    obtain ⟨c, hc, hcx⟩ := hx
    rwa [s.injective hcx] at hc
  · rcases hC.2 with h3 | hA
    · exact Or.inl (by rwa [Set.ncard_image_of_injective C s.injective])
    · right
      obtain ⟨i, k, j, l, rfl, hik, hjl, hij, hil, hkj, hkl⟩ := hA
      refine ⟨s i, s k, s j, s l, by simp [s], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [qTwoForkSwap_coxeter m hm i k]; exact hik
      · rw [qTwoForkSwap_coxeter m hm j l]; exact hjl
      · rw [qTwoForkSwap_coxeter m hm i j]; exact hij
      · rw [qTwoForkSwap_coxeter m hm i l]; exact hil
      · rw [qTwoForkSwap_coxeter m hm k j]; exact hkj
      · rw [qTwoForkSwap_coxeter m hm k l]; exact hkl


private theorem conjTau_smul_flagChamber_iff (m : ℕ) (hm : 3 ≤ m)
    (x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
    (j : Fin (m + 1)) :
    (conjTau E x) • flagChamber E m j = flagChamber E m j ↔
      x • flagChamber E m (qTwoForkSwap m hm j) =
        flagChamber E m (qTwoForkSwap m hm j) := by
  let W := Fin (m + 1) → K
  let X := Fin (m + 1) ⊕ Fin (m + 1) → K
  let elt := (stdDChamber (unitaryInvolution K 2 1) (m + 1)).elt
  let s := qTwoForkSwap m hm
  let τ : W ≃ₗ[F] W := tauAt E (Fin.last m)
  have hbcτ : (bc E (m + 1) τ)⁻¹ = bc E (m + 1) τ := by
    apply inv_eq_of_mul_eq_one_right
    rw [← map_mul, tauAt_mul_self, map_one]
  have hbc : bc E (m + 1) ((conjTau E x :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) : W ≃ₗ[F] W) =
      bc E (m + 1) τ * bc E (m + 1) (x : W ≃ₗ[F] W) * bc E (m + 1) τ := by
    rw [coe_conjTau, map_mul, map_mul, map_inv, hbcτ]
  have hinj : Function.Injective (bcLin E (m + 1) (τ : W →ₗ[F] W)) := by
    intro u v huv
    rw [bcLin_eq_coe_bc] at huv
    exact (bc E (m + 1) τ).injective huv
  have helt : ∀ k : Fin (m + 1),
      (elt k).map (bcLin E (m + 1) (τ : W →ₗ[F] W)) = elt (s k) := by
    intro k
    simpa [s, qTwoForkSwap, elt, τ] using map_bc_tauAt_elt (f := 1) E hm k
  have hmap : (elt j).map
        (bcLin E (m + 1) (((conjTau E x :
          ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) : W ≃ₗ[F] W))) =
      ((elt (s j)).map (bcLin E (m + 1) ((x : W ≃ₗ[F] W) : W →ₗ[F] W))).map
        (bcLin E (m + 1) (τ : W →ₗ[F] W)) := by
    rw [bcLin_eq_coe_bc, bcLin_eq_coe_bc, bcLin_eq_coe_bc, hbc]
    rw [show ((bc E (m + 1) τ * bc E (m + 1) (x : W ≃ₗ[F] W) * bc E (m + 1) τ :
          X ≃ₗ[K] X) : X →ₗ[K] X) =
        (bc E (m + 1) τ : X →ₗ[K] X).comp
          (((bc E (m + 1) (x : W ≃ₗ[F] W)) : X →ₗ[K] X).comp
            (bc E (m + 1) τ : X →ₗ[K] X)) from rfl,
      Submodule.map_comp, Submodule.map_comp, ← bcLin_eq_coe_bc E (m + 1) τ, helt j]
  constructor
  · intro h
    have hval := congrArg Subtype.val h
    rw [coe_smul_flagVert, coe_flagChamber, hmap] at hval
    apply Subtype.ext
    rw [coe_smul_flagVert, coe_flagChamber]
    apply Submodule.map_injective_of_injective hinj
    rw [hval, helt, qTwoForkSwap_apply_apply]
  · intro hx
    have hval := congrArg Subtype.val hx
    rw [coe_smul_flagVert, coe_flagChamber] at hval
    apply Subtype.ext
    rw [coe_smul_flagVert, coe_flagChamber, hmap]
    rw [hval, helt, qTwoForkSwap_apply_apply]

theorem map_qTwoParab_conjTau (m : ℕ) (hm : 3 ≤ m) (C : Set (Fin (m + 1))) :
    (qTwoParab E m C).map (conjTau E).toMonoidHom =
      qTwoParab E m (qTwoForkSwap m hm '' C) := by
  let s := qTwoForkSwap m hm
  change (qTwoParab E m C).map (conjTau E).toMonoidHom = qTwoParab E m (s '' C)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y ∈ qTwoParab E m C at hy
    rw [mem_qTwoParab] at hy
    change (conjTau E y) ∈ qTwoParab E m (s '' C)
    rw [mem_qTwoParab]
    intro k hk
    have hsk : s k ∉ C := fun hmem => hk ⟨s k, hmem, qTwoForkSwap_apply_apply m hm k⟩
    exact (conjTau_smul_flagChamber_iff E m hm y k).mpr (hy (s k) hsk)
  · intro hx
    change x ∈ qTwoParab E m (s '' C) at hx
    rw [mem_qTwoParab] at hx
    refine ⟨conjTau E x, ?_, conjTau_conjTau E x⟩
    change (conjTau E x) ∈ qTwoParab E m C
    rw [mem_qTwoParab]
    intro j hj
    have hsj : s j ∉ s '' C := by
      rintro ⟨c, hc, hcs⟩
      exact hj (by rwa [s.injective hcs] at hc)
    exact (conjTau_smul_flagChamber_iff E m hm x j).mpr (hx (s j) hsj)


private theorem subtype_comp_conjTau (m : ℕ) :
    (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))).comp
        (conjTau E).toMonoidHom =
      (stdConj E m).toMonoidHom.comp
        (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
  ext g v w
  change ((conjTau E g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) v w =
    (stdConj E m) (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) v w
  rw [coe_conjTau]
  rfl

private theorem map_stdConj_diagTorus (m : ℕ) :
    (diagTorusV F (unitaryInvolution K 2 1) (m + 1)).map
        (stdConj E m).toMonoidHom =
      diagTorusV F (unitaryInvolution K 2 1) (m + 1) := by
  apply le_antisymm
  · rintro x ⟨y, ⟨t, rfl⟩, rfl⟩
    rw [stdConj_diagHom]
    exact ⟨Function.update t (Fin.last m) ((t (Fin.last m))⁻¹), rfl⟩
  · intro x hx
    obtain ⟨t, rfl⟩ := hx
    refine ⟨(stdConj E m).toMonoidHom
      (diagHom F (unitaryInvolution K 2 1) (m + 1) t), ?_, ?_⟩
    · rw [stdConj_diagHom]
      exact ⟨Function.update t (Fin.last m) ((t (Fin.last m))⁻¹), rfl⟩
    · exact stdConj_stdConj E m _

theorem map_qTwoTor_iSup_conjTau (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m) :
    (⨆ i, qTwoTor E m hm i).map (conjTau E).toMonoidHom =
      ⨆ i, qTwoTor E m hm i := by
  let H := ⨆ i, qTwoTor E m hm i
  change H.map (conjTau E).toMonoidHom = H
  apply Subgroup.map_injective
    (f := Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
    (Subgroup.subtype_injective _)
  rw [Subgroup.map_map, subtype_comp_conjTau, ← Subgroup.map_map,
    map_qTwoTor_iSup_eq_diagTorus E hK m hm]
  exact map_stdConj_diagTorus E m


private theorem chainTheta_commute_tau (m : ℕ) (k : Fin m) (h : k.val + 1 < m)
    (hk : k.val + 2 < m) (B : Su K 2 1 3) :
    Commute (stdChainTheta (F := F) (f := 1) m k h B) (stdTau E m) := by
  have hblk : k.val + 3 ≤ m + 1 := by omega
  have hl : ¬ (k.val ≤ (Fin.last m).val ∧ (Fin.last m).val < k.val + 3) := by
    simp only [Fin.val_last]
    omega
  have hfix : blockEmb3 K 2 1 m k h B •
      (Pi.single (Fin.last m) (1 : K) : Fin (m + 1) → K) =
      Pi.single (Fin.last m) 1 := by
    change blockEmb K 2 1 (m + 1) 3 k.val hblk B • _ = _
    exact blockEmb_smul_single_of_not_mem hblk B hl
  have hpres : ∀ x : Fin (m + 1) → K, x (Fin.last m) = 0 →
      (blockEmb3 K 2 1 m k h B • x) (Fin.last m) = 0 := by
    intro x hx
    rw [CFSG.ClassicalGroups.Unitary.smul_def, coe_coe_blockEmb3, blockMat_mulVec_of_not_mem _ _ hl]
    exact hx
  exact suEndN_commute_tauAt E (blockEmb3 K 2 1 m k h B) (Fin.last m) hfix hpres

private theorem stdConj_chainTheta (m : ℕ) (k : Fin m) (h : k.val + 1 < m)
    (hk : k.val + 2 < m) (B : Su K 2 1 3) :
    (stdConj E m).toMonoidHom (stdChainTheta (F := F) (f := 1) m k h B) =
      stdChainTheta (F := F) (f := 1) m k h B := by
  have hc := chainTheta_commute_tau E m k h hk B
  rw [stdConj]
  change MulAut.conj (stdTau E m) (stdChainTheta (F := F) (f := 1) m k h B) =
    stdChainTheta (F := F) (f := 1) m k h B
  rw [MulAut.conj_apply, ← hc, mul_assoc, mul_inv_cancel, mul_one]

private theorem stdConj_chainTheta_fork (m : ℕ) (hm : 3 ≤ m) (B : Su K 2 1 3) :
    (stdConj E m).toMonoidHom
        (stdChainTheta (F := F) (f := 1) m ⟨m - 2, by omega⟩ (by omega : m - 2 + 1 < m) B) =
      stdForkTheta E m hm B := by
  rw [stdForkTheta]
  rfl

private theorem stdConj_forkTheta (m : ℕ) (hm : 3 ≤ m) (B : Su K 2 1 3) :
    (stdConj E m).toMonoidHom (stdForkTheta E m hm B) =
      stdChainTheta (F := F) (f := 1) m ⟨m - 2, by omega⟩ (by omega : m - 2 + 1 < m) B := by
  rw [stdForkTheta, MonoidHom.comp_apply]
  exact stdConj_stdConj E m _


private theorem qTwoForkSwap_lt_iff_of_three (m : ℕ) (hm : 3 ≤ m)
    {i j : Fin (m + 1)}
    (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) :
    i < j ↔ qTwoForkSwap m hm i < qTwoForkSwap m hm j := by
  let a : Fin (m + 1) := ⟨m - 1, by omega⟩
  let b : Fin (m + 1) := Fin.last m
  have hs : qTwoForkSwap m hm = Equiv.swap a b := rfl
  rw [hs]
  have hedge := (qtwoLabel_three_iff hm i j).mp hM
  have hi_lt := i.isLt
  have hj_lt := j.isLt
  have ha_val : (a : ℕ) = m - 1 := rfl
  have hb_val : (b : ℕ) = m := rfl
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    by_cases hja : j = a <;> by_cases hjb : j = b <;>
    simp [Equiv.swap_apply_def, hia, hib, hja, hjb, a, b, ha_val] at hedge ⊢ <;> omega



private theorem qTwoForkSwap_apply_of_ne_val (m : ℕ) (hm : 3 ≤ m) {i : Fin (m + 1)}
    (hi₁ : i.val ≠ m - 1) (hi₂ : i.val ≠ m) :
    qTwoForkSwap m hm i = i := by
  apply qTwoForkSwap_apply_of_ne m hm
  · intro h
    exact hi₁ (by simpa using congrArg Fin.val h)
  · intro h
    exact hi₂ (by simpa using congrArg Fin.val h)

private theorem map_qtwoStdWin_conjTau_of_far (m : ℕ) (len : ℕ) {a : ℕ}
    (ha : a + len ≤ m) :
    ((qtwoStdWin (F := F) (K := K) m a len (by omega)).range.map
        (stdConj E m).toMonoidHom) =
      (qtwoStdWin (F := F) (K := K) m a len (by omega)).range := by
  apply le_antisymm
  · rintro y ⟨x, ⟨A, rfl⟩, rfl⟩
    exact ⟨A, (qtwoStdConj_win E (k := len) ha A).symm⟩
  · rintro y ⟨A, rfl⟩
    refine ⟨qtwoStdWin (F := F) (K := K) m a len (by omega) A, ⟨A, rfl⟩, ?_⟩
    rw [qtwoStdConj_win E (k := len) ha]

private theorem map_map_stdConj_self (m : ℕ)
    (H : Subgroup ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))) :
    (H.map (stdConj E m).toMonoidHom).map (stdConj E m).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have hcomp : (stdConj E m).toMonoidHom.comp (stdConj E m).toMonoidHom =
      MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact stdConj_stdConj E m x
  rw [hcomp, Subgroup.map_id]

private theorem map_qtwoStdW_conjTau_of_lt (m : ℕ) (hm : 3 ≤ m)
    {i j : Fin (m + 1)} (hij : i < j)
    (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) :
    (qtwoStdW E m hm i j).map (stdConj E m).toMonoidHom =
      qtwoStdW E m hm (qTwoForkSwap m hm i) (qTwoForkSwap m hm j) := by
  let s := qTwoForkSwap m hm
  have hedge := (qtwoLabel_three_iff hm i j).mp hM
  by_cases hj : j = Fin.last m
  · subst j
    have hi : i.val = m - 2 := by
      rcases hedge with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        simp only [Fin.val_last] at * <;> omega
    have hsi : s i = i :=
      qTwoForkSwap_apply_of_ne_val m hm (by omega) (by omega)
    have hsj : s (Fin.last m) = (⟨m - 1, by omega⟩ : Fin (m + 1)) :=
      qTwoForkSwap_apply_last m hm
    rw [qtwoStdW_fork E m hm i (Fin.last m) hi rfl, hsi, hsj,
      qtwoStdW_chain E m hm (m - 2) (by omega) i
        (⟨m - 1, by omega⟩ : Fin (m + 1)) hi (by rw [Fin.val_mk]; omega)]
    exact map_map_stdConj_self E m _
  · have hjval_ne : (j : ℕ) ≠ m := by
      intro h
      apply hj
      ext
      simpa using h
    have hji : (j : ℕ) = i.val + 1 := by
      rcases hedge with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have hjle : (j : ℕ) ≤ m - 1 := by
      rcases hedge with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    by_cases hnear : i.val + 2 = m
    · have hi : i.val = m - 2 := by omega
      have hjval : (j : ℕ) = m - 1 := by omega
      have hsi : s i = i :=
        qTwoForkSwap_apply_of_ne_val m hm (by omega) (by omega)
      have hsj : s j = Fin.last m := by
        have hj_eq : j = (⟨m - 1, by omega⟩ : Fin (m + 1)) := Fin.ext hjval
        rw [hj_eq]
        exact qTwoForkSwap_apply_penultimate m hm
      rw [hsi, hsj, qtwoStdW_chain E m hm (m - 2) (by omega) i j hi (by omega),
        qtwoStdW_fork E m hm i (Fin.last m) hi rfl]
    · have hi_far : i.val + 3 ≤ m := by omega
      have hsi : s i = i :=
        qTwoForkSwap_apply_of_ne_val m hm (by omega) (by omega)
      have hsj : s j = j :=
        qTwoForkSwap_apply_of_ne_val m hm (by omega) (by omega)
      rw [hsi, hsj, qtwoStdW_chain E m hm i.val (by omega) i j rfl hji]
      exact map_qtwoStdWin_conjTau_of_far E m 3 hi_far


private theorem map_qtwoStdW_conjTau (m : ℕ) (hm : 3 ≤ m)
    {i j : Fin (m + 1)}
    (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) :
    (qtwoStdW E m hm i j).map (stdConj E m).toMonoidHom =
      qtwoStdW E m hm (qTwoForkSwap m hm i) (qTwoForkSwap m hm j) := by
  by_cases hij : i < j
  · exact map_qtwoStdW_conjTau_of_lt E m hm hij hM
  · have hne : i ≠ j := by
      rintro rfl
      rw [CFSG.StandardType.ggCoxeterMatrixD_apply, if_pos rfl] at hM
      omega
    have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm hne)
    have hM' : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j i = 3 := by
      rw [show CFSG.StandardType.ggCoxeterMatrixD (m + 1) j i =
          CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j from
        ((CFSG.StandardType.ggCoxeterMatrixD (m + 1)).isSymm.apply j i).symm]
      exact hM
    rw [qtwoStdW_symm E m hm i j, qtwoStdW_symm E m hm
      (qTwoForkSwap m hm i) (qTwoForkSwap m hm j)]
    exact map_qtwoStdW_conjTau_of_lt E m hm hji hM'


private theorem map_range_qTwoStdTheta₀ (m : ℕ) (hm : 3 ≤ m) (i j : Fin (m + 1)) :
    (qTwoStdTheta₀ E m hm i j).range.map
        (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) =
      ((stdFamilyV E m hm).θ i j).range := by
  unfold qTwoStdTheta₀
  rw [MonoidHom.map_range]
  rfl

private theorem map_range_qTwoStdTheta_of_three (m : ℕ) (hm : 3 ≤ m)
    {i j : Fin (m + 1)}
    (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) :
    (qTwoStdTheta E m hm i j).range.map
        (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) =
      qtwoStdW E m hm i j := by
  unfold qtwoStdW
  rw [if_pos hM]
  by_cases hij : i < j
  · rw [if_pos hij, qTwoStdTheta, if_pos hij]
    exact map_range_qTwoStdTheta₀ E m hm i j
  · rw [if_neg hij, qTwoStdTheta, if_neg hij]
    rw [MonoidHom.range_comp, Subgroup.map_map,
      MonoidHom.range_eq_top.mpr (revSU3 K 2 1).surjective, Subgroup.map_top,
      ← MonoidHom.map_range]
    exact map_range_qTwoStdTheta₀ E m hm j i


private theorem map_range_qTwoStdIota (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1)) :
    (qTwoStdIota E m hm i).range.map
        (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) =
      qtwoStdU E m hm i := by
  unfold qTwoStdIota qtwoStdU
  rw [MonoidHom.map_range]
  rfl

private theorem map_qtwoStdU_conjTau (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1)) :
    (qtwoStdU E m hm i).map (stdConj E m).toMonoidHom =
      qtwoStdU E m hm (qTwoForkSwap m hm i) := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨k, rfl⟩ | rfl
  · by_cases hk : k.val = m - 1
    · have hk_eq : k = (⟨m - 1, by omega⟩ : Fin m) := Fin.ext hk
      rw [hk_eq, qtwoStdU_castSucc E m hm (⟨m - 1, by omega⟩ : Fin m)]
      have hs : qTwoForkSwap m hm
          (Fin.castSucc (⟨m - 1, by omega⟩ : Fin m)) = Fin.last m := by
        simp
      rw [hs, qtwoStdU_last E m hm]
    · have hk_le : k.val + 2 ≤ m := by omega
      rw [qtwoStdU_castSucc E m hm k]
      have hs : qTwoForkSwap m hm (Fin.castSucc k) = Fin.castSucc k := by
        apply qTwoForkSwap_apply_of_ne_val m hm
        · simpa using (by omega : k.val ≠ m - 1)
        · simpa using (by omega : k.val ≠ m)
      rw [hs, qtwoStdU_castSucc E m hm k]
      exact map_qtwoStdWin_conjTau_of_far E m 2 hk_le
  · rw [qtwoStdU_last E m hm]
    have hs : qTwoForkSwap m hm (Fin.last m) =
        Fin.castSucc (⟨m - 1, by omega⟩ : Fin m) := by
      simp
    rw [hs, qtwoStdU_castSucc E m hm (⟨m - 1, by omega⟩ : Fin m)]
    exact map_map_stdConj_self E m _


private theorem levi_map_subtype (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (C : Set (Fin (m + 1))) :
    ((qTwoStdFamily E hK m hm).levi C).map
        (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) =
      (⨆ i ∈ C, qtwoStdU E m hm i) ⊔
        (⨆ (i ∈ C) (j ∈ C) (_ : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3),
          qtwoStdW E m hm i j) := by
  rw [QTwoPhanFamily.levi, Subgroup.map_sup]
  congr 1
  · simp only [Subgroup.map_iSup, MonoidHom.map_range]
    apply iSup_congr
    intro i
    apply iSup_congr
    intro hi
    change ((Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))).comp
      (qTwoStdIota E m hm i)).range = qtwoStdU E m hm i
    rw [← MonoidHom.map_range]
    exact map_range_qTwoStdIota E m hm i
  · simp only [Subgroup.map_iSup, MonoidHom.map_range]
    apply iSup_congr
    intro i
    apply iSup_congr
    intro hi
    apply iSup_congr
    intro j
    apply iSup_congr
    intro hj
    apply iSup_congr
    intro hij
    change ((Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))).comp
      (qTwoStdTheta E m hm i j)).range = qtwoStdW E m hm i j
    rw [← MonoidHom.map_range]
    exact map_range_qTwoStdTheta_of_three E m hm hij


private theorem map_ambient_levi (m : ℕ) (hm : 3 ≤ m) (C : Set (Fin (m + 1))) :
    ((⨆ i ∈ C, qtwoStdU E m hm i) ⊔
        (⨆ (i ∈ C) (j ∈ C) (_ : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3),
          qtwoStdW E m hm i j)).map (stdConj E m).toMonoidHom =
      (⨆ i ∈ qTwoForkSwap m hm '' C, qtwoStdU E m hm i) ⊔
        (⨆ (i ∈ qTwoForkSwap m hm '' C) (j ∈ qTwoForkSwap m hm '' C)
            (_ : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3),
          qtwoStdW E m hm i j) := by
  rw [Subgroup.map_sup]
  congr 1
  · simp only [Subgroup.map_iSup, map_qtwoStdU_conjTau, iSup_image]
  · simp only [Subgroup.map_iSup, iSup_image, qTwoForkSwap_coxeter]
    apply iSup_congr
    intro i
    apply iSup_congr
    intro hi
    apply iSup_congr
    intro j
    apply iSup_congr
    intro hj
    apply iSup_congr
    intro hij
    rw [map_qtwoStdW_conjTau E m hm hij]


theorem map_qTwoLevi_conjTau (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (C : Set (Fin (m + 1))) :
    ((qTwoStdFamily E hK m hm).levi C).map (conjTau E).toMonoidHom =
      (qTwoStdFamily E hK m hm).levi (qTwoForkSwap m hm '' C) := by
  let S := qTwoStdFamily E hK m hm
  apply Subgroup.map_injective
    (f := Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
    (Subgroup.subtype_injective _)
  have hL : ((S.levi C).map (conjTau E).toMonoidHom).map
        (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) =
      ((S.levi C).map
        (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))).map
        (stdConj E m).toMonoidHom := by
    rw [Subgroup.map_map, subtype_comp_conjTau, ← Subgroup.map_map]
  rw [hL, levi_map_subtype E hK m hm C, map_ambient_levi E m hm C,
    levi_map_subtype E hK m hm (qTwoForkSwap m hm '' C)]

end CFSG.ClassicalInvolution.PhanDn.QTwo
