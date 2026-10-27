module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Four
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8TwoLow

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley CFSG.LieType.CurtisTits
  CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.RankThree.Classical2
open scoped MatrixGroups

@[expose] noncomputable def spinDerivedHom (K : Type) [Field K] :
    spinGroup (quadPlus 8 K) →* ↥(orthDerived (quadPlus 8 K)) :=
  (spinAction (quadPlus 8 K)).codRestrict _ fun x => by
    show spinAction (quadPlus 8 K) x ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 8 K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 8 K)⁆
    exact (range_spinAction_quadPlus_eq_commutator (K := K) (n := 8) (by norm_num)) ▸
      MonoidHom.mem_range.mpr ⟨x, rfl⟩

theorem coe_spinDerivedHom (K : Type) [Field K] (x : spinGroup (quadPlus 8 K)) :
    ↑(spinDerivedHom K x) = spinAction (quadPlus 8 K) x := by
  rw [spinDerivedHom, MonoidHom.codRestrict_apply]

theorem spinDerivedHom_ker (K : Type) [Field K] :
    (spinDerivedHom K).ker = (spinAction (quadPlus 8 K)).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff, coe_spinDerivedHom, Subgroup.coe_one]

theorem spinDerivedHom_injective (K : Type) [Field K] [Finite K] [CharP K 2] :
    Function.Injective (spinDerivedHom K) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : x ∈ (spinAction (quadPlus 8 K)).ker := by
    rw [← spinDerivedHom_ker]; exact hx
  have hbot : (spinAction (quadPlus 8 K)).ker = ⊥ := by
    haveI := isCentral_cliffordAlgebra_quadPlus K 8
    exact ker_spinAction_eq_bot_of_isCentral _ (CharP.cast_eq_zero K 2)
  rw [hbot, Subgroup.mem_bot] at hx'
  exact hx'

theorem spinDerivedHom_surjective (K : Type) [Field K] :
    Function.Surjective (spinDerivedHom K) := by
  intro y
  have hy : (y : (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) ∈
      (spinAction (quadPlus 8 K)).range := by
    rw [range_spinAction_quadPlus_eq_commutator (n := 8) (by norm_num)]
    exact y.2
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, Subtype.ext ?_⟩
  rw [coe_spinDerivedHom]
  exact hx

@[expose] noncomputable def spinDerivedEquiv (K : Type) [Field K] [Finite K] [CharP K 2] :
    spinGroup (quadPlus 8 K) ≃* ↥(orthDerived (quadPlus 8 K)) where
  toFun := spinDerivedHom K
  invFun y := Classical.choose (spinDerivedHom_surjective K y)
  left_inv x := spinDerivedHom_injective K (Classical.choose_spec (spinDerivedHom_surjective K _))
  right_inv y := Classical.choose_spec (spinDerivedHom_surjective K y)
  map_mul' := map_mul _

theorem coe_spinDerivedEquiv (K : Type) [Field K] [Finite K] [CharP K 2]
    (x : spinGroup (quadPlus 8 K)) :
    ↑(spinDerivedEquiv K x) = spinAction (quadPlus 8 K) x :=
  coe_spinDerivedHom K x

theorem center_le_ker_spinAction_quadPlus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) :
    Subgroup.center (spinGroup (quadPlus n K)) ≤ (spinAction (quadPlus n K)).ker := by
  intro x hx
  have hcomap := center_le_comap_statedScalars (quadPlus n K) (range_spinMatrix_quadPlus hn)
    (center_statedOmega_quadPlus hn) hx
  rw [Subgroup.mem_comap, CFSG.ClassicalGroups.Orthogonal.mem_statedScalars_iff,
    toLinEquiv_spinMatrix] at hcomap
  obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Orthogonal.mem_scalars.mp hcomap
  obtain ⟨v₀, hv₀⟩ := exists_map_ne_zero_of_hypPair (quadPlus n K)
    (CFSG.ClassicalGroups.Orthogonal.plusPair K (⟨0, by omega⟩ : Fin n))
  have hc2 : c * c = 1 := by
    have h := map_spinAction (quadPlus n K) x v₀
    rw [hc, CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq] at h
    have h' : (c ^ 2 - 1) * quadPlus n K v₀ = 0 := by rw [sub_mul, h, one_mul, sub_self]
    have h2 := (mul_eq_zero.mp h').resolve_right hv₀
    rw [pow_two] at h2
    exact sub_eq_zero.mp h2
  have h1 : (-1 : K) = 1 := neg_one_eq_one_iff.mpr (by rw [ringChar.eq K 2])
  rcases mul_self_eq_one_iff.mp hc2 with rfl | hneg
  · rw [MonoidHom.mem_ker]
    refine LinearEquiv.ext fun v => ?_
    rw [hc v, one_smul]
    rfl
  · rw [MonoidHom.mem_ker]
    refine LinearEquiv.ext fun v => ?_
    rw [hc v, hneg, h1, one_smul]
    rfl

@[expose] noncomputable def e8D8SpinHom (K : Type) [Field K] [Finite K] :
    spinGroup (quadPlus 8 K) →* adjointGroup .E8 K :=
  (exists_psi_D8_param K (by norm_num)).choose

theorem e8D8SpinHom_ker (K : Type) [Field K] [Finite K] :
    (e8D8SpinHom K).ker ≤ Subgroup.center (spinGroup (quadPlus 8 K)) :=
  (exists_psi_D8_param K (by norm_num)).choose_spec.1

theorem e8D8SpinHom_range (K : Type) [Field K] [Finite K] :
    (e8D8SpinHom K).range = ⨆ k, e8D8Chain K k :=
  (exists_psi_D8_param K (by norm_num)).choose_spec.2.1

theorem e8D8SpinHom_rankOne (K : Type) [Field K] [Finite K] (k : Fin 8) :
    ((CurtisTits.rankOne (plusDatum 8 K (by norm_num)).rootGroup k).map (e8D8SpinHom K)) =
      e8D8Chain K k :=
  (exists_psi_D8_param K (by norm_num)).choose_spec.2.2.1 k

theorem e8D8SpinHom_weylD (K : Type) [Field K] [Finite K] {k : Fin 8} (hk : k ≠ 0) :
    e8D8SpinHom K (weylD K (by norm_num) k) =
      weylElement .E8 K (e8D8Node k) :=
  (exists_psi_D8_param K (by norm_num)).choose_spec.2.2.2 k hk

theorem e8D8SpinHom_injective (K : Type) [Field K] [Finite K] [CharP K 2] :
    Function.Injective (e8D8SpinHom K) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : x ∈ Subgroup.center (spinGroup (quadPlus 8 K)) :=
    e8D8SpinHom_ker K (MonoidHom.mem_ker.mpr hx)
  have h2 := center_le_ker_spinAction_quadPlus (K := K) (by norm_num) h1
  have hbot : (spinAction (quadPlus 8 K)).ker = ⊥ := by
    haveI := isCentral_cliffordAlgebra_quadPlus K 8
    exact ker_spinAction_eq_bot_of_isCentral _ (CharP.cast_eq_zero K 2)
  rw [hbot, Subgroup.mem_bot] at h2
  exact h2

@[expose] noncomputable def e8D8ChainHom (K : Type) [Field K] [Finite K] :
    spinGroup (quadPlus 8 K) →* ↥(⨆ k, e8D8Chain K k) :=
  (e8D8SpinHom K).codRestrict _ fun x => by
    rw [← e8D8SpinHom_range]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩

theorem coe_e8D8ChainHom (K : Type) [Field K] [Finite K] (x : spinGroup (quadPlus 8 K)) :
    ↑(e8D8ChainHom K x) = e8D8SpinHom K x := by
  rw [e8D8ChainHom, MonoidHom.codRestrict_apply]

theorem e8D8ChainHom_injective (K : Type) [Field K] [Finite K] [CharP K 2] :
    Function.Injective (e8D8ChainHom K) := fun _ _ h =>
  e8D8SpinHom_injective K
    (by rw [← coe_e8D8ChainHom, ← coe_e8D8ChainHom]; exact congrArg Subtype.val h)

theorem e8D8ChainHom_surjective (K : Type) [Field K] [Finite K] :
    Function.Surjective (e8D8ChainHom K) := by
  intro y
  have hy : (y : adjointGroup .E8 K) ∈ (e8D8SpinHom K).range := by
    rw [e8D8SpinHom_range]; exact y.2
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
  exact ⟨x, Subtype.ext (by rw [coe_e8D8ChainHom]; exact hx)⟩

@[expose] noncomputable def e8D8Equiv (K : Type) [Field K] [Finite K] [CharP K 2] :
    spinGroup (quadPlus 8 K) ≃* ↥(⨆ k, e8D8Chain K k) where
  toFun := e8D8ChainHom K
  invFun y := Classical.choose (e8D8ChainHom_surjective K y)
  left_inv x := e8D8ChainHom_injective K (Classical.choose_spec (e8D8ChainHom_surjective K _))
  right_inv y := Classical.choose_spec (e8D8ChainHom_surjective K y)
  map_mul' := map_mul _

theorem coe_e8D8Equiv (K : Type) [Field K] [Finite K] [CharP K 2]
    (x : spinGroup (quadPlus 8 K)) :
    ↑(e8D8Equiv K x) = e8D8SpinHom K x :=
  coe_e8D8ChainHom K x

@[expose] noncomputable def e8D8Theta (K : Type) [Field K] [Finite K] [CharP K 2] :
    ↥(⨆ k, e8D8Chain K k) ≃* ↥(orthDerived (quadPlus 8 K)) :=
  (e8D8Equiv K).symm.trans (spinDerivedEquiv K)

theorem e8D8Theta_e8D8Equiv (K : Type) [Field K] [Finite K] [CharP K 2]
    (x : spinGroup (quadPlus 8 K)) :
    e8D8Theta K (e8D8Equiv K x) = spinDerivedEquiv K x := by
  rw [e8D8Theta, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

theorem coe_e8D8Theta_e8D8Equiv (K : Type) [Field K] [Finite K] [CharP K 2]
    (x : spinGroup (quadPlus 8 K)) (v : Fin 8 ⊕ Fin 8 → K) :
    ((e8D8Theta K (e8D8Equiv K x) : ↥(orthDerived (quadPlus 8 K))) :
      (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) v = spinAction (quadPlus 8 K) x v := by
  rw [e8D8Theta_e8D8Equiv K x, coe_spinDerivedEquiv]

@[expose] def e8SpinW2 (K : Type) [Field K] : Submodule K (Fin 8 ⊕ Fin 8 → K) where
  carrier := {v | ∀ m : Fin 8, 4 ≤ (m : ℕ) → v (.inl m) = 0 ∧ v (.inr m) = 0}
  add_mem' := by
    intro a b ha hb m hm
    exact ⟨by rw [Pi.add_apply, ha m hm |>.1, hb m hm |>.1, add_zero],
      by rw [Pi.add_apply, ha m hm |>.2, hb m hm |>.2, add_zero]⟩
  zero_mem' := by intro m _; exact ⟨rfl, rfl⟩
  smul_mem' := by
    intro c a ha m hm
    exact ⟨by rw [Pi.smul_apply, ha m hm |>.1, smul_zero],
      by rw [Pi.smul_apply, ha m hm |>.2, smul_zero]⟩

@[expose] def e8SpinW1 (K : Type) [Field K] : Submodule K (Fin 8 ⊕ Fin 8 → K) where
  carrier := {v | ∀ m : Fin 8, (m : ℕ) < 4 → v (.inl m) = 0 ∧ v (.inr m) = 0}
  add_mem' := by
    intro a b ha hb m hm
    exact ⟨by rw [Pi.add_apply, ha m hm |>.1, hb m hm |>.1, add_zero],
      by rw [Pi.add_apply, ha m hm |>.2, hb m hm |>.2, add_zero]⟩
  zero_mem' := by intro m _; exact ⟨rfl, rfl⟩
  smul_mem' := by
    intro c a ha m hm
    exact ⟨by rw [Pi.smul_apply, ha m hm |>.1, smul_zero],
      by rw [Pi.smul_apply, ha m hm |>.2, smul_zero]⟩

theorem mem_e8SpinW2 {K : Type} [Field K] {v : Fin 8 ⊕ Fin 8 → K} :
    v ∈ e8SpinW2 K ↔ ∀ m : Fin 8, 4 ≤ (m : ℕ) → v (.inl m) = 0 ∧ v (.inr m) = 0 :=
  Iff.rfl

theorem mem_e8SpinW1 {K : Type} [Field K] {v : Fin 8 ⊕ Fin 8 → K} :
    v ∈ e8SpinW1 K ↔ ∀ m : Fin 8, (m : ℕ) < 4 → v (.inl m) = 0 ∧ v (.inr m) = 0 :=
  Iff.rfl

private theorem polar_plusVec_eq_zero_of_mem_W2 {K : Type} [Field K] {v : Fin 8 ⊕ Fin 8 → K}
    (hv : v ∈ e8SpinW2 K) {m : Fin 8} (hm : 4 ≤ (m : ℕ)) (s : Bool) :
    QuadraticMap.polar (⇑(quadPlus 8 K)) v ((plusFrame 8 K (by norm_num)).vec m s) = 0 := by
  rw [plusFrame_vec]
  cases s
  · rw [plusVec_false, polar_quadPlus_single_inr]
    exact (mem_e8SpinW2.mp hv m hm).1
  · rw [plusVec_true, polar_quadPlus_single_inl]
    exact (mem_e8SpinW2.mp hv m hm).2

private theorem polar_plusVec_eq_zero_of_mem_W1 {K : Type} [Field K] {v : Fin 8 ⊕ Fin 8 → K}
    (hv : v ∈ e8SpinW1 K) {m : Fin 8} (hm : (m : ℕ) < 4) (s : Bool) :
    QuadraticMap.polar (⇑(quadPlus 8 K)) v ((plusFrame 8 K (by norm_num)).vec m s) = 0 := by
  rw [plusFrame_vec]
  cases s
  · rw [plusVec_false, polar_quadPlus_single_inr]
    exact (mem_e8SpinW1.mp hv m hm).1
  · rw [plusVec_true, polar_quadPlus_single_inl]
    exact (mem_e8SpinW1.mp hv m hm).2

theorem spinAction_longRoot_fixes_W2 {K : Type} [Field K] {i j : Fin 8} (hij : i ≠ j)
    (hi : 4 ≤ (i : ℕ)) (hj : 4 ≤ (j : ℕ)) (s t : Bool) (c : K) {v : Fin 8 ⊕ Fin 8 → K}
    (hv : v ∈ e8SpinW2 K) :
    spinAction (quadPlus 8 K) ((plusFrame 8 K (by norm_num)).longRoot hij s t
      (Multiplicative.ofAdd c)) v = v := by
  rw [HypFrame.spinAction_longRoot_eq_eichler]
  refine CFSG.ClassicalGroups.Orthogonal.eichler_apply_of_polar_eq_zero
    (polar_plusVec_eq_zero_of_mem_W2 hv hj t) ?_
  rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
    polar_plusVec_eq_zero_of_mem_W2 hv hi s, mul_zero]

theorem spinAction_longRoot_fixes_W1 {K : Type} [Field K] {i j : Fin 8} (hij : i ≠ j)
    (hi : (i : ℕ) < 4) (hj : (j : ℕ) < 4) (s t : Bool) (c : K) {v : Fin 8 ⊕ Fin 8 → K}
    (hv : v ∈ e8SpinW1 K) :
    spinAction (quadPlus 8 K) ((plusFrame 8 K (by norm_num)).longRoot hij s t
      (Multiplicative.ofAdd c)) v = v := by
  rw [HypFrame.spinAction_longRoot_eq_eichler]
  refine CFSG.ClassicalGroups.Orthogonal.eichler_apply_of_polar_eq_zero
    (polar_plusVec_eq_zero_of_mem_W1 hv hj t) ?_
  rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
    polar_plusVec_eq_zero_of_mem_W1 hv hi s, mul_zero]

private def spinFixW2 (K : Type) [Field K] : Subgroup (spinGroup (quadPlus 8 K)) where
  carrier := {g | ∀ v ∈ e8SpinW2 K, spinAction (quadPlus 8 K) g v = v}
  one_mem' := by intro v _; rw [map_one]; rfl
  mul_mem' := by
    intro a b ha hb v hv
    rw [map_mul, LinearEquiv.mul_apply, hb v hv, ha v hv]
  inv_mem' := by
    intro a ha v hv
    have h1 : spinAction (quadPlus 8 K) a (spinAction (quadPlus 8 K) a⁻¹ v) = v := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    exact (spinAction (quadPlus 8 K) a).injective (h1.trans (ha v hv).symm)

private theorem four_le_rootIdxD {k : Fin 8} (hk : 4 ≤ (k : ℕ)) : 4 ≤ (rootIdxD 8 k : ℕ) := by
  unfold rootIdxD
  split_ifs with h
  · exact hk
  · simp

private theorem four_le_rootIdxD' {k : Fin 8} (hk : 4 ≤ (k : ℕ)) : 4 ≤ (rootIdxD' 8 k : ℕ) := by
  unfold rootIdxD'
  split_ifs with h
  · simp only [Fin.val_mk]; omega
  · simp

private theorem rootD_mem_spinFixW2 {K : Type} [Field K] {k : Fin 8} (hk : 4 ≤ (k : ℕ))
    (c : Multiplicative K) :
    rootD (n := 8) K (by norm_num) k c ∈ spinFixW2 K := by
  intro v hv
  exact spinAction_longRoot_fixes_W2 (K := K) (rootIdxD_ne 8 (by omega) k) (four_le_rootIdxD hk)
    (four_le_rootIdxD' hk) true (rootSignD 8 k) (Multiplicative.toAdd c) hv

private theorem negRootD_mem_spinFixW2 {K : Type} [Field K] {k : Fin 8} (hk : 4 ≤ (k : ℕ))
    (c : Multiplicative K) :
    negRootD (n := 8) K (by norm_num) k c ∈ spinFixW2 K := by
  intro v hv
  exact spinAction_longRoot_fixes_W2 (K := K) (rootIdxD_ne 8 (by omega) k).symm
    (four_le_rootIdxD' hk) (four_le_rootIdxD hk) (!rootSignD 8 k) false (Multiplicative.toAdd c) hv

private theorem plusRootGroup_single_le_spinFixW2 {K : Type} [Field K] {k : Fin 8}
    (hk : 4 ≤ (k : ℕ)) :
    plusRootGroup 8 K (by norm_num) (Pi.single k 1) ≤ spinFixW2 K := by
  rw [plusRootGroup_single (by norm_num) k]
  rintro _ ⟨c, rfl⟩
  exact rootD_mem_spinFixW2 hk c

private theorem plusRootGroup_neg_single_le_spinFixW2 {K : Type} [Field K] {k : Fin 8}
    (hk : 4 ≤ (k : ℕ)) :
    plusRootGroup 8 K (by norm_num) (-Pi.single k 1) ≤ spinFixW2 K := by
  rw [plusRootGroup_neg_single (by norm_num) k]
  rintro _ ⟨c, rfl⟩
  exact negRootD_mem_spinFixW2 hk c

private theorem rankOne_le_spinFixW2 {K : Type} [Field K] {k : Fin 8} (hk : 4 ≤ (k : ℕ)) :
    CurtisTits.rankOne (plusDatum 8 K (by norm_num)).rootGroup k ≤ spinFixW2 K :=
  sup_le (plusRootGroup_single_le_spinFixW2 hk) (plusRootGroup_neg_single_le_spinFixW2 hk)

theorem e8D4Levi_le_e8D8Chain (K : Type) [Field K] :
    e8D4Levi K ≤ ⨆ k, e8D8Chain K k :=
  iSup_le fun j => le_iSup (fun k : Fin 8 => e8D8Chain K k) (Fin.natAdd 4 j)

private theorem four_le_val_natAdd (j : Fin 4) : 4 ≤ ((Fin.natAdd 4 j : Fin 8) : ℕ) := by
  simp [Fin.natAdd]

private theorem iSup_rankOne_le_spinFixW2 (K : Type) [Field K] :
    (⨆ j : Fin 4, CurtisTits.rankOne (plusDatum 8 K (by norm_num)).rootGroup
      (Fin.natAdd 4 j)) ≤ spinFixW2 K :=
  iSup_le fun j => rankOne_le_spinFixW2 (four_le_val_natAdd j)

theorem e8D4Levi_eq_map_rankOne (K : Type) [Field K] [Finite K] :
    e8D4Levi K = (⨆ j : Fin 4, CurtisTits.rankOne (plusDatum 8 K (by norm_num)).rootGroup
      (Fin.natAdd 4 j)).map (e8D8SpinHom K) := by
  unfold e8D4Levi
  rw [Subgroup.map_iSup]
  exact iSup_congr fun j => (e8D8SpinHom_rankOne K (Fin.natAdd 4 j)).symm

theorem e8D4Levi_fixes_e8SpinW2 (K : Type) [Field K] [Finite K] [CharP K 2]
    {y : ↥(⨆ k, e8D8Chain K k)} (hy : (y : adjointGroup .E8 K) ∈ e8D4Levi K)
    {v : Fin 8 ⊕ Fin 8 → K} (hv : v ∈ e8SpinW2 K) :
    ((e8D8Theta K y : ↥(orthDerived (quadPlus 8 K))) :
      (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) v = v := by
  have hx' : (y : adjointGroup .E8 K) ∈
      (⨆ j : Fin 4, CurtisTits.rankOne (plusDatum 8 K (by norm_num)).rootGroup
        (Fin.natAdd 4 j)).map (e8D8SpinHom K) := by
    rw [← e8D4Levi_eq_map_rankOne K]
    exact hy
  obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hx'
  have hwfix : w ∈ spinFixW2 K := iSup_rankOne_le_spinFixW2 K hw
  have hsub : y = e8D8Equiv K w := Subtype.ext (by rw [coe_e8D8Equiv]; exact hwy.symm)
  rw [hsub, coe_e8D8Theta_e8D8Equiv]
  exact hwfix v hv

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin
