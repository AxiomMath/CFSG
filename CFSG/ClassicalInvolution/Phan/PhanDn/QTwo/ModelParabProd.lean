module


public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabChain

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabSwap

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabShape


public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabTwoTail

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabTail

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

theorem qTwo_chain_rot_mul_fork_rot (m : ℕ) (hm : 3 ≤ m) :
    stdChainIota (F := F) (f := 1) m ⟨m - 1, by omega⟩
        (rotSU (unitaryInvolution K 2 1)) *
      stdForkIota E m hm (rotSU (unitaryInvolution K 2 1)) =
      tauAt E (⟨m - 1, by omega⟩ : Fin (m + 1)) * tauAt E (Fin.last m) := by
  have hab : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_mk, Fin.val_last] at this
    omega
  have hneg : (-1 : K) = 1 := by
    have htwo : (1 : K) + 1 = 0 := by
      calc (1 : K) + 1 = 2 := by norm_num
           _ = 0 := CharP.cast_eq_zero K 2
    exact neg_eq_of_add_eq_zero_left htwo
  apply LinearEquiv.ext
  intro w
  funext d
  change stdChainIota (F := F) (f := 1) m ⟨m - 1, by omega⟩
    (rotSU (unitaryInvolution K 2 1))
    (stdForkIota E m hm (rotSU (unitaryInvolution K 2 1)) w) d =
      tauAt E (⟨m - 1, by omega⟩ : Fin (m + 1)) (tauAt E (Fin.last m) w) d
  by_cases hda : d = (⟨m - 1, by omega⟩ : Fin (m + 1))
  · subst d
    rw [stdChainIota_apply, blockEmb2_last_smul_zero hm]
    simp [rotSU, rotMat, hneg, stdForkIota_apply_right, tauAt_apply, hab]
  by_cases hdb : d = Fin.last m
  · subst d
    rw [stdChainIota_apply, blockEmb2_last_smul_one hm]
    simp [rotSU, rotMat, hneg, stdForkIota_apply_left, tauAt_apply, Ne.symm hab]
  have hda' : d.val ≠ m - 1 := fun h => hda (Fin.ext h)
  have hdb' : d.val ≠ m := fun h => hdb (Fin.ext h)
  rw [stdChainIota_apply_of_not_mem]
  · rw [stdForkIota_apply_of_not_mem E hm _ _ hda' hdb']
    simp [tauAt_apply, hda, hdb]
  · simp only [Fin.val_mk]
    omega

theorem qTwo_doubleTau_mem_levi (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    {C : Set (Fin (m + 1))}
    (ha : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∈ C) (hb : Fin.last m ∈ C) :
    ∃ l ∈ (qTwoStdFamily E hK m hm).levi C,
      (l : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
        tauAt E (⟨m - 1, by omega⟩ : Fin (m + 1)) * tauAt E (Fin.last m) := by
  let S := qTwoStdFamily E hK m hm
  let a : Fin (m + 1) := ⟨m - 1, by omega⟩
  let r := rotSU (unitaryInvolution K 2 1)
  refine ⟨S.ι a r * S.ι (Fin.last m) r,
    (S.levi C).mul_mem (S.mem_levi_node ha r) (S.mem_levi_node hb r), ?_⟩
  change (stdFamilyV E m hm).ι a r * (stdFamilyV E m hm).ι (Fin.last m) r = _
  have ha' : a = Fin.castSucc (⟨m - 1, by omega⟩ : Fin m) := Fin.ext rfl
  rw [ha', stdFamilyV_ι_castSucc, stdFamilyV_ι_last]
  exact qTwo_chain_rot_mul_fork_rot E m hm

theorem qTwo_fix_last_of_isKLinear {m : ℕ}
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hK : ∀ (a : K) (w : Fin (m + 1) → K),
      (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (a • w) =
        a • (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) w) :
    x • flagChamber E m (Fin.last m) = flagChamber E m (Fin.last m) := by
  apply Subtype.ext
  rw [coe_smul_flagVert, coe_flagChamber, stdDChamber_elt_last_eq_stdLag]
  apply Submodule.eq_of_le_of_finrank_eq
  · exact (map_stdLag_bcLin_le_iff E (m + 1) x).mpr hK
  · rw [bcLin_eq_coe_bc]
    exact (bc E (m + 1) x).finrank_map_eq (stdLag (m + 1) K)

theorem qTwoParab_mem_diff_last_of_isKLinear {m : ℕ} {C : Set (Fin (m + 1))}
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hx : x ∈ qTwoParab E m C)
    (hK : ∀ (a : K) (w : Fin (m + 1) → K),
      (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (a • w) =
        a • (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) w) :
    x ∈ qTwoParab E m (C \ {Fin.last m}) := by
  rw [mem_qTwoParab] at hx ⊢
  intro j hj
  by_cases hlast : j = Fin.last m
  · subst j
    exact qTwo_fix_last_of_isKLinear E hK
  exact hx j (fun hjC => hj ⟨hjC, by simpa using hlast⟩)

theorem qTwoParab_preserves_twoTail_prefix (m : ℕ) (hm : 3 ≤ m)
    {C : Set (Fin (m + 1))}
    (hc : (⟨m - 2, by omega⟩ : Fin (m + 1)) ∉ C)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hx : x ∈ qTwoParab E m C) :
    (coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅ := by
  have h := congrArg Subtype.val ((mem_qTwoParab E).mp hx ⟨m - 2, by omega⟩ hc)
  rw [coe_smul_flagVert, coe_flagChamber] at h
  have hne : (⟨m - 2, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
    intro heq
    have := congrArg Fin.val heq
    simp only [Fin.val_mk, Fin.val_last] at this
    omega
  rw [stdDChamber_elt_eq_sub_coordSpan hne (by simp only [Fin.val_mk]; omega)] at h
  simpa only [Fin.val_mk, show m - 2 + 1 = m - 1 by omega] using h

theorem qTwo_doubleTau_mem_parab (m : ℕ) (hm : 3 ≤ m) {C : Set (Fin (m + 1))}
    (ha : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∈ C) (hb : Fin.last m ∈ C)
    {l : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hl : (l : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      tauAt E (⟨m - 1, by omega⟩ : Fin (m + 1)) * tauAt E (Fin.last m)) :
    l ∈ qTwoParab E m C := by
  have hfix (i k : Fin (m + 1)) (hik : i ≠ k) :
      bc E (m + 1) (tauAt E k) (stdE (K := K) i) = stdE i := by
    ext (j | j)
    · rw [(bc_tauAt E (m + 1) k (stdE i)).1]
      by_cases hj : j = k
      · subst j
        simp [stdE_inl, stdE_inr, hik, Ne.symm hik]
      · simp [stdE_inl, stdE_inr, hj]
    · rw [(bc_tauAt E (m + 1) k (stdE i)).2]
      by_cases hj : j = k
      · subst j
        simp [stdE_inl, stdE_inr, hik, Ne.symm hik]
      · simp [stdE_inl, stdE_inr, hj]
  rw [mem_qTwoParab]
  intro j hj
  have hja : j ≠ (⟨m - 1, by omega⟩ : Fin (m + 1)) := fun h => hj (h.symm ▸ ha)
  have hjb : j ≠ Fin.last m := fun h => hj (h.symm ▸ hb)
  have hjval : j.val ≤ m - 2 := by
    have hlt := j.isLt
    have hna : j.val ≠ m - 1 := fun h => hja (Fin.ext h)
    have hnb : j.val ≠ m := fun h => hjb (Fin.ext h)
    omega
  have hjm : j.val + 1 ≠ m := by omega
  apply Subtype.ext
  rw [coe_smul_flagVert, coe_flagChamber,
    stdDChamber_elt_eq_sub_coordSpan hjb hjm]
  refine map_coordSpan_eq_of_bc E
    (l : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ?_ ?_
  · intro i hi
    have hi' : i.val < j.val + 1 := hi
    have hival : i.val < m - 1 := by omega
    have hia : i ≠ (⟨m - 1, by omega⟩ : Fin (m + 1)) :=
      fun h => (Nat.ne_of_lt hival) (congrArg Fin.val h)
    have hib : i ≠ Fin.last m := by
      have hival' : i.val < m := by omega
      exact fun h => (Nat.ne_of_lt hival') (congrArg Fin.val h)
    rw [hl, map_mul]
    change bc E (m + 1) (tauAt E ⟨m - 1, by omega⟩)
      (bc E (m + 1) (tauAt E (Fin.last m)) (stdE i)) ∈ _
    rw [hfix i (Fin.last m) hib, hfix i ⟨m - 1, by omega⟩ hia]
    exact Submodule.subset_span (Or.inl (Set.mem_image_of_mem _ hi))
  · intro i hi
    exact hi.elim

theorem qTwoParab_prod (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m) {C : Set (Fin (m + 1))}
    (hC : C ∈ qTwoShape (CFSG.StandardType.ggCoxeterMatrixD (m + 1)))
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))} (hx : x ∈ qTwoParab E m C) :
    ∃ t ∈ ⨆ i, qTwoTor E m hm i, ∃ l ∈ (qTwoStdFamily E hK m hm).levi C, x = t * l := by
  classical
  by_cases hb : Fin.last m ∈ C
  swap
  · exact (qTwoParab_prod_of_last_not_mem E hK m hm) hC hb hx
  by_cases ha : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∈ C
  swap
  · have hs : Fin.last m ∉ qTwoForkSwap m hm '' C := by
      rintro ⟨i, hi, heq⟩
      have hi' := congrArg (qTwoForkSwap m hm) heq
      simp only [qTwoForkSwap_apply_apply, qTwoForkSwap_apply_last] at hi'
      exact ha (hi' ▸ hi)
    have hx' : conjTau E x ∈ qTwoParab E m (qTwoForkSwap m hm '' C) := by
      rw [← map_qTwoParab_conjTau E m hm C]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨t', ht', l', hl', hxl⟩ := (qTwoParab_prod_of_last_not_mem E hK m hm) (qTwoShape_forkSwap m hm hC) hs hx'
    rw [← map_qTwoTor_iSup_conjTau E hK m hm] at ht'
    rw [← map_qTwoLevi_conjTau E hK m hm C] at hl'
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ht'
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hl'
    refine ⟨t, ht, l, hl, (conjTau E).injective ?_⟩
    simpa only [MulEquiv.coe_toMonoidHom, map_mul] using hxl
  by_cases hc : (⟨m - 2, by omega⟩ : Fin (m + 1)) ∈ C
  · have htriple := qTwoShape_eq_fork_triple hm hC ha hb hc
    subst C
    have hmin : ∀ i ∈ ({⟨m - 2, by omega⟩, ⟨m - 1, by omega⟩, Fin.last m} : Set (Fin (m + 1))),
        m - 2 ≤ i.val := by
      intro i hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with rfl | rfl | rfl <;> simp only [Fin.val_mk, Fin.val_last] <;> omega
    obtain ⟨t, ht, hfix⟩ := qTwoParab_remove_prefix E hK m hm (m - 2) (by omega) hmin hx
    exact ⟨t, ht, t⁻¹ * x, qTwo_supported_three_mem_levi_fork E hK m hm hfix, by group⟩
  have linear_case {y : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
      (hy : y ∈ qTwoParab E m C)
      (hlin : ∀ (a : K) (w : Fin (m + 1) → K),
        (y : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (a • w) =
          a • (y : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) w) :
      ∃ t ∈ ⨆ i, qTwoTor E m hm i,
        ∃ l ∈ (qTwoStdFamily E hK m hm).levi C, y = t * l := by
    have hsmall := qTwoShape_mono hC (Set.diff_subset (t := {Fin.last m}))
    obtain ⟨t, ht, l, hl, hyl⟩ := (qTwoParab_prod_of_last_not_mem E hK m hm) hsmall (by simp)
      (qTwoParab_mem_diff_last_of_isKLinear E hy hlin)
    exact ⟨t, ht, l, (qTwoStdFamily E hK m hm).levi_mono Set.diff_subset hl, hyl⟩
  rcases qTwo_twoTail_correction E hK m hm (qTwoParab_preserves_twoTail_prefix E m hm hc hx) with hlin | hlin
  · exact linear_case hx hlin
  obtain ⟨d, hdL, hd⟩ := qTwo_doubleTau_mem_levi E hK m hm ha hb
  have hdP := qTwo_doubleTau_mem_parab E m hm ha hb hd
  have hxd : ∀ (a : K) (w : Fin (m + 1) → K),
      ((x * d : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (a • w) =
      a • ((x * d : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) w := by
    simpa only [Subgroup.coe_mul, hd] using hlin
  obtain ⟨t, ht, l, hl, heq⟩ := linear_case ((qTwoParab E m C).mul_mem hx hdP) hxd
  refine ⟨t, ht, l * d⁻¹,
    (qTwoStdFamily E hK m hm).levi C |>.mul_mem hl ((qTwoStdFamily E hK m hm).levi C |>.inv_mem hdL), ?_⟩
  calc x = (x * d) * d⁻¹ := by group
       _ = t * (l * d⁻¹) := by rw [heq, mul_assoc]

end CFSG.ClassicalInvolution.PhanDn.QTwo
