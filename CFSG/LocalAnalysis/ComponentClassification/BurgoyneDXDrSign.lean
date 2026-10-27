module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrBlockA
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcT1

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Dr

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C (blockP blockP_cases SplitP projBlock omegaI
  blockP_eq_projBlock projBlock_le_blockP oBlock_le_matrixDerived projH_injOn_oBlock)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat compInd)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem false_of_sign [Finite K] (hK : ringChar K ≠ 2) {d : ℕ} {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0)
    {M : Subgroup (GL (Fin d) K)} (hd : ExcData (diagGL hw) M) {J : Finset (Fin d)}
    (hJ : J.Nonempty) (hJc : Jᶜ.Nonempty)
    (hNF : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I)
    (hfix : ∀ X ∈ M, X * signGL K J = signGL K J * X)
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ (diagGL hw)))).map
      (projH _)).subgroupOf (autFixed (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))))
    {A : GL (Fin d) K} {a₀ : K} (ha₀ : a₀ ≠ 0)
    (hA2 : (A : Matrix (Fin d) (Fin d) K) * A = a₀ • 1)
    (hAR : (A : Matrix (Fin d) (Fin d) K)ᵀ * diagonal w = -(diagonal w * A))
    (hAM' : ∀ X ∈ M, A⁻¹ * X * A ∈ M)
    (hAS : A * signGL K J = signGL K J * A ∨
      (A : Matrix (Fin d) (Fin d) K) * signMat K J = -(signMat K J * A)) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨I, hI, hMO, hAc, hcard, hIc⟩ :=
    exists_block_of_sign hK hw hd hJ hJc hfix hQc ha₀ hA2 hAR hAM' hAS
  set H := matrixDerived (oQ (diagGL hw)) with hH
  set Qb := (M.subgroupOf H).map (projH H) with hQb
  obtain ⟨u₁, hu₁, -, -, -, -, n₁, -, -, -⟩ := hd.klein
  have hQP : Qb ≤ blockP K hw I :=
    map_mono fun g hg => mem_subgroupOf.2 (hMO (mem_subgroupOf.1 hg))
  have hPs : blockP K hw I ≤ autFixed (oκ _ (sgnPair h2 hw J)) :=
    blockP_le_autFixed h2 hw J I hI
  have hQc' := C.isPComponent_subgroupOf_of_le hQP hPs hQc
  have hinj : ∀ m m' : H, (m : GL (Fin d) K) ∈ M → (m' : GL (Fin d) K) ∈ M →
      projH H m = projH H m' → m = m' := by
    intro m m' hm hm' h
    have h1 : projH H (m⁻¹ * m') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have hmem : m⁻¹ * m' ∈ (oBlock K hw I).subgroupOf H :=
      mem_subgroupOf.2 (mul_mem (inv_mem (hMO hm)) (hMO hm'))
    exact inv_mul_eq_one.1 (projH_injOn_oBlock hw hIc hmem h1)
  rcases blockP_cases hw hK I hIc with hsol | hqs |
      ⟨-, -, L₁, L₂, hsup, hL₁, hL₂, hn₁, hn₂, hq₁, hq₂, ⟨f₁⟩, ⟨f₂⟩⟩
  · exact C.not_le_of_isSolvable hQP hQc' hsol hQP
  ·
    have heq := C.eq_of_le_of_isQuasisimple hQP le_rfl hQc' hqs
    have hOM : oBlock K hw I ≤ M := by
      intro g hg
      have hgH := oBlock_le_matrixDerived hw h2 I hg
      have hgP : projH H ⟨g, hgH⟩ ∈ Qb := by
        rw [heq]
        exact ⟨⟨g, hgH⟩, mem_subgroupOf.2 hg, rfl⟩
      obtain ⟨m, hm, hmg⟩ := hgP
      have hm' := mem_subgroupOf.1 hm
      have h1 : projH H (m⁻¹ * ⟨g, hgH⟩) = 1 := by rw [map_mul, map_inv, hmg, inv_mul_cancel]
      have hmem : m⁻¹ * ⟨g, hgH⟩ ∈ (oBlock K hw I).subgroupOf H :=
        mem_subgroupOf.2 (mul_mem (inv_mem (hMO hm')) hg)
      have h4 := congrArg Subtype.val (inv_mul_eq_one.1 (projH_injOn_oBlock hw hIc hmem h1))
      change (m : GL (Fin d) K) = g at h4
      rw [← h4]
      exact hm'
    obtain ⟨I₀, hI₀, hI₀3, hI₀w, hns⟩ := hNF I hI (by omega)
    have hdiff : (I \ I₀).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      rw [Finset.mem_sdiff] at hx hy
      exact hns x hx.1 y hy.1 hx.2 hy.2
    have hI₀c : (I \ I₀).card = I.card - I₀.card := Finset.card_sdiff_of_subset hI₀
    have hI₀le : I₀.card ≤ I.card := Finset.card_le_card hI₀
    obtain ⟨T, hT4, hTO⟩ : ∃ T : Finset (Fin d), T.card = 4 ∧ signGL K T ∈ oBlock K hw I := by
      by_cases hI₀4 : 4 ≤ I₀.card
      · obtain ⟨T, hTI₀, hT⟩ := Finset.exists_subset_card_eq hI₀4
        exact ⟨T, hT, signGL_mem_oBlock_of_even hw hI₀ hI₀w 2 T hTI₀ (by omega)⟩
      ·
        have h4 : I.card = 4 := by omega
        obtain ⟨e, he⟩ : ∃ e, I \ I₀ = {e} := Finset.card_eq_one.1 (by omega)
        have heI : e ∈ I := (Finset.mem_sdiff.1 (he ▸ Finset.mem_singleton_self e)).1
        have heI₀ : e ∉ I₀ := (Finset.mem_sdiff.1 (he ▸ Finset.mem_singleton_self e)).2
        obtain ⟨a, ha⟩ : I₀.Nonempty := Finset.card_pos.1 (by omega)
        have hae : a ≠ e := fun h => heI₀ (h ▸ ha)
        have hIeq : I = insert e I₀ := by
          ext x
          rw [Finset.mem_insert]
          constructor
          · intro hx
            by_cases hx0 : x ∈ I₀
            · exact Or.inr hx0
            · left
              have : x ∈ I \ I₀ := Finset.mem_sdiff.2 ⟨hx, hx0⟩
              rw [he] at this
              exact Finset.mem_singleton.1 this
          · rintro (rfl | hx)
            · exact heI
            · exact hI₀ hx
        have hprod : ∏ i ∈ I, w i = w a ^ 3 * w e := by
          rw [hIeq, Finset.prod_insert heI₀,
            Finset.prod_congr rfl (fun i hi => hI₀w i hi a ha), Finset.prod_const]
          rw [show I₀.card = 3 by omega]
          ring
        have hsq := isSquare_prod_of_skew hK hw h4 hAc hAR ha₀ hA2
        rw [hprod] at hsq
        obtain ⟨t, ht⟩ := hsq
        have hwa := hw a
        have hwe := hw e
        have ht0 : t ≠ 0 := by
          rintro rfl
          rw [mul_zero] at ht
          exact mul_ne_zero (pow_ne_zero _ hwa) hwe ht
        have hr0 : t / w a ^ 2 ≠ 0 := div_ne_zero ht0 (pow_ne_zero _ hwa)
        have hwr : w e = (t / w a ^ 2) ^ 2 * w a := by
          field_simp
          linear_combination ht
        have hpair := signGL_pair_mem_oBlock_sq hw (hI₀ ha) heI hae hr0 hwr
        have hrest := signGL_mem_oBlock_of_even hw hI₀ hI₀w 1 (I₀.erase a)
          (Finset.erase_subset _ _) (by rw [Finset.card_erase_of_mem ha]; omega)
        have hdisj : Disjoint ({a, e} : Finset (Fin d)) (I₀.erase a) := by
          rw [Finset.disjoint_left]
          intro x hx hx'
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact (Finset.mem_erase.1 hx').1 rfl
          · exact heI₀ (Finset.mem_of_mem_erase hx')
        refine ⟨{a, e} ∪ I₀.erase a, ?_, ?_⟩
        · rw [Finset.card_union_of_disjoint hdisj, Finset.card_pair hae,
            Finset.card_erase_of_mem ha]
          omega
        · have hmul : signGL K ({a, e} ∪ I₀.erase a) = signGL K {a, e} * signGL K (I₀.erase a) := by
            apply Units.ext
            rw [Units.val_mul, coe_signGL, coe_signGL, coe_signGL, signMat_mul_of_disjoint hdisj]
          rw [hmul]
          exact mul_mem hpair hrest
    have hTM := hOM hTO
    have hTT : signGL K T * signGL K T = 1 := Units.ext (PSL.signMat_mul_self T)
    have hT1 : signGL K T ≠ 1 := by
      intro h
      obtain ⟨t, ht⟩ : T.Nonempty := by
        rw [← Finset.card_pos]
        omega
      have e := congrArg (fun B : GL (Fin d) K => (B : Matrix (Fin d) (Fin d) K) t t) h
      simp only [coe_signGL, Units.val_one, signMat, diagonal_apply_eq, one_apply_eq, ht,
        ↓reduceIte] at e
      exact h2 (by linear_combination -e)
    have hpar := hd.par _ hTM hTT hT1
    rw [coe_signGL, finrank_negE_signMat h2, hT4] at hpar
    norm_num at hpar
  ·
    have hle₁ := projBlock_le_blockP hw I hL₁
    have hle₂ := projBlock_le_blockP hw I hL₂
    have hs₁ := (normal_projBlock hw I hL₁ hn₁).isSubnormal
    have hs₂ := (normal_projBlock hw I hL₂ hn₂).isSubnormal
    have hQle : Qb ≤ projBlock hw I L₁ ⊔ projBlock hw I L₂ := hsup ▸ hQP
    obtain ⟨N, hQN, ⟨f⟩⟩ : ∃ N : Subgroup (StatedProj H), Qb = N ∧ Nonempty (N ≃* SL(2, K)) := by
      rcases C.le_or_le_of_le_sup hQP hQc' hle₁ hle₂ hs₁ hs₂ hQle with h | h
      · exact ⟨_, C.eq_of_le_of_isQuasisimple h hle₁ hQc' hq₁, ⟨f₁⟩⟩
      · exact ⟨_, C.eq_of_le_of_isQuasisimple h hle₂ hQc' hq₂, ⟨f₂⟩⟩
    have hne : (-1 : SL(2, K)) ≠ 1 := by
      intro h
      have e := congrFun (congrFun (congrArg Subtype.val h) 0) 0
      simp at e
      exact h2 (by linear_combination -e)
    have hcen : ∀ y : SL(2, K), y * -1 = -1 * y := fun y => by
      ext i j
      simp
    have hsq1 : (-1 : SL(2, K)) * -1 = 1 := by
      ext i j
      simp
    have hzbQ : ((f.symm (-1) : N) : StatedProj H) ∈ Qb := by rw [hQN]; exact (f.symm (-1)).2
    obtain ⟨m, hm, hmz⟩ := hzbQ
    have hmM := mem_subgroupOf.1 hm
    have hzc : ∀ x : H, (x : GL (Fin d) K) ∈ M → projH H x * projH H m = projH H m * projH H x := by
      intro x hx
      have hxN : projH H x ∈ N := by rw [← hQN]; exact ⟨x, mem_subgroupOf.2 hx, rfl⟩
      rw [hmz]
      have := congrArg Subtype.val (show (⟨projH H x, hxN⟩ : N) * f.symm (-1) =
          f.symm (-1) * ⟨projH H x, hxN⟩ from by
        apply f.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hcen])
      exact this
    have hcomm : ∀ x ∈ M, x * (m : GL (Fin d) K) = m * x := by
      intro x hx
      have hxH := hd.le hx
      have h := hinj (⟨x, hxH⟩ * m) (m * ⟨x, hxH⟩) (mul_mem hx hmM) (mul_mem hmM hx)
        (by rw [map_mul, map_mul]; exact hzc ⟨x, hxH⟩ hx)
      exact congrArg Subtype.val h
    have hmm : (m : GL (Fin d) K) * m = 1 := by
      have h := hinj (m * m) 1 (mul_mem hmM hmM) (one_mem M) (by
        rw [map_mul, map_one, hmz, ← Subgroup.coe_mul, ← map_mul, hsq1, map_one]
        rfl)
      exact congrArg Subtype.val h
    have hm1 : (m : GL (Fin d) K) ≠ 1 := by
      intro h
      have h' : m = 1 := Subtype.ext h
      rw [h', map_one] at hmz
      have := congrArg f (Subtype.ext hmz.symm : f.symm (-1) = 1)
      rw [MulEquiv.apply_symm_apply, map_one] at this
      exact hne this
    have hNz : zpowers (m : GL (Fin d) K) = M := by
      refine hd.normal _ (zpowers_le.2 hmM) ⟨fun a ha b => ?_⟩ ⟨m, mem_zpowers _, hmm, hm1⟩
      rw [mem_subgroupOf] at ha ⊢
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ha
      change (b : GL (Fin d) K) * a * (b : GL (Fin d) K)⁻¹ ∈ zpowers (m : GL (Fin d) K)
      have hbm : Commute (b : GL (Fin d) K) (m : GL (Fin d) K) := hcomm b b.2
      rw [← hk, (hbm.zpow_right k).mul_inv_cancel]
      exact ⟨k, rfl⟩
    have hbot : ⁅M, M⁆ = ⊥ := by
      rw [← hNz, eq_bot_iff, commutator_le]
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm, ← _root_.zpow_add, ← _root_.zpow_add,
        add_comm]
    rw [hd.perf] at hbot
    exact n₁ (by
      have := hu₁
      rw [hbot] at this
      exact (mem_bot).1 this)

end CFSG.ComponentClassification.Burgoyne.DX.Dr
