module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBLevi
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWZero
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveNModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSOne

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type*} [Field K]

theorem pointRadElem_single_eq_transvection_sixS {i j : Fin n} (hij : i ≠ j) :
    pointRadElem i (Pi.single j (1 : K)) = SpecialLinearGroup.transvection hij 1 := by
  apply Subtype.ext
  rw [coe_pointRadElem, pointRadMat_single (Ne.symm hij), SpecialLinearGroup.transvection_coe,
    single_eq_single_vecMulVec_single]

theorem proj_pointRadElem_single_eq_xab_sixS {i j : Fin n} (hij : i ≠ j) :
    LinearFlag.proj n K (pointRadElem i (Pi.single j (1 : K))) = xab hij 1 := by
  rw [pointRadElem_single_eq_transvection_sixS hij, xab]

theorem pointRadElem_inv_sixS (c : Fin n) (r : Fin n → K) :
    (pointRadElem c r)⁻¹ = pointRadElem c (-r) :=
  (eq_inv_of_mul_eq_one_left (by rw [pointRadElem_mul, neg_add_cancel, pointRadElem_zero])).symm

theorem pointRadElem_mem_blockSpecialLinear_compl_sixS {c i : Fin n} (hci : c ≠ i) {s : Fin n → K}
    (hsc : s c = 0) : pointRadElem i s ∈ blockSpecialLinear ({c}ᶜ : Finset (Fin n)) := by
  have h := pointRadSL_le_blockSpecialLinear (K := K) i ({c}ᶜ : Finset (Fin n))
    ⟨s, fun j hj => by
      rw [Finset.mem_compl, Finset.mem_singleton, not_not] at hj
      rw [hj, hsc], rfl⟩
  rwa [Finset.insert_eq_of_mem (by simpa using Ne.symm hci)] at h

theorem conj_pointRadElem_pointRadElem_sixS {c i : Fin n} (hci : c ≠ i) {s : Fin n → K}
    (hsc : s c = 0) (r : Fin n → K) :
    pointRadElem i s * pointRadElem c r * (pointRadElem i s)⁻¹ =
      pointRadElem c (Function.update r c 0 +
        Function.update r c 0 i • Function.update (-s) i 0) := by
  rw [conj_pointRadElem_of_mem_blockSpecialLinear
      (pointRadElem_mem_blockSpecialLinear_compl_sixS hci hsc),
    pointRadElem_inv_sixS, coe_pointRadElem, vecMul_pointRadMat]

theorem mem_normalizer_of_conj_mem_of_conj_inv_mem_sixS {X : Type*} [Group X] {H : Subgroup X}
    {g : X} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    g ∈ normalizer (H : Set X) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

theorem vecMul_apply_of_mem_blockSpecialLinear_sixS {I : Finset (Fin n)}
    {B : SpecialLinearGroup (Fin n) K} (hB : B ∈ blockSpecialLinear I) (v : Fin n → K) {j : Fin n}
    (hj : j ∉ I) : (v ᵥ* (B : Matrix (Fin n) (Fin n) K)) j = v j := by
  have hcol : ∀ m, (B : Matrix (Fin n) (Fin n) K) m j = (1 : Matrix (Fin n) (Fin n) K) m j :=
    fun m => hB m j (Or.inr hj)
  calc (v ᵥ* (B : Matrix (Fin n) (Fin n) K)) j = (v ᵥ* (1 : Matrix (Fin n) (Fin n) K)) j := by
        simp only [vecMul, dotProduct, hcol]
    _ = v j := by rw [vecMul_one]

theorem blockSL_le_normalizer_pointRadOn_sixS {c : Fin n} {I T : Finset (Fin n)} (hcI : c ∉ I)
    (hIT : I ⊆ T) :
    blockSL (K := K) I ≤
      normalizer (pointRadOn (K := K) c T : Set (LinearFlag.projectiveSL n K)) := by
  have hIc : I ⊆ ({c}ᶜ : Finset (Fin n)) := fun j hj => by
    rw [Finset.mem_compl, Finset.mem_singleton]
    rintro rfl
    exact hcI hj
  have key : ∀ B ∈ blockSpecialLinear (K := K) I, ∀ x ∈ pointRadOn (K := K) c T,
      LinearFlag.proj n K B * x * (LinearFlag.proj n K B)⁻¹ ∈ pointRadOn (K := K) c T := by
    intro B hB x hx
    obtain ⟨_, ⟨r, hr, rfl⟩, rfl⟩ := hx
    rw [← map_inv, ← map_mul, ← map_mul,
      conj_pointRadElem_of_mem_blockSpecialLinear (blockSpecialLinear_mono hIc hB)]
    refine ⟨_, ⟨_, fun j hj => ?_, rfl⟩, rfl⟩
    have hjI : j ∉ I := fun h => hj (hIT h)
    rw [vecMul_apply_of_mem_blockSpecialLinear_sixS (inv_mem hB) _ hjI]
    by_cases hjc : j = c
    · rw [hjc, Function.update_self]
    · rw [Function.update_of_ne hjc]
      exact hr j hj
  intro p hp
  obtain ⟨B, hB, rfl⟩ := mem_blockSL.1 hp
  refine mem_normalizer_of_conj_mem_of_conj_inv_mem_sixS (key B hB) fun x hx => ?_
  have h := key B⁻¹ (inv_mem hB) x hx
  rwa [map_inv, inv_inv] at h

theorem pointRadOn_inf_pointRadOn_eq_bot_sixS (hK : Nat.card K = 2) {c c' : Fin n} (hcc' : c ≠ c')
    (S S' : Finset (Fin n)) : pointRadOn (K := K) c S ⊓ pointRadOn c' S' = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨⟨_, ⟨r, -, rfl⟩, rfl⟩, ⟨_, ⟨s, -, rfl⟩, hs'⟩⟩
  have h1 : pointRadElem c' s = pointRadElem c r := proj_injective_of_natCard_eq_two hK hs'
  have hr0 : Function.update r c 0 = 0 := by
    funext j
    by_cases hjc : j = c
    · rw [hjc, Function.update_self, Pi.zero_apply]
    · rw [Function.update_of_ne hjc, Pi.zero_apply]
      have h2 := congrArg (fun A : SpecialLinearGroup (Fin n) K =>
        (A : Matrix (Fin n) (Fin n) K) c j) h1
      rw [coe_pointRadElem, coe_pointRadElem, pointRadMat_apply, pointRadMat_apply,
        ite_eq_right (fun h => hcc' h.1), ite_eq_left ⟨rfl, hjc⟩] at h2
      exact add_left_cancel h2.symm
  rw [Subgroup.mem_bot, pointRadElem_eq_of_update_eq (s := 0)
    (by rw [hr0]; exact (Function.update_eq_self c (0 : Fin n → K)).symm), pointRadElem_zero,
    map_one]

theorem mem_pointRadOn_of_mem_blockSL_of_forall_commute_sixS (hK : Nat.card K = 2) {c : Fin n}
    {S : Finset (Fin n)} (hcS : c ∉ S) (hS : S.Nonempty) {p : LinearFlag.projectiveSL n K}
    (hp : p ∈ blockSL (K := K) (insert c S))
    (hcomm : ∀ v ∈ pointRadOn (K := K) c S, p * v = v * p) : p ∈ pointRadOn (K := K) c S := by
  classical
  obtain ⟨B, hB, rfl⟩ := mem_blockSL.1 hp
  have hrel : ∀ j ∈ S, ∀ i k : Fin n,
      (B : Matrix (Fin n) (Fin n) K) i c * (Pi.single j (1 : K) : Fin n → K) k =
        (Pi.single c (1 : K) : Fin n → K) i * (B : Matrix (Fin n) (Fin n) K) j k := by
    intro j hj i k
    have hjc : j ≠ c := by rintro rfl; exact hcS hj
    have hmem : LinearFlag.proj n K (pointRadElem c (Pi.single j (1 : K))) ∈
        pointRadOn (K := K) c S :=
      ⟨_, ⟨Pi.single j 1, fun k hk => Pi.single_eq_of_ne (by rintro rfl; exact hk hj) 1, rfl⟩,
        rfl⟩
    have h1 := mul_eq_mul_of_proj_mul_eq hK (hcomm _ hmem)
    rw [coe_pointRadElem, pointRadMat_single hjc] at h1
    have h2 := congrFun₂ (vecMulVec_eq_of_commute_one_add h1) i k
    simpa only [vecMulVec_apply, mulVec_single_one, single_one_vecMul, col_apply,
      row_apply] using h2
  have hrow : ∀ j ∈ S, ∀ k : Fin n,
      (B : Matrix (Fin n) (Fin n) K) j k =
        (B : Matrix (Fin n) (Fin n) K) c c * (Pi.single j (1 : K) : Fin n → K) k := by
    intro j hj k
    have := hrel j hj c k
    rw [Pi.single_eq_same, one_mul] at this
    exact this.symm
  obtain ⟨j₀, hj₀⟩ := hS
  have hcc : (B : Matrix (Fin n) (Fin n) K) c c = 1 := by
    rcases eq_zero_or_eq_one_of_natCard_eq_two hK ((B : Matrix (Fin n) (Fin n) K) c c) with
      h0 | h1
    · exfalso
      have hdet : (B : Matrix (Fin n) (Fin n) K).det = 0 :=
        det_eq_zero_of_row_eq_zero j₀ fun k => by rw [hrow j₀ hj₀ k, h0, zero_mul]
      rw [B.2] at hdet
      exact one_ne_zero hdet
    · exact h1
  set r : Fin n → K := fun k => (B : Matrix (Fin n) (Fin n) K) c k with hr
  have hBr : pointRadElem c r = B := by
    apply Subtype.ext
    ext i k
    rw [coe_pointRadElem, pointRadMat_apply]
    by_cases hi : i = c
    · subst hi
      by_cases hk : k = i
      · subst hk
        rw [one_apply_eq, hcc]
        simp
      · rw [one_apply_ne (Ne.symm hk), zero_add, ite_eq_left ⟨rfl, hk⟩]
    · rw [ite_eq_right (fun h => hi h.1), add_zero]
      by_cases hiS : i ∈ S
      · rw [hrow i hiS k, hcc, one_mul, Pi.single_apply, one_apply]
        by_cases hik : i = k
        · rw [ite_eq_left hik, ite_eq_left hik.symm]
        · rw [ite_eq_right hik, ite_eq_right (Ne.symm hik)]
      · exact (hB i k (Or.inl (by simp [hi, hiS]))).symm
  refine ⟨B, ⟨Function.update r c 0, fun j hj => ?_, ?_⟩, rfl⟩
  · by_cases hjc : j = c
    · rw [hjc, Function.update_self]
    · rw [Function.update_of_ne hjc, hr]
      simp only
      rw [hB c j (Or.inr (by simp [hjc, hj])), one_apply_ne (Ne.symm hjc)]
  · rw [← hBr, pointRadElem_update_eq]

theorem transvection_mul_pointRadElem_mul_sixS [CharP K 2] {i j : Fin n} (hij : i ≠ j)
    {s : Fin n → K} (hsi : s i = 0) (hsj : s j = 0) :
    SpecialLinearGroup.transvection hij 1 * pointRadElem j s *
        SpecialLinearGroup.transvection hij 1 = pointRadElem i s * pointRadElem j s := by
  have hsj' : Function.update s j 0 = s := Function.update_eq_self_iff.2 hsj.symm
  have hsi' : Function.update s i 0 = s := Function.update_eq_self_iff.2 hsi.symm
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    coe_pointRadElem, pointRadMat, hsj', hsi', single_eq_single_vecMulVec_single]
  have hji : (Pi.single j (1 : K)) ⬝ᵥ (Pi.single i 1) = 0 := by
    rw [dotProduct_single, mul_one, Pi.single_eq_of_ne hij]
  have hjj : (Pi.single j (1 : K)) ⬝ᵥ (Pi.single j 1) = 1 := by
    rw [dotProduct_single, mul_one, Pi.single_eq_same]
  have hsi2 : s ⬝ᵥ (Pi.single i 1) = 0 := by rw [dotProduct_single, mul_one, hsi]
  have hsj2 : s ⬝ᵥ (Pi.single j 1) = 0 := by rw [dotProduct_single, mul_one, hsj]
  have hPP : vecMulVec (Pi.single i (1 : K)) (Pi.single j 1) *
      vecMulVec (Pi.single i 1) (Pi.single j 1) = 0 := by
    rw [vecMulVec_mul_vecMulVec, hji, zero_smul, vecMulVec_zero]
  have hQP : vecMulVec (Pi.single j (1 : K)) s * vecMulVec (Pi.single i 1) (Pi.single j 1) = 0 := by
    rw [vecMulVec_mul_vecMulVec, hsi2, zero_smul, vecMulVec_zero]
  have hPQ : vecMulVec (Pi.single i (1 : K)) (Pi.single j 1) * vecMulVec (Pi.single j 1) s =
      vecMulVec (Pi.single i 1) s := by
    rw [vecMulVec_mul_vecMulVec, hjj, one_smul]
  have hNP : vecMulVec (Pi.single i (1 : K)) s * vecMulVec (Pi.single i 1) (Pi.single j 1) = 0 := by
    rw [vecMulVec_mul_vecMulVec, hsi2, zero_smul, vecMulVec_zero]
  have hNQ : vecMulVec (Pi.single i (1 : K)) s * vecMulVec (Pi.single j 1) s = 0 := by
    rw [vecMulVec_mul_vecMulVec, hsj2, zero_smul, vecMulVec_zero]
  have h2 : ∀ M : Matrix (Fin n) (Fin n) K, M + M = 0 := fun M => by
    ext k l
    simp [CharTwo.add_self_eq_zero]
  simp only [add_mul, mul_add, one_mul, mul_one, hPP, hQP, hPQ, hNP, hNQ, add_zero]
  calc _ = 1 + vecMulVec (Pi.single j (1 : K)) s + vecMulVec (Pi.single i 1) s +
        (vecMulVec (Pi.single i 1) (Pi.single j 1) +
          vecMulVec (Pi.single i 1) (Pi.single j 1)) := by
          abel
    _ = _ := by rw [h2]; abel

theorem xab_commutator_proj_pointRadElem_sixS [CharP K 2] {i j : Fin n} (hij : i ≠ j)
    {s : Fin n → K} (hsi : s i = 0) (hsj : s j = 0) :
    xab hij 1 * LinearFlag.proj n K (pointRadElem j s) * (xab hij 1)⁻¹ *
        (LinearFlag.proj n K (pointRadElem j s))⁻¹ = LinearFlag.proj n K (pointRadElem i s) := by
  have hinv : (SpecialLinearGroup.transvection hij (1 : K))⁻¹ =
      SpecialLinearGroup.transvection hij 1 :=
    (eq_inv_of_mul_eq_one_left (InvPlacement.transvection_mul_self hij 1)).symm
  rw [xab, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hinv,
    transvection_mul_pointRadElem_mul_sixS hij hsi hsj, mul_inv_cancel_right]

theorem pointRadElem_conj_single_sixS [CharP K 2] {a d : Fin n} (had : a ≠ d) {s : Fin n → K}
    (hsa : s a = 0) (hsd : s d = 1) :
    pointRadElem d s * pointRadElem a (Pi.single d 1) * (pointRadElem d s)⁻¹ =
      pointRadElem a s := by
  rw [conj_pointRadElem_pointRadElem_sixS had hsa]
  congr 1
  funext k
  have hneg : -s = s := by
    funext m
    simp only [Pi.neg_apply]
    exact neg_eq_of_add_eq_zero_left (CharTwo.add_self_eq_zero (s m))
  have hu : Function.update (Pi.single d (1 : K) : Fin n → K) a 0 = (Pi.single d 1 : Fin n → K) :=
    Function.update_eq_self_iff.2 (Pi.single_eq_of_ne (M := fun _ : Fin n => K) had 1).symm
  rw [hneg, hu, Pi.single_eq_same, one_smul, Pi.add_apply]
  by_cases hk : k = d
  · rw [hk, Function.update_self, Pi.single_eq_same, add_zero, hsd]
  · rw [Function.update_of_ne hk, Pi.single_eq_of_ne hk, zero_add]

theorem eq_zero_of_proj_pointRadElem_commute_sixS (hK : Nat.card K = 2) {a c : Fin n} (hca : c ≠ a)
    {s : Fin n → K} (hsc : s c = 0) (hsa : s a = 0)
    (h : LinearFlag.proj n K (pointRadElem a s) *
        LinearFlag.proj n K (pointRadElem c (Pi.single a 1)) =
      LinearFlag.proj n K (pointRadElem c (Pi.single a 1)) *
        LinearFlag.proj n K (pointRadElem a s)) : s = 0 := by
  have h1 : pointRadElem a s * pointRadElem c (Pi.single a 1) * (pointRadElem a s)⁻¹ =
      pointRadElem c (Pi.single a 1) := by
    apply proj_injective_of_natCard_eq_two hK
    rw [map_mul, map_mul, map_inv, h, mul_inv_cancel_right]
  rw [conj_pointRadElem_pointRadElem_sixS hca hsc] at h1
  have h2 := update_eq_update_of_pointRadElem_eq h1
  funext j
  by_cases hjc : j = c
  · rw [hjc, hsc, Pi.zero_apply]
  have h3 := congrFun h2 j
  have hsa' : Function.update (-s) a 0 = -s :=
    Function.update_eq_self_iff.2 (by rw [Pi.neg_apply, hsa, neg_zero])
  rw [Function.update_of_ne hjc, Function.update_of_ne hjc, Pi.add_apply,
    Function.update_of_ne (Ne.symm hca), Pi.single_eq_same, one_smul, hsa',
    Function.update_of_ne hjc] at h3
  have h4 : (-s) j = 0 := add_left_cancel (h3.trans (add_zero _).symm)
  rw [Pi.neg_apply, neg_eq_zero] at h4
  rw [h4, Pi.zero_apply]

theorem conj_proj_pointRadElem_eq_sixS {a c : Fin n} (hca : c ≠ a)
    {s : Fin n → K} (hsc : s c = 0) (hsa : s a = 0) (v : Fin n → K) :
    LinearFlag.proj n K (pointRadElem a s) * LinearFlag.proj n K (pointRadElem c v) *
        (LinearFlag.proj n K (pointRadElem a s))⁻¹ =
      LinearFlag.proj n K (pointRadElem c (v + v a • (-s))) := by
  rw [← map_inv, ← map_mul, ← map_mul, conj_pointRadElem_pointRadElem_sixS hca hsc]
  congr 1
  apply pointRadElem_eq_of_update_eq
  have hsa' : Function.update (-s) a 0 = -s :=
    Function.update_eq_self_iff.2 (by rw [Pi.neg_apply, hsa, neg_zero])
  rw [Function.update_of_ne (Ne.symm hca), hsa']
  funext j
  by_cases hjc : j = c
  · rw [hjc, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hjc, Function.update_of_ne hjc, Pi.add_apply, Pi.add_apply,
      Function.update_of_ne hjc]

theorem transvection_braid_sixS [CharP K 2] {i j : Fin n} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : K) * SpecialLinearGroup.transvection hij.symm 1 *
        SpecialLinearGroup.transvection hij 1 =
      SpecialLinearGroup.transvection hij.symm 1 * SpecialLinearGroup.transvection hij 1 *
        SpecialLinearGroup.transvection hij.symm 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  have hEE : single i j (1 : K) * single i j 1 = 0 := single_mul_single_of_ne _ _ _ _ hij.symm _
  have hFF : single j i (1 : K) * single j i 1 = 0 := single_mul_single_of_ne _ _ _ _ hij _
  have hEF : single i j (1 : K) * single j i 1 = single i i 1 := by
    rw [single_mul_single_same, mul_one]
  have hFE : single j i (1 : K) * single i j 1 = single j j 1 := by
    rw [single_mul_single_same, mul_one]
  have hEFE : single i i (1 : K) * single i j 1 = single i j 1 := by
    rw [single_mul_single_same, mul_one]
  have hFEF : single j j (1 : K) * single j i 1 = single j i 1 := by
    rw [single_mul_single_same, mul_one]
  have h2 : ∀ M : Matrix (Fin n) (Fin n) K, M + M = 0 := fun M => by
    ext k l
    simp [CharTwo.add_self_eq_zero]
  simp only [add_mul, mul_add, one_mul, mul_one, hEE, hFF, hEF, hFE, add_zero, hEFE, hFEF]
  calc _ = 1 + single j i 1 + single i i 1 + single j j 1 + single i j 1 +
        (single i j (1 : K) + single i j 1) := by abel
    _ = 1 + single i j 1 + single i i 1 + single j j 1 + single j i 1 +
        (single j i (1 : K) + single j i 1) := by rw [h2, h2]; abel
    _ = _ := by abel

theorem xab_mul_xab_pow_three_sixS [CharP K 2] {i j : Fin n} (hij : i ≠ j) :
    (xab hij (1 : K) * xab hij.symm 1) ^ 3 = 1 := by
  have hx : xab hij (1 : K) * xab hij 1 = 1 := xab_mul_self_of_charTwo hij 1
  have hy : xab hij.symm (1 : K) * xab hij.symm 1 = 1 := xab_mul_self_of_charTwo hij.symm 1
  have hb : xab hij (1 : K) * xab hij.symm 1 * xab hij 1 =
      xab hij.symm 1 * xab hij 1 * xab hij.symm 1 := by
    simp only [xab, ← map_mul, transvection_braid_sixS hij]
  calc (xab hij (1 : K) * xab hij.symm 1) ^ 3
      = (xab hij (1 : K) * xab hij.symm 1 * xab hij 1) * (xab hij.symm 1 * xab hij 1 *
          xab hij.symm 1) := by rw [pow_three]; group
    _ = (xab hij.symm 1 * xab hij 1 * xab hij.symm 1) * (xab hij.symm 1 * xab hij 1 *
          xab hij.symm 1) := by rw [hb]
    _ = xab hij.symm 1 * xab hij 1 * (xab hij.symm 1 * xab hij.symm 1) * xab hij 1 *
          xab hij.symm 1 := by group
    _ = 1 := by
        rw [hy, mul_one, mul_assoc (xab hij.symm 1), hx, mul_one, hy]

theorem xab_mul_xab_ne_one_sixS [CharP K 2] (hK : Nat.card K = 2) {i j : Fin n} (hij : i ≠ j) :
    xab hij (1 : K) * xab hij.symm 1 ≠ 1 := by
  intro h
  have hy : (xab hij.symm (1 : K))⁻¹ = xab hij.symm 1 :=
    inv_eq_of_mul_eq_one_right (xab_mul_self_of_charTwo hij.symm 1)
  have h1 : xab hij (1 : K) = xab hij.symm 1 := by
    have h2 : xab hij (1 : K) = (xab hij.symm (1 : K))⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [hy] at h2
    exact h2
  have h4 : SpecialLinearGroup.transvection hij (1 : K) =
      SpecialLinearGroup.transvection hij.symm 1 := by
    apply proj_injective_of_natCard_eq_two hK
    rw [← xab_def, ← xab_def]
    exact h1
  have h5 : ((SpecialLinearGroup.transvection hij (1 : K) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i j =
      ((SpecialLinearGroup.transvection hij.symm (1 : K) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) i j := by rw [h4]
  rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, Matrix.add_apply,
    Matrix.add_apply, one_apply_ne hij, single_apply_same, zero_add] at h5
  have h6 : (single j i (1 : K) : Matrix (Fin n) (Fin n) K) i j = 0 := by
    simp [hij]
  rw [h6, add_zero] at h5
  exact one_ne_zero h5

theorem xab_conj_xab_mul_xab_sixS [CharP K 2] {i j : Fin n} (hij : i ≠ j) :
    xab hij (1 : K) * (xab hij 1 * xab hij.symm 1) * (xab hij 1)⁻¹ =
      (xab hij 1 * xab hij.symm 1)⁻¹ := by
  have hx : (xab hij (1 : K))⁻¹ = xab hij 1 :=
    inv_eq_of_mul_eq_one_right (xab_mul_self_of_charTwo hij 1)
  have hy : (xab hij.symm (1 : K))⁻¹ = xab hij.symm 1 :=
    inv_eq_of_mul_eq_one_right (xab_mul_self_of_charTwo hij.symm 1)
  rw [_root_.mul_inv_rev, hx, hy, ← mul_assoc, xab_mul_self_of_charTwo hij 1, one_mul]

theorem pointRadical_inf_centralizer_xab_mul_xab_le_sixS (hK : Nat.card K = 2) [CharP K 2]
    {c i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hci : c ≠ i) (hcj : c ≠ j) (hck : c ≠ k) (hcl : c ≠ l) :
    pointRadical (K := K) c ⊓
        centralizer ({xab hij 1 * xab hkl 1} : Set (LinearFlag.projectiveSL n K)) ≤
      pointRadOn c (({c}ᶜ : Finset (Fin n)) \ {i, k}) := by
  rintro v ⟨⟨_, ⟨r, hr, rfl⟩, rfl⟩, hvc⟩
  have hrc : r c = 0 := hr c (by simp)
  have hel : (Pi.single l (1 : K) : Fin n → K) c = 0 := Pi.single_eq_of_ne hcl 1
  have hej : (Pi.single j (1 : K) : Fin n → K) c = 0 := Pi.single_eq_of_ne hcj 1
  have hel' : (Pi.single l (1 : K) : Fin n → K) k = 0 := Pi.single_eq_of_ne hkl 1
  have hej' : (Pi.single j (1 : K) : Fin n → K) i = 0 := Pi.single_eq_of_ne hij 1
  set r₁ : Fin n → K := Function.update r c 0 +
    Function.update r c 0 k • Function.update (-(Pi.single l (1 : K))) k 0 with hr₁
  set r₂ : Fin n → K := Function.update r₁ c 0 +
    Function.update r₁ c 0 i • Function.update (-(Pi.single j (1 : K))) i 0 with hr₂
  have hneg : ∀ (m : Fin n) (w : Fin n → K), w m = 0 → (-w) m = 0 := fun m w hw => by
    rw [Pi.neg_apply, hw, neg_zero]
  have hconj : (pointRadElem i (Pi.single j (1 : K)) * pointRadElem k (Pi.single l 1)) *
      pointRadElem c r * (pointRadElem i (Pi.single j (1 : K)) * pointRadElem k (Pi.single l 1))⁻¹ =
      pointRadElem c r₂ := by
    rw [_root_.mul_inv_rev, show ∀ x y z w u : SpecialLinearGroup (Fin n) K,
      x * y * z * (w * u) = x * (y * z * w) * u from fun x y z w u => by group,
      conj_pointRadElem_pointRadElem_sixS hck hel r, conj_pointRadElem_pointRadElem_sixS hci hej r₁]
  have hcomm : pointRadElem c r *
      (pointRadElem i (Pi.single j (1 : K)) * pointRadElem k (Pi.single l 1)) =
      (pointRadElem i (Pi.single j (1 : K)) * pointRadElem k (Pi.single l 1)) *
        pointRadElem c r := by
    apply proj_injective_of_natCard_eq_two hK
    simp only [map_mul]
    rw [proj_pointRadElem_single_eq_xab_sixS hij, proj_pointRadElem_single_eq_xab_sixS hkl]
    exact (mem_centralizer_singleton_iff.1 hvc)
  have h1 : pointRadElem c r₂ = pointRadElem c r := by
    rw [← hconj, ← hcomm, mul_inv_cancel_right]
  have h2 := update_eq_update_of_pointRadElem_eq h1
  have hl0 : r₂ l = r l - r k := by
    simp [hr₂, hr₁, Function.update_apply, hcl.symm, hck.symm, hil.symm, hjl.symm, hkl.symm,
      hci.symm]
    ring
  have hj0 : r₂ j = r j - r i := by
    simp [hr₂, hr₁, Function.update_apply, hcj.symm, hck.symm, hij.symm, hjl, hjk, hci.symm,
      hil]
    ring
  have hl := congrFun h2 l
  have hj := congrFun h2 j
  rw [Function.update_of_ne hcl.symm, Function.update_of_ne hcl.symm, hl0] at hl
  rw [Function.update_of_ne hcj.symm, Function.update_of_ne hcj.symm, hj0] at hj
  have hrk : r k = 0 := by
    have := hl
    rw [sub_eq_self] at this
    exact this
  have hri : r i = 0 := by
    have := hj
    rw [sub_eq_self] at this
    exact this
  refine ⟨pointRadElem c r, ⟨r, fun m hm => ?_, rfl⟩, rfl⟩
  by_cases hmc : m = c
  · rw [hmc, hrc]
  have hm' : m = i ∨ m = k := by
    by_contra hcon
    push Not at hcon
    exact hm (Finset.mem_sdiff.2 ⟨by simpa using hmc, by simp [hcon.1, hcon.2]⟩)
  rcases hm' with rfl | rfl
  · exact hri
  · exact hrk

theorem single_vecMul_of_mem_blockSpecialLinear_sixS {S : Finset (Fin n)}
    {B : SpecialLinearGroup (Fin n) K} (hB : B ∈ blockSpecialLinear S) {i : Fin n} (hi : i ∉ S) :
    (Pi.single i (1 : K) : Fin n → K) ᵥ* (B : Matrix (Fin n) (Fin n) K) = Pi.single i 1 := by
  rw [single_one_vecMul]
  funext k
  rw [row_apply, hB i k (Or.inl hi), one_apply, Pi.single_apply]
  by_cases h : i = k
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem single_vecMul_pointRadMat_self_sixS (i : Fin n) (r : Fin n → K) :
    (Pi.single i (1 : K) : Fin n → K) ᵥ* pointRadMat i r =
      Pi.single i 1 + Function.update r i 0 := by
  rw [vecMul_pointRadMat, Pi.single_eq_same, one_smul]

theorem single_vecMul_pointRadMat_of_ne_sixS {a b : Fin n} (hab : a ≠ b) (r : Fin n → K) :
    (Pi.single b (1 : K) : Fin n → K) ᵥ* pointRadMat a r = Pi.single b 1 := by
  rw [vecMul_pointRadMat, Pi.single_eq_of_ne hab, zero_smul, add_zero]

theorem pointRadOn_sup_inf_blockSL_eq_bot_sixS (hK : Nat.card K = 2) {a b : Fin n} (hab : a ≠ b)
    {S S' : Finset (Fin n)} (haS : a ∉ S) (haS' : a ∉ S') (hbS' : b ∉ S') :
    (pointRadOn (K := K) a (insert b S) ⊔ pointRadOn b S) ⊓ blockSL S' = ⊥ := by
  have haI : a ∉ insert b S := by simp [hab, haS]
  have hN : pointRadOn (K := K) b S ≤
      normalizer (pointRadOn (K := K) a (insert b S) : Set (LinearFlag.projectiveSL n K)) :=
    (pointRadOn_le_blockSL b S).trans (blockSL_le_normalizer_pointRadOn_sixS haI subset_rfl)
  rw [eq_bot_iff]
  rintro x ⟨hx, hxS'⟩
  obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer_sOne hN hx
  obtain ⟨_, ⟨r, -, rfl⟩, rfl⟩ := hp
  obtain ⟨_, ⟨s, -, rfl⟩, rfl⟩ := hq
  obtain ⟨B, hB, hBe⟩ := mem_blockSL.1 hxS'
  rw [← map_mul] at hBe
  have hB' : B = pointRadElem a r * pointRadElem b s := proj_injective_of_natCard_eq_two hK hBe
  have hrowb := single_vecMul_of_mem_blockSpecialLinear_sixS hB hbS'
  rw [hB', Matrix.SpecialLinearGroup.coe_mul, ← vecMul_vecMul, coe_pointRadElem,
    coe_pointRadElem, single_vecMul_pointRadMat_of_ne_sixS hab,
    single_vecMul_pointRadMat_self_sixS] at hrowb
  have hs0 : Function.update s b 0 = 0 := by
    have h1 := congrArg (fun v => v - Pi.single b (1 : K)) hrowb
    simpa using h1
  have hsb : pointRadElem b s = 1 := by
    rw [pointRadElem_eq_of_update_eq (s := 0)
      (by rw [hs0]; exact (Function.update_eq_self b (0 : Fin n → K)).symm), pointRadElem_zero]
  have hrowa := single_vecMul_of_mem_blockSpecialLinear_sixS hB haS'
  rw [hB', hsb, mul_one, coe_pointRadElem, single_vecMul_pointRadMat_self_sixS] at hrowa
  have hr0 : Function.update r a 0 = 0 := by
    have h1 := congrArg (fun v => v - Pi.single a (1 : K)) hrowa
    simpa using h1
  have hra : pointRadElem a r = 1 := by
    rw [pointRadElem_eq_of_update_eq (s := 0)
      (by rw [hr0]; exact (Function.update_eq_self a (0 : Fin n → K)).symm), pointRadElem_zero]
  rw [Subgroup.mem_bot, hra, hsb, map_one, one_mul]

theorem exists_conj_eq_elt_of_mem_blockSL_mem_sixS [Finite K] [CharP K 2] {I : Finset (Fin n)}
    (hI : I.card < n) {y : LinearFlag.projectiveSL n K} (hyI : y ∈ blockSL I) (hy : y * y = 1) :
    ∃ (k : ℕ) (P : InvPlacement n k) (g : LinearFlag.projectiveSL n K),
      g ∈ blockSL I ∧ P.outer ⊆ I ∧ g * y * g⁻¹ = P.elt K := by
  obtain ⟨A, hAI, rfl⟩ := mem_blockSL.1 hyI
  have hA : A * A = 1 := by
    rw [← map_mul, LinearFlag.proj_eq_one_iff] at hy
    exact eq_one_of_mem_scalars_of_mem_blockSpecialLinear hI
      ((blockSpecialLinear I).mul_mem hAI hAI) hy
  rw [← range_blockEmbed] at hAI
  obtain ⟨A', rfl⟩ := hAI
  have hA' : A' * A' = 1 := by
    apply blockEmbed_injective I
    rw [map_mul, hA, map_one]
  obtain ⟨k, u, w, hu, hw, huw, g, hg⟩ := exists_conj_eq_one_add_nilOf (K := K) hA'
  refine ⟨k, InvPlacement.ofSubtype u w hu hw huw, LinearFlag.proj n K (blockEmbed I g),
    proj_mem_blockSL (by rw [← range_blockEmbed]; exact ⟨g, rfl⟩),
    InvPlacement.outer_ofSubtype_subset u w hu hw huw, ?_⟩
  rw [← map_mul, ← map_inv, ← map_mul, InvPlacement.elt]
  congr 1
  apply Subtype.ext
  rw [← map_inv, ← map_mul, ← map_mul, coe_blockEmbed, hg]
  exact blockMatrix_one_add_nilOf u w hu hw huw

theorem InvPlacement.card_outer_sixS {k : ℕ} (P : InvPlacement n k) : P.outer.card = 2 * k := by
  rw [InvPlacement.outer, Finset.card_image_of_injective _ P.supp_injective, Finset.card_univ,
    Fintype.card_sum, Fintype.card_fin]
  ring

theorem InvPlacement.elt_eq_xab_sixS (P : InvPlacement n 1) :
    P.elt K = xab (P.u_ne_w 0 0) 1 := by
  rw [InvPlacement.elt, InvPlacement.mat_eq_transvection, xab]

theorem InvPlacement.elt_eq_xab_mul_xab_sixS (P : InvPlacement n 2) :
    P.elt K = xab (P.u_ne_w 0 0) 1 * xab (P.u_ne_w 1 1) 1 := by
  rw [InvPlacement.elt, InvPlacement.mat_eq_transvection_mul_transvection, map_mul, xab, xab]

theorem InvPlacement.elt_eq_one_sixS (P : InvPlacement n 0) : P.elt K = 1 := by
  rw [InvPlacement.elt, InvPlacement.mat_eq_one_of_zero, map_one]

end CFSG.SeitzReduction.LinearPilot
