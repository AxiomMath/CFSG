module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL3

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddLin

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.C (uBlockProjEquiv subsingleton_statedSU_of_le_one
  statedSUCongr uBlock_mono isSolvable_SL_two_of_card_three commutator_le_uBlock_sup
  isSubnormal_map_mk le_map_commutator_of_perfect_mk)
open CFSG.ComponentClassification.Burgoyne.PSL (signMat compInd)
open CFSG.ComponentClassification.CatLeafProof.EndOddCore
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

variable [Finite K]

variable {m : ℕ}

omit [Finite K] in
theorem prW_conj (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0)
    (g : Matrix (Fin (m + m)) (Fin (m + m)) K) :
    prW m l * (prWi m l * g * prW m l) * prWi m l = g := by
  calc prW m l * (prWi m l * g * prW m l) * prWi m l =
      (prW m l * prWi m l) * g * (prW m l * prWi m l) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [prW_mul_prWi h2 hl, Matrix.one_mul, Matrix.mul_one]

omit [Finite K] in
theorem prEv_injective (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0)
    {g g' : Matrix (Fin (m + m)) (Fin (m + m)) K} (e : prEv m l g = prEv m l g') : g = g' := by
  have e1 : prWi m l * g * prW m l = prWi m l * g' * prW m l := (prFin K m).symm.injective e
  rw [← prW_conj h2 hl g, e1, prW_conj h2 hl g']

omit [Finite K] in
theorem eq_prPhi_scalar_of_commute (hu : UnitaryFieldData p f K) (h2 : (2 : K) ≠ 0) {l : K}
    (hl : l ≠ 0) (hN : hu.norm l = -1) (hm : 2 ≤ m) {X : Matrix (Fin (m + m)) (Fin (m + m)) K}
    (hX : ∀ G : SL(m, K), X * (((prSLHom hu h2 hl hN G : StatedSU (m + m) (p ^ f) K) :
      GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
        (((prSLHom hu h2 hl hN G : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) :
          Matrix (Fin (m + m)) (Fin (m + m)) K) * X) :
    ∃ a b : K, X = prPhi m l (a • 1) (b • 1) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  set Y := prEv m l X with hY
  have hT : ∀ i j : Fin m, i ≠ j → ∀ c : K,
      Y * fromBlocks (single i j c) 0 0 (-(hu.bar c • single j i 1)) =
        fromBlocks (single i j c) 0 0 (-(hu.bar c • single j i 1)) * Y := by
    intro i j hij c
    have h1 := hX (Matrix.SpecialLinearGroup.transvection hij c)
    rw [coe_prSLHom_transvection hu h2 hl hN hij c, sub_eq_add_neg,
      prPhi_add, prPhi_one h2 hl, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at h1
    have h3 := add_left_cancel h1
    have h4 := congrArg (prEv m l) h3
    rwa [prEv_mul h2 hl, prEv_mul h2 hl, prEv_prPhi h2 hl, ← hY] at h4
  have hblk : ∀ i j : Fin m, i ≠ j → ∀ c : K,
      Y.toBlocks₁₁ * single i j c = single i j c * Y.toBlocks₁₁ ∧
      Y.toBlocks₁₂ * (-(hu.bar c • single j i 1)) = single i j c * Y.toBlocks₁₂ ∧
      Y.toBlocks₂₁ * single i j c = (-(hu.bar c • single j i 1)) * Y.toBlocks₂₁ ∧
      Y.toBlocks₂₂ * (-(hu.bar c • single j i 1)) =
        (-(hu.bar c • single j i 1)) * Y.toBlocks₂₂ := by
    intro i j hij c
    have h1 := hT i j hij c
    rw [← fromBlocks_toBlocks Y, fromBlocks_multiply, fromBlocks_multiply] at h1
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h1
    obtain ⟨e1, e2, e3, e4⟩ := fromBlocks_inj.1 h1
    exact ⟨e1, e2, e3, e4⟩
  obtain ⟨η, hη0, hη⟩ := exists_skew hu
  have hbar1 : hu.bar 1 = 1 := map_one hu.bar
  obtain ⟨a, ha⟩ := mem_range_scalar_of_commute_single (M := Y.toBlocks₁₁) fun i j hij =>
    ((hblk i j hij 1).1).symm
  obtain ⟨b, hb⟩ := mem_range_scalar_of_commute_single (M := Y.toBlocks₂₂) fun i j hij => by
    have h1 := (hblk j i (Ne.symm hij) 1).2.2.2
    rw [hbar1, one_smul, Matrix.mul_neg, Matrix.neg_mul] at h1
    exact (neg_injective h1).symm
  have hY12 : Y.toBlocks₁₂ = 0 := by
    ext j k
    obtain ⟨i, hi⟩ := exists_ne j
    have e1 := (hblk i j hi 1).2.1
    have e2 := (hblk i j hi η).2.1
    rw [hbar1, one_smul] at e1
    have hs : single i j η = η • single i j (1 : K) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hη, neg_smul, neg_neg, Matrix.mul_smul, hs, Matrix.smul_mul] at e2
    have e3 : single i j (1 : K) * Y.toBlocks₁₂ = 0 := by
      have e4 := smul_right_injective _ hη0 e2
      rw [Matrix.mul_neg] at e1
      have h5 : (2 : K) • (single i j (1 : K) * Y.toBlocks₁₂) = 0 := by
        rw [two_smul]
        calc single i j (1 : K) * Y.toBlocks₁₂ + single i j 1 * Y.toBlocks₁₂ =
            Y.toBlocks₁₂ * single j i 1 + -(Y.toBlocks₁₂ * single j i 1) := by rw [e1, e4]
          _ = 0 := add_neg_cancel _
      exact (smul_eq_zero.1 h5).resolve_left h2
    have e5 := congrFun (congrFun e3 i) k
    simpa [Matrix.mul_apply, single_apply] using e5
  have hY21 : Y.toBlocks₂₁ = 0 := by
    ext k i
    obtain ⟨j, hj⟩ := exists_ne i
    have e1 := (hblk i j (Ne.symm hj) 1).2.2.1
    have e2 := (hblk i j (Ne.symm hj) η).2.2.1
    rw [hbar1, one_smul] at e1
    have hs : single i j η = η • single i j (1 : K) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hη, neg_smul, neg_neg, Matrix.smul_mul, hs, Matrix.mul_smul] at e2
    have e3 : Y.toBlocks₂₁ * single i j (1 : K) = 0 := by
      have e4 := smul_right_injective _ hη0 e2
      rw [Matrix.neg_mul] at e1
      have h5 : (2 : K) • (Y.toBlocks₂₁ * single i j (1 : K)) = 0 := by
        rw [two_smul]
        calc Y.toBlocks₂₁ * single i j (1 : K) + Y.toBlocks₂₁ * single i j 1 =
            single j i 1 * Y.toBlocks₂₁ + -(single j i 1 * Y.toBlocks₂₁) := by
              rw [← e1, ← e4]
          _ = 0 := add_neg_cancel _
      exact (smul_eq_zero.1 h5).resolve_left h2
    have e5 := congrFun (congrFun e3 k) j
    simpa [Matrix.mul_apply, single_apply] using e5
  refine ⟨a, b, prEv_injective h2 hl ?_⟩
  rw [prEv_prPhi h2 hl, ← hY, ← fromBlocks_toBlocks Y, hY12, hY21, ← ha, ← hb,
    Matrix.scalar_apply, Matrix.scalar_apply, ← smul_one_eq_diagonal, ← smul_one_eq_diagonal]

theorem false_of_config_psu_paired (hu : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hm : 2 ≤ m)
    {l : K} (hl : l ≠ 0) (hN : hu.norm l = -1) {A : StatedSU (m + m) (p ^ f) K}
    (hA : ((A : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) = prA m l)
    {L D : Subgroup (StatedProj (StatedSU (m + m) (p ^ f) K))} (h : Config (projH _ A) L D) :
    False := by
  have h2 := two_ne_zero_of_unitary hu hp2
  have hZ := scalars_subgroupOf_le_center (H := StatedSU (m + m) (p ^ f) K)
  set L₀ := (prSLHom (m := m) hu h2 hl hN).range with hL₀
  have hcent : ∀ g : StatedSU (m + m) (p ^ f) K, g ∈ centralizer ({A} : Set _) →
      prA m l * ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
        ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) * prA m l := by
    intro g hg
    have h' := congrArg (fun u : StatedSU (m + m) (p ^ f) K =>
      ((u : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K))
      (mem_centralizer_singleton_iff.1 hg)
    simp only [Subgroup.coe_mul, Units.val_mul, hA] at h'
    exact h'.symm
  have hcomm : ⁅centralizer ({A} : Set (StatedSU (m + m) (p ^ f) K)),
      centralizer ({A} : Set (StatedSU (m + m) (p ^ f) K))⁆ ≤ L₀ := by
    rw [commutator_le]
    intro g hg k hk
    have hgk : ⁅g, k⁆ ∈ centralizer ({A} : Set (StatedSU (m + m) (p ^ f) K)) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hk) (inv_mem hg)) (inv_mem hk)
    refine mem_range_prSLHom hu h2 hl hN (hcent _ hgk) ?_
    have hblk : ∀ {u : StatedSU (m + m) (p ^ f) K},
        u ∈ centralizer ({A} : Set (StatedSU (m + m) (p ^ f) K)) →
        ∃ G G' : Matrix (Fin m) (Fin m) K,
          prEv m l ((u : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
            fromBlocks G 0 0 G' := by
      intro u hu'
      obtain ⟨G, G', hG⟩ := exists_prPhi_of_commute h2 hl (hcent u hu').symm
      exact ⟨G, G', by rw [hG, prEv_prPhi h2 hl]⟩
    obtain ⟨G₁, G₁', e₁⟩ := hblk hg
    obtain ⟨G₂, G₂', e₂⟩ := hblk hk
    obtain ⟨G₃, G₃', e₃⟩ := hblk (inv_mem hg)
    obtain ⟨G₄, G₄', e₄⟩ := hblk (inv_mem hk)
    have hinv : ∀ {u : StatedSU (m + m) (p ^ f) K} {G G' H H' : Matrix (Fin m) (Fin m) K},
        prEv m l ((u : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
          fromBlocks G 0 0 G' →
        prEv m l (((u⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) :
          Matrix (Fin (m + m)) (Fin (m + m)) K) = fromBlocks H 0 0 H' → G * H = 1 := by
      intro u G G' H H' eG eH
      have e1 : ((u : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *
          (((u⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) :
            Matrix (Fin (m + m)) (Fin (m + m)) K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          Units.val_one]
      have := congrArg (prEv m l) e1
      rw [prEv_mul h2 hl, eG, eH, prEv_one h2 hl, fromBlocks_multiply, ← fromBlocks_one] at this
      simpa using (fromBlocks_inj.1 this).1
    have h13 := hinv e₁ e₃
    have h24 := hinv e₂ e₄
    have hm4 : ((⁅g, k⁆ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) =
        (g : GL (Fin (m + m)) K) * (k : GL (Fin (m + m)) K) *
          ((g⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) *
          ((k⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) := by
      rw [commutatorElement_def]
      rfl
    rw [hm4, Units.val_mul, Units.val_mul, Units.val_mul, prEv_mul h2 hl, prEv_mul h2 hl,
      prEv_mul h2 hl, e₁, e₂, e₃, e₄]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      toBlocks_fromBlocks₁₁, det_mul]
    have d13 : G₁.det * G₃.det = 1 := by rw [← det_mul, h13, det_one]
    have d24 : G₂.det * G₄.det = 1 := by rw [← det_mul, h24, det_one]
    linear_combination G₂.det * G₄.det * d13 + d24
  have hK4 : 4 ≤ Nat.card K := by
    rw [hu.card_eq_sq]
    have := hu.prime.two_le
    have : p ≤ p ^ f := Nat.le_self_pow (by have := hu.one_le; omega) p
    nlinarith
  have hLq : IsQuasisimple L₀ := isQuasisimple_range_prSLHom hu h2 hl hN hm hK4
  set φ := (QuotientGroup.mk' ((StatedScalars (Fin (m + m)) K).subgroupOf
    (StatedSU (m + m) (p ^ f) K))).comp L₀.subtype with hφ
  have hφr : φ.range = L₀.map (QuotientGroup.mk' _) := by
    rw [hφ, MonoidHom.range_comp, range_subtype]
  have hNH : L₀.map (QuotientGroup.mk' ((StatedScalars (Fin (m + m)) K).subgroupOf
      (StatedSU (m + m) (p ^ f) K))) ≤ centralizer ({QuotientGroup.mk' _ A} : Set _) := by
    rintro _ ⟨g, ⟨G, rfl⟩, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change prPhi m l G (prDual hu G) * ((A : GL (Fin (m + m)) K) : Matrix _ _ K) =
      ((A : GL (Fin (m + m)) K) : Matrix _ _ K) * prPhi m l G (prDual hu G)
    rw [hA]
    exact (prPhi_commute_prA h2 hl _ _).symm
  have hperf : ∀ L' : Subgroup (StatedProj (StatedSU (m + m) (p ^ f) K)),
      L' ≤ centralizer ({QuotientGroup.mk' _ A} : Set _) → ⁅L', L'⁆ = L' →
      L' ≤ L₀.map (QuotientGroup.mk' _) := fun L' hL hp =>
    (le_map_commutator_of_perfect_mk hZ A hL hp).trans (map_mono hcomm)
  rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hLq φ with h0 | h0
  · have hb : L₀.map (QuotientGroup.mk' ((StatedScalars (Fin (m + m)) K).subgroupOf
        (StatedSU (m + m) (p ^ f) K))) = ⊥ := by rw [← hφr, h0]
    exact false_of_config_layer h hNH hperf (quatBlock_of_isSolvable (by rw [hb]; infer_instance))
  rw [hφr] at h0
  refine false_of_config_layer_comm h hNH hperf h0 ?_
  have hlift : ∀ {u : StatedSU (m + m) (p ^ f) K},
      QuotientGroup.mk' ((StatedScalars (Fin (m + m)) K).subgroupOf
        (StatedSU (m + m) (p ^ f) K)) u ∈
        centralizer (L₀.map (QuotientGroup.mk' ((StatedScalars (Fin (m + m)) K).subgroupOf
          (StatedSU (m + m) (p ^ f) K))) : Set (StatedProj (StatedSU (m + m) (p ^ f) K))) →
      ∃ a b : K, ((u : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
        prPhi m l (a • 1) (b • 1) := by
    intro u hu'
    have hcu := EndOddCore.commute_of_commutator_mem hZ (Subgroup.isPerfect_iff.1 hLq.1)
      (g := u) (by
        intro x hx
        have h1 := mem_centralizer_iff.1 hu' _ (mem_map_of_mem (QuotientGroup.mk' _) hx)
        refine (QuotientGroup.eq_one_iff _).1 ?_
        change QuotientGroup.mk' ((StatedScalars (Fin (m + m)) K).subgroupOf
          (StatedSU (m + m) (p ^ f) K)) (u * x * u⁻¹ * x⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group)
    refine eq_prPhi_scalar_of_commute hu h2 hl hN hm fun G => ?_
    have h1 := congrArg (fun x : StatedSU (m + m) (p ^ f) K =>
      ((x : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K))
      (hcu (prSLHom hu h2 hl hN G) ⟨G, rfl⟩)
    simpa only [Subgroup.coe_mul, Units.val_mul] using h1
  intro x hx y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨a, b, he⟩ := hlift hx
  obtain ⟨a', b', he'⟩ := hlift hy
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, he, he', prPhi_mul h2 hl,
    prPhi_mul h2 hl]
  congr 1 <;> rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, smul_smul, smul_smul, mul_comm]

end CFSG.ComponentClassification.CatLeafProof.EndOddLin
