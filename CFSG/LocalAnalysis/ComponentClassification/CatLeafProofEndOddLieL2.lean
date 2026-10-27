module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL1
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCL

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddLin

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)
open CFSG.ComponentClassification.Burgoyne.PSL (coordBlock coordBlockEquiv
  isQuasisimple_coordBlock coordBlock_mono coordBlock_le_slCentralizer normalizes_coordBlock
  slCentralizer mem_slCentralizer signGL coe_signGL signMat exists_split_normal_form
  exists_quad_normal_form even_of_sq_eq_nonsquare quadMat quadPoly blockRep blockRep_injective
  exists_blockRep_of_commute blockRep_commute_quadMat blockSLE coe_blockSLE blockSLE_injective
  isQuasisimple_SL_quadExt QuadExt slReindex)
open CFSG.ComponentClassification.Burgoyne.C (coordBlockProjEquiv subsingleton_SL_of_le_one
  isSolvable_SL_two_of_card_three commutator_slCentralizer_le isSubnormal_map_mk
  le_map_commutator_of_perfect_mk)
open CFSG.ComponentClassification.CatLeafProof.EndOddCore
open scoped MatrixGroups commutatorElement

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem quatBlock_coordBlock (hK : ringChar K ≠ 2) {I : Finset (Fin n)} {k : Fin n}
    (hk : k ∉ I) : QuatBlock ((coordBlock K I).map (proj n K)) := by
  set e := coordBlockProjEquiv (K := K) hk with he
  have hK3 : 3 ≤ Nat.card K := by
    have := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    obtain ⟨j, hj⟩ := this
    omega
  by_cases h1 : I.card ≤ 1
  · have := subsingleton_SL_of_le_one (K := K) h1
    have : Subsingleton (coordBlock K I) :=
      (coordBlockEquiv (K := K) I).symm.injective.subsingleton
    have : Subsingleton ((coordBlock K I).map (proj n K)) := e.symm.injective.subsingleton
    exact quatBlock_of_isSolvable inferInstance
  by_cases h23 : I.card = 2 ∧ Nat.card K = 3
  · have hs : Group.IsSolvable SL(2, K) := isSolvable_SL_two_of_card_three h23.2
    have e2 : (coordBlock K I).map (proj n K) ≃* SL(2, K) :=
      (e.symm.trans (coordBlockEquiv I).symm).trans (slReindex K (finCongr h23.1))
    exact quatBlock_of_isSolvable
      (Group.isSolvable_of_isSolvable_injective (f := e2.toMonoidHom) e2.injective)
  have hI2 : 2 ≤ I.card := by omega
  have hq : 3 ≤ I.card ∨ 4 ≤ Nat.card K := by
    by_contra h
    push Not at h
    exact h23 ⟨by omega, by omega⟩
  have hqs : IsQuasisimple ((coordBlock K I).map (proj n K)) :=
    LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_coordBlock hI2 hq)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < I.card)
  have hsub : ({a, b} : Finset (Fin n)) ⊆ I := by
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact ha
    · rw [Finset.mem_singleton.1 hy]
      exact hb
  let φ : SL(2, K) →* (coordBlock K I).map (proj n K) :=
    e.toMonoidHom.comp ((Subgroup.inclusion (coordBlock_mono (K := K) hsub)).comp
      ((coordBlockEquiv (K := K) ({a, b} : Finset (Fin n))).toMonoidHom.comp
        (slReindex K (finCongr (Finset.card_pair hab).symm)).toMonoidHom))
  have hφ : Function.Injective φ :=
    e.injective.comp ((Subgroup.inclusion_injective (coordBlock_mono (K := K) hsub)).comp
      ((coordBlockEquiv _).injective.comp (slReindex K _).injective))
  obtain ⟨H, ⟨eH⟩⟩ := exists_quaternion_of_injective_SL hK φ hφ
  exact quatBlock_of_quat hqs H eH

theorem false_of_config_psl_split (hK : ringChar K ≠ 2) {J : Finset (Fin n)} {a b : Fin n}
    (ha : a ∈ J) (hb : b ∉ J) {μ : Kˣ} {A : SpecialLinearGroup (Fin n) K}
    (hA : SpecialLinearGroup.toGL A = GeneralLinearGroup.scalar (Fin n) μ * signGL K J)
    {L D : Subgroup (projectiveSL n K)} (h : Config (proj n K A) L D) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hAm : (A : Matrix (Fin n) (Fin n) K) = (μ : K) • signMat K J := by
    have := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hA
    simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Units.val_mul,
      GeneralLinearGroup.coe_scalar, coe_signGL] at this
    rw [this, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  have hcent : centralizer ({A} : Set (SpecialLinearGroup (Fin n) K)) =
      slCentralizer (signGL K J) := by
    ext g
    rw [mem_centralizer_singleton_iff, mem_slCentralizer, coe_signGL]
    constructor
    · intro hg
      have h' : (g : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
          (A : Matrix (Fin n) (Fin n) K) * g := congrArg Subtype.val hg
      rw [hAm, Matrix.mul_smul, Matrix.smul_mul] at h'
      exact smul_right_injective _ μ.ne_zero h'
    · intro hg
      apply Subtype.ext
      change (g : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
        (A : Matrix (Fin n) (Fin n) K) * g
      rw [hAm, Matrix.mul_smul, Matrix.smul_mul, hg]
  have hZ := scalars_le_center n K
  have h' : Config (QuotientGroup.mk' (scalars n K) A) L D := h
  have hsub : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) →
      (coordBlock K I).map (QuotientGroup.mk' (scalars n K)) ≤
          centralizer ({QuotientGroup.mk' (scalars n K) A} : Set _) ∧
        (((coordBlock K I).map (QuotientGroup.mk' (scalars n K))).subgroupOf
          (centralizer ({QuotientGroup.mk' (scalars n K) A} : Set _))).IsSubnormal := by
    intro I hI
    refine isSubnormal_map_mk hZ A (by rw [hcent]; exact coordBlock_le_slCentralizer h2 hI) ?_
    intro B hB g hg
    rw [hcent] at hB
    exact normalizes_coordBlock h2 hI B hB g hg
  have hperf : ∀ L' : Subgroup (projectiveSL n K),
      L' ≤ centralizer ({QuotientGroup.mk' (scalars n K) A} : Set _) → ⁅L', L'⁆ = L' →
      L' ≤ (coordBlock K J).map (QuotientGroup.mk' (scalars n K)) ⊔
        (coordBlock K Jᶜ).map (QuotientGroup.mk' (scalars n K)) := by
    intro L' hL hp
    refine (le_map_commutator_of_perfect_mk hZ A hL hp).trans ?_
    rw [← Subgroup.map_sup, hcent]
    exact map_mono (commutator_slCentralizer_le h2 J)
  have haJ : a ∉ Jᶜ := by simpa using ha
  exact false_of_config_blocks h' (hsub (Or.inl rfl)).1 (hsub (Or.inr rfl)).1
    (hsub (Or.inl rfl)).2 (hsub (Or.inr rfl)).2 hperf (quatBlock_coordBlock hK hb)
    (quatBlock_coordBlock hK haJ)

variable {l : K} {m : ℕ}

theorem commute_blockRep_of_commute (hl : ¬ IsSquare l) (hm : 2 ≤ m)
    {X : Matrix (Fin (m * 2)) (Fin (m * 2)) K}
    (hX : ∀ g : Matrix.SpecialLinearGroup (Fin m) (QuadExt l),
      X * (blockSLE hl hm g : Matrix (Fin (m * 2)) (Fin (m * 2)) K) =
        (blockSLE hl hm g : Matrix (Fin (m * 2)) (Fin (m * 2)) K) * X)
    (M : Matrix (Fin m) (Fin m) (QuadExt l)) : X * blockRep l m M = blockRep l m M * X := by
  have hoff : ∀ i j : Fin m, i ≠ j → ∀ c : QuadExt l,
      X * blockRep l m (single i j c) = blockRep l m (single i j c) * X := by
    intro i j hij c
    have h1 := hX (Matrix.SpecialLinearGroup.transvection hij c)
    rw [coe_blockSLE, Matrix.SpecialLinearGroup.transvection_coe, map_add, map_one,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h1
    exact add_left_cancel h1
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  induction M using Matrix.induction_on' with
  | h_zero => rw [map_zero, Matrix.mul_zero, Matrix.zero_mul]
  | h_add p q hp hq => rw [map_add, Matrix.mul_add, Matrix.add_mul, hp, hq]
  | h_std_basis i j c =>
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hk⟩ := exists_ne i
      have e : single i i c = single i k (1 : QuadExt l) * single k i c := by
        rw [single_mul_single_same, one_mul]
      rw [e, map_mul, ← Matrix.mul_assoc, hoff i k (Ne.symm hk) 1, Matrix.mul_assoc,
        hoff k i hk c, Matrix.mul_assoc]
    · exact hoff i j hij c

theorem eq_blockRep_scalar_of_commute (hl : ¬ IsSquare l) (hm : 2 ≤ m)
    {X : Matrix (Fin (m * 2)) (Fin (m * 2)) K}
    (hX : ∀ g : Matrix.SpecialLinearGroup (Fin m) (QuadExt l),
      X * (blockSLE hl hm g : Matrix (Fin (m * 2)) (Fin (m * 2)) K) =
        (blockSLE hl hm g : Matrix (Fin (m * 2)) (Fin (m * 2)) K) * X) :
    ∃ e : QuadExt l, X = blockRep l m (Matrix.scalar (Fin m) e) := by
  have hc := commute_blockRep_of_commute hl hm hX
  obtain ⟨Y, hY⟩ := exists_blockRep_of_commute (l := l) (m := m) (X := X)
    (hc (Matrix.scalar (Fin m) (AdjoinRoot.root (quadPoly l))))
  subst hY
  obtain ⟨e, he⟩ := mem_range_scalar_of_commute_single (M := Y) fun i j _ => by
    have h1 := hc (single i j 1)
    rw [← map_mul (blockRep l m), ← map_mul (blockRep l m)] at h1
    exact (blockRep_injective hl h1).symm
  exact ⟨e, by rw [he]⟩

theorem false_of_config_psl_nonsplit (hl : ¬ IsSquare l) (hm : 2 ≤ m)
    {A : SpecialLinearGroup (Fin (m * 2)) K}
    (hA : (A : Matrix (Fin (m * 2)) (Fin (m * 2)) K) = quadMat l m)
    {L D : Subgroup (projectiveSL (m * 2) K)} (h : Config (proj (m * 2) K A) L D) : False := by
  have hZ := scalars_le_center (m * 2) K
  have h' : Config (QuotientGroup.mk' (scalars (m * 2) K) A) L D := h
  set F := (blockSLE hl hm).range with hF
  have hcent : ∀ {g : SpecialLinearGroup (Fin (m * 2)) K},
      g ∈ centralizer ({A} : Set (SpecialLinearGroup (Fin (m * 2)) K)) ↔
        (g : Matrix (Fin (m * 2)) (Fin (m * 2)) K) * quadMat l m = quadMat l m * g := by
    intro g
    rw [mem_centralizer_singleton_iff, ← hA]
    constructor
    · intro hg
      exact congrArg Subtype.val hg
    · intro hg
      exact Subtype.ext hg
  have hcomm : ⁅centralizer ({A} : Set (SpecialLinearGroup (Fin (m * 2)) K)),
      centralizer ({A} : Set (SpecialLinearGroup (Fin (m * 2)) K))⁆ ≤ F := by
    rw [commutator_le]
    intro g hg k hk
    have hY : ∀ {u : SpecialLinearGroup (Fin (m * 2)) K},
        u ∈ centralizer ({A} : Set (SpecialLinearGroup (Fin (m * 2)) K)) →
        ∃ Y : Matrix (Fin m) (Fin m) (QuadExt l),
          blockRep l m Y = (u : Matrix (Fin (m * 2)) (Fin (m * 2)) K) :=
      fun hu => exists_blockRep_of_commute (hcent.1 hu)
    obtain ⟨Y₁, hY₁⟩ := hY hg
    obtain ⟨Y₂, hY₂⟩ := hY hk
    obtain ⟨Y₃, hY₃⟩ := hY (inv_mem hg)
    obtain ⟨Y₄, hY₄⟩ := hY (inv_mem hk)
    have hinv : ∀ {u : SpecialLinearGroup (Fin (m * 2)) K} {Y Y' : Matrix (Fin m) (Fin m)
        (QuadExt l)}, blockRep l m Y = (u : Matrix _ _ K) →
        blockRep l m Y' = ((u⁻¹ : SpecialLinearGroup (Fin (m * 2)) K) : Matrix _ _ K) →
        Y * Y' = 1 := by
      intro u Y Y' hYu hY'u
      apply blockRep_injective hl
      rw [map_mul, hYu, hY'u, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, map_one]
    have h13 := hinv hY₁ hY₃
    have h24 := hinv hY₂ hY₄
    have hdet : (Y₁ * Y₂ * Y₃ * Y₄).det = 1 := by
      have e1 : Y₁.det * Y₃.det = 1 := by rw [← det_mul, h13, det_one]
      have e2 : Y₂.det * Y₄.det = 1 := by rw [← det_mul, h24, det_one]
      rw [det_mul, det_mul, det_mul]
      calc _ = (Y₁.det * Y₃.det) * (Y₂.det * Y₄.det) := by ring
        _ = 1 := by rw [e1, e2, mul_one]
    refine ⟨⟨_, hdet⟩, Subtype.ext ?_⟩
    change blockRep l m (Y₁ * Y₂ * Y₃ * Y₄) =
      ((⁅g, k⁆ : SpecialLinearGroup (Fin (m * 2)) K) : Matrix (Fin (m * 2)) (Fin (m * 2)) K)
    rw [commutatorElement_def, map_mul, map_mul, map_mul, hY₁, hY₂, hY₃, hY₄]
    rfl
  have hFq : IsQuasisimple F :=
    LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (blockSLE_injective hl hm))
      (isQuasisimple_SL_quadExt hl hm)
  set f := (QuotientGroup.mk' (scalars (m * 2) K)).comp F.subtype with hf
  have hfr : f.range = F.map (QuotientGroup.mk' (scalars (m * 2) K)) := by
    rw [hf, MonoidHom.range_comp, range_subtype]
  have hNH : F.map (QuotientGroup.mk' (scalars (m * 2) K)) ≤
      centralizer ({QuotientGroup.mk' (scalars (m * 2) K) A} : Set _) := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨W, rfl⟩ := hg
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change blockRep l m W * (A : Matrix (Fin (m * 2)) (Fin (m * 2)) K) =
      (A : Matrix (Fin (m * 2)) (Fin (m * 2)) K) * blockRep l m W
    rw [hA]
    exact blockRep_commute_quadMat _
  have hperf : ∀ L' : Subgroup (projectiveSL (m * 2) K),
      L' ≤ centralizer ({QuotientGroup.mk' (scalars (m * 2) K) A} : Set _) → ⁅L', L'⁆ = L' →
      L' ≤ F.map (QuotientGroup.mk' (scalars (m * 2) K)) := fun L' hL hp =>
    (le_map_commutator_of_perfect_mk hZ A hL hp).trans (map_mono hcomm)
  rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hFq f with h0 | h0
  · have hb : F.map (QuotientGroup.mk' (scalars (m * 2) K)) = ⊥ := by rw [← hfr, h0]
    exact false_of_config_layer h' hNH hperf (quatBlock_of_isSolvable (by rw [hb]; infer_instance))
  rw [hfr] at h0
  refine false_of_config_layer_comm h' hNH hperf h0 ?_
  have hlift : ∀ {u : SpecialLinearGroup (Fin (m * 2)) K},
      QuotientGroup.mk' (scalars (m * 2) K) u ∈
        centralizer (F.map (QuotientGroup.mk' (scalars (m * 2) K)) : Set (projectiveSL (m * 2) K)) →
      ∃ e : QuadExt l, (u : Matrix (Fin (m * 2)) (Fin (m * 2)) K) =
        blockRep l m (Matrix.scalar (Fin m) e) := by
    intro u hu
    have hcu := EndOddCore.commute_of_commutator_mem hZ (Subgroup.isPerfect_iff.1 hFq.1) (g := u)
      (by
        intro x hx
        have h1 := mem_centralizer_iff.1 hu _ (mem_map_of_mem (QuotientGroup.mk' _) hx)
        refine (QuotientGroup.eq_one_iff _).1 ?_
        change QuotientGroup.mk' (scalars (m * 2) K) (u * x * u⁻¹ * x⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group)
    refine eq_blockRep_scalar_of_commute hl hm fun Y => ?_
    exact congrArg Subtype.val (hcu (blockSLE hl hm Y) ⟨Y, rfl⟩)
  intro x hx y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (scalars (m * 2) K) x
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (scalars (m * 2) K) y
  obtain ⟨e, he⟩ := hlift hx
  obtain ⟨e', he'⟩ := hlift hy
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, he, he']
  exact ((Matrix.scalar_commute e (fun _ => Commute.all _ _) (Matrix.scalar (Fin m) e')).map
    (blockRep l m)).eq

theorem false_of_config_psl_nonsplit_one {A : SpecialLinearGroup (Fin (1 * 2)) K}
    (hA : (A : Matrix (Fin (1 * 2)) (Fin (1 * 2)) K) = quadMat l 1)
    {L D : Subgroup (projectiveSL (1 * 2) K)} (h : Config (proj (1 * 2) K A) L D) : False := by
  have hZ := scalars_le_center (1 * 2) K
  have h' : Config (QuotientGroup.mk' (scalars (1 * 2) K) A) L D := h
  have hY : ∀ {u : SpecialLinearGroup (Fin (1 * 2)) K},
      u ∈ centralizer ({A} : Set (SpecialLinearGroup (Fin (1 * 2)) K)) →
      ∃ Y : Matrix (Fin 1) (Fin 1) (QuadExt l),
        blockRep l 1 Y = (u : Matrix (Fin (1 * 2)) (Fin (1 * 2)) K) := by
    intro u hu
    refine exists_blockRep_of_commute ?_
    have hu' := mem_centralizer_singleton_iff.1 hu
    have h1 : (u : Matrix (Fin (1 * 2)) (Fin (1 * 2)) K) *
        (A : Matrix (Fin (1 * 2)) (Fin (1 * 2)) K) =
        (A : Matrix (Fin (1 * 2)) (Fin (1 * 2)) K) * (u : Matrix (Fin (1 * 2)) (Fin (1 * 2)) K) :=
      congrArg Subtype.val hu'
    rw [hA] at h1
    exact h1
  have hcomm : ⁅centralizer ({A} : Set (SpecialLinearGroup (Fin (1 * 2)) K)),
      centralizer ({A} : Set (SpecialLinearGroup (Fin (1 * 2)) K))⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro g hg
    rw [mem_centralizer_iff]
    intro g' hg'
    obtain ⟨Y, hY₁⟩ := hY hg
    obtain ⟨Y', hY₂⟩ := hY hg'
    apply Subtype.ext
    change (g' : Matrix (Fin (1 * 2)) (Fin (1 * 2)) K) * g = g * g'
    rw [← hY₁, ← hY₂, ← map_mul (blockRep l 1), ← map_mul (blockRep l 1)]
    congr 1
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  have hperf : ∀ L' : Subgroup (projectiveSL (1 * 2) K),
      L' ≤ centralizer ({QuotientGroup.mk' (scalars (1 * 2) K) A} : Set _) → ⁅L', L'⁆ = L' →
      L' ≤ ⊥ := fun L' hL hp =>
    (le_map_commutator_of_perfect_mk hZ A hL hp).trans (by rw [hcomm, Subgroup.map_bot])
  exact false_of_config_layer h' bot_le hperf (quatBlock_of_isSolvable inferInstance)

end CFSG.ComponentClassification.CatLeafProof.EndOddLin
