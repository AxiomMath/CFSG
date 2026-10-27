module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCAbs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOCent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearModelSchreier
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOBlock
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThree
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)
open CFSG.ComponentClassification.Burgoyne.PSL (coordBlock mem_coordBlock_iff coordBlockEquiv
  isQuasisimple_coordBlock coordBlock_mono proj_injOn_coordBlock coordBlock_le_slCentralizer
  normalizes_coordBlock slCentralizer mem_slCentralizer signGL coe_signGL signSL coe_signSL
  signSL_mem_coordBlock signSL_mul_self even_card_pair signMat compInd commute_signMat_iff
  exists_split_normal_form exists_quad_normal_form even_of_sq_eq_nonsquare quadMat blockRep
  blockRep_injective exists_blockRep_of_commute blockRep_commute_quadMat blockSLE coe_blockSLE
  blockSLE_injective isQuasisimple_SL_quadExt QuadExt slReindex)
open scoped MatrixGroups commutatorElement

variable {n : ℕ} {K : Type} [Field K]

omit [Field K] in
theorem det_blkL_commutator {F : Type} [Field F] {m : Type*} [Fintype m] [DecidableEq m]
    {c : Matrix m m F} (hc : c * c = c) {g h gi hi : Matrix m m F} (hh : h * c = c * h)
    (hgi : gi * c = c * gi) (hhi : hi * c = c * hi) (hggi : g * gi = 1) (hhhi : h * hi = 1) :
    (blkL c (g * h * gi * hi)).det = 1 := by
  have e1 : blkL c (g * h * gi * hi) = blkL c g * blkL c h * blkL c gi * blkL c hi := by
    rw [blkL_mul hc hh, blkL_mul hc hgi, blkL_mul hc hhi]
  have e2 : (blkL c g).det * (blkL c gi).det = 1 := by
    rw [← det_mul, blkL_mul hc hgi, hggi, blkL_one, det_one]
  have e3 : (blkL c h).det * (blkL c hi).det = 1 := by
    rw [← det_mul, blkL_mul hc hhi, hhhi, blkL_one, det_one]
  rw [e1, det_mul, det_mul, det_mul]
  calc _ = ((blkL c g).det * (blkL c gi).det) * ((blkL c h).det * (blkL c hi).det) := by ring
    _ = 1 := by rw [e2, e3, mul_one]

theorem mem_coordBlock_of_blkL {J : Finset (Fin n)} {M : Matrix (Fin n) (Fin n) K}
    (hM : M * compInd K J = compInd K J * M) {g : SpecialLinearGroup (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K) = blkL (compInd K J) M) : g ∈ coordBlock K J := by
  have hc := compInd_mul_self (K := K) J
  refine ⟨?_, ?_⟩
  · rw [hg, blkL, mul_add, ← mul_assoc, ← hM, mul_assoc, mul_one_sub_self hc, mul_zero, zero_add,
      hc]
  · rw [hg, blkL, add_mul, mul_assoc, one_sub_mul_self hc, mul_zero, zero_add, hc]

theorem commute_compInd_of_mem_slCentralizer (h2 : (2 : K) ≠ 0) {J : Finset (Fin n)}
    {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ slCentralizer (signGL K J)) :
    (g : Matrix (Fin n) (Fin n) K) * compInd K J = compInd K J * g := by
  have h := mem_slCentralizer.1 hg
  rw [coe_signGL] at h
  exact ((commute_signMat_iff h2 J _).1 h.symm).symm

theorem commutator_slCentralizer_le (h2 : (2 : K) ≠ 0) (J : Finset (Fin n)) :
    ⁅slCentralizer (signGL K J), slCentralizer (signGL K J)⁆ ≤
      coordBlock K J ⊔ coordBlock K Jᶜ := by
  have hc := compInd_mul_self (K := K) J
  have hc' : (1 - compInd K J) * (1 - compInd K J) = 1 - compInd K J := one_sub_mul_one_sub hc
  rw [commutator_le]
  intro g hg h hh
  have hcom : ∀ {u : SpecialLinearGroup (Fin n) K}, u ∈ slCentralizer (signGL K J) →
      (u : Matrix (Fin n) (Fin n) K) * compInd K J = compInd K J * u :=
    fun hu => commute_compInd_of_mem_slCentralizer h2 hu
  have hcom' : ∀ {u : SpecialLinearGroup (Fin n) K}, u ∈ slCentralizer (signGL K J) →
      (u : Matrix (Fin n) (Fin n) K) * (1 - compInd K J) = (1 - compInd K J) * u := by
    intro u hu
    rw [mul_sub, sub_mul, mul_one, one_mul, hcom hu]
  set C := ⁅g, h⁆ with hCdef
  have hC : C ∈ slCentralizer (signGL K J) := commutator_mem_commutator hg hh |> fun h' =>
    (commutator_le_self _ |> fun hle => hle h')
  have hCm : (C : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K) *
      (h : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hCdef, commutatorElement_def]
    rfl
  have hinv : ∀ u : SpecialLinearGroup (Fin n) K, (u : Matrix (Fin n) (Fin n) K) *
      ((u⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := fun u => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hd₁ : (blkL (compInd K J) (C : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [hCm]
    exact det_blkL_commutator hc (hcom hh) (hcom (inv_mem hg)) (hcom (inv_mem hh)) (hinv g)
      (hinv h)
  have hd₂ : (blkL (1 - compInd K J) (C : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [hCm]
    exact det_blkL_commutator hc' (hcom' hh) (hcom' (inv_mem hg)) (hcom' (inv_mem hh)) (hinv g)
      (hinv h)
  set u₁ : SpecialLinearGroup (Fin n) K := ⟨_, hd₁⟩
  set u₂ : SpecialLinearGroup (Fin n) K := ⟨_, hd₂⟩
  have hu₁ : u₁ ∈ coordBlock K J := mem_coordBlock_of_blkL (hcom hC) rfl
  have hu₂ : u₂ ∈ coordBlock K Jᶜ := by
    refine mem_coordBlock_of_blkL (M := (C : Matrix (Fin n) (Fin n) K)) ?_ ?_
    · rw [compInd_compl]
      exact hcom' hC
    · rw [compInd_compl]
  have hCu : C = u₁ * u₂ := by
    apply Subtype.ext
    exact (blkL_mul_blkL_one_sub hc (hcom hC)).symm
  rw [hCu]
  exact mul_mem (mem_sup_left hu₁) (mem_sup_right hu₂)

theorem subsingleton_SL_of_le_one {m : ℕ} (hm : m ≤ 1) :
    Subsingleton (SpecialLinearGroup (Fin m) K) := by
  interval_cases m
  · constructor
    intro a b
    apply Subtype.ext
    ext i
    exact i.elim0
  · constructor
    intro a b
    apply Subtype.ext
    ext i j
    fin_cases i
    fin_cases j
    have ha := a.2
    have hb := b.2
    rw [det_fin_one] at ha hb
    exact ha.trans hb.symm

variable [Finite K]

@[expose] def coordBlockProjEquiv {I : Finset (Fin n)} {k : Fin n} (hk : k ∉ I) :
    coordBlock K I ≃* (coordBlock K I).map (proj n K) :=
  (MonoidHom.ofInjective (f := (proj n K).comp (coordBlock K I).subtype) fun g h e =>
    Subtype.ext (proj_injOn_coordBlock hk g.2 h.2 e)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype]))

omit [Finite K] in
theorem orderOf_proj_signSL (hK : ringChar K ≠ 2) (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    orderOf (proj n K (signSL K {a, b} (even_card_pair hab))) = 2 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, pow_two, signSL_mul_self, map_one]
  · intro h1
    rw [proj_eq_one_iff] at h1
    obtain ⟨c, -, hc⟩ := mem_scalars.1 h1
    obtain ⟨k, hk⟩ := PSL.exists_not_mem_pair hn a b
    have ha := congrFun (congrFun hc a) a
    have hk' := congrFun (congrFun hc k) k
    rw [coe_signSL, signMat, diagonal_apply_eq, scalar_apply, diagonal_apply_eq] at ha hk'
    rw [ite_eq_left (by simp)] at ha
    rw [ite_eq_right hk] at hk'
    rw [← ha] at hk'
    exact h2 (by linear_combination hk')

theorem blockOK_coordBlock (hK : ringChar K ≠ 2) (hn : 3 ≤ n) {I : Finset (Fin n)} {k : Fin n}
    (hk : k ∉ I) : BlockOK K ((coordBlock K I).map (proj n K)) := by
  set e := coordBlockProjEquiv (K := K) hk with he
  have hK3 : 3 ≤ Nat.card K := by
    have := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    obtain ⟨j, hj⟩ := this
    omega
  by_cases h1 : I.card ≤ 1
  · left
    have := subsingleton_SL_of_le_one (K := K) h1
    have : Subsingleton (coordBlock K I) :=
      (coordBlockEquiv (K := K) I).symm.injective.subsingleton
    have : Subsingleton ((coordBlock K I).map (proj n K)) := e.symm.injective.subsingleton
    infer_instance
  by_cases h23 : I.card = 2 ∧ Nat.card K = 3
  · left
    have hs : Group.IsSolvable SL(2, K) := isSolvable_SL_two_of_card_three h23.2
    have e2 : (coordBlock K I).map (proj n K) ≃* SL(2, K) :=
      (e.symm.trans (coordBlockEquiv I).symm).trans (slReindex K (finCongr h23.1))
    exact Group.isSolvable_of_isSolvable_injective (f := e2.toMonoidHom) e2.injective
  right
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
  refine ⟨hqs, ?_, ?_⟩
  ·
    rw [← Nat.card_congr e.toEquiv]
    have hdvd := Subgroup.card_dvd_of_le (coordBlock_mono (K := K) hsub)
    rwa [← Nat.card_congr (coordBlockEquiv (K := K) ({a, b} : Finset (Fin n))).toEquiv,
      Finset.card_pair hab] at hdvd
  · by_cases h3 : I.card = 2
    · right
      exact ⟨(e.symm.trans (coordBlockEquiv I).symm).trans (slReindex K (finCongr h3))⟩
    ·
      left
      obtain ⟨c, hc, hcab⟩ : ∃ c ∈ I, c ∉ ({a, b} : Finset (Fin n)) := by
        by_contra h
        push Not at h
        have := Finset.card_le_card (fun y hy => h y hy : I ⊆ {a, b})
        rw [Finset.card_pair hab] at this
        omega
      have hca : c ≠ a := fun h => hcab (h ▸ by simp)
      have hcb : c ≠ b := fun h => hcab (h ▸ by simp)
      have hbc : b ≠ c := Ne.symm hcb
      have hsub' : ({b, c} : Finset (Fin n)) ⊆ I := by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hb
        · rw [Finset.mem_singleton.1 hy]
          exact hc
      refine ⟨_, ⟨_, coordBlock_mono hsub (signSL_mem_coordBlock _ (even_card_pair hab)), rfl⟩,
        _, ⟨_, coordBlock_mono hsub' (signSL_mem_coordBlock _ (even_card_pair hbc)), rfl⟩,
        orderOf_proj_signSL hK hn hab, orderOf_proj_signSL hK hn hbc, ?_, ?_⟩
      · rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Matrix.SpecialLinearGroup.coe_mul, coe_signSL]
        exact O.signMat_mul_comm _ _
      · intro h
        rw [proj_eq_proj_iff] at h
        obtain ⟨z, -, hz⟩ := mem_scalars.1 h
        have hzz : ∀ y, ((signSL K {a, b} (even_card_pair hab))⁻¹ *
            signSL K {b, c} (even_card_pair hbc) : SpecialLinearGroup (Fin n) K) y y =
            (z : K) := fun y => by
          rw [hz, scalar_apply, diagonal_apply_eq]
        have hsinv : (signSL K {a, b} (even_card_pair hab))⁻¹ =
            signSL K {a, b} (even_card_pair hab) :=
          inv_eq_of_mul_eq_one_right (signSL_mul_self _ _)
        have h_a := hzz a
        have h_b := hzz b
        rw [hsinv, Matrix.SpecialLinearGroup.coe_mul, coe_signSL, coe_signSL, signMat, signMat,
          diagonal_mul_diagonal, diagonal_apply_eq] at h_a h_b
        simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, ite_true,
          hab, Ne.symm hab, hca.symm, or_false, ite_false] at h_a h_b
        have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
        simp only [mul_one, mul_neg, neg_neg] at h_a h_b
        exact h2 (by linear_combination h_b - h_a)

theorem psl_split_false (hK : ringChar K ≠ 2) (hn : 3 ≤ n) {J : Finset (Fin n)} {a b : Fin n}
    (ha : a ∈ J) (hb : b ∉ J) {μ : Kˣ} {A : SpecialLinearGroup (Fin n) K}
    (hA : SpecialLinearGroup.toGL A = GeneralLinearGroup.scalar (Fin n) μ * signGL K J)
    {R₁ R₂ : Subgroup (projectiveSL n K)} {p m : ℕ} [Fact p.Prime]
    (hC : PropCData (proj n K A) R₁ R₂ p m) : False := by
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
    · intro h
      have h' : (g : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
          (A : Matrix (Fin n) (Fin n) K) * g := congrArg Subtype.val h
      rw [hAm, Matrix.mul_smul, Matrix.smul_mul] at h'
      exact smul_right_injective _ μ.ne_zero h'
    · intro h
      apply Subtype.ext
      change (g : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
        (A : Matrix (Fin n) (Fin n) K) * g
      rw [hAm, Matrix.mul_smul, Matrix.smul_mul, h]
  have hZ := scalars_le_center n K
  have hC' : PropCData (QuotientGroup.mk' (scalars n K) A) R₁ R₂ p m := hC
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
  have hperf : ∀ L : Subgroup (projectiveSL n K),
      L ≤ centralizer ({QuotientGroup.mk' (scalars n K) A} : Set _) → ⁅L, L⁆ = L →
      L ≤ (coordBlock K J).map (QuotientGroup.mk' (scalars n K)) ⊔
        (coordBlock K Jᶜ).map (QuotientGroup.mk' (scalars n K)) := by
    intro L hL hp
    refine (le_map_commutator_of_perfect_mk hZ A hL hp).trans ?_
    rw [← Subgroup.map_sup, hcent]
    exact map_mono (commutator_slCentralizer_le h2 J)
  have hbJ : b ∉ J := hb
  have haJ : a ∉ Jᶜ := by simpa using ha
  exact propCData_false_of_blocks hC' (F := K) (hsub (Or.inl rfl)).1 (hsub (Or.inr rfl)).1
    (hsub (Or.inl rfl)).2 (hsub (Or.inr rfl)).2 hperf (blockOK_coordBlock hK hn hbJ)
    (blockOK_coordBlock hK hn haJ)

theorem psl_nonsplit_false {l : K} (hl : ¬ IsSquare l) {m' : ℕ} (hm : 2 ≤ m')
    {A : SpecialLinearGroup (Fin (m' * 2)) K}
    (hA : (A : Matrix (Fin (m' * 2)) (Fin (m' * 2)) K) = quadMat l m')
    {R₁ R₂ : Subgroup (projectiveSL (m' * 2) K)} {p m : ℕ} [Fact p.Prime]
    (hC : PropCData (proj (m' * 2) K A) R₁ R₂ p m) : False := by
  have hZ := scalars_le_center (m' * 2) K
  have hC' : PropCData (QuotientGroup.mk' (scalars (m' * 2) K) A) R₁ R₂ p m := hC
  set F := (blockSLE hl hm).range with hF
  have hcent : ∀ {g : SpecialLinearGroup (Fin (m' * 2)) K},
      g ∈ centralizer ({A} : Set (SpecialLinearGroup (Fin (m' * 2)) K)) ↔
        (g : Matrix (Fin (m' * 2)) (Fin (m' * 2)) K) * quadMat l m' = quadMat l m' * g := by
    intro g
    rw [mem_centralizer_singleton_iff, ← hA]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcomm : ⁅centralizer ({A} : Set (SpecialLinearGroup (Fin (m' * 2)) K)),
      centralizer ({A} : Set (SpecialLinearGroup (Fin (m' * 2)) K))⁆ ≤ F := by
    rw [commutator_le]
    intro g hg h hh
    have hY : ∀ {u : SpecialLinearGroup (Fin (m' * 2)) K},
        u ∈ centralizer ({A} : Set (SpecialLinearGroup (Fin (m' * 2)) K)) →
        ∃ Y : Matrix (Fin m') (Fin m') (QuadExt l),
          blockRep l m' Y = (u : Matrix (Fin (m' * 2)) (Fin (m' * 2)) K) :=
      fun hu => exists_blockRep_of_commute (hcent.1 hu)
    obtain ⟨Y₁, hY₁⟩ := hY hg
    obtain ⟨Y₂, hY₂⟩ := hY hh
    obtain ⟨Y₃, hY₃⟩ := hY (inv_mem hg)
    obtain ⟨Y₄, hY₄⟩ := hY (inv_mem hh)
    have hinv : ∀ {u : SpecialLinearGroup (Fin (m' * 2)) K} {Y Y' : Matrix (Fin m') (Fin m')
        (QuadExt l)}, blockRep l m' Y = (u : Matrix _ _ K) →
        blockRep l m' Y' = ((u⁻¹ : SpecialLinearGroup (Fin (m' * 2)) K) : Matrix _ _ K) →
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
    change blockRep l m' (Y₁ * Y₂ * Y₃ * Y₄) =
      ((⁅g, h⁆ : SpecialLinearGroup (Fin (m' * 2)) K) : Matrix (Fin (m' * 2)) (Fin (m' * 2)) K)
    rw [commutatorElement_def, map_mul, map_mul, map_mul, hY₁, hY₂, hY₃, hY₄]
    rfl
  have hFq : IsQuasisimple F :=
    LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (blockSLE_injective hl hm))
      (isQuasisimple_SL_quadExt hl hm)
  set f := (QuotientGroup.mk' (scalars (m' * 2) K)).comp F.subtype with hf
  have hfr : f.range = F.map (QuotientGroup.mk' (scalars (m' * 2) K)) := by
    rw [hf, MonoidHom.range_comp, range_subtype]
  have hN : Group.IsSolvable (F.map (QuotientGroup.mk' (scalars (m' * 2) K))) ∨
      IsQuasisimple (F.map (QuotientGroup.mk' (scalars (m' * 2) K))) := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hFq f with h | h
    · left
      rw [← hfr, h]
      infer_instance
    · right
      rwa [← hfr]
  have hNH : F.map (QuotientGroup.mk' (scalars (m' * 2) K)) ≤
      centralizer ({QuotientGroup.mk' (scalars (m' * 2) K) A} : Set _) := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨W, rfl⟩ := hg
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change blockRep l m' W * (A : Matrix (Fin (m' * 2)) (Fin (m' * 2)) K) =
      (A : Matrix (Fin (m' * 2)) (Fin (m' * 2)) K) * blockRep l m' W
    rw [hA]
    exact blockRep_commute_quadMat _
  refine propCData_false_of_layer hC' hNH (fun L hL hp => ?_) hN
  exact (le_map_commutator_of_perfect_mk hZ A hL hp).trans (map_mono hcomm)

theorem psl_propC_false (hK : ringChar K ≠ 2) (hn : 3 ≤ n) {x : projectiveSL n K}
    {R₁ R₂ : Subgroup (projectiveSL n K)} {p m : ℕ} [Fact p.Prime]
    (hC : PropCData x R₁ R₂ p m) : False := by
  obtain ⟨A, rfl⟩ := proj_surjective n K x
  have hx2 : proj n K (A * A) = 1 := by
    rw [map_mul, ← pow_two, ← hC.orderOf_eq, pow_orderOf_eq_one]
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hx2)
  have hAA : SpecialLinearGroup.toGL A * SpecialLinearGroup.toGL A =
      GeneralLinearGroup.scalar (Fin n) c := by
    apply Units.ext
    rw [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar,
      ← hc, Matrix.SpecialLinearGroup.coe_mul]
  have hns : ∀ c' : Kˣ, SpecialLinearGroup.toGL A ≠ GeneralLinearGroup.scalar (Fin n) c' := by
    intro c' hc'
    have hA : (A : Matrix (Fin n) (Fin n) K) = scalar (Fin n) (c' : K) := by
      have := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc'
      simpa only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar]
        using this
    have hdet : c' ^ n = 1 := by
      apply Units.ext
      have := A.2
      rw [hA, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at this
      rw [Units.val_pow_eq_pow_val, this, Units.val_one]
    have h1 : proj n K A = 1 := proj_eq_one_iff.2 (mem_scalars.2 ⟨c', hdet, hA⟩)
    have := hC.orderOf_eq
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  by_cases hsq : IsSquare (c : K)
  ·
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by rw [hr, mul_zero])
    set μ := Units.mk0 r hr0
    have hAμ : SpecialLinearGroup.toGL A * SpecialLinearGroup.toGL A =
        GeneralLinearGroup.scalar (Fin n) (μ * μ) := by
      rw [hAA]
      congr 1
      exact Units.ext hr
    obtain ⟨H, J, a, b, ha, hb, hH⟩ := exists_split_normal_form hK hAμ hns
    have hC' := hC.map (conjAut n K H)
    rw [conjAut_proj] at hC'
    refine psl_split_false hK hn ha hb (μ := μ) ?_ hC'
    rw [toGL_slConjugation, hH]
  ·
    have hev := even_of_sq_eq_nonsquare hAA hsq
    obtain ⟨m', rfl⟩ : ∃ m', n = m' * 2 := ⟨n / 2, by obtain ⟨k, hk⟩ := hev; omega⟩
    have hm : 2 ≤ m' := by omega
    have hAm : (SpecialLinearGroup.toGL A : Matrix (Fin (m' * 2)) (Fin (m' * 2)) K) *
        (SpecialLinearGroup.toGL A : Matrix (Fin (m' * 2)) (Fin (m' * 2)) K) = (c : K) • 1 := by
      have := congrArg Units.val hAA
      rw [Units.val_mul] at this
      rw [this]
      ext i j
      simp [GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply, diagonal_apply]
    obtain ⟨H, hH⟩ := exists_quad_normal_form hsq hAm
    have hC' := hC.map (conjAut (m' * 2) K H)
    rw [conjAut_proj] at hC'
    refine psl_nonsplit_false hsq hm ?_ hC'
    rw [coe_slConjugation]
    exact hH

theorem burgoynePropC_PSL {X : Type} [Group X] [Finite X] (hX : IsM4 X) {n' p' f' : ℕ}
    (hp2' : p' ≠ 2) (hL : LieModel (GeneralizedFitting.subgroup X) .PSL n' p' f') {r : X}
    {R₁ R₂ : Subgroup X} {p n : ℕ} [Fact p.Prime] (hC : PropCData r R₁ R₂ p n) : False := by
  obtain ⟨hsimple, hnab, -, hnot2, -⟩ := hX
  obtain ⟨hp, hf, hn2⟩ : p'.Prime ∧ 1 ≤ f' ∧ 2 ≤ n' := by
    rcases hL with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact ⟨h.1, h.2.1, h.2.2.1⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  have hn : 3 ≤ n' := by
    by_contra hn
    have h2 : n' = 2 := by omega
    subst h2
    exact hnot2 p' f' hp hp2' hL
  have hmod : StatedClassicalModel (GeneralizedFitting.subgroup X) .PSL n' p' f' := by
    rcases hL with ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  have hout := (LocalAnalysis.ComponentInitial.UnitaryHigher.linear_higher_classical_model_schreier
    hn hmod).2
  obtain ⟨K, _, _, hKc, ⟨θ⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have : Fintype K := Fintype.ofFinite K
  have : Fact p'.Prime := ⟨hp⟩
  have : CharP K p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p']; exact hp2'
  obtain ⟨x, R₁', R₂', hC', -⟩ := exists_propCData_of_socle hsimple hnab hout θ hC.orderOf_eq
    hC.le₁ hC.comp₁ hC.le₂ hC.comp₂ hC.p_ne_two hC.n_pos hC.iso₁ hC.iso₂ hC.mem
  exact psl_propC_false hK hn hC'

end CFSG.ComponentClassification.Burgoyne.C
