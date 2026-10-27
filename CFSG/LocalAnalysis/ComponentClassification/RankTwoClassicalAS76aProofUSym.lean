module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUNoInv
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviSym

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate)
open scoped MatrixGroups commutatorElement

section Matrices

variable {K : Type} [Field K] {k : ℕ}

theorem eq_blk_of_commute_smul_one {M : Matrix (Fin (2 + k)) (Fin (2 + k)) K} {a b : K}
    (hab : a ≠ b)
    (h : M * blk (a • (1 : Matrix (Fin 2) (Fin 2) K)) (b • (1 : Matrix (Fin k) (Fin k) K)) =
      blk (a • 1) (b • 1) * M) :
    ∃ (X : Matrix (Fin 2) (Fin 2) K) (D : Matrix (Fin k) (Fin k) K), M = blk X D := by
  obtain ⟨A, B, C, D, hM⟩ := eq_reindex_fromBlocks M
  rw [hM, blk, ← map_mul, ← map_mul] at h
  have h' := (reindexAlgEquiv K K finSumFinEquiv).injective h
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h'
  obtain ⟨-, hB, hC, -⟩ := h'
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at hB hC
  have hB0 : B = 0 := by
    have h3 : (b - a) • B = 0 := by rw [sub_smul, hB, sub_self]
    exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hab))
  have hC0 : C = 0 := by
    have h3 : (a - b) • C = 0 := by rw [sub_smul, hC, sub_self]
    exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hab)
  exact ⟨A, D, by rw [hM, hB0, hC0, blk]⟩

theorem eq_diagonal_of_commute {E : Matrix (Fin 2) (Fin 2) K} {s : Fin 2 → K} (hs : s 0 ≠ s 1)
    (h : E * diagonal s = diagonal s * E) : E = diagonal fun i => E i i := by
  have key : ∀ i j, E i j * (s j - s i) = 0 := by
    intro i j
    have h1 := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => N i j) h
    simp only [mul_diagonal, diagonal_mul] at h1
    rw [mul_sub, h1]
    ring
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [diagonal_apply_ne _ hij]
    refine (mul_eq_zero.mp (key i j)).resolve_right (sub_ne_zero.mpr fun h2 => hs ?_)
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h2.symm
    · exact h2
    · exact absurd rfl hij

theorem map_swapBlk (g : K → K) (hg0 : g 0 = 0) (hg1 : g 1 = 1) :
    (swapBlk : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).map g = swapBlk := by
  rw [swapBlk, coe_reindexAlgEquiv, reindex_apply, ← submatrix_map, fromBlocks_map,
    Matrix.map_zero _ hg0, Matrix.map_one _ hg0 hg1]

theorem transpose_swapBlk : (swapBlk : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K)ᵀ = swapBlk := by
  rw [swapBlk, coe_reindexAlgEquiv, transpose_reindex, fromBlocks_transpose, transpose_zero,
    transpose_one]

end Matrices

section Swap

variable {K : Type} [Field K] {f : ℕ}

theorem exists_swapBlk_mem [CharP K 2] (f : ℕ) :
    ∃ s : StatedSU (2 + 2) (2 ^ f) K, (s : GL (Fin (2 + 2)) K).val = swapBlk ∧ s * s = 1 := by
  obtain ⟨s, hs⟩ := exists_statedSU_eq (n := 2 + 2) (q := 2 ^ f) (M := (swapBlk : Matrix _ _ K))
    det_swapBlk (by
      rw [map_swapBlk _ (by simp) (by simp), transpose_swapBlk, swapBlk_mul_swapBlk])
  exact ⟨s, hs, mul_self_eq_one_of_val hs swapBlk_mul_swapBlk⟩

theorem uProj_injective_four [CharP K 2] : Function.Injective (uProj K (2 + 2) f) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker, uProj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  have hdet := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU g.2
  rw [← hc, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hdet
  have hc1 : (c : K) = 1 := UnitaryHigher.eq_one_of_pow_four_eq_one_of_charTwo hdet
  rw [mem_bot]
  apply Subtype.ext
  rw [← hc, Subgroup.coe_one, show c = 1 from Units.ext hc1, map_one]

theorem conj_uProj_swap (s₀ g : StatedSU (2 + 2) (2 ^ f) K) :
    MulAut.conj (uProj K (2 + 2) f s₀) (uProj K (2 + 2) f g) =
      uProj K (2 + 2) f (s₀ * g * s₀⁻¹) := by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

variable {s₀ : StatedSU (2 + 2) (2 ^ f) K} (hs₀ : (s₀ : GL (Fin (2 + 2)) K).val = swapBlk)
  (hss : s₀ * s₀ = 1)
include hs₀ hss

theorem conj_swap_val (g : StatedSU (2 + 2) (2 ^ f) K) :
    ((s₀ * g * s₀⁻¹ : StatedSU (2 + 2) (2 ^ f) K) : GL (Fin (2 + 2)) K).val =
      swapBlk * (g : GL (Fin (2 + 2)) K).val * swapBlk := by
  have hinv : s₀⁻¹ = s₀ := inv_eq_of_mul_eq_one_right hss
  rw [hinv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hs₀]

theorem map_conj_uBarW :
    (uBarW K 2 f).map (MulAut.conj (uProj K (2 + 2) f s₀)).toMonoidHom = uBarL K 2 f := by
  rw [uBarW, uBarL, ← MonoidHom.range_comp]
  congr 1
  ext X
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [conj_uProj_swap s₀]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [conj_swap_val hs₀ hss, coe_uW, coe_uL, swapBlk_conj]

theorem map_conj_uBarL :
    (uBarL K 2 f).map (MulAut.conj (uProj K (2 + 2) f s₀)).toMonoidHom = uBarW K 2 f := by
  rw [uBarW, uBarL, ← MonoidHom.range_comp]
  congr 1
  ext X
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [conj_uProj_swap s₀]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [conj_swap_val hs₀ hss, coe_uW, coe_uL, swapBlk_conj]

theorem conj_torusU (c : rootsOfUnity (2 ^ f + 1) K) :
    s₀ * torusU K f c * s₀⁻¹ = torusU K f c⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  rw [conj_swap_val hs₀ hss, coe_torusU, coe_torusU, swapBlk_conj]
  simp only [InvMemClass.coe_inv, inv_inv]

theorem map_conj_uBarT :
    (uBarT K f).map (MulAut.conj (uProj K (2 + 2) f s₀)).toMonoidHom = uBarT K f := by
  ext y
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨c⁻¹, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [conj_uProj_swap s₀, conj_torusU hs₀ hss]
  · rintro ⟨c, rfl⟩
    refine ⟨uProj K (2 + 2) f (torusU K f c⁻¹), ⟨c⁻¹, rfl⟩, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [conj_uProj_swap s₀, conj_torusU hs₀ hss, inv_inv]

end Swap

section Five

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

omit [Finite K] [CharP K 2] in
theorem exists_diag_pair_mem {ζ : K} (hζ : ζ ^ 2 ^ f * ζ = 1) :
    ∃ X : StatedSU 2 (2 ^ f) K, (X : GL (Fin 2) K).val = diagonal ![ζ, ζ⁻¹] := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ
    exact zero_ne_one hζ
  refine exists_diagonal_mem (fun i => ?_) (by rw [Fin.prod_univ_two]; simp [hζ0])
  fin_cases i
  · exact hζ
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [inv_pow, ← mul_inv, hζ, inv_one]

theorem eq_one_of_fixes_u_five (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (α : MulAut (StatedProj (StatedSU (2 + 2) (2 ^ f) K))) (h2 : α * α = 1)
    (hW : ∀ w ∈ uBarW K 2 f, α w = w) (hT : ∀ t ∈ uBarT K f, α t = t) {ζ : K}
    (hζ : ζ ^ 2 ^ f * ζ = 1) (hζ1 : ζ ≠ 1) {X : StatedSU 2 (2 ^ f) K}
    (hX : (X : GL (Fin 2) K).val = diagonal ![ζ, ζ⁻¹])
    (hx : α (uProj K (2 + 2) f (uL K 2 f X)) = uProj K (2 + 2) f (uL K 2 f X)) : α = 1 := by
  have h := unitaryFieldData_of_card hK hf
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ
    exact zero_ne_one hζ
  obtain ⟨τ, A, -, hα⟩ := exists_unitary_semilinear_statedProj h (n := 2 + 2) (by norm_num)
    (fun h3 => by have := h3.1; omega) α
  obtain ⟨A₁, D, hA⟩ := exists_blk_of_fix_uBarW hα hζ hζ1 hW
  rcases eq_refl_or_bar_of_fix_uBarW hα h hA hW with rfl | hτ
  swap
  · obtain ⟨c, -, hc⟩ := exists_rootsOfUnity_ne_one hζ hζ1
    exact (false_of_fix_torus_bar h hα hτ hA hc (hT _ ⟨c, rfl⟩)).elim
  obtain ⟨J, hJ⟩ := exists_swapM_mem (K := K) f
  obtain ⟨J', hJ'⟩ := exists_twJ_mem hζ
  have e1 := mul_eq_of_fix_uBarW hα hA hW (mul_self_eq_one_of_val hJ swapM_mul_swapM)
  have e2 := mul_eq_of_fix_uBarW hα hA hW (mul_self_eq_one_of_val hJ' (twJ_mul_twJ hζ0))
  rw [hJ] at e1
  rw [hJ'] at e2
  have hA₁ := eq_smul_one_of_commute_twJ hζ0 hζ1 e1 e2
  have e := mul_eq_of_fix_uL hα hA hx
  rw [hX] at e
  have hD := eq_diagonal_of_commute (E := D) (s := ![ζ, ζ⁻¹])
    (by simpa using sub_ne_zero.mp (sub_inv_ne_zero hζ0 hζ1)) e.symm
  refine eq_one_of_sq_of_blk_diagonal (by norm_num) hα h2 (a := A₁ 0 0) (d := fun i => D i i) ?_
  rw [hA, ← hA₁, ← hD]

end Five

section Lift

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSU (2 + 2) (2 ^ 2) K)}

omit [Finite K] in
theorem exists_blk_of_mem_centralizer_u (hθ : Function.Surjective θ) {ζ : K}
    (hζ : ζ ^ 2 ^ 2 * ζ = 1) (hζ1 : ζ ≠ 1) {X : StatedSU 2 (2 ^ 2) K}
    (hX : (X : GL (Fin 2) K).val = diagonal ![ζ, ζ⁻¹]) {x : G} (hxA : x ∈ A)
    (hxθ : θ ⟨x, hxA⟩ = uProj K (2 + 2) 2 (uL K 2 2 X)) {m : G}
    (hm : m ∈ centralizer ((liftSub θ (uBarT K 2) ⊔ zpowers x : Subgroup G) : Set G))
    (hmA : m ∈ A) :
    ∃ g : StatedSU (2 + 2) (2 ^ 2) K, uProj K (2 + 2) 2 g = θ ⟨m, hmA⟩ ∧
      ∃ (Y E : Matrix (Fin 2) (Fin 2) K), (g : GL (Fin (2 + 2)) K).val = blk Y E ∧
        E = diagonal fun i => E i i := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ
    exact zero_ne_one hζ
  obtain ⟨g, hg⟩ := uProj_surjective (K := K) (f := 2) (2 + 2) (θ ⟨m, hmA⟩)
  refine ⟨g, hg, ?_⟩
  have hcomm : ∀ y : G, ∀ hy : y ∈ liftSub θ (uBarT K 2) ⊔ zpowers x, ∀ hyA : y ∈ A,
      θ ⟨m, hmA⟩ * θ ⟨y, hyA⟩ = θ ⟨y, hyA⟩ * θ ⟨m, hmA⟩ := by
    intro y hy hyA
    have h1 := mem_centralizer_iff.mp hm y hy
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext h1.symm)
  obtain ⟨c, hcζ, hc⟩ := exists_rootsOfUnity_ne_one hζ hζ1
  obtain ⟨t, ht⟩ := hθ (uProj K (2 + 2) 2 (torusU K 2 c))
  have htT : (t : G) ∈ liftSub θ (uBarT K 2) ⊔ zpowers x :=
    mem_sup_left (mem_liftSub.mpr ⟨t.2, by rw [ht]; exact ⟨c, rfl⟩⟩)
  have h1 := hcomm t htT t.2
  rw [show (⟨(t : G), t.2⟩ : ↥A) = t from rfl, ht, ← hg, ← map_mul, ← map_mul] at h1
  have h1' := congrArg (fun y : StatedSU (2 + 2) (2 ^ 2) K => (y : GL (Fin (2 + 2)) K).val)
    (uProj_injective_four h1)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_torusU, hcζ] at h1'
  rw [Units.val_inv_eq_inv_val, hcζ] at h1'
  obtain ⟨Y, E, hYE⟩ := eq_blk_of_commute_smul_one (k := 2)
    (fun h0 => (sub_inv_ne_zero hζ0 hζ1) (by rw [h0, sub_self])) h1'
  refine ⟨Y, E, hYE, ?_⟩
  have h2 := hcomm x (mem_sup_right (mem_zpowers x)) hxA
  rw [hxθ, ← hg, ← map_mul, ← map_mul] at h2
  have h2' := congrArg (fun y : StatedSU (2 + 2) (2 ^ 2) K => (y : GL (Fin (2 + 2)) K).val)
    (uProj_injective_four h2)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_uL, hX, hYE, blk_mul] at h2'
  refine eq_diagonal_of_commute (s := ![ζ, ζ⁻¹])
    (by simpa using sub_ne_zero.mp (sub_inv_ne_zero hζ0 hζ1)) ?_
  have h3 := (blk_injective h2').2
  exact h3

theorem sym_u_four [Finite G] (hA : commutator ↥A = ⊤) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hZ : Odd (Nat.card (center ↥A)))
    (hK : Nat.card K = (2 ^ 2) ^ 2) :
    ∃ (D' : Subgroup G) (s x : G), liftSub θ (uBarT K 2) ⊔ uLeviW θ = D' ⊔ uLeviW θ ∧ s ∈ A ∧
      rightConjugate (uLeviW θ) s = uLeviL θ ∧ rightConjugate (uLeviL θ) s = uLeviW θ ∧
      rightConjugate D' s = D' ∧ x ∈ uLeviL θ ∧ orderOf x = 5 ∧
      AS76b.layerCentralizer A (D' ⊔ zpowers x) = uLeviW θ ∧
      NoInvolutoryCentralizing A (D' ⊔ zpowers x ⊔ uLeviW θ) := by
  have h := unitaryFieldData_of_card hK (by norm_num)
  obtain ⟨ζ, hζ, hζ1⟩ := exists_norm_one_ne_one hK
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ
    exact zero_ne_one hζ
  obtain ⟨s₀, hs₀, hss⟩ := exists_swapBlk_mem (K := K) 2
  obtain ⟨sA, hsA⟩ := hθ (uProj K (2 + 2) 2 s₀)
  have hsθ : (θ ⟨(sA : G), sA.2⟩)⁻¹ = uProj K (2 + 2) 2 s₀ := by
    rw [show (⟨(sA : G), sA.2⟩ : ↥A) = sA from rfl, hsA, ← map_inv,
      inv_eq_of_mul_eq_one_right hss]
  obtain ⟨X, hX⟩ := exists_diag_pair_mem hζ
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hζ5 : ζ ^ 5 = 1 := by rw [pow_succ]; exact hζ
  have hX5 : uProj K (2 + 2) 2 (uL K 2 2 X) ^ 5 = 1 := by
    have hX5' : X ^ 5 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hX, diagonal_pow]
      simp only [Subgroup.coe_one, Units.val_one]
      rw [← diagonal_one]
      congr 1
      funext i
      fin_cases i
      · exact hζ5
      · simp [inv_pow, hζ5]
    rw [← map_pow, ← map_pow, hX5', map_one, map_one]
  have hX1 : uProj K (2 + 2) 2 (uL K 2 2 X) ≠ 1 := by
    intro h1
    have h2 : ((uProj K (2 + 2) 2).comp (uL K 2 2)) X =
        ((uProj K (2 + 2) 2).comp (uL K 2 2)) 1 := by
      rw [map_one]
      exact h1
    have h3 := congrArg (fun y : StatedSU 2 (2 ^ 2) K => (y : GL (Fin 2) K).val 0 0)
      (uProj_uL_injective h2)
    simp only [hX, diagonal_apply_eq, Subgroup.coe_one, Units.val_one] at h3
    exact hζ1 (by simpa using h3)
  obtain ⟨e₂⟩ := nonempty_SL2_equiv_statedSU_two hK
  obtain ⟨x, hxL, hxA, hxθ, hx5⟩ := exists_mem_levLift_orderOf hker hθ hZ (f := 2) le_rfl
    (CFSG.LieType.Steinberg.card_fixedSubfield hK) (commutator_uBarL hK le_rfl le_rfl)
    (e₂.trans (uBarLEquiv K 2 2)) ⟨X, rfl⟩ hX5 hX1
  have hxθ' : θ ⟨x, hxA⟩ = uProj K (2 + 2) 2 (uL K 2 2 X) := hxθ
  refine ⟨liftSub θ (uBarT K 2), sA, x, rfl, sA.2, ?_, ?_, ?_, hxL, hx5, ?_, ?_⟩
  · rw [uLeviW, rightConjugate_levLift sA.2, hsθ, map_conj_uBarW hs₀ hss]
    rfl
  · rw [uLeviL, rightConjugate_levLift sA.2, hsθ, map_conj_uBarL hs₀ hss]
    rfl
  · rw [rightConjugate_liftSub sA.2, hsθ, map_conj_uBarT hs₀ hss]
  · refine layerCentralizer_eq_levLift hker hθ (commutator_uBarW hK le_rfl)
      (isQuasisimple_uBarW hK le_rfl (by norm_num)) ?_ ?_ ?_
    · refine le_inf levLift_le ?_
      rw [le_centralizer_iff]
      refine sup_le (fun d hd => ?_) ?_
      · obtain ⟨hdA, hdT⟩ := mem_liftSub.mp hd
        have hle := levLift_le_centralizer hker hdA (S := uBarW K 2 2) fun w hw =>
          uBarT_commute_uBarW hdT hw
        rw [mem_centralizer_iff]
        intro w hw
        exact mem_centralizer_singleton_iff.mp (hle hw)
      · rw [zpowers_le]
        exact le_centralizer_iff.mp (levLift_le_centralizer_levLift hker
          (fun _ hs _ hs' => uBarW_commute_uBarL hs hs')) hxL
    · intro m hmM hm
      obtain ⟨g, hg, Y, E, hgE, -⟩ := exists_blk_of_mem_centralizer_u hθ hζ hζ1 hX hxA hxθ
        (mem_inf.mp hmM).2 hm
      rw [← hg]
      exact uProj_mem_normalizer_uBarW h hgE
    · intro a ha b hb haA hbA
      obtain ⟨g, hg, Y, E, hgE, hE⟩ := exists_blk_of_mem_centralizer_u hθ hζ hζ1 hX hxA hxθ
        (mem_inf.mp ha).2 haA
      obtain ⟨g', hg', Y', E', hgE', hE'⟩ := exists_blk_of_mem_centralizer_u hθ hζ hζ1 hX hxA
        hxθ (mem_inf.mp hb).2 hbA
      rw [← hg, ← hg', ← map_commutatorElement]
      obtain ⟨S, hS⟩ := commutatorElement_mem_range_uW h hgE hgE' (by
        rw [hE, hE', diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        exact mul_comm _ _)
      exact ⟨S, by simp only [MonoidHom.comp_apply]; rw [hS]⟩
  · intro σ hσ hfix
    obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
    have hT := inducedAut_fix_of_liftSub hθ (le_sup_left.trans le_sup_left) hfix hα
    have hW := inducedAut_fix_of_levLift hθ (commutator_uBarW hK le_rfl) le_sup_right hfix hα
    have hx : α (uProj K (2 + 2) 2 (uL K 2 2 X)) = uProj K (2 + 2) 2 (uL K 2 2 X) := by
      rw [← hxθ', hα, hfix ⟨x, hxA⟩ (mem_sup_left (mem_sup_right (mem_zpowers x)))]
    have h1 := eq_one_of_fixes_u_five hK (by norm_num) α (inducedAut_sq hθ hσ hα) hW hT hζ hζ1
      hX hx
    exact eq_one_of_theta_eq hker hA σ fun a => by rw [← hα, h1, MulAut.one_apply]

end Lift

end CFSG.ComponentClassification.RankTwoClassical
