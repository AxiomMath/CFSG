module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareOrthogonalModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace CLSFourGroupScalarSquare

open Matrix FourGroupOddBilinear FourGroupOddUnitary Module QuadraticMap
open CFSG.ComponentClassification CatalogueBOrthogonalScalarSquare
  CatalogueBOrthogonalScalarSquareField CatalogueBOrthogonalScalarSquareStructure

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Sign

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem signEquiv_empty (c : Basis ι K V) : signEquiv c ∅ = 1 := by
  have h := signEquiv_mul_self c ∅
  rwa [signEquiv_mul, symmDiff_self, Finset.bot_eq_empty] at h

theorem signEquiv_preserves_sesq {σ : K →+* K} (h : V →ₛₗ[σ] V →ₗ[K] K) (c : Basis ι K V)
    {S : Finset ι} (hS : ∀ i j, h (c i) (c j) ≠ 0 → (i ∈ S ↔ j ∈ S)) (v w : V) :
    h (signEquiv c S v) (signEquiv c S w) = h v w :=
  toLin_preserves h c (Matrix.of fun i j => h (c i) (c j)) (fun _ _ => rfl)
    (fun i j => map_signDiag σ S i j) (signDiag_conj fun i j hij => hS i j hij) v w

theorem eq_of_toMatrix_ne_zero (c : Basis ι K V) {T : V →ₗ[K] V}
    (hT : ∀ j, ∃ l : K, T (c j) = l • c j) {i j : ι} (h : LinearMap.toMatrix c c T i j ≠ 0) :
    i = j := by
  obtain ⟨l, hl⟩ := hT j
  rw [LinearMap.toMatrix_apply, hl, map_smul, c.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply] at h
  by_contra hij
  exact h (by simp [Ne.symm hij])

end Sign

theorem apply_of_mem_positiveSquareKernel {A : V ≃ₗ[K] V} {b : K} (hb : b ≠ 0) {v : V}
    (hv : v ∈ positiveSquareKernel A b) : A v = b • v := by
  have h := LinearMap.mem_ker.1 hv
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    Module.End.one_apply, sub_eq_zero] at h
  calc A v = b • (b⁻¹ • A v) := by rw [smul_smul, mul_inv_cancel₀ hb, one_smul]
    _ = b • v := by rw [h]

theorem apply_of_mem_negativeSquareKernel {A : V ≃ₗ[K] V} {b : K} (hb : b ≠ 0) {v : V}
    (hv : v ∈ negativeSquareKernel A b) : A v = (-b) • v := by
  have h := LinearMap.mem_ker.1 hv
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    Module.End.one_apply, add_eq_zero_iff_eq_neg] at h
  calc A v = b • (b⁻¹ • A v) := by rw [smul_smul, mul_inv_cancel₀ hb, one_smul]
    _ = (-b) • v := by rw [h, smul_neg, neg_smul]

section Systems

variable {Q : QuadraticForm K V} {A : V ≃ₗ[K] V}

theorem exists_four_of_signSystem_le [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : Q.polarBilin.Nondegenerate) {C : Subgroup (V ≃ₗ[K] V)} {ι : Type*} [DecidableEq ι]
    (t : Finset ι → V ≃ₗ[K] V) (ht0 : t ∅ = 1) (htm : ∀ S T, t S * t T = t (symmDiff S T))
    (htn : ∀ S : Finset ι, ∀ i ∈ S, ∀ j ∉ S, NotScalar (t S)) {S₁ S₂ S₃ : Finset ι}
    (hS₁ : t S₁ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    (hS₂ : t S₂ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    (hS₃ : t S₃ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    (hA₁ : t S₁ ∈ C) (hA₂ : t S₂ ∈ C) (hA₃ : t S₃ ∈ C) {z : ι} (hz₁ : z ∉ S₁) (hz₂ : z ∉ S₂)
    (hz₃ : z ∉ S₃) {y₁ y₂ y₃ y₁₂ y₁₃ y₂₃ y₁₂₃ : ι} (hy₁ : y₁ ∈ S₁) (hy₂ : y₂ ∈ S₂)
    (hy₃ : y₃ ∈ S₃) (hy₁₂ : y₁₂ ∈ symmDiff S₁ S₂) (hy₁₃ : y₁₃ ∈ symmDiff S₁ S₃)
    (hy₂₃ : y₂₃ ∈ symmDiff S₂ S₃) (hy₁₂₃ : y₁₂₃ ∈ symmDiff (symmDiff S₁ S₂) S₃) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ (C.subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  have hinv : ∀ S, t S * t S = 1 := fun S => by
    rw [htm, symmDiff_self, Finset.bot_eq_empty, ht0]
  have hcomm : ∀ S T, t S * t T = t T * t S := fun S T => by rw [htm, htm, symmDiff_comm]
  have hz : ∀ {S T : Finset ι}, z ∉ S → z ∉ T → z ∉ symmDiff S T := fun hS hT h =>
    (Finset.mem_symmDiff.1 h).elim (fun h => hS h.1) (fun h => hT h.1)
  refine exists_four_of_triple_le hK hQ hS₁ hS₂ hS₃ hA₁ hA₂ hA₃ (hinv _) (hinv _) (hinv _)
    (hcomm _ _) (hcomm _ _) (hcomm _ _) (htn _ _ hy₁ _ hz₁) (htn _ _ hy₂ _ hz₂)
    (htn _ _ hy₃ _ hz₃) ?_ ?_ ?_ ?_
  · rw [htm]
    exact htn _ _ hy₁₂ _ (hz hz₁ hz₂)
  · rw [htm]
    exact htn _ _ hy₁₃ _ (hz hz₁ hz₃)
  · rw [htm]
    exact htn _ _ hy₂₃ _ (hz hz₂ hz₃)
  · rw [htm, htm]
    exact htn _ _ hy₁₂₃ _ (hz (hz hz₁ hz₂) hz₃)

theorem exists_four_of_signSystem [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : Q.polarBilin.Nondegenerate) {ι : Type*} [DecidableEq ι] (t : Finset ι → V ≃ₗ[K] V)
    (ht0 : t ∅ = 1) (htm : ∀ S T, t S * t T = t (symmDiff S T))
    (htn : ∀ S : Finset ι, ∀ i ∈ S, ∀ j ∉ S, NotScalar (t S)) {S₁ S₂ S₃ : Finset ι}
    (hS₁ : t S₁ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    (hS₂ : t S₂ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    (hS₃ : t S₃ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    (hA₁ : t S₁ ∈ Subgroup.centralizer {A}) (hA₂ : t S₂ ∈ Subgroup.centralizer {A})
    (hA₃ : t S₃ ∈ Subgroup.centralizer {A}) {z : ι} (hz₁ : z ∉ S₁) (hz₂ : z ∉ S₂)
    (hz₃ : z ∉ S₃) {y₁ y₂ y₃ y₁₂ y₁₃ y₂₃ y₁₂₃ : ι} (hy₁ : y₁ ∈ S₁) (hy₂ : y₂ ∈ S₂)
    (hy₃ : y₃ ∈ S₃) (hy₁₂ : y₁₂ ∈ symmDiff S₁ S₂) (hy₁₃ : y₁₃ ∈ symmDiff S₁ S₃)
    (hy₂₃ : y₂₃ ∈ symmDiff S₂ S₃) (hy₁₂₃ : y₁₂₃ ∈ symmDiff (symmDiff S₁ S₂) S₃) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 :=
  exists_four_of_signSystem_le hK hQ t ht0 htm htn hS₁ hS₂ hS₃ hA₁ hA₂ hA₃ hz₁ hz₂ hz₃ hy₁ hy₂
    hy₃ hy₁₂ hy₁₃ hy₂₃ hy₁₂₃

theorem exists_four_of_blocks [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : Q.polarBilin.Nondegenerate) {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (c : Basis ι K V) (blk : ι → β) (hB : ∀ i j, Q.polarBilin (c i) (c j) ≠ 0 → blk i = blk j)
    (hA : ∀ j, ∃ l : K, A (c j) = l • c j) {S₁ S₂ S₃ : Finset ι}
    (hsat : ∀ S ∈ [S₁, S₂, S₃], ∀ i j, blk i = blk j → (i ∈ S ↔ j ∈ S))
    (hev : ∀ S ∈ [S₁, S₂, S₃], Even S.card) {z : ι} (hz₁ : z ∉ S₁) (hz₂ : z ∉ S₂)
    (hz₃ : z ∉ S₃) {y₁ y₂ y₃ y₁₂ y₁₃ y₂₃ y₁₂₃ : ι} (hy₁ : y₁ ∈ S₁) (hy₂ : y₂ ∈ S₂)
    (hy₃ : y₃ ∈ S₃) (hy₁₂ : y₁₂ ∈ symmDiff S₁ S₂) (hy₁₃ : y₁₃ ∈ symmDiff S₁ S₃)
    (hy₂₃ : y₂₃ ∈ symmDiff S₂ S₃) (hy₁₂₃ : y₁₂₃ ∈ symmDiff (symmDiff S₁ S₂) S₃) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hSO : ∀ S ∈ [S₁, S₂, S₃],
      signEquiv c S ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q := fun S hS =>
    TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.2
      ⟨(TauCeti.QuadraticMap.mem_orthogonalGroup_iff_polar (IsSMulRegular.of_ne_zero h2)).2
        fun x y => signEquiv_preserves Q.polarBilin c (fun i j h => hsat S hS i j (hB i j h)) x y,
        Units.ext (by rw [det_signEquiv, (hev S hS).neg_one_pow]; rfl)⟩
  have hC : ∀ S ∈ [S₁, S₂, S₃], signEquiv c S ∈ Subgroup.centralizer {A} := fun S hS =>
    signEquiv_mem_centralizer c fun i j h => hsat S hS i j (congrArg blk
      (eq_of_toMatrix_ne_zero c (T := (A : V →ₗ[K] V)) hA h))
  exact exists_four_of_signSystem hK hQ (signEquiv c) (signEquiv_empty c) (signEquiv_mul c)
    (fun S i hi j hj => notScalar_signEquiv h2 c hi hj) (hSO _ (by simp)) (hSO _ (by simp))
    (hSO _ (by simp)) (hC _ (by simp)) (hC _ (by simp)) (hC _ (by simp)) hz₁ hz₂ hz₃ hy₁ hy₂ hy₃
    hy₁₂ hy₁₃ hy₂₃ hy₁₂₃

theorem exists_four_of_diagonal [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : Q.polarBilin.Nondegenerate) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Basis ι K V) (h5 : 5 ≤ Fintype.card ι)
    (hB : ∀ i j, Q.polarBilin (c i) (c j) ≠ 0 → i = j) (hA : ∀ j, ∃ l : K, A (c j) = l • c j) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  let x : Fin 5 ↪ ι := (Fin.castLEEmb h5).trans (Fintype.equivFin ι).symm.toEmbedding
  have hx : ∀ a b : Fin 5, x a = x b ↔ a = b := fun a b => x.injective.eq_iff
  have hev : ∀ k : Fin 5, k ≠ 0 → Even ({x 0, x k} : Finset ι).card := fun k hk => by
    rw [Finset.card_pair (by rw [Ne, hx]; exact hk.symm)]
    exact even_two
  refine exists_four_of_blocks hK hQ c id hB hA (S₁ := {x 0, x 1}) (S₂ := {x 0, x 2})
    (S₃ := {x 0, x 3}) (fun S _ i j (h : i = j) => by rw [h]) ?_ (z := x 4) ?_ ?_ ?_
    (y₁ := x 0) (y₂ := x 0) (y₃ := x 0) (y₁₂ := x 1) (y₁₃ := x 1) (y₂₃ := x 2) (y₁₂₃ := x 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl
    · exact hev 1 (by decide)
    · exact hev 2 (by decide)
    · exact hev 3 (by decide)
  all_goals simp [Finset.mem_symmDiff, hx]

theorem exists_four_split_orthogonal [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : Q.polarBilin.Nondegenerate) (hd : 5 ≤ finrank K V) {b : K} {Vp Vm : Submodule K V}
    (hc : IsCompl Vp Vm) (hAp : ∀ v ∈ Vp, A v = b • v) (hAm : ∀ v ∈ Vm, A v = (-b) • v)
    (horth : ∀ x ∈ Vp, ∀ y ∈ Vm, Q.polarBilin x y = 0) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  have : Invertible (2 : K) := invertibleOfNonzero (Ring.two_ne_zero hK)
  have hsym : LinearMap.BilinForm.IsSymm Q.polarBilin := ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  obtain ⟨bp, hbp⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.1 (hsym.restrict Vp))
  obtain ⟨bm, hbm⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.1 (hsym.restrict Vm))
  let c := (bp.prod bm).map (Submodule.prodEquivOfIsCompl Vp Vm hc)
  have hcl : ∀ i, c (Sum.inl i) = (bp i : V) := fun i => by
    simp [c, Submodule.coe_prodEquivOfIsCompl']
  have hcr : ∀ j, c (Sum.inr j) = (bm j : V) := fun j => by
    simp [c, Submodule.coe_prodEquivOfIsCompl']
  refine exists_four_of_diagonal hK hQ c ?_ ?_ ?_
  · rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
      Submodule.finrank_add_eq_of_isCompl hc]
    exact hd
  · rintro (i | i) (j | j) h
    · rw [hcl, hcl] at h
      rcases eq_or_ne i j with rfl | hne
      · rfl
      · exact absurd (hbp hne) h
    · rw [hcl, hcr, horth _ (bp i).2 _ (bm j).2] at h
      exact absurd rfl h
    · rw [hcr, hcl, ← hsym.eq, horth _ (bp j).2 _ (bm i).2] at h
      exact absurd rfl h
    · rw [hcr, hcr] at h
      rcases eq_or_ne i j with rfl | hne
      · rfl
      · exact absurd (hbm hne) h
  · rintro (i | j)
    · exact ⟨b, by rw [hcl]; exact hAp _ (bp i).2⟩
    · exact ⟨-b, by rw [hcr]; exact hAm _ (bm j).2⟩

theorem mem_pair_iff {m : ℕ} (k : Fin m) (i : Fin m ⊕ Fin m) :
    i ∈ ({Sum.inl k, Sum.inr k} : Finset (Fin m ⊕ Fin m)) ↔ Sum.elim id id i = k := by
  rcases i with i | i <;> simp [eq_comm]

theorem exists_four_paired_orthogonal [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : Q.polarBilin.Nondegenerate) {b : K} {Vp Vm : Submodule K V} (hc : IsCompl Vp Vm)
    (hm : 4 ≤ finrank K Vp) (hAp : ∀ v ∈ Vp, A v = b • v) (hAm : ∀ v ∈ Vm, A v = (-b) • v)
    (hQp : ∀ x ∈ Vp, Q x = 0) (hQm : ∀ y ∈ Vm, Q y = 0)
    (hperf : (crossPairing Q.polarBilin Vp Vm).IsPerfPair) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  have hBp : ∀ x ∈ Vp, ∀ y ∈ Vp, Q.polarBilin x y = 0 := fun x hx y hy => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hQp _ (Vp.add_mem hx hy),
      hQp _ hx, hQp _ hy, sub_zero, sub_zero]
  have hBm : ∀ x ∈ Vm, ∀ y ∈ Vm, Q.polarBilin x y = 0 := fun x hx y hy => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hQm _ (Vm.add_mem hx hy),
      hQm _ hx, hQm _ hy, sub_zero, sub_zero]
  have hsym : ∀ x y, Q.polarBilin x y = Q.polarBilin y x := fun x y =>
    QuadraticMap.polar_comm Q x y
  let ep := Module.finBasis K Vp
  let φ : Vm ≃ₗ[K] Module.Dual K Vp :=
    LinearEquiv.ofBijective (crossPairing Q.polarBilin Vp Vm).flip hperf.bijective_right
  let fm : Basis (Fin (finrank K Vp)) K Vm := ep.dualBasis.map φ.symm
  have hφ : ∀ (y : Vm) (x : Vp), φ y x = Q.polarBilin x y := fun _ _ => rfl
  have hpair : ∀ i j, Q.polarBilin (ep i : V) (fm j : V) = if i = j then 1 else 0 := fun i j => by
    rw [← hφ, show fm j = φ.symm (ep.dualBasis j) from Basis.map_apply _ _ _,
      LinearEquiv.apply_symm_apply, Basis.dualBasis_apply_self]
  let c := (ep.prod fm).map (Submodule.prodEquivOfIsCompl Vp Vm hc)
  have hcl : ∀ i, c (Sum.inl i) = (ep i : V) := fun i => by
    simp [c, Submodule.coe_prodEquivOfIsCompl']
  have hcr : ∀ j, c (Sum.inr j) = (fm j : V) := fun j => by
    simp [c, Submodule.coe_prodEquivOfIsCompl']
  have hpij : ∀ i j, Q.polarBilin (ep i : V) (fm j : V) ≠ 0 → i = j := fun i j h => by
    rw [hpair] at h
    by_contra hij
    simp [hij] at h
  let k : ℕ → Fin (finrank K Vp) := fun r => ⟨r % finrank K Vp, Nat.mod_lt _ (by omega)⟩
  have hk : ∀ r s, r < 4 → s < 4 → (k r = k s ↔ r = s) := fun r s hr hs => by
    simp only [k, Fin.ext_iff, Nat.mod_eq_of_lt (show r < finrank K Vp by omega),
      Nat.mod_eq_of_lt (show s < finrank K Vp by omega)]
  have hev2 : ∀ r, Even ({Sum.inl (k r), Sum.inr (k r)} : Finset (_ ⊕ _)).card := fun r => by
    rw [Finset.card_pair Sum.inl_ne_inr]
    exact even_two
  refine exists_four_of_blocks hK hQ c (Sum.elim id id) ?_ ?_
    (S₁ := {Sum.inl (k 0), Sum.inr (k 0)}) (S₂ := {Sum.inl (k 1), Sum.inr (k 1)})
    (S₃ := {Sum.inl (k 2), Sum.inr (k 2)}) ?_ ?_ (z := Sum.inl (k 3)) ?_ ?_ ?_
    (y₁ := Sum.inl (k 0)) (y₂ := Sum.inl (k 1)) (y₃ := Sum.inl (k 2)) (y₁₂ := Sum.inl (k 0))
    (y₁₃ := Sum.inl (k 0)) (y₂₃ := Sum.inl (k 1)) (y₁₂₃ := Sum.inl (k 0)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro (i | i) (j | j) h
    · rw [hcl, hcl, hBp _ (ep i).2 _ (ep j).2] at h
      exact absurd rfl h
    · rw [hcl, hcr] at h
      exact hpij i j h
    · rw [hcr, hcl, hsym] at h
      exact (hpij j i h).symm
    · rw [hcr, hcr, hBm _ (fm i).2 _ (fm j).2] at h
      exact absurd rfl h
  · rintro (i | j)
    · exact ⟨b, by rw [hcl]; exact hAp _ (ep i).2⟩
    · exact ⟨-b, by rw [hcr]; exact hAm _ (fm j).2⟩
  · intro S hS i j h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl <;> rw [mem_pair_iff, mem_pair_iff, h]
  · intro S hS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl <;> exact hev2 _
  all_goals simp [Finset.mem_symmDiff, hk]

end Systems

section Field

variable {Q : QuadraticForm K V} {A : V ≃ₗ[K] V}

theorem two_ne_zero_of_algebra (hK : ringChar K ≠ 2) {E : Type*} [Field E] [Algebra K E] :
    (2 : E) ≠ 0 := by
  rw [← map_ofNat (algebraMap K E) 2]
  exact (map_ne_zero (algebraMap K E)).2 (Ring.two_ne_zero hK)

theorem exists_four_field_signs [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : Q.polarBilin.Nondegenerate) {E : Type*} [Field E] [Algebra K E] [Module E V]
    [IsScalarTower K E V] (hE : finrank K E = 2) {m : ℕ} (hm : 4 ≤ m) (c : Basis (Fin m) E V)
    {G : Subgroup (V ≃ₗ[E] V)} (hG : ∀ S, signEquiv c S ∈ G)
    (e : orthogonalOperatorCentralizer Q A.toLinearMap ≃* G)
    (he : ∀ g x, (e.symm g).val.val x = g.val x) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  have h2E : (2 : E) ≠ 0 := two_ne_zero_of_algebra hK
  let t : Finset (Fin m) → V ≃ₗ[K] V := fun S => (e.symm ⟨signEquiv c S, hG S⟩).val.val
  have ht : ∀ S x, t S x = signEquiv c S x := fun S x => he _ x
  have hO : ∀ S, t S ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun S =>
    (e.symm ⟨signEquiv c S, hG S⟩).val.prop
  have hC : ∀ S, t S ∈ Subgroup.centralizer {A} := fun S => by
    refine Subgroup.mem_centralizer_singleton_iff.2 (LinearEquiv.ext fun x => ?_)
    have hc : ∀ y, t S (A.toLinearMap y) = A.toLinearMap (t S y) :=
      (e.symm ⟨signEquiv c S, hG S⟩).prop
    exact hc x
  have hdet : ∀ S, LinearEquiv.det (t S) = 1 := fun S => by
    refine Units.ext ?_
    have hl : (t S : V →ₗ[K] V) = ((signEquiv c S : V ≃ₗ[E] V) : V →ₗ[E] V).restrictScalars K :=
      LinearMap.ext (ht S)
    rw [LinearEquiv.coe_det, Units.val_one, hl, LinearMap.det_restrictScalars,
      ← LinearEquiv.coe_det, det_signEquiv,
      show ((-1 : E) ^ S.card) = algebraMap K E ((-1) ^ S.card) by simp,
      Algebra.norm_algebraMap, hE, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hns : ∀ S : Finset (Fin m), ∀ i ∈ S, ∀ j ∉ S, NotScalar (t S) := fun S i hi j hj a h =>
    notScalar_signEquiv h2E c hi hj (algebraMap K E a) (LinearMap.ext fun x => by
      have hx := LinearMap.congr_fun h x
      simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply] at hx
      rw [LinearEquiv.coe_coe, ← ht, hx, LinearMap.smul_apply, LinearMap.id_apply,
        algebraMap_smul])
  let k : ℕ → Fin m := fun r => ⟨r % m, Nat.mod_lt _ (by omega)⟩
  have hk : ∀ r s, r < 4 → s < 4 → (k r = k s ↔ r = s) := fun r s hr hs => by
    simp only [k, Fin.ext_iff, Nat.mod_eq_of_lt (show r < m by omega),
      Nat.mod_eq_of_lt (show s < m by omega)]
  have hSO : ∀ S, t S ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q := fun S =>
    TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.2 ⟨hO S, hdet S⟩
  refine exists_four_of_signSystem hK hQ t ?_ ?_ hns (S₁ := {k 0}) (S₂ := {k 1}) (S₃ := {k 2})
    (hSO _) (hSO _) (hSO _) (hC _) (hC _) (hC _) (z := k 3) ?_ ?_ ?_ (y₁ := k 0) (y₂ := k 1)
    (y₃ := k 2) (y₁₂ := k 0) (y₁₃ := k 0) (y₂₃ := k 1) (y₁₂₃ := k 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact LinearEquiv.ext fun x => by rw [ht, signEquiv_empty]; rfl
  · intro S T
    refine LinearEquiv.ext fun x => ?_
    change t S (t T x) = t (symmDiff S T) x
    rw [ht, ht, ht, ← signEquiv_mul]
    rfl
  all_goals simp [Finset.mem_symmDiff, hk]

theorem exists_four_field_orthogonal [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : Q.polarBilin.Nondegenerate) {E : Type*} [Field E] [Algebra K E] [Module E V]
    [IsScalarTower K E V] [FiniteDimensional E V] (hE : finrank K E = 2) (hm : 4 ≤ finrank E V)
    {QE : QuadraticForm E V} {BE : LinearMap.BilinForm E V} (hBE : BE.IsSymm)
    (hQE : QE.polarBilin = BE)
    (e : orthogonalOperatorCentralizer Q A.toLinearMap ≃* TauCeti.QuadraticMap.orthogonalGroup QE)
    (he : ∀ g x, (e.symm g).val.val x = g.val x) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  have h2E : (2 : E) ≠ 0 := two_ne_zero_of_algebra hK
  have : Invertible (2 : E) := invertibleOfNonzero h2E
  obtain ⟨ob, hob⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.1 hBE)
  refine exists_four_field_signs hK hQ hE hm ob (fun S => ?_) e he
  refine (TauCeti.QuadraticMap.mem_orthogonalGroup_iff_polar (IsSMulRegular.of_ne_zero h2E)).2
    fun x y => ?_
  have hS : ∀ i j, BE (ob i) (ob j) ≠ 0 → (i ∈ S ↔ j ∈ S) := fun i j hij => by
    rcases eq_or_ne i j with rfl | hne
    · rfl
    · exact absurd (hob hne) hij
  have := signEquiv_preserves BE ob hS x y
  rw [← hQE] at this
  exact this

theorem exists_orthonormal_of_eq_pow {E : Type*} [Field E] {W : Type*} [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] {ℓ f : ℕ} (hUF : UnitaryFieldData ℓ f E)
    {τ : E →+* E} (hτ : ∀ z, τ z = z ^ (ℓ ^ f)) (h : W →ₛₗ[τ] W →ₗ[E] E) (hs : h.IsSymm)
    (hl : h.SeparatingLeft) :
    ∃ ob : Basis (Fin (finrank E W)) E W, ∀ i j, h (ob i) (ob j) = if i = j then 1 else 0 := by
  have hb : τ = hUF.bar := RingHom.ext fun z => by rw [hτ, hUF.bar_apply]
  subst hb
  exact hUF.exists_orthonormal_basis hs hl

theorem exists_four_field_unitary [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    (hQ : Q.polarBilin.Nondegenerate) {E : Type*} [Field E] [Algebra K E] [Module E V]
    [IsScalarTower K E V] [FiniteDimensional E V] (hE : finrank K E = 2) (hm : 4 ≤ finrank E V)
    {ℓ f : ℕ} (hUF : UnitaryFieldData ℓ f E) {sigma : E ≃+* E}
    {h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E} (hs : h.IsSymm) (hn : h.Nondegenerate)
    (e : orthogonalOperatorCentralizer Q A.toLinearMap ≃* CatalogueBUnitaryIsometry.isometryGroup h)
    (he : ∀ g x, (e.symm g).val.val x = g.val x) (hsig : ∀ z, sigma z = z ^ (ℓ ^ f)) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  obtain ⟨ob, hob⟩ := exists_orthonormal_of_eq_pow hUF (τ := sigma.toRingHom) hsig h hs hn.1
  refine exists_four_field_signs hK hQ hE hm ob (fun S =>
    (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h _).2 fun x y =>
      signEquiv_preserves_sesq h ob (fun i j hij => ?_) x y) e he
  rcases eq_or_ne i j with rfl | hne
  · rfl
  · exact absurd ((hob i j).trans (by simp [hne])) hij

end Field

theorem odd_orthogonal_scalar_square_centralizer_projective_four_group [Finite K]
    (hK : ringChar K ≠ 2) [FiniteDimensional K V] (hd : 7 ≤ finrank K V)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (a μ : Kˣ)
    (hsq : ∀ x, A (A x) = (a : K) • x)
    (hsim : ∀ x y, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hns : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    ∃ W : Subgroup (OrthogonalProj Q),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨n, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK' : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨hε, -, hsqcase, hnscase⟩ := scalar_square_centralizer_structure (ringChar K) n hℓ hK
    n.pos hK' (by omega) Q hQ A a μ hsq hsim hns
  by_cases hsqa : IsSquare (a : K)
  · obtain ⟨b, hb⟩ := hsqa
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hb
      exact a.ne_zero hb
    obtain ⟨hc, -, -, h1, h2⟩ := hsqcase (Units.mk0 b hb0) (by rw [Units.val_mk0, hb, pow_two])
    have hAp : ∀ v ∈ positiveSquareKernel A ((Units.mk0 b hb0 : Kˣ) : K), A v = b • v :=
      fun v hv => apply_of_mem_positiveSquareKernel hb0 hv
    have hAm : ∀ v ∈ negativeSquareKernel A ((Units.mk0 b hb0 : Kˣ) : K), A v = (-b) • v :=
      fun v hv => apply_of_mem_negativeSquareKernel hb0 hv
    rcases hε with hε | hε
    · obtain ⟨horth, -, -, -⟩ := h1 hε
      exact exists_four_split_orthogonal hK hQ (by omega) hc hAp hAm horth
    · obtain ⟨hQp, hQm, hperf, hpm, -, -, -⟩ := h2 hε
      have := Submodule.finrank_add_eq_of_isCompl hc
      exact exists_four_paired_orthogonal hK hQ hc (by omega) hAp hAm hQp hQm hperf
  · let _ : Field (scalarAlgebra A.toLinearMap) :=
      scalarField A.toLinearMap (a : K) hsqa (original_endomorphism_square A (a : K) hsq)
    let _ : Module (scalarAlgebra A.toLinearMap) V := evaluationModule A.toLinearMap
    obtain ⟨⟨-, -, -, -, -, -, -, hrk2, hcardE, -, -, -, -, -, hconj, -, -, -, hST, hFin, hfr, -⟩,
      hc1, hc2⟩ := hnscase hsqa
    have hmE : 4 ≤ finrank (scalarAlgebra A.toLinearMap) V := by omega
    rcases hε with hε | hε
    · obtain ⟨hBEs, -, hQEB, -, -, -, e, -, he, -, -⟩ := hc1 hε
      exact exists_four_field_orthogonal hK hQ hrk2 hmE hBEs hQEB e he
    · obtain ⟨hhs, hhn, -, -, -, -, e, -, he, -, -⟩ := hc2 hε
      have hUF : UnitaryFieldData (ringChar K) n (scalarAlgebra A.toLinearMap) :=
        ⟨hℓ, n.pos, by rw [hcardE, ← pow_mul, mul_comm]⟩
      exact exists_four_field_unitary hK hQ hrk2 hmE hUF hhs hhn e he hconj

end CLSFourGroupScalarSquare

end CFSG.LocalAnalysis.ComponentInitial
