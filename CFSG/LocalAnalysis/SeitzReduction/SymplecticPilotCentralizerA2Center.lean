module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerA2

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

section RightMul

variable {m : ℕ}

theorem mat_mul_siegPair_apply {i j : Fin m} (hij : i ≠ j) (c : K) (g : StatedSp m K)
    (r : Fin m ⊕ Fin m) :
    mat m K (g * siegPair K i j c) r (Sum.inr i) =
      mat m K g r (Sum.inr i) + c * mat m K g r (Sum.inl j) := by
  rw [map_mul, mat_siegPair, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.add_apply, Matrix.single_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
  · simp [hij, Ne.symm hij]
    ring
  · intro b _ hb
    simp [hb]
  · simp
  · intro b _ hb
    have : ¬(i = b ∧ j = i) := fun h => hij h.2.symm
    simp [Ne.symm hb, this]
  · simp

theorem mat_mul_leviTv_apply {i j : Fin m} (hij : i ≠ j) (c : K) (g : StatedSp m K)
    (r : Fin m ⊕ Fin m) :
    mat m K (g * leviTv K hij c) r (Sum.inr i) =
      mat m K g r (Sum.inr i) - c * mat m K g r (Sum.inr j) := by
  rw [map_mul, mat_leviTv, coe_transvectionUnit_inv_transpose, Matrix.mul_apply,
    Fintype.sum_sum_type]
  simp only [fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply]
  rw [Finset.sum_eq_add i j hij]
  · simp [Ne.symm hij]
    ring
  · intro b _ hb
    have h1 : ¬ b = i := hb.1
    have h2 : ¬ (j = b) := fun h => hb.2 h.symm
    simp [h1, h2]
  · simp
  · simp

end RightMul

section Center

variable (K n) in
@[expose] def wCenter : Subgroup (StatedSp (n + 3) K) :=
  (center (wRadical K (1 : Fin (n + 3)) 2)).map (wRadical K (1 : Fin (n + 3)) 2).subtype

theorem mem_wCenter_iff {x : StatedSp (n + 3) K} :
    x ∈ wCenter K n ↔ x ∈ wRadical K (1 : Fin (n + 3)) 2 ∧
      ∀ y ∈ wRadical K (1 : Fin (n + 3)) 2, x * y = y * x := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, fun y hy => ?_⟩
    exact congrArg Subtype.val ((mem_center_iff.1 hx ⟨y, hy⟩).symm)
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, mem_center_iff.2 fun y => Subtype.ext (h y y.2).symm, rfl⟩

theorem rows_eq_zero_of_mem_wCenter {x : StatedSp (n + 3) K} (hx : x ∈ wCenter K n) :
    ∀ t, OffPQ (1 : Fin (n + 3)) 2 t →
      mat (n + 3) K x (Sum.inl 1) t = 0 ∧ mat (n + 3) K x (Sum.inl 2) t = 0 := by
  have h12 := one_ne_two_fin (n := n)
  obtain ⟨-, hcomm⟩ := mem_wCenter_iff.1 hx
  have hl1 : (Sum.inl 1 : Fin (n + 3) ⊕ Fin (n + 3)) ≠ Sum.inl 2 :=
    fun h => h12 (Sum.inl_injective h)
  intro t ht
  rcases t with j | j
  · have hj1 : j ≠ 1 := fun h => ht.1 (h ▸ inl_mem_coords _)
    have hj2 : j ≠ 2 := fun h => ht.2 (h ▸ inl_mem_coords _)
    constructor
    · have e := congrArg (fun g => mat (n + 3) K g (Sum.inl 1) (Sum.inr 2))
        (hcomm _ (siegPair_mem_wRadical (j := j) (Or.inr rfl) (1 : K)))
      rw [mat_mul_siegPair_apply (Ne.symm hj2), mat_siegPair_mul_apply_of_ne _ _ hl1
        (fun h => hj1 (Sum.inl_injective h).symm)] at e
      linear_combination e
    · have e := congrArg (fun g => mat (n + 3) K g (Sum.inl 2) (Sum.inr 1))
        (hcomm _ (siegPair_mem_wRadical (j := j) (Or.inl rfl) (1 : K)))
      rw [mat_mul_siegPair_apply (Ne.symm hj1), mat_siegPair_mul_apply_of_ne _ _ hl1.symm
        (fun h => hj2 (Sum.inl_injective h).symm)] at e
      linear_combination e
  · have hj1 : j ≠ 1 := fun h => ht.1 (h ▸ inr_mem_coords _)
    have hj2 : j ≠ 2 := fun h => ht.2 (h ▸ inr_mem_coords _)
    constructor
    · have e := congrArg (fun g => mat (n + 3) K g (Sum.inl 1) (Sum.inr 2))
        (hcomm _ (leviTv_mem_wRadical h12 (Ne.symm hj2) (Or.inr rfl) hj1 hj2 (1 : K)))
      rw [mat_mul_leviTv_apply, mat_leviTv_mul_apply_of_ne _ _ _ hl1 Sum.inl_ne_inr] at e
      linear_combination -e
    · have e := congrArg (fun g => mat (n + 3) K g (Sum.inl 2) (Sum.inr 1))
        (hcomm _ (leviTv_mem_wRadical h12 (Ne.symm hj1) (Or.inl rfl) hj1 hj2 (1 : K)))
      rw [mat_mul_leviTv_apply, mat_leviTv_mul_apply_of_ne _ _ _ hl1.symm Sum.inl_ne_inr] at e
      linear_combination -e


omit [Field K] in
theorem mat_siegDiag_eq_add' {F : Type} [Field F] {m : ℕ} (i : Fin m) (c : F) :
    mat m F (siegDiag F i c) = 1 + single (Sum.inl i) (Sum.inr i) c := by
  rw [mat_siegDiag]
  ext r t
  rcases r with x | x <;> rcases t with y | y <;>
    simp [Matrix.one_apply, Matrix.single_apply, and_comm]

omit [Field K] in
theorem mat_siegPair_eq_add {F : Type} [Field F] {m : ℕ} (i j : Fin m) (c : F) :
    mat m F (siegPair F i j c) =
      1 + single (Sum.inl i) (Sum.inr j) c + single (Sum.inl j) (Sum.inr i) c := by
  rw [mat_siegPair]
  ext r t
  rcases r with x | x <;> rcases t with y | y <;>
    simp [Matrix.one_apply, Matrix.single_apply, and_comm]

theorem siegDiag_mem_wCenter {i : Fin (n + 3)} (hi : i = 1 ∨ i = 2) (c : K) :
    siegDiag K i c ∈ wCenter K n := by
  refine mem_wCenter_iff.2 ⟨siegDiag_mem_wRadical hi c, fun y hy => mat_injective ?_⟩
  have hcol : ∀ r, mat (n + 3) K y r (Sum.inl i) =
      (1 : Matrix (Fin (n + 3) ⊕ Fin (n + 3)) (Fin (n + 3) ⊕ Fin (n + 3)) K) r (Sum.inl i) := by
    rcases hi with rfl | rfl
    exacts [hy.1, hy.2.1]
  have hrow : ∀ t, mat (n + 3) K y (Sum.inr i) t =
      (1 : Matrix (Fin (n + 3) ⊕ Fin (n + 3)) (Fin (n + 3) ⊕ Fin (n + 3)) K) (Sum.inr i) t :=
    mat_inr_apply_of_col_inl hcol
  rw [map_mul, map_mul, mat_siegDiag_eq_add', Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, mul_single_of_col hcol, single_mul_of_row hrow]

theorem siegPair_mem_wCenter (c : K) : siegPair K (1 : Fin (n + 3)) 2 c ∈ wCenter K n := by
  refine mem_wCenter_iff.2 ⟨siegPair_mem_wRadical (Or.inl rfl) c, fun y hy => mat_injective ?_⟩
  rw [map_mul, map_mul, mat_siegPair_eq_add]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    mul_single_of_col hy.1, mul_single_of_col hy.2.1,
    single_mul_of_row (mat_inr_p_of_mem_wRadical hy),
    single_mul_of_row (mat_inr_q_of_mem_wRadical hy)]

theorem eq_siegel_of_mem_wCenter {x : StatedSp (n + 3) K} (hx : x ∈ wCenter K n) :
    x = siegDiag K 1 (mat (n + 3) K x (Sum.inl 1) (Sum.inr 1)) *
      siegDiag K 2 (mat (n + 3) K x (Sum.inl 2) (Sum.inr 2)) *
      siegPair K 1 2 (mat (n + 3) K x (Sum.inl 1) (Sum.inr 2)) :=
  eq_siegel_of_mem_wRadical one_ne_two_fin (mem_wCenter_iff.1 hx).1
    (rows_eq_zero_of_mem_wCenter hx)

theorem siegel_mem_suppGroup {C : Matrix (Fin (n + 3)) (Fin (n + 3)) K} (hC : Cᵀ = C)
    (hCs : ∀ x y, ¬((x = 1 ∨ x = 2) ∧ (y = 1 ∨ y = 2)) → C x y = 0) :
    upperUnipotentSp (n + 3) K hC ∈
      suppGroup {t : Fin (n + 3) ⊕ Fin (n + 3) | ¬ OffPQ 1 2 t} := by
  intro r t hrt
  simp only [Set.mem_ofPred_eq, not_not, not_and_or] at hrt
  rw [mat_upperUnipotentSp]
  have hoff : ∀ x : Fin (n + 3), (OffPQ 1 2 (Sum.inl x) ↔ x ≠ 1 ∧ x ≠ 2) ∧
      (OffPQ 1 2 (Sum.inr x) ↔ x ≠ 1 ∧ x ≠ 2) := fun x => by
    simp [OffPQ, mem_coords]
  rcases r with x | x <;> rcases t with y | y
  · simp [Matrix.one_apply]
  · rw [fromBlocks_apply₁₂, Matrix.one_apply_ne Sum.inl_ne_inr, hCs x y]
    rintro ⟨hx, hy⟩
    rcases hrt with h | h
    · exact ((hoff x).1.1 h).1 (hx.resolve_right ((hoff x).1.1 h).2)
    · exact ((hoff y).2.1 h).1 (hy.resolve_right ((hoff y).2.1 h).2)
  · simp
  · simp [Matrix.one_apply]

theorem spCompl12_le_centralizer_wCenter :
    spCompl12 K n ≤ centralizer (wCenter K n : Set (StatedSp (n + 3) K)) := by
  intro m hm
  rw [mem_centralizer_iff]
  intro x hx
  have hS : x ∈ suppGroup {t : Fin (n + 3) ⊕ Fin (n + 3) | ¬ OffPQ 1 2 t} := by
    rw [eq_siegel_of_mem_wCenter hx, siegDiag, siegDiag, siegPair, upperUnipotentSp_mul,
      upperUnipotentSp_mul]
    refine siegel_mem_suppGroup _ fun a b hab => ?_
    simp only [Matrix.add_apply, Matrix.single_apply]
    rw [not_and_or, not_or, not_or] at hab
    rcases hab with ⟨ha1, ha2⟩ | ⟨hb1, hb2⟩
    · simp [Ne.symm ha1, Ne.symm ha2]
    · simp [Ne.symm hb1, Ne.symm hb2]
  have hm' : m ∈ suppGroup ({t : Fin (n + 3) ⊕ Fin (n + 3) | ¬ OffPQ 1 2 t})ᶜ := by
    have e : ({t : Fin (n + 3) ⊕ Fin (n + 3) | ¬ OffPQ 1 2 t})ᶜ = {t | OffPQ 1 2 t} := by
      ext t
      simp
    rw [e, ← spCompl12_eq_suppGroup]
    exact hm
  exact (commute_suppGroup_compl hS hm').eq

theorem a2Levi_inf_centralizer_wCenter [CharP K 2] :
    a2Levi K n ⊓ centralizer (wCenter K n : Set (StatedSp (n + 3) K)) = spCompl12 K n := by
  have h12 := one_ne_two_fin (n := n)
  refine le_antisymm ?_ (le_inf le_sup_right spCompl12_le_centralizer_wCenter)
  rintro m ⟨hmM, hmZ⟩
  have hMC : a2Levi K n ≤
      centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} : Set (StatedSp (n + 3) K)) :=
    sup_le (by rintro _ ⟨A, rfl⟩; exact shortBlock_mem_centralizer h12 A 1)
      (spCompl12_le_centralizer_twoCentralElt n 0 1)
  have hML : a2Levi K n ≤ (leviHom h12 0 (one_ne_zero (α := K))).range :=
    sup_le (range_shortBlock_le_range_leviHom one_ne_zero)
      (spCompl12_le_range_leviHom one_ne_zero)
  have hcol : ∀ i : Fin (n + 3), (i = 1 ∨ i = 2) → ∀ r, mat (n + 3) K m r (Sum.inl i) =
      (1 : Matrix (Fin (n + 3) ⊕ Fin (n + 3)) (Fin (n + 3) ⊕ Fin (n + 3)) K) r (Sum.inl i) := by
    intro i hi
    refine mem_centralizer_siegDiag_iff.1 (mem_centralizer_singleton_iff.2 ?_)
    exact ((mem_centralizer_iff.1 hmZ) _ (siegDiag_mem_wCenter hi 1)).symm
  have hrow : ∀ i : Fin (n + 3), (i = 1 ∨ i = 2) → ∀ t, mat (n + 3) K m (Sum.inr i) t =
      (1 : Matrix (Fin (n + 3) ⊕ Fin (n + 3)) (Fin (n + 3) ⊕ Fin (n + 3)) K) (Sum.inr i) t :=
    fun i hi => mat_inr_apply_of_col_inl (hcol i hi)
  set m' : centralizer ({twoCentralElt (n + 3) 1 2 (0 : K) 1} : Set (StatedSp (n + 3) K)) :=
    ⟨m, hMC hmM⟩
  have hA : ∀ u v : Fin (n + 3), (u = 1 ∨ u = 2) → (v = 1 ∨ v = 2) →
      mat (n + 3) K m' (Sum.inl u) (Sum.inl v) =
        (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) K) u v := by
    intro u v _ hv
    change mat (n + 3) K m (Sum.inl u) (Sum.inl v) = _
    rw [hcol v hv]
    simp [Matrix.one_apply]
  have hD : ∀ u v : Fin (n + 3), (u = 1 ∨ u = 2) → (v = 1 ∨ v = 2) →
      mat (n + 3) K m' (Sum.inr u) (Sum.inr v) =
        (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) K) u v := by
    intro u v hu _
    change mat (n + 3) K m (Sum.inr u) (Sum.inr v) = _
    rw [hrow u hu]
    simp [Matrix.one_apply]
  have hm := leviHom_mem_spCompl12 (one_ne_zero (α := K)) m' hA hD
  obtain ⟨y, hy⟩ := hML hmM
  have hm'eq : m' = ⟨leviHom h12 0 one_ne_zero y, leviHom_mem_centralizer h12 one_ne_zero y⟩ :=
    Subtype.ext hy.symm
  have hfix : leviHom h12 0 (one_ne_zero (α := K)) m' = m := by
    rw [hm'eq, leviHom_leviHom, hy]
  rwa [hfix] at hm

theorem perfectCore_a2Levi_inf_centralizer_wCenter [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    perfectCore (a2Levi K n ⊓ centralizer (wCenter K n : Set (StatedSp (n + 3) K))) =
      spCompl12 K n := by
  rw [a2Levi_inf_centralizer_wCenter,
    CFSG.Quasithin.perfectCore_eq_self_of_perfect (commutator_spCompl12 n hK)]

theorem perfectCore_centralizer_spRep_a2_intrinsic [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    ∃ Q M S : Subgroup (StatedSp (n + 3) K), IsPGroup 2 Q ∧
      M ≤ normalizer (Q : Set (StatedSp (n + 3) K)) ∧ Disjoint Q M ∧
      perfectCore (centralizer ({spRep n .a2} : Set (StatedSp (n + 3) K))) = Q ⊔ M ∧
      (∀ N : Subgroup M, N.Normal → IsPGroup 2 N → N = ⊥) ∧
      spRep n .a2 ∈ perfectCore (centralizer ({spRep n .a2} : Set (StatedSp (n + 3) K))) ∧
      longRootSp2 K (n + 3) 0 ≤ S ∧
      S = perfectCore (M ⊓ centralizer (((center Q).map Q.subtype : Subgroup _) :
        Set (StatedSp (n + 3) K))) ∧
      Nonempty (S ≃* StatedSp (n + 1) K) := by
  have h12 := one_ne_two_fin (n := n)
  have hML : a2Levi K n ≤ (leviHom h12 0 (one_ne_zero (α := K))).range :=
    sup_le (range_shortBlock_le_range_leviHom one_ne_zero)
      (spCompl12_le_range_leviHom one_ne_zero)
  refine ⟨wRadical K (1 : Fin (n + 3)) 2, a2Levi K n, spCompl12 K n, isPGroup_wRadical h12,
    hML.trans (range_leviHom_le_normalizer_wRadical h12 one_ne_zero),
    (disjoint_wRadical_range_leviHom h12 one_ne_zero).mono_right hML, ?_,
    fun N hN hN2 => eq_bot_of_normal_of_isPGroup_a2Levi hK N hN2,
    spRep_mem_perfectCore_centralizer hK n .a2, longRootSp2_le_spCompl12 n,
    (perfectCore_a2Levi_inf_centralizer_wCenter hK).symm, ⟨(spCompl12Equiv K n).symm⟩⟩
  rw [spRep_a2_eq]
  exact (perfectCore_centralizer_a2 hK).1
end Center

section Uniform

@[expose] def spIntrinsic {G : Type*} [Group G] (κ : SpTwoCentral) (Q : Subgroup G) :
    Subgroup G :=
  match κ with
  | .b1 => ⊥
  | .a2 => (center Q).map Q.subtype
  | .c2 => ⊥

@[expose] def spLeviRank (κ : SpTwoCentral) (n : ℕ) : ℕ :=
  match κ with
  | .b1 => n + 2
  | .a2 => n + 1
  | .c2 => n + 1

theorem perfectCore_centralizer_spRep [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (κ : SpTwoCentral) :
    ∃ Q M S : Subgroup (StatedSp (n + 3) K), IsPGroup 2 Q ∧
      M ≤ normalizer (Q : Set (StatedSp (n + 3) K)) ∧ Disjoint Q M ∧
      perfectCore (centralizer ({spRep n κ} : Set (StatedSp (n + 3) K))) = Q ⊔ M ∧
      (∀ N : Subgroup M, N.Normal → IsPGroup 2 N → N = ⊥) ∧
      spRep n κ ∈ perfectCore (centralizer ({spRep n κ} : Set (StatedSp (n + 3) K))) ∧
      longRootSp2 K (n + 3) 0 ≤ S ∧
      S = perfectCore (M ⊓ centralizer (spIntrinsic κ Q : Set (StatedSp (n + 3) K))) ∧
      Nonempty (S ≃* StatedSp (spLeviRank κ n) K) := by
  have hbot : ∀ M : Subgroup (StatedSp (n + 3) K),
      M ⊓ centralizer (((⊥ : Subgroup (StatedSp (n + 3) K)) : Set (StatedSp (n + 3) K))) = M := by
    intro M
    rw [Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2 (by simp), inf_top_eq]
  cases κ with
  | b1 =>
    obtain ⟨Q, M, S, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      perfectCore_centralizer_spRep_b1 (K := K) hK n
    exact ⟨Q, M, S, h1, h2, h3, h4, h5, h6, h7, by simp only [spIntrinsic, hbot]; exact h8, h9⟩
  | a2 => exact perfectCore_centralizer_spRep_a2_intrinsic hK
  | c2 =>
    obtain ⟨Q, M, S, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      perfectCore_centralizer_spRep_c2 (K := K) (n := n) hK
    exact ⟨Q, M, S, h1, h2, h3, h4, h5, h6, h7, by simp only [spIntrinsic, hbot]; exact h8, h9⟩

end Uniform

end CFSG.SeitzReduction.SymplecticPilot
