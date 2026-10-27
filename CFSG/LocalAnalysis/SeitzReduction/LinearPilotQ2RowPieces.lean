module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowUnique

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open scoped commutatorElement

section Matrices

variable {n : ℕ} {F : Type*} [Field F]

theorem entries_of_mul_single_comm {M : Matrix (Fin n) (Fin n) F} {i j : Fin n}
    (h : M * single i j (1 : F) = single i j 1 * M) :
    (∀ k, k ≠ i → M k i = 0) ∧ (∀ l, l ≠ j → M j l = 0) ∧ M i i = M j j := by
  refine ⟨fun k hk => ?_, fun l hl => ?_, ?_⟩
  · have h1 := congrFun (congrFun h k) j
    rw [mul_single_apply_same, single_mul_apply_of_ne (h := hk), mul_one] at h1
    exact h1
  · have h1 := congrFun (congrFun h i) l
    rw [mul_single_apply_of_ne (hbj := hl), single_mul_apply_same, one_mul] at h1
    exact h1.symm
  · have h1 := congrFun (congrFun h i) j
    rw [mul_single_apply_same, single_mul_apply_same, mul_one, one_mul] at h1
    exact h1

theorem entries_of_commute_transvection {A : SpecialLinearGroup (Fin n) F} {i j : Fin n}
    (hij : i ≠ j)
    (h : A * SpecialLinearGroup.transvection hij 1 = SpecialLinearGroup.transvection hij 1 * A) :
    (∀ k, k ≠ i → (A : Matrix (Fin n) (Fin n) F) k i = 0) ∧
      (∀ l, l ≠ j → (A : Matrix (Fin n) (Fin n) F) j l = 0) ∧
      (A : Matrix (Fin n) (Fin n) F) i i = (A : Matrix (Fin n) (Fin n) F) j j := by
  have h' : (A : Matrix (Fin n) (Fin n) F) * (1 + single i j (1 : F)) =
      (1 + single i j (1 : F)) * (A : Matrix (Fin n) (Fin n) F) :=
    congrArg Subtype.val h
  refine entries_of_mul_single_comm ?_
  have h2 : (A : Matrix (Fin n) (Fin n) F) * 1 + (A : Matrix (Fin n) (Fin n) F) * single i j 1 =
      1 * (A : Matrix (Fin n) (Fin n) F) + single i j 1 * (A : Matrix (Fin n) (Fin n) F) := by
    rw [← Matrix.mul_add, ← Matrix.add_mul]
    exact h'
  rw [Matrix.mul_one, Matrix.one_mul] at h2
  exact add_left_cancel h2

@[expose] def TPattern (T : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ i ∈ T, ∀ k, k ≠ i → M k i = 0 ∧ M i k = 0) ∧ ∀ i ∈ T, ∀ j ∈ T, M i i = M j j

theorem pattern_of_commute_transvections {T : Finset (Fin n)} (hT : 2 ≤ T.card)
    {A : SpecialLinearGroup (Fin n) F}
    (h : ∀ i ∈ T, ∀ j ∈ T, ∀ hij : i ≠ j,
      A * SpecialLinearGroup.transvection hij 1 = SpecialLinearGroup.transvection hij 1 * A) :
    TPattern T (A : Matrix (Fin n) (Fin n) F) := by
  refine ⟨fun i hi k hk => ?_, fun i hi j hj => ?_⟩
  · obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (s := T) (by omega) i
    exact ⟨(entries_of_commute_transvection (Ne.symm hji) (h i hi j hj (Ne.symm hji))).1 k hk,
      (entries_of_commute_transvection hji (h j hj i hi hji)).2.1 k hk⟩
  · by_cases hij : i = j
    · rw [hij]
    · exact (entries_of_commute_transvection hij (h i hi j hj hij)).2.2

theorem mul_apply_self_of_pattern {T : Finset (Fin n)} {M M' : Matrix (Fin n) (Fin n) F}
    (hM : TPattern T M) {i : Fin n} (hi : i ∈ T) : (M * M') i i = M i i * M' i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rw [(hM.1 i hi k hk).2, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coe_mul_specialLinear (A B : SpecialLinearGroup (Fin n) F) :
    ((A * B : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) :=
  rfl

theorem coe_one_specialLinear :
    ((1 : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 :=
  rfl

theorem blockSpecialLinear_inf (I J : Finset (Fin n)) :
    blockSpecialLinear (K := F) I ⊓ blockSpecialLinear J = blockSpecialLinear (I ∩ J) := by
  refine le_antisymm (fun A hA i j hij => ?_)
    (le_inf (blockSpecialLinear_mono Finset.inter_subset_left)
      (blockSpecialLinear_mono Finset.inter_subset_right))
  have hA1 := (Subgroup.mem_inf.1 hA).1
  have hA2 := (Subgroup.mem_inf.1 hA).2
  rcases hij with hi | hj
  · by_cases hiI : i ∈ I
    · exact hA2 i j (Or.inl fun h => hi (Finset.mem_inter.2 ⟨hiI, h⟩))
    · exact hA1 i j (Or.inl hiI)
  · by_cases hjI : j ∈ I
    · exact hA2 i j (Or.inr fun h => hj (Finset.mem_inter.2 ⟨hjI, h⟩))
    · exact hA1 i j (Or.inr hjI)

theorem commutator_mem_blockSpecialLinear_compl_of_pattern {T : Finset (Fin n)}
    {Q : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hQ : ∀ A ∈ Q, TPattern T (A : Matrix (Fin n) (Fin n) F))
    {a b : SpecialLinearGroup (Fin n) F} (ha : a ∈ Q) (hb : b ∈ Q) :
    ⁅a, b⁆ ∈ blockSpecialLinear (K := F) Tᶜ := by
  have hab : a * b ∈ Q := Q.mul_mem ha hb
  have haba : a * b * a⁻¹ ∈ Q := Q.mul_mem hab (Q.inv_mem ha)
  have hc : ⁅a, b⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem haba (Q.inv_mem hb)
  have hinv : ∀ x ∈ Q, ∀ k ∈ T, (x : Matrix (Fin n) (Fin n) F) k k *
      ((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k k = 1 := by
    intro x hx k hk
    rw [← mul_apply_self_of_pattern (hQ x hx) hk, ← coe_mul_specialLinear, mul_inv_cancel,
      coe_one_specialLinear, Matrix.one_apply_eq]
  have hdiag : ∀ k ∈ T,
      ((⁅a, b⁆ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k k = 1 := by
    intro k hk
    rw [commutatorElement_def, coe_mul_specialLinear,
      mul_apply_self_of_pattern (hQ _ haba) hk, coe_mul_specialLinear,
      mul_apply_self_of_pattern (hQ _ hab) hk, coe_mul_specialLinear,
      mul_apply_self_of_pattern (hQ _ ha) hk]
    calc (a : Matrix (Fin n) (Fin n) F) k k * (b : Matrix (Fin n) (Fin n) F) k k *
          ((a⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k k *
          ((b⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k k
        = ((a : Matrix (Fin n) (Fin n) F) k k *
            ((a⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k k) *
          ((b : Matrix (Fin n) (Fin n) F) k k *
            ((b⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k k) := by ring
      _ = 1 := by rw [hinv a ha k hk, hinv b hb k hk, mul_one]
  intro i j hij
  rcases hij with hi | hj
  · have hi : i ∈ T := by simpa using hi
    by_cases hji : j = i
    · rw [hji, hdiag i hi, Matrix.one_apply_eq]
    · rw [((hQ _ hc).1 i hi j hji).2, Matrix.one_apply_ne (Ne.symm hji)]
  · have hj : j ∈ T := by simpa using hj
    by_cases hij : i = j
    · rw [hij, hdiag j hj, Matrix.one_apply_eq]
    · rw [((hQ _ hc).1 j hj i hij).1, Matrix.one_apply_ne hij]

theorem le_blockSpecialLinear_sdiff_of_commute {N T : Finset (Fin n)} (hT : 2 ≤ T.card)
    {Q : Subgroup (SpecialLinearGroup (Fin n) F)} (hQN : Q ≤ blockSpecialLinear N)
    (hperf : ⁅Q, Q⁆ = Q)
    (hcomm : ∀ A ∈ Q, ∀ i ∈ T, ∀ j ∈ T, ∀ hij : i ≠ j,
      A * SpecialLinearGroup.transvection hij 1 = SpecialLinearGroup.transvection hij 1 * A) :
    Q ≤ blockSpecialLinear (N \ T) := by
  have hpat : ∀ A ∈ Q, TPattern T (A : Matrix (Fin n) (Fin n) F) := fun A hA =>
    pattern_of_commute_transvections hT (hcomm A hA)
  have h1 : Q ≤ blockSpecialLinear (K := F) Tᶜ := by
    rw [← hperf, Subgroup.commutator_le]
    intro a ha b hb
    exact commutator_mem_blockSpecialLinear_compl_of_pattern hpat ha hb
  rw [Finset.sdiff_eq_inter_compl, ← blockSpecialLinear_inf]
  exact le_inf hQN h1

end Matrices

theorem le_centralizer_of_commutator_le_center_of_perfect {H : Type*} [Group H]
    {C J : Subgroup H} (hC : ⁅C, C⁆ = C) (hCJ : ⁅C, J⁆ ≤ center H) :
    C ≤ centralizer (J : Set H) := by
  have hZC : ⁅center H, C⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [mem_centralizer_iff]
    intro c _
    exact mem_center_iff.1 hz c
  have h1 : ⁅⁅C, J⁆, C⁆ = ⊥ := eq_bot_iff.2 ((commutator_mono hCJ le_rfl).trans hZC.le)
  have h2 : ⁅⁅J, C⁆, C⁆ = ⊥ := by rw [commutator_comm J C]; exact h1
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hC] at h3
  exact commutator_eq_bot_iff_le_centralizer.1 h3

section Pieces

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  {F : Type*} [Field F] [Finite F]

omit [Finite F] in
theorem map_transvection_one (ι : K →+* F) {i j : Fin n} (hij : i ≠ j) :
    SpecialLinearGroup.map ι (SpecialLinearGroup.transvection hij (1 : K)) =
      SpecialLinearGroup.transvection hij (1 : F) := by
  ext k l
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  change ι ((1 + single i j (1 : K)) k l) = (1 + single i j (1 : F)) k l
  rw [Matrix.add_apply, Matrix.add_apply, map_add, single_apply, single_apply]
  by_cases hkl : k = l
  · subst hkl
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    split_ifs <;> simp
  · rw [Matrix.one_apply_ne hkl, Matrix.one_apply_ne hkl, map_zero]
    split_ifs <;> simp

theorem complPieceCore_le_map_of_fieldNeighbourParam {e : L ≃* LinearFlag.projectiveSL n K}
    {t : G} {ι : K →+* F} {σ : F ≃+* F} {X : Subgroup G} {N : Finset (Fin n)}
    (P : FieldNeighbourParam e t ι σ X N) {A : Finset (Fin n)} (hAN : A ⊆ N)
    (hXA : X ≤ modelToG e (blockSL (K := K) Aᶜ)) (hT : 2 ≤ (N \ A).card) :
    complPieceCore e A ≤
      ((blockSpecialLinear (K := F) A).subgroupOf (blockSpecialLinear N)).map P.Φ := by
  set H := blockSpecialLinear (K := F) N with hH
  set R := complPieceCore e A with hR
  have hRX : R ≤ P.Φ.range := by
    rw [P.range_eq]
    exact F4Pilot.centralizerPerfectCore_anti hXA
  set Q : Subgroup H := perfectCore (R.comap P.Φ) with hQ
  have hQR : Q.map P.Φ = R := by
    rw [hQ, CFSG.Quasithin.map_perfectCore, Subgroup.map_comap_eq, inf_eq_right.2 hRX,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect (commutator_complPieceCore e A)]
  have hQperf : ⁅Q, Q⁆ = Q := CFSG.Quasithin.perfectCore_perfect _
  set T := N \ A with hTdef
  have hTN : T ⊆ N := Finset.sdiff_subset
  have hTA : ∀ i ∈ T, i ∈ Aᶜ := fun i hi => Finset.mem_compl.2 (Finset.mem_sdiff.1 hi).2
  let y : ∀ i j : Fin n, i ∈ T → j ∈ T → i ≠ j → H := fun i j hi hj hij =>
    ⟨SpecialLinearGroup.transvection hij 1,
      transvection_mem_blockSpecialLinear hij (hTN hi) (hTN hj) 1⟩
  set S : Set H :=
    {z | ∃ (i j : Fin n) (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j), z = y i j hi hj hij}
    with hS
  have hSΦ : closure S ≤ (modelToG e (blockSL (K := K) Aᶜ)).comap P.Φ := by
    rw [closure_le]
    rintro _ ⟨i, j, hi, hj, hij, rfl⟩
    have hxK : SpecialLinearGroup.transvection hij (1 : K) ∈ blockSpecialLinear (K := K) N :=
      transvection_mem_blockSpecialLinear hij (hTN hi) (hTN hj) 1
    have h1 := P.N1 ⟨SpecialLinearGroup.transvection hij (1 : K), hxK⟩
    have hyeq : (⟨SpecialLinearGroup.map ι (SpecialLinearGroup.transvection hij (1 : K)),
        map_ringHom_mem_blockSpecialLinear ι hxK⟩ : H) = y i j hi hj hij :=
      Subtype.ext (map_transvection_one ι hij)
    rw [hyeq] at h1
    change P.Φ (y i j hi hj hij) ∈ modelToG e (blockSL (K := K) Aᶜ)
    rw [h1]
    exact symm_mem_modelToG e (proj_mem_blockSL
      (transvection_mem_blockSpecialLinear hij (hTA i hi) (hTA j hj) 1))
  have hQJ : Q ≤ centralizer (closure S : Set H) := by
    refine le_centralizer_of_commutator_le_center_of_perfect hQperf ?_
    rw [Subgroup.commutator_le]
    intro q hq z hz
    refine P.ker_le ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have hqR : P.Φ q ∈ R := by
      rw [← hQR]
      exact mem_map_of_mem _ hq
    exact (mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ hqR)
      (P.Φ z) (hSΦ hz)).symm
  have hQ' : Q.map H.subtype ≤ blockSpecialLinear (K := F) A := by
    have hle := le_blockSpecialLinear_sdiff_of_commute (N := N) hT (Q := Q.map H.subtype)
      (map_subtype_le _) (by rw [← map_commutator, hQperf]) (by
        rintro _ ⟨q, hq, rfl⟩ i hi j hj hij
        have h1 := mem_centralizer_iff.1 (hQJ hq) (y i j hi hj hij)
          (subset_closure ⟨i, j, hi, hj, hij, rfl⟩)
        exact (congrArg Subtype.val h1).symm)
    rwa [Finset.sdiff_sdiff_eq_self hAN] at hle
  rw [← hQR]
  refine map_mono fun q hq => ?_
  rw [mem_subgroupOf]
  exact hQ' (mem_map_of_mem _ hq)

theorem complPieceCore_eq_map_of_le_centralizer {e : L ≃* LinearFlag.projectiveSL n K}
    {t : G} {ι : K →+* F} {σ : F ≃+* F} {X : Subgroup G} {N : Finset (Fin n)}
    (P : FieldNeighbourParam e t ι σ X N) {A : Finset (Fin n)} (hAN : A ⊆ N)
    (hXA : X ≤ modelToG e (blockSL (K := K) Aᶜ)) (hT : 2 ≤ (N \ A).card)
    (hA : ⁅blockSpecialLinear (K := F) A, blockSpecialLinear (K := F) A⁆ =
      blockSpecialLinear (K := F) A)
    (hrev : ((blockSpecialLinear (K := F) A).subgroupOf (blockSpecialLinear N)).map P.Φ ≤
      centralizer (modelToG e (blockSL (K := K) Aᶜ) : Set G)) :
    complPieceCore e A =
      ((blockSpecialLinear (K := F) A).subgroupOf (blockSpecialLinear N)).map P.Φ :=
  le_antisymm (complPieceCore_le_map_of_fieldNeighbourParam P hAN hXA hT)
    (le_complPieceCore e (by
      rw [← map_commutator, commutator_subgroupOf_eq_self (blockSpecialLinear_mono hAN) hA])
      hrev)

end Pieces
