module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabPrefix
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabTwoRuling
public import CFSG.ClassicalInvolution.Phan.PhanDn.PanelParabLe

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.ClassicalGroups.Unitary
open scoped BigOperators

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

@[expose] noncomputable def qttPrefixIdx (m : ℕ) (hm : 3 ≤ m) (i : Fin (m - 1)) : Fin (m + 1) :=
  ⟨i.val, by omega⟩

theorem qttPrefixIdx_injective (m : ℕ) (hm : 3 ≤ m) :
    Function.Injective (qttPrefixIdx (m := m) hm) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [qttPrefixIdx] using this

@[expose] noncomputable def qttTailIdx (m : ℕ) (hm : 3 ≤ m) (t : Fin 2) : Fin (m + 1) :=
  ⟨m - 1 + t.val, by omega⟩

theorem qttTailIdx_injective (m : ℕ) (hm : 3 ≤ m) :
    Function.Injective (qttTailIdx (m := m) hm) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [qttTailIdx, Fin.val_mk] at this
  omega

theorem qttPrefixIdx_ne_tailIdx (m : ℕ) (hm : 3 ≤ m) (i : Fin (m - 1)) (t : Fin 2) :
    qttPrefixIdx m hm i ≠ qttTailIdx m hm t := by
  intro h
  have := congrArg Fin.val h
  simp only [qttPrefixIdx, qttTailIdx, Fin.val_mk] at this
  have hi := i.isLt
  have ht := t.isLt
  omega

@[expose] noncomputable def qttPrefixLift (m : ℕ) (hm : 3 ≤ m) :
    (Fin (m - 1) → K) →ₗ[F] (Fin (m + 1) → K) where
  toFun x := ∑ i : Fin (m - 1), x i • Pi.single (qttPrefixIdx m hm i) (1 : K)
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_assoc, Finset.smul_sum, RingHom.id_apply]

@[expose] noncomputable def qttPrefixCoords (m : ℕ) (hm : 3 ≤ m) :
    (Fin (m + 1) → K) →ₗ[F] (Fin (m - 1) → K) where
  toFun x i := x (qttPrefixIdx m hm i)
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl

@[expose] noncomputable def qttTailLift (m : ℕ) (hm : 3 ≤ m) :
    (Fin 2 → K) →ₗ[F] (Fin (m + 1) → K) where
  toFun x := ∑ t : Fin 2, x t • Pi.single (qttTailIdx m hm t) (1 : K)
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_assoc, Finset.smul_sum, RingHom.id_apply]

@[expose] noncomputable def qttTailCoords (m : ℕ) (hm : 3 ≤ m) :
    (Fin (m + 1) → K) →ₗ[F] (Fin 2 → K) where
  toFun x t := x (qttTailIdx m hm t)
  map_add' x y := by ext t; rfl
  map_smul' c x := by ext t; rfl

theorem qttTailCoords_tailLift (m : ℕ) (hm : 3 ≤ m) (x : Fin 2 → K) :
    qttTailCoords (F := F) (K := K) m hm (qttTailLift (F := F) (K := K) m hm x) = x := by
  ext t
  change (∑ b : Fin 2, x b • Pi.single (qttTailIdx m hm b) (1 : K)) (qttTailIdx m hm t) = x t
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    have hne : qttTailIdx m hm t ≠ qttTailIdx m hm b :=
      fun h => hb ((qttTailIdx_injective m hm h).symm)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem qttPrefixCoords_prefixLift (m : ℕ) (hm : 3 ≤ m) (x : Fin (m - 1) → K) :
    qttPrefixCoords (F := F) (K := K) m hm (qttPrefixLift (F := F) (K := K) m hm x) = x := by
  ext i
  change (∑ b : Fin (m - 1), x b • Pi.single (qttPrefixIdx m hm b) (1 : K))
    (qttPrefixIdx m hm i) = x i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have hne : qttPrefixIdx m hm i ≠ qttPrefixIdx m hm b :=
      fun h => hb ((qttPrefixIdx_injective m hm h).symm)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem qttTailLift_apply_prefix (m : ℕ) (hm : 3 ≤ m) (x : Fin 2 → K)
    (i : Fin (m + 1)) (hi : i.val < m - 1) :
    qttTailLift (F := F) (K := K) m hm x i = 0 := by
  change (∑ t : Fin 2, x t • Pi.single (qttTailIdx m hm t) (1 : K)) i = 0
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  have hne : qttTailIdx m hm t ≠ i := by
    intro h
    have := congrArg Fin.val h
    simp only [qttTailIdx, Fin.val_mk] at this
    omega
  simp [hne]

theorem qttPrefixLift_apply_tail (m : ℕ) (hm : 3 ≤ m) (x : Fin (m - 1) → K)
    (i : Fin (m + 1)) (hi : m - 1 ≤ i.val) :
    qttPrefixLift (F := F) (K := K) m hm x i = 0 := by
  change (∑ t : Fin (m - 1), x t • Pi.single (qttPrefixIdx m hm t) (1 : K)) i = 0
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  have hne : qttPrefixIdx m hm t ≠ i := by
    intro h
    have := congrArg Fin.val h
    simp only [qttPrefixIdx, Fin.val_mk] at this
    omega
  simp [hne]

theorem qttPrefixLift_apply_prefix (m : ℕ) (hm : 3 ≤ m) (x : Fin (m - 1) → K)
    (i : Fin (m - 1)) :
    qttPrefixLift (F := F) (K := K) m hm x (qttPrefixIdx m hm i) = x i := by
  change (∑ b : Fin (m - 1), x b • Pi.single (qttPrefixIdx m hm b) (1 : K))
    (qttPrefixIdx m hm i) = x i
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have hne : qttPrefixIdx m hm i ≠ qttPrefixIdx m hm b :=
      fun h => hb ((qttPrefixIdx_injective m hm h).symm)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem qttTailLift_apply_tail (m : ℕ) (hm : 3 ≤ m) (x : Fin 2 → K) (t : Fin 2) :
    qttTailLift (F := F) (K := K) m hm x (qttTailIdx m hm t) = x t := by
  change (∑ b : Fin 2, x b • Pi.single (qttTailIdx m hm b) (1 : K))
    (qttTailIdx m hm t) = x t
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    have hne : qttTailIdx m hm t ≠ qttTailIdx m hm b :=
      fun h => hb ((qttTailIdx_injective m hm h).symm)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem qttTailLift_smul_K (m : ℕ) (hm : 3 ≤ m) (a : K) (v : Fin 2 → K) :
    qttTailLift (F := F) (K := K) m hm (a • v) =
      a • qttTailLift (F := F) (K := K) m hm v := by
  ext j
  by_cases hj : ∃ t : Fin 2, j = qttTailIdx m hm t
  · obtain ⟨t, ht⟩ := hj
    rw [ht]
    simp [qttTailLift_apply_tail, Pi.smul_apply]
  · have hlt : j.val < m - 1 := by
      by_contra h
      apply hj
      have hge : m - 1 ≤ j.val := by omega
      let t : Fin 2 := ⟨j.val - (m - 1), by omega⟩
      refine ⟨t, ?_⟩
      apply Fin.ext
      simp [t, qttTailIdx]
      omega
    simp [qttTailLift_apply_prefix (F := F) (K := K) m hm _ j hlt, Pi.smul_apply]

theorem qtt_eq_prefix_add_tail (m : ℕ) (hm : 3 ≤ m) (v : Fin (m + 1) → K) :
    qttPrefixLift (F := F) (K := K) m hm
        (qttPrefixCoords (F := F) (K := K) m hm v) +
      qttTailLift (F := F) (K := K) m hm
        (qttTailCoords (F := F) (K := K) m hm v) = v := by
  ext i
  simp only [Pi.add_apply]
  by_cases hi : i.val < m - 1
  · let j : Fin (m - 1) := ⟨i.val, by omega⟩
    have hij : qttPrefixIdx m hm j = i := Fin.ext (by simp [j, qttPrefixIdx])
    rw [← hij]
    rw [qttPrefixLift_apply_prefix,
      qttTailLift_apply_prefix _ _ _ _ (by simpa [qttPrefixIdx] using hi), add_zero]
    rfl
  · have hi' : m - 1 ≤ i.val := by omega
    let t : Fin 2 := ⟨i.val - (m - 1), by omega⟩
    have hit : qttTailIdx m hm t = i := by
      apply Fin.ext
      simp [t, qttTailIdx]
      omega
    rw [← hit]
    rw [qttPrefixLift_apply_tail _ _ _ _ (by simp [qttTailIdx]), zero_add,
      qttTailLift_apply_tail]
    rfl


@[expose] noncomputable def qttP (m : ℕ) (hm : 3 ≤ m) :
    Submodule F (Fin (m + 1) → K) :=
  LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F) (qttTailCoords (F := F) (K := K) m hm)

@[expose] noncomputable def qttT (m : ℕ) (hm : 3 ≤ m) :
    Submodule F (Fin (m + 1) → K) :=
  LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F) (qttPrefixCoords (F := F) (K := K) m hm)

theorem qttPrefixLift_single (m : ℕ) (hm : 3 ≤ m) (i : Fin (m - 1)) (a : K) :
    qttPrefixLift (F := F) (K := K) m hm (Pi.single i a) =
      (Pi.single (qttPrefixIdx m hm i) a : Fin (m + 1) → K) := by
  ext j
  change (∑ b : Fin (m - 1),
      (Pi.single i a : Fin (m - 1) → K) b •
        (Pi.single (qttPrefixIdx m hm b) (1 : K) : Fin (m + 1) → K)) j =
    (Pi.single (qttPrefixIdx m hm i) a : Fin (m + 1) → K) j
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · by_cases hj : j = qttPrefixIdx m hm i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul, Pi.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem qttTailLift_single (m : ℕ) (hm : 3 ≤ m) (t : Fin 2) (a : K) :
    qttTailLift (F := F) (K := K) m hm (Pi.single t a) =
      (Pi.single (qttTailIdx m hm t) a : Fin (m + 1) → K) := by
  ext j
  change (∑ b : Fin 2,
      (Pi.single t a : Fin 2 → K) b •
        (Pi.single (qttTailIdx m hm b) (1 : K) : Fin (m + 1) → K)) j =
    (Pi.single (qttTailIdx m hm t) a : Fin (m + 1) → K) j
  rw [Finset.sum_apply, Finset.sum_eq_single t]
  · by_cases hj : j = qttTailIdx m hm t
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul, Pi.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem qttPrefixLift_mem_qttP (m : ℕ) (hm : 3 ≤ m) (x : Fin (m - 1) → K) :
    qttPrefixLift (F := F) (K := K) m hm x ∈ qttP (F := F) (K := K) m hm := by
  change qttPrefixLift (F := F) (K := K) m hm x ∈
    LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
      (qttTailCoords (F := F) (K := K) m hm)
  rw [LinearMap.mem_ker]
  ext t
  change qttPrefixLift (F := F) (K := K) m hm x (qttTailIdx m hm t) = 0
  exact qttPrefixLift_apply_tail _ _ _ _ (by simp [qttTailIdx])

theorem qttTailLift_mem_qttT (m : ℕ) (hm : 3 ≤ m) (x : Fin 2 → K) :
    qttTailLift (F := F) (K := K) m hm x ∈ qttT (F := F) (K := K) m hm := by
  change qttTailLift (F := F) (K := K) m hm x ∈
    LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
      (qttPrefixCoords (F := F) (K := K) m hm)
  rw [LinearMap.mem_ker]
  ext i
  change qttTailLift (F := F) (K := K) m hm x (qttPrefixIdx m hm i) = 0
  exact qttTailLift_apply_prefix _ _ _ _ (by simp [qttPrefixIdx])

theorem qttP_apply_tail {m : ℕ} (hm : 3 ≤ m) {v : Fin (m + 1) → K}
    (hv : v ∈ qttP (F := F) (K := K) m hm) {i : Fin (m + 1)} (hi : m - 1 ≤ i.val) :
    v i = 0 := by
  let t : Fin 2 := ⟨i.val - (m - 1), by omega⟩
  have hit : qttTailIdx m hm t = i := by
    apply Fin.ext
    simp [t, qttTailIdx]
    omega
  have h := congrFun (LinearMap.mem_ker.mp hv) t
  change v (qttTailIdx m hm t) = 0 at h
  simpa [hit] using h

theorem qttP_smul_K {m : ℕ} (hm : 3 ≤ m) (a : K) {v : Fin (m + 1) → K}
    (hv : v ∈ qttP (F := F) (K := K) m hm) :
    a • v ∈ qttP (F := F) (K := K) m hm := by
  rw [qttP, LinearMap.mem_ker] at hv ⊢
  ext t
  change a * v (qttTailIdx m hm t) = 0
  have h0 : v (qttTailIdx m hm t) = 0 := by
    simpa [qttTailCoords] using congrFun hv t
  rw [h0, mul_zero]

theorem qttT_apply_prefix {m : ℕ} (hm : 3 ≤ m) {v : Fin (m + 1) → K}
    (hv : v ∈ qttT (F := F) (K := K) m hm) {i : Fin (m + 1)} (hi : i.val < m - 1) :
    v i = 0 := by
  let t : Fin (m - 1) := ⟨i.val, hi⟩
  have hit : qttPrefixIdx m hm t = i := by
    apply Fin.ext
    simp [t, qttPrefixIdx]
  have h := congrFun (LinearMap.mem_ker.mp hv) t
  change v (qttPrefixIdx m hm t) = 0 at h
  simpa [hit] using h

theorem qttP_sup_qttT (m : ℕ) (hm : 3 ≤ m) :
    qttP (F := F) (K := K) m hm ⊔ qttT (F := F) (K := K) m hm = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have h := qtt_eq_prefix_add_tail (F := F) (K := K) m hm v
  exact Submodule.mem_sup.mpr
    ⟨qttPrefixLift m hm (qttPrefixCoords m hm v), qttPrefixLift_mem_qttP m hm _,
      qttTailLift m hm (qttTailCoords m hm v), qttTailLift_mem_qttT m hm _, h⟩

theorem qttP_inf_qttT (m : ℕ) (hm : 3 ≤ m) :
    qttP (F := F) (K := K) m hm ⊓ qttT (F := F) (K := K) m hm = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  ext i
  by_cases hi : i.val < m - 1
  · have h := qttT_apply_prefix hm hv.2 hi
    simpa using h
  · have hi' : m - 1 ≤ i.val := by omega
    exact qttP_apply_tail hm hv.1 hi'

theorem qttPolar_prefixLift_single (m : ℕ) (hm : 3 ≤ m) (i : Fin (m - 1)) (a : K)
    (w : Fin (m + 1) → K) :
    QuadraticMap.polar (Qn E (m + 1))
        (qttPrefixLift (F := F) (K := K) m hm (Pi.single i a)) w =
      QuadraticMap.polar (normQuad E) a (w (qttPrefixIdx m hm i)) := by
  rw [qttPrefixLift_single, polar_Qn]
  rw [Finset.sum_eq_single (qttPrefixIdx m hm i)]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem qttPolar_tailLift_single (m : ℕ) (hm : 3 ≤ m) (t : Fin 2) (a : K)
    (w : Fin (m + 1) → K) :
    QuadraticMap.polar (Qn E (m + 1))
        (qttTailLift (F := F) (K := K) m hm (Pi.single t a)) w =
      QuadraticMap.polar (normQuad E) a (w (qttTailIdx m hm t)) := by
  rw [qttTailLift_single, polar_Qn]
  rw [Finset.sum_eq_single (qttTailIdx m hm t)]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem qttT_le_orthogonal_qttP (m : ℕ) (hm : 3 ≤ m) :
    qttT (F := F) (K := K) m hm ≤
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (Qn E (m + 1)))
        (qttP (F := F) (K := K) m hm) := by
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro p hp
  rw [QuadraticMap.polarBilin_apply_apply, polar_Qn]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val < m - 1
  · have hv0 : v i = 0 := qttT_apply_prefix hm hv hi
    simp [hv0]
  · have hp0 : p i = 0 := qttP_apply_tail hm hp (by omega)
    simp [hp0]

theorem qtt_orthogonal_qttP_le_qttT (m : ℕ) (hm : 3 ≤ m) :
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (Qn E (m + 1)))
        (qttP (F := F) (K := K) m hm) ≤ qttT (F := F) (K := K) m hm := by
  intro v hv
  change v ∈ LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
    (qttPrefixCoords (F := F) (K := K) m hm)
  rw [LinearMap.mem_ker]
  ext i'
  change v (qttPrefixIdx m hm i') = 0
  have hnd := (normQuad_polarBilin_nondegenerate E).2
  refine hnd (v (qttPrefixIdx m hm i')) ?_
  intro a
  have hmem : qttPrefixLift (F := F) (K := K) m hm (Pi.single i' a) ∈
      qttP (F := F) (K := K) m hm := qttPrefixLift_mem_qttP m hm _
  have horth := (LinearMap.BilinForm.mem_orthogonal_iff.mp hv)
    (qttPrefixLift (F := F) (K := K) m hm (Pi.single i' a)) hmem
  rw [QuadraticMap.polarBilin_apply_apply, qttPolar_prefixLift_single] at horth
  exact horth

theorem qtt_orthogonal_qttP (m : ℕ) (hm : 3 ≤ m) :
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (Qn E (m + 1)))
        (qttP (F := F) (K := K) m hm) = qttT (F := F) (K := K) m hm := by
  exact le_antisymm (qtt_orthogonal_qttP_le_qttT (E := E) m hm)
    (qttT_le_orthogonal_qttP (E := E) m hm)


theorem qtt_elim_eq_sum_smul {n : ℕ} (v : Fin n → K) :
    (Sum.elim v 0 : Fin n ⊕ Fin n → K) = ∑ i, v i • stdE (K := K) (n := n) i := by
  ext p
  cases p with
  | inl j =>
    simp only [Sum.elim_inl, stdE_inl, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      have hji : j ≠ i := Ne.symm hij
      rw [if_neg hji, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  | inr j =>
    simp [stdE]

theorem qtt_elim_mem_coordSpan {m : ℕ} {v : Fin (m + 1) → K}
    (hv : ∀ i : Fin (m + 1), m - 1 ≤ i.val → v i = 0) :
    (Sum.elim v 0 : Fin (m + 1) ⊕ Fin (m + 1) → K) ∈
      coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅ := by
  rw [qtt_elim_eq_sum_smul]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i.val < m - 1
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨i, hi, rfl⟩))
  · rw [hv i (by omega), zero_smul]
    exact Submodule.zero_mem _

theorem qtt_coordSpan_le_stdLag (m : ℕ) :
    coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅ ≤
      stdLag (m + 1) K := by
  rw [coordSpan]
  refine Submodule.span_le.mpr ?_
  rintro v (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
  · apply mem_stdLag.mpr
    intro t
    simp [stdE]
  · simp at hj

theorem qtt_tail_coords_eq_zero {m : ℕ} (hm : 3 ≤ m) {v : Fin (m + 1) → K}
    (hv : qttTailCoords (F := F) (K := K) m hm v = 0) :
    ∀ i : Fin (m + 1), m - 1 ≤ i.val → v i = 0 := by
  intro i hi
  let t : Fin 2 := ⟨i.val - (m - 1), by omega⟩
  have hit : qttTailIdx m hm t = i := by
    apply Fin.ext
    simp [t, qttTailIdx]
    omega
  have h := congrFun hv t
  change v (qttTailIdx m hm t) = 0 at h
  simpa [hit] using h


theorem qtt_bcLin_mem_coordSpan_of_mem_qttP (m : ℕ) (hm : 3 ≤ m)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hprefix : (coordSpan (K := K) (m + 1)
        {i : Fin (m + 1) | i.val < m - 1} ∅).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅)
    {v : Fin (m + 1) → K} (hv : v ∈ qttP (F := F) (K := K) m hm) :
    bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
        (Sum.elim v 0) ∈
      coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅ := by
  have hle : (coordSpan (K := K) (m + 1)
      {i : Fin (m + 1) | i.val < m - 1} ∅).map
        (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) ≤
      coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅ := by
    rw [hprefix]
  have hvzero : ∀ i : Fin (m + 1), m - 1 ≤ i.val → v i = 0 := by
    have hker : v ∈ LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
        (qttTailCoords (F := F) (K := K) m hm) := hv
    exact qtt_tail_coords_eq_zero (m := m) hm (LinearMap.mem_ker.mp hker)
  exact hle (Submodule.mem_map_of_mem (qtt_elim_mem_coordSpan hvzero))

theorem qtt_coordSpan_apply_inl_eq_zero_of_not_mem {n : ℕ} {I : Set (Fin n)}
    {z : Fin n ⊕ Fin n → K} (hz : z ∈ coordSpan (K := K) n I ∅)
    {i : Fin n} (hi : i ∉ I) : z (Sum.inl i) = 0 := by
  rw [coordSpan] at hz
  refine Submodule.span_induction (p := fun z _ => z (Sum.inl i) = 0) ?_ ?_ ?_ ?_ hz
  · rintro _ (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · by_cases hji : i = j
      · subst hji
        exact absurd hj hi
      · simp [stdE, Pi.single_apply, hji]
    · simp [stdF]
  · simp
  · intro u v _ _ hu hv
    simp [hu, hv]
  · intro c u _ hu
    simp [hu]

theorem qtt_x_mem_qttP (m : ℕ) (hm : 3 ≤ m)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hprefix : (coordSpan (K := K) (m + 1)
        {i : Fin (m + 1) | i.val < m - 1} ∅).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅)
    {v : Fin (m + 1) → K} (hv : v ∈ qttP (F := F) (K := K) m hm) :
    (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) v ∈
      qttP (F := F) (K := K) m hm := by
  have hmem := qtt_bcLin_mem_coordSpan_of_mem_qttP E m hm hprefix hv
  have hlag : bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
      (Sum.elim v 0) ∈ stdLag (m + 1) K :=
    qtt_coordSpan_le_stdLag m hmem
  have heq := bcLin_firstHalf_eq_of_mem_stdLag E
    (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) v hlag
  change (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) v ∈
    LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
      (qttTailCoords (F := F) (K := K) m hm)
  rw [LinearMap.mem_ker]
  ext t
  change ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) v) (qttTailIdx m hm t) = 0
  have h := congrFun heq (Sum.inl (qttTailIdx m hm t))
  have hzero : bcLin E (m + 1)
      (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
      (Sum.elim v 0) (Sum.inl (qttTailIdx m hm t)) = 0 :=
    qtt_coordSpan_apply_inl_eq_zero_of_not_mem (I := {i : Fin (m + 1) | i.val < m - 1})
      hmem (by simp [qttTailIdx])
  rw [hzero] at h
  simpa [Sum.elim] using h.symm

theorem qtt_x_isKLinear_on_qttP (m : ℕ) (hm : 3 ≤ m)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hprefix : (coordSpan (K := K) (m + 1)
        {i : Fin (m + 1) | i.val < m - 1} ∅).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅)
    {v : Fin (m + 1) → K} (hv : v ∈ qttP (F := F) (K := K) m hm) (a : K) :
    (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (a • v) =
      a • (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) v := by
  have hmem := qtt_bcLin_mem_coordSpan_of_mem_qttP E m hm hprefix hv
  have hlag : bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
      (Sum.elim v 0) ∈ stdLag (m + 1) K :=
    qtt_coordSpan_le_stdLag m hmem
  exact isKLinear_at_of_bcLin_mem_stdLag E
    (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) v hlag a

theorem qtt_x_map_qttP (m : ℕ) (hm : 3 ≤ m)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hprefix : (coordSpan (K := K) (m + 1)
        {i : Fin (m + 1) | i.val < m - 1} ∅).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅) :
    (qttP (F := F) (K := K) m hm).map
        (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) =
      qttP (F := F) (K := K) m hm := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact qtt_x_mem_qttP E m hm hprefix hv
  · rw [LinearEquiv.finrank_map_eq]



theorem qtt_x_mem_qttT (m : ℕ) (hm : 3 ≤ m)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hprefix : (coordSpan (K := K) (m + 1)
        {i : Fin (m + 1) | i.val < m - 1} ∅).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅)
    {v : Fin (m + 1) → K} (hv : v ∈ qttT (F := F) (K := K) m hm) :
    (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) v ∈
      qttT (F := F) (K := K) m hm := by
  have hxO : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)) :=
    Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) x.2
  rw [← qtt_orthogonal_qttP (E := E) m hm]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro p hp
  have hp' : p ∈ (qttP (F := F) (K := K) m hm).map
      (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) := by
    rw [qtt_x_map_qttP E m hm hprefix]
    exact hp
  obtain ⟨p0, hp0, hp0eq⟩ := Submodule.mem_map.mp hp'
  rw [← hp0eq]
  rw [QuadraticMap.polarBilin_apply_apply]
  let xL : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K) :=
    (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
  change QuadraticMap.polar (Qn E (m + 1)) (xL p0) (xL v) = 0
  have hpol := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hxO p0 v
  have hpol' : QuadraticMap.polar (Qn E (m + 1)) (xL p0) (xL v) =
      QuadraticMap.polar (Qn E (m + 1)) p0 v := hpol
  rw [hpol']
  have hvorth := (qttT_le_orthogonal_qttP (E := E) m hm hv) p0 hp0
  rwa [QuadraticMap.polarBilin_apply_apply] at hvorth


theorem qttTailLift_tailCoords_of_mem_qttT {m : ℕ} (hm : 3 ≤ m) {v : Fin (m + 1) → K}
    (hv : v ∈ qttT (F := F) (K := K) m hm) :
    qttTailLift (F := F) (K := K) m hm
        (qttTailCoords (F := F) (K := K) m hm v) = v := by
  have hker : v ∈ LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
      (qttPrefixCoords (F := F) (K := K) m hm) := hv
  have hp : qttPrefixCoords (F := F) (K := K) m hm v = 0 := LinearMap.mem_ker.mp hker
  have h := qtt_eq_prefix_add_tail (F := F) (K := K) m hm v
  rw [hp, map_zero, zero_add] at h
  exact h

theorem qtt_x_map_qttT (m : ℕ) (hm : 3 ≤ m)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hprefix : (coordSpan (K := K) (m + 1)
        {i : Fin (m + 1) | i.val < m - 1} ∅).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅) :
    (qttT (F := F) (K := K) m hm).map
        (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) =
      qttT (F := F) (K := K) m hm := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact qtt_x_mem_qttT E m hm hprefix hv
  · rw [LinearEquiv.finrank_map_eq]

theorem qtt_x_symm_mem_qttT (m : ℕ) (hm : 3 ≤ m)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hprefix : (coordSpan (K := K) (m + 1)
        {i : Fin (m + 1) | i.val < m - 1} ∅).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅)
    {v : Fin (m + 1) → K} (hv : v ∈ qttT (F := F) (K := K) m hm) :
    (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))⁻¹ v ∈
      qttT (F := F) (K := K) m hm := by
  have hv' : v ∈ (qttT (F := F) (K := K) m hm).map
      (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) := by
    rw [qtt_x_map_qttT E m hm hprefix]
    exact hv
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hv'
  have hwv' : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) w = v := hwv
  rw [← hwv']
  simpa [LinearEquiv.symm_apply_apply] using hw

noncomputable def qttXT (m : ℕ) (hm : 3 ≤ m)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hprefix : (coordSpan (K := K) (m + 1)
        {i : Fin (m + 1) | i.val < m - 1} ∅).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅) :
    (Fin 2 → K) ≃ₗ[F] (Fin 2 → K) where
  toFun v := qttTailCoords (F := F) (K := K) m hm
    ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
      (qttTailLift (F := F) (K := K) m hm v))
  invFun v := qttTailCoords (F := F) (K := K) m hm
    ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))⁻¹
      (qttTailLift (F := F) (K := K) m hm v))
  left_inv v := by
    have hxT : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        (qttTailLift (F := F) (K := K) m hm v) ∈ qttT (F := F) (K := K) m hm :=
      qtt_x_mem_qttT E m hm hprefix (qttTailLift_mem_qttT m hm v)
    change qttTailCoords (F := F) (K := K) m hm
      ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))⁻¹
        (qttTailLift (F := F) (K := K) m hm
          (qttTailCoords (F := F) (K := K) m hm
            ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
              (qttTailLift (F := F) (K := K) m hm v))))) = v
    rw [qttTailLift_tailCoords_of_mem_qttT (m := m) hm hxT]
    simpa [LinearEquiv.symm_apply_apply] using qttTailCoords_tailLift m hm v
  right_inv v := by
    have hxT : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))⁻¹
        (qttTailLift (F := F) (K := K) m hm v) ∈ qttT (F := F) (K := K) m hm :=
      qtt_x_symm_mem_qttT E m hm hprefix (qttTailLift_mem_qttT m hm v)
    change qttTailCoords (F := F) (K := K) m hm
      ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        (qttTailLift (F := F) (K := K) m hm
          (qttTailCoords (F := F) (K := K) m hm
            ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))⁻¹
              (qttTailLift (F := F) (K := K) m hm v))))) = v
    rw [qttTailLift_tailCoords_of_mem_qttT (m := m) hm hxT]
    simpa [LinearEquiv.apply_symm_apply] using qttTailCoords_tailLift m hm v
  map_add' v w := by
    change qttTailCoords (F := F) (K := K) m hm
      ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        (qttTailLift (F := F) (K := K) m hm (v + w))) =
      qttTailCoords (F := F) (K := K) m hm
        ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
          (qttTailLift (F := F) (K := K) m hm v)) +
      qttTailCoords (F := F) (K := K) m hm
        ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
          (qttTailLift (F := F) (K := K) m hm w))
    rw [map_add, map_add, map_add]
  map_smul' a v := by
    change qttTailCoords (F := F) (K := K) m hm
      ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        (qttTailLift (F := F) (K := K) m hm (a • v))) =
      a • qttTailCoords (F := F) (K := K) m hm
        ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
          (qttTailLift (F := F) (K := K) m hm v))
    rw [map_smul, map_smul, map_smul]


theorem qtt_tail_sum_eq {m : ℕ} (hm : 3 ≤ m) {M : Type} [AddCommMonoid M]
    (f : Fin (m + 1) → M) (hf : ∀ i : Fin (m + 1), i.val < m - 1 → f i = 0) :
    ∑ i, f i = ∑ t : Fin 2, f (qttTailIdx m hm t) := by
  have hzero : ∀ x ∈ (Finset.univ : Finset (Fin (m + 1))),
      x ∉ Finset.univ.image (qttTailIdx (m := m) hm) → f x = 0 := by
    intro x _ hx
    have hx' : x.val < m - 1 := by
      by_contra h
      apply hx
      let t : Fin 2 := ⟨x.val - (m - 1), by omega⟩
      refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp [t, qttTailIdx]
      omega
    exact hf x hx'
  calc ∑ i, f i = ∑ i ∈ Finset.univ.image (qttTailIdx (m := m) hm), f i := by
        rw [Finset.sum_subset (s₁ := Finset.univ.image (qttTailIdx (m := m) hm))
          (s₂ := Finset.univ) (Finset.subset_univ _) hzero]
    _ = ∑ t : Fin 2, f (qttTailIdx m hm t) := by
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact qttTailIdx_injective m hm hab

theorem qtt_Qn_tailLift (m : ℕ) (hm : 3 ≤ m) (v : Fin 2 → K) :
    Qn E (m + 1) (qttTailLift (F := F) (K := K) m hm v) = Qn E 2 v := by
  rw [Qn_apply, Qn_apply]
  refine (qtt_tail_sum_eq (m := m) (M := F) hm
    (fun i => normQuad E (qttTailLift (F := F) (K := K) m hm v i)) ?_).trans ?_
  · intro i hi
    rw [qttTailLift_apply_prefix (F := F) (K := K) m hm v i hi, map_zero]
  · apply Finset.sum_congr rfl
    intro t _
    rw [qttTailLift_apply_tail]

theorem qttXT_tailLift (m : ℕ) (hm : 3 ≤ m)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hprefix : (coordSpan (K := K) (m + 1)
        {i : Fin (m + 1) | i.val < m - 1} ∅).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅)
    (v : Fin 2 → K) :
    qttTailLift (F := F) (K := K) m hm (qttXT E m hm hprefix v) =
      (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        (qttTailLift (F := F) (K := K) m hm v) := by
  change qttTailLift (F := F) (K := K) m hm
    (qttTailCoords (F := F) (K := K) m hm
      ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        (qttTailLift (F := F) (K := K) m hm v))) = _
  exact qttTailLift_tailCoords_of_mem_qttT (m := m) hm
    (qtt_x_mem_qttT E m hm hprefix (qttTailLift_mem_qttT m hm v))

theorem qttXT_mem_orthogonalGroup (m : ℕ) (hm : 3 ≤ m)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hprefix : (coordSpan (K := K) (m + 1)
        {i : Fin (m + 1) | i.val < m - 1} ∅).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅) :
    qttXT E m hm hprefix ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E 2) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  have hxO : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)) :=
    Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) x.2
  have hval := qttXT_tailLift E m hm hprefix v
  calc Qn E 2 (qttXT E m hm hprefix v)
      = Qn E (m + 1) (qttTailLift (F := F) (K := K) m hm
          (qttXT E m hm hprefix v)) := (qtt_Qn_tailLift E m hm _).symm
    _ = Qn E (m + 1) ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
          (qttTailLift (F := F) (K := K) m hm v)) := by rw [hval]
    _ = Qn E (m + 1) (qttTailLift (F := F) (K := K) m hm v) := by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hxO]
    _ = Qn E 2 v := qtt_Qn_tailLift E m hm v


theorem qtt_isKLinear_of_prefix_tail (m : ℕ) (hm : 3 ≤ m)
    (G : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hP : ∀ (a : K) (p : Fin (m + 1) → K), p ∈ qttP (F := F) (K := K) m hm →
      G (a • p) = a • G p)
    (hT : ∀ (a : K) (t : Fin (m + 1) → K), t ∈ qttT (F := F) (K := K) m hm →
      G (a • t) = a • G t) :
    ∀ (a : K) (w : Fin (m + 1) → K), G (a • w) = a • G w := by
  intro a w
  let p := qttPrefixLift (F := F) (K := K) m hm
    (qttPrefixCoords (F := F) (K := K) m hm w)
  let t := qttTailLift (F := F) (K := K) m hm
    (qttTailCoords (F := F) (K := K) m hm w)
  have hp : p ∈ qttP (F := F) (K := K) m hm :=
    qttPrefixLift_mem_qttP m hm _
  have ht : t ∈ qttT (F := F) (K := K) m hm :=
    qttTailLift_mem_qttT m hm _
  have hw : p + t = w := qtt_eq_prefix_add_tail (F := F) (K := K) m hm w
  calc G (a • w) = G (a • (p + t)) := by rw [← hw]
    _ = G (a • p + a • t) := by rw [smul_add]
    _ = G (a • p) + G (a • t) := by rw [map_add]
    _ = a • G p + a • G t := by rw [hP a p hp, hT a t ht]
    _ = a • (G p + G t) := by rw [smul_add]
    _ = a • G (p + t) := by rw [map_add]
    _ = a • G w := by rw [hw]


theorem qtt_tauAt_tail_fixes_qttP (m : ℕ) (hm : 3 ≤ m) (k : Fin 2)
    {v : Fin (m + 1) → K} (hv : v ∈ qttP (F := F) (K := K) m hm) :
    tauAt E (qttTailIdx m hm k) v = v := by
  ext j
  by_cases hj : j = qttTailIdx m hm k
  · subst j
    have h0 : v (qttTailIdx m hm k) = 0 :=
      qttP_apply_tail (F := F) (K := K) (m := m) hm hv (by simp [qttTailIdx])
    simp [tauAt_apply, h0]
  · simp [tauAt_apply, hj]

theorem qtt_tauAt_tail_tailLift (m : ℕ) (hm : 3 ≤ m) (k : Fin 2) (v : Fin 2 → K) :
    tauAt E (qttTailIdx m hm k) (qttTailLift (F := F) (K := K) m hm v) =
      qttTailLift (F := F) (K := K) m hm (tauAt E k v) := by
  ext j
  by_cases hj : ∃ t : Fin 2, j = qttTailIdx m hm t
  · obtain ⟨t, ht⟩ := hj
    rw [ht]
    by_cases htk : t = k
    · subst t
      simp [tauAt_apply, qttTailLift_apply_tail]
    · have hne : qttTailIdx m hm t ≠ qttTailIdx m hm k :=
        fun h => htk (qttTailIdx_injective m hm h)
      simp [tauAt_apply, qttTailLift_apply_tail, htk, hne]
  · have hlt : j.val < m - 1 := by
      by_contra h
      apply hj
      have hge : m - 1 ≤ j.val := by omega
      let t : Fin 2 := ⟨j.val - (m - 1), by omega⟩
      refine ⟨t, ?_⟩
      apply Fin.ext
      simp [t, qttTailIdx]
      omega
    have hjk : j ≠ qttTailIdx m hm k := fun h => hj ⟨k, h⟩
    rw [tauAt_apply, if_neg hjk,
      qttTailLift_apply_prefix (F := F) (K := K) m hm v j hlt,
      qttTailLift_apply_prefix (F := F) (K := K) m hm (tauAt E k v) j hlt]

theorem qtt_x_mul_global_isKLinear_of_local (m : ℕ) (hm : 3 ≤ m)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hprefix : (coordSpan (K := K) (m + 1)
        {i : Fin (m + 1) | i.val < m - 1} ∅).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅)
    (c : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K))
    (C : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hCfix : ∀ p : Fin (m + 1) → K, p ∈ qttP (F := F) (K := K) m hm → C p = p)
    (hCtail : ∀ v : Fin 2 → K,
      C (qttTailLift (F := F) (K := K) m hm v) =
        qttTailLift (F := F) (K := K) m hm (c v))
    (hc : ∀ (a : K) (w : Fin 2 → K),
      (qttXT (E := E) m hm hprefix * c) (a • w) =
        a • (qttXT (E := E) m hm hprefix * c) w) :
    ∀ (a : K) (w : Fin (m + 1) → K),
      ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) * C) (a • w) =
        a • ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) * C) w := by
  apply qtt_isKLinear_of_prefix_tail m hm
    ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) * C)
  · intro a p hp
    rw [LinearEquiv.mul_apply, hCfix (a • p) (qttP_smul_K (F := F) (K := K) hm a hp), LinearEquiv.mul_apply, hCfix p hp]
    exact qtt_x_isKLinear_on_qttP E m hm hprefix hp a
  · intro a t ht
    let v : Fin 2 → K := qttTailCoords (F := F) (K := K) m hm t
    have ht_eq : qttTailLift (F := F) (K := K) m hm v = t :=
      qttTailLift_tailCoords_of_mem_qttT (m := m) hm ht
    have hCt : C t = qttTailLift (F := F) (K := K) m hm (c v) := by
      rw [← ht_eq, hCtail]
    have hCat : C (a • t) = qttTailLift (F := F) (K := K) m hm (c (a • v)) := by
      rw [← ht_eq, ← qttTailLift_smul_K (F := F) (K := K) m hm a v, hCtail]
    have hxat : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        (qttTailLift (F := F) (K := K) m hm (c (a • v))) =
        qttTailLift (F := F) (K := K) m hm
          ((qttXT (E := E) m hm hprefix) (c (a • v))) :=
      (qttXT_tailLift (E := E) m hm hprefix (c (a • v))).symm
    have hxvt : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        (qttTailLift (F := F) (K := K) m hm (c v)) =
        qttTailLift (F := F) (K := K) m hm
          ((qttXT (E := E) m hm hprefix) (c v)) :=
      (qttXT_tailLift (E := E) m hm hprefix (c v)).symm
    calc ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) * C) (a • t) =
          (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (C (a • t)) := by
            rw [LinearEquiv.mul_apply]
      _ = (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
            (qttTailLift (F := F) (K := K) m hm (c (a • v))) := by rw [hCat]
      _ = qttTailLift (F := F) (K := K) m hm
            ((qttXT (E := E) m hm hprefix) (c (a • v))) := hxat
      _ = qttTailLift (F := F) (K := K) m hm
            (a • (qttXT (E := E) m hm hprefix) (c v)) := by
            change qttTailLift (F := F) (K := K) m hm
              ((qttXT (E := E) m hm hprefix * c) (a • v)) = _
            rw [hc a v]
            rfl
      _ = a • qttTailLift (F := F) (K := K) m hm
            ((qttXT (E := E) m hm hprefix) (c v)) := by rw [qttTailLift_smul_K]
      _ = a • (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
            (qttTailLift (F := F) (K := K) m hm (c v)) := by rw [hxvt]
      _ = a • (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (C t) := by rw [hCt]
      _ = a • ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) * C) t := by
        rw [LinearEquiv.mul_apply]

theorem qTwo_twoTail_correction (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hprefix : (coordSpan (K := K) (m + 1)
        {i : Fin (m + 1) | i.val < m - 1} ∅).map
      (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        coordSpan (K := K) (m + 1) {i : Fin (m + 1) | i.val < m - 1} ∅) :
    (∀ (a : K) (w : Fin (m + 1) → K),
      (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (a • w) =
        a • (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) w) ∨
    (∀ (a : K) (w : Fin (m + 1) → K),
      ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
          (tauAt E (⟨m - 1, by omega⟩ : Fin (m + 1)) * tauAt E (Fin.last m))) (a • w) =
        a • ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
          (tauAt E (⟨m - 1, by omega⟩ : Fin (m + 1)) * tauAt E (Fin.last m))) w) := by
  classical
  have hO : qttXT (E := E) m hm hprefix ∈
      TauCeti.QuadraticMap.orthogonalGroup (Qn E 2) :=
    qttXT_mem_orthogonalGroup E m hm hprefix
  obtain ⟨b0, b1, hcorr⟩ := qTwo_isometry_coordinate_correction E hK hO
  have hxR : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈ rulingGroup E (m + 1) :=
    orthDerived_le_rulingGroup E (m + 1) x.2
  cases b0 <;> cases b1
  ·
    have hc : ∀ (a : K) (w : Fin 2 → K),
        (qttXT (E := E) m hm hprefix * (1 : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K))) (a • w) =
          a • (qttXT (E := E) m hm hprefix * (1 : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K))) w := by
      simpa using hcorr
    have hlin := qtt_x_mul_global_isKLinear_of_local E m hm hprefix
      (1 : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K))
      (1 : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
      (by intro p hp; rfl) (by intro v; rfl) hc
    exact Or.inl (by simpa using hlin)
  ·
    have hc : ∀ (a : K) (w : Fin 2 → K),
        (qttXT (E := E) m hm hprefix * tauAt E (1 : Fin 2)) (a • w) =
          a • (qttXT (E := E) m hm hprefix * tauAt E (1 : Fin 2)) w := by
      simpa using hcorr
    have hlin := qtt_x_mul_global_isKLinear_of_local E m hm hprefix
      (tauAt E (1 : Fin 2)) (tauAt E (qttTailIdx m hm (1 : Fin 2)))
      (fun p hp => qtt_tauAt_tail_fixes_qttP E m hm 1 hp)
      (fun v => qtt_tauAt_tail_tailLift E m hm 1 v) hc
    exfalso
    exact qTwo_not_isKLinear_mul_tauAt E hxR (qttTailIdx m hm (1 : Fin 2)) hlin
  ·
    have hc : ∀ (a : K) (w : Fin 2 → K),
        (qttXT (E := E) m hm hprefix * tauAt E (0 : Fin 2)) (a • w) =
          a • (qttXT (E := E) m hm hprefix * tauAt E (0 : Fin 2)) w := by
      simpa using hcorr
    have hlin := qtt_x_mul_global_isKLinear_of_local E m hm hprefix
      (tauAt E (0 : Fin 2)) (tauAt E (qttTailIdx m hm (0 : Fin 2)))
      (fun p hp => qtt_tauAt_tail_fixes_qttP E m hm 0 hp)
      (fun v => qtt_tauAt_tail_tailLift E m hm 0 v) hc
    exfalso
    exact qTwo_not_isKLinear_mul_tauAt E hxR (qttTailIdx m hm (0 : Fin 2)) hlin
  ·
    let c : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K) := tauAt E (0 : Fin 2) * tauAt E (1 : Fin 2)
    let C : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K) :=
      tauAt E (qttTailIdx m hm (0 : Fin 2)) * tauAt E (qttTailIdx m hm (1 : Fin 2))
    have hc : ∀ (a : K) (w : Fin 2 → K),
        (qttXT (E := E) m hm hprefix * c) (a • w) =
          a • (qttXT (E := E) m hm hprefix * c) w := by
      simpa [c] using hcorr
    have hCfix : ∀ p : Fin (m + 1) → K, p ∈ qttP (F := F) (K := K) m hm → C p = p := by
      intro p hp
      rw [LinearEquiv.mul_apply, qtt_tauAt_tail_fixes_qttP E m hm 1 hp,
        qtt_tauAt_tail_fixes_qttP E m hm 0 hp]
    have hCtail : ∀ v : Fin 2 → K,
        C (qttTailLift (F := F) (K := K) m hm v) =
          qttTailLift (F := F) (K := K) m hm (c v) := by
      intro v
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      rw [qtt_tauAt_tail_tailLift E m hm 1]
      rw [qtt_tauAt_tail_tailLift E m hm 0]
    have hlin := qtt_x_mul_global_isKLinear_of_local E m hm hprefix c C hCfix hCtail hc
    have hfirst : qttTailIdx m hm (0 : Fin 2) = (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext
      simp [qttTailIdx]
    have hlast : qttTailIdx m hm (1 : Fin 2) = Fin.last m := by
      apply Fin.ext
      simp [qttTailIdx, Fin.last]
      omega
    refine Or.inr ?_
    simpa [C, hfirst, hlast] using hlin



end CFSG.ClassicalInvolution.PhanDn.QTwo
