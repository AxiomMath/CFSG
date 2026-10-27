module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.StdFamily
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabKlein
import all CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabSwap
public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelFork
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.AmalgamFamily
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagResidueA

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin
open CFSG.StandardType.QTwo
open CFSG.RankThree.PartOne.K159

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

noncomputable def qtsTailIdx (m : ℕ) (hm : 3 ≤ m) (t : Fin 3) : Fin (m + 1) :=
  ⟨m - 2 + t.val, by omega⟩

theorem qtsTailIdx_injective (m : ℕ) (hm : 3 ≤ m) :
    Function.Injective (qtsTailIdx (m := m) hm) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [qtsTailIdx, Fin.val_mk] at this
  omega

noncomputable def qtsPrefixIdx (m : ℕ) (hm : 3 ≤ m) (i : Fin (m - 2)) : Fin (m + 1) :=
  ⟨i.val, by omega⟩

theorem qtsPrefixIdx_injective (m : ℕ) (hm : 3 ≤ m) :
    Function.Injective (qtsPrefixIdx (m := m) hm) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [qtsPrefixIdx, Fin.val_mk] at this
  exact this

@[expose] noncomputable def qtsTailLift (m : ℕ) (hm : 3 ≤ m) :
    (Fin 3 → K) →ₗ[F] (Fin (m + 1) → K) where
  toFun x := ∑ t : Fin 3, x t • Pi.single (qtsTailIdx m hm t) (1 : K)
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_add, Finset.smul_sum, smul_assoc, RingHom.id_apply]

@[expose] noncomputable def qtsTailCoords (m : ℕ) (hm : 3 ≤ m) :
    (Fin (m + 1) → K) →ₗ[F] (Fin 3 → K) where
  toFun x t := x (qtsTailIdx m hm t)
  map_add' x y := by ext t; rfl
  map_smul' c x := by ext t; rfl

@[expose] noncomputable def qtsPrefixLift (m : ℕ) (hm : 3 ≤ m) :
    (Fin (m - 2) → K) →ₗ[F] (Fin (m + 1) → K) where
  toFun x := ∑ i : Fin (m - 2), x i • Pi.single (qtsPrefixIdx m hm i) (1 : K)
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_add, Finset.smul_sum, smul_assoc, RingHom.id_apply]

@[expose] noncomputable def qtsPrefixCoords (m : ℕ) (hm : 3 ≤ m) :
    (Fin (m + 1) → K) →ₗ[F] (Fin (m - 2) → K) where
  toFun x i := x (qtsPrefixIdx m hm i)
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl

theorem qtsTailCoords_tailLift (m : ℕ) (hm : 3 ≤ m) (x : Fin 3 → K) :
    qtsTailCoords (F := F) (K := K) m hm (qtsTailLift (F := F) (K := K) m hm x) = x := by
  ext t
  change (∑ b : Fin 3, x b • Pi.single (qtsTailIdx m hm b) (1 : K)) (qtsTailIdx m hm t) = x t
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    have hne : qtsTailIdx m hm t ≠ qtsTailIdx m hm b :=
      fun h => hb ((qtsTailIdx_injective m hm h).symm)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem qtsPrefixCoords_prefixLift (m : ℕ) (hm : 3 ≤ m) (x : Fin (m - 2) → K) :
    qtsPrefixCoords (F := F) (K := K) m hm (qtsPrefixLift (F := F) (K := K) m hm x) = x := by
  ext i
  change (∑ b : Fin (m - 2), x b • Pi.single (qtsPrefixIdx m hm b) (1 : K))
    (qtsPrefixIdx m hm i) = x i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have hne : qtsPrefixIdx m hm i ≠ qtsPrefixIdx m hm b :=
      fun h => hb ((qtsPrefixIdx_injective m hm h).symm)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem qtsTailLift_apply_prefix (m : ℕ) (hm : 3 ≤ m) (x : Fin 3 → K)
    (i : Fin (m + 1)) (hi : i.val < m - 2) : qtsTailLift (F := F) (K := K) m hm x i = 0 := by
  change (∑ t : Fin 3, x t • Pi.single (qtsTailIdx m hm t) (1 : K)) i = 0
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  have hne : qtsTailIdx m hm t ≠ i := by
    intro h
    have := congrArg Fin.val h
    simp only [qtsTailIdx, Fin.val_mk] at this
    omega
  simp [hne]

theorem qtsPrefixLift_apply_tail (m : ℕ) (hm : 3 ≤ m) (x : Fin (m - 2) → K)
    (i : Fin (m + 1)) (hi : m - 2 ≤ i.val) : qtsPrefixLift (F := F) (K := K) m hm x i = 0 := by
  change (∑ t : Fin (m - 2), x t • Pi.single (qtsPrefixIdx m hm t) (1 : K)) i = 0
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  have hne : qtsPrefixIdx m hm t ≠ i := by
    intro h
    have := congrArg Fin.val h
    simp only [qtsPrefixIdx, Fin.val_mk] at this
    omega
  simp [hne]

theorem qtsPrefixLift_apply_prefix (m : ℕ) (hm : 3 ≤ m) (x : Fin (m - 2) → K)
    (i : Fin (m - 2)) :
    qtsPrefixLift (F := F) (K := K) m hm x (qtsPrefixIdx m hm i) = x i := by
  change (∑ b : Fin (m - 2), x b • Pi.single (qtsPrefixIdx m hm b) (1 : K))
    (qtsPrefixIdx m hm i) = x i
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have hne : qtsPrefixIdx m hm i ≠ qtsPrefixIdx m hm b :=
      fun h => hb ((qtsPrefixIdx_injective m hm h).symm)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem qtsTailLift_apply_tail (m : ℕ) (hm : 3 ≤ m) (x : Fin 3 → K) (t : Fin 3) :
    qtsTailLift (F := F) (K := K) m hm x (qtsTailIdx m hm t) = x t := by
  change (∑ b : Fin 3, x b • Pi.single (qtsTailIdx m hm b) (1 : K))
    (qtsTailIdx m hm t) = x t
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    have hne : qtsTailIdx m hm t ≠ qtsTailIdx m hm b :=
      fun h => hb ((qtsTailIdx_injective m hm h).symm)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem qts_eq_prefix_add_tail (m : ℕ) (hm : 3 ≤ m) (v : Fin (m + 1) → K) :
    qtsPrefixLift (F := F) (K := K) m hm
        (qtsPrefixCoords (F := F) (K := K) m hm v) +
      qtsTailLift (F := F) (K := K) m hm
        (qtsTailCoords (F := F) (K := K) m hm v) = v := by
  ext i
  simp only [Pi.add_apply]
  by_cases hi : i.val < m - 2
  · let j : Fin (m - 2) := ⟨i.val, by omega⟩
    have hij : qtsPrefixIdx m hm j = i := Fin.ext (by simp [j, qtsPrefixIdx])
    rw [← hij]
    rw [qtsPrefixLift_apply_prefix,
      qtsTailLift_apply_prefix _ _ _ _ (by simpa [qtsPrefixIdx] using hi), add_zero]
    rfl
  · have hi' : m - 2 ≤ i.val := by omega
    let t : Fin 3 := ⟨i.val - (m - 2), by omega⟩
    have hit : qtsTailIdx m hm t = i := by
      apply Fin.ext
      simp [t, qtsTailIdx]
      omega
    rw [← hit]
    rw [qtsPrefixLift_apply_tail _ _ _ _ (by simp [qtsTailIdx]), zero_add,
      qtsTailLift_apply_tail]
    rfl


@[expose] noncomputable def qtsP (m : ℕ) (hm : 3 ≤ m) :
    Submodule F (Fin (m + 1) → K) :=
  LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F) (qtsTailCoords (F := F) (K := K) m hm)

@[expose] noncomputable def qtsT (m : ℕ) (hm : 3 ≤ m) :
    Submodule F (Fin (m + 1) → K) :=
  LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F) (qtsPrefixCoords (F := F) (K := K) m hm)

theorem qtsPrefixLift_single (m : ℕ) (hm : 3 ≤ m) (i : Fin (m - 2)) (a : K) :
    qtsPrefixLift (F := F) (K := K) m hm (Pi.single i a) =
      (Pi.single (qtsPrefixIdx m hm i) a : Fin (m + 1) → K) := by
  ext j
  change (∑ b : Fin (m - 2),
      (Pi.single i a : Fin (m - 2) → K) b •
        (Pi.single (qtsPrefixIdx m hm b) (1 : K) : Fin (m + 1) → K)) j =
    (Pi.single (qtsPrefixIdx m hm i) a : Fin (m + 1) → K) j
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · rw [← Pi.single_smul (f := fun _ : Fin (m + 1) => K)]
    simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul, Pi.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem qtsTailLift_single (m : ℕ) (hm : 3 ≤ m) (t : Fin 3) (a : K) :
    qtsTailLift (F := F) (K := K) m hm (Pi.single t a) =
      (Pi.single (qtsTailIdx m hm t) a : Fin (m + 1) → K) := by
  ext j
  change (∑ b : Fin 3,
      (Pi.single t a : Fin 3 → K) b •
        (Pi.single (qtsTailIdx m hm b) (1 : K) : Fin (m + 1) → K)) j =
    (Pi.single (qtsTailIdx m hm t) a : Fin (m + 1) → K) j
  rw [Finset.sum_apply, Finset.sum_eq_single t]
  · rw [← Pi.single_smul (f := fun _ : Fin (m + 1) => K)]
    simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul, Pi.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem qtsPrefixLift_mem_qtsP (m : ℕ) (hm : 3 ≤ m) (x : Fin (m - 2) → K) :
    qtsPrefixLift (F := F) (K := K) m hm x ∈ qtsP (F := F) (K := K) m hm := by
  change qtsPrefixLift (F := F) (K := K) m hm x ∈
    LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
      (qtsTailCoords (F := F) (K := K) m hm)
  rw [LinearMap.mem_ker]
  ext t
  change qtsPrefixLift (F := F) (K := K) m hm x (qtsTailIdx m hm t) = 0
  exact qtsPrefixLift_apply_tail _ _ _ _ (by simp [qtsTailIdx])

theorem qtsTailLift_mem_qtsT (m : ℕ) (hm : 3 ≤ m) (x : Fin 3 → K) :
    qtsTailLift (F := F) (K := K) m hm x ∈ qtsT (F := F) (K := K) m hm := by
  change qtsTailLift (F := F) (K := K) m hm x ∈
    LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
      (qtsPrefixCoords (F := F) (K := K) m hm)
  rw [LinearMap.mem_ker]
  ext t
  change qtsTailLift (F := F) (K := K) m hm x (qtsPrefixIdx m hm t) = 0
  exact qtsTailLift_apply_prefix _ _ _ _ (by simp [qtsPrefixIdx])

theorem qtsP_apply_tail {m : ℕ} (hm : 3 ≤ m) {v : Fin (m + 1) → K}
    (hv : v ∈ qtsP (F := F) (K := K) m hm) {i : Fin (m + 1)} (hi : m - 2 ≤ i.val) :
    v i = 0 := by
  let t : Fin 3 := ⟨i.val - (m - 2), by omega⟩
  have hit : qtsTailIdx m hm t = i := by
    apply Fin.ext
    simp [t, qtsTailIdx]
    omega
  have h := congrFun (LinearMap.mem_ker.mp hv) t
  change v (qtsTailIdx m hm t) = 0 at h
  simpa [hit] using h

theorem qtsT_apply_prefix {m : ℕ} (hm : 3 ≤ m) {v : Fin (m + 1) → K}
    (hv : v ∈ qtsT (F := F) (K := K) m hm) {i : Fin (m + 1)} (hi : i.val < m - 2) :
    v i = 0 := by
  let t : Fin (m - 2) := ⟨i.val, hi⟩
  have hit : qtsPrefixIdx m hm t = i := by
    apply Fin.ext
    simp [t, qtsPrefixIdx]
  have h := congrFun (LinearMap.mem_ker.mp hv) t
  change v (qtsPrefixIdx m hm t) = 0 at h
  simpa [hit] using h

theorem qtsP_sup_qtsT (m : ℕ) (hm : 3 ≤ m) :
    qtsP (F := F) (K := K) m hm ⊔ qtsT (F := F) (K := K) m hm = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have h := qts_eq_prefix_add_tail (F := F) (K := K) m hm v
  exact Submodule.mem_sup.mpr
    ⟨qtsPrefixLift m hm (qtsPrefixCoords m hm v), qtsPrefixLift_mem_qtsP m hm _,
      qtsTailLift m hm (qtsTailCoords m hm v), qtsTailLift_mem_qtsT m hm _, h⟩

theorem qtsP_inf_qtsT (m : ℕ) (hm : 3 ≤ m) :
    qtsP (F := F) (K := K) m hm ⊓ qtsT (F := F) (K := K) m hm = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  ext i
  by_cases hi : i.val < m - 2
  · have h := qtsT_apply_prefix hm hv.2 hi
    simpa using h
  · have hi' : m - 2 ≤ i.val := by omega
    exact qtsP_apply_tail hm hv.1 hi'

theorem qtsPrefixLift_single_mem (m : ℕ) (hm : 3 ≤ m) (i : Fin (m - 2)) (a : K) :
    (Pi.single (qtsPrefixIdx m hm i) a : Fin (m + 1) → K) ∈ qtsP (F := F) (K := K) m hm := by
  change (Pi.single (qtsPrefixIdx m hm i) a : Fin (m + 1) → K) ∈
    LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
      (qtsTailCoords (F := F) (K := K) m hm)
  rw [LinearMap.mem_ker]
  ext t
  change (Pi.single (qtsPrefixIdx m hm i) a : Fin (m + 1) → K) (qtsTailIdx m hm t) = 0
  have hne : qtsPrefixIdx m hm i ≠ qtsTailIdx m hm t := by
    intro h
    have := congrArg Fin.val h
    simp [qtsPrefixIdx, qtsTailIdx] at this
    omega
  exact Pi.single_eq_of_ne (M := fun _ : Fin (m + 1) => K) (Ne.symm hne) a

theorem qtsTailLift_single_mem (m : ℕ) (hm : 3 ≤ m) (t : Fin 3) (a : K) :
    (Pi.single (qtsTailIdx m hm t) a : Fin (m + 1) → K) ∈ qtsT (F := F) (K := K) m hm := by
  change (Pi.single (qtsTailIdx m hm t) a : Fin (m + 1) → K) ∈
    LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
      (qtsPrefixCoords (F := F) (K := K) m hm)
  rw [LinearMap.mem_ker]
  ext i
  change (Pi.single (qtsTailIdx m hm t) a : Fin (m + 1) → K) (qtsPrefixIdx m hm i) = 0
  have hne : qtsTailIdx m hm t ≠ qtsPrefixIdx m hm i := by
    intro h
    have := congrArg Fin.val h
    simp [qtsPrefixIdx, qtsTailIdx] at this
    omega
  exact Pi.single_eq_of_ne (M := fun _ : Fin (m + 1) => K) (Ne.symm hne) a

theorem qtsPolar_prefixLift_single (m : ℕ) (hm : 3 ≤ m) (i : Fin (m - 2)) (a : K)
    (w : Fin (m + 1) → K) :
    QuadraticMap.polar (Qn E (m + 1))
        (qtsPrefixLift (F := F) (K := K) m hm (Pi.single i a : Fin (m - 2) → K)) w =
      QuadraticMap.polar (normQuad E) a (w (qtsPrefixIdx m hm i)) := by
  rw [qtsPrefixLift_single, polar_Qn]
  rw [Finset.sum_eq_single (qtsPrefixIdx m hm i)]
  · simp
  · intro j _ hj
    change QuadraticMap.polar (normQuad E)
      ((Pi.single (qtsPrefixIdx m hm i) a : Fin (m + 1) → K) j) (w j) = 0
    have hzero : (Pi.single (qtsPrefixIdx m hm i) a : Fin (m + 1) → K) j = 0 :=
      Pi.single_eq_of_ne (M := fun _ : Fin (m + 1) => K) hj a
    rw [hzero]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem qtsPolar_tailLift_single (m : ℕ) (hm : 3 ≤ m) (t : Fin 3) (a : K)
    (w : Fin (m + 1) → K) :
    QuadraticMap.polar (Qn E (m + 1))
        (qtsTailLift (F := F) (K := K) m hm (Pi.single t a : Fin 3 → K)) w =
      QuadraticMap.polar (normQuad E) a (w (qtsTailIdx m hm t)) := by
  rw [qtsTailLift_single, polar_Qn]
  rw [Finset.sum_eq_single (qtsTailIdx m hm t)]
  · simp
  · intro j _ hj
    change QuadraticMap.polar (normQuad E)
      ((Pi.single (qtsTailIdx m hm t) a : Fin (m + 1) → K) j) (w j) = 0
    have hzero : (Pi.single (qtsTailIdx m hm t) a : Fin (m + 1) → K) j = 0 :=
      Pi.single_eq_of_ne (M := fun _ : Fin (m + 1) => K) hj a
    rw [hzero]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem qtsT_le_orthogonal_qtsP (m : ℕ) (hm : 3 ≤ m) :
    qtsT (F := F) (K := K) m hm ≤
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (Qn E (m + 1)))
        (qtsP (F := F) (K := K) m hm) := by
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro p hp
  rw [QuadraticMap.polarBilin_apply_apply, polar_Qn]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val < m - 2
  · have hv0 : v i = 0 := qtsT_apply_prefix hm hv hi
    simp [hv0]
  · have hp0 : p i = 0 := qtsP_apply_tail hm hp (by omega)
    simp [hp0]

theorem qts_orthogonal_qtsP_le_qtsT (m : ℕ) (hm : 3 ≤ m) :
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (Qn E (m + 1)))
        (qtsP (F := F) (K := K) m hm) ≤ qtsT (F := F) (K := K) m hm := by
  intro v hv
  change v ∈ LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
    (qtsPrefixCoords (F := F) (K := K) m hm)
  rw [LinearMap.mem_ker]
  ext i'
  change v (qtsPrefixIdx m hm i') = 0
  have hnd := (normQuad_polarBilin_nondegenerate E).2
  refine hnd (v (qtsPrefixIdx m hm i')) ?_
  intro a
  have hmem : qtsPrefixLift (F := F) (K := K) m hm (Pi.single i' a) ∈
      qtsP (F := F) (K := K) m hm := qtsPrefixLift_mem_qtsP m hm _
  have horth := (LinearMap.BilinForm.mem_orthogonal_iff.mp hv)
    (qtsPrefixLift (F := F) (K := K) m hm (Pi.single i' a)) hmem
  rw [QuadraticMap.polarBilin_apply_apply, qtsPolar_prefixLift_single] at horth
  exact horth

theorem qts_orthogonal_qtsP (m : ℕ) (hm : 3 ≤ m) :
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (Qn E (m + 1)))
        (qtsP (F := F) (K := K) m hm) = qtsT (F := F) (K := K) m hm := by
  exact le_antisymm (qts_orthogonal_qtsP_le_qtsT (E := E) m hm)
    (qtsT_le_orthogonal_qtsP (E := E) m hm)



@[expose] def qtsFixesPrefix (m : ℕ)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) : Prop :=
  ∀ (i : Fin (m + 1)), i.val < m - 2 → ∀ a : K,
    X (Pi.single i a : Fin (m + 1) → K) = Pi.single i a

theorem qtsX_fixes_prefix (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X) (x : Fin (m - 2) → K) :
    X (qtsPrefixLift (F := F) (K := K) m hm x) =
      qtsPrefixLift (F := F) (K := K) m hm x := by
  change X (∑ i : Fin (m - 2), x i •
      (Pi.single (qtsPrefixIdx m hm i) (1 : K) : Fin (m + 1) → K)) =
    ∑ i : Fin (m - 2), x i •
      (Pi.single (qtsPrefixIdx m hm i) (1 : K) : Fin (m + 1) → K)
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsingle : x i • (Pi.single (qtsPrefixIdx m hm i) (1 : K) : Fin (m + 1) → K) =
      (Pi.single (qtsPrefixIdx m hm i) (x i) : Fin (m + 1) → K) := by
    rw [← Pi.single_smul (f := fun _ : Fin (m + 1) => K)]
    simp
  rw [hsingle, hfix (qtsPrefixIdx m hm i) (by simp [qtsPrefixIdx])]

theorem qtsX_symm_fixes_prefix (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X) (x : Fin (m - 2) → K) :
    X.symm (qtsPrefixLift (F := F) (K := K) m hm x) =
      qtsPrefixLift (F := F) (K := K) m hm x := by
  have hfix' : qtsFixesPrefix (F := F) (K := K) m X.symm := by
    intro i hi a
    apply X.injective
    rw [X.apply_symm_apply]
    exact (hfix i hi a).symm
  exact qtsX_fixes_prefix m hm X.symm hfix' x

theorem qtsX_maps_tail (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    {v : Fin (m + 1) → K} (hv : qtsPrefixCoords (F := F) (K := K) m hm v = 0) :
    qtsPrefixCoords (F := F) (K := K) m hm (X v) = 0 := by
  have hvT : v ∈ qtsT (F := F) (K := K) m hm := by
    change v ∈ LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
      (qtsPrefixCoords (F := F) (K := K) m hm)
    exact LinearMap.mem_ker.mpr hv
  have hXvT : X v ∈ qtsT (F := F) (K := K) m hm := by
    rw [← qts_orthogonal_qtsP (E := E) m hm]
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro p hp
    have hp' : p ∈ qtsP (F := F) (K := K) m hm := hp
    have hp_eq : p = qtsPrefixLift (F := F) (K := K) m hm
        (qtsPrefixCoords (F := F) (K := K) m hm p) := by
      have htail : qtsTailCoords (F := F) (K := K) m hm p = 0 := by
        change p ∈ LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
          (qtsTailCoords (F := F) (K := K) m hm) at hp
        exact LinearMap.mem_ker.mp hp
      have h := qts_eq_prefix_add_tail (F := F) (K := K) m hm p
      rw [htail, map_zero, add_zero] at h
      exact h.symm
    have hsymm : X.symm p = p := by
      rw [hp_eq]
      exact qtsX_symm_fixes_prefix m hm X hfix _
    have hpol := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hX
      (X.symm p) v
    rw [X.apply_symm_apply, hsymm] at hpol
    have hpv : QuadraticMap.polar (Qn E (m + 1)) p v = 0 := by
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp
        (qtsT_le_orthogonal_qtsP (E := E) m hm hvT)) p hp'
      rwa [QuadraticMap.polarBilin_apply_apply] at h
    rw [QuadraticMap.polarBilin_apply_apply, hpol, hpv]
  change X v ∈ LinearMap.ker (R := F) (R₂ := F) (τ₁₂ := RingHom.id F)
    (qtsPrefixCoords (F := F) (K := K) m hm) at hXvT
  exact LinearMap.mem_ker.mp hXvT



theorem qtsPrefixCoords_tailLift (m : ℕ) (hm : 3 ≤ m) (x : Fin 3 → K) :
    qtsPrefixCoords (F := F) (K := K) m hm
      (qtsTailLift (F := F) (K := K) m hm x) = 0 := by
  ext i
  change qtsTailLift (F := F) (K := K) m hm x (qtsPrefixIdx m hm i) = 0
  exact qtsTailLift_apply_prefix _ _ _ _ (by simp [qtsPrefixIdx])

theorem qtsTailCoords_prefixLift (m : ℕ) (hm : 3 ≤ m) (x : Fin (m - 2) → K) :
    qtsTailCoords (F := F) (K := K) m hm
      (qtsPrefixLift (F := F) (K := K) m hm x) = 0 := by
  ext t
  change qtsPrefixLift (F := F) (K := K) m hm x (qtsTailIdx m hm t) = 0
  exact qtsPrefixLift_apply_tail _ _ _ _ (by simp [qtsTailIdx])

@[expose] noncomputable def qtsTailRestrict (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :
    (Fin 3 → K) →ₗ[F] (Fin 3 → K) :=
  (qtsTailCoords (F := F) (K := K) m hm).comp
    (X.toLinearMap.comp (qtsTailLift (F := F) (K := K) m hm))

theorem qtsTailRestrict_apply (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (x : Fin 3 → K) :
    qtsTailRestrict (F := F) (K := K) m hm X x =
      qtsTailCoords (F := F) (K := K) m hm
        (X (qtsTailLift (F := F) (K := K) m hm x)) := rfl

theorem qtsX_tailLift_apply (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)))
    (x : Fin 3 → K) :
    X (qtsTailLift (F := F) (K := K) m hm x) =
      qtsTailLift (F := F) (K := K) m hm
        (qtsTailRestrict (F := F) (K := K) m hm X x) := by
  have hv := qtsX_maps_tail (E := E) m hm X hX hfix
    (v := qtsTailLift (F := F) (K := K) m hm x)
    (qtsPrefixCoords_tailLift (F := F) (K := K) m hm x)
  have h := qts_eq_prefix_add_tail (F := F) (K := K) m hm
    (X (qtsTailLift (F := F) (K := K) m hm x))
  rw [hv, map_zero, zero_add] at h
  exact h.symm

theorem qtsFixesPrefix_symm (m : ℕ)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X) :
    qtsFixesPrefix (F := F) (K := K) m X.symm := by
  intro i hi a
  apply X.injective
  rw [X.apply_symm_apply, hfix i hi a]

theorem qtsX_symm_mem_orthogonalGroup (m : ℕ)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) :
    X.symm ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  have hX' := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hX
  rw [← hX' (X.symm v), X.apply_symm_apply]

@[expose] noncomputable def qtsTailEquiv (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) :
    (Fin 3 → K) ≃ₗ[F] (Fin 3 → K) where
  toLinearMap := qtsTailRestrict (F := F) (K := K) m hm X
  invFun := qtsTailRestrict (F := F) (K := K) m hm X.symm
  left_inv x := by
    have hXtail := qtsX_tailLift_apply (E := E) m hm X hfix hX x
    have hfixs := qtsFixesPrefix_symm (F := F) (K := K) m X hfix
    have hXs := qtsX_symm_mem_orthogonalGroup (E := E) m X hX
    have hXstail := qtsX_tailLift_apply (E := E) m hm X.symm hfixs hXs
      (qtsTailRestrict (F := F) (K := K) m hm X x)
    have h := congrArg X.symm hXtail
    rw [X.symm_apply_apply, hXstail] at h
    have h' := congrArg (qtsTailCoords (F := F) (K := K) m hm) h
    simpa [qtsTailRestrict, qtsTailCoords_tailLift] using h'.symm
  right_inv x := by
    have hfixs := qtsFixesPrefix_symm (F := F) (K := K) m X hfix
    have hXs := qtsX_symm_mem_orthogonalGroup (E := E) m X hX
    have hXstail := qtsX_tailLift_apply (E := E) m hm X.symm hfixs hXs x
    have hXtail := qtsX_tailLift_apply (E := E) m hm X hfix hX
      (qtsTailRestrict (F := F) (K := K) m hm X.symm x)
    have h := congrArg X hXstail
    rw [X.apply_symm_apply, hXtail] at h
    have h' := congrArg (qtsTailCoords (F := F) (K := K) m hm) h
    simpa [qtsTailRestrict, qtsTailCoords_tailLift] using h'.symm


theorem Qn_tailLift (m : ℕ) (hm : 3 ≤ m) (x : Fin 3 → K) :
    Qn E (m + 1) (qtsTailLift (F := F) (K := K) m hm x) = Qn E 3 x := by
  rw [Qn_apply, Qn_apply]
  let s : Finset (Fin (m + 1)) := Finset.univ.image (qtsTailIdx m hm)
  have hsub : s ⊆ Finset.univ := by intro i _; simp
  have hzero : ∀ i ∈ Finset.univ, i ∉ s → normQuad E (qtsTailLift (F := F) (K := K) m hm x i) = 0 := by
    intro i _ hi
    have hnot : ∀ t : Fin 3, qtsTailIdx m hm t ≠ i := by
      intro t ht
      exact hi (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, ht⟩)
    have hlt : i.val < m - 2 := by
      by_contra h
      have hge : m - 2 ≤ i.val := by omega
      let t : Fin 3 := ⟨i.val - (m - 2), by omega⟩
      have hit : qtsTailIdx m hm t = i := by
        apply Fin.ext
        simp [t, qtsTailIdx]
        omega
      exact hnot t hit
    rw [qtsTailLift_apply_prefix _ _ _ _ hlt]
    simp
  have h1 : (∑ i, normQuad E (qtsTailLift (F := F) (K := K) m hm x i)) =
      ∑ i ∈ s, normQuad E (qtsTailLift (F := F) (K := K) m hm x i) :=
    (Finset.sum_subset hsub hzero).symm
  rw [h1, Finset.sum_image]
  · exact Finset.sum_congr rfl fun t _ => by rw [qtsTailLift_apply_tail]
  · intro a _ b _ h
    exact qtsTailIdx_injective m hm h

theorem qtsTailEquiv_Qn (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)))
    (x : Fin 3 → K) :
    Qn E 3 (qtsTailEquiv (E := E) m hm X hfix hX x) = Qn E 3 x := by
  have hXq := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hX
  calc
    Qn E 3 (qtsTailEquiv (E := E) m hm X hfix hX x) =
        Qn E (m + 1)
          (qtsTailLift (F := F) (K := K) m hm
            (qtsTailEquiv (E := E) m hm X hfix hX x)) :=
      (Qn_tailLift (E := E) m hm _).symm
    _ = Qn E (m + 1) (X (qtsTailLift (F := F) (K := K) m hm x)) := by
      rw [qtsX_tailLift_apply (E := E) m hm X hfix hX]
      rfl
    _ = Qn E (m + 1) (qtsTailLift (F := F) (K := K) m hm x) := hXq _
    _ = Qn E 3 x := Qn_tailLift (E := E) m hm x

theorem qtsTailEquiv_mem_orthogonalGroup (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) :
    qtsTailEquiv (E := E) m hm X hfix hX ∈
      TauCeti.QuadraticMap.orthogonalGroup (Qn E 3) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  exact qtsTailEquiv_Qn (E := E) m hm X hfix hX x



@[expose] noncomputable def qtsFlipPrefixProj (m : ℕ) (hm : 3 ≤ m) :
    (Fin (m + 1) ⊕ Fin (m + 1) → K) →ₗ[K] (Fin (m - 2) ⊕ Fin (m - 2) → K) :=
  LinearMap.pi fun s =>
    match s with
    | Sum.inl i => LinearMap.proj (Sum.inl (qtsPrefixIdx m hm i))
    | Sum.inr i => LinearMap.proj (Sum.inr (qtsPrefixIdx m hm i))

@[expose] noncomputable def qtsFlipTailProj (m : ℕ) (hm : 3 ≤ m) :
    (Fin (m + 1) ⊕ Fin (m + 1) → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) :=
  LinearMap.pi fun s =>
    match s with
    | Sum.inl t => LinearMap.proj (Sum.inl (qtsTailIdx m hm t))
    | Sum.inr t => LinearMap.proj (Sum.inr (qtsTailIdx m hm t))

theorem qtsFlipPrefixProj_inl (m : ℕ) (hm : 3 ≤ m)
    (v : Fin (m + 1) ⊕ Fin (m + 1) → K) (i : Fin (m - 2)) :
    qtsFlipPrefixProj (K := K) m hm v (Sum.inl i) = v (Sum.inl (qtsPrefixIdx m hm i)) := by
  simp [qtsFlipPrefixProj]

theorem qtsFlipPrefixProj_inr (m : ℕ) (hm : 3 ≤ m)
    (v : Fin (m + 1) ⊕ Fin (m + 1) → K) (i : Fin (m - 2)) :
    qtsFlipPrefixProj (K := K) m hm v (Sum.inr i) = v (Sum.inr (qtsPrefixIdx m hm i)) := by
  simp [qtsFlipPrefixProj]

theorem qtsFlipTailProj_inl (m : ℕ) (hm : 3 ≤ m)
    (v : Fin (m + 1) ⊕ Fin (m + 1) → K) (t : Fin 3) :
    qtsFlipTailProj (K := K) m hm v (Sum.inl t) = v (Sum.inl (qtsTailIdx m hm t)) := by
  simp [qtsFlipTailProj]

theorem qtsFlipTailProj_inr (m : ℕ) (hm : 3 ≤ m)
    (v : Fin (m + 1) ⊕ Fin (m + 1) → K) (t : Fin 3) :
    qtsFlipTailProj (K := K) m hm v (Sum.inr t) = v (Sum.inr (qtsTailIdx m hm t)) := by
  simp [qtsFlipTailProj]

@[expose] noncomputable def qtsFlipP (m : ℕ) (hm : 3 ≤ m) :
    Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
  LinearMap.ker (qtsFlipTailProj (K := K) m hm)

@[expose] noncomputable def qtsFlipT (m : ℕ) (hm : 3 ≤ m) :
    Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
  LinearMap.ker (qtsFlipPrefixProj (K := K) m hm)

theorem qtsFlipP_inf_qtsFlipT (m : ℕ) (hm : 3 ≤ m) :
    qtsFlipP (K := K) m hm ⊓ qtsFlipT (K := K) m hm = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  ext s
  rcases s with j | j
  · by_cases hj : j.val < m - 2
    · have h := congrFun (LinearMap.mem_ker.mp hv.2) (Sum.inl ⟨j.val, hj⟩)
      simpa [qtsFlipPrefixProj_inl, qtsPrefixIdx] using h
    · have hj' : m - 2 ≤ j.val := by omega
      let t : Fin 3 := ⟨j.val - (m - 2), by omega⟩
      have hit : qtsTailIdx m hm t = j := by
        apply Fin.ext
        simp [t, qtsTailIdx]
        omega
      have h := congrFun (LinearMap.mem_ker.mp hv.1) (Sum.inl t)
      simpa [qtsFlipTailProj_inl, hit] using h
  · by_cases hj : j.val < m - 2
    · have h := congrFun (LinearMap.mem_ker.mp hv.2) (Sum.inr ⟨j.val, hj⟩)
      simpa [qtsFlipPrefixProj_inr, qtsPrefixIdx] using h
    · have hj' : m - 2 ≤ j.val := by omega
      let t : Fin 3 := ⟨j.val - (m - 2), by omega⟩
      have hit : qtsTailIdx m hm t = j := by
        apply Fin.ext
        simp [t, qtsTailIdx]
        omega
      have h := congrFun (LinearMap.mem_ker.mp hv.1) (Sum.inr t)
      simpa [qtsFlipTailProj_inr, hit] using h

@[expose] noncomputable def qtsLp (m : ℕ) (hm : 3 ≤ m) :
    Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
  Submodule.span K (stdE (K := K) (n := m + 1) '' {i : Fin (m + 1) | i.val < m - 2})

@[expose] noncomputable def qtsTailStdEmb (m : ℕ) (hm : 3 ≤ m) :
    (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K) where
  toFun v :=
    (∑ t : Fin 3, v (Sum.inl t) • stdE (K := K) (n := m + 1) (qtsTailIdx m hm t)) +
      ∑ t : Fin 3, v (Sum.inr t) • stdF (K := K) (n := m + 1) (qtsTailIdx m hm t)
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_add, Finset.smul_sum, smul_assoc, RingHom.id_apply]

theorem qtsTailStdEmb_single_inl (m : ℕ) (hm : 3 ≤ m) (t : Fin 3) :
    qtsTailStdEmb (K := K) m hm
        (Pi.single (Sum.inl t) (1 : K) : Fin 3 ⊕ Fin 3 → K) =
      stdE (K := K) (n := m + 1) (qtsTailIdx m hm t) := by
  ext s
  simp [qtsTailStdEmb, stdE, stdF, Pi.single_apply, Finset.sum_eq_single,
    Sum.inl.injEq, Sum.inr.injEq]

theorem qtsTailStdEmb_single_inr (m : ℕ) (hm : 3 ≤ m) (t : Fin 3) :
    qtsTailStdEmb (K := K) m hm
        (Pi.single (Sum.inr t) (1 : K) : Fin 3 ⊕ Fin 3 → K) =
      stdF (K := K) (n := m + 1) (qtsTailIdx m hm t) := by
  ext s
  simp [qtsTailStdEmb, stdE, stdF, Pi.single_apply, Finset.sum_eq_single,
    Sum.inl.injEq, Sum.inr.injEq]

theorem qtsTailStdEmb_apply_inl (m : ℕ) (hm : 3 ≤ m)
    (v : Fin 3 ⊕ Fin 3 → K) (t : Fin 3) :
    qtsTailStdEmb (K := K) m hm v (Sum.inl (qtsTailIdx m hm t)) = v (Sum.inl t) := by
  simp [qtsTailStdEmb, stdE, stdF, Pi.single_apply]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    have hne : qtsTailIdx m hm t ≠ qtsTailIdx m hm b :=
      fun h => hb ((qtsTailIdx_injective m hm h).symm)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem qtsTailStdEmb_apply_inr (m : ℕ) (hm : 3 ≤ m)
    (v : Fin 3 ⊕ Fin 3 → K) (t : Fin 3) :
    qtsTailStdEmb (K := K) m hm v (Sum.inr (qtsTailIdx m hm t)) = v (Sum.inr t) := by
  simp [qtsTailStdEmb, stdE, stdF, Pi.single_apply]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    have hne : qtsTailIdx m hm t ≠ qtsTailIdx m hm b :=
      fun h => hb ((qtsTailIdx_injective m hm h).symm)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem qtsTailStdEmb_injective (m : ℕ) (hm : 3 ≤ m) :
    Function.Injective (qtsTailStdEmb (K := K) m hm) := by
  intro v w h
  ext s
  rcases s with t | t
  · have := congrFun h (Sum.inl (qtsTailIdx m hm t))
    simpa [qtsTailStdEmb_apply_inl] using this
  · have := congrFun h (Sum.inr (qtsTailIdx m hm t))
    simpa [qtsTailStdEmb_apply_inr] using this

theorem qtsTailStdEmb_stdE (m : ℕ) (hm : 3 ≤ m) (t : Fin 3) :
    qtsTailStdEmb (K := K) m hm (stdE (K := K) (n := 3) t) =
      stdE (K := K) (n := m + 1) (qtsTailIdx m hm t) :=
  qtsTailStdEmb_single_inl m hm t

theorem qtsTailStdEmb_stdF (m : ℕ) (hm : 3 ≤ m) (t : Fin 3) :
    qtsTailStdEmb (K := K) m hm (stdF (K := K) (n := 3) t) =
      stdF (K := K) (n := m + 1) (qtsTailIdx m hm t) :=
  qtsTailStdEmb_single_inr m hm t

@[expose] noncomputable def qtsLt (m : ℕ) (hm : 3 ≤ m) :
    Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
  (stdLag 3 K).map (qtsTailStdEmb (K := K) m hm)

theorem qtsLt_eq_span (m : ℕ) (hm : 3 ≤ m) :
    qtsLt (K := K) m hm =
      Submodule.span K (stdE (K := K) (n := m + 1) '' {i : Fin (m + 1) | m - 2 ≤ i.val}) := by
  rw [qtsLt, stdLag_eq_span_stdE, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
    exact ⟨qtsTailIdx m hm i, by simp [qtsTailIdx]; omega,
      (qtsTailStdEmb_stdE m hm i).symm⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : m - 2 ≤ j.val := by simpa using hj
    let t : Fin 3 := ⟨j.val - (m - 2), by omega⟩
    have hit : qtsTailIdx m hm t = j := by
      apply Fin.ext
      simp [t, qtsTailIdx]
      omega
    exact ⟨stdE (K := K) (n := 3) t, ⟨t, rfl⟩,
      by rw [qtsTailStdEmb_stdE, hit]⟩

theorem qtsLp_finrank (m : ℕ) (hm : 3 ≤ m) :
    Module.finrank K (qtsLp (K := K) m hm) = m - 2 := by
  rw [qtsLp]
  exact aRes_finrank_stdE_span (K := K) (m + 1) (m - 2) (by omega)

theorem qtsLt_finrank (m : ℕ) (hm : 3 ≤ m) :
    Module.finrank K (qtsLt (K := K) m hm) = 3 := by
  rw [qtsLt]
  let e := Submodule.equivMapOfInjective (qtsTailStdEmb (K := K) m hm)
    (qtsTailStdEmb_injective m hm) (stdLag 3 K)
  rw [← e.finrank_eq, finrank_stdLag]

theorem qtsPrefixStdE_mem_qtsFlipP (m : ℕ) (hm : 3 ≤ m)
    (i : Fin (m + 1)) (hi : i.val < m - 2) :
    stdE (K := K) (n := m + 1) i ∈ qtsFlipP (K := K) m hm := by
  rw [qtsFlipP, LinearMap.mem_ker]
  ext s
  rcases s with j | j
  · rw [qtsFlipTailProj_inl]
    have hne : (Sum.inl (qtsTailIdx m hm j) : Fin (m + 1) ⊕ Fin (m + 1)) ≠ Sum.inl i := by
      intro h
      have hidx : qtsTailIdx m hm j = i := by simpa using h
      have hval := congrArg Fin.val hidx
      simp [qtsPrefixIdx, qtsTailIdx] at hval
      omega
    exact Pi.single_eq_of_ne (M := fun _ : Fin (m + 1) ⊕ Fin (m + 1) => K) hne (1 : K)
  · rw [qtsFlipTailProj_inr]
    simp [stdE]

theorem qtsTailStdE_mem_qtsFlipT (m : ℕ) (hm : 3 ≤ m)
    (i : Fin (m + 1)) (hi : m - 2 ≤ i.val) :
    stdE (K := K) (n := m + 1) i ∈ qtsFlipT (K := K) m hm := by
  rw [qtsFlipT, LinearMap.mem_ker]
  ext s
  rcases s with j | j
  · rw [qtsFlipPrefixProj_inl]
    have hne : (Sum.inl (qtsPrefixIdx m hm j) : Fin (m + 1) ⊕ Fin (m + 1)) ≠ Sum.inl i := by
      intro h
      have hidx : qtsPrefixIdx m hm j = i := by simpa using h
      have hval := congrArg Fin.val hidx
      simp [qtsPrefixIdx] at hval
      omega
    exact Pi.single_eq_of_ne (M := fun _ : Fin (m + 1) ⊕ Fin (m + 1) => K) hne (1 : K)
  · rw [qtsFlipPrefixProj_inr]
    simp [stdE]

theorem qtsLp_le_qtsFlipP (m : ℕ) (hm : 3 ≤ m) :
    qtsLp (K := K) m hm ≤ qtsFlipP (K := K) m hm := by
  rw [qtsLp]
  refine Submodule.span_le.mpr ?_
  rintro v ⟨i, hi, rfl⟩
  exact qtsPrefixStdE_mem_qtsFlipP m hm i hi

theorem qtsLt_le_qtsFlipT (m : ℕ) (hm : 3 ≤ m) :
    qtsLt (K := K) m hm ≤ qtsFlipT (K := K) m hm := by
  rw [qtsLt_eq_span]
  refine Submodule.span_le.mpr ?_
  rintro v ⟨j, hj, rfl⟩
  exact qtsTailStdE_mem_qtsFlipT m hm j (by simpa using hj)



theorem qts_bcLin_stdE_prefix (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (i : Fin (m + 1)) (hi : i.val < m - 2) :
    bcLin E (m + 1) X.toLinearMap (stdE (K := K) (n := m + 1) i) =
      stdE (K := K) (n := m + 1) i := by
  let Y : (Fin (m + 1) ⊕ Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    bcLin E (m + 1) X.toLinearMap
  have h := congrArg Y (bcDelta_smul_stdE (E := E) (n := m + 1) i)
  have hsingle : (X : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
      (Pi.single i (1 : K) : Fin (m + 1) → K) = Pi.single i 1 := by
    simpa using hfix i hi 1
  have htheta : (X : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
      (bcTheta E • (Pi.single i (1 : K) : Fin (m + 1) → K)) =
      bcTheta E • Pi.single i 1 := by
    calc
      X (bcTheta E • (Pi.single i (1 : K) : Fin (m + 1) → K)) =
          X (Pi.single i (bcTheta E • (1 : K))) := by rw [Pi.single_smul]
      _ = Pi.single i (bcTheta E • (1 : K)) := hfix i hi (bcTheta E • 1)
      _ = bcTheta E • Pi.single i 1 := by rw [Pi.single_smul]
  simp only [Y, map_smul, map_add, bcLin_jEmb] at h
  rw [hsingle, htheta] at h
  rw [← bcDelta_smul_stdE (E := E) (n := m + 1) i] at h
  ext s
  have hcoord := congrFun h s
  simp only [Pi.smul_apply, smul_eq_mul] at hcoord
  exact mul_left_cancel₀ (bcDelta_ne_zero E) hcoord

theorem qts_bcLin_stdF_prefix (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (i : Fin (m + 1)) (hi : i.val < m - 2) :
    bcLin E (m + 1) X.toLinearMap (stdF (K := K) (n := m + 1) i) =
      stdF (K := K) (n := m + 1) i := by
  let Y : (Fin (m + 1) ⊕ Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    bcLin E (m + 1) X.toLinearMap
  have h := congrArg Y (bcDelta_smul_stdF (E := E) (n := m + 1) i)
  have hsingle : (X : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
      (Pi.single i (1 : K) : Fin (m + 1) → K) = Pi.single i 1 := by
    simpa using hfix i hi 1
  have htheta : (X : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
      (bcTheta E • (Pi.single i (1 : K) : Fin (m + 1) → K)) =
      bcTheta E • Pi.single i 1 := by
    calc
      X (bcTheta E • (Pi.single i (1 : K) : Fin (m + 1) → K)) =
          X (Pi.single i (bcTheta E • (1 : K))) := by rw [Pi.single_smul]
      _ = Pi.single i (bcTheta E • (1 : K)) := hfix i hi (bcTheta E • 1)
      _ = bcTheta E • Pi.single i 1 := by rw [Pi.single_smul]
  simp only [Y, map_smul, map_add, bcLin_jEmb] at h
  rw [hsingle, htheta] at h
  rw [← bcDelta_smul_stdF (E := E) (n := m + 1) i] at h
  ext s
  have hcoord := congrFun h s
  simp only [Pi.smul_apply, smul_eq_mul] at hcoord
  exact mul_left_cancel₀ (bcDelta_ne_zero E) hcoord



theorem qtsPrefixCoords_single_tail (m : ℕ) (hm : 3 ≤ m)
    (i : Fin (m + 1)) (hi : m - 2 ≤ i.val) (a : K) :
    qtsPrefixCoords (F := F) (K := K) m hm
      (Pi.single i a : Fin (m + 1) → K) = 0 := by
  ext j
  change (Pi.single i a : Fin (m + 1) → K) (qtsPrefixIdx m hm j) = 0
  have hne : qtsPrefixIdx m hm j ≠ i := by
    intro h
    have hval := congrArg Fin.val h
    simp [qtsPrefixIdx] at hval
    omega
  exact Pi.single_eq_of_ne (M := fun _ : Fin (m + 1) => K) hne a

theorem jEmb_mem_qtsFlipT_of_prefix_zero (m : ℕ) (hm : 3 ≤ m)
    {v : Fin (m + 1) → K}
    (hv : qtsPrefixCoords (F := F) (K := K) m hm v = 0) :
    jEmb E (m + 1) v ∈ qtsFlipT (K := K) m hm := by
  rw [qtsFlipT, LinearMap.mem_ker]
  ext s
  rcases s with i | i
  · rw [qtsFlipPrefixProj_inl]
    have h := congrFun hv i
    simpa [qtsPrefixCoords] using h
  · rw [qtsFlipPrefixProj_inr]
    have h := congrFun hv i
    have h0 : v (qtsPrefixIdx m hm i) = 0 := by simpa [qtsPrefixCoords] using h
    simp [h0]

theorem qts_bcLin_stdE_tail_mem_qtsFlipT (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)))
    (i : Fin (m + 1)) (hi : m - 2 ≤ i.val) :
    bcLin E (m + 1) X.toLinearMap (stdE (K := K) (n := m + 1) i) ∈
      qtsFlipT (K := K) m hm := by
  let Y : (Fin (m + 1) ⊕ Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    bcLin E (m + 1) X.toLinearMap
  have h := congrArg Y (bcDelta_smul_stdE (E := E) (n := m + 1) i)
  simp only [Y, map_smul, map_add, bcLin_jEmb] at h
  have hv1 : qtsPrefixCoords (F := F) (K := K) m hm
      ((X : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
        (Pi.single i (1 : K) : Fin (m + 1) → K)) = 0 := by
    exact qtsX_maps_tail (E := E) m hm X hX hfix
      (qtsPrefixCoords_single_tail m hm i hi 1)
  have hvθ : qtsPrefixCoords (F := F) (K := K) m hm
      ((X : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
        (bcTheta E • (Pi.single i (1 : K) : Fin (m + 1) → K))) = 0 := by
    have harg : bcTheta E • (Pi.single i (1 : K) : Fin (m + 1) → K) =
        Pi.single i (bcTheta E) := by
      rw [← Pi.single_smul (f := fun _ : Fin (m + 1) => K)]
      simp
    rw [harg]
    exact qtsX_maps_tail (E := E) m hm X hX hfix
      (qtsPrefixCoords_single_tail m hm i hi (bcTheta E))
  have hmem : bcSigmaTheta E • jEmb E (m + 1)
        ((X : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
          (Pi.single i (1 : K) : Fin (m + 1) → K)) +
      jEmb E (m + 1)
        ((X : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
          (bcTheta E • (Pi.single i (1 : K) : Fin (m + 1) → K))) ∈
      qtsFlipT (K := K) m hm :=
    (qtsFlipT (K := K) m hm).add_mem
      ((qtsFlipT (K := K) m hm).smul_mem (bcSigmaTheta E)
        (jEmb_mem_qtsFlipT_of_prefix_zero (E := E) m hm hv1))
      (jEmb_mem_qtsFlipT_of_prefix_zero (E := E) m hm hvθ)
  rw [← h] at hmem
  have hinv : (bcDelta E)⁻¹ • ((bcDelta E) •
      bcLin E (m + 1) X.toLinearMap (stdE (K := K) (n := m + 1) i)) =
      bcLin E (m + 1) X.toLinearMap (stdE (K := K) (n := m + 1) i) := by
    rw [smul_smul, inv_mul_cancel₀ (bcDelta_ne_zero E), one_smul]
  rw [← hinv]
  exact (qtsFlipT (K := K) m hm).smul_mem (bcDelta E)⁻¹ hmem

theorem qts_bcLin_stdF_tail_mem_qtsFlipT (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)))
    (i : Fin (m + 1)) (hi : m - 2 ≤ i.val) :
    bcLin E (m + 1) X.toLinearMap (stdF (K := K) (n := m + 1) i) ∈
      qtsFlipT (K := K) m hm := by
  let Y : (Fin (m + 1) ⊕ Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    bcLin E (m + 1) X.toLinearMap
  have h := congrArg Y (bcDelta_smul_stdF (E := E) (n := m + 1) i)
  simp only [Y, map_smul, map_add, bcLin_jEmb] at h
  have hv1 : qtsPrefixCoords (F := F) (K := K) m hm
      ((X : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
        (Pi.single i (1 : K) : Fin (m + 1) → K)) = 0 := by
    exact qtsX_maps_tail (E := E) m hm X hX hfix
      (qtsPrefixCoords_single_tail m hm i hi 1)
  have hvθ : qtsPrefixCoords (F := F) (K := K) m hm
      ((X : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
        (bcTheta E • (Pi.single i (1 : K) : Fin (m + 1) → K))) = 0 := by
    have harg : bcTheta E • (Pi.single i (1 : K) : Fin (m + 1) → K) =
        Pi.single i (bcTheta E) := by
      rw [← Pi.single_smul (f := fun _ : Fin (m + 1) => K)]
      simp
    rw [harg]
    exact qtsX_maps_tail (E := E) m hm X hX hfix
      (qtsPrefixCoords_single_tail m hm i hi (bcTheta E))
  have hmem : bcTheta E • jEmb E (m + 1)
        ((X : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
          (Pi.single i (1 : K) : Fin (m + 1) → K)) +
      jEmb E (m + 1)
        ((X : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))
          (bcTheta E • (Pi.single i (1 : K) : Fin (m + 1) → K))) ∈
      qtsFlipT (K := K) m hm :=
    (qtsFlipT (K := K) m hm).add_mem
      ((qtsFlipT (K := K) m hm).smul_mem (bcTheta E)
        (jEmb_mem_qtsFlipT_of_prefix_zero (E := E) m hm hv1))
      (jEmb_mem_qtsFlipT_of_prefix_zero (E := E) m hm hvθ)
  rw [← h] at hmem
  have hinv : (bcDelta E)⁻¹ • ((bcDelta E) •
      bcLin E (m + 1) X.toLinearMap (stdF (K := K) (n := m + 1) i)) =
      bcLin E (m + 1) X.toLinearMap (stdF (K := K) (n := m + 1) i) := by
    rw [smul_smul, inv_mul_cancel₀ (bcDelta_ne_zero E), one_smul]
  rw [← hinv]
  exact (qtsFlipT (K := K) m hm).smul_mem (bcDelta E)⁻¹ hmem



theorem eq_of_eqOn_range_jEmb_of_codomain {m n : ℕ}
    {f g : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin n ⊕ Fin n → K)}
    (h : ∀ x : Fin m → K, f (jEmb E m x) = g (jEmb E m x)) : f = g := by
  apply LinearMap.ext
  intro v
  have hv : v ∈ Submodule.span K (Set.range (jEmb E m)) := by
    rw [span_range_jEmb]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun v _ => f v = g v) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨x, rfl⟩
    exact h x
  · simp
  · intro u w _ _ hu hw
    rw [map_add, map_add, hu, hw]
  · intro c u _ hu
    rw [map_smul, map_smul, hu]

theorem qtsTailStdEmb_apply_prefix_inl (m : ℕ) (hm : 3 ≤ m)
    (v : Fin 3 ⊕ Fin 3 → K) (j : Fin (m + 1)) (hj : j.val < m - 2) :
    qtsTailStdEmb (K := K) m hm v (Sum.inl j) = 0 := by
  rw [qtsTailStdEmb]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply,
    Pi.add_apply, stdE, stdF]
  have h2 : (∑ t : Fin 3,
      v (Sum.inr t) • (Pi.single (Sum.inr (qtsTailIdx m hm t)) 1 :
        Fin (m + 1) ⊕ Fin (m + 1) → K) (Sum.inl j)) = 0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [Pi.single_apply]
  rw [h2, add_zero]
  refine Finset.sum_eq_zero fun t _ => ?_
  have hne : qtsTailIdx m hm t ≠ j := by
    intro h
    have hval := congrArg Fin.val h
    simp [qtsTailIdx] at hval
    omega
  simp [Pi.single_apply, hne]

theorem qtsTailStdEmb_apply_prefix_inr (m : ℕ) (hm : 3 ≤ m)
    (v : Fin 3 ⊕ Fin 3 → K) (j : Fin (m + 1)) (hj : j.val < m - 2) :
    qtsTailStdEmb (K := K) m hm v (Sum.inr j) = 0 := by
  rw [qtsTailStdEmb]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply,
    Pi.add_apply, stdE, stdF]
  have h1 : (∑ t : Fin 3,
      v (Sum.inl t) • (Pi.single (Sum.inl (qtsTailIdx m hm t)) 1 :
        Fin (m + 1) ⊕ Fin (m + 1) → K) (Sum.inr j)) = 0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [Pi.single_apply]
  rw [h1, zero_add]
  refine Finset.sum_eq_zero fun t _ => ?_
  have hne : qtsTailIdx m hm t ≠ j := by
    intro h
    have hval := congrArg Fin.val h
    simp [qtsTailIdx] at hval
    omega
  simp [Pi.single_apply, hne]

theorem qtsTailStdEmb_jEmb (m : ℕ) (hm : 3 ≤ m) (x : Fin 3 → K) :
    qtsTailStdEmb (K := K) m hm (jEmb E 3 x) =
      jEmb E (m + 1) (qtsTailLift (F := F) (K := K) m hm x) := by
  ext s
  rcases s with j | j
  · by_cases hj : j.val < m - 2
    · rw [qtsTailStdEmb_apply_prefix_inl m hm (jEmb E 3 x) j hj]
      simp [jEmb_apply_inl, qtsTailLift_apply_prefix _ _ _ _ hj]
    · have hj' : m - 2 ≤ j.val := by omega
      let t : Fin 3 := ⟨j.val - (m - 2), by omega⟩
      have hit : qtsTailIdx m hm t = j := by
        apply Fin.ext
        simp [t, qtsTailIdx]
        omega
      rw [← hit, qtsTailStdEmb_apply_inl]
      simp [jEmb_apply_inl, qtsTailLift_apply_tail]
  · by_cases hj : j.val < m - 2
    · rw [qtsTailStdEmb_apply_prefix_inr m hm (jEmb E 3 x) j hj]
      simp [jEmb_apply_inr, qtsTailLift_apply_prefix _ _ _ _ hj]
    · have hj' : m - 2 ≤ j.val := by omega
      let t : Fin 3 := ⟨j.val - (m - 2), by omega⟩
      have hit : qtsTailIdx m hm t = j := by
        apply Fin.ext
        simp [t, qtsTailIdx]
        omega
      rw [← hit, qtsTailStdEmb_apply_inr]
      simp [jEmb_apply_inr, qtsTailLift_apply_tail]

theorem qts_bcLin_comp_tailStdEmb (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) :
    (bcLin E (m + 1) X.toLinearMap).comp (qtsTailStdEmb (K := K) m hm) =
      (qtsTailStdEmb (K := K) m hm).comp
        (bcLin E 3 (qtsTailEquiv (E := E) m hm X hfix hX).toLinearMap) := by
  apply eq_of_eqOn_range_jEmb_of_codomain (E := E) (m := 3) (n := m + 1)
  intro x
  simp only [LinearMap.comp_apply]
  calc
    bcLin E (m + 1) X.toLinearMap
        (qtsTailStdEmb (K := K) m hm (jEmb E 3 x)) =
      bcLin E (m + 1) X.toLinearMap
        (jEmb E (m + 1) (qtsTailLift (F := F) (K := K) m hm x)) := by
      rw [qtsTailStdEmb_jEmb]
    _ = jEmb E (m + 1)
        (X ((qtsTailLift (F := F) (K := K) m hm x))) := by
      rw [bcLin_jEmb]
      rfl
    _ = jEmb E (m + 1)
        (qtsTailLift (F := F) (K := K) m hm
          (qtsTailEquiv (E := E) m hm X hfix hX x)) := by
      rw [qtsX_tailLift_apply (E := E) m hm X hfix hX]
      rfl
    _ = qtsTailStdEmb (K := K) m hm
        (jEmb E 3 (qtsTailEquiv (E := E) m hm X hfix hX x)) := by
      rw [qtsTailStdEmb_jEmb]
    _ = qtsTailStdEmb (K := K) m hm
        (bcLin E 3 (qtsTailEquiv (E := E) m hm X hfix hX).toLinearMap
          (jEmb E 3 x)) := by
      rw [bcLin_jEmb]
      rfl



theorem qts_inf_sup_sup_eq_sup_inf {V : Type} [AddCommGroup V] [Module K V]
    {Wp Wt Lp Lt Yt : Submodule K V}
    (hW : Wp ⊓ Wt = ⊥) (hLp : Lp ≤ Wp) (hLt : Lt ≤ Wt) (hYt : Yt ≤ Wt) :
    (Lp ⊔ Lt) ⊓ (Lp ⊔ Yt) = Lp ⊔ (Lt ⊓ Yt) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨p1, hp1, l1, hl1, rfl⟩ := Submodule.mem_sup.mp hx1
    obtain ⟨p2, hp2, y1, hy1, hxy⟩ := Submodule.mem_sup.mp hx2
    have hdiff : p1 - p2 = y1 - l1 := by
      rw [sub_eq_sub_iff_add_eq_add]
      simpa [add_comm, add_left_comm, add_assoc] using hxy.symm
    have hWmem : p1 - p2 ∈ Wp ⊓ Wt :=
      ⟨Wp.sub_mem (hLp hp1) (hLp hp2),
        hdiff ▸ Wt.sub_mem (hYt hy1) (hLt hl1)⟩
    rw [hW, Submodule.mem_bot, sub_eq_zero] at hWmem
    have hyl : y1 = l1 := by
      have h0 : y1 - l1 = 0 := by
        rw [← hdiff, hWmem, sub_self]
      exact sub_eq_zero.mp h0
    exact Submodule.mem_sup.mpr ⟨p1, hp1, l1, ⟨hl1, hyl ▸ hy1⟩, rfl⟩
  · refine sup_le ?_ ?_
    · exact le_inf le_sup_left le_sup_left
    · exact le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans le_sup_right)

theorem qts_bcLin_fixes_qtsLp (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X) :
    ∀ v ∈ qtsLp (K := K) m hm,
      bcLin E (m + 1) X.toLinearMap v = v := by
  intro v hv
  rw [qtsLp] at hv
  refine Submodule.span_induction (p := fun v _ =>
    bcLin E (m + 1) X.toLinearMap v = v) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨i, hi, rfl⟩
    exact qts_bcLin_stdE_prefix (E := E) m hm X hfix i hi
  · simp
  · intro a b _ _ ha hb
    rw [map_add, ha, hb]
  · intro c a _ ha
    rw [map_smul, ha]

theorem qts_bcLin_qtsLt_map_le_qtsFlipT (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) :
    (qtsLt (K := K) m hm).map (bcLin E (m + 1) X.toLinearMap) ≤
      qtsFlipT (K := K) m hm := by
  rw [qtsLt_eq_span, Submodule.map_span]
  refine Submodule.span_le.mpr ?_
  rintro v ⟨w, ⟨j, hj, rfl⟩, rfl⟩
  exact qts_bcLin_stdE_tail_mem_qtsFlipT (E := E) m hm X hfix hX j (by simpa using hj)



theorem qts_stdLag_eq_sup (m : ℕ) (hm : 3 ≤ m) :
    stdLag (m + 1) K = qtsLp (K := K) m hm ⊔ qtsLt (K := K) m hm := by
  rw [stdLag_eq_span_stdE, qtsLp, qtsLt_eq_span, ← Submodule.span_union]
  congr 1
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    by_cases h : j.val < m - 2
    · left
      exact ⟨j, h, rfl⟩
    · right
      exact ⟨j, Nat.le_of_not_lt h, rfl⟩
  · rintro (⟨j, -, rfl⟩ | ⟨j, -, rfl⟩)
    · exact ⟨j, rfl⟩
    · exact ⟨j, rfl⟩

theorem qts_bcLin_map_qtsLp (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X) :
    (qtsLp (K := K) m hm).map (bcLin E (m + 1) X.toLinearMap) =
      qtsLp (K := K) m hm := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [qts_bcLin_fixes_qtsLp (E := E) m hm X hfix w hw]
    exact hw
  · intro hv
    exact ⟨v, hv, qts_bcLin_fixes_qtsLp (E := E) m hm X hfix v hv⟩



theorem qts_bcLin_map_stdLag (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X) :
    (stdLag (m + 1) K).map (bcLin E (m + 1) X.toLinearMap) =
      qtsLp (K := K) m hm ⊔ (qtsLt (K := K) m hm).map
        (bcLin E (m + 1) X.toLinearMap) := by
  rw [qts_stdLag_eq_sup, Submodule.map_sup, qts_bcLin_map_qtsLp (E := E) m hm X hfix]

theorem qts_stdLag_inf_eq (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) :
    stdLag (m + 1) K ⊓ (stdLag (m + 1) K).map
        (bcLin E (m + 1) X.toLinearMap) =
      qtsLp (K := K) m hm ⊔
        (qtsLt (K := K) m hm ⊓ (qtsLt (K := K) m hm).map
          (bcLin E (m + 1) X.toLinearMap)) := by
  rw [qts_bcLin_map_stdLag (E := E) m hm X hfix, qts_stdLag_eq_sup]
  exact qts_inf_sup_sup_eq_sup_inf (K := K)
    (qtsFlipP_inf_qtsFlipT (K := K) m hm)
    (qtsLp_le_qtsFlipP (K := K) m hm)
    (qtsLt_le_qtsFlipT (K := K) m hm)
    (qts_bcLin_qtsLt_map_le_qtsFlipT (E := E) m hm X hfix hX)

theorem qts_stdLag_inf_finrank (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) :
    Module.finrank K ↥(stdLag (m + 1) K ⊓ (stdLag (m + 1) K).map
        (bcLin E (m + 1) X.toLinearMap)) =
      (m - 2) + Module.finrank K
        ↥(qtsLt (K := K) m hm ⊓ (qtsLt (K := K) m hm).map
          (bcLin E (m + 1) X.toLinearMap)) := by
  rw [qts_stdLag_inf_eq (E := E) m hm X hfix hX]
  have hLpLt : qtsLp (K := K) m hm ⊓ qtsLt (K := K) m hm = ⊥ := by
    refine le_bot_iff.mp (le_trans (inf_le_inf
      (qtsLp_le_qtsFlipP (K := K) m hm)
      (qtsLt_le_qtsFlipT (K := K) m hm)) ?_)
    rw [qtsFlipP_inf_qtsFlipT]
  have hdisj : qtsLp (K := K) m hm ⊓
      (qtsLt (K := K) m hm ⊓ (qtsLt (K := K) m hm).map
        (bcLin E (m + 1) X.toLinearMap)) = ⊥ := by
    rw [← inf_assoc, hLpLt]
    simp
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (qtsLp (K := K) m hm)
    (qtsLt (K := K) m hm ⊓ (qtsLt (K := K) m hm).map
      (bcLin E (m + 1) X.toLinearMap))
  rw [hdisj, finrank_bot, add_zero] at hdim
  have hLp : Module.finrank K (qtsLp (K := K) m hm) = m - 2 :=
    qtsLp_finrank (K := K) m hm
  omega

theorem qts_tail_inf_finrank (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) :
    Module.finrank K
        ↥(qtsLt (K := K) m hm ⊓ (qtsLt (K := K) m hm).map
          (bcLin E (m + 1) X.toLinearMap)) =
      Module.finrank K
        ↥(stdLag 3 K ⊓ (stdLag 3 K).map
          (bcLin E 3 (qtsTailEquiv (E := E) m hm X hfix hX).toLinearMap)) := by
  let r := qtsTailEquiv (E := E) m hm X hfix hX
  rw [qtsLt]
  rw [← Submodule.map_comp]
  rw [qts_bcLin_comp_tailStdEmb (E := E) m hm X hfix hX]
  rw [Submodule.map_comp]
  rw [← Submodule.map_inf (qtsTailStdEmb (K := K) m hm)
    (qtsTailStdEmb_injective m hm)]
  let e := Submodule.equivMapOfInjective (qtsTailStdEmb (K := K) m hm)
    (qtsTailStdEmb_injective m hm)
    (stdLag 3 K ⊓ (stdLag 3 K).map (bcLin E 3 r.toLinearMap))
  rw [← e.finrank_eq]



theorem qtsTailEquiv_mem_rulingGroup_of_even (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)))
    (hEven : Even ((m + 1) - Module.finrank K
      ↥(stdLag (m + 1) K ⊓ (stdLag (m + 1) K).map
        (bcLin E (m + 1) X.toLinearMap)))) :
    qtsTailEquiv (E := E) m hm X hfix hX ∈ rulingGroup E 3 := by
  let r := qtsTailEquiv (E := E) m hm X hfix hX
  let d := Module.finrank K
    ↥(stdLag 3 K ⊓ (stdLag 3 K).map (bcLin E 3 r.toLinearMap))
  have hfin := qts_stdLag_inf_finrank (E := E) m hm X hfix hX
  have htail := qts_tail_inf_finrank (E := E) m hm X hfix hX
  have htotal : Module.finrank K
      ↥(stdLag (m + 1) K ⊓ (stdLag (m + 1) K).map
        (bcLin E (m + 1) X.toLinearMap)) = (m - 2) + d := by
    rw [hfin, htail]
  have hEven' : Even ((m + 1) - ((m - 2) + d)) := by
    simpa [htotal] using hEven
  have hdle : d ≤ 3 := by
    have hmono := Submodule.finrank_mono
      (inf_le_left : stdLag 3 K ⊓ (stdLag 3 K).map
        (bcLin E 3 r.toLinearMap) ≤ stdLag 3 K)
    simpa [d, finrank_stdLag 3 K] using hmono
  have hEq : (m + 1) - ((m - 2) + d) = 3 - d := by omega
  refine (mem_rulingGroup E 3 r).mpr ⟨?_, ?_⟩
  · exact qtsTailEquiv_mem_orthogonalGroup (E := E) m hm X hfix hX
  · simpa [hEq] using hEven'

theorem qtsTailEquiv_mem_rulingGroup (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :
    qtsTailEquiv (E := E) m hm X hfix
      (Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) hX) ∈
      CFSG.ClassicalInvolution.PhanDn.rulingGroup E 3 := by
  let hXo := Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) hX
  have hrul : X ∈ CFSG.ClassicalInvolution.PhanDn.rulingGroup E (m + 1) :=
    CFSG.ClassicalInvolution.PhanDn.orthDerived_le_rulingGroup E (m + 1) hX
  have hEven : Even ((m + 1) - Module.finrank K
      ↥(stdLag (m + 1) K ⊓ (stdLag (m + 1) K).map
        (bcLin E (m + 1) X.toLinearMap))) :=
    ((CFSG.ClassicalInvolution.PhanDn.mem_rulingGroup E (m + 1) X).mp hrul).2
  exact qtsTailEquiv_mem_rulingGroup_of_even (E := E) m hm X hfix hXo hEven



theorem qts_winExt_prefixLift (m : ℕ) (hm : 3 ≤ m)
    (φ : Module.End F (Fin 3 → K)) (x : Fin (m - 2) → K) :
    CFSG.StandardType.QTwo.winExt (F := F) (K := K) m hm φ
        (qtsPrefixLift (F := F) (K := K) m hm x) =
      qtsPrefixLift (F := F) (K := K) m hm x := by
  ext i
  by_cases hi : i.val < m - 2
  · rw [CFSG.StandardType.QTwo.winExt_apply_of_lt (F := F) (K := K) m hm φ _ i hi]
  · have hi' : m - 2 ≤ i.val := by omega
    let t : Fin 3 := ⟨i.val - (m - 2), by omega⟩
    have hit : (⟨m - 2 + t.val, by omega⟩ : Fin (m + 1)) = i := by
      apply Fin.ext
      simp [t]
      omega
    rw [← hit, CFSG.StandardType.QTwo.winExt_apply_window]
    have hzero : (fun s : Fin 3 =>
        qtsPrefixLift (F := F) (K := K) m hm x ⟨m - 2 + s.val, by omega⟩) = 0 := by
      funext s
      simpa [qtsTailIdx] using
        (qtsPrefixLift_apply_tail (F := F) (K := K) m hm x (qtsTailIdx m hm s)
          (by simp [qtsTailIdx]))
    rw [hzero, map_zero]
    simpa [qtsTailIdx] using
      (qtsPrefixLift_apply_tail (F := F) (K := K) m hm x (qtsTailIdx m hm t)
        (by simp [qtsTailIdx])).symm

theorem qts_winExt_tailLift (m : ℕ) (hm : 3 ≤ m)
    (φ : Module.End F (Fin 3 → K)) (x : Fin 3 → K) :
    CFSG.StandardType.QTwo.winExt (F := F) (K := K) m hm φ
        (qtsTailLift (F := F) (K := K) m hm x) =
      qtsTailLift (F := F) (K := K) m hm (φ x) := by
  ext i
  by_cases hi : i.val < m - 2
  · rw [CFSG.StandardType.QTwo.winExt_apply_of_lt (F := F) (K := K) m hm φ _ i hi,
      qtsTailLift_apply_prefix _ _ _ _ hi,
      qtsTailLift_apply_prefix _ _ _ _ hi]
  · let t : Fin 3 := ⟨i.val - (m - 2), by omega⟩
    have hit : (⟨m - 2 + t.val, by omega⟩ : Fin (m + 1)) = i := by
      apply Fin.ext
      simp [t]
      omega
    rw [← hit, CFSG.StandardType.QTwo.winExt_apply_window]
    have hinner : (fun s : Fin 3 =>
        qtsTailLift (F := F) (K := K) m hm x ⟨m - 2 + s.val, by omega⟩) = x := by
      funext s
      simpa [qtsTailIdx] using (qtsTailLift_apply_tail (F := F) (K := K) m hm x s)
    rw [hinner]
    simpa [qtsTailIdx] using
      (qtsTailLift_apply_tail (F := F) (K := K) m hm (φ x) t).symm

theorem qts_winExt_eq (m : ℕ) (hm : 3 ≤ m)
    (X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hfix : qtsFixesPrefix (F := F) (K := K) m X)
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) :
    X.toLinearMap =
      CFSG.StandardType.QTwo.winExt (F := F) (K := K) m hm
        (qtsTailEquiv (E := E) m hm X hfix hX).toLinearMap := by
  apply LinearMap.ext
  intro v
  let p := qtsPrefixCoords (F := F) (K := K) m hm v
  let t := qtsTailCoords (F := F) (K := K) m hm v
  have hdec := qts_eq_prefix_add_tail (F := F) (K := K) m hm v
  calc
    X v = X (qtsPrefixLift (F := F) (K := K) m hm p +
        qtsTailLift (F := F) (K := K) m hm t) := by rw [hdec]
    _ = X (qtsPrefixLift (F := F) (K := K) m hm p) +
        X (qtsTailLift (F := F) (K := K) m hm t) := map_add _ _ _
    _ = qtsPrefixLift (F := F) (K := K) m hm p +
        qtsTailLift (F := F) (K := K) m hm
          (qtsTailEquiv (E := E) m hm X hfix hX t) := by
      rw [qtsX_fixes_prefix (F := F) (K := K) m hm X hfix p,
        qtsX_tailLift_apply (E := E) m hm X hfix hX]
      rfl
    _ = CFSG.StandardType.QTwo.winExt (F := F) (K := K) m hm
          (qtsTailEquiv (E := E) m hm X hfix hX).toLinearMap
          (qtsPrefixLift (F := F) (K := K) m hm p +
            qtsTailLift (F := F) (K := K) m hm t) := by
      rw [map_add, qts_winExt_prefixLift, qts_winExt_tailLift]
      rfl
    _ = CFSG.StandardType.QTwo.winExt (F := F) (K := K) m hm
          (qtsTailEquiv (E := E) m hm X hfix hX).toLinearMap v := by
      rw [hdec]

theorem qts_forkHom_block_one (m : ℕ) (hm : 3 ≤ m)
    (θ : Su K 2 1 4 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))
    (hθ : ∀ (g : Su K 2 1 4) (v : Fin (m + 1) → K),
      θ g v = winExt (F := F) (K := K) m hm (kleinPsiHom E g) v)
    (h : Su K 2 1 3) :
    θ (blockEmb K 2 1 4 3 1 (by norm_num) h) =
      qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) h := by
  apply LinearEquiv.ext
  intro v
  rw [hθ, kleinPsiHom_blockEmb_one_eq E h, winExt_suEndN m hm h]
  rfl

theorem qts_forkHom_block_zero (m : ℕ) (hm : 3 ≤ m)
    (θ : Su K 2 1 4 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))
    (hθ : ∀ (g : Su K 2 1 4) (v : Fin (m + 1) → K),
      θ g v = winExt (F := F) (K := K) m hm (kleinPsiHom E g) v)
    (h : Su K 2 1 3) :
    θ (blockEmb K 2 1 4 3 0 (by norm_num) h) =
      stdConj E m (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)
        (revSU3 K 2 1 h)) := by
  apply LinearEquiv.ext
  intro v
  rw [hθ, kleinPsiHom_blockEmb_zero_eq E h]
  rw [map_mul, map_mul, winExt_tauAt m hm E, winExt_suEndN m hm (revSU3 K 2 1 h)]
  have hτ : (stdTau E m)⁻¹ = stdTau E m := by
    rw [stdTau]
    exact inv_eq_of_mul_eq_one_right (tauAt_mul_self E (Fin.last m))
  unfold stdConj
  rw [MulAut.conj_apply, hτ]
  rw [← LinearEquiv.coe_toLinearMap (e := stdTau E m * qtwoStdWin (F := F) (K := K) m
    (m - 2) 3 (by omega) (revSU3 K 2 1 h) * stdTau E m)]
  rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]

theorem qts_forkHom_range_le (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (θ : Su K 2 1 4 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))
    (h1 : ∀ h : Su K 2 1 3,
      θ (blockEmb K 2 1 4 3 1 (by norm_num) h) =
        qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) h)
    (h0 : ∀ h : Su K 2 1 3,
      θ (blockEmb K 2 1 4 3 0 (by norm_num) h) =
        stdConj E m (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)
          (revSU3 K 2 1 h))) :
    θ.range ≤ qtwoStdW E m hm (⟨m - 1, by omega⟩ : Fin (m + 1))
        (⟨m - 2, by omega⟩ : Fin (m + 1)) ⊔
      qtwoStdW E m hm (⟨m - 2, by omega⟩ : Fin (m + 1)) (Fin.last m) := by
  let i : Fin (m + 1) := ⟨m - 1, by omega⟩
  let j : Fin (m + 1) := ⟨m - 2, by omega⟩
  let k : Fin (m + 1) := Fin.last m
  have hgen := blockEmb_three_sup_eq_top (K := K) hK
  rw [MonoidHom.range_eq_map θ, ← hgen, Subgroup.map_sup,
    ← MonoidHom.range_comp θ (blockEmb K 2 1 4 3 0 (by norm_num)),
    ← MonoidHom.range_comp θ (blockEmb K 2 1 4 3 1 (by norm_num))]
  apply sup_le
  · have hcomp0 : θ.comp (blockEmb K 2 1 4 3 0 (by norm_num)) =
        (stdConj E m).toMonoidHom.comp
          ((qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)).comp
            (revSU3 K 2 1).toMonoidHom) := by
      apply MonoidHom.ext
      intro h
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using h0 h
    rw [hcomp0, MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (revSU3 K 2 1).surjective, Subgroup.map_top]
    rw [← qtwoStdW_fork E m hm j k (by simp [j, k]) (by simp [k])]
    exact le_sup_of_le_right le_rfl
  · have hcomp1 : θ.comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
        qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) := by
      apply MonoidHom.ext
      intro h
      exact h1 h
    rw [hcomp1]
    rw [qtwoStdW_symm E m hm i j, ← qtwoStdW_chain E m hm (m - 2) (by omega) j i
      (by simp [j]) (by simp [i]; omega)]
    exact le_sup_of_le_left le_rfl

theorem qTwo_supported_three_mem_levi_fork (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hfix : ∀ (i : Fin (m + 1)), i.val < m - 2 → ∀ a : K,
      (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single i a) = Pi.single i a) :
    x ∈ (qTwoStdFamily E hK m hm).levi
      {⟨m - 2, by omega⟩, ⟨m - 1, by omega⟩, Fin.last m} := by
  classical
  let X : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K) := x
  have hfixX : qtsFixesPrefix (F := F) (K := K) m X := hfix
  have hXorth : X ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)) :=
    Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) x.2
  let r := qtsTailEquiv (E := E) m hm X hfixX hXorth
  have hrul : r ∈ rulingGroup E 3 := by
    dsimp [r]
    exact qtsTailEquiv_mem_rulingGroup (E := E) m hm X hfixX x.2
  obtain ⟨u, hu⟩ := exists_kleinPsiHom_eq_of_mem_rulingGroup (E := E) hrul
  obtain ⟨θ, hθ⟩ := exists_linearEquivHom_of_end (F := F)
    (V := Fin (m + 1) → K) ((winExt (F := F) (K := K) m hm).comp (kleinPsiHom E))
  have h1 : ∀ h : Su K 2 1 3,
      θ (blockEmb K 2 1 4 3 1 (by norm_num) h) =
        qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) h :=
    qts_forkHom_block_one (E := E) m hm θ hθ
  have h0 : ∀ h : Su K 2 1 3,
      θ (blockEmb K 2 1 4 3 0 (by norm_num) h) =
        stdConj E m (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)
          (revSU3 K 2 1 h)) :=
    qts_forkHom_block_zero (E := E) m hm θ hθ
  have hθu : (θ u).toLinearMap =
      winExt (F := F) (K := K) m hm r.toLinearMap := by
    apply LinearMap.ext
    intro v
    change (θ u) v = winExt (F := F) (K := K) m hm r.toLinearMap v
    rw [hθ, MonoidHom.comp_apply, hu]
  have hxθ : X = θ u := by
    apply LinearEquiv.ext
    intro v
    calc
      X v = X.toLinearMap v := rfl
      _ = winExt (F := F) (K := K) m hm r.toLinearMap v := by
        have hw := LinearMap.congr_fun (qts_winExt_eq (E := E) m hm X hfixX hXorth) v
        simpa [r] using hw
      _ = θ u v := by
        rw [← hθu]
        rfl
  let i : Fin (m + 1) := ⟨m - 1, by omega⟩
  let j : Fin (m + 1) := ⟨m - 2, by omega⟩
  let k : Fin (m + 1) := Fin.last m
  have hxrange : X ∈ θ.range := MonoidHom.mem_range.mpr ⟨u, hxθ.symm⟩
  have hxW : X ∈ qtwoStdW E m hm i j ⊔ qtwoStdW E m hm j k :=
    qts_forkHom_range_le (E := E) hK m hm θ h1 h0 hxrange
  let C : Set (Fin (m + 1)) := {j, i, k}
  let S := qTwoStdFamily E hK m hm
  have hiC : i ∈ C := by simp [C]
  have hjC : j ∈ C := by simp [C]
  have hkC : k ∈ C := by simp [C]
  have h3ij : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3 := by
    rw [qtwoLabel_three_iff hm]
    right
    left
    exact ⟨by simp [i, j]; omega, by simp [i, j]⟩
  have h3jk : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j k = 3 := by
    rw [qtwoLabel_three_iff hm]
    right
    right
    left
    exact ⟨by simp [j, k]; omega, by simp [k]⟩
  have hWij_le : qtwoStdW E m hm i j ≤ (S.levi C).map
      (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
    rw [← map_range_qTwoStdTheta_of_three E m hm h3ij]
    exact Subgroup.map_mono (S.le_levi_edge hiC hjC h3ij)
  have hWjk_le : qtwoStdW E m hm j k ≤ (S.levi C).map
      (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
    rw [← map_range_qTwoStdTheta_of_three E m hm h3jk]
    exact Subgroup.map_mono (S.le_levi_edge hjC hkC h3jk)
  have hxmap : X ∈ (S.levi C).map
      (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :=
    (sup_le hWij_le hWjk_le) hxW
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
  have hyX : y = x := Subtype.ext (by simpa [X] using hyx)
  have hxC : x ∈ S.levi C := by simpa [hyX] using hy
  have hCeq : ({⟨m - 2, by omega⟩, ⟨m - 1, by omega⟩, Fin.last m} : Set (Fin (m + 1))) = C := by
    ext z
    simp [C, i, j, k]
  simpa [hCeq] using hxC
