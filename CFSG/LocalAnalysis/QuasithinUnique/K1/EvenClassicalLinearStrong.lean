module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearBasic
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong

public section

namespace CFSG.QuasithinUnique.K1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] {n : ℕ}

theorem exists_eq_one_add_single_of_commute (hn : 3 ≤ n) {u : SpecialLinearGroup (Fin n) K}
    (hu : u ∈ unitriangular n K) (hc : ∀ v ∈ unitriangular n K, u * v = v * u) :
    ∃ b : K, (u : Matrix (Fin n) (Fin n) K) =
      1 + single (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) b := by
  obtain ⟨a, b, hab⟩ := eq_smul_one_add_single_of_commute (n := n) (by omega)
    (u : Matrix (Fin n) (Fin n) K) (by
      intro i j hij
      have hlt : i < j := by
        rw [Fin.lt_def]
        omega
      have h := congrArg (fun g : SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
        (hc _ (transvection_mem_unitriangular hlt (1 : K)))
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
        mul_add, add_mul, mul_one, one_mul] at h
      exact add_left_cancel h)
  have h00 : a = 1 := by
    have h := hu.2 ⟨0, by omega⟩
    have h' := congrFun₂ hab ⟨0, by omega⟩ ⟨0, by omega⟩
    have e : single (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) (1 : K)
        ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 :=
      single_apply_of_ne _ _ _ _ _ (fun h => fin_mk_ne _ _ (by omega) h.2)
    rw [h, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, one_apply_eq, e] at h'
    simpa using h'.symm
  refine ⟨b, ?_⟩
  rw [hab, h00, one_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem transvection_mul_ne_of_ne_zero (hn : 3 ≤ n) {b : K} (hb : b ≠ 0) :
    Matrix.SpecialLinearGroup.transvection (i := (⟨0, by omega⟩ : Fin n)) (j := ⟨1, by omega⟩)
        (fin_mk_ne _ _ (by omega)) b *
      Matrix.SpecialLinearGroup.transvection (i := (⟨1, by omega⟩ : Fin n)) (j := ⟨2, by omega⟩)
        (fin_mk_ne _ _ (by omega)) b ≠
    Matrix.SpecialLinearGroup.transvection (i := (⟨1, by omega⟩ : Fin n)) (j := ⟨2, by omega⟩)
        (fin_mk_ne _ _ (by omega)) b *
      Matrix.SpecialLinearGroup.transvection (i := (⟨0, by omega⟩ : Fin n)) (j := ⟨1, by omega⟩)
        (fin_mk_ne _ _ (by omega)) b := by
  intro h
  have h' := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    mul_add, add_mul, mul_one, one_mul, single_mul_single_same] at h'
  have h2 : single (⟨1, by omega⟩ : Fin n) (⟨2, by omega⟩ : Fin n) b *
      single (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) b = 0 :=
    single_mul_single_of_ne _ _ _ _ (fin_mk_ne _ _ (by omega)) _
  rw [h2] at h'
  have h3 := congrFun₂ h' ⟨0, by omega⟩ ⟨2, by omega⟩
  have e1 : (1 : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨2, by omega⟩ = 0 :=
    one_apply_ne (fin_mk_ne _ _ (by omega))
  have e2 : single (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) b
      ⟨0, by omega⟩ ⟨2, by omega⟩ = 0 :=
    single_apply_of_ne _ _ _ _ _ (fun h => fin_mk_ne _ _ (by omega) h.2)
  have e3 : single (⟨1, by omega⟩ : Fin n) (⟨2, by omega⟩ : Fin n) b
      ⟨0, by omega⟩ ⟨2, by omega⟩ = 0 :=
    single_apply_of_ne _ _ _ _ _ (fun h => fin_mk_ne _ _ (by omega) h.1)
  have e4 : single (⟨0, by omega⟩ : Fin n) (⟨2, by omega⟩ : Fin n) (b * b)
      ⟨0, by omega⟩ ⟨2, by omega⟩ = b * b :=
    single_apply_same _ _ _
  simp only [Matrix.add_apply, e1, e2, e3, e4, add_zero, zero_add] at h3
  exact hb (mul_self_eq_zero.mp h3)

theorem noStronglyClosed_projectiveSL [Finite K] [CharP K 2] (hn : 3 ≤ n) :
    NoStronglyClosedElemAbelian (projectiveSL n K) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := K) 2 hn1
  have hQ₀ : IsSylowTwoOf (projUnitriangular n K) ⊤ := by
    rw [← hS]
    exact isSylowTwoOf_top_iff.mpr ⟨S.isPGroup', S.not_dvd_index⟩
  refine noStronglyClosedElemAbelian_of_sylow _ hQ₀ fun A hW => ?_
  by_contra hne
  have hAn : ∀ a ∈ A, ∀ q ∈ projUnitriangular n K, q⁻¹ * a * q ∈ A := by
    intro a ha q hq
    refine hW.closed a ha q ?_
    exact (projUnitriangular n K).mul_mem ((projUnitriangular n K).mul_mem
      ((projUnitriangular n K).inv_mem hq) (hW.le ha)) hq
  obtain ⟨a, haA, ha1, hac⟩ := exists_ne_one_mem_centralizer hW.sylow.2.1 hW.le hAn hne
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp (hW.le haA)
  have hc : ∀ v ∈ unitriangular n K, u * v = v * u := by
    intro v hv
    have h := hac (proj n K v) (Subgroup.mem_map_of_mem _ hv)
    rw [← map_mul, ← map_mul] at h
    exact (proj_injOn_unitriangular n ((unitriangular n K).mul_mem hv hu)
      ((unitriangular n K).mul_mem hu hv) h).symm
  obtain ⟨b, hb⟩ := exists_eq_one_add_single_of_commute hn hu hc
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply ha1
    have : u = 1 := Subtype.ext (by simpa using hb)
    rw [this, map_one]
  have hil : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := fin_mk_ne _ _ (by omega)
  have hu' : u = Matrix.SpecialLinearGroup.transvection hil b := Subtype.ext (by
    rw [hb, Matrix.SpecialLinearGroup.transvection_coe])
  have key : ∀ (w : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i < j),
      w ⟨0, by omega⟩ = i → w ⟨n - 1, by omega⟩ = j →
      proj n K (Matrix.SpecialLinearGroup.transvection hij.ne b) ∈ A := by
    intro w i j hij hwi hwj
    have hconj := signedPermutation_conj_transvection (K := K) w hil b
    rw [transvection_congr (w.injective.ne hil) hij.ne hwi hwj] at hconj
    have hmem : proj n K (Matrix.SpecialLinearGroup.transvection hij.ne b) ∈
        projUnitriangular n K :=
      Subgroup.mem_map_of_mem _ (transvection_mem_unitriangular hij b)
    have hrewrite : ((proj n K (signedPermutation n K w))⁻¹)⁻¹ * proj n K u *
        (proj n K (signedPermutation n K w))⁻¹ =
        proj n K (Matrix.SpecialLinearGroup.transvection hij.ne b) := by
      rw [inv_inv, ← map_inv, ← map_mul, ← map_mul, hu', hconj]
    have h := hW.closed (proj n K u) haA (proj n K (signedPermutation n K w))⁻¹ (by
      rw [hrewrite]
      exact hmem)
    rwa [hrewrite] at h
  have h01 : (⟨0, by omega⟩ : Fin n) < ⟨1, by omega⟩ := by simp [Fin.lt_def]
  have h12 : (⟨1, by omega⟩ : Fin n) < ⟨2, by omega⟩ := by simp [Fin.lt_def]
  have hw1a : Equiv.swap (⟨1, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ ⟨0, by omega⟩ =
      ⟨0, by omega⟩ :=
    Equiv.swap_apply_of_ne_of_ne (fin_mk_ne _ _ (by omega)) (fin_mk_ne _ _ (by omega))
  have hw1b : Equiv.swap (⟨1, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ =
      ⟨1, by omega⟩ := Equiv.swap_apply_right _ _
  have hi2 : Equiv.swap (⟨2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ ⟨0, by omega⟩ =
      ⟨0, by omega⟩ :=
    Equiv.swap_apply_of_ne_of_ne (fin_mk_ne _ _ (by omega)) (fin_mk_ne _ _ (by omega))
  have hi3 : Equiv.swap (⟨2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ =
      ⟨2, by omega⟩ := Equiv.swap_apply_right _ _
  have hi4 : Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ⟨2, by omega⟩ = ⟨2, by omega⟩ :=
    Equiv.swap_apply_of_ne_of_ne (fin_mk_ne _ _ (by omega)) (fin_mk_ne _ _ (by omega))
  have hw2a : (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ *
      Equiv.swap (⟨2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
    rw [Equiv.Perm.mul_apply, hi2, Equiv.swap_apply_left]
  have hw2b : (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ *
      Equiv.swap (⟨2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) ⟨n - 1, by omega⟩ =
      ⟨2, by omega⟩ := by
    rw [Equiv.Perm.mul_apply, hi3, hi4]
  have hA01 := key _ _ _ h01 hw1a hw1b
  have hA12 := key _ _ _ h12 hw2a hw2b
  have hcomm := hW.elem.1.is_comm.comm ⟨_, hA01⟩ ⟨_, hA12⟩
  have hcomm' := congrArg Subtype.val hcomm
  simp only [Subgroup.coe_mul] at hcomm'
  rw [← map_mul, ← map_mul] at hcomm'
  exact transvection_mul_ne_of_ne_zero hn hb0
    (proj_injOn_unitriangular n
      ((unitriangular n K).mul_mem (transvection_mem_unitriangular h01 b)
        (transvection_mem_unitriangular h12 b))
      ((unitriangular n K).mul_mem (transvection_mem_unitriangular h12 b)
        (transvection_mem_unitriangular h01 b)) hcomm')

end CFSG.QuasithinUnique.K1
