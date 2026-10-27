module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.Stage2.Final.ModelLayer

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

theorem diagGL_comm_yGL (a b : GL (Fin 2) F) : diagGL a b * yGL F = yGL F * diagGL a b := by
  rw [yGL, diagGL_mul, diagGL_mul]
  simp

theorem mkP_diag_mem_C0 (M : ModelData F) {a b : GL (Fin 2) F} (h : diagGL a b ∈ M.K4) :
    mkP M ⟨diagGL a b, h⟩ ∈ C0 M :=
  ⟨_, mem_Dsub.2 (Subtype.ext (diagGL_comm_yGL a b)), rfl⟩

theorem diag_inv_mem_K4 (M : ModelData F) {a : GL (Fin 2) F} (ha : a ∈ M.U2) :
    diagGL a a⁻¹ ∈ M.K4 :=
  M.diagGL_mem_K4_iff.2 ⟨ha, M.U2.inv_mem ha, by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]⟩

@[expose] def tP (M : ModelData F) : PG M := mkP M M.wK

@[expose] def dP (M : ModelData F) (a : GL (Fin 2) F) (ha : a ∈ M.U2) : PG M :=
  mkP M ⟨diagGL a a⁻¹, diag_inv_mem_K4 M ha⟩

theorem tP_sq (M : ModelData F) : tP M * tP M = 1 := by
  rw [tP, ← map_mul, wK_mul_self, map_one]

theorem tP_mem_Cg (M : ModelData F) : tP M ∈ Cg M := by
  show tP M ∈ Subgroup.centralizer {yP M}
  rw [centralizer_yP]
  exact ⟨M.wK, wK_mem_Nsub M, rfl⟩

theorem dP_mem_C0 (M : ModelData F) {a : GL (Fin 2) F} (ha : a ∈ M.U2) : dP M a ha ∈ C0 M :=
  mkP_diag_mem_C0 M _

theorem dP_mem_Cg (M : ModelData F) {a : GL (Fin 2) F} (ha : a ∈ M.U2) : dP M a ha ∈ Cg M :=
  C0_le_Cg M (dP_mem_C0 M ha)

theorem tP_not_mem_C0 (M : ModelData F) (h2 : (2 : F) ≠ 0) : tP M ∉ C0 M := by
  rintro ⟨g, hg, hgw⟩
  have h1 : mkP M (M.wK⁻¹ * g) = 1 := by
    rw [map_mul, map_inv]
    have : mkP M g = mkP M M.wK := hgw
    rw [this, inv_mul_cancel]
  have h4 : M.wK⁻¹ * g ∈ Dsub M := ker_mkP_le_D M (MonoidHom.mem_ker.2 h1)
  have h5 : M.wK ∈ Dsub M := by
    have e : M.wK = g * (M.wK⁻¹ * g)⁻¹ := by group
    rw [e]
    exact (Dsub M).mul_mem hg ((Dsub M).inv_mem h4)
  exact wK_not_mem_Dsub M h2 h5

theorem E_le_C0 (M : ModelData F) : K1 M ⊔ K2 M ≤ C0 M := sup_le (K1_le_C0 M) (K2_le_C0 M)

theorem E_le_Cg (M : ModelData F) : K1 M ⊔ K2 M ≤ Cg M := (E_le_C0 M).trans (C0_le_Cg M)

theorem tP_ne_one (M : ModelData F) (h2 : (2 : F) ≠ 0) : tP M ≠ 1 := fun h =>
  tP_not_mem_C0 M h2 (h ▸ (C0 M).one_mem)

theorem orderOf_tP (M : ModelData F) (h2 : (2 : F) ≠ 0) : orderOf (tP M) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact tP_sq M) (tP_ne_one M h2)

theorem tP_not_mem_E (M : ModelData F) (h2 : (2 : F) ≠ 0) : tP M ∉ K1 M ⊔ K2 M :=
  fun h => tP_not_mem_C0 M h2 (E_le_C0 M h)

theorem tP_mul_not_mem_E (M : ModelData F) (h2 : (2 : F) ≠ 0) {x : PG M} (hx : x ∈ C0 M) :
    tP M * x ∉ K1 M ⊔ K2 M := fun h => tP_not_mem_C0 M h2 (by
  have := (C0 M).mul_mem (E_le_C0 M h) ((C0 M).inv_mem hx)
  simpa using this)

theorem tP_conj_iota1 (M : ModelData F) (a : ↥M.H2) :
    tP M * iota1 M a * (tP M)⁻¹ = iota2 M a := by
  have key : (M.wK * (⟨blkL F a, M.blkL_mem_K4 a.2⟩ : ↥M.K4) * M.wK⁻¹ : ↥M.K4) =
      (⟨blkR F a, M.blkR_mem_K4 a.2⟩ : ↥M.K4) := by
    apply Subtype.ext
    show swapGL F * blkL F (a : GL (Fin 2) F) * (swapGL F)⁻¹ = blkR F (a : GL (Fin 2) F)
    rw [blkL_apply, blkR_apply]
    exact swapGL_mul_diagGL_mul_inv (a : GL (Fin 2) F) 1
  calc tP M * iota1 M a * (tP M)⁻¹
      = mkP M (M.wK * (⟨blkL F a, M.blkL_mem_K4 a.2⟩ : ↥M.K4) * M.wK⁻¹) := by
        simp only [tP, iota1_apply, map_mul, map_inv]
    _ = mkP M ⟨blkR F a, M.blkR_mem_K4 a.2⟩ := by rw [key]
    _ = iota2 M a := (iota2_apply M a).symm

theorem tP_conj_iota2 (M : ModelData F) (a : ↥M.H2) :
    tP M * iota2 M a * (tP M)⁻¹ = iota1 M a := by
  have h := tP_conj_iota1 M a
  have h2 : tP M * (tP M * iota1 M a * (tP M)⁻¹) * (tP M)⁻¹ = iota1 M a := by
    have hs : tP M * tP M = 1 := tP_sq M
    have hi : (tP M)⁻¹ = tP M := inv_eq_of_mul_eq_one_right hs
    rw [hi]
    calc tP M * (tP M * iota1 M a * tP M) * tP M = (tP M * tP M) * iota1 M a * (tP M * tP M) := by
          group
      _ = iota1 M a := by rw [hs]; group
  rw [h] at h2
  exact h2

theorem tP_swap (M : ModelData F) :
    (K1 M).map (MulAut.conj (tP M)).toMonoidHom = K2 M := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (tP_conj_iota1 M a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨iota1 M a, ⟨a, rfl⟩, tP_conj_iota1 M a⟩

theorem normalizer_K1_of_C0 (M : ModelData F) (h2 : (2 : F) ≠ 0) {x : PG M} (hx : x ∈ C0 M) :
    x ∈ Subgroup.normalizer (K1 M : Set (PG M)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh; exact C0_conj_K1 M h2 hx hh
  · intro hh
    have := C0_conj_K1 M h2 ((C0 M).inv_mem hx) hh
    simpa [mul_assoc] using this

theorem mem_zpowers_of_sq_one {G : Type*} [Group G] {c y : G} (hc : c * c = 1)
    (hy : y ∈ Subgroup.zpowers c) : y = 1 ∨ y = c := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hc
  rw [zpow_eq_zpow_emod n h2]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
