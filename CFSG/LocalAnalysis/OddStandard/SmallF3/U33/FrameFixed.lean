module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.FrameFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.K28Sigma4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.FrameDef

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.GH74.KGroups.U33
  CFSG.OddStandard.SmallF3.HarrisU33.K28

section KLevel

variable
  {K : Type} [Group K]

private noncomputable def stdAut (m : Model28 K) : MulAut K :=
  m.Φ.symm ⟨ftau, ftau_mem_A⟩

private theorem stdAut_ι (m : Model28 K) : m.ι (stdAut m) = ftau := by
  simp [stdAut, Model28.ι]

private theorem stdAut_sq (m : Model28 K) : stdAut m * stdAut m = 1 := by
  apply m.ι_injective
  rw [map_mul, map_one, stdAut_ι]
  simpa [pow_two] using ftau_pow.1

private theorem stdAut_outer (m : Model28 K) : ∀ k : K, stdAut m ≠ MulAut.conj k := by
  intro k hk
  apply ftau_not_mem_P
  rw [← stdAut_ι m, hk, Model28.ι_conj]
  exact m.ε_mem k

private theorem mem_centralizer_stdAut_iff (m : Model28 K) (k : K) :
    m.ε k ∈ Subgroup.centralizer ({ftau} : Set Pm) ↔ (stdAut m) k = k := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hcomm
    apply m.ε_injective
    rw [m.ε_apply, stdAut_ι, ← hcomm]
    group
  · intro hfix
    have hε : ftau * m.ε k * ftau⁻¹ = m.ε k := by
      rw [← stdAut_ι m, ← m.ε_apply (stdAut m) k, hfix]
    have hcomm : ftau * m.ε k = m.ε k * ftau := by
      calc ftau * m.ε k = (ftau * m.ε k * ftau⁻¹) * ftau := by group
        _ = m.ε k * ftau := by rw [hε]
    exact hcomm.symm

private noncomputable def stdAutHom (m : Model28 K) :
    ↥(autFixed (stdAut m)) →*
      ↥(QP.originalSubgroup ⊓ Subgroup.centralizer ({ftau} : Set Pm)) where
  toFun k := ⟨m.ε k, Subgroup.mem_inf.mpr
    ⟨m.ε_mem k, (mem_centralizer_stdAut_iff m k).mpr k.2⟩⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

private theorem stdAutHom_bijective (m : Model28 K) : Function.Bijective (stdAutHom m) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply m.ε_injective
    simpa [stdAutHom] using congrArg Subtype.val hab
  · intro z
    have hzP : (z : Pm) ∈ QP.originalSubgroup := (Subgroup.mem_inf.mp z.2).1
    have hzc : (z : Pm) ∈ Subgroup.centralizer ({ftau} : Set Pm) :=
      (Subgroup.mem_inf.mp z.2).2
    obtain ⟨k, hk⟩ := m.exists_ε hzP
    refine ⟨⟨k, ?_⟩, ?_⟩
    · exact (mem_centralizer_stdAut_iff m k).mp (by rw [hk]; exact hzc)
    · apply Subtype.ext
      simpa [stdAutHom] using hk

private noncomputable def stdAutEquiv (m : Model28 K) :
    ↥(autFixed (stdAut m)) ≃*
      ↥(QP.originalSubgroup ⊓ Subgroup.centralizer ({ftau} : Set Pm)) :=
  MulEquiv.ofBijective (stdAutHom m) (stdAutHom_bijective m)

private theorem conj_stdAut_fixed_iff (m : Model28 K) {α : MulAut K} {k : K}
    (hk : α = MulAut.conj k * stdAut m * (MulAut.conj k)⁻¹) (x : K) :
    α x = x ↔ (stdAut m) ((MulAut.conj k)⁻¹ x) = (MulAut.conj k)⁻¹ x := by
  rw [hk]
  constructor
  · intro h
    have h' := congrArg (fun z => ((MulAut.conj k)⁻¹) z) h
    simpa only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] using h'
  · intro h
    have h' : MulAut.conj k ((stdAut m) ((MulAut.conj k)⁻¹ x)) = x := by
      rw [h]
      simp only [MulAut.inv_apply, MulEquiv.apply_symm_apply]
    simpa only [MulAut.mul_apply, MulAut.inv_apply] using h'

private noncomputable def conjStdAutHom (m : Model28 K) {α : MulAut K} {k : K}
    (hk : α = MulAut.conj k * stdAut m * (MulAut.conj k)⁻¹) :
    ↥(autFixed α) →* ↥(autFixed (stdAut m)) where
  toFun x := ⟨(MulAut.conj k)⁻¹ x, (conj_stdAut_fixed_iff m hk x).mp x.2⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp
    group

private theorem conjStdAutHom_bijective (m : Model28 K) {α : MulAut K} {k : K}
    (hk : α = MulAut.conj k * stdAut m * (MulAut.conj k)⁻¹) :
    Function.Bijective (conjStdAutHom m hk) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    have h : (MulAut.conj k).symm (a : K) = (MulAut.conj k).symm (b : K) :=
      congrArg Subtype.val hab
    exact (MulAut.conj k).symm.injective h
  · intro y
    refine ⟨⟨MulAut.conj k y, ?_⟩, ?_⟩
    · refine (conj_stdAut_fixed_iff m hk (MulAut.conj k y)).mpr ?_
      have hcy : ((MulAut.conj k)⁻¹) ((MulAut.conj k) (y : K)) = (y : K) := by
        simp only [MulAut.inv_apply, MulEquiv.symm_apply_apply]
      rw [hcy]
      exact y.2
    · apply Subtype.ext
      show (MulAut.conj k)⁻¹ (MulAut.conj k (y : K)) = (y : K)
      simp only [MulAut.inv_apply, MulEquiv.symm_apply_apply]

private noncomputable def conjStdAutEquiv (m : Model28 K) {α : MulAut K} {k : K}
    (hk : α = MulAut.conj k * stdAut m * (MulAut.conj k)⁻¹) :
    ↥(autFixed α) ≃* ↥(autFixed (stdAut m)) :=
  MulEquiv.ofBijective (conjStdAutHom m hk) (conjStdAutHom_bijective m hk)

theorem autFixed_card_of_psu33 (h : LieModel K .PSU 3 3 1) {α : MulAut K} (hα : α * α = 1)
    (hα' : ∀ k : K, α ≠ MulAut.conj k) : Nat.card (autFixed α) = 24 := by
  obtain ⟨m⟩ := exists_model28 h
  obtain ⟨k, hk⟩ := outer_invol_conj_of_psu33 h (stdAut_sq m) (stdAut_outer m) hα hα'
  calc Nat.card (autFixed α)
      = Nat.card (autFixed (stdAut m)) := Nat.card_congr (conjStdAutEquiv m hk).toEquiv
    _ = Nat.card ↥(QP.originalSubgroup ⊓ Subgroup.centralizer ({ftau} : Set Pm)) :=
        Nat.card_congr (stdAutEquiv m).toEquiv
    _ = 24 := card_cent_ftau

theorem autFixed_perm_four_of_psu33 (h : LieModel K .PSU 3 3 1) {α : MulAut K}
    (hα : α * α = 1) (hα' : ∀ k : K, α ≠ MulAut.conj k) :
    Nonempty (↥(autFixed α) ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨m⟩ := exists_model28 h
  obtain ⟨k, hk⟩ := outer_invol_conj_of_psu33 h (stdAut_sq m) (stdAut_outer m) hα hα'
  obtain ⟨e⟩ := cent_ftau_perm_four
  exact ⟨(conjStdAutEquiv m hk).trans ((stdAutEquiv m).trans e)⟩

end KLevel

end CFSG.OddStandard.SmallF3.HarrisU33
