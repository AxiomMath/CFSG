module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.OrthExt

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def hypPerpCoords (P : HypPair Q) : V →ₗ[K] K × K :=
  ((polarBilin Q).flip P.e).prod ((polarBilin Q).flip P.f)

theorem hypPerpCoords_surjective (P : HypPair Q) : Function.Surjective (hypPerpCoords P) := by
  rintro ⟨a, b⟩
  refine ⟨b • P.e + a • P.f, ?_⟩
  simp [hypPerpCoords, P.polar_ee, P.polar_fe, P.polar_ef, P.polar_ff]

theorem ker_hypPerpCoords (P : HypPair Q) : LinearMap.ker (hypPerpCoords P) = hypPerp P := by
  ext v
  simp [hypPerpCoords, mem_hypPerp]

theorem finrank_hypPerp [FiniteDimensional K V] (P : HypPair Q) :
    Module.finrank K (hypPerp P) = Module.finrank K V - 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (hypPerpCoords P)
  rw [LinearMap.range_eq_top.2 (hypPerpCoords_surjective P), finrank_top, ker_hypPerpCoords,
    Module.finrank_prod, Module.finrank_self] at h
  omega

theorem separatingLeft_perpForm (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    (m : hypPerp P) (hm : ∀ n : hypPerp P, polar (perpForm P) m n = 0) : m = 0 := by
  have hm' : (m : V) = 0 := by
    refine eq_zero_of_polar_eq_zero hQ fun x => ?_
    have hd := perpProj_add P x
    have hd0 : polar Q (perpProj P x : V) (m : V) = 0 := by
      have h := hm (perpProj P x)
      rw [polar_perpForm] at h
      rw [polar_comm]
      exact h
    have he : polar Q P.e (m : V) = 0 := by
      rw [polar_comm]
      exact m.2.1
    have hf : polar Q P.f (m : V) = 0 := by
      rw [polar_comm]
      exact m.2.2
    rw [polar_comm, ← hd, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
      hd0, he, hf]
    ring
  exact Subtype.ext hm'

theorem nondegenerate_perpForm (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q) :
    (polarBilin (perpForm P)).Nondegenerate :=
  ⟨fun m hm => separatingLeft_perpForm hQ P m (fun n => by simpa [polarBilin_apply_apply] using hm n),
    fun m hm => separatingLeft_perpForm hQ P m (fun n => by
      rw [polar_comm]
      simpa [polarBilin_apply_apply] using hm n)⟩

theorem orth_e_mem {P P' : HypPair Q} (h : P.Orth P') : P'.e ∈ hypPerp P :=
  mem_hypPerp.2 ⟨by rw [polar_comm]; exact h.ee, by rw [polar_comm]; exact h.fe⟩

theorem orth_f_mem {P P' : HypPair Q} (h : P.Orth P') : P'.f ∈ hypPerp P :=
  mem_hypPerp.2 ⟨by rw [polar_comm]; exact h.ef, by rw [polar_comm]; exact h.ff⟩

@[expose] def hypPairPerp {P P' : HypPair Q} (h : P.Orth P') : HypPair (perpForm P) where
  e := ⟨P'.e, orth_e_mem h⟩
  f := ⟨P'.f, orth_f_mem h⟩
  Q_e := by
    rw [perpForm_apply]
    exact P'.Q_e
  Q_f := by
    rw [perpForm_apply]
    exact P'.Q_f
  polar_ef := by
    rw [polar_perpForm]
    exact P'.polar_ef

theorem hypPairPerp_orth {P P' P'' : HypPair Q} (h' : P.Orth P') (h'' : P.Orth P'')
    (h : P'.Orth P'') : (hypPairPerp h').Orth (hypPairPerp h'') where
  ee := by
    rw [polar_perpForm]
    exact h.ee
  ef := by
    rw [polar_perpForm]
    exact h.ef
  fe := by
    rw [polar_perpForm]
    exact h.fe
  ff := by
    rw [polar_perpForm]
    exact h.ff

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

end
