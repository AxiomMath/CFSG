module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCuts

public section

namespace CFSG.AGLEmbedding.LeviBlock

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r t : ℕ}

variable (K A) in
@[expose] def orthResProj (ht : t ≤ r) :
    ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin (r - t) ⊕ Fin (r - t) → K) × A) where
  toFun v := (hiPart ht v.1, v.2)
  map_add' v w := Prod.ext (funext fun c => by rcases c with i | i <;> rfl) rfl
  map_smul' c v := Prod.ext (funext fun c => by rcases c with i | i <;> rfl) rfl

variable (K A) in
@[expose] def orthResIncl (ht : t ≤ r) :
    ((Fin (r - t) ⊕ Fin (r - t) → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A) where
  toFun u := (joinHi ht 0 u.1, u.2)
  map_add' u w := Prod.ext (funext fun c => by
    rcases c with p | p <;> obtain ⟨x, rfl⟩ := (splitIdx ht).surjective p <;>
      rcases x with _ | _ <;> simp [joinHi]) rfl
  map_smul' c u := Prod.ext (funext fun c => by
    rcases c with p | p <;> obtain ⟨x, rfl⟩ := (splitIdx ht).surjective p <;>
      rcases x with _ | _ <;> simp [joinHi]) rfl

theorem orthResProj_apply (ht : t ≤ r) (v : (Fin r ⊕ Fin r → K) × A) :
    orthResProj K A ht v = (hiPart ht v.1, v.2) :=
  rfl

theorem orthResIncl_apply (ht : t ≤ r) (u : (Fin (r - t) ⊕ Fin (r - t) → K) × A) :
    orthResIncl K A ht u = (joinHi ht 0 u.1, u.2) :=
  rfl

theorem orthResProj_orthResIncl (ht : t ≤ r) (u : (Fin (r - t) ⊕ Fin (r - t) → K) × A) :
    orthResProj K A ht (orthResIncl K A ht u) = u := by
  rw [orthResIncl_apply, orthResProj_apply, hiPart_joinHi]

@[expose] def IsResPerp (ht : t ≤ r) (v : (Fin r ⊕ Fin r → K) × A) : Prop :=
  ∀ i : Fin t, v.1 (.inr (splitIdx ht (.inl i))) = 0

theorem isResPerp_orthResIncl (ht : t ≤ r) (u : (Fin (r - t) ⊕ Fin (r - t) → K) × A) :
    IsResPerp ht (orthResIncl K A ht u) :=
  fun i => joinHi_low_f ht 0 u.1 i

theorem isResPerp_of_mem_tailFlag (ht : t ≤ r) {v : (Fin r ⊕ Fin r → K) × A}
    (hv : v ∈ tailFlag K A r t) : IsResPerp ht v :=
  fun _ => (mem_flag.1 (mem_tailFlag_iff.1 hv).1).1 _

theorem orthResProj_eq_zero_of_mem (ht : t ≤ r) {v : (Fin r ⊕ Fin r → K) × A}
    (hv : v ∈ tailFlag K A r t) : orthResProj K A ht v = 0 := by
  obtain ⟨h1, h2⟩ := mem_tailFlag_iff.1 hv
  rw [orthResProj_apply, (mem_flag_iff_hiPart ht (isResPerp_of_mem_tailFlag ht hv)).1 h1, h2]
  rfl

theorem sub_orthResIncl_mem (ht : t ≤ r) {v : (Fin r ⊕ Fin r → K) × A} (hv : IsResPerp ht v) :
    v - orthResIncl K A ht (orthResProj K A ht v) ∈ tailFlag K A r t := by
  have hv' := joinHi_hiPart ht hv
  refine mem_tailFlag_iff.2 ⟨?_, by simp [orthResIncl_apply, orthResProj_apply]⟩
  have hlow : ∀ i : Fin t, (v - orthResIncl K A ht (orthResProj K A ht v)).1
      (.inr (splitIdx ht (.inl i))) = 0 := fun i => by
    simp [orthResIncl_apply, orthResProj_apply, joinHi_low_f, hv i]
  refine (mem_flag_iff_hiPart ht hlow).2 (funext fun c => ?_)
  rcases c with i | i <;>
    simp [orthResIncl_apply, orthResProj_apply, hiPart, joinHi]

theorem mem_tailFlag_of_orthResProj_eq_zero (ht : t ≤ r) {v : (Fin r ⊕ Fin r → K) × A}
    (hv : IsResPerp ht v) (h0 : orthResProj K A ht v = 0) : v ∈ tailFlag K A r t := by
  have := sub_orthResIncl_mem ht hv
  rwa [h0, map_zero, sub_zero] at this

theorem quadTail_eq_of_isResPerp {qA : QuadraticForm K A} (ht : t ≤ r)
    {v : (Fin r ⊕ Fin r → K) × A} (hv : IsResPerp ht v) :
    quadTail r qA v = quadTail (r - t) qA (orthResProj K A ht v) := by
  rw [quadTail_eq_add_highPart ht, Finset.sum_eq_zero fun i _ => by rw [hv i, mul_zero],
    zero_add]
  rfl

theorem isResPerp_map {qA : QuadraticForm K A} (ht : t ≤ r)
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA))
    (hgF : (tailFlag K A r t).map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = tailFlag K A r t)
    {v : (Fin r ⊕ Fin r → K) × A} (hv : IsResPerp ht v) : IsResPerp ht (g v) := by
  have hperp : ∀ w ∈ tailFlag K A r t, polar (quadTail r qA) v w = 0 :=
    (polar_tailFlag_eq_zero_iff ht).2 hv
  refine (polar_tailFlag_eq_zero_iff (qB := qA) ht).1 fun w hw => ?_
  have hgw : g.symm w ∈ tailFlag K A r t := by
    rw [← hgF] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    rwa [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [← g.apply_symm_apply w, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg]
  exact hperp _ hgw

@[expose] def orthResMat (ht : t ≤ r)
    (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
    Module.End K ((Fin (r - t) ⊕ Fin (r - t) → K) × A) :=
  (orthResProj K A ht).comp ((g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _).comp (orthResIncl K A ht))

theorem orthResMat_apply (ht : t ≤ r)
    (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
    (u : (Fin (r - t) ⊕ Fin (r - t) → K) × A) :
    orthResMat ht g u = orthResProj K A ht (g (orthResIncl K A ht u)) :=
  rfl

theorem orthResMat_one (ht : t ≤ r) :
    orthResMat ht (1 : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) = 1 :=
  LinearMap.ext fun u => orthResProj_orthResIncl ht u

theorem orthResMat_mul (ht : t ≤ r)
    {g h : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : ∀ v ∈ tailFlag K A r t, g v ∈ tailFlag K A r t)
    (hh : ∀ v, IsResPerp ht v → IsResPerp ht (h v)) :
    orthResMat ht (g * h) = orthResMat ht g * orthResMat ht h := by
  refine LinearMap.ext fun u => ?_
  have hv := hh _ (isResPerp_orthResIncl ht u)
  have hw := sub_orthResIncl_mem ht hv
  rw [Module.End.mul_apply, orthResMat_apply, orthResMat_apply, orthResMat_apply,
    LinearEquiv.mul_apply]
  set v := h (orthResIncl K A ht u)
  have hsplit : g v = g (v - orthResIncl K A ht (orthResProj K A ht v)) +
      g (orthResIncl K A ht (orthResProj K A ht v)) := by
    rw [← map_add, sub_add_cancel]
  rw [hsplit, map_add, orthResProj_eq_zero_of_mem ht (hg _ hw), zero_add]

theorem map_orthResMat {qA : QuadraticForm K A} (ht : t ≤ r)
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA))
    (hh : ∀ v, IsResPerp ht v → IsResPerp ht (g v)) (u : (Fin (r - t) ⊕ Fin (r - t) → K) × A) :
    quadTail (r - t) qA (orthResMat ht g u) = quadTail (r - t) qA u := by
  rw [orthResMat_apply, ← quadTail_eq_of_isResPerp ht (hh _ (isResPerp_orthResIncl ht u)),
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg,
    quadTail_eq_of_isResPerp ht (isResPerp_orthResIncl ht u), orthResProj_orthResIncl]

variable {qA : QuadraticForm K A} {s : ℕ} {d : Fin (s + 1) → ℕ}

theorem mem_orthogonalGroup_of_mem_orthParab {x : ↥(orthElementaryGroup (quadTail r qA))} :
    (x : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) :=
  orthElementaryGroup_le _ x.2

theorem isResPerp_of_mem_orthParab (hd : OrthCuts r d) {x : ↥(orthElementaryGroup (quadTail r qA))}
    (hx : x ∈ orthParab r qA d) {v : (Fin r ⊕ Fin r → K) × A} (hv : IsResPerp hd.last v) :
    IsResPerp hd.last ((x : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) v) :=
  isResPerp_map hd.last mem_orthogonalGroup_of_mem_orthParab (mem_orthParab.1 hx (Fin.last s)) hv

variable (qA) in
@[expose] noncomputable def orthResHom (hd : OrthCuts r d) :
    ↥(orthParab r qA d) →* ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × A) ≃ₗ[K]
      ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × A) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K _).toMonoidHom.comp
    (MonoidHom.toHomUnits
      { toFun := fun x => orthResMat hd.last ((x : ↥(orthElementaryGroup (quadTail r qA))) :
          ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
        map_one' := orthResMat_one hd.last
        map_mul' := fun x y => orthResMat_mul hd.last
          (mapsTo_of_mem_orthParab x.2 (Fin.last s))
          (fun _ hv => isResPerp_of_mem_orthParab hd y.2 hv) })

theorem orthResHom_apply (hd : OrthCuts r d) (x : ↥(orthParab r qA d))
    (u : (Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × A) :
    orthResHom qA hd x u = orthResMat hd.last ((x : ↥(orthElementaryGroup (quadTail r qA))) :
      ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) u :=
  rfl

theorem orthResHom_mem_orthogonalGroup (hd : OrthCuts r d) (x : ↥(orthParab r qA d)) :
    orthResHom qA hd x ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail (r - d (Fin.last s)) qA) :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun u =>
    map_orthResMat hd.last mem_orthogonalGroup_of_mem_orthParab
      (fun _ hv => isResPerp_of_mem_orthParab hd x.2 hv) u

theorem sub_mem_tailFlag_of_orthResHom_eq_one (hd : OrthCuts r d) {x : ↥(orthParab r qA d)}
    (h1 : orthResHom qA hd x = 1) {v : (Fin r ⊕ Fin r → K) × A} (hv : IsResPerp hd.last v) :
    ((x : ↥(orthElementaryGroup (quadTail r qA))) :
      ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) v - v ∈
        tailFlag K A r (d (Fin.last s)) := by
  set g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) :=
    ((x : ↥(orthElementaryGroup (quadTail r qA))) :
      ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) with hgdef
  set u := orthResProj K A hd.last v
  set w := v - orthResIncl K A hd.last u
  have hw : w ∈ tailFlag K A r (d (Fin.last s)) := sub_orthResIncl_mem hd.last hv
  have hv' : v = w + orthResIncl K A hd.last u := by rw [sub_add_cancel]
  have hy : g (orthResIncl K A hd.last u) - orthResIncl K A hd.last u ∈
      tailFlag K A r (d (Fin.last s)) := by
    refine mem_tailFlag_of_orthResProj_eq_zero hd.last ?_ ?_
    · intro i
      have h1 := isResPerp_of_mem_orthParab hd x.2 (isResPerp_orthResIncl hd.last u) i
      have h2 := isResPerp_orthResIncl (K := K) (A := A) hd.last u i
      rw [Prod.fst_sub, Pi.sub_apply, h1, h2, sub_zero]
    · have h2 : orthResMat hd.last g u = u := by
        rw [← orthResHom_apply hd x u, h1, LinearEquiv.coe_one, id]
      rw [map_sub, ← orthResMat_apply, h2, orthResProj_orthResIncl, sub_self]
  have hgw : g w - w ∈ tailFlag K A r (d (Fin.last s)) :=
    Submodule.sub_mem _ (mapsTo_of_mem_orthParab x.2 (Fin.last s) w hw) hw
  rw [hv', map_add, add_sub_add_comm]
  exact Submodule.add_mem _ hgw hy

end CFSG.AGLEmbedding.LeviBlock
