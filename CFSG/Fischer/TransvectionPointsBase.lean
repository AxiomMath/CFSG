
module

public import CFSG.Fischer.T46Unitary
import all CFSG.Fischer.F4
public import Certificates.Data.CFSGNative.Fischer.Polar
public import CFSG.Fischer.UnitaryTransport

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix Blueprint.Fischer Native

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec tvTabs

@[expose] noncomputable def tvSU' (m : Fin 693) : SU0 :=
  ⟨tvGL (uVec m) (uVec_iso ptsFacts m.2), tvGL_mem_SU0 _⟩

@[expose] noncomputable def tvP (m : Fin 693) : Equiv.Perm (Fin 693) := piSU (tvSU' m)

@[expose] noncomputable def tvPsu (m : Fin 693) : PSU (1 : Matrix (Fin 6) (Fin 6) K) :=
  QuotientGroup.mk (suEquiv (tvSU' m))

theorem tvP_mem (m : Fin 693) : tvP m ∈ T46 := by rw [← range_piSU]; exact ⟨_, rfl⟩

theorem suQuot_tvPsu (m : Fin 693) :
    suQuotEquiv (psuEquiv.symm (tvPsu m)) = ⟨tvP m, tvP_mem m⟩ := by
  apply Subtype.ext
  rw [tvPsu, ← psuEquiv_mk, MulEquiv.symm_apply_apply, suQuotEquiv_mk]
  rfl

theorem tvTabs_get (m : Fin 693) : tvTabs[m.val]! = tvTable uPts[m.val]! := by
  unfold tvTabs
  rw [getElem!_pos _ m.val (by simp), Array.getElem_ofFn]

theorem rep_tvP (m : Fin 693) : Rep 693 tvTabs[m.val]! (tvP m) := by
  rw [tvTabs_get]
  intro i hi
  have h := rep_tvTable (uVec m) (uVec_iso ptsFacts m.2)
  rw [codeOf_uVec ptsFacts m.2] at h
  rw [h i hi, idx_of_lt _ hi, idx_of_lt _ hi]
  rfl

theorem perm_eq_of_rep {T : Table} {g h : Equiv.Perm (Fin 693)} (hg : Rep 693 T g)
    (hh : Rep 693 T h) : g = h := by
  ext i
  have := (hg i.val i.2).symm.trans (hh i.val i.2)
  rwa [idx_of_lt _ i.2, idx_of_lt _ i.2] at this

theorem rep_unique_table {T T' : Table} {g : Equiv.Perm (Fin 693)} (hT : T.size = 693)
    (hT' : T'.size = 693) (hg : Rep 693 T g) (hg' : Rep 693 T' g) : T = T' := by
  apply Array.ext (by rw [hT, hT'])
  intro i hi _
  have h1 := hg i (by rwa [hT] at hi)
  have h2 := hg' i (by rwa [hT] at hi)
  have := h1.trans h2.symm
  unfold ap at this
  rw [getElem!_pos T i hi, getElem!_pos T' i (by rw [hT']; rwa [hT] at hi)] at this
  exact UInt32.toNat_inj.1 this

theorem tvTabs_size (m : Fin 693) : tvTabs[m.val]!.size = 693 := by
  rw [tvTabs_get]; unfold tvTable; simp

theorem compT_size (P Q : Table) : (compT 693 P Q).size = 693 := by unfold compT; simp

theorem ψV_add_smul' (x w : W) (c : F4) : ψV (x + c • w) = ψV x + ψ c • ψV w := by
  funext i
  simp only [ψV, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]

theorem ψGL_tvGL_mulVec (w : W) (hw : hermStd w w = 0) (x : Blueprint.Fischer.V) :
    ((ψGL (tvGL w hw) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec x =
      x + hermitian 1 x (ψV w) • ψV w := by
  obtain ⟨x0, rfl⟩ := ψV_surjective x
  rw [ψGL_val, tvGL_val, mulVec_ψ, tvM_mulVec, ψV_add_smul', hermitian_ψ, herm_eq_std]

theorem ψV_ne_zero' {w : W} (hw : w ≠ 0) : ψV w ≠ 0 := by
  intro h
  apply hw
  apply ψV_injective
  rw [h]
  funext i
  simp [ψV]

theorem tvPsu_mem (u : Fin 693) : tvPsu u ∈ Transvections 1 := by
  refine ⟨suEquiv (tvSU' u), rfl, ψV (uVec u), ψV_ne_zero' (uVec_ne_zero ptsFacts u.2), ?_, ?_⟩
  · rw [hermitian_ψ, herm_eq_std, uVec_iso ptsFacts u.2, map_zero]
  · intro x
    rw [suEquiv_val]
    exact ψGL_tvGL_mulVec _ (uVec_iso ptsFacts u.2) x

private theorem cube_one' : ∀ c : F4, c ≠ 0 → c ^ 2 * c = 1 := by decide

theorem tvM_smul' {c : F4} (hc : c ≠ 0) (w : W) : tvM (c • w) = tvM w := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [tvM_mulVec, tvM_mulVec, hermStd_smul_right, smul_smul]
  congr 2
  calc c ^ 2 * hermStd x w * c = (c ^ 2 * c) * hermStd x w := by ring
    _ = hermStd x w := by rw [cube_one' c hc, one_mul]

theorem exists_tvPsu (q : PSU (1 : Matrix (Fin 6) (Fin 6) K)) (hq : q ∈ Transvections 1) :
    ∃ u : Fin 693, q = tvPsu u := by
  obtain ⟨s', rfl, v, hv0, hviso, hact⟩ := hq
  obtain ⟨w0, rfl⟩ := ψV_surjective v
  have hw0 : w0 ≠ 0 := fun h => hv0 (by rw [h]; funext i; simp [ψV])
  have hiso : hermStd w0 w0 = 0 := by
    rw [hermitian_ψ, herm_eq_std] at hviso
    exact ψ.injective (by rw [hviso, map_zero])
  refine ⟨⟨ptIdx w0, ptIdx_lt ptsFacts hw0 hiso⟩, congrArg QuotientGroup.mk ?_⟩
  have hgl : (tvSU' ⟨ptIdx w0, ptIdx_lt ptsFacts hw0 hiso⟩ : GL (Fin 6) F4) = tvGL w0 hiso := by
    apply Units.ext
    show tvM (uVec (ptIdx w0)) = tvM w0
    rw [uVec_ptIdx ptsFacts hw0 hiso]
    obtain ⟨c, hc, hcw⟩ := normV_eq_smul hw0
    rw [hcw, tvM_smul' hc]
  apply Subtype.ext
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [hact x, suEquiv_val, hgl, ψGL_tvGL_mulVec]

theorem transvections_eq : Transvections (1 : Matrix (Fin 6) (Fin 6) K) = Set.range tvPsu := by
  ext q
  constructor
  · intro hq
    obtain ⟨u, rfl⟩ := exists_tvPsu q hq
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact tvPsu_mem u

noncomputable def psuT46 : PSU (1 : Matrix (Fin 6) (Fin 6) K) ≃* T46 :=
  psuEquiv.symm.trans suQuotEquiv

theorem psuT46_tvPsu (m : Fin 693) : (psuT46 (tvPsu m) : Equiv.Perm (Fin 693)) = tvP m := by
  rw [psuT46, MulEquiv.trans_apply, suQuot_tvPsu]

end CFSG.Fischer
