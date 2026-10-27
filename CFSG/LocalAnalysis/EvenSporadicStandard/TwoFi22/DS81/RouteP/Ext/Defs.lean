module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Walk
public import CFSG.Quasithin.Background.HMathieuO2Cert

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

structure CocodeExtension (N : Type*) [Group N] (E : Subgroup N) (e : ↥E ≃* W11) : Prop where
  normal : E.Normal
  centralizer_eq : Subgroup.centralizer (E : Set N) = E
  range_eq : (MonoidHom.range (@MulAut.conjNormal N _ E normal)).map
      (MulAut.congr e).toMonoidHom = img11 AutPerm

namespace CocodeExtension

variable {N : Type*} [Group N] {E : Subgroup N} {e : ↥E ≃* W11} (h : CocodeExtension N E e)

@[expose] def conjE (n : N) : MulAut ↥E := @MulAut.conjNormal N _ E h.normal n

theorem coe_conjE (n : N) (x : ↥E) : ((h.conjE n x : ↥E) : N) = n * x * n⁻¹ := by
  haveI := h.normal
  exact MulAut.conjNormal_apply n x

@[expose] noncomputable def act : N →* MulAut W11 :=
  (MulAut.congr e).toMonoidHom.comp (@MulAut.conjNormal N _ E h.normal)

theorem act_apply (n : N) (x : ↥E) : h.act n (e x) = e (h.conjE n x) := by
  show e (h.conjE n (e.symm (e x))) = e (h.conjE n x)
  rw [MulEquiv.symm_apply_apply]

theorem act_mem_range (n : N) : h.act n ∈ (rho11 AutPerm le_rfl).range := by
  rw [range_rho11_eq_img11 AutPerm le_rfl, ← h.range_eq]
  exact Subgroup.mem_map_of_mem _ (⟨n, rfl⟩)

@[expose] noncomputable def π : N →* ↥AutPerm :=
  ((MonoidHom.ofInjective (rho11_injective AutPerm le_rfl)).symm :
      ↥(rho11 AutPerm le_rfl).range →* ↥AutPerm).comp
    (h.act.codRestrict (rho11 AutPerm le_rfl).range h.act_mem_range)

theorem rho_π (n : N) : rho11 AutPerm le_rfl (h.π n) = h.act n :=
  MonoidHom.apply_ofInjective_symm (rho11_injective AutPerm le_rfl) ⟨h.act n, h.act_mem_range n⟩

theorem π_apply_e (n : N) (x : ↥E) :
    rho11 AutPerm le_rfl (h.π n) (e x) = e (h.conjE n x) := by
  rw [h.rho_π, h.act_apply]

theorem π_surjective : Function.Surjective h.π := by
  intro σ
  have hmem : rho11 AutPerm le_rfl σ ∈ (rho11 AutPerm le_rfl).range :=
    ⟨σ, rfl⟩
  rw [range_rho11_eq_img11 AutPerm le_rfl, ← h.range_eq] at hmem
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hmem
  refine ⟨n, rho11_injective AutPerm le_rfl ?_⟩
  rw [h.rho_π]
  exact hn

theorem π_eq_one_iff {n : N} : h.π n = 1 ↔ n ∈ E := by
  have hcent : n ∈ E ↔ n ∈ Subgroup.centralizer (E : Set N) := by rw [h.centralizer_eq]
  rw [hcent, Subgroup.mem_centralizer_iff]
  constructor
  · intro hn x hx
    have h1 : rho11 AutPerm le_rfl (h.π n) (e ⟨x, hx⟩) = e ⟨x, hx⟩ := by
      rw [hn, map_one]
      rfl
    rw [h.π_apply_e] at h1
    have h2 := congrArg Subtype.val (e.injective h1)
    rw [h.coe_conjE] at h2
    have h3 : n * x * n⁻¹ * n = x * n := by rw [h2]
    simpa [mul_assoc] using h3.symm
  · intro hn
    apply rho11_injective AutPerm le_rfl
    rw [map_one]
    refine MulEquiv.ext fun w => ?_
    obtain ⟨x, rfl⟩ := e.surjective w
    rw [h.π_apply_e]
    refine congrArg e (Subtype.ext ?_)
    rw [h.coe_conjE]
    have h4 := hn x x.2
    rw [← h4]
    simp

@[expose] noncomputable def toExtData :
    ExtData (rho11 AutPerm le_rfl) N := by
  classical
  exact
  { π := h.π
    eT := fun n => if hn : n ∈ E then e ⟨n, hn⟩ else 1
    π_surjective := h.π_surjective
    eT_mul := fun x y hx hy => by
      have hx' : x ∈ E := h.π_eq_one_iff.1 hx
      have hy' : y ∈ E := h.π_eq_one_iff.1 hy
      have hxy : x * y ∈ E := E.mul_mem hx' hy'
      rw [dif_pos hxy, dif_pos hx', dif_pos hy']
      exact map_mul e ⟨x, hx'⟩ ⟨y, hy'⟩
    eT_conj := fun n x hx => by
      have hx' : x ∈ E := h.π_eq_one_iff.1 hx
      have hnx : n * x * n⁻¹ ∈ E := h.normal.conj_mem x hx' n
      rw [dif_pos hnx, dif_pos hx']
      exact (congrArg e (Subtype.ext (h.coe_conjE n ⟨x, hx'⟩).symm)).trans
        (h.π_apply_e n ⟨x, hx'⟩).symm
    eT_inj := fun x y hx hy hxy => by
      have hx' : x ∈ E := h.π_eq_one_iff.1 hx
      have hy' : y ∈ E := h.π_eq_one_iff.1 hy
      rw [dif_pos hx', dif_pos hy'] at hxy
      exact congrArg Subtype.val (e.injective hxy)
    eT_surj := fun w => by
      refine ⟨(e.symm w : N), h.π_eq_one_iff.2 (e.symm w).2, ?_⟩
      rw [dif_pos (e.symm w).2]
      exact e.apply_symm_apply w }

theorem toExtData_eT {x : N} (hx : x ∈ E) :
    h.toExtData.eT x = e ⟨x, hx⟩ := by
  classical
  exact dif_pos hx

end CocodeExtension

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
