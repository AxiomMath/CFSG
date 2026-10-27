module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67RedAut
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem isElementaryAbelian_of_injective' {G H : Type*} [Group G] [Group H] {p : ℕ} (f : G →* H)
    (hf : Function.Injective f) [IsElementaryAbelian p H] : IsElementaryAbelian p G :=
  { is_comm := ⟨fun x y => hf (by rw [map_mul, map_mul]; exact IsMulCommutative.is_comm.comm _ _)⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => hf (by
      rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p p H)
        _) }

section Inner

variable {Y : Type} [Group Y]

theorem exists_plane_of_inner (hcen : Subgroup.center Y = ⊥) {r : ℕ} {V : Subgroup (MulAut Y)}
    (hVe : IsElementaryAbelian r V) (hVc : Nat.card V = r ^ 2)
    (hVinn : ∀ v ∈ V, v ∈ (MulAut.conj : Y →* MulAut Y).range) :
    ∃ E : Subgroup Y, IsElementaryAbelian r E ∧ Nat.card E = r ^ 2 ∧
      E.map (MulAut.conj : Y →* MulAut Y) = V := by
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    mulAut_conj_injective_of_center_bot hcen
  set E : Subgroup Y := V.comap (MulAut.conj : Y →* MulAut Y) with hE
  have hEmap : E.map (MulAut.conj : Y →* MulAut Y) = V := by
    rw [hE, Subgroup.map_comap_eq]
    exact inf_eq_right.2 (fun v hv => hVinn v hv)
  let e : E ≃* V := (Subgroup.equivMapOfInjective E (MulAut.conj : Y →* MulAut Y) hinj).trans
    (MulEquiv.subgroupCongr hEmap)
  refine ⟨E, isElementaryAbelian_of_injective' (p := r) e.toMonoidHom e.injective, ?_, hEmap⟩
  rw [Nat.card_congr e.toEquiv]
  exact hVc

theorem iSup_fixSub_eq_top_of_closure (hcen : Subgroup.center Y = ⊥) {E : Subgroup Y}
    (hcl : Subgroup.closure {k : Y | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤) :
    (⨆ v ∈ E.map (MulAut.conj : Y →* MulAut Y), ⨆ (_ : v ≠ 1), fixSub v) = ⊤ := by
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    mulAut_conj_injective_of_center_bot hcen
  rw [eq_top_iff, ← hcl, Subgroup.closure_le]
  rintro k ⟨x, hx, hx1, hk⟩
  have hv : MulAut.conj x ∈ E.map (MulAut.conj : Y →* MulAut Y) := ⟨x, hx, rfl⟩
  have hv1 : MulAut.conj x ≠ 1 := fun h => hx1 (hinj (by rw [h, map_one]))
  have hkfix : k ∈ fixSub (MulAut.conj x) := by
    rw [mem_fixSub, MulAut.conj_apply]
    calc x * k * x⁻¹ = k * x * x⁻¹ := by rw [← hk]
      _ = k := by group
  exact Subgroup.mem_iSup_of_mem (MulAut.conj x) (Subgroup.mem_iSup_of_mem hv
    (Subgroup.mem_iSup_of_mem hv1 hkfix))

end Inner

end CFSG.GH74.GLS.Stage2.Bender.Thm1
