module

public import CFSG.LargeExtraspecial.S4CESp
public import CFSG.LargeExtraspecial.S4SpFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Transvection
open scoped commutatorElement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

theorem conj_mem_spPointRadical_of_isometry {p : V} {e : V ≃ₗ[ZMod 2] V}
    (he : e ∈ spPointRadical β p) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.BilinForm.isometryGroup β) : g * e * g⁻¹ ∈ spPointRadical β (g p) := by
  obtain ⟨he1, hep, he2, he3⟩ := he
  have hiso := TauCeti.BilinForm.mem_isometryGroup_iff.mp hg
  have hc : ∀ x, (g * e * g⁻¹) x - x = g (e (g⁻¹ x) - g⁻¹ x) := fun x => by
    rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply, apply_inv_self']
  refine ⟨mul_mem (mul_mem hg he1) (inv_mem hg), ?_, fun x hx => ?_, fun v => ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, inv_apply_self', hep]
  · have hx' : β p (g⁻¹ x) = 0 := by rw [← hiso, apply_inv_self']; exact hx
    rw [hc]
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (he2 _ hx')
    rw [← hk, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [hc, hiso]
    exact he3 _

theorem spPointRadical_map_conj {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.BilinForm.isometryGroup β) (p : V) :
    (spPointRadical β p).map (MulAut.conj g).toMonoidHom = spPointRadical β (g p) := by
  apply le_antisymm
  · rintro _ ⟨e, he, rfl⟩
    exact conj_mem_spPointRadical_of_isometry he hg
  · intro e he
    refine ⟨g⁻¹ * e * g⁻¹⁻¹, ?_, by simp [mul_assoc]⟩
    have := conj_mem_spPointRadical_of_isometry he (inv_mem hg)
    rwa [inv_apply_self'] at this

theorem spRho_eq_mul_spTransvection (hβ : β.IsAlt) {u w : V} (huw : β u w = 0) :
    spRho hβ huw 0 = spTransvection β hβ u * spTransvection β hβ w *
      spTransvection β hβ (u + w) := by
  have hwu : β w u = 0 := by rw [OrthoF2.isAlt_symm hβ, huw]
  ext x
  simp only [LinearEquiv.mul_apply, spTransvection_apply, spRho_apply, map_add, map_smul,
    hβ.self_eq_zero, huw, hwu]
  match_scalars <;> (ring_nf; try reduce_mod_char)

theorem spTransvection_commute (hβ : β.IsAlt) {u w : V} (huw : β u w = 0) :
    spTransvection β hβ u * spTransvection β hβ w =
      spTransvection β hβ w * spTransvection β hβ u := by
  have hwu : β w u = 0 := by rw [OrthoF2.isAlt_symm hβ, huw]
  ext x
  simp only [LinearEquiv.mul_apply, spTransvection_apply, map_add, map_smul, huw, hwu,
    add_zero, zero_smul]
  abel

section Lift

variable [FiniteDimensional (ZMod 2) V] {K : Type*} [Group K] {π : K →* (V ≃ₗ[ZMod 2] V)}
  {E : Subgroup K} {a : V}

theorem CEHyp.exists_apply_eq_of_sp
    (h : CEHyp π E a (TauCeti.BilinForm.isometryGroup β) (spPointRadical β a))
    (hβ : β.IsAlt) (hnd : β.Nondegenerate) (ha : a ≠ 0) {v : V} (hv : v ≠ 0) :
    ∃ k, π k a = v := by
  obtain ⟨g, hg, hgv⟩ := exists_isometry_apply_eq hβ hnd ha hv
  have hgX : g ∈ TauCeti.BilinForm.isometryGroup β := (closure_le _).mpr (by
    rintro _ ⟨c, rfl⟩
    exact spTransvection_mem_isometryGroup hβ c) hg
  have hgr : g ∈ π.range := h.range_eq ▸ hgX
  obtain ⟨k, hk⟩ := hgr
  exact ⟨k, by rw [hk, hgv]⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem CEHyp.map_Ept_sp
    (h : CEHyp π E a (TauCeti.BilinForm.isometryGroup β) (spPointRadical β a)) {p : V} {k : K}
    (hk : π k a = p) : (Ept π E a p).map π = spPointRadical β p := by
  have hkX : π k ∈ TauCeti.BilinForm.isometryGroup β := h.range_eq ▸ ⟨k, rfl⟩
  rw [h.map_Ept hk, spPointRadical_map_conj hkX, hk]

theorem CEHyp.liftPt_spRho_symm
    (h : CEHyp π E a (TauCeti.BilinForm.isometryGroup β) (spPointRadical β a))
    (hβ : β.IsAlt) (hnd : β.Nondegenerate) (ha : a ≠ 0) {u w u' w' : V} (huw : β u w = 0)
    (huu' : β u u' = 1) (hww' : β w w' = 1) (huw' : β u w' = 0) (hwu' : β w u' = 0) :
    liftPt π E a w (spRho hβ huw 0) = liftPt π E a u (spRho hβ huw 0) := by
  have hwu : β w u = 0 := by rw [OrthoF2.isAlt_symm hβ, huw]
  have hne : ∀ {v v' : V}, β v v' = 1 → v ≠ 0 := fun {v v'} hvv' h0 => by
    rw [h0, map_zero, LinearMap.zero_apply] at hvv'
    exact zero_ne_one hvv'
  have hs1 : β (u + w) u' = 1 := by rw [map_add, LinearMap.add_apply, huu', hwu', add_zero]
  obtain ⟨ku, hku⟩ := h.exists_apply_eq_of_sp hβ hnd ha (hne huu')
  obtain ⟨kw, hkw⟩ := h.exists_apply_eq_of_sp hβ hnd ha (hne hww')
  obtain ⟨ks, hks⟩ := h.exists_apply_eq_of_sp hβ hnd ha (hne hs1)
  set ρ := spRho hβ huw 0 with hρdef
  have hρw' : ρ = spRho hβ hwu 0 := LinearEquiv.ext fun x => by
    rw [spRho_apply, spRho_apply, zero_mul, zero_mul, add_zero, add_zero, add_right_comm]
  have hρu : ρ ∈ (Ept π E a u).map π := by
    rw [h.map_Ept_sp hku]
    exact spRho_mem_spPointRadical hβ huw 0
  have hρw : ρ ∈ (Ept π E a w).map π := by
    rw [h.map_Ept_sp hkw, hρw']
    exact spRho_mem_spPointRadical hβ hwu 0
  have hτ : ∀ {v : V} {k : K}, π k a = v → spTransvection β hβ v ∈ (Ept π E a v).map π :=
    fun {v k} hk => by
      rw [h.map_Ept_sp hk]
      exact spTransvection_mem_spPointRadical hβ v
  have hs : β (u + w) (u' + w') = 0 := by
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, huu', hww', huw', hwu',
      add_zero, zero_add]
    rfl
  set g := spRho hβ hs 0
  have hgX : g ∈ TauCeti.BilinForm.isometryGroup β := spRho_mem_isometryGroup hβ hs 0
  have hgu : g u = w := by
    rw [spRho_apply, map_add, hβ.self_eq_zero, huw, add_zero, zero_smul, add_zero, map_add, huu',
      huw', add_zero, zero_mul, add_zero, one_smul, ← add_assoc, OrthoF2.vec_add_self, zero_add]
  have hgw : g w = u := by
    rw [spRho_apply, map_add, hwu, hβ.self_eq_zero, add_zero, zero_smul, add_zero, map_add, hwu',
      hww', zero_add, zero_mul, add_zero, one_smul, add_comm u w, ← add_assoc,
      OrthoF2.vec_add_self, zero_add]
  have hgs : g (u + w) = u + w := by rw [map_add, hgu, hgw, add_comm]
  have hgρ : g * ρ * g⁻¹ = ρ := by
    rw [conj_spRho hβ huw 0 hgX (by rw [hgu, hgw]; exact hwu), spRho_congr hβ _ hwu hgu hgw rfl,
      ← hρw']
  have hgrange : g ∈ π.range := h.range_eq ▸ hgX
  obtain ⟨x, hx⟩ := hgrange
  have e1 : x * liftPt π E a u ρ * x⁻¹ = liftPt π E a w ρ := by
    rw [← h.liftPt_conj ⟨ku, hku⟩ hρu x, hx, hgu, hgρ]
  set tu := liftPt π E a u (spTransvection β hβ u)
  set tw := liftPt π E a w (spTransvection β hβ w)
  set ts := liftPt π E a (u + w) (spTransvection β hβ (u + w))
  have e2 : x * tu * x⁻¹ = tw := by
    rw [← h.liftPt_conj ⟨ku, hku⟩ (hτ hku) x, hx, conj_spTransvection hβ u hgX, hgu]
  have e3 : x * tw * x⁻¹ = tu := by
    rw [← h.liftPt_conj ⟨kw, hkw⟩ (hτ hkw) x, hx, conj_spTransvection hβ w hgX, hgw]
  have e4 : x * ts * x⁻¹ = ts := by
    rw [← h.liftPt_conj ⟨ks, hks⟩ (hτ hks) x, hx, conj_spTransvection hβ _ hgX, hgs]
  have hcomm : tu * tw = tw * tu := by
    have hfix : π tw u = u := by
      rw [apply_liftPt (hτ hkw), spTransvection_apply, huw, zero_smul, add_zero]
    have := h.commutatorElement_liftPt ⟨ku, hku⟩ (hτ hku) hfix
    rw [apply_liftPt (hτ hkw), commutatorElement_eq_one_iff_mul_comm.mpr
      (spTransvection_commute hβ huw), h.liftPt_one ⟨ku, hku⟩] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  set P := tu * tw * ts
  have hPπ : π P = ρ := by
    rw [map_mul, map_mul, apply_liftPt (hτ hku), apply_liftPt (hτ hkw), apply_liftPt (hτ hks),
      hρdef, spRho_eq_mul_spTransvection hβ huw]
  have hPx : x * P * x⁻¹ = P := by
    calc x * P * x⁻¹ = x * (tu * tw * ts) * x⁻¹ := rfl
      _ = (x * tu * x⁻¹) * (x * tw * x⁻¹) * (x * ts * x⁻¹) := by group
      _ = P := by rw [e2, e3, e4, ← hcomm]
  set eu := liftPt π E a u ρ
  have hz : (eu⁻¹ * P)⁻¹ ∈ center K := inv_mem (h.mem_center_of_mem_ker (by
    rw [map_mul, map_inv, apply_liftPt hρu, hPπ, inv_mul_cancel]))
  have hzx := (mem_center_iff.mp hz) x
  calc liftPt π E a w ρ = x * eu * x⁻¹ := e1.symm
    _ = x * P * x⁻¹ * (x * (eu⁻¹ * P)⁻¹ * x⁻¹) := by group
    _ = P * (eu⁻¹ * P)⁻¹ := by rw [hPx, hzx, mul_inv_cancel_right]
    _ = eu := by group

end Lift

theorem IsSpBasis.spPointRadical_le_closure [FiniteDimensional (ZMod 2) V] {n : ℕ}
    {c : Basis (Fin n ⊕ Fin n) (ZMod 2) V} (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (hc : IsSpBasis β c) (p : Fin n ⊕ Fin n) :
    spPointRadical β (c p) ≤
      closure {g | ∃ q, q ≠ Sum.swap p ∧ g = spIota c (spElt p q (1 : ZMod 2))} := by
  set H := closure {g | ∃ q, q ≠ Sum.swap p ∧ g = spIota c (spElt p q (1 : ZMod 2))}
  have hτ : spTransvection β hβ (c p) ∈ H :=
    subset_closure ⟨p, (Pres.swap_ne_self p).symm, (hc.spIota_spElt_one_self hβ p).symm⟩
  have hρ0 : ∀ (h0 : β (c p) 0 = 0), spRho hβ h0 0 = 1 := fun h0 =>
    LinearEquiv.ext fun x => by
      rw [spRho_apply]
      simp
  set S : Set V := c '' {r | r ≠ Sum.swap p}
  have hS : Submodule.span (ZMod 2) S ≤ LinearMap.ker (β (c p)) := by
    rw [Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    exact hc.apply_eq_zero hr
  have hk : ∀ {d : V}, d ∈ Submodule.span (ZMod 2) S → β (c p) d = 0 := fun hd =>
    LinearMap.mem_ker.mp (hS hd)
  have key : ∀ d (hd : d ∈ Submodule.span (ZMod 2) S), spRho hβ (hk hd) 0 ∈ H := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, hr, rfl⟩ := hx
      by_cases hrp : r = p
      · subst hrp
        have h0 : β (c r) 0 = 0 := by rw [map_zero]
        have h1 : β (c r) (0 + c r) = 0 := by
          rw [zero_add]
          exact hk (Submodule.subset_span ⟨r, hr, rfl⟩)
        rw [spRho_congr hβ _ h1 rfl (zero_add (c r)).symm rfl, spRho_add_self hβ h0 0, hρ0]
        exact one_mem _
      · rw [← hc.spIota_spElt_one hβ hrp hr]
        exact subset_closure ⟨r, hr, rfl⟩
    | zero =>
      rw [hρ0]
      exact one_mem _
    | add x y hx hy ihx ihy =>
      have hm := spRho_mul hβ (hk hx) (hk hy) 0 0 (hk (add_mem hx hy))
      rcases OrthoF2.zmod2_eq_zero_or_eq_one (β x y) with h0 | h1
      · rw [h0, add_zero, add_zero] at hm
        rw [← hm]
        exact mul_mem ihx ihy
      · rw [h1, zero_add, zero_add, spRho_one_eq] at hm
        have : spRho hβ (hk (add_mem hx hy)) 0 =
            spRho hβ (hk hx) 0 * spRho hβ (hk hy) 0 * (spTransvection β hβ (c p))⁻¹ := by
          rw [hm, mul_inv_cancel_right]
        rw [this]
        exact mul_mem (mul_mem ihx ihy) (inv_mem hτ)
    | smul t x hx ih =>
      rcases OrthoF2.zmod2_eq_zero_or_eq_one t with rfl | rfl
      · rw [spRho_congr hβ _ (by rw [map_zero]) rfl (zero_smul _ x) rfl, hρ0]
        exact one_mem _
      · rw [spRho_congr hβ _ (hk hx) rfl (one_smul _ x) rfl]
        exact ih
  intro g hg
  obtain ⟨d, hcd, l, rfl⟩ := exists_eq_spRho hβ hnd (c.ne_zero p) hg
  have hd : d ∈ Submodule.span (ZMod 2) S := by
    rw [← c.sum_repr d]
    refine Submodule.sum_mem _ fun r _ => ?_
    by_cases hr : r = Sum.swap p
    · subst hr
      rw [hc.repr_swap, OrthoF2.isAlt_symm hβ, hcd, zero_smul]
      exact zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, hr, rfl⟩)
  rcases OrthoF2.zmod2_eq_zero_or_eq_one l with rfl | rfl
  · exact key d hd
  · rw [spRho_one_eq]
    exact mul_mem (key d hd) hτ

end CFSG.LargeExtraspecial.S4
