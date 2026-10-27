module

public import CFSG.GH74.Uniqueness.Bender.UnitaryOuterRoot
public import CFSG.GH74.Uniqueness.Section13A

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem A6.exists_U
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n e' : ℕ} (hL : LData c n 1) {u : X}
    (huM : u ∈ M) {LA V : Subgroup X} {Vb : Sylow 2 (↥LA ⧸ center ↥LA)}
    (hDA : A6.Dict Z M LA n e' Vb V) (hLA : c.L ≤ LA)
    (hun : u ∈ normalizer (LA : Set X))
    (hα2 : A6.barHom LA ⟨u, hun⟩ * A6.barHom LA ⟨u, hun⟩ = 1)
    (hout : ¬ ∃ k, ∀ x, A6.barHom LA ⟨u, hun⟩ x = k * x * k⁻¹) :
    ∃ U : Subgroup X, U ≤ V ∧ (∀ v ∈ U, ∀ w ∈ U, v * w = w * v) ∧
      Nat.card U = (2 ^ n) ^ 2 ∧ zHull Z M ≤ U ∧ (∀ w ∈ U, w * w ∈ zHull Z M) ∧
      (∀ w ∈ U, u * w * u⁻¹ = w⁻¹) ∧
      (∀ v ∈ V, v ∈ U ↔ v⁻¹ * (u * v * u⁻¹) ∈ zHull Z M) ∧
      (∀ h ∈ M, h ∈ normalizer (LA : Set X) → h * u = u * h → ∀ w ∈ U, h * w * h⁻¹ ∈ U) := by
  set π := QuotientGroup.mk' (center ↥LA) with hπ
  set α := A6.barHom LA ⟨u, hun⟩ with hα
  have hMF : zHull Z M ≤ LA := hL.m_le.trans hLA
  have hMV : zHull Z M ≤ V := hDA.zHull_le S hL hMF
  have huV : ∀ v ∈ V, u * v * u⁻¹ ∈ V := by
    intro v hv
    have hvLA := hDA.le hv
    have hm : u * v * u⁻¹ ∈ M := M.mul_mem (M.mul_mem huM (hDA.le_M S hv)) (M.inv_mem huM)
    have hF : u * v * u⁻¹ ∈ LA := (mem_normalizer_iff.mp hun v).mp hvLA
    obtain ⟨k, hk⟩ := hDA.two hv
    exact hDA.mem_of_mem_M S hm hF (k := k) (by rw [conj_pow, hk]; group)
  have hαV : ∀ v (hv : v ∈ V), α (π ⟨v, hDA.le hv⟩) = π ⟨u * v * u⁻¹, hDA.le (huV v hv)⟩ :=
    fun v hv => A6.barHom_mk' _ _ _ _ rfl
  have hQ : ∀ x ∈ (Vb : Subgroup (↥LA ⧸ center ↥LA)), α x ∈ (Vb : Subgroup (↥LA ⧸ center ↥LA)) := by
    intro x hx
    rw [← hDA.map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    have hv' : (v : X) ∈ V := hv
    rw [hαV v hv']
    exact hDA.mk_mem (huV v hv')
  obtain ⟨hUle, hZU, hUcard, hUcomm, hUinv, hUsq, -, -, hUchar⟩ :=
    hDA.bsub.bender.lemma_3_4_d5_unitary Vb α hα2 hout hQ
  set Ub := Bender.commutatorAut (Vb : Subgroup (↥LA ⧸ center ↥LA)) α with hUb
  set U : Subgroup X := V ⊓ (Ub.comap π).map LA.subtype with hU
  have hmemU : ∀ v, v ∈ U ↔ v ∈ V ∧ ∃ hv : v ∈ LA, π ⟨v, hv⟩ ∈ Ub := by
    intro v
    rw [hU, mem_inf, A6.mem_preimage_iff]
  have hUV : U ≤ V := inf_le_left
  have hπU : ∀ w (hw : w ∈ U), π ⟨w, hDA.le (hUV hw)⟩ ∈ Ub := by
    intro w hw
    obtain ⟨-, hwF, hwU⟩ := (hmemU w).mp hw
    exact hwU
  have hrc : ∀ v (hv : v ∈ V), v ∈ zHull Z M ↔
      π ⟨v, hDA.le hv⟩ ∈ Bender.rootCenter (Vb : Subgroup (↥LA ⧸ center ↥LA)) :=
    fun v hv => hDA.mem_zHull_iff S hL hMF hv
  refine ⟨U, hUV, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v hv w hw
    have hvV := hUV hv
    have hwV := hUV hw
    refine hDA.eq_of_mk_eq (mul_mem hvV hwV) (mul_mem hwV hvV) ?_
    have e1 : (⟨v * w, hDA.le (mul_mem hvV hwV)⟩ : ↥LA) = ⟨v, hDA.le hvV⟩ * ⟨w, hDA.le hwV⟩ := rfl
    have e2 : (⟨w * v, hDA.le (mul_mem hwV hvV)⟩ : ↥LA) = ⟨w, hDA.le hwV⟩ * ⟨v, hDA.le hvV⟩ := rfl
    rw [e1, e2, map_mul, map_mul]
    exact hUcomm _ (hπU v hv) _ (hπU w hw)
  ·
    have hmap : (U.subgroupOf LA).map π = Ub := by
      apply le_antisymm
      · rintro _ ⟨w, hw, rfl⟩
        exact hπU w hw
      · intro x hx
        have hxV := hUle hx
        rw [← hDA.map] at hxV
        obtain ⟨v, hv, rfl⟩ := hxV
        have hv' : (v : X) ∈ V := hv
        exact ⟨v, (hmemU v).mpr ⟨hv', v.2, hx⟩, rfl⟩
    have h1 := A6.card_map_of_ker π (U.subgroupOf LA) (fun x hx hx1 => by
      have hx' : (x : X) ∈ V := hUV hx
      exact Subtype.ext (hDA.eq_of_mk_eq hx' V.one_mem (by rw [hx1]; exact (map_one _).symm)))
    rw [hmap, hUcard, A6.card_subgroupOf (hUV.trans hDA.le)] at h1
    exact h1.symm
  ·
    intro m hm
    have hmV := hMV hm
    refine (hmemU m).mpr ⟨hmV, hDA.le hmV, hZU ((hrc m hmV).mp hm)⟩
  ·
    intro w hw
    have hwV := hUV hw
    rw [hrc (w * w) (mul_mem hwV hwV)]
    have e1 : (⟨w * w, hDA.le (mul_mem hwV hwV)⟩ : ↥LA) = ⟨w, hDA.le hwV⟩ * ⟨w, hDA.le hwV⟩ := rfl
    rw [e1, map_mul]
    exact hUsq _ (hπU w hw)
  ·
    intro w hw
    have hwV := hUV hw
    refine hDA.eq_of_mk_eq (huV w hwV) (inv_mem hwV) ?_
    rw [← hαV w hwV, hUinv _ (hπU w hw), ← map_inv]
    rfl
  ·
    intro v hv
    have hc : v⁻¹ * (u * v * u⁻¹) ∈ V := mul_mem (inv_mem hv) (huV v hv)
    rw [hrc _ hc]
    have e1 : π ⟨v⁻¹ * (u * v * u⁻¹), hDA.le hc⟩ = (π ⟨v, hDA.le hv⟩)⁻¹ * α (π ⟨v, hDA.le hv⟩) := by
      rw [hαV v hv, ← map_inv, ← map_mul]
      rfl
    rw [e1, hUchar _ (hDA.mk_mem hv)]
    constructor
    · intro hvU
      exact hπU v hvU
    · intro hvU
      exact (hmemU v).mpr ⟨hv, hDA.le hv, hvU⟩
  ·
    intro h hhM hhN hhu w hw
    have hwV := hUV hw
    have hhw : h * w * h⁻¹ ∈ V := by
      have hm : h * w * h⁻¹ ∈ M := M.mul_mem (M.mul_mem hhM (hDA.le_M S hwV)) (M.inv_mem hhM)
      have hF : h * w * h⁻¹ ∈ LA := (mem_normalizer_iff.mp hhN w).mp (hDA.le hwV)
      obtain ⟨k, hk⟩ := hDA.two hwV
      exact hDA.mem_of_mem_M S hm hF (k := k) (by rw [conj_pow, hk]; group)
    have hchar : ∀ v ∈ V, v ∈ U ↔ v⁻¹ * (u * v * u⁻¹) ∈ zHull Z M := by
      intro v hv
      have hc : v⁻¹ * (u * v * u⁻¹) ∈ V := mul_mem (inv_mem hv) (huV v hv)
      rw [hrc _ hc]
      have e1 : π ⟨v⁻¹ * (u * v * u⁻¹), hDA.le hc⟩ =
          (π ⟨v, hDA.le hv⟩)⁻¹ * α (π ⟨v, hDA.le hv⟩) := by
        rw [hαV v hv, ← map_inv, ← map_mul]
        rfl
      rw [e1, hUchar _ (hDA.mk_mem hv)]
      exact ⟨fun hvU => hπU v hvU, fun hvU => (hmemU v).mpr ⟨hv, hDA.le hv, hvU⟩⟩
    rw [hchar _ hhw]
    have h1 := (hchar w hwV).mp hw
    have hhu' : h⁻¹ * u⁻¹ = u⁻¹ * h⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hhu]
    have e2 : (h * w * h⁻¹)⁻¹ * (u * (h * w * h⁻¹) * u⁻¹) = h * (w⁻¹ * (u * w * u⁻¹)) * h⁻¹ := by
      calc (h * w * h⁻¹)⁻¹ * (u * (h * w * h⁻¹) * u⁻¹)
          = h * w⁻¹ * h⁻¹ * (u * h) * w * (h⁻¹ * u⁻¹) := by group
        _ = h * w⁻¹ * h⁻¹ * (h * u) * w * (u⁻¹ * h⁻¹) := by rw [← hhu, hhu']
        _ = h * (w⁻¹ * (u * w * u⁻¹)) * h⁻¹ := by group
    rw [e2]
    exact hL.m_normal h hhM _ h1

end CFSG.GH74.Uniqueness
