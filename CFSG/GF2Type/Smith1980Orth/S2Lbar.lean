module

public import CFSG.GF2Type.Smith1980Orth.S2Decomp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions
  CFSG.Open
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Pre

variable {M1 : Subgroup S.O} (D : S2Pre S M1)

theorem eq_one_of_mem_Obar_of_comm {y : S.O} (hy : y ∈ D.Obar) (hyt : y * D.t = D.t * y) :
    y = 1 := by
  have hy3 : y ^ 3 = 1 := S13.pow_three_eq_one D.card_Obar hy
  have hinv : D.t * y * D.t⁻¹ = y⁻¹ := by
    rw [D.Obar_eq_zpowers] at hy
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    rw [← conj_zpow, D.t_inv, inv_zpow]
  have hcomm : D.t * y * D.t⁻¹ = y := by rw [← hyt]; group
  have hy2 : y * y = 1 := by
    rw [hcomm] at hinv
    exact mul_eq_one_iff_eq_inv.mpr hinv
  calc y = y ^ 3 * (y * y)⁻¹ := by group
    _ = 1 := by rw [hy3, hy2, inv_one, mul_one]

theorem eq_one_or_eq_t_of_mem_Obar_sup_of_comm {s : S.O} (hs : s ∈ D.Obar ⊔ zpowers D.t)
    (hst : s * D.t = D.t * s) : s = 1 ∨ s = D.t := by
  have hcancel : ∀ {y : S.O}, y ∈ D.Obar → (y * D.t) * D.t = D.t * (y * D.t) → y = 1 := by
    intro y hy h
    refine D.eq_one_of_mem_Obar_of_comm hy ?_
    have h' : (y * D.t) * D.t = (D.t * y) * D.t := by rw [h, mul_assoc]
    exact mul_right_cancel h'
  rcases D.mem_Obar_sup_cases hs with hso | rfl | rfl | rfl
  · exact Or.inl (D.eq_one_of_mem_Obar_of_comm hso hst)
  · exact Or.inr rfl
  · exact Or.inr (by rw [hcancel D.k_mem_Obar hst, one_mul])
  · exact Or.inr (by rw [hcancel (pow_mem D.k_mem_Obar 2) hst, one_mul])

theorem t_notMem_Cbar : D.t ∉ D.Cbar := by
  intro hc
  exact D.k_ne (D.eq_one_of_mem_Obar_of_comm D.k_mem_Obar
    (mem_centralizer_iff.mp hc.2 D.k (mem_sup_left D.k_mem_Obar)))

theorem mem_Cbar_of_comm {x : S.O} (hx : x ∈ S.Mbar) (hxt : x * D.t = D.t * x) :
    x ∈ D.Cbar ∨ D.t * x ∈ D.Cbar := by
  obtain ⟨s, hs, c, hc, rfl⟩ := D.exists_mul_Cbar_of_mem_M1 (D.rel.cent_le x hx hxt)
  have hct := D.comm_of_mem_Cbar hc
  have hst : s * D.t = D.t * s := by
    have h : (s * D.t) * c = (D.t * s) * c := by
      calc (s * D.t) * c = s * (D.t * c) := mul_assoc _ _ _
        _ = s * (c * D.t) := by rw [hct]
        _ = s * c * D.t := (mul_assoc _ _ _).symm
        _ = D.t * (s * c) := hxt
        _ = (D.t * s) * c := (mul_assoc _ _ _).symm
    exact mul_right_cancel h
  rcases D.eq_one_or_eq_t_of_mem_Obar_sup_of_comm hs hst with rfl | rfl
  · exact Or.inl (by rwa [one_mul])
  · refine Or.inr ?_
    rwa [← mul_assoc, D.t_mul_t, one_mul]

theorem mem_Lbar_inf_Cbar_or {ℓ : S.O} (hℓ : ℓ ∈ S.Lbar D.g) :
    ℓ ∈ S.Lbar D.g ⊓ D.Cbar ∨ D.t * ℓ ∈ S.Lbar D.g ⊓ D.Cbar := by
  have hcomm : ℓ * D.t = D.t * ℓ := Lbar_comm S D.good.H.conj_mem hℓ D.good.ht
  rcases D.mem_Cbar_of_comm (S.Lbar_le_Mbar D.g hℓ) hcomm with h | h
  · exact Or.inl ⟨hℓ, h⟩
  · exact Or.inr ⟨mul_mem D.good.ht hℓ, h⟩

theorem exists_eq_mul_of_mem_Lbar {ℓ : S.O} (hℓ : ℓ ∈ S.Lbar D.g) :
    ∃ c ∈ S.Lbar D.g ⊓ D.Cbar, ℓ = c ∨ ℓ = D.t * c := by
  rcases D.mem_Lbar_inf_Cbar_or hℓ with h | h
  · exact ⟨ℓ, h, Or.inl rfl⟩
  · refine ⟨D.t * ℓ, h, Or.inr ?_⟩
    rw [← mul_assoc, D.t_mul_t, one_mul]

theorem Cbar_apply_k_apply {c : S.O} (hc : c ∈ D.Cbar) (x : S.Qt) :
    (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) x) =
      (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) x) := by
  rw [← coe_mul_apply, ← coe_mul_apply, D.Cbar_comm_k hc]

theorem exists_eq_add_k_apply (x : S.Qt) :
    ∃ v ∈ Vt S D.g D.t, ∃ v' ∈ Vt S D.g D.t,
      x = v + (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v' := by
  have hx : x ∈ Vt S D.g D.t ⊔ D.Wk := by
    rw [D.isCompl_Vt_Wk.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨u, hu, rfl⟩ := D.mem_Wk_iff.mp hw
  exact ⟨v, hv, u, hu, rfl⟩

theorem eq_of_apply_eq_of_mem_Vt {c c' : S.O} (hc : c ∈ D.Cbar) (hc' : c' ∈ D.Cbar)
    (h : ∀ v ∈ Vt S D.g D.t,
      (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (c' : S.Qt ≃ₗ[ZMod 2] S.Qt) v) : c = c' := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  obtain ⟨v, hv, u, hu, rfl⟩ := D.exists_eq_add_k_apply x
  rw [map_add, map_add, h v hv, D.Cbar_apply_k_apply hc, D.Cbar_apply_k_apply hc', h u hu]

theorem resC_injective : Function.Injective D.resC := fun c c' h =>
  Subtype.ext (D.eq_of_apply_eq_of_mem_Vt c.2 c'.2 fun v hv =>
    congrArg (fun e : Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t =>
      ((e ⟨v, hv⟩ : Vt S D.g D.t) : S.Qt)) h)

@[expose] noncomputable def resLC :
    (S.Lbar D.g ⊓ D.Cbar : Subgroup S.O) →*
      (Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t) :=
  D.resC.comp (Subgroup.inclusion inf_le_right)

theorem coe_resLC_apply (c : (S.Lbar D.g ⊓ D.Cbar : Subgroup S.O)) (v : Vt S D.g D.t) :
    ((D.resLC c v : Vt S D.g D.t) : S.Qt) = ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
  rfl

theorem resLC_injective : Function.Injective D.resLC :=
  D.resC_injective.comp (Subgroup.inclusion_injective _)

theorem range_resLC : D.resLC.range = LmodN S D.g D.t := by
  ext e
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, c.2.1, fun v => rfl⟩
  · rintro ⟨x, hx, hex⟩
    obtain ⟨c, hc, hxc | hxc⟩ := D.exists_eq_mul_of_mem_Lbar hx
    · refine ⟨⟨c, hc⟩, LinearEquiv.ext fun v => Subtype.ext ?_⟩
      rw [coe_resLC_apply, hex v, hxc]
    · refine ⟨⟨c, hc⟩, LinearEquiv.ext fun v => Subtype.ext ?_⟩
      rw [coe_resLC_apply, hex v, hxc, coe_mul_apply]
      exact (D.t_apply_of_mem (D.Cbar_apply_mem_Vt hc.2 v.2)).symm

theorem exists_eichler_of_mem_Lbar_inf_Cbar {Q : QuadraticForm (ZMod 2) (Vt S D.g D.t)}
    (hQ : Q.polarBilin.Nondegenerate) (hQa : Q (aV D.good.ht) = 0)
    (hL : LmodN S D.g D.t = pointRadical Q (aV D.good.ht)) {c : S.O}
    (hc : c ∈ S.Lbar D.g ⊓ D.Cbar) :
    ∃ u : Vt S D.g D.t, polar Q (aV D.good.ht) u = 0 ∧ ∀ v : Vt S D.g D.t,
      (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = ((eichler Q (aV D.good.ht) u v : Vt S D.g D.t) : S.Qt) := by
  have hmem : D.resLC ⟨c, hc⟩ ∈ pointRadical Q (aV D.good.ht) := by
    rw [← hL, ← D.range_resLC]
    exact ⟨_, rfl⟩
  obtain ⟨u, hu, he⟩ := (mem_pointRadical_iff hQ (aV_ne_zero D.good.H D.good.ht) hQa).mp hmem
  refine ⟨u, hu, fun v => ?_⟩
  have := congrArg (fun e : Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t => ((e v : Vt S D.g D.t) : S.Qt))
    he
  exact this

end S2Pre

end CFSG.GF2Type.Smith1980Orth
