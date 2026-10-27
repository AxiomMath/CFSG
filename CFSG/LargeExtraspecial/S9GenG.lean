module

public import CFSG.LargeExtraspecial.S9One
public import CFSG.LargeExtraspecial.S9Cent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_commSpace_mul_eq {x y : S.O}
    (hinf : commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (hx : ∀ v ∈ commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt), (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    finrank (ZMod 2) (commSpace ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) +
        finrank (ZMod 2) (commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  set A := commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) with hA
  set B := commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) with hB
  have hO : ∀ z : S.O, fixSpace (z : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      LinearMap.BilinForm.orthogonal S.q.polarBilin (commSpace (z : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
    fun z => fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate z.2
  have hfix : fixSpace ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ fixSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    ext v
    rw [Submodule.mem_inf, mem_fixSpace, mem_fixSpace, mem_fixSpace, coe_mul_apply]
    constructor
    · intro h
      have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) - v =
          ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) + ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) := by
        have h1 := hx _ (sub_mem_commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
        rw [map_sub] at h1
        calc (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) - v =
            ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) -
              (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) + ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) := by abel
          _ = ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) + ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) := by
            rw [h1]
      rw [h, sub_self] at e
      have hmem : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ A ⊓ B := by
        refine ⟨sub_mem_commSpace _ v, ?_⟩
        rw [eq_neg_of_add_eq_zero_right e.symm]
        exact neg_mem (sub_mem_commSpace _ v)
      rw [hinf, Submodule.mem_bot, sub_eq_zero] at hmem
      exact ⟨hmem, (x : S.Qt ≃ₗ[ZMod 2] S.Qt).injective (h.trans hmem.symm)⟩
    · rintro ⟨h1, h2⟩
      rw [h2, h1]
  have hperp : fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ fixSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      LinearMap.BilinForm.orthogonal S.q.polarBilin (A ⊔ B) := by
    rw [hO x, hO y]
    ext v
    rw [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff,
      LinearMap.BilinForm.mem_orthogonal_iff,
      LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · rintro ⟨h1, h2⟩ w hw
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
      have e1 : S.q.polarBilin a v = 0 := h1 a ha
      have e2 : S.q.polarBilin b v = 0 := h2 b hb
      show S.q.polarBilin (a + b) v = 0
      rw [map_add, LinearMap.add_apply, e1, e2, add_zero]
    · intro h
      exact ⟨fun a ha => h a (Submodule.mem_sup_left ha),
        fun b hb => h b (Submodule.mem_sup_right hb)⟩
  have h1 := finrank_commSpace_add_finrank_fixSpace ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have h2 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate (A ⊔ B)
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hinf, finrank_bot, add_zero] at h3
  have h4 := Submodule.finrank_le (A ⊔ B)
  rw [hfix, hperp, h2] at h1
  omega

theorem not_conj_mul_t_of_inf_eq_bot (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {x : S.O}
    (hinf : Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (hτV : ∀ v ∈ Vt S g t, ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    {y : S.O} (hy : y * (x * t * x⁻¹) * y⁻¹ = x * t * x⁻¹ * t) : False := by
  have hcomm := (commSpace_t_eq H C ht ht1 hVQ).1
  have hinf' : commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
      commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
    rw [hcomm, inf_comm]
    exact hinf
  have hdim := finrank_commSpace_mul_eq hinf' (fun v hv => by
    rw [hcomm] at hv
    exact hτV v hv)
  have hconj : commSpace ((x * t * x⁻¹ * t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
        (y : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [← hy, S8.commSpace_conj]
  have hdimy := LinearEquiv.finrank_map_eq (y : S.Qt ≃ₗ[ZMod 2] S.Qt)
    (commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
  rw [← hconj] at hdimy
  have ht0 : 1 ≤ finrank (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
    one_le_finrank_commSpace fun h => ht1 (Subtype.ext h)
  omega

theorem false_of_fix_clSub_inf_Wt (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {x : S.O} (hxM : x ∈ S.Mbar)
    (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hinf : Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (hτP : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t,
      ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) : False := by
  have haQ := H.conj_mem
  have hτM : x * t * x⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hτV := fix_Vt_of_inf_eq_bot H hτM hτt hinf
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hc := fun l (hl : l ∈ S.Lbar g) =>
    comm_mem_zpowers_of_fix H C ht ht1 hVQ hτM hτV hτP hl
  have hcl : ∀ l ∈ S.Lbar g, (x * t * x⁻¹) * l = l * (x * t * x⁻¹) := by
    intro l hl
    rcases S8.eq_one_or_eq_of_mem_zpowers htt (hc l hl) with h1 | h1
    · calc (x * t * x⁻¹) * l = ((x * t * x⁻¹) * l * (x * t * x⁻¹)⁻¹ * l⁻¹) * l *
          (x * t * x⁻¹) := by group
        _ = l * (x * t * x⁻¹) := by rw [h1, one_mul]
    · exfalso
      have hlt : l * t = t * l := Lbar_comm S haQ hl ht
      refine not_conj_mul_t_of_inf_eq_bot H C ht ht1 hVQ hinf hτV (y := l⁻¹) ?_
      calc l⁻¹ * (x * t * x⁻¹) * l⁻¹⁻¹ =
          l⁻¹ * ((x * t * x⁻¹) * l * (x * t * x⁻¹)⁻¹ * l⁻¹) * l * (x * t * x⁻¹) := by group
        _ = l⁻¹ * t * l * (x * t * x⁻¹) := by rw [h1]
        _ = t * (x * t * x⁻¹) := by rw [mul_assoc l⁻¹, ← hlt]; group
        _ = x * t * x⁻¹ * t := hτt.symm
  have hτL := mem_Lbar_of_commute H C ht hxM fun l hl => hcl l hl
  have hτ1 : x * t * x⁻¹ ≠ 1 := fun h1 => ht1 (by
    calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group)
  have haV : S.cl (g * S.z * g⁻¹) ∈ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    by_contra hna
    apply hτ1
    refine C.faithful _ hτL fun v hv => ?_
    rcases mem_span_cl_iff.mp (Lbar_apply_sub_mem_span' haQ hv hτL) with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd (h0 ▸ sub_mem_commSpace _ v) hna
  have hmem : S.cl (g * S.z * g⁻¹) ∈
      Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨cl_a_mem_Vt ht, haV⟩
  rw [hinf, Submodule.mem_bot] at hmem
  exact cl_conj_z_ne_zero S haQ H.conj_ne hmem

end CFSG.LargeExtraspecial.S9
