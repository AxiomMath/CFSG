module

public import CFSG.LargeExtraspecial.S4FiveL
public import CFSG.LargeExtraspecial.S4FiveA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] noncomputable def Wt (g : G) (t : S.O) : Submodule (ZMod 2) S.Qt :=
  LinearMap.BilinForm.orthogonal S.q.polarBilin (Vt S g t)

theorem mem_Wt {t : S.O} {v : S.Qt} : v ∈ Wt S g t ↔ ∀ u ∈ Vt S g t, polar S.q u v = 0 := by
  simp [Wt, LinearMap.BilinForm.mem_orthogonal_iff, polarBilin_apply_apply]

theorem clSub_W {t : S.O} : S.clSub (W S g t) = Wt S g t := by
  rw [W, S.centralizer_inf_QG_eq_clPre V_le_QG, clSub_V, S.clSub_clPre]
  rfl

theorem W_eq_clPre {t : S.O} : W S g t = S.clPre (Wt S g t) := by
  rw [W, S.centralizer_inf_QG_eq_clPre V_le_QG, clSub_V]
  rfl

theorem finrank_Wt {t : S.O} :
    finrank (ZMod 2) (Wt S g t) + finrank (ZMod 2) (Vt S g t) = finrank (ZMod 2) S.Qt := by
  have := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate (Vt S g t)
  rw [Wt]
  have h2 := Submodule.finrank_le (Vt S g t)
  omega

theorem Vt_le_Wt (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1) : Vt S g t ≤ Wt S g t :=
  fun _ hv => mem_Wt.mpr fun _ hu => polar_eq_zero_of_mem_Vt H ht1 hu hv

theorem apply_mem_Wt (H : Hyp4 S g) {t x : S.O} (hx : x ∈ Rbar S g t) {v : S.Qt}
    (hv : v ∈ Wt S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Wt S g t := by
  rw [mem_Wt] at hv ⊢
  intro u hu
  have hu' := apply_mem_Vt_of_mem_Rbar H.conj_mem (inv_mem hx) hu
  have := hv _ hu'
  rwa [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2, apply_inv_apply_O] at this

variable (S) in
@[expose] noncomputable def Wt1 (g : G) (t : S.O) : Submodule (ZMod 2) S.Qt :=
  Wt S g t ⊓ ⨅ x : Rbar S g t,
    (S.clSub (S.QG ⊓ S.Qa g)).map ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap

theorem mem_Wt1 {t : S.O} {v : S.Qt} : v ∈ Wt1 S g t ↔ v ∈ Wt S g t ∧
    ∀ x ∈ Rbar S g t, (((x⁻¹ : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  rw [Wt1, Submodule.mem_inf, Submodule.mem_iInf]
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h x => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := h ⟨x, hx⟩
    simpa [inv_apply_apply_O] using hw
  · exact ⟨_, h x x.2, apply_inv_apply_O _ _⟩

theorem apply_mem_Wt1 (H : Hyp4 S g) {t x : S.O} (hx : x ∈ Rbar S g t) {v : S.Qt}
    (hv : v ∈ Wt1 S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Wt1 S g t := by
  rw [mem_Wt1] at hv ⊢
  refine ⟨apply_mem_Wt H hx hv.1, fun y hy => ?_⟩
  have := hv.2 (x⁻¹ * y) (mul_mem (inv_mem hx) hy)
  rwa [mul_inv_rev, inv_inv, coe_mul_apply] at this

theorem V_le_Qa_iff (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) {t : S.O} :
    V S g t ≤ S.Qa g ↔ Vt S g t ≤ S.clSub (S.QG ⊓ S.Qa g) := by
  constructor
  · exact Vt_le_clSub_of_V_le
  · intro h x hx
    have hz : S.z ∈ S.QG ⊓ S.Qa g := ⟨S.z_mem_QG, S.z_mem_Qa_of_mem_QG rfl haQ hne⟩
    have := S.clPre_mono h hx
    rw [S.clPre_clSub inf_le_left hz] at this
    exact this.2

theorem Wt1_eq_bot (H : Hyp4 S g) {t : S.O} (hVQ : ¬ V S g t ≤ S.Qa g) :
    Wt1 S g t = ⊥ := by
  by_contra hne
  apply hVQ
  rw [V_le_Qa_iff H.conj_mem H.conj_ne]
  refine (Vt_le_of_invariant H hne fun x hx v hv => apply_mem_Wt1 H hx hv).trans fun v hv => ?_
  have := (mem_Wt1.mp hv).2 1 (one_mem _)
  simpa using this

theorem mem_W_inf_Qa_mul (H : Hyp4 S g) {t : S.O} (hVQ : ¬ V S g t ≤ S.Qa g) {x : G}
    (hxW : x ∈ W S g t)
    (hx : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x ∈ S.Qa ((k : G) * g)) : x = 1 ∨ x = S.z := by
  have hxQ : x ∈ S.QG := hxW.1
  rw [← S.cl_eq_zero_iff hxQ]
  have hmem : S.cl x ∈ Wt1 S g t := by
    rw [mem_Wt1]
    refine ⟨clSub_W (S := S) ▸ S.cl_mem_clSub hxW hxQ, fun y hy => ?_⟩
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hy)
    have hxk := hx k hy
    rw [← map_inv, S.ρ_cl k⁻¹ hxQ]
    refine S.cl_mem_clSub ⟨S.conj_mem_QG (k⁻¹).2 hxQ, ?_⟩ (S.conj_mem_QG (k⁻¹).2 hxQ)
    rw [mem_Qa_mul_iff] at hxk
    simpa using hxk
  rw [Wt1_eq_bot H hVQ, Submodule.mem_bot] at hmem
  exact hmem

theorem inv_apply_t_sub_mem (H : Hyp4 S g) (H11 : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    {v : S.Qt} (hv : v ∈ Wt S g t) {x : S.O} (hx : x ∈ Rbar S g t) :
    ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hx)
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hx
  obtain ⟨w, hwQ, rfl⟩ := S.exists_cl v
  have hwW : w ∈ W S g t := by rw [W_eq_clPre]; exact ⟨hwQ, hv⟩
  have hbV := conj_mem_V H htk
  have hwb : w ∈ S.QG ⊓ centralizer ({(k : G) * g * S.z * ((k : G) * g)⁻¹} : Set G) :=
    ⟨hwQ, mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hwW.2) _ hbV).symm⟩
  have h1 := (Cons311.mul H11 k).comm_le w hwb t htk
  rw [QG_inf_Qa_mul k, mem_clSub_map_conj_iff k inf_le_left] at h1
  exact h1

theorem t_apply_of_mem_Wt (H : Hyp4 S g) (H11 : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hVQ : ¬ V S g t ≤ S.Qa g) {v : S.Qt} (hv : v ∈ Wt S g t) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have hmem : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Wt1 S g t := by
    rw [mem_Wt1]
    refine ⟨Submodule.sub_mem _ (apply_mem_Wt H (Lbar_le_Rbar ht ht) hv) hv,
      fun x hx => inv_apply_t_sub_mem H H11 ht hv hx⟩
  rw [Wt1_eq_bot H hVQ, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

theorem apply_mem_commSpace_t (H : Hyp4 S g) {t x : S.O} (hx : x ∈ Rbar S g t) {v : S.Qt}
    (hv : v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  refine mem_commSpace.mpr ⟨(x : S.Qt ≃ₗ[ZMod 2] S.Qt) w, ?_⟩
  rw [map_sub, ← coe_mul_apply, ← coe_mul_apply, commute_of_mem_Rbar H.conj_mem hx]

theorem commSpace_t_eq (H : Hyp4 S g) (H11 : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) :
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t ∧
      fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Wt S g t := by
  have hne : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ ⊥ := by
    intro h
    have := one_le_finrank_commSpace (g := (t : S.Qt ≃ₗ[ZMod 2] S.Qt))
      (fun h1 => ht1 (Subtype.ext h1))
    rw [h, finrank_bot] at this
    omega
  have hVle : Vt S g t ≤ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    Vt_le_of_invariant H hne fun x hx v hv => apply_mem_commSpace_t H hx hv
  have hWle : Wt S g t ≤ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := fun v hv =>
    mem_fixSpace.mpr (t_apply_of_mem_Wt H H11 ht hVQ hv)
  have h1 := finrank_commSpace_add_finrank_fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have h2 := finrank_Wt (S := S) (g := g) (t := t)
  have h3 := Submodule.finrank_mono hVle
  have h4 := Submodule.finrank_mono hWle
  constructor
  · exact (Submodule.eq_of_le_of_finrank_le hVle (by omega)).symm
  · exact (Submodule.eq_of_le_of_finrank_le hWle (by omega)).symm

theorem isTypeA_t (H : Hyp4 S g) (H11 : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) :
    IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (finrank (ZMod 2) (Vt S g t)) := by
  obtain ⟨hc, -⟩ := commSpace_t_eq H H11 ht ht1 hVQ
  refine ⟨fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup t.2 v,
    fun h => ht1 (Subtype.ext h), ?_, by rw [hc], fun v hv => ?_⟩
  · have := mul_self_of_mem_Lbar S H.conj_mem ht
    exact congrArg Subtype.val this
  · rw [hc] at hv
    exact q_eq_zero_of_mem_Vt H ht1 hv

theorem Nbar_apply_sub_mem_Wt (H : Hyp4 S g) (H11 : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {x : S.O} (hx : x ∈ Nbar S g t) (v : S.Qt) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Wt S g t := by
  rw [← (commSpace_t_eq H H11 ht ht1 hVQ).2, mem_fixSpace]
  have htv : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t := by
    rw [← (commSpace_t_eq H H11 ht ht1 hVQ).1]
    exact sub_mem_commSpace _ v
  have hxt : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
    rw [← coe_mul_apply, ← coe_mul_apply, commute_of_mem_Rbar H.conj_mem hx.1]
  have h1 := hx.2 _ htv
  rw [map_sub, hxt] at h1
  rw [map_sub]
  calc (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) -
        (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) -
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) + ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v -
          (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by abel
    _ = ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) + ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v -
          (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by rw [h1]
    _ = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v := by abel

@[expose] noncomputable def chi (H : Hyp4 S g) (H11 : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) :
    (S.Qt ⧸ Wt S g t) ≃ₗ[ZMod 2] Vt S g t :=
  (Submodule.quotEquivOfEq _ _ (commSpace_t_eq H H11 ht ht1 hVQ).2).symm.trans
    ((LinearMap.quotKerEquivRange ((t : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)).trans
      (LinearEquiv.ofEq _ _ (commSpace_t_eq H H11 ht ht1 hVQ).1))

theorem coe_chi_apply_mk (H : Hyp4 S g) (H11 : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (v : S.Qt) :
    ((chi H H11 ht ht1 hVQ (Submodule.Quotient.mk v) : Vt S g t) : S.Qt) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v :=
  rfl

theorem chi_equivariant (H : Hyp4 S g) (H11 : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (x : Rbar S g t) (v : S.Qt) :
    chi H H11 ht ht1 hVQ (Submodule.Quotient.mk (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) =
      resV H.conj_mem t x (chi H H11 ht ht1 hVQ (Submodule.Quotient.mk v)) := by
  apply Subtype.ext
  rw [coe_chi_apply_mk, coe_resV_apply, coe_chi_apply_mk, map_sub, ← coe_mul_apply,
    ← coe_mul_apply, commute_of_mem_Rbar H.conj_mem x.2]

end CFSG.LargeExtraspecial.S4
