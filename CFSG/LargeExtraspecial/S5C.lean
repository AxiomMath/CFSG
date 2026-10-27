module

public import CFSG.LargeExtraspecial.S4FiveW

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem inv_apply_sub_mem_of_forall (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) {τ : S.O}
    (hτD : ∀ k : S.M, S.ρ k ∈ Rbar S g t → τ ∈ S.Lbar ((k : G) * g))
    {v : S.Qt} (hv : v ∈ Wt S g t) {x : S.O} (hx : x ∈ Rbar S g t) :
    ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hx)
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hx
  have hτk := hτD k hx
  obtain ⟨w, hwQ, rfl⟩ := S.exists_cl v
  have hwW : w ∈ W S g t := by rw [W_eq_clPre]; exact ⟨hwQ, hv⟩
  have hbV := conj_mem_V H htk
  have hwb : w ∈ S.QG ⊓ centralizer ({(k : G) * g * S.z * ((k : G) * g)⁻¹} : Set G) :=
    ⟨hwQ, mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hwW.2) _ hbV).symm⟩
  have h1 := (Cons311.mul C k).comm_le w hwb τ hτk
  rw [QG_inf_Qa_mul k, mem_clSub_map_conj_iff k inf_le_left] at h1
  exact h1

theorem apply_eq_of_mem_Wt_of_forall (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (hVQ : ¬ V S g t ≤ S.Qa g) {τ : S.O} (hτL : τ ∈ S.Lbar g)
    (hτD : ∀ k : S.M, S.ρ k ∈ Rbar S g t → τ ∈ S.Lbar ((k : G) * g))
    {v : S.Qt} (hv : v ∈ Wt S g t) :
    (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have hmem : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Wt1 S g t := by
    rw [mem_Wt1]
    exact ⟨Submodule.sub_mem _ (apply_mem_Wt H (Lbar_le_Rbar ht hτL) hv) hv,
      fun x hx => inv_apply_sub_mem_of_forall H C ht hτD hv hx⟩
  rw [Wt1_eq_bot H hVQ, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

theorem eq_one_or_eq_of_forall (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {τ : S.O}
    (hτL : τ ∈ S.Lbar g) (hτD : ∀ k : S.M, S.ρ k ∈ Rbar S g t → τ ∈ S.Lbar ((k : G) * g))
    (hXorb : ∀ r ∈ Rbar S g t, ∃ x ∈ Rbar S g t, x * τ = τ * x ∧
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) :
    τ = 1 ∨ τ = t := by
  have haQ := H.conj_mem
  obtain ⟨hcomm, hfix⟩ := commSpace_t_eq H C ht ht1 hVQ
  set T : S.Qt ≃ₗ[ZMod 2] S.Qt := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hT
  set U : S.Qt ≃ₗ[ZMod 2] S.Qt := (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hU
  have hUW : ∀ v ∈ Wt S g t, U v = v := fun v hv =>
    apply_eq_of_mem_Wt_of_forall H C ht hVQ hτL hτD hv
  have hTW : ∀ v, T v = v → U v = v := fun v hv =>
    hUW v (hfix ▸ mem_fixSpace.mpr hv)
  obtain ⟨y', hy'⟩ : ∃ y', T y' - y' = S.cl (g * S.z * g⁻¹) := by
    have : S.cl (g * S.z * g⁻¹) ∈ commSpace T := by rw [hcomm]; exact cl_a_mem_Vt ht
    exact mem_commSpace.mp this
  have hu : U y' - y' ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    rw [← H.fixSub_eq]
    intro l hl
    have hla : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
      (mem_fixSub S).mp (by rw [H.fixSub_eq]; exact Submodule.mem_span_singleton_self _) l hl
    have hlt : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (T y') = T ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) y') := by
      rw [hT, ← coe_mul_apply, ← coe_mul_apply, Lbar_comm S haQ hl ht]
    have hlτ : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (U y') = U ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) y') := by
      rw [hU, ← coe_mul_apply, ← coe_mul_apply, Lbar_comm S haQ hl hτL]
    have hd : T ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) y' - y') = (l : S.Qt ≃ₗ[ZMod 2] S.Qt) y' - y' := by
      rw [map_sub, ← hlt, show T y' = y' + S.cl (g * S.z * g⁻¹) by rw [← hy']; abel, map_add,
        hla]
      abel
    have hd' := hTW _ hd
    rw [map_sub, ← hlτ] at hd'
    rw [map_sub, hlτ]
    calc U ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) y') - (l : S.Qt ≃ₗ[ZMod 2] S.Qt) y'
        = (U ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) y') - U y') + (U y' - y') -
            ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) y' - y') := by abel
      _ = U y' - y' := by rw [← hlτ, hd']; abel
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
  let K : Submodule (ZMod 2) S.Qt :=
    { carrier := {x | U x - x = c • (T x - x)}
      add_mem' := by
        intro x y hx hy
        change U x - x = c • (T x - x) at hx
        change U y - y = c • (T y - y) at hy
        change U (x + y) - (x + y) = c • (T (x + y) - (x + y))
        rw [map_add, map_add, show U x + U y - (x + y) = (U x - x) + (U y - y) by abel, hx, hy,
          show T x + T y - (x + y) = (T x - x) + (T y - y) by abel, smul_add]
      zero_mem' := by
        change U 0 - 0 = c • (T 0 - 0)
        rw [map_zero, map_zero, sub_zero, smul_zero]
      smul_mem' := by
        intro d x hx
        change U x - x = c • (T x - x) at hx
        change U (d • x) - d • x = c • (T (d • x) - d • x)
        rw [map_smul, map_smul, ← smul_sub, hx, ← smul_sub, smul_comm] }
  have hKW : ∀ v, T v = v → v ∈ K := fun v hv => by
    change U v - v = c • (T v - v)
    rw [hTW v hv, hv, sub_self, smul_zero]
  have hKr : ∀ x ∈ Rbar S g t, x * τ = τ * x → (x : S.Qt ≃ₗ[ZMod 2] S.Qt) y' ∈ K := by
    intro x hx hxτ
    change U _ - _ = c • (T _ - _)
    have hxt : T ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) y') = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (T y') := by
      rw [hT, ← coe_mul_apply, ← coe_mul_apply, commute_of_mem_Rbar haQ hx]
    have hxτ' : U ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) y') = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (U y') := by
      rw [hU, ← coe_mul_apply, ← coe_mul_apply, hxτ]
    rw [hxt, hxτ', ← map_sub, ← map_sub, hy', ← hc, map_smul]
  have hKtop : ∀ x, x ∈ K := by
    intro x
    set f : S.Qt →ₗ[ZMod 2] S.Qt := T.toLinearMap - LinearMap.id with hf
    have hVle : Vt S g t ≤ K.map f := by
      rw [Vt_eq_span_orbit H ht, Submodule.span_le]
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨x, hx, hxτ, hxr⟩ := hXorb r hr
      refine ⟨_, hKr x hx hxτ, ?_⟩
      change T ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) y') - (x : S.Qt ≃ₗ[ZMod 2] S.Qt) y' = _
      have hxt : T ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) y') = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (T y') := by
        rw [hT, ← coe_mul_apply, ← coe_mul_apply, commute_of_mem_Rbar haQ hx]
      rw [hxt, ← map_sub, hy', hxr]
    have hfx : f x ∈ Vt S g t := by
      rw [← hcomm]
      exact sub_mem_commSpace _ x
    obtain ⟨k, hk, hkx⟩ := hVle hfx
    have hxk : T (x - k) = x - k := by
      have : f (x - k) = 0 := by rw [map_sub, hkx, sub_self]
      rw [hf, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
      exact this
    have := K.add_mem hk (hKW _ hxk)
    rwa [add_sub_cancel] at this
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl
  · left
    refine Subtype.ext (LinearEquiv.ext fun x => ?_)
    have := hKtop x
    change U x - x = (0 : ZMod 2) • (T x - x) at this
    rw [zero_smul, sub_eq_zero] at this
    exact this
  · right
    refine Subtype.ext (LinearEquiv.ext fun x => ?_)
    have := hKtop x
    change U x - x = (1 : ZMod 2) • (T x - x) at this
    rw [one_smul, sub_left_inj] at this
    exact this

end CFSG.LargeExtraspecial.S5
