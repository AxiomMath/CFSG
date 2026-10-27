module

public import CFSG.LargeExtraspecial.GLW4RhoLift
public import CFSG.LargeExtraspecial.GLW4MatB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module Matrix QuadraticMap CFSG.LargeExtraspecial.GLR CFSG.GH74.GLS.Bg.Thompson

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

@[expose] def sqSub (T : Subgroup G) : Subgroup G := closure {g | ∃ t ∈ T, t * t = g}

omit [Finite G] in
theorem sq_mem_sqSub {T : Subgroup G} {t : G} (ht : t ∈ T) : t * t ∈ sqSub T :=
  subset_closure ⟨t, ht, rfl⟩

omit [Finite G] in
theorem conj_mem_sqSub {T : Subgroup G} {s : G} (hs : s ∈ normalizer T) {w : G}
    (hw : w ∈ sqSub T) : s * w * s⁻¹ ∈ sqSub T := by
  have hle : sqSub T ≤ (sqSub T).comap (MulAut.conj s).toMonoidHom := by
    rw [sqSub, closure_le]
    rintro _ ⟨t, ht, rfl⟩
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      show s * (t * t) * s⁻¹ = (s * t * s⁻¹) * (s * t * s⁻¹) by group]
    exact sq_mem_sqSub ((mem_normalizer_iff.mp hs t).mp ht)
  have := hle hw
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem isoN_of_commute (e : Basis (Fin 4) (ZMod 2) C.At) {τ : G} (hτM : τ ∈ S.M)
    (hN : gram C e (S.ρ ⟨τ, hτM⟩) = N) {t : G} (ht : t ∈ C.X) (htτ : t * τ = τ * t) :
    IsoN (matX C e (C.xbarHom ⟨t, ht⟩)) := by
  set y := C.xbarHom ⟨t, ht⟩
  have hy : (y : S.O) = S.ρ ⟨t, C.X_le_M ht⟩ := C.xbarHom_coe _
  have h1 : S.ρ ⟨t, C.X_le_M ht⟩ * S.ρ ⟨τ, hτM⟩ = S.ρ ⟨τ, hτM⟩ * S.ρ ⟨t, C.X_le_M ht⟩ := by
    rw [← ρ_mul (C.X_le_M ht) hτM, ← ρ_mul hτM (C.X_le_M ht)]
    congr 1
    exact Subtype.ext htτ
  have hc : (y : S.O) * S.ρ ⟨τ, hτM⟩ * (y : S.O)⁻¹ = S.ρ ⟨τ, hτM⟩ := by
    rw [hy, h1, mul_inv_cancel_right]
  have h2 := gram_conj e (S.ρ ⟨τ, hτM⟩) y
  rw [hc, hN] at h2
  exact IsoN.of_inv h2.symm (by rw [← matX_mul, mul_inv_cancel, matX_one])

theorem sq_mem_K₀ (e : Basis (Fin 4) (ZMod 2) C.At) {τ : G} (hτM : τ ∈ S.M) (hτX : τ ∉ C.X)
    (hττ : τ * τ = 1) (hN : gram C e (S.ρ ⟨τ, hτM⟩) = N) {t : G} (htM : t ∈ S.M)
    (htτ : t * τ = τ * t) : ∃ h : t * t ∈ C.X, InK₀ (matX C e (C.xbarHom ⟨t * t, h⟩)) := by
  obtain ⟨t', ht'X, ht'τ, htt⟩ : ∃ t', t' ∈ C.X ∧ t' * τ = τ * t' ∧ t' * t' = t * t := by
    by_cases ht : t ∈ C.X
    · exact ⟨t, ht, htτ, rfl⟩
    · refine ⟨τ * t, (C.mul_mem_X_iff hτM htM).mpr (iff_of_false hτX ht), ?_, ?_⟩
      · rw [mul_assoc, htτ]
      · calc τ * t * (τ * t) = τ * (t * τ) * t := by group
          _ = τ * τ * (t * t) := by rw [htτ]; group
          _ = t * t := by rw [hττ, one_mul]
  have hX : t * t ∈ C.X := htt ▸ C.X.mul_mem ht'X ht'X
  refine ⟨hX, ?_⟩
  have h1 : C.xbarHom ⟨t * t, hX⟩ = C.xbarHom ⟨t', ht'X⟩ * C.xbarHom ⟨t', ht'X⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext htt.symm
  rw [h1, matX_mul]
  exact (isoN_of_commute e hτM hN ht'X ht'τ).sq_mem
    ⟨matX C e (C.xbarHom ⟨t', ht'X⟩)⁻¹, by rw [← matX_mul, inv_mul_cancel, matX_one]⟩

theorem sqSub_mem_K₀ (e : Basis (Fin 4) (ZMod 2) C.At) {τ : G} (hτM : τ ∈ S.M) (hτX : τ ∉ C.X)
    (hττ : τ * τ = 1) (hN : gram C e (S.ρ ⟨τ, hτM⟩) = N) {T : Subgroup G} (hTM : T ≤ S.M)
    (hTC : T ≤ centralizer {τ}) {w : G} (hw : w ∈ sqSub T) :
    ∃ h : w ∈ C.X, InK₀ (matX C e (C.xbarHom ⟨w, h⟩)) := by
  induction hw using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    exact sq_mem_K₀ e hτM hτX hττ hN (hTM ht) (mem_centralizer_singleton_iff.mp (hTC ht))
  | inv_mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    rw [_root_.mul_inv_rev]
    exact sq_mem_K₀ e hτM hτX hττ hN (hTM (T.inv_mem ht))
      (mem_centralizer_singleton_iff.mp (hTC (T.inv_mem ht)))
  | one =>
    refine ⟨C.X.one_mem, ?_⟩
    rw [show C.xbarHom ⟨1, C.X.one_mem⟩ = 1 from map_one _, matX_one]
    intro v hv
    rwa [one_mulVec]
  | mul x y _ _ hx hy =>
    obtain ⟨hxX, hxK⟩ := hx
    obtain ⟨hyX, hyK⟩ := hy
    refine ⟨C.X.mul_mem hxX hyX, ?_⟩
    have h1 : C.xbarHom ⟨x * y, C.X.mul_mem hxX hyX⟩ = C.xbarHom ⟨x, hxX⟩ * C.xbarHom ⟨y, hyX⟩ := by
      rw [← map_mul]
      exact congrArg C.xbarHom (Subtype.ext rfl)
    rw [h1, matX_mul]
    exact hxK.mul hyK

theorem mem_QG_of_K₀ (e : Basis (Fin 4) (ZMod 2) C.At) {τ : G} (hτM : τ ∈ S.M) (hτX : τ ∉ C.X)
    (hττ : τ * τ = 1) (hN : gram C e (S.ρ ⟨τ, hτM⟩) = N) {x : G} (hx : x ∈ C.X)
    (hK : InK₀ (matX C e (C.xbarHom ⟨x, hx⟩)))
    (hxc : ∀ q ∈ S.QG, τ * q = q * τ → x * q = q * x) : x ∈ S.QG := by
  have hsM : S.ρ ⟨τ, hτM⟩ ∈ S.Mbar := Config.ρ_mem_Mbar _
  have hsX := Config.ρ_not_mem_Xbar hτM hτX
  have hxM := C.X_le_M hx
  set y := C.xbarHom ⟨x, hx⟩ with hy
  have hyc : (y : S.O) = S.ρ ⟨x, hxM⟩ := C.xbarHom_coe _
  have hfix : ∀ j : Fin 4, N j j = 0 → C.resAt y (e j) = e j := by
    intro j hj
    have haa : C.formOf (S.ρ ⟨τ, hτM⟩) (e j) (e j) = 0 := by
      have := congrFun (congrFun hN j) j
      rw [hj] at this
      exact this
    obtain ⟨q, hq, hqτ, hcl⟩ :=
      Config.exists_mem_centralizer_cl_eq hτM hτX (Or.inl hττ) (e j).2 haa
    have h1 : ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) = S.cl q := by
      rw [hyc, ← Config.cl_conj hxM hq, hxc q hq hqτ, mul_inv_cancel_right]
    rw [hcl, map_add] at h1
    have hsa := C.apply_mem_Bt_of_not_mem hsM hsX (e j).2
    exact Subtype.ext
      (C.eq_of_add_eq (C.apply_At _ y.2 _ (e j).2) (e j).2 (C.apply_Bt _ y.2 _ hsa) hsa h1).1
  have hcol : ∀ j : Fin 4, N j j = 0 → matX C e y *ᵥ Pi.single j 1 = Pi.single j 1 := by
    intro j hj
    ext i
    rw [mulVec_single_apply, matX, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hfix j hj,
      Basis.repr_self, Finsupp.single_eq_pi_single]
  have hg := hK.eq_one_of_fix (hcol 0 (by decide)) (hcol 1 (by decide)) (hcol 3 (by decide))
  have hy1 : y = 1 := matX_injective e (by rw [hg, matX_one])
  refine (S.ρ_eq_one_iff ⟨x, hxM⟩).mp ?_
  rw [← hyc, hy1]
  rfl

theorem sylowIn_centralizer_N (e : Basis (Fin 4) (ZMod 2) C.At) {τ : G} (hτM : τ ∈ S.M)
    (hτX : τ ∉ C.X) (hττ : τ * τ = 1) (hN : gram C e (S.ρ ⟨τ, hτM⟩) = N) {T : Subgroup G}
    (hT : IsSylowIn 2 T (centralizer {τ} ⊓ S.M)) {σ : G} (hσT : σ ∈ T) (hσσ : σ * σ = S.z) :
    IsSylowIn 2 T (centralizer {τ}) := by
  refine SylowIn.of_normalizer hT inf_le_left fun P hP _ s hsP hsN => ?_
  have hsC : s ∈ centralizer {τ} := hP hsP
  have hTM : T ≤ S.M := fun t ht => (SylowIn.le hT ht).2
  have hTC : T ≤ centralizer {τ} := fun t ht => (SylowIn.le hT ht).1
  have hsT' : ∀ t ∈ T, s⁻¹ * t * s ∈ T := fun t ht => by
    have := (mem_normalizer_iff.mp (inv_mem hsN) t).mp ht
    rwa [inv_inv] at this
  have hw : s * S.z * s⁻¹ ∈ sqSub T := conj_mem_sqSub hsN (hσσ ▸ sq_mem_sqSub hσT)
  have hwc : ∀ t ∈ T, (s * S.z * s⁻¹) * t = t * (s * S.z * s⁻¹) := by
    intro t ht
    have h1 := S.z_comm (hTM (hsT' t ht))
    calc s * S.z * s⁻¹ * t = s * (S.z * (s⁻¹ * t * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * t * s) * S.z) * s⁻¹ := by rw [h1]
      _ = t * (s * S.z * s⁻¹) := by group
  obtain ⟨hwX, hwK⟩ := sqSub_mem_K₀ e hτM hτX hττ hN hTM hTC hw
  have hwQ : s * S.z * s⁻¹ ∈ S.QG := mem_QG_of_K₀ e hτM hτX hττ hN hwX hwK
    fun q hq hqτ => hwc q (Levi.centralizer_QG_le hT
      ⟨hq, mem_centralizer_singleton_iff.mpr hqτ.symm⟩)
  have hτT := Levi.mem_of_sylowIn hτM hττ hT
  have hwz := Config.conj_eq_z_of_commute hτM hτX hwQ (hwc τ hτT).symm
  refine ⟨hsC, S.mem_M_iff.mpr ?_⟩
  calc s * S.z = s * S.z * s⁻¹ * s := by group
    _ = S.z * s := by rw [hwz]

end CFSG.LargeExtraspecial.GLW4
