module

public import CFSG.LargeExtraspecial.S10Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Natural

variable {U U' : Type*} [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup U']
  [Module (ZMod 2) U'] {Q : QuadraticForm (ZMod 2) U} {Q' : QuadraticForm (ZMod 2) U'}
  {κ : U ≃ₗ[ZMod 2] U'} (hκ : ∀ u, Q' (κ u) = Q u)
include hκ

theorem polar_kappa (u v : U) : polar Q' (κ u) (κ v) = polar Q u v := by
  simp only [polar, ← map_add, hκ]

theorem mem_omegaGroup_iff_autCongr' [FiniteDimensional (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U'] (hQ : Q.polarBilin.Nondegenerate)
    (hQ' : Q'.polarBilin.Nondegenerate) (g : U ≃ₗ[ZMod 2] U) :
    g ∈ omegaGroup Q hQ ↔ LinearEquiv.autCongr κ g ∈ omegaGroup Q' hQ' := by
  have hc : commSpace (LinearEquiv.autCongr κ g) = (commSpace g).map κ.toLinearMap := by
    ext m
    rw [mem_commSpace, Submodule.mem_map]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨g (κ.symm v) - κ.symm v, sub_mem_commSpace g _, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
      exact ⟨κ v, by simp⟩
  rw [mem_omegaGroup, mem_omegaGroup, hc, LinearEquiv.finrank_map_eq,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  refine and_congr_left fun _ => ⟨fun h m => ?_, fun h u => ?_⟩
  · rw [LinearEquiv.autCongr_apply_apply, hκ, h, ← hκ, LinearEquiv.apply_symm_apply]
  · have := h (κ u)
    rwa [LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_apply_apply, hκ, hκ] at this

theorem mem_pointRadical_iff_autCongr (a : U) (g : U ≃ₗ[ZMod 2] U) :
    g ∈ pointRadical Q a ↔ LinearEquiv.autCongr κ g ∈ pointRadical Q' (κ a) := by
  rw [mem_pointRadical, mem_pointRadical, TauCeti.QuadraticMap.mem_orthogonalGroup_iff,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  simp only [LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_apply_apply]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun m => ?_, by rw [h2], fun x hx => ?_, fun v => ?_⟩
    · rw [hκ, h1, ← hκ, LinearEquiv.apply_symm_apply]
    · have hx' : polar Q a (κ.symm x) = 0 := by
        rw [← polar_kappa hκ, LinearEquiv.apply_symm_apply]; exact hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h3 _ hx')
      refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
      rw [← map_smul, hc, map_sub, LinearEquiv.apply_symm_apply]
    · have := h4 (κ.symm v)
      rw [← polar_kappa hκ, map_sub, LinearEquiv.apply_symm_apply] at this
      exact this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun m => ?_, κ.injective h2, fun x hx => ?_, fun v => ?_⟩
    · have := h1 (κ m)
      rwa [LinearEquiv.symm_apply_apply, hκ, hκ] at this
    · have hx' : polar Q' (κ a) (κ x) = 0 := by rw [polar_kappa hκ]; exact hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h3 _ hx')
      refine Submodule.mem_span_singleton.mpr ⟨c, κ.injective ?_⟩
      rw [map_smul, hc, LinearEquiv.symm_apply_apply, map_sub]
    · have := h4 (κ v)
      rw [LinearEquiv.symm_apply_apply, ← map_sub, polar_kappa hκ] at this
      exact this

omit hκ in
theorem transport_omega_data [FiniteDimensional (ZMod 2) U] [FiniteDimensional (ZMod 2) U']
    (hQ : Q.polarBilin.Nondegenerate) {R L : Subgroup (U ≃ₗ[ZMod 2] U)} {a : U}
    (hR : R = omegaGroup Q hQ) (hL : L = pointRadical Q a)
    (hsing : ∀ v : U, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf R a))
    (hQ' : (Q.comp κ.symm.toLinearMap).polarBilin.Nondegenerate) :
    R.map (LinearEquiv.autCongr κ).toMonoidHom = omegaGroup (Q.comp κ.symm.toLinearMap) hQ' ∧
    L.map (LinearEquiv.autCongr κ).toMonoidHom = pointRadical (Q.comp κ.symm.toLinearMap) (κ a) ∧
    ∀ v : U', v ≠ 0 → ((Q.comp κ.symm.toLinearMap) v = 0 ↔
      v ∈ orbitOf (R.map (LinearEquiv.autCongr κ).toMonoidHom) (κ a)) := by
  have hκ' : ∀ u, (Q.comp κ.symm.toLinearMap) (κ u) = Q u := fun u => by simp
  refine ⟨?_, ?_, ?_⟩
  · ext e
    rw [hR, Subgroup.mem_map]
    constructor
    · rintro ⟨e', he', rfl⟩
      exact (mem_omegaGroup_iff_autCongr' hκ' hQ hQ' e').mp he'
    · intro he
      refine ⟨(LinearEquiv.autCongr κ).symm e, ?_, by simp⟩
      rw [mem_omegaGroup_iff_autCongr' hκ' hQ hQ']
      simpa using he
  · ext e
    rw [hL, Subgroup.mem_map]
    constructor
    · rintro ⟨e', he', rfl⟩
      exact (mem_pointRadical_iff_autCongr hκ' _ e').mp he'
    · intro he
      refine ⟨(LinearEquiv.autCongr κ).symm e, ?_, by simp⟩
      rw [mem_pointRadical_iff_autCongr hκ']
      simpa using he
  · intro v hv0
    have hv0' : κ.symm v ≠ 0 := fun h => hv0 (κ.symm.injective (h.trans (map_zero _).symm))
    have e1 : (Q.comp κ.symm.toLinearMap) v = Q (κ.symm v) := rfl
    rw [e1, hsing _ hv0']
    constructor
    · rintro ⟨e, he, hea⟩
      refine ⟨LinearEquiv.autCongr κ e, ⟨e, he, rfl⟩, ?_⟩
      simp [hea]
    · rintro ⟨_, ⟨e, he, rfl⟩, hea⟩
      refine ⟨e, he, ?_⟩
      rw [← hea]
      simp

end Natural

noncomputable abbrev cK (S : Setting G) (k : S.M) : S.O →* S.O :=
  (MulAut.conj (S.ρ k)).toMonoidHom

theorem cK_apply (k : S.M) (x : S.O) : cK S k x = S.ρ k * x * (S.ρ k)⁻¹ := rfl

theorem cK_injective (k : S.M) : Function.Injective (cK S k) := (MulAut.conj (S.ρ k)).injective

theorem mem_map_cK_iff (k : S.M) {X : Subgroup S.O} {x : S.O} :
    x ∈ X.map (cK S k) ↔ (S.ρ k)⁻¹ * x * S.ρ k ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨_, hx, by simp [mul_assoc]⟩

theorem Lbar_mul_map_cK (k h : S.M) :
    (S.Lbar ((h : G) * g)).map (cK S k) = S.Lbar (((k * h : S.M) : G) * g) := by
  rw [Subgroup.coe_mul, mul_assoc, Lbar_mul S k]

theorem Dset_conj (k : S.M) (t : S.O) :
    Dset S g (S.ρ k * t * (S.ρ k)⁻¹) = (fun X => X.map (cK S k)) '' Dset S g t := by
  ext X
  constructor
  · rintro ⟨h, rfl, hτ⟩
    refine ⟨S.Lbar (((k⁻¹ * h : S.M) : G) * g), ⟨k⁻¹ * h, rfl, ?_⟩, ?_⟩
    · rw [← Lbar_mul_map_cK]
      refine ⟨S.ρ k * t * (S.ρ k)⁻¹, hτ, ?_⟩
      simp [mul_assoc]
    · show (S.Lbar (((k⁻¹ * h : S.M) : G) * g)).map (cK S k) = _
      rw [Lbar_mul_map_cK, mul_inv_cancel_left]
  · rintro ⟨_, ⟨h, rfl, ht⟩, rfl⟩
    refine ⟨k * h, Lbar_mul_map_cK k h, ?_⟩
    show _ ∈ (S.Lbar ((h : G) * g)).map (cK S k)
    exact ⟨t, ht, rfl⟩

theorem Rbar_conj (k : S.M) (t : S.O) :
    Rbar S g (S.ρ k * t * (S.ρ k)⁻¹) = (Rbar S g t).map (cK S k) := by
  rw [Rbar, Rbar, Dset_conj, sSup_image, ← (Subgroup.gc_map_comap (cK S k)).l_sSup]

theorem Vt_conj (haQ : g * S.z * g⁻¹ ∈ S.QG) (k : S.M) (t : S.O) :
    Vt S g (S.ρ k * t * (S.ρ k)⁻¹) =
      (Vt S g t).map ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
  rw [Vt, Vt, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨h, hτ, rfl⟩
    refine ⟨S.cl (((k⁻¹ * h : S.M) : G) * g * S.z * (((k⁻¹ * h : S.M) : G) * g)⁻¹),
      ⟨k⁻¹ * h, ?_, rfl⟩, ?_⟩
    · rw [← Lbar_mul_map_cK]
      refine ⟨S.ρ k * t * (S.ρ k)⁻¹, hτ, ?_⟩
      simp [mul_assoc]
    · have e : (k : G) * (((k⁻¹ * h : S.M) : G) * g) = (h : G) * g := by
        simp [mul_assoc]
      change ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (((k⁻¹ * h : S.M) : G) * g * S.z *
        (((k⁻¹ * h : S.M) : G) * g)⁻¹)) = _
      rw [ρ_cl_conj_z S k (conj_mem_QG' S (k⁻¹ * h).2 haQ), e]
  · rintro ⟨_, ⟨h, ht, rfl⟩, rfl⟩
    refine ⟨k * h, ?_, ?_⟩
    · rw [← Lbar_mul_map_cK]
      exact ⟨t, ht, rfl⟩
    · have e : (k : G) * ((h : G) * g) = ((k * h : S.M) : G) * g := by
        simp [mul_assoc]
      change ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h : G) * g * S.z *
        ((h : G) * g)⁻¹)) = _
      rw [ρ_cl_conj_z S k (conj_mem_QG' S h.2 haQ), e]

theorem mem_Vt_conj (haQ : g * S.z * g⁻¹ ∈ S.QG) (k : S.M) {t : S.O} {v : S.Qt} :
    v ∈ Vt S g (S.ρ k * t * (S.ρ k)⁻¹) ↔
      (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t := by
  rw [Vt_conj haQ]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [inv_apply_apply_O] using hw
  · intro hv
    exact ⟨_, hv, by simp⟩

theorem Nbar_conj (haQ : g * S.z * g⁻¹ ∈ S.QG) (k : S.M) (t : S.O) :
    Nbar S g (S.ρ k * t * (S.ρ k)⁻¹) = (Nbar S g t).map (cK S k) := by
  ext x
  rw [mem_map_cK_iff, mem_Nbar, mem_Nbar, Rbar_conj, mem_map_cK_iff]
  refine and_congr_right fun _ => ⟨fun h v hv => ?_, fun h v hv => ?_⟩
  · have hmem : ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g (S.ρ k * t * (S.ρ k)⁻¹) :=
      (mem_Vt_conj haQ k).mpr (by rw [inv_apply_apply_O]; exact hv)
    have h1 := h _ hmem
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [h1, inv_apply_apply_O]
  · have h1 := h _ ((mem_Vt_conj haQ k).mp hv)
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at h1
    have := congrArg ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    simpa [apply_inv_apply_O] using this

section Tau

variable {t τ : S.O} {k : S.M}

theorem mem_Vt_conj' (haQ : g * S.z * g⁻¹ ∈ S.QG) (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹)
    {v : S.Qt} : v ∈ Vt S g τ ↔ (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t := by
  subst hτ
  exact mem_Vt_conj haQ k

@[expose] noncomputable def kappa (haQ : g * S.z * g⁻¹ ∈ S.QG) (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) :
    Vt S g t ≃ₗ[ZMod 2] Vt S g τ where
  toFun v := ⟨((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, (mem_Vt_conj' haQ hτ).mpr (by
    rw [inv_apply_apply_O]; exact v.2)⟩
  invFun v := ⟨(((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, (mem_Vt_conj' haQ hτ).mp v.2⟩
  map_add' v w := Subtype.ext (map_add _ _ _)
  map_smul' c v := Subtype.ext (map_smul _ _ _)
  left_inv v := Subtype.ext (inv_apply_apply_O _ _)
  right_inv v := Subtype.ext (apply_inv_apply_O _ _)

theorem coe_kappa (haQ : g * S.z * g⁻¹ ∈ S.QG) (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹)
    (v : Vt S g t) :
    ((kappa haQ hτ v : Vt S g τ) : S.Qt) = ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := rfl

theorem coe_kappa_symm (haQ : g * S.z * g⁻¹ ∈ S.QG) (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹)
    (v : Vt S g τ) :
    (((kappa haQ hτ).symm v : Vt S g t) : S.Qt) =
      (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := rfl

theorem RmodN_conj (haQ : g * S.z * g⁻¹ ∈ S.QG) (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) :
    RmodN S g τ = (RmodN S g t).map (LinearEquiv.autCongr (kappa haQ hτ)).toMonoidHom := by
  have hR : Rbar S g τ = (Rbar S g t).map (cK S k) := by subst hτ; exact Rbar_conj k t
  ext e
  constructor
  · rintro ⟨x, hx, hex⟩
    rw [hR, mem_map_cK_iff] at hx
    refine ⟨(LinearEquiv.autCongr (kappa haQ hτ)).symm e, ⟨_, hx, fun v => ?_⟩, by simp⟩
    rw [LinearEquiv.autCongr_symm_apply_apply, coe_kappa_symm, hex, coe_kappa]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
  · rintro ⟨e', ⟨x, hx, hex⟩, rfl⟩
    refine ⟨S.ρ k * x * (S.ρ k)⁻¹, ?_, fun v => ?_⟩
    · rw [hR]
      exact ⟨x, hx, rfl⟩
    · simp only [MulEquiv.coe_toMonoidHom, LinearEquiv.autCongr_apply_apply, coe_kappa, hex,
        coe_kappa_symm, Subgroup.coe_mul, LinearEquiv.mul_apply]

theorem LmodN_conj (haQ : g * S.z * g⁻¹ ∈ S.QG) (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹)
    (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) :
    LmodN S g τ = (LmodN S g t).map (LinearEquiv.autCongr (kappa haQ hτ)).toMonoidHom := by
  ext e
  constructor
  · rintro ⟨x, hx, hex⟩
    have hx' : (S.ρ k)⁻¹ * x * S.ρ k ∈ S.Lbar g := by
      have := (mem_normalizer_iff.mp (inv_mem hk) x).mp hx
      simpa using this
    refine ⟨(LinearEquiv.autCongr (kappa haQ hτ)).symm e, ⟨_, hx', fun v => ?_⟩, by simp⟩
    rw [LinearEquiv.autCongr_symm_apply_apply, coe_kappa_symm, hex, coe_kappa]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
  · rintro ⟨e', ⟨x, hx, hex⟩, rfl⟩
    refine ⟨S.ρ k * x * (S.ρ k)⁻¹, (mem_normalizer_iff.mp hk x).mp hx, fun v => ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, LinearEquiv.autCongr_apply_apply, coe_kappa, hex,
      coe_kappa_symm, Subgroup.coe_mul, LinearEquiv.mul_apply]

end Tau

section Normalizer

variable (H : Hyp4 S g) {k : S.M} (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O))
include H hk

theorem fix_cl_of_mem_normalizer :
    ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  have hmem : ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      fixSub S (S.Lbar g) := by
    intro s hs
    have hs' : (S.ρ k)⁻¹ * s * S.ρ k ∈ S.Lbar g := by
      have := (mem_normalizer_iff.mp (inv_mem hk) s).mp hs
      simpa using this
    have hfix : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar g) := by
      rw [H.fixSub_eq]; exact Submodule.mem_span_singleton_self _
    have h1 := hfix _ hs'
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at h1
    have := congrArg ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    simpa using this
  rw [H.fixSub_eq] at hmem
  rcases mem_span_cl_iff.mp hmem with h0 | h1
  · exfalso
    have : S.cl (g * S.z * g⁻¹) = 0 := by
      have := congrArg (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h0
      simpa [inv_apply_apply_O] using this
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne this
  · exact h1

omit H in
theorem mem_Lbar_conj {t τ : S.O} (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) (ht : t ∈ S.Lbar g) :
    τ ∈ S.Lbar g := by
  rw [hτ]; exact (mem_normalizer_iff.mp hk t).mp ht

theorem kappa_aV {t τ : S.O} (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) (ht : t ∈ S.Lbar g) :
    kappa H.conj_mem hτ (aV ht) = aV (mem_Lbar_conj hk hτ ht) :=
  Subtype.ext (fix_cl_of_mem_normalizer H hk)

theorem apply_mem_clSub_Qa_of_normalizer {v : S.Qt} (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g) :=
  apply_mem_clSub_of_fix H.conj_mem H.conj_ne (MonoidHom.mem_range.mpr ⟨k, rfl⟩)
    (fix_cl_of_mem_normalizer H hk) hv

end Normalizer

theorem beta_kappa (H : Hyp4 S g) (C : Cons311 S g) {t τ : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {k : S.M} (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹)
    (hτL : τ ∈ S.Lbar g) (hτ1 : τ ≠ 1) (hVQτ : ¬ V S g τ ≤ S.Qa g) (x y : Vt S g t) :
    beta H C hτL hτ1 hVQτ (kappa H.conj_mem hτ x) (kappa H.conj_mem hτ y) =
      beta H C ht ht1 hVQ x y := by
  obtain ⟨y', hy'⟩ := exists_t_sub_eq H C ht ht1 hVQ y
  have hy'' : ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y') - ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y' =
      ((kappa H.conj_mem hτ y : Vt S g τ) : S.Qt) := by
    rw [coe_kappa, ← hy', map_sub, hτ]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, inv_apply_apply_O]
  rw [beta_apply H C hτL hτ1 hVQτ _ _ hy'', beta_apply H C ht ht1 hVQ _ _ hy', coe_kappa]
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ k).2 _ _

theorem mem_orbitOf_conj (H : Hyp4 S g) {k : S.M} (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O))
    {t τ : S.O} (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) (ht : t ∈ S.Lbar g) (v : Vt S g τ) :
    v ∈ orbitOf (RmodN S g τ) (aV (mem_Lbar_conj hk hτ ht)) ↔
      (kappa H.conj_mem hτ).symm v ∈ orbitOf (RmodN S g t) (aV ht) := by
  rw [RmodN_conj H.conj_mem hτ, ← kappa_aV H hk hτ ht]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨e, he, by simp⟩
  · rintro ⟨e, he, hev⟩
    refine ⟨LinearEquiv.autCongr (kappa H.conj_mem hτ) e, ⟨e, he, rfl⟩, ?_⟩
    simp [hev]

theorem not_V_le_Qa_conj {t τ : S.O} (X : Hyp10 S g t) {k : S.M}
    (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) :
    ¬ V S g τ ≤ S.Qa g := by
  intro hle
  apply X.hVQ
  rw [V_le_Qa_iff X.haQ X.H.conj_ne] at hle ⊢
  intro v hv
  have h1 := hle ((mem_Vt_conj' X.haQ hτ).mpr (by rw [inv_apply_apply_O]; exact hv))
  have h2 := apply_mem_clSub_Qa_of_normalizer X.H (k := k⁻¹)
    (by rw [map_inv]; exact inv_mem hk) h1
  simpa [map_inv, inv_apply_apply_O] using h2

theorem omegaCase_conj {t τ : S.O} (X : Hyp10 S g t) {k : S.M}
    (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹)
    (hτL : τ ∈ S.Lbar g) (hτ1 : τ ≠ 1) (hVQτ : ¬ V S g τ ≤ S.Qa g) :
    OmegaCase X.H X.C hτL hτ1 hVQτ := by
  obtain ⟨Q, hQ, hpol, hRQ, hLQ, hsing⟩ := X.hΩ.exists_form
  have hRconj := RmodN_conj X.haQ hτ
  have hLconj := LmodN_conj X.haQ hτ hk
  have hκaV := kappa_aV X.H hk hτ X.ht
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = kappa X.H.conj_mem hτ := ⟨_, rfl⟩
  have hbk : ∀ x y, beta X.H X.C hτL hτ1 hVQτ (κ x) (κ y) = beta X.H X.C X.ht X.ht1 X.hVQ x y :=
    fun x y => by rw [hκ]; exact beta_kappa X.H X.C X.ht X.ht1 X.hVQ hτ hτL hτ1 hVQτ x y
  have hRconj' : RmodN S g τ = (RmodN S g t).map (LinearEquiv.autCongr κ).toMonoidHom := by
    rw [hκ]; exact hRconj
  have hLconj' : LmodN S g τ = (LmodN S g t).map (LinearEquiv.autCongr κ).toMonoidHom := by
    rw [hκ]; exact hLconj
  have hκaV' : κ (aV X.ht) = aV hτL := by rw [hκ]; exact hκaV
  have horb : ∀ v, v ∈ orbitOf (RmodN S g τ) (aV hτL) ↔
      κ.symm v ∈ orbitOf (RmodN S g t) (aV X.ht) := fun v => by
    rw [hκ]; exact mem_orbitOf_conj X.H hk hτ X.ht v
  clear hRconj hLconj hκaV
  have hpolτ : (Q.comp κ.symm.toLinearMap).polarBilin = beta X.H X.C hτL hτ1 hVQτ := by
    ext u v
    have h1 := hbk (κ.symm u) (κ.symm v)
    rw [LinearEquiv.apply_symm_apply κ u, LinearEquiv.apply_symm_apply κ v] at h1
    rw [h1, ← hpol, polarBilin_apply_apply, polarBilin_apply_apply]
    simp only [QuadraticMap.polar, QuadraticMap.comp_apply, LinearEquiv.coe_coe, map_add]
  have hQτnd : (Q.comp κ.symm.toLinearMap).polarBilin.Nondegenerate :=
    hpolτ ▸ beta_nondegenerate X.H X.C hτL hτ1 hVQτ
  obtain ⟨h1, h2, h3⟩ := transport_omega_data hQ hRQ hLQ hsing hQτnd
  rw [← hRconj'] at h1 h3
  rw [← hLconj', hκaV'] at h2
  rw [hκaV'] at h3
  refine ⟨?_, ⟨_, hQτnd, hpolτ, h1, h2, h3⟩⟩
  obtain ⟨v, hv0, hv⟩ := X.hΩ.not_transitive
  refine ⟨κ v, fun h => hv0 (κ.injective (h.trans (map_zero _).symm)), ?_⟩
  rw [horb, LinearEquiv.symm_apply_apply]
  exact hv

theorem Hyp10.conj' {t τ : S.O} (X : Hyp10 S g t) {k : S.M}
    (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) :
    Hyp10 S g τ := by
  have hτL := mem_Lbar_conj hk hτ X.ht
  have hτ1 : τ ≠ 1 := fun h => X.ht1 (by
    rw [hτ] at h
    have := congrArg (fun x => (S.ρ k)⁻¹ * x * S.ρ k) h
    simpa [mul_assoc] using this)
  have hLmap : (S.Lbar g).map (cK S k) = S.Lbar g := by
    ext x
    rw [mem_map_cK_iff]
    have := mem_normalizer_iff.mp (inv_mem hk) x
    rw [inv_inv] at this
    exact this.symm
  have hVQτ := not_V_le_Qa_conj X hk hτ
  have hRc : Rbar S g τ = (Rbar S g t).map (cK S k) := by subst hτ; exact Rbar_conj k t
  have hNc : Nbar S g τ = (Nbar S g t).map (cK S k) := by subst hτ; exact Nbar_conj X.haQ k t
  have hVc : Vt S g τ = (Vt S g t).map ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    subst hτ; exact Vt_conj X.haQ k t
  refine ⟨X.H, X.hNo, X.C, hτL, hτ1, ?_, ?_, hVQτ, omegaCase_conj X hk hτ hτL hτ1 hVQτ, ?_, ?_⟩
  · intro h
    apply X.hR
    have h1 : (Rbar S g t).map (cK S k) = (S.Lbar g).map (cK S k) := by
      rw [← hRc, h, hLmap]
    exact Subgroup.map_injective (cK_injective k) h1
  · intro h
    apply X.hA
    have h1 : (S.Lbar g ⊓ Nbar S g t).map (cK S k) = (zpowers t).map (cK S k) := by
      rw [Subgroup.map_inf_eq _ _ _ (cK_injective k), hLmap, ← hNc, h,
        MonoidHom.map_zpowers, cK_apply, hτ]
    exact Subgroup.map_injective (cK_injective k) h1
  · rw [hVc, LinearEquiv.finrank_map_eq, X.h4]
  · obtain ⟨W, hW, hWs⟩ := X.plus
    refine ⟨W.map (kappa X.H.conj_mem hτ).toLinearMap, by rw [LinearEquiv.finrank_map_eq, hW],
      ?_⟩
    rintro _ ⟨w, hw, rfl⟩ hw0
    rw [mem_orbitOf_conj X.H hk hτ X.ht]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hWs w hw fun h => hw0 (by rw [h]; exact map_zero _)

end CFSG.LargeExtraspecial.S10
