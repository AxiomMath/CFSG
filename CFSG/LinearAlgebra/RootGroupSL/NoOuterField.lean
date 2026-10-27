module

public import CFSG.LinearAlgebra.RootGroupSL.Normalizer
public import CFSG.LinearAlgebra.RootGroupSL.FpfArith
public import CFSG.LinearAlgebra.RootGroupSL.SLFacts

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
  [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

private lemma mem_flagW_iff (v : DSpace E X) : v ∈ flagW k E X ↔ v.2 = 0 := by
  rw [flagW, LinearMap.mem_ker]
  rfl

private lemma mem_flagK_iff (v : DSpace E X) : v ∈ flagK k E X ↔ v.2.2 = 0 := by
  rw [flagK, LinearMap.mem_ker]
  rfl

private lemma rootEquiv_sub_self_mem_flagW (t : E) (v : DSpace E X) :
    rootEquiv k X t v - v ∈ flagW k E X := by
  rw [mem_flagW_iff]
  simp [rootEquiv, shearE, LinearMap.mulLeft_apply]

private lemma snd_snd_eq_zero_of_rootEquiv_one_eq_self {v : DSpace E X}
    (h : rootEquiv k X 1 v = v) : v.2.2 = 0 := by
  have h1 : v.1 + v.2.2 = v.1 := by
    have := congrArg Prod.fst h
    simpa [rootEquiv, shearE, LinearMap.mulLeft_apply] using this
  exact add_eq_left.mp h1

private lemma blockDiag_apply_flagW (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E)
    {v : DSpace E X} (hv : v ∈ flagW k E X) :
    blockDiag a g b v = (a v.1, 0, 0) := by
  have h1 : v.2.1 = 0 := congrArg Prod.fst ((mem_flagW_iff v).mp hv)
  have h2 : v.2.2 = 0 := congrArg Prod.snd ((mem_flagW_iff v).mp hv)
  ext <;> simp [blockDiag, LinearEquiv.prodCongr_apply, h1, h2]

private lemma blockDiag_one_sub_smul_mem_flagW (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E) (c : k)
    (hg : ∀ x : X, g x = c • x) {v : DSpace E X} (hv : v ∈ flagK k E X) :
    blockDiag (1 : E ≃ₗ[k] E) g b v - c • v ∈ flagW k E X := by
  obtain ⟨a, x, e⟩ := v
  have h2 : e = 0 := (mem_flagK_iff (a, x, e)).mp hv
  rw [mem_flagW_iff, h2]
  simp [blockDiag, LinearEquiv.prodCongr_apply, hg]

private lemma mulLeftEquiv_symm_apply (u : Eˣ) (x : E) :
    (mulLeftEquiv k u).symm x = ((u⁻¹ : Eˣ) : E) * x := by
  apply (mulLeftEquiv k u).injective
  rw [LinearEquiv.apply_symm_apply, mulLeftEquiv_apply]
  rw [Units.val_inv_eq_inv_val u]
  exact (mul_inv_cancel_left₀ (Units.ne_zero u) x).symm

private lemma smulOfUnit_apply' (a : kˣ) (x : X) :
    (LinearEquiv.smulOfUnit a : X ≃ₗ[k] X) x = (a : k) • x := rfl

private lemma det_smulOfUnit_eq (a : kˣ) :
    LinearEquiv.det (LinearEquiv.smulOfUnit a : X ≃ₗ[k] X) = a ^ Module.finrank k X := by
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.val_pow_eq_pow_val]
  have h : ((LinearEquiv.smulOfUnit a : X ≃ₗ[k] X) : X →ₗ[k] X) =
      (a : k) • (1 : X →ₗ[k] X) := by
    ext x
    rfl
  rw [h, LinearMap.det_smul, map_one, mul_one]

private lemma det_mulLeftEquiv_eq_norm (u : Eˣ) :
    ((LinearEquiv.det (mulLeftEquiv k u) : kˣ) : k) = Algebra.norm k (u : E) := by
  apply det_mulLeft_eq_norm
  ext x
  simp [mulLeftEquiv_apply]

private lemma mapsTo_flagW_flagK_of_semilinear
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (T : DSpace E X ≃+ DSpace E X)
    (hR : (rootSL k E X).map α.toMonoidHom = rootSL k E X)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X)) (v : DSpace E X), α g (T v) = T (g v)) :
    Set.MapsTo T (flagW k E X : Set (DSpace E X)) (flagW k E X) ∧
      Set.MapsTo T (flagK k E X : Set (DSpace E X)) (flagK k E X) := by
  haveI : Module.Finite k E := inferInstance
  constructor
  · intro w hw
    change w ∈ flagW k E X at hw
    change T w ∈ flagW k E X
    rw [mem_flagW_iff] at hw ⊢
    have hwdec : w = rootEquiv k X w.1 ((0 : E), (0 : X), (1 : E)) -
        ((0 : E), (0 : X), (1 : E)) := by
      have hw1 : w.2.1 = 0 := congrArg Prod.fst hw
      have hw2 : w.2.2 = 0 := congrArg Prod.snd hw
      ext <;> simp [rootEquiv, shearE, LinearMap.mulLeft_apply, hw1, hw2]
    have hmem : α (rootElt k X w.1) ∈ rootSL k E X := by
      rw [← hR]
      exact Subgroup.mem_map.mpr ⟨rootElt k X w.1, rootElt_mem_rootSL w.1, rfl⟩
    obtain ⟨t, ht⟩ := (mem_rootSL_iff).mp hmem
    have hTval : T w = rootEquiv k X t (T ((0 : E), (0 : X), (1 : E))) -
        T ((0 : E), (0 : X), (1 : E)) := by
      rw [hwdec, map_sub]
      congr 1
      rw [← ht]
      exact (hα (rootElt k X w.1) ((0 : E), (0 : X), (1 : E))).symm
    rw [hTval]
    exact rootEquiv_sub_self_mem_flagW t (T ((0 : E), (0 : X), (1 : E)))
  · intro v hv
    change v ∈ flagK k E X at hv
    change T v ∈ flagK k E X
    rw [mem_flagK_iff] at hv ⊢
    have h1mem : rootElt k X (1 : E) ∈ (rootSL k E X).map α.toMonoidHom := by
      rw [hR]
      exact rootElt_mem_rootSL 1
    obtain ⟨r, hr, hreq⟩ := Subgroup.mem_map.mp h1mem
    have hrfix : r v = v := by
      obtain ⟨t, ht⟩ := (mem_rootSL_iff).mp hr
      rw [show r v = (r : DSpace E X ≃ₗ[k] DSpace E X) v from rfl, ht]
      simp [rootEquiv, shearE, LinearMap.mulLeft_apply, hv]
    have hfix : rootEquiv k X 1 (T v) = T v := by
      have h := hα r v
      have h1 : α r = rootElt k X 1 := hreq
      rw [h1, hrfix] at h
      exact h
    exact snd_snd_eq_zero_of_rootEquiv_one_eq_self hfix

private lemma map_inv_semilinear
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (T : DSpace E X ≃+ DSpace E X)
    (hR : (rootSL k E X).map α.toMonoidHom = rootSL k E X)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X)) (v : DSpace E X), α g (T v) = T (g v)) :
    (rootSL k E X).map (α⁻¹).toMonoidHom = rootSL k E X ∧
      (∀ (g : SpecialLinearGroup k (DSpace E X)) (v : DSpace E X),
        α⁻¹ g (T.symm v) = T.symm (g v)) := by
  constructor
  · have hcomp : (α⁻¹).toMonoidHom.comp α.toMonoidHom =
        MonoidHom.id (SpecialLinearGroup k (DSpace E X)) := by
      refine MonoidHom.ext fun g => ?_
      simp
    calc (rootSL k E X).map (α⁻¹).toMonoidHom
        = ((rootSL k E X).map α.toMonoidHom).map (α⁻¹).toMonoidHom := by rw [hR]
      _ = (rootSL k E X).map ((α⁻¹).toMonoidHom.comp α.toMonoidHom) :=
            (rootSL k E X).map_map (α⁻¹).toMonoidHom α.toMonoidHom
      _ = (rootSL k E X).map (MonoidHom.id _) := by rw [hcomp]
      _ = rootSL k E X := Subgroup.map_id _
  · intro g v
    have h := hα (α⁻¹ g) (T.symm v)
    rw [show α (α⁻¹ g) = g by simp, AddEquiv.apply_symm_apply] at h
    exact ((AddEquiv.symm_apply_eq T).mpr h).symm

private lemma field_form_scalar_eq_one
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (T : DSpace E X ≃+ DSpace E X)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X)) (v : DSpace E X), α g (T v) = T (g v))
    (hmapWinv : Set.MapsTo T.symm (flagW k E X : Set (DSpace E X)) (flagW k E X))
    (h u z : SpecialLinearGroup k (DSpace E X)) (hu : u ∈ QK k E X)
    (hαh : α h = u * z * h)
    (lam : kˣ)
    (hlam : ∀ x : DSpace E X, (z : DSpace E X ≃ₗ[k] DSpace E X) x = (lam : k) • x)
    (hhWid : ∀ w ∈ flagW k E X, h w = w) :
    (lam : k) = 1 := by
  have hscalar : ∀ w ∈ flagW k E X, w = (lam : k) • w := by
    intro w hw
    have hTw : T.symm w ∈ flagW k E X := hmapWinv hw
    have hhW : h (T.symm w) = T.symm w := hhWid _ hTw
    have hwW : h w = w := hhWid _ hw
    have huW : u w = w := (mem_QK_iff.mp hu).1 w hw
    have e1 : α h w = w := by
      have hh := hα h (T.symm w)
      rw [AddEquiv.apply_symm_apply, hhW] at hh
      simpa using hh
    have e2 : α h w = (lam : k) • w := by
      have hcomp : (u * z * h) w = u (z (h w)) := rfl
      rw [hαh, hcomp, hwW]
      simp only [hlam, map_smul, huW]
    exact e1.symm.trans e2
  have hw0 : ((1 : E), (0 : X), (0 : E)) ∈ flagW k E X := (mem_flagW_iff _).mpr rfl
  have h1 := congrArg Prod.fst (hscalar _ hw0)
  have h2 : (lam : k) • (1 : E) = 1 := h1.symm
  rw [Algebra.smul_def, mul_one] at h2
  exact FaithfulSMul.algebraMap_injective k E (by rw [h2, map_one])

private lemma field_form_Kpart
    (hX : 0 < Module.finrank k X)
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (T : DSpace E X ≃+ DSpace E X) (σ : k ≃+* k)
    (hT : ∀ (c : k) (v : DSpace E X), T (c • v) = σ c • T v)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X)) (v : DSpace E X), α g (T v) = T (g v))
    (hmapW : Set.MapsTo T (flagW k E X : Set (DSpace E X)) (flagW k E X))
    (hmapKinv : Set.MapsTo T.symm (flagK k E X : Set (DSpace E X)) (flagK k E X))
    (c : k)
    (h u z : SpecialLinearGroup k (DSpace E X)) (hu : u ∈ QK k E X)
    (hαh : α h = u * z * h)
    (lam : kˣ)
    (hlam : ∀ x : DSpace E X, (z : DSpace E X ≃ₗ[k] DSpace E X) x = (lam : k) • x)
    (hlam1 : (lam : k) = 1)
    (hK : ∀ v ∈ flagK k E X, h v - c • v ∈ flagW k E X) :
    σ c = c := by
  obtain ⟨x, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hX
  let v : DSpace E X := ((0 : E), x, (0 : E))
  have hvK : v ∈ flagK k E X := (mem_flagK_iff _).mpr rfl
  have hTin : T.symm v ∈ flagK k E X := hmapKinv hvK
  set w : DSpace E X := h (T.symm v) - c • (T.symm v) with hw_def
  have hwW : w ∈ flagW k E X := hK _ hTin
  have hdecomp : h (T.symm v) = c • (T.symm v) + w := by
    rw [hw_def, add_comm]
    exact (sub_add_cancel _ _).symm
  have hαv : α h v = σ c • v + T w := by
    have hh := hα h (T.symm v)
    rw [AddEquiv.apply_symm_apply, hdecomp, map_add, hT c (T.symm v),
      AddEquiv.apply_symm_apply] at hh
    exact hh
  have hW1 : α h v - σ c • v ∈ flagW k E X := by
    rw [hαv, add_sub_cancel_left]
    exact hmapW hwW
  set w' : DSpace E X := h v - c • v with hw'_def
  have hw'W : w' ∈ flagW k E X := hK v hvK
  have hdecomp' : h v = c • v + w' := by
    rw [hw'_def, add_comm]
    exact (sub_add_cancel _ _).symm
  have huv : u v - v ∈ flagW k E X := (mem_QK_iff.mp hu).2.1 v hvK
  have huw' : u w' = w' := (mem_QK_iff.mp hu).1 w' hw'W
  have hαv2 : α h v = c • u v + w' := by
    have hcomp : (u * z * h) v = u (z (h v)) := rfl
    rw [hαh, hcomp, hdecomp']
    simp only [hlam, map_smul, hlam1, one_smul, map_add, huw']
  have hW2 : α h v - c • v ∈ flagW k E X := by
    have heq : α h v - c • v = c • (u v - v) + w' := by
      rw [hαv2, smul_sub]
      abel
    rw [heq]
    exact Submodule.add_mem _ (Submodule.smul_mem _ c huv) hw'W
  have hW3 : (σ c - c) • v ∈ flagW k E X := by
    have heq : (α h v - c • v) - (α h v - σ c • v) = (σ c - c) • v := by
      rw [sub_sub_sub_cancel_left, sub_smul]
    rw [← heq]
    exact Submodule.sub_mem _ hW2 hW1
  have hxzero : (σ c - c) • x = 0 := by
    have hmem := (mem_flagW_iff ((σ c - c) • v)).mp hW3
    have := congrArg Prod.fst hmem
    simpa [v] using this
  have hsub : σ c - c = 0 := by
    rcases smul_eq_zero.mp hxzero with h | h
    · exact h
    · exact absurd h hx0
  exact sub_eq_zero.mp hsub

private lemma norm_exists (c' : kˣ) :
    ∃ s : Eˣ, Algebra.norm k (s : E) = (c' : k) ^ Module.finrank k X := by
  obtain ⟨s, hs⟩ := FiniteField.unitsMap_norm_surjective k E (c' ^ Module.finrank k X)
  exact ⟨s, by
    have := congrArg (fun u : kˣ => (u : k)) hs
    simpa [Units.val_pow_eq_pow_val] using this⟩

private lemma det_blockSL_eq_one (c' : kˣ) (s : Eˣ)
    (hnorm : Algebra.norm k (s : E) = (c' : k) ^ Module.finrank k X) :
    LinearEquiv.det (1 : E ≃ₗ[k] E) *
      LinearEquiv.det (LinearEquiv.smulOfUnit c' : X ≃ₗ[k] X) *
      LinearEquiv.det (mulLeftEquiv k s⁻¹) = 1 := by
  have hg : LinearEquiv.det (LinearEquiv.smulOfUnit c' : X ≃ₗ[k] X) =
      c' ^ Module.finrank k X := det_smulOfUnit_eq c'
  have hb : LinearEquiv.det (mulLeftEquiv k s⁻¹) = (c' ^ Module.finrank k X)⁻¹ := by
    apply Units.ext
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    change ((LinearEquiv.det (mulLeftEquiv k s⁻¹) : kˣ) : k) =
      ((c' : k) ^ Module.finrank k X)⁻¹
    rw [det_mulLeftEquiv_eq_norm]
    rw [show ((s⁻¹ : Eˣ) : E) = (s : E)⁻¹ from Units.val_inv_eq_inv_val s,
      Algebra.norm_inv, hnorm]
  rw [map_one, one_mul, hg, hb, mul_inv_cancel]

private lemma blockSL_mem_normalizer (c' : kˣ) (s : Eˣ)
    (hdet : LinearEquiv.det (1 : E ≃ₗ[k] E) *
      LinearEquiv.det (LinearEquiv.smulOfUnit c' : X ≃ₗ[k] X) *
      LinearEquiv.det (mulLeftEquiv k s⁻¹) = 1) :
    blockSL (1 : E ≃ₗ[k] E) (LinearEquiv.smulOfUnit c' : X ≃ₗ[k] X) (mulLeftEquiv k s⁻¹) hdet ∈
      Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) := by
  haveI : Module.Finite k E := inferInstance
  rw [blockSL_mem_normalizer_iff]
  intro t
  refine ⟨t * s, ?_⟩
  ext y
  simp [mulLeftEquiv_symm_apply, LinearMap.mulLeft_apply, mul_assoc]

private lemma center_scalar (z : SpecialLinearGroup k (DSpace E X))
    (hz : z ∈ Subgroup.center (SpecialLinearGroup k (DSpace E X))) :
    ∃ lam : kˣ, ∀ x : DSpace E X,
      (z : DSpace E X ≃ₗ[k] DSpace E X) x = (lam : k) • x := by
  have hcomm : ∀ s' : SpecialLinearGroup k (DSpace E X),
      (z : DSpace E X ≃ₗ[k] DSpace E X) * SpecialLinearGroup.toLinearEquiv s' =
        SpecialLinearGroup.toLinearEquiv s' * (z : DSpace E X ≃ₗ[k] DSpace E X) := by
    intro s'
    have h := congrArg SpecialLinearGroup.toLinearEquiv ((Subgroup.mem_center_iff.mp hz) s')
    rw [map_mul, map_mul] at h
    exact h.symm
  exact exists_smul_of_commute_specialLinearGroup (z : DSpace E X ≃ₗ[k] DSpace E X) hcomm

private lemma field_form_blockSL (c : k) (hc : c ≠ 0) :
    ∃ h : SpecialLinearGroup k (DSpace E X),
      h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) ∧
      (∀ w ∈ flagW k E X, h w = w) ∧
      (∀ v ∈ flagK k E X, h v - c • v ∈ flagW k E X) := by
  haveI : Module.Finite k E := inferInstance
  let c' : kˣ := Units.mk0 c hc
  obtain ⟨s, hnorm⟩ := norm_exists (k := k) (E := E) (X := X) c'
  have hdet := det_blockSL_eq_one (k := k) (E := E) (X := X) c' s hnorm
  let h : SpecialLinearGroup k (DSpace E X) :=
    blockSL (1 : E ≃ₗ[k] E) (LinearEquiv.smulOfUnit c' : X ≃ₗ[k] X) (mulLeftEquiv k s⁻¹) hdet
  have hhN : h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) := by
    rw [show h = blockSL (1 : E ≃ₗ[k] E) (LinearEquiv.smulOfUnit c' : X ≃ₗ[k] X)
      (mulLeftEquiv k s⁻¹) hdet from rfl]
    exact blockSL_mem_normalizer (k := k) (E := E) (X := X) c' s hdet
  have hhWid : ∀ w ∈ flagW k E X, h w = w := by
    intro w hw
    rw [show h w = blockDiag (1 : E ≃ₗ[k] E) (LinearEquiv.smulOfUnit c' : X ≃ₗ[k] X)
      (mulLeftEquiv k s⁻¹) w from rfl, blockDiag_apply_flagW _ _ _ hw]
    have hw1 : w.2.1 = 0 := congrArg Prod.fst (LinearMap.mem_ker.mp hw)
    have hw2 : w.2.2 = 0 := congrArg Prod.snd (LinearMap.mem_ker.mp hw)
    ext <;> simp [hw1, hw2]
  have hK : ∀ v ∈ flagK k E X, h v - c • v ∈ flagW k E X := by
    intro v hv
    rw [show h v = blockDiag (1 : E ≃ₗ[k] E) (LinearEquiv.smulOfUnit c' : X ≃ₗ[k] X)
      (mulLeftEquiv k s⁻¹) v from rfl]
    exact blockDiag_one_sub_smul_mem_flagW (LinearEquiv.smulOfUnit c' : X ≃ₗ[k] X)
      (mulLeftEquiv k s⁻¹) c (fun y => smulOfUnit_apply' c' y) hv
  exact ⟨h, hhN, hhWid, hK⟩

private lemma field_form_decompose
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (h : SpecialLinearGroup k (DSpace E X))
    (hmem : α h * h⁻¹ ∈ QK k E X ⊔ Subgroup.center (SpecialLinearGroup k (DSpace E X))) :
    ∃ (u z : SpecialLinearGroup k (DSpace E X)) (lam : kˣ),
      u ∈ QK k E X ∧ z ∈ Subgroup.center (SpecialLinearGroup k (DSpace E X)) ∧
      α h = u * z * h ∧
      (∀ x : DSpace E X, (z : DSpace E X ≃ₗ[k] DSpace E X) x = (lam : k) • x) := by
  obtain ⟨u, hu, z, hz, huz⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := QK k E X)
      (t := Subgroup.center (SpecialLinearGroup k (DSpace E X)))).mp hmem
  have hαh : α h = u * z * h := by
    rw [huz, mul_assoc, inv_mul_cancel, mul_one]
  obtain ⟨lam, hlam⟩ := center_scalar (k := k) (E := E) (X := X) z hz
  exact ⟨u, z, lam, hu, hz, hαh, hlam⟩

private lemma field_form_scalar_step
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (hC : ∀ h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))),
      α h * h⁻¹ ∈ QK k E X ⊔ Subgroup.center (SpecialLinearGroup k (DSpace E X)))
    (T : DSpace E X ≃+ DSpace E X)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X)) (v : DSpace E X), α g (T v) = T (g v))
    (hmapWinv : Set.MapsTo T.symm (flagW k E X : Set (DSpace E X)) (flagW k E X))
    (c : k) (hc : c ≠ 0) :
    ∃ (h u z : SpecialLinearGroup k (DSpace E X)) (lam : kˣ),
      h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) ∧
      u ∈ QK k E X ∧ z ∈ Subgroup.center (SpecialLinearGroup k (DSpace E X)) ∧
      α h = u * z * h ∧
      (∀ x : DSpace E X, (z : DSpace E X ≃ₗ[k] DSpace E X) x = (lam : k) • x) ∧
      (lam : k) = 1 ∧
      (∀ v ∈ flagK k E X, h v - c • v ∈ flagW k E X) := by
  obtain ⟨h, hhN, hhWid, hK⟩ := field_form_blockSL (k := k) (E := E) (X := X) c hc
  have hmem : α h * h⁻¹ ∈ QK k E X ⊔ Subgroup.center (SpecialLinearGroup k (DSpace E X)) :=
    hC h hhN
  obtain ⟨u, z, lam, hu, hz, hαh, hlam⟩ := field_form_decompose α h hmem
  have hlam1 : (lam : k) = 1 :=
    field_form_scalar_eq_one α T hα hmapWinv h u z hu hαh lam hlam hhWid
  exact ⟨h, u, z, lam, hhN, hu, hz, hαh, hlam, hlam1, hK⟩

private lemma field_form_nonzero
    (hX : 0 < Module.finrank k X)
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (hC : ∀ h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))),
      α h * h⁻¹ ∈ QK k E X ⊔ Subgroup.center (SpecialLinearGroup k (DSpace E X)))
    (σ : k ≃+* k) (T : DSpace E X ≃+ DSpace E X)
    (hT : ∀ (c : k) (v : DSpace E X), T (c • v) = σ c • T v)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X)) (v : DSpace E X), α g (T v) = T (g v))
    (hmapW : Set.MapsTo T (flagW k E X : Set (DSpace E X)) (flagW k E X))
    (hmapWinv : Set.MapsTo T.symm (flagW k E X : Set (DSpace E X)) (flagW k E X))
    (hmapKinv : Set.MapsTo T.symm (flagK k E X : Set (DSpace E X)) (flagK k E X))
    (c : k) (hc : c ≠ 0) :
    σ c = c := by
  obtain ⟨h, u, z, lam, hhN, hu, hz, hαh, hlam, hlam1, hK⟩ :=
    field_form_scalar_step α hC T hα hmapWinv c hc
  exact field_form_Kpart hX α T σ hT hα hmapW hmapKinv c h u z hu hαh lam hlam hlam1 hK

theorem field_form_eq_refl (hX : 0 < Module.finrank k X)
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (hR : (rootSL k E X).map α.toMonoidHom = rootSL k E X)
    (hC : ∀ h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))),
      α h * h⁻¹ ∈ QK k E X ⊔ Subgroup.center (SpecialLinearGroup k (DSpace E X)))
    (σ : k ≃+* k) (T : DSpace E X ≃+ DSpace E X)
    (hT : ∀ (c : k) (v : DSpace E X), T (c • v) = σ c • T v)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X)) (v : DSpace E X), α g (T v) = T (g v)) :
    σ = RingEquiv.refl k := by
  haveI : Module.Finite k E := inferInstance
  have hmap := mapsTo_flagW_flagK_of_semilinear α T hR hα
  have hmapW : Set.MapsTo T (flagW k E X : Set (DSpace E X)) (flagW k E X) := hmap.1
  have hinv := map_inv_semilinear α T hR hα
  have hmapinv := mapsTo_flagW_flagK_of_semilinear (α⁻¹) T.symm hinv.1 hinv.2
  have hmapWinv : Set.MapsTo T.symm (flagW k E X : Set (DSpace E X)) (flagW k E X) := hmapinv.1
  have hmapKinv : Set.MapsTo T.symm (flagK k E X : Set (DSpace E X)) (flagK k E X) := hmapinv.2
  refine RingEquiv.ext fun c => ?_
  by_cases hc : c = 0
  · simp [hc]
  exact field_form_nonzero hX α hC σ T hT hα hmapW hmapWinv hmapKinv c hc

end CFSG.LinearAlgebra.RootGroupSL
