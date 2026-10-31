module

public import CFSG.LinearAlgebra.RootGroupSL.Normalizer
import CFSG.LinearAlgebra.RootGroupSL.SLFacts

public section

namespace CFSG.LinearAlgebra.RootGroupSL

namespace NoOuterGraph

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
  [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

abbrev RootN := Subgroup.normalizer
  (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))

lemma mem_flagW_iff (v : DSpace E X) :
    v ∈ flagW k E X ↔ v.2.1 = 0 ∧ v.2.2 = 0 := by
  simp [flagW, Prod.ext_iff]

lemma mem_flagK_iff (v : DSpace E X) :
    v ∈ flagK k E X ↔ v.2.2 = 0 := by
  simp [flagK]

lemma rootEquiv_apply (t : E) (v : DSpace E X) :
    rootEquiv k X t v = (v.1 + t * v.2.2, v.2.1, v.2.2) := rfl

lemma rootEquiv_zero : rootEquiv k X (0 : E) = 1 := by
  apply LinearEquiv.ext
  intro v
  simp [rootEquiv, shearE]

lemma rootEquiv_neg (t : E) :
    (rootEquiv k X t)⁻¹ = rootEquiv k X (-t) := by
  have h := rootEquiv_add (k := k) (X := X) t (-t)
  rw [add_neg_cancel, rootEquiv_zero] at h
  exact (eq_inv_of_mul_eq_one_right h.symm).symm

lemma rootEquiv_inv_apply_of_mem_flagK (t : E) {v : DSpace E X}
    (hv : v ∈ flagK k E X) : (rootEquiv k X t)⁻¹ v = v := by
  rw [rootEquiv_neg, rootEquiv_apply]
  have hb : v.2.2 = 0 := (mem_flagK_iff v).mp hv
  ext <;> simp [hb]

lemma rootEquiv_inv_sub_mem_flagW (t : E) (v : DSpace E X) :
    (rootEquiv k X t)⁻¹ v - v ∈ flagW k E X := by
  rw [rootEquiv_neg, rootEquiv_apply, mem_flagW_iff]
  simp

lemma blockDiag_apply (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E)
    (v : DSpace E X) :
    blockDiag a g b v = (a v.1, g v.2.1, b v.2.2) := rfl

lemma blockSL_apply (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E)
    (h : LinearEquiv.det a * LinearEquiv.det g * LinearEquiv.det b = 1)
    (v : DSpace E X) :
    (blockSL a g b h : SpecialLinearGroup k (DSpace E X)) v =
      (a v.1, g v.2.1, b v.2.2) := rfl

lemma QK_apply_eq_self_of_mem_flagW {u : SpecialLinearGroup k (DSpace E X)}
    (hu : u ∈ QK k E X) {v : DSpace E X} (hv : v ∈ flagW k E X) : u v = v :=
  (mem_QK_iff.mp hu).1 v hv

lemma QK_sub_mem_flagW_of_mem_flagK {u : SpecialLinearGroup k (DSpace E X)}
    (hu : u ∈ QK k E X) {v : DSpace E X} (hv : v ∈ flagK k E X) :
    u v - v ∈ flagW k E X :=
  (mem_QK_iff.mp hu).2.1 v hv

lemma center_apply_smul {z : SpecialLinearGroup k (DSpace E X)}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup k (DSpace E X))) :
    ∃ c : kˣ, ∀ v : DSpace E X, z v = (c : k) • v := by
  refine exists_smul_of_commute_specialLinearGroup
    (u := SpecialLinearGroup.toLinearEquiv z) ?_
  intro s
  have hzs : z * s = s * z := (Subgroup.mem_center_iff.mp hz s).symm
  have h := congrArg SpecialLinearGroup.toLinearEquiv hzs
  simpa only [map_mul] using h

abbrev AnnK (k E X : Type) [Field k] [Field E] [Algebra k E]
    [AddCommGroup X] [Module k X] : Submodule k (Module.Dual k (DSpace E X)) :=
  (flagK k E X).dualAnnihilator

abbrev AnnW (k E X : Type) [Field k] [Field E] [Algebra k E]
    [AddCommGroup X] [Module k X] : Submodule k (Module.Dual k (DSpace E X)) :=
  (flagW k E X).dualAnnihilator

lemma exists_dualAnnK_of_mem_flagW
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (hR : (rootSL k E X).map α.toMonoidHom = rootSL k E X)
    (T : Module.Dual k (DSpace E X) ≃+ DSpace E X)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X))
      (f : Module.Dual k (DSpace E X)),
      α g (T f) = T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap))
    {w : DSpace E X} (hw : w ∈ flagW k E X) :
    ∃ f ∈ AnnK k E X, T f = w := by
  obtain ⟨hw1, hw2⟩ := (mem_flagW_iff w).mp hw
  let f0 : Module.Dual k (DSpace E X) := T.symm (0, 0, 1)
  have hTf0 : T f0 = (0, 0, 1) := T.apply_symm_apply _
  have hre : rootElt k X w.1 ∈ (rootSL k E X).map α.toMonoidHom := by
    rw [hR]
    exact rootElt_mem_rootSL w.1
  obtain ⟨r', hr', hr'eq⟩ := Subgroup.mem_map.mp hre
  obtain ⟨t, ht⟩ := mem_rootSL_iff.mp hr'
  let f : Module.Dual k (DSpace E X) :=
    f0 ∘ₗ (SpecialLinearGroup.toLinearEquiv (r'⁻¹)).toLinearMap - f0
  refine ⟨f, ?_, ?_⟩
  · rw [Submodule.mem_dualAnnihilator]
    intro v hv
    have hinv : (SpecialLinearGroup.toLinearEquiv (r'⁻¹)).toLinearMap v = v := by
      have ht' : SpecialLinearGroup.toLinearEquiv r' = rootEquiv k X t := by
        rw [SpecialLinearGroup.toLinearEquiv_eq_coe]
        exact ht
      have hcoe : SpecialLinearGroup.toLinearEquiv (r'⁻¹) =
          (rootEquiv k X t)⁻¹ := by
        rw [map_inv, ht']
      rw [hcoe]
      exact rootEquiv_inv_apply_of_mem_flagK t hv
    have hinv' : (SpecialLinearGroup.toLinearEquiv (r'⁻¹)) v = v := hinv
    change f0 ((SpecialLinearGroup.toLinearEquiv (r'⁻¹)) v) - f0 v = 0
    rw [hinv']
    simp
  · have hαr' := hα r' f0
    have hTsub : T (f0 ∘ₗ
        (SpecialLinearGroup.toLinearEquiv (r'⁻¹)).toLinearMap - f0) =
        T (f0 ∘ₗ (SpecialLinearGroup.toLinearEquiv (r'⁻¹)).toLinearMap) - T f0 :=
      T.map_sub _ _
    have hαeq : α r' (T f0) = rootElt k X w.1 (T f0) :=
      congrArg (fun g => g (T f0)) hr'eq
    have hroot : rootElt k X w.1 ((0 : E), (0 : X), (1 : E)) = (w.1, 0, 1) := by
      change rootEquiv k X w.1 ((0 : E), (0 : X), (1 : E)) = (w.1, 0, 1)
      simp [rootEquiv_apply]
    calc
      T f = T (f0 ∘ₗ
          (SpecialLinearGroup.toLinearEquiv (r'⁻¹)).toLinearMap - f0) := rfl
      _ = T (f0 ∘ₗ (SpecialLinearGroup.toLinearEquiv (r'⁻¹)).toLinearMap) - T f0 :=
        hTsub
      _ = α r' (T f0) - T f0 := by rw [← hαr']
      _ = rootElt k X w.1 (T f0) - T f0 := by rw [hαeq]
      _ = rootElt k X w.1 ((0 : E), (0 : X), (1 : E)) - ((0 : E), (0 : X), (1 : E)) := by
        rw [hTf0]
      _ = (w.1, 0, 0) := by rw [hroot]; ext <;> simp
      _ = w := by
        have hw_eq : w = (w.1, (0 : X), (0 : E)) := by
          ext <;> simp [hw1, hw2]
        rw [hw_eq]

lemma T_mem_flagK_of_mem_dualAnnW
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (hR : (rootSL k E X).map α.toMonoidHom = rootSL k E X)
    (T : Module.Dual k (DSpace E X) ≃+ DSpace E X)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X))
      (f : Module.Dual k (DSpace E X)),
      α g (T f) = T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap))
    {f : Module.Dual k (DSpace E X)} (hf : f ∈ AnnW k E X) :
    T f ∈ flagK k E X := by
  rw [mem_flagK_iff]
  have hfix : ∀ t : E, rootElt k X t (T f) = T f := by
    intro t
    have hmem : rootElt k X t ∈ (rootSL k E X).map α.toMonoidHom := by
      rw [hR]
      exact rootElt_mem_rootSL t
    obtain ⟨r', hr', hr'eq⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨t', ht'⟩ := mem_rootSL_iff.mp hr'
    have hαr' : α r' (T f) = T f := by
      rw [hα r' f]
      congr 1
      apply LinearMap.ext
      intro v
      have hsub : (SpecialLinearGroup.toLinearEquiv (r'⁻¹)).toLinearMap v - v ∈
          flagW k E X := by
        have ht'' : SpecialLinearGroup.toLinearEquiv r' = rootEquiv k X t' := by
          rw [SpecialLinearGroup.toLinearEquiv_eq_coe]
          exact ht'
        have hcoe : SpecialLinearGroup.toLinearEquiv (r'⁻¹) =
            (rootEquiv k X t')⁻¹ := by
          rw [map_inv, ht'']
        rw [hcoe]
        exact rootEquiv_inv_sub_mem_flagW t' v
      have hfv := ((Submodule.mem_dualAnnihilator f).mp hf) _ hsub
      have hdecomp : v + ((SpecialLinearGroup.toLinearEquiv (r'⁻¹)).toLinearMap v - v) =
          (SpecialLinearGroup.toLinearEquiv (r'⁻¹)).toLinearMap v := by abel
      calc
        f ((SpecialLinearGroup.toLinearEquiv (r'⁻¹)).toLinearMap v) =
            f (v + ((SpecialLinearGroup.toLinearEquiv (r'⁻¹)).toLinearMap v - v)) := by
          rw [hdecomp]
        _ = f v + f ((SpecialLinearGroup.toLinearEquiv (r'⁻¹)).toLinearMap v - v) :=
          map_add f v _
        _ = f v + 0 := by rw [hfv]
        _ = f v := add_zero _
    calc
      rootElt k X t (T f) = α r' (T f) :=
        (congrArg (fun g => g (T f)) hr'eq).symm
      _ = T f := hαr'
  have h1 := hfix 1
  have hfst : (T f).1 + (1 : E) * (T f).2.2 = (T f).1 := by
    have := congrArg Prod.fst h1
    simpa [rootElt, rootEquiv_apply] using this
  have h' : (T f).1 + (T f).2.2 = (T f).1 + 0 := by simpa using hfst
  exact add_left_cancel h'

lemma mem_dualAnnK_of_T_mem_flagW
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (hR : (rootSL k E X).map α.toMonoidHom = rootSL k E X)
    (T : Module.Dual k (DSpace E X) ≃+ DSpace E X)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X))
      (f : Module.Dual k (DSpace E X)),
      α g (T f) = T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap))
    {f : Module.Dual k (DSpace E X)} (hf : T f ∈ flagW k E X) :
    f ∈ AnnK k E X := by
  obtain ⟨f', hf'K, hf'eq⟩ := exists_dualAnnK_of_mem_flagW α hR T hα hf
  have hfeq : f' = f := T.injective hf'eq
  rw [← hfeq]
  exact hf'K

lemma action_fixes_dualAnnK
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (T : Module.Dual k (DSpace E X) ≃+ DSpace E X)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X))
      (f : Module.Dual k (DSpace E X)),
      α g (T f) = T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap))
    {h : SpecialLinearGroup k (DSpace E X)}
    (htriv : ∀ v : DSpace E X,
      (SpecialLinearGroup.toLinearEquiv h) v - v ∈ flagK k E X)
    {f : Module.Dual k (DSpace E X)} (hf : f ∈ AnnK k E X) :
    α h (T f) = T f := by
  rw [hα h f]
  congr 1
  apply LinearMap.ext
  intro v
  have hcoe : SpecialLinearGroup.toLinearEquiv h⁻¹ =
      (SpecialLinearGroup.toLinearEquiv h)⁻¹ := map_inv _ _
  have hvv : (SpecialLinearGroup.toLinearEquiv h)
      ((SpecialLinearGroup.toLinearEquiv h)⁻¹ v) = v :=
    LinearEquiv.apply_symm_apply _ _
  have hsub : (SpecialLinearGroup.toLinearEquiv h⁻¹) v - v ∈ flagK k E X := by
    rw [hcoe]
    have hv := htriv ((SpecialLinearGroup.toLinearEquiv h)⁻¹ v)
    have hneg : (SpecialLinearGroup.toLinearEquiv h)⁻¹ v - v =
        -((SpecialLinearGroup.toLinearEquiv h) ((SpecialLinearGroup.toLinearEquiv h)⁻¹ v) -
          (SpecialLinearGroup.toLinearEquiv h)⁻¹ v) := by
      rw [hvv]
      abel
    rw [hneg]
    exact Submodule.neg_mem (flagK k E X) hv
  have hfv := ((Submodule.mem_dualAnnihilator f).mp hf) _ hsub
  have hdecomp : v + ((SpecialLinearGroup.toLinearEquiv h⁻¹) v - v) =
      (SpecialLinearGroup.toLinearEquiv h⁻¹) v := by abel
  calc
    f ((SpecialLinearGroup.toLinearEquiv h⁻¹) v) =
        f (v + ((SpecialLinearGroup.toLinearEquiv h⁻¹) v - v)) := by rw [hdecomp]
    _ = f v + f ((SpecialLinearGroup.toLinearEquiv h⁻¹) v - v) := map_add f v _
    _ = f v + 0 := by rw [hfv]
    _ = f v := add_zero _

lemma action_flagW_and_second
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (hC : ∀ h ∈ RootN, α h * h⁻¹ ∈ QK k E X ⊔
      Subgroup.center (SpecialLinearGroup k (DSpace E X)))
    {h : SpecialLinearGroup k (DSpace E X)} (hh : h ∈ RootN) :
    ∃ c : kˣ,
      (∀ w ∈ flagW k E X, α h w = (c : k) • h w) ∧
      (∀ v ∈ flagK k E X, (α h v).2.1 = (c : k) • (h v).2.1) := by
  have hmem : α h * h⁻¹ ∈ QK k E X ⊔
      Subgroup.center (SpecialLinearGroup k (DSpace E X)) := hC h hh
  obtain ⟨u, hu, z, hz, huz⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  obtain ⟨c, hc⟩ := center_apply_smul (k := k) (E := E) (X := X) hz
  refine ⟨c, ?_, ?_⟩
  · intro w hw
    have hhw : h w ∈ flagW k E X := (mem_flagW_iff_of_mem_normalizer hh w).mpr hw
    have hαw : α h w = (u * z) (h w) := by
      rw [huz]
      simp [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv]
    rw [hαw]
    calc
      (u * z) (h w) = u (z (h w)) := LinearEquiv.mul_apply _ _ _
      _ = u ((c : k) • h w) := by rw [hc (h w)]
      _ = (c : k) • u (h w) := map_smul _ _ _
      _ = (c : k) • h w := by rw [QK_apply_eq_self_of_mem_flagW hu hhw]
  · intro v hv
    have hv' : h v ∈ flagK k E X := (mem_flagK_iff_of_mem_normalizer hh v).mpr hv
    have huw : u (h v) - h v ∈ flagW k E X := QK_sub_mem_flagW_of_mem_flagK hu hv'
    have hsec : (u (h v)).2.1 = (h v).2.1 := by
      have h := (mem_flagW_iff (u (h v) - h v)).mp huw
      exact sub_eq_zero.mp h.1
    have hαv : α h v = (u * z) (h v) := by
      rw [huz]
      simp [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv]
    rw [hαv]
    have huz_apply : (u * z) (h v) = u (z (h v)) := by
      change ((↑u : DSpace E X ≃ₗ[k] DSpace E X) *
        (↑z : DSpace E X ≃ₗ[k] DSpace E X)) (h v) = u (z (h v))
      rw [LinearEquiv.mul_apply]
    rw [huz_apply, hc (h v)]
    have hsmul : u ((c : k) • h v) = (c : k) • u (h v) :=
      LinearEquiv.map_smul (u : DSpace E X ≃ₗ[k] DSpace E X) (c : k) (h v)
    rw [hsmul]
    rw [show ((c : k) • u (h v)).2.1 = (c : k) • (u (h v)).2.1 from rfl, hsec]

lemma action_fixes_flagW_of_trivial_quotient
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (hR : (rootSL k E X).map α.toMonoidHom = rootSL k E X)
    (T : Module.Dual k (DSpace E X) ≃+ DSpace E X)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X))
      (f : Module.Dual k (DSpace E X)),
      α g (T f) = T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap))
    {h : SpecialLinearGroup k (DSpace E X)}
    (htriv : ∀ v : DSpace E X,
      (SpecialLinearGroup.toLinearEquiv h) v - v ∈ flagK k E X)
    {w : DSpace E X} (hw : w ∈ flagW k E X) : α h w = w := by
  obtain ⟨f, hfK, hTf⟩ := exists_dualAnnK_of_mem_flagW α hR T hα hw
  rw [← hTf]
  exact action_fixes_dualAnnK α T hα htriv hfK

end NoOuterGraph

end CFSG.LinearAlgebra.RootGroupSL
