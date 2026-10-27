module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def hypPerp (P : HypPair Q) : Submodule K V where
  carrier := {v | polar Q v P.e = 0 ∧ polar Q v P.f = 0}
  add_mem' {x y} hx hy :=
    ⟨by rw [polar_add_left, hx.1, hy.1, add_zero], by rw [polar_add_left, hx.2, hy.2, add_zero]⟩
  zero_mem' := ⟨polar_zero_left Q _, polar_zero_left Q _⟩
  smul_mem' c x hx :=
    ⟨by rw [polar_smul_left_eq, hx.1, mul_zero], by rw [polar_smul_left_eq, hx.2, mul_zero]⟩

theorem mem_hypPerp {P : HypPair Q} {v : V} :
    v ∈ hypPerp P ↔ polar Q v P.e = 0 ∧ polar Q v P.f = 0 :=
  Iff.rfl

noncomputable abbrev perpForm (P : HypPair Q) : QuadraticForm K (hypPerp P) :=
  Q.comp (hypPerp P).subtype

theorem perpForm_apply (P : HypPair Q) (v : hypPerp P) : perpForm P v = Q v :=
  rfl

theorem polar_perpForm (P : HypPair Q) (u v : hypPerp P) :
    polar (perpForm P) u v = polar Q u v := by
  simp [perpForm, polar, QuadraticMap.comp_apply]

@[expose] noncomputable def perpProj (P : HypPair Q) : V →ₗ[K] hypPerp P where
  toFun x := ⟨x - polar Q x P.f • P.e - polar Q x P.e • P.f, by
    refine ⟨?_, ?_⟩
    · rw [polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, P.polar_ee,
        P.polar_fe]
      ring
    · rw [polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, P.polar_ef,
        P.polar_ff]
      ring⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, polar_add_left, add_smul]
    abel
  map_smul' c x := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, polar_smul_left_eq, RingHom.id_apply, smul_sub, smul_smul]

theorem perpProj_coe (P : HypPair Q) (x : V) :
    (perpProj P x : V) = x - polar Q x P.f • P.e - polar Q x P.e • P.f :=
  rfl

theorem perpProj_of_mem (P : HypPair Q) {v : V} (hv : v ∈ hypPerp P) :
    perpProj P v = ⟨v, hv⟩ := by
  apply Subtype.ext
  rw [perpProj_coe, hv.1, hv.2, zero_smul, zero_smul, sub_zero, sub_zero]

theorem perpProj_add (P : HypPair Q) (x : V) :
    (perpProj P x : V) + polar Q x P.f • P.e + polar Q x P.e • P.f = x := by
  rw [perpProj_coe]
  abel

@[expose] noncomputable def extLin (P : HypPair Q) (g : hypPerp P →ₗ[K] hypPerp P) : V →ₗ[K] V :=
  (hypPerp P).subtype ∘ₗ g ∘ₗ perpProj P +
    (((polarBilin Q).flip P.f).smulRight P.e + ((polarBilin Q).flip P.e).smulRight P.f)

theorem extLin_apply (P : HypPair Q) (g : hypPerp P →ₗ[K] hypPerp P) (x : V) :
    extLin P g x = (g (perpProj P x) : V) + polar Q x P.f • P.e + polar Q x P.e • P.f := by
  simp [extLin, polarBilin_apply_apply, add_assoc]

theorem polar_extLin_e (P : HypPair Q) (g : hypPerp P →ₗ[K] hypPerp P) (x : V) :
    polar Q (extLin P g x) P.e = polar Q x P.e := by
  rw [extLin_apply, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
    (g (perpProj P x)).2.1, P.polar_ee, P.polar_fe]
  ring

theorem polar_extLin_f (P : HypPair Q) (g : hypPerp P →ₗ[K] hypPerp P) (x : V) :
    polar Q (extLin P g x) P.f = polar Q x P.f := by
  rw [extLin_apply, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
    (g (perpProj P x)).2.2, P.polar_ef, P.polar_ff]
  ring

theorem perpProj_extLin (P : HypPair Q) (g : hypPerp P →ₗ[K] hypPerp P) (x : V) :
    perpProj P (extLin P g x) = g (perpProj P x) := by
  apply Subtype.ext
  rw [perpProj_coe, polar_extLin_e, polar_extLin_f, extLin_apply]
  abel

theorem extLin_comp (P : HypPair Q) (g h : hypPerp P →ₗ[K] hypPerp P) :
    extLin P (g ∘ₗ h) = extLin P g ∘ₗ extLin P h := by
  ext x
  rw [LinearMap.comp_apply, extLin_apply P g, perpProj_extLin, polar_extLin_e, polar_extLin_f,
    extLin_apply, LinearMap.comp_apply]

theorem extLin_id (P : HypPair Q) : extLin P LinearMap.id = LinearMap.id := by
  ext x
  rw [extLin_apply, LinearMap.id_apply, LinearMap.id_apply, perpProj_add]

@[expose] noncomputable def extHom (P : HypPair Q) : (hypPerp P ≃ₗ[K] hypPerp P) →* (V ≃ₗ[K] V) where
  toFun g := LinearEquiv.ofLinearMap (extLin P g) (extLin P g.symm)
    (by
      rw [← extLin_comp, ← extLin_id P]
      congr 1
      ext x
      simp)
    (by
      rw [← extLin_comp, ← extLin_id P]
      congr 1
      ext x
      simp)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change extLin P LinearMap.id x = x
    rw [extLin_id, LinearMap.id_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    change extLin P ((g : hypPerp P →ₗ[K] hypPerp P) ∘ₗ (h : hypPerp P →ₗ[K] hypPerp P)) x =
      extLin P g (extLin P h x)
    rw [extLin_comp, LinearMap.comp_apply]

theorem extHom_apply (P : HypPair Q) (g : hypPerp P ≃ₗ[K] hypPerp P) (x : V) :
    extHom P g x = (g (perpProj P x) : V) + polar Q x P.f • P.e + polar Q x P.e • P.f :=
  extLin_apply P g x

theorem extHom_apply_mem (P : HypPair Q) (g : hypPerp P ≃ₗ[K] hypPerp P) {v : V}
    (hv : v ∈ hypPerp P) : extHom P g v = g ⟨v, hv⟩ := by
  rw [extHom_apply, perpProj_of_mem P hv, hv.1, hv.2, zero_smul, zero_smul, add_zero, add_zero]

theorem perpProj_e (P : HypPair Q) : perpProj P P.e = 0 := by
  apply Subtype.ext
  rw [perpProj_coe, P.polar_ef, P.polar_ee, one_smul, zero_smul, sub_zero, sub_self,
    Submodule.coe_zero]

theorem extHom_apply_e (P : HypPair Q) (g : hypPerp P ≃ₗ[K] hypPerp P) : extHom P g P.e = P.e := by
  rw [extHom_apply, perpProj_e, map_zero, Submodule.coe_zero, P.polar_ef, P.polar_ee, one_smul,
    zero_smul, zero_add, add_zero]

theorem polar_perpProj (P : HypPair Q) (x : V) {u : V} (hu : u ∈ hypPerp P) :
    polar Q (perpProj P x) u = polar Q x u := by
  rw [perpProj_coe, polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq,
    polar_comm Q P.e u, polar_comm Q P.f u, hu.1, hu.2]
  ring

theorem extHom_eichler (P : HypPair Q) (u w : hypPerp P) :
    extHom P (eichler (perpForm P) u w) = eichler Q u w := by
  by_cases h : perpForm P u = 0 ∧ polar (perpForm P) u w = 0
  · have hu : Q u = 0 := h.1
    have hw : polar Q u w = 0 := by rw [← polar_perpForm]; exact h.2
    apply LinearEquiv.ext
    intro x
    rw [extHom_apply, eichler_apply h.1 h.2, eichler_apply hu hw]
    simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, polar_perpForm,
      perpForm_apply, polar_perpProj P x u.2, polar_perpProj P x w.2]
    linear_combination (norm := module) perpProj_add P x
  · have h' : ¬(Q u = 0 ∧ polar Q u w = 0) := by rwa [← polar_perpForm]
    rw [eichler_of_not h, eichler_of_not h', map_one]

theorem extHom_mem_elementaryGroup (P : HypPair Q) {g : hypPerp P ≃ₗ[K] hypPerp P}
    (hg : g ∈ elementaryGroup (perpForm P)) : extHom P g ∈ elementaryGroup Q := by
  have hle : elementaryGroup (perpForm P) ≤ (elementaryGroup Q).comap (extHom P) := by
    apply elementaryGroup_le_of_eichler_mem
    intro u w _ _
    rw [Subgroup.mem_comap, extHom_eichler]
    exact eichler_mem_elementaryGroup Q _ _
  exact hle hg

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
