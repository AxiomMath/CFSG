module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Facts
import CFSG.GroupTheory.PLayer.CentralQuotient
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Iso
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {H H' : Type} [Group H] [Group H'] [Finite H] [Finite H']

private theorem centralizer_singleton_map (e : H ≃* H') (x : H) :
    Subgroup.centralizer ({e x} : Set H') =
      (Subgroup.centralizer ({x} : Set H)).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hy
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply, hy]
  · intro hy
    have := congrArg e hy
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this

private theorem ker_central (e : H ≃* H') (X : Subgroup H) :
    ∀ y ∈ X ⊓ e.toMonoidHom.ker, ∀ x ∈ X, x * y = y * x := by
  intro y hy x _
  have hy1 : y = 1 := e.injective (by simpa using hy.2)
  rw [hy1, mul_one, one_mul]

private theorem glaPPrimeCoreOf_map_mulEquiv (p : ℕ) (e : H ≃* H') (M : Subgroup H) :
    GLAPPrimeCoreOf p (M.map e.toMonoidHom) = (GLAPPrimeCoreOf p M).map e.toMonoidHom :=
  CFSG.LocalAnalysis.GLTheoremA.T123C.glaPPrimeCoreOf_map e.injective p M

theorem h81Choice_map_mulEquiv {p : ℕ} (hp : p.Prime) (e : H ≃* H') {P : Subgroup H}
    {JType : Subgroup H → Prop} {JType' : Subgroup H' → Prop}
    (hJ : ∀ J : Subgroup H, JType J → JType' (J.map e.toMonoidHom)) (h : H81Choice p P JType) :
    H81Choice p (P.map e.toMonoidHom) JType' := by
  obtain ⟨yy, hyy, hy1, JH, hcomp, huniq, hJT, ⟨zz, hzz, hzy, hlay⟩, haut⟩ := h
  have hc := centralizer_singleton_map e yy
  have hbij := CFSG.glaPComponent_map_bijective_of_ker_le_center hp e.toMonoidHom
    (ker_central e (Subgroup.centralizer ({yy} : Set H)))
  refine ⟨e yy, ⟨yy, hyy, rfl⟩, fun h1 => hy1 (e.injective (by rw [h1, map_one])),
    JH.map e.toMonoidHom, ?_, ?_, hJ JH hJT, ?_, ?_⟩
  · rw [hc]
    exact hbij.1 JH hcomp
  · intro K hK
    rw [hc] at hK
    obtain ⟨J, hJ', rfl⟩ := hbij.2 K hK
    rw [huniq J hJ']
  · refine ⟨e zz, ⟨zz, hzz, rfl⟩, fun hmem => hzy ?_, ?_⟩
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      exact Subgroup.mem_zpowers_iff.2 ⟨k, e.injective (by rw [map_zpow, hk])⟩
    · have hinf : JH.map e.toMonoidHom ⊓ Subgroup.centralizer ({e zz} : Set H') =
          (JH ⊓ Subgroup.centralizer ({zz} : Set H)).map e.toMonoidHom := by
        rw [centralizer_singleton_map e zz, ← Subgroup.map_inf_eq _ _ _ e.injective]
      rw [hinf, ← CFSG.glaPLayer_map_eq_of_ker_le_center hp e.toMonoidHom
        (ker_central e (JH ⊓ Subgroup.centralizer ({zz} : Set H)))]
      intro hbot
      apply hlay
      rwa [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hbot
  · intro α hα hcent
    set β : MulAut H := (MulAut.congr e).symm α with hβ
    have hβapp : ∀ x, β x = e.symm (α (e x)) := fun x => rfl
    have hβp : β ^ p = 1 := by rw [hβ, ← map_pow, hα, map_one]
    have hβc : ∀ j ∈ JH, β j * j⁻¹ ∈ GLAPPrimeCoreOf p JH := by
      intro j hj
      have h1 := hcent (e j) ⟨j, hj, rfl⟩
      rw [glaPPrimeCoreOf_map_mulEquiv p e JH] at h1
      obtain ⟨w, hw, hwe⟩ := h1
      have hw' : w = β j * j⁻¹ := by
        apply e.injective
        rw [MulEquiv.coe_toMonoidHom] at hwe
        rw [hwe, map_mul, map_inv, hβapp, MulEquiv.apply_symm_apply]
      rwa [← hw']
    obtain ⟨k, hk⟩ := haut β hβp hβc
    refine ⟨k, MulEquiv.ext fun x => ?_⟩
    have h2 : α x = e (β (e.symm x)) := by rw [hβapp, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    rw [h2, hk, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, map_zpow,
      MulEquiv.apply_symm_apply]

private noncomputable def pQuotMapEquiv (p : ℕ) (e : H ≃* H') (J : Subgroup H) :
    PQuot p (J.map e.toMonoidHom) ≃* PQuot p J :=
  QuotientGroup.congr _ _ (Subgroup.equivMapOfInjective J e.toMonoidHom e.injective).symm
    (CFSG.LocalAnalysis.GLTheoremA.T123C.map_glaPPrimeCore_equiv p _)

theorem isSL3Type_map_mulEquiv {p q : ℕ} (e : H ≃* H') {J : Subgroup H} (h : IsSL3Type p q J) :
    IsSL3Type p q (J.map e.toMonoidHom) :=
  isSL3Type_of_mulEquiv (pQuotMapEquiv p e J) h

theorem isOmegaType_map_mulEquiv {p q : ℕ} (e : H ≃* H') {J : Subgroup H}
    (h : IsOmegaType p q J) : IsOmegaType p q (J.map e.toMonoidHom) :=
  isOmegaType_of_mulEquiv (pQuotMapEquiv p e J) h

end CFSG.LocalAnalysis.GLTheoremA.H81
