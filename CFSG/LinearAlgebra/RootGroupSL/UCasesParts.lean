module

public import CFSG.LinearAlgebra.RootGroupSL.DatumGroups
public import CFSG.LinearAlgebra.RootGroupSL.DatumLin
public import CFSG.LinearAlgebra.RootGroupSL.Normalizer

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
  [Module.Finite k E] [Module.Finite k X]

private def stdInlX : X →ₗ[k] DSpace E X :=
  LinearMap.prod (0 : X →ₗ[k] E)
    (LinearMap.prod (LinearMap.id : X →ₗ[k] X) (0 : X →ₗ[k] E))

private def stdInlE : E →ₗ[k] DSpace E X :=
  LinearMap.prod (0 : E →ₗ[k] E)
    (LinearMap.prod (0 : E →ₗ[k] X) (LinearMap.id : E →ₗ[k] E))

private lemma stdIota_apply' (t : E) : stdIota k E X t = (t, (0 : X), (0 : E)) := rfl

private lemma stdPi_apply' (v : DSpace E X) : stdPi k E X v = v.2.2 := rfl

private lemma mem_range_stdIota_iff (w : DSpace E X) :
    w ∈ LinearMap.range (stdIota k E X) ↔ w.2.1 = 0 ∧ w.2.2 = 0 := by
  constructor
  · rintro ⟨t, ht⟩
    have h : w = (t, (0 : X), (0 : E)) := by rw [← ht, stdIota_apply']
    rw [h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨w.1, ?_⟩
    rw [stdIota_apply']
    exact Prod.ext rfl (Prod.ext h1.symm h2.symm)

@[expose] def uSL (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    SpecialLinearGroup k (DSpace E X) :=
  ⟨unipElt φ χ ψ, det_unipElt φ χ ψ⟩

theorem uSL_mul (φ φ' : X →ₗ[k] E) (χ χ' : E →ₗ[k] X) (ψ ψ' : E →ₗ[k] E) :
    uSL φ χ ψ * uSL φ' χ' ψ' = uSL (φ + φ') (χ + χ') (ψ + ψ' + φ ∘ₗ χ') := by
  apply SpecialLinearGroup.ext
  intro v
  change (unipElt φ χ ψ * unipElt φ' χ' ψ') v =
    unipElt (φ + φ') (χ + χ') (ψ + ψ' + φ ∘ₗ χ') v
  rw [unipElt_mul]

theorem uSL_zero : uSL (0 : X →ₗ[k] E) (0 : E →ₗ[k] X) (0 : E →ₗ[k] E) = 1 := by
  apply SpecialLinearGroup.ext
  intro v
  change unipElt (0 : X →ₗ[k] E) (0 : E →ₗ[k] X) (0 : E →ₗ[k] E) v =
    (1 : DSpace E X ≃ₗ[k] DSpace E X) v
  rw [unipElt_zero]

theorem uSL_inj {φ φ' : X →ₗ[k] E} {χ χ' : E →ₗ[k] X} {ψ ψ' : E →ₗ[k] E} :
    uSL φ χ ψ = uSL φ' χ' ψ' ↔ φ = φ' ∧ χ = χ' ∧ ψ = ψ' := by
  constructor
  · intro h
    exact unipElt_inj.mp (Subtype.ext_iff.mp h)
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem exists_uSL_of_mem_QK {g : SpecialLinearGroup k (DSpace E X)} (hg : g ∈ QK k E X) :
    ∃ (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E), g = uSL φ χ ψ := by
  obtain ⟨φ, χ, ψ, h⟩ := exists_unipElt_of_mem_unipRad (mem_QK_iff.mp hg)
  exact ⟨φ, χ, ψ, by
    apply Subtype.ext
    simpa [uSL] using h⟩

theorem mem_datumQ0_std_iff {g : SpecialLinearGroup k (DSpace E X)} :
    g ∈ datumQ0 (stdIota k E X) (stdPi k E X) ↔ ∃ ψ : E →ₗ[k] E, g = uSL 0 0 ψ := by
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := hg
    have h1e : ∀ v : DSpace E X,
        (g : DSpace E X ≃ₗ[k] DSpace E X) v - v ∈ LinearMap.range (stdIota k E X) := h1
    have h2e : ∀ v : DSpace E X, stdPi k E X v = 0 →
        (g : DSpace E X ≃ₗ[k] DSpace E X) v = v := h2
    let ψ : E →ₗ[k] E :=
      (LinearMap.fst k E (X × E)).comp
        (((g : DSpace E X ≃ₗ[k] DSpace E X).toLinearMap - 1) ∘ₗ stdInlE)
    refine ⟨ψ, ?_⟩
    apply SpecialLinearGroup.ext
    intro v
    obtain ⟨a, x, b⟩ := v
    show (g : DSpace E X ≃ₗ[k] DSpace E X) (a, x, b) = unipElt 0 0 ψ (a, x, b)
    have hψ : ψ b = ((g : DSpace E X ≃ₗ[k] DSpace E X) (0, (0 : X), b)).1 := by
      simp [ψ, stdInlE, LinearMap.sub_apply]
    have hfix : (g : DSpace E X ≃ₗ[k] DSpace E X) (a, x, (0 : E)) = (a, x, (0 : E)) := by
      apply h2e
      rw [stdPi_apply']
    have hE0 : (g : DSpace E X ≃ₗ[k] DSpace E X) (0, (0 : X), b) = (ψ b, (0 : X), b) := by
      have hw := h1e (0, (0 : X), b)
      rw [mem_range_stdIota_iff] at hw
      have hdiff : (g : DSpace E X ≃ₗ[k] DSpace E X) (0, (0 : X), b) - (0, (0 : X), b) =
          (ψ b, (0 : X), (0 : E)) := by
        refine Prod.ext ?_ (Prod.ext hw.1 hw.2)
        rw [hψ]
        simp
      have hsum : (g : DSpace E X ≃ₗ[k] DSpace E X) (0, (0 : X), b) =
          (0, (0 : X), b) + (ψ b, (0 : X), (0 : E)) := by
        rw [← hdiff]
        abel
      rw [hsum]
      simp
    rw [show (a, x, b) = (a, x, (0 : E)) + (0, (0 : X), b) by ext <;> simp]
    rw [map_add, hfix, hE0]
    ext <;> simp [uSL, unipElt] <;> abel
  · rintro ⟨ψ, rfl⟩
    refine ⟨?_, ?_⟩
    · intro v
      refine ⟨ψ v.2.2, ?_⟩
      rw [stdIota_apply']
      ext <;> simp [uSL, unipElt] <;> abel
    · intro v hv
      rw [stdPi_apply'] at hv
      ext <;> simp [uSL, unipElt, hv]

theorem mem_datumU1_std_iff {g : SpecialLinearGroup k (DSpace E X)} :
    g ∈ datumU1 (stdIota k E X) ↔ ∃ (φ : X →ₗ[k] E) (ψ : E →ₗ[k] E), g = uSL φ 0 ψ := by
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := hg
    have h1e : ∀ v : DSpace E X,
        (g : DSpace E X ≃ₗ[k] DSpace E X) v - v ∈ LinearMap.range (stdIota k E X) := h1
    have h2e : ∀ t : E,
        (g : DSpace E X ≃ₗ[k] DSpace E X) (stdIota k E X t) = stdIota k E X t := h2
    let φ : X →ₗ[k] E :=
      (LinearMap.fst k E (X × E)).comp
        (((g : DSpace E X ≃ₗ[k] DSpace E X).toLinearMap - 1) ∘ₗ stdInlX)
    let ψ : E →ₗ[k] E :=
      (LinearMap.fst k E (X × E)).comp
        (((g : DSpace E X ≃ₗ[k] DSpace E X).toLinearMap - 1) ∘ₗ stdInlE)
    refine ⟨φ, ψ, ?_⟩
    apply SpecialLinearGroup.ext
    intro v
    obtain ⟨a, x, b⟩ := v
    show (g : DSpace E X ≃ₗ[k] DSpace E X) (a, x, b) = unipElt φ 0 ψ (a, x, b)
    have hφ : φ x = ((g : DSpace E X ≃ₗ[k] DSpace E X) (0, x, (0 : E))).1 := by
      simp [φ, stdInlX, LinearMap.sub_apply]
    have hψ : ψ b = ((g : DSpace E X ≃ₗ[k] DSpace E X) (0, (0 : X), b)).1 := by
      simp [ψ, stdInlE, LinearMap.sub_apply]
    have hfixW : (g : DSpace E X ≃ₗ[k] DSpace E X) (a, (0 : X), (0 : E)) =
        (a, (0 : X), (0 : E)) := by
      have h := h2e a
      rwa [stdIota_apply'] at h
    have hX : (g : DSpace E X ≃ₗ[k] DSpace E X) (0, x, (0 : E)) = (φ x, x, (0 : E)) := by
      have hw := h1e (0, x, (0 : E))
      rw [mem_range_stdIota_iff] at hw
      have hdiff : (g : DSpace E X ≃ₗ[k] DSpace E X) (0, x, (0 : E)) - (0, x, (0 : E)) =
          (φ x, (0 : X), (0 : E)) := by
        refine Prod.ext ?_ (Prod.ext hw.1 hw.2)
        rw [hφ]
        simp
      have hsum : (g : DSpace E X ≃ₗ[k] DSpace E X) (0, x, (0 : E)) =
          (0, x, (0 : E)) + (φ x, (0 : X), (0 : E)) := by
        rw [← hdiff]
        abel
      rw [hsum]
      simp
    have hE0 : (g : DSpace E X ≃ₗ[k] DSpace E X) (0, (0 : X), b) = (ψ b, (0 : X), b) := by
      have hw := h1e (0, (0 : X), b)
      rw [mem_range_stdIota_iff] at hw
      have hdiff : (g : DSpace E X ≃ₗ[k] DSpace E X) (0, (0 : X), b) - (0, (0 : X), b) =
          (ψ b, (0 : X), (0 : E)) := by
        refine Prod.ext ?_ (Prod.ext hw.1 hw.2)
        rw [hψ]
        simp
      have hsum : (g : DSpace E X ≃ₗ[k] DSpace E X) (0, (0 : X), b) =
          (0, (0 : X), b) + (ψ b, (0 : X), (0 : E)) := by
        rw [← hdiff]
        abel
      rw [hsum]
      simp
    rw [show (a, x, b) = (a, (0 : X), (0 : E)) + ((0, x, (0 : E)) + (0, (0 : X), b)) by
      ext <;> simp]
    rw [map_add, map_add, hfixW, hX, hE0]
    ext <;> simp [uSL, unipElt] <;> abel
  · rintro ⟨φ, ψ, rfl⟩
    refine ⟨?_, ?_⟩
    · intro v
      refine ⟨φ v.2.1 + ψ v.2.2, ?_⟩
      rw [stdIota_apply']
      ext <;> simp [uSL, unipElt] <;> abel
    · intro t
      rw [stdIota_apply']
      ext <;> simp [uSL, unipElt]

theorem mem_datumU2_std_iff {g : SpecialLinearGroup k (DSpace E X)} :
    g ∈ datumU2 (stdPi k E X) ↔ ∃ (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E), g = uSL 0 χ ψ := by
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := hg
    have h1e : ∀ v : DSpace E X, stdPi k E X
        ((g : DSpace E X ≃ₗ[k] DSpace E X) v - v) = 0 := h1
    have h2e : ∀ v : DSpace E X, stdPi k E X v = 0 →
        (g : DSpace E X ≃ₗ[k] DSpace E X) v = v := h2
    let χ : E →ₗ[k] X :=
      ((LinearMap.fst k X E).comp (LinearMap.snd k E (X × E))).comp
        (((g : DSpace E X ≃ₗ[k] DSpace E X).toLinearMap - 1) ∘ₗ stdInlE)
    let ψ : E →ₗ[k] E :=
      (LinearMap.fst k E (X × E)).comp
        (((g : DSpace E X ≃ₗ[k] DSpace E X).toLinearMap - 1) ∘ₗ stdInlE)
    refine ⟨χ, ψ, ?_⟩
    apply SpecialLinearGroup.ext
    intro v
    obtain ⟨a, x, b⟩ := v
    show (g : DSpace E X ≃ₗ[k] DSpace E X) (a, x, b) = unipElt 0 χ ψ (a, x, b)
    have hχ : χ b = ((g : DSpace E X ≃ₗ[k] DSpace E X) (0, (0 : X), b)).2.1 := by
      simp [χ, stdInlE, LinearMap.sub_apply]
    have hψ : ψ b = ((g : DSpace E X ≃ₗ[k] DSpace E X) (0, (0 : X), b)).1 := by
      simp [ψ, stdInlE, LinearMap.sub_apply]
    have hfix : (g : DSpace E X ≃ₗ[k] DSpace E X) (a, x, (0 : E)) = (a, x, (0 : E)) := by
      apply h2e
      rw [stdPi_apply']
    have hb : ((g : DSpace E X ≃ₗ[k] DSpace E X) (0, (0 : X), b)).2.2 = b := by
      have hw := h1e (0, (0 : X), b)
      rw [stdPi_apply'] at hw
      exact sub_eq_zero.mp (by simpa using hw)
    have hE0 : (g : DSpace E X ≃ₗ[k] DSpace E X) (0, (0 : X), b) = (ψ b, χ b, b) := by
      refine Prod.ext ?_ (Prod.ext ?_ hb)
      · rw [hψ]
      · rw [hχ]
    rw [show (a, x, b) = (a, x, (0 : E)) + (0, (0 : X), b) by ext <;> simp]
    rw [map_add, hfix, hE0]
    ext <;> simp [uSL, unipElt] <;> abel
  · rintro ⟨χ, ψ, rfl⟩
    refine ⟨?_, ?_⟩
    · intro v
      rw [stdPi_apply']
      simp [uSL, unipElt]
    · intro v hv
      rw [stdPi_apply'] at hv
      ext <;> simp [uSL, unipElt, hv]

theorem blockSL_mul_uSL_mul_inv (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E)
    (h : LinearEquiv.det a * LinearEquiv.det g * LinearEquiv.det b = 1)
    (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    blockSL a g b h * uSL φ χ ψ * (blockSL a g b h)⁻¹ =
      uSL (a.toLinearMap ∘ₗ φ ∘ₗ g.symm.toLinearMap)
        (g.toLinearMap ∘ₗ χ ∘ₗ b.symm.toLinearMap)
        (a.toLinearMap ∘ₗ ψ ∘ₗ b.symm.toLinearMap) := by
  apply SpecialLinearGroup.ext
  intro v
  change (blockDiag a g b * unipElt φ χ ψ * (blockDiag a g b)⁻¹) v =
    unipElt (a.toLinearMap ∘ₗ φ ∘ₗ g.symm.toLinearMap)
      (g.toLinearMap ∘ₗ χ ∘ₗ b.symm.toLinearMap)
      (a.toLinearMap ∘ₗ ψ ∘ₗ b.symm.toLinearMap) v
  rw [blockDiag_mul_unipElt_mul_inv]

end CFSG.LinearAlgebra.RootGroupSL
