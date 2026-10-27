module

public import CFSG.Fischer.Uniq.EdgeFixed

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {Y : Type} [Group Y] {F : Set Y}

@[expose] def StarTau (hF : Pair Y F) {q p : Y} (θ : LocalClass F q ≃ LocalClass F p) : Prop :=
  ∀ x y : LocalClass F q,
    (θ ⟨(x : Y) * y * x, LocalPoints.mul_mul_mem_localClass hF x y⟩ : Y) = θ x * θ y * θ x

@[expose] def starConjTo (hF : Pair Y F) (g : Y) {t q : Y} (h : g * t * g⁻¹ = q) :
    LocalClass F t ≃ LocalClass F q :=
  (conjStar hF g t).trans (Set.equivOfEq (congrArg (LocalClass F) h))

theorem starConjTo_symm_val (hF : Pair Y F) (g : Y) {t q : Y} (h : g * t * g⁻¹ = q)
    (x : LocalClass F q) : ((starConjTo hF g h).symm x : Y) = g⁻¹ * x * g := rfl

theorem exists_conj_of_star_equiv (hF : Pair Y F) {t : Y} (ht : t ∈ F)
    (hrig : ∀ θ : LocalClass F t ≃ LocalClass F t, StarTau hF θ →
      ∃ m : Y, m * t * m⁻¹ = t ∧ ∀ x, (θ x : Y) = m * x * m⁻¹)
    {q p : Y} (hq : q ∈ F) (hp : p ∈ F) (θ : LocalClass F q ≃ LocalClass F p)
    (hθ : StarTau hF θ) : ∃ r : Y, r * q * r⁻¹ = p ∧ ∀ x, (θ x : Y) = r * x * r⁻¹ := by
  obtain ⟨cq, hcq⟩ := isConj_iff.1 (Pair.isConj hF ht hq)
  obtain ⟨cp, hcp⟩ := isConj_iff.1 (Pair.isConj hF ht hp)
  set θ' : LocalClass F t ≃ LocalClass F t :=
    ((starConjTo hF cq hcq).trans θ).trans (starConjTo hF cp hcp).symm with hθ'
  have hval : ∀ x, (θ' x : Y) = cp⁻¹ * θ (starConjTo hF cq hcq x) * cp := fun x => rfl
  have hτ : StarTau hF θ' := by
    intro x y
    rw [hval, hval, hval]
    have e : starConjTo hF cq hcq ⟨(x : Y) * y * x, LocalPoints.mul_mul_mem_localClass hF x y⟩ =
        ⟨(starConjTo hF cq hcq x : Y) * starConjTo hF cq hcq y * starConjTo hF cq hcq x,
          LocalPoints.mul_mul_mem_localClass hF _ _⟩ := by
      apply Subtype.ext
      show cq * ((x : Y) * y * x) * cq⁻¹ =
        (cq * x * cq⁻¹) * (cq * y * cq⁻¹) * (cq * x * cq⁻¹)
      group
    rw [e, hθ]
    group
  obtain ⟨m, hmt, hm⟩ := hrig θ' hτ
  refine ⟨cp * m * cq⁻¹, ?_, fun y => ?_⟩
  · rw [← hcq, ← hcp]
    calc cp * m * cq⁻¹ * (cq * t * cq⁻¹) * (cp * m * cq⁻¹)⁻¹ = cp * (m * t * m⁻¹) * cp⁻¹ := by
          group
      _ = cp * t * cp⁻¹ := by rw [hmt]
  · set x := (starConjTo hF cq hcq).symm y
    have hy : starConjTo hF cq hcq x = y := Equiv.apply_symm_apply _ _
    have h1 := hm x
    rw [hval, hy] at h1
    have hx : (x : Y) = cq⁻¹ * y * cq := starConjTo_symm_val hF cq hcq y
    calc (θ y : Y) = cp * (cp⁻¹ * θ y * cp) * cp⁻¹ := by group
      _ = cp * (m * x * m⁻¹) * cp⁻¹ := by rw [h1]
      _ = cp * m * cq⁻¹ * y * (cp * m * cq⁻¹)⁻¹ := by rw [hx]; group

theorem starRigid_of_model {Z : Type} [Group Z] {F' : Set Z} (hF : Pair Y F) (hF' : Pair Z F')
    {t : Y} (L : LocalPoints (pairModel hF') F t)
    (hrigF' : ∀ σ : tauGroup hF', σ ∈ (innerTau hF').range)
    (hlift : ∀ g : Z, ∃ m : Y, m * t * m⁻¹ = t ∧ ∀ x y : LocalClass F t,
      (y : Y) = m * x * m⁻¹ → (L.χ y : Z) = g * L.χ x * g⁻¹) :
    ∀ θ : LocalClass F t ≃ LocalClass F t, StarTau hF θ →
      ∃ m : Y, m * t * m⁻¹ = t ∧ ∀ x, (θ x : Y) = m * x * m⁻¹ := by
  intro θ hθ
  set σ : Equiv.Perm F' := L.χ.symm.trans (θ.trans L.χ) with hσdef
  have hσ : σ ∈ tauGroup hF' := by
    rw [mem_tauGroup]
    intro u v
    set x := L.χ.symm u
    set y := L.χ.symm v
    have hu : L.χ x = u := Equiv.apply_symm_apply _ _
    have hv : L.χ y = v := Equiv.apply_symm_apply _ _
    have h1 : tauE hF' u v = L.χ ⟨(x : Y) * y * x, LocalPoints.mul_mul_mem_localClass hF x y⟩ := by
      rw [L.tau x y, ← hu, ← hv]
      rfl
    have h2 : θ ⟨(x : Y) * y * x, LocalPoints.mul_mul_mem_localClass hF x y⟩ =
        ⟨(θ x : Y) * θ y * θ x, LocalPoints.mul_mul_mem_localClass hF (θ x) (θ y)⟩ :=
      Subtype.ext (hθ x y)
    have h3 : σ u = L.χ (θ x) := rfl
    have h4 : σ v = L.χ (θ y) := rfl
    have h5 : σ (L.χ ⟨(x : Y) * y * x, LocalPoints.mul_mul_mem_localClass hF x y⟩) =
        L.χ (θ ⟨(x : Y) * y * x, LocalPoints.mul_mul_mem_localClass hF x y⟩) := by
      show L.χ (θ (L.χ.symm (L.χ _))) = _
      rw [Equiv.symm_apply_apply]
    rw [h1, h3, h4, h5, h2, L.tau (θ x) (θ y)]
    rfl
  obtain ⟨g, hg⟩ := hrigF' ⟨σ, hσ⟩
  obtain ⟨m, hmt, hm⟩ := hlift g
  refine ⟨m, hmt, fun x => ?_⟩
  have hy : m * x * m⁻¹ ∈ LocalClass F t := by
    have := (Pair.conj_mem_localClass_iff hF m (e := t) (f := (x : Y))).2 x.2
    rwa [hmt] at this
  have e1 : (L.χ ⟨m * x * m⁻¹, hy⟩ : Z) = g * L.χ x * g⁻¹ := hm x ⟨_, hy⟩ rfl
  have e2 : (L.χ (θ x) : Z) = g * L.χ x * g⁻¹ := by
    have h5 : L.χ (θ x) = σ (L.χ x) := by
      show L.χ (θ x) = L.χ (θ (L.χ.symm (L.χ x)))
      rw [Equiv.symm_apply_apply]
    rw [h5, ← innerTau_apply hF' g, hg]
  have e3 : θ x = ⟨m * x * m⁻¹, hy⟩ := L.χ.injective (Subtype.ext (e2.trans e1.symm))
  rw [e3]

end CFSG.Fischer
