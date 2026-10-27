module

public import CFSG.LinearAlgebra.RootGroupSL.Generation

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E V : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup V] [Module k V]
  [Module.Finite k V] [Module.Finite k E]

private lemma det_one_add_of_sq_eq_zero (N : V →ₗ[k] V) (h : N ∘ₗ N = 0) :
    LinearMap.det (LinearMap.id + N) = 1 := by
  have hsq : N ^ 2 = 0 := by
    rw [sq, Module.End.mul_eq_comp]
    exact h
  have hM : IsNilpotent (-N) := by
    refine ⟨2, ?_⟩
    rw [neg_sq, hsq]
  have hchar : (-N).charpoly = Polynomial.X ^ Module.finrank k V :=
    IsNilpotent.charpoly_eq_X_pow_finrank hM
  have heval := LinearMap.eval_charpoly (-N) (1 : k)
  rw [hchar] at heval
  simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow] at heval
  have hsub : (algebraMap k (V →ₗ[k] V)) (1 : k) - (-N) = LinearMap.id + N := by
    ext v
    simp
  rw [hsub] at heval
  exact heval.symm

private lemma rootElt_apply {X : Type} [AddCommGroup X] [Module k X] [Module.Finite k X]
    (t : E) (a : E) (y : X) (b : E) :
    (rootElt k X t) (a, y, b) = (a + t * b, y, b) :=
  rfl

private lemma rootNegElt_apply {X : Type} [AddCommGroup X] [Module k X] [Module.Finite k X]
    (t : E) (a : E) (y : X) (b : E) :
    (rootNegElt k X t) (a, y, b) = (a, y, b + t * a) :=
  rfl

@[expose] def datumElt (ι : E →ₗ[k] V) (π : V →ₗ[k] E) (h : ∀ t, π (ι t) = 0) (t : E) :
    SpecialLinearGroup k V :=
  ⟨LinearEquiv.ofLinear (LinearMap.id + ι ∘ₗ (LinearMap.mulLeft k t) ∘ₗ π)
    (LinearMap.id - ι ∘ₗ (LinearMap.mulLeft k t) ∘ₗ π)
    (by
      ext v
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.id_apply, LinearMap.mulLeft_apply]
      rw [show π (v - ι (t * π v)) = π v by rw [map_sub, h (t * π v), sub_zero]]
      abel)
    (by
      ext v
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.id_apply, LinearMap.mulLeft_apply]
      rw [show π (v + ι (t * π v)) = π v by rw [map_add, h (t * π v), add_zero]]
      abel),
    by
      apply Units.ext
      rw [LinearEquiv.coe_det, Units.val_one]
      have hNN : (ι ∘ₗ (LinearMap.mulLeft k t) ∘ₗ π) ∘ₗ
          (ι ∘ₗ (LinearMap.mulLeft k t) ∘ₗ π) = 0 := by
        ext v
        simp only [LinearMap.comp_apply, LinearMap.zero_apply]
        rw [h (LinearMap.mulLeft k t (π v))]
        simp
      exact det_one_add_of_sq_eq_zero (ι ∘ₗ (LinearMap.mulLeft k t) ∘ₗ π) hNN⟩

theorem datumElt_apply (ι : E →ₗ[k] V) (π : V →ₗ[k] E) (h : ∀ t, π (ι t) = 0) (t : E) (v : V) :
    (datumElt ι π h t : V ≃ₗ[k] V) v = v + ι (t * π v) := by
  rfl

theorem datumElt_add (ι : E →ₗ[k] V) (π : V →ₗ[k] E) (h : ∀ t, π (ι t) = 0) (s t : E) :
    datumElt ι π h (s + t) = datumElt ι π h s * datumElt ι π h t := by
  apply SpecialLinearGroup.ext
  intro v
  simp only [SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply]
  rw [datumElt_apply, datumElt_apply, datumElt_apply]
  rw [show π (v + ι (t * π v)) = π v by rw [map_add, h (t * π v), add_zero]]
  rw [add_mul, map_add]
  abel

theorem datumElt_zero (ι : E →ₗ[k] V) (π : V →ₗ[k] E) (h : ∀ t, π (ι t) = 0) :
    datumElt ι π h 0 = 1 := by
  apply SpecialLinearGroup.ext
  intro v
  simp only [datumElt_apply]
  simp

@[expose] def datumRoot (ι : E →ₗ[k] V) (π : V →ₗ[k] E) (h : ∀ t, π (ι t) = 0) :
    Subgroup (SpecialLinearGroup k V) :=
  Subgroup.closure (Set.range (datumElt ι π h))

theorem mem_datumRoot_iff (ι : E →ₗ[k] V) (π : V →ₗ[k] E) (h : ∀ t, π (ι t) = 0)
    {g : SpecialLinearGroup k V} : g ∈ datumRoot ι π h ↔ ∃ t, datumElt ι π h t = g := by
  let φ : Multiplicative E →* SpecialLinearGroup k V :=
    { toFun := fun x => datumElt ι π h (Multiplicative.toAdd x)
      map_one' := by rw [toAdd_one, datumElt_zero]
      map_mul' := by
        intro x y
        rw [toAdd_mul, datumElt_add] }
  have hrange : Set.range (datumElt ι π h) = (φ.range : Set (SpecialLinearGroup k V)) := by
    ext g
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨Multiplicative.ofAdd t, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Multiplicative.toAdd x, rfl⟩
  rw [datumRoot, hrange, Subgroup.closure_eq, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨Multiplicative.toAdd x, hx⟩
  · rintro ⟨t, ht⟩
    exact ⟨Multiplicative.ofAdd t, ht⟩

@[expose] def datumJ0 (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E) (h1 : ∀ t, π (ι t) = 0)
    (h4 : ∀ t, π₁ (ι₁ t) = 0) : Subgroup (SpecialLinearGroup k V) :=
  Subgroup.closure (Set.range (datumElt ι π h1) ∪ Set.range (datumElt ι₁ π₁ h4))

theorem datumRoot_le_datumJ0 (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E) (h1 : ∀ t, π (ι t) = 0)
    (h4 : ∀ t, π₁ (ι₁ t) = 0) : datumRoot ι π h1 ≤ datumJ0 ι ι₁ π π₁ h1 h4 :=
  Subgroup.closure_mono Set.subset_union_left

theorem isPGroup_datumRoot [CharP k 2] (ι : E →ₗ[k] V) (π : V →ₗ[k] E)
    (h : ∀ t, π (ι t) = 0) : IsPGroup 2 (datumRoot ι π h) := by
  haveI : CharP E 2 := charP_of_injective_algebraMap (algebraMap k E).injective 2
  intro g
  obtain ⟨t, ht⟩ := (mem_datumRoot_iff ι π h).mp g.2
  refine ⟨1, ?_⟩
  have hsq : datumElt ι π h t * datumElt ι π h t = 1 := by
    rw [← datumElt_add]
    have htt : t + t = 0 := CharTwo.add_self_eq_zero t
    rw [htt, datumElt_zero]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  show (g : SpecialLinearGroup k V) ^ 2 = 1
  rw [← ht, pow_two]
  exact hsq

theorem datumRoot_ne_bot (ι : E →ₗ[k] V) (π : V →ₗ[k] E) (h : ∀ t, π (ι t) = 0)
    (hι : Function.Injective ι) (hπ : π ≠ 0) : datumRoot ι π h ≠ ⊥ := by
  intro hbot
  obtain ⟨v, hv⟩ : ∃ v, π v ≠ 0 := by
    by_contra hc
    apply hπ
    ext w
    by_contra hw
    exact hc ⟨w, hw⟩
  have hmem : datumElt ι π h 1 ∈ datumRoot ι π h :=
    Subgroup.subset_closure ⟨1, rfl⟩
  rw [hbot] at hmem
  have hone : datumElt ι π h 1 = 1 := Subgroup.mem_bot.mp hmem
  have hιπ : ι (π v) ≠ 0 := by
    intro hz
    apply hv
    apply hι
    rw [hz, map_zero]
  have hne : datumElt ι π h 1 ≠ 1 := by
    intro h1
    have happ : (datumElt ι π h 1 : V ≃ₗ[k] V) v = (1 : V ≃ₗ[k] V) v := by
      rw [h1]
      rfl
    rw [datumElt_apply] at happ
    simp only [LinearMap.mulLeft_apply, one_mul, LinearEquiv.coe_one, LinearMap.id_coe,
      id_eq] at happ
    apply hιπ
    have h0 : v + ι (π v) = v + 0 := by simpa using happ
    exact add_left_cancel h0
  exact hne hone

private def datumX (π π₁ : V →ₗ[k] E) : Submodule k V :=
  LinearMap.ker π ⊓ LinearMap.ker π₁

private lemma mem_datumX {π π₁ : V →ₗ[k] E} {v : V} :
    v ∈ datumX π π₁ ↔ π v = 0 ∧ π₁ v = 0 := by
  rw [datumX, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker]

private def datumMidV (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E) : V →ₗ[k] V :=
  LinearMap.id - ι ∘ₗ π₁ - ι₁ ∘ₗ π

private lemma datumMidV_mem (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0) (v : V) :
    datumMidV ι ι₁ π π₁ v ∈ datumX π π₁ := by
  rw [mem_datumX]
  constructor
  · simp only [datumMidV, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
    rw [map_sub, map_sub, h1 (π₁ v), h2 (π v)]
    abel
  · simp only [datumMidV, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
    rw [map_sub, map_sub, h3 (π₁ v), h4 (π v)]
    abel

private def datumMid (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0) :
    V →ₗ[k] ↥(datumX π π₁) :=
  (datumMidV ι ι₁ π π₁).codRestrict (datumX π π₁) (datumMidV_mem ι ι₁ π π₁ h1 h2 h3 h4)

private def datumF (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0) :
    V →ₗ[k] DSpace E ↥(datumX π π₁) :=
  π₁.prod ((datumMid ι ι₁ π π₁ h1 h2 h3 h4).prod π)

private def datumG (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E) :
    DSpace E ↥(datumX π π₁) →ₗ[k] V :=
  (ι ∘ₗ LinearMap.fst k E (↥(datumX π π₁) × E))
    + ((Submodule.subtype (datumX π π₁)) ∘ₗ
        (LinearMap.fst k ↥(datumX π π₁) E ∘ₗ
          LinearMap.snd k E (↥(datumX π π₁) × E)))
    + (ι₁ ∘ₗ (LinearMap.snd k ↥(datumX π π₁) E ∘ₗ
        LinearMap.snd k E (↥(datumX π π₁) × E)))

private lemma datumF_apply (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0) (v : V) :
    datumF ι ι₁ π π₁ h1 h2 h3 h4 v
      = (π₁ v, datumMid ι ι₁ π π₁ h1 h2 h3 h4 v, π v) :=
  rfl

private lemma datumG_apply (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (a : E) (x : ↥(datumX π π₁)) (b : E) :
    datumG ι ι₁ π π₁ (a, x, b) = ι a + (x : V) + ι₁ b :=
  rfl

private lemma datumMid_apply (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0) (v : V) :
    (datumMid ι ι₁ π π₁ h1 h2 h3 h4 v : V) = datumMidV ι ι₁ π π₁ v :=
  rfl

private lemma pi_datumG (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (a : E) (x : ↥(datumX π π₁)) (b : E) :
    π (datumG ι ι₁ π π₁ (a, x, b)) = b := by
  rw [datumG_apply]
  have hx : π (x : V) = 0 := (mem_datumX.mp x.2).1
  rw [map_add, map_add, h1 a, hx, h2 b]
  abel

private lemma pi1_datumG (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0)
    (a : E) (x : ↥(datumX π π₁)) (b : E) :
    π₁ (datumG ι ι₁ π π₁ (a, x, b)) = a := by
  rw [datumG_apply]
  have hx : π₁ (x : V) = 0 := (mem_datumX.mp x.2).2
  rw [map_add, map_add, h3 a, hx, h4 b]
  abel

private lemma datumG_comp_datumF (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0) :
    (datumG ι ι₁ π π₁).comp (datumF ι ι₁ π π₁ h1 h2 h3 h4) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, LinearMap.id_apply, datumF_apply, datumG_apply,
    datumMid_apply, datumMidV]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
  abel

private lemma datumMid_datumG (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0)
    (a : E) (x : ↥(datumX π π₁)) (b : E) :
    (datumMid ι ι₁ π π₁ h1 h2 h3 h4 (datumG ι ι₁ π π₁ (a, x, b)) : V) = (x : V) := by
  rw [datumMid_apply, datumMidV]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
  rw [pi1_datumG ι ι₁ π π₁ h3 h4, pi_datumG ι ι₁ π π₁ h1 h2, datumG_apply]
  abel

private lemma datumMid_datumG_add_iota (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0)
    (a : E) (x : ↥(datumX π π₁)) (b s : E) :
    (datumMid ι ι₁ π π₁ h1 h2 h3 h4 (datumG ι ι₁ π π₁ (a, x, b) + ι s) : V) = (x : V) := by
  rw [datumMid_apply, datumMidV]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
  have hx1 : π₁ (datumG ι ι₁ π π₁ (a, x, b) + ι s) = a + s := by
    rw [map_add, pi1_datumG ι ι₁ π π₁ h3 h4, h3]
  have hx2 : π (datumG ι ι₁ π π₁ (a, x, b) + ι s) = b := by
    rw [map_add, pi_datumG ι ι₁ π π₁ h1 h2, h1, add_zero]
  rw [hx1, hx2, datumG_apply]
  simp only [map_add, add_zero, zero_add, sub_zero]
  abel

private lemma datumMid_datumG_add_iota₁ (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0)
    (a : E) (x : ↥(datumX π π₁)) (b s : E) :
    (datumMid ι ι₁ π π₁ h1 h2 h3 h4 (datumG ι ι₁ π π₁ (a, x, b) + ι₁ s) : V) = (x : V) := by
  rw [datumMid_apply, datumMidV]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
  have hx1 : π₁ (datumG ι ι₁ π π₁ (a, x, b) + ι₁ s) = a := by
    rw [map_add, pi1_datumG ι ι₁ π π₁ h3 h4, h4, add_zero]
  have hx2 : π (datumG ι ι₁ π π₁ (a, x, b) + ι₁ s) = b + s := by
    rw [map_add, pi_datumG ι ι₁ π π₁ h1 h2, h2]
  rw [hx1, hx2, datumG_apply]
  simp only [map_add, add_zero, zero_add, sub_zero]
  abel

private lemma datumF_comp_datumG (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0) :
    (datumF ι ι₁ π π₁ h1 h2 h3 h4).comp (datumG ι ι₁ π π₁) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  obtain ⟨a, x, b⟩ := v
  rw [LinearMap.comp_apply, LinearMap.id_apply, datumF_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [pi1_datumG ι ι₁ π π₁ h3 h4]
  · apply Subtype.ext
    exact datumMid_datumG ι ι₁ π π₁ h1 h2 h3 h4 a x b
  · rw [pi_datumG ι ι₁ π π₁ h1 h2]

private noncomputable def datumL (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0) :
    V ≃ₗ[k] DSpace E ↥(datumX π π₁) :=
  LinearEquiv.ofLinearMap (datumF ι ι₁ π π₁ h1 h2 h3 h4) (datumG ι ι₁ π π₁)
    (datumF_comp_datumG ι ι₁ π π₁ h1 h2 h3 h4)
    (datumG_comp_datumF ι ι₁ π π₁ h1 h2 h3 h4)

private lemma datumL_apply (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0) (v : V) :
    datumL ι ι₁ π π₁ h1 h2 h3 h4 v
      = (π₁ v, datumMid ι ι₁ π π₁ h1 h2 h3 h4 v, π v) :=
  rfl

private lemma datumL_symm_apply (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E)
    (h1 : ∀ t, π (ι t) = 0) (h2 : ∀ t, π (ι₁ t) = t)
    (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0)
    (a : E) (x : ↥(datumX π π₁)) (b : E) :
    (datumL ι ι₁ π π₁ h1 h2 h3 h4).symm (a, x, b) = datumG ι ι₁ π π₁ (a, x, b) :=
  rfl

theorem exists_datumEquiv (ι ι₁ : E →ₗ[k] V) (π π₁ : V →ₗ[k] E) (h1 : ∀ t, π (ι t) = 0)
    (h2 : ∀ t, π (ι₁ t) = t) (h3 : ∀ t, π₁ (ι t) = t) (h4 : ∀ t, π₁ (ι₁ t) = 0) :
    ∃ (X' : Type) (_ : AddCommGroup X') (_ : Module k X') (_ : Module.Finite k X')
      (e : SpecialLinearGroup k V ≃* SpecialLinearGroup k (DSpace E X')),
      (∀ t, e (datumElt ι π h1 t) = rootElt k X' t) ∧
      (∀ t, e (datumElt ι₁ π₁ h4 t) = rootNegElt k X' t) ∧
      Module.finrank k V = 2 * Module.finrank k E + Module.finrank k X' := by
  let X' : Type := ↥(datumX π π₁)
  have hroot : ∀ t, SpecialLinearGroup.congr_linearEquiv (datumL ι ι₁ π π₁ h1 h2 h3 h4)
      (datumElt ι π h1 t) = rootElt k X' t := by
    intro t
    apply SpecialLinearGroup.ext
    intro v
    obtain ⟨a, y, b⟩ := v
    simp only [SpecialLinearGroup.congr_linearEquiv_apply_apply, datumL_symm_apply,
      datumElt_apply, datumL_apply, rootElt_apply]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change π₁ (datumG ι ι₁ π π₁ (a, y, b) +
          ι (t * π (datumG ι ι₁ π π₁ (a, y, b)))) = a + t * b
      rw [map_add, pi1_datumG ι ι₁ π π₁ h3 h4, pi_datumG ι ι₁ π π₁ h1 h2, h3]
    · apply Subtype.ext
      exact datumMid_datumG_add_iota ι ι₁ π π₁ h1 h2 h3 h4 a y b _
    · change π (datumG ι ι₁ π π₁ (a, y, b) +
          ι (t * π (datumG ι ι₁ π π₁ (a, y, b)))) = b
      rw [map_add, pi_datumG ι ι₁ π π₁ h1 h2, h1]
      abel
  have hrootNeg : ∀ t, SpecialLinearGroup.congr_linearEquiv (datumL ι ι₁ π π₁ h1 h2 h3 h4)
      (datumElt ι₁ π₁ h4 t) = rootNegElt k X' t := by
    intro t
    apply SpecialLinearGroup.ext
    intro v
    obtain ⟨a, y, b⟩ := v
    simp only [SpecialLinearGroup.congr_linearEquiv_apply_apply, datumL_symm_apply,
      datumElt_apply, datumL_apply, rootNegElt_apply]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change π₁ (datumG ι ι₁ π π₁ (a, y, b) +
          ι₁ (t * π₁ (datumG ι ι₁ π π₁ (a, y, b)))) = a
      rw [map_add, pi1_datumG ι ι₁ π π₁ h3 h4, h4]
      abel
    · apply Subtype.ext
      exact datumMid_datumG_add_iota₁ ι ι₁ π π₁ h1 h2 h3 h4 a y b _
    · change π (datumG ι ι₁ π π₁ (a, y, b) +
          ι₁ (t * π₁ (datumG ι ι₁ π π₁ (a, y, b)))) = b + t * a
      rw [map_add, pi_datumG ι ι₁ π π₁ h1 h2, h2, pi1_datumG ι ι₁ π π₁ h3 h4]
  have hfin' : Module.finrank k V = 2 * Module.finrank k E + Module.finrank k X' := by
    have hfin : Module.finrank k V = Module.finrank k (DSpace E X') :=
      (datumL ι ι₁ π π₁ h1 h2 h3 h4).finrank_eq
    rw [hfin]
    change Module.finrank k (E × X' × E) = 2 * Module.finrank k E + Module.finrank k X'
    rw [Module.finrank_prod, Module.finrank_prod]
    ring
  exact ⟨X', inferInstance, inferInstance, inferInstance,
    SpecialLinearGroup.congr_linearEquiv (datumL ι ι₁ π π₁ h1 h2 h3 h4),
    hroot, hrootNeg, hfin'⟩

end CFSG.LinearAlgebra.RootGroupSL
