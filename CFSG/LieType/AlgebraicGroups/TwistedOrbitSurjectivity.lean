module

public import CFSG.LieType.AlgebraicGroups.InnerTwistDifferential
public import CFSG.LieType.AlgebraicGroups.SmoothTangentOpen

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open Coalgebra Bialgebra HopfAlgebra TensorProduct WithConv

section Transfer

variable {k : Type} [Field k] {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

theorem tangentMap_bijective_of_comp_eq_id (ψ : B →ₐ[k] A) (ψ' : A →ₐ[k] B)
    (h₁ : ψ.comp ψ' = AlgHom.id k A) (h₂ : ψ'.comp ψ = AlgHom.id k B) {x : A →ₐ[k] k}
    {y : B →ₐ[k] k} (h : x.comp ψ = y) : Function.Bijective (tangentMap ψ h) := by
  have h' : y.comp ψ' = x := by rw [← h, AlgHom.comp_assoc, h₁, AlgHom.comp_id]
  refine Function.bijective_iff_has_inverse.2 ⟨tangentMap ψ' h', fun D => ?_, fun E => ?_⟩
  · refine Subtype.ext (LinearMap.ext fun a => ?_)
    change (D : A →ₗ[k] k) (ψ (ψ' a)) = (D : A →ₗ[k] k) a
    rw [← AlgHom.comp_apply, h₁, AlgHom.id_apply]
  · refine Subtype.ext (LinearMap.ext fun b => ?_)
    change (E : B →ₗ[k] k) (ψ' (ψ b)) = (E : B →ₗ[k] k) b
    rw [← AlgHom.comp_apply, h₂, AlgHom.id_apply]

theorem tangentMap_bijective_of_comp_eq (φ : B →ₐ[k] A) {α α' : A →ₐ[k] A} {β β' : B →ₐ[k] B}
    (hα : α.comp α' = AlgHom.id k A) (hα' : α'.comp α = AlgHom.id k A)
    (hβ : β.comp β' = AlgHom.id k B) (hβ' : β'.comp β = AlgHom.id k B)
    (hcomm : α.comp φ = φ.comp β) {x x' : A →ₐ[k] k} (hx' : x.comp α = x')
    (hx : Function.Bijective (tangentMap φ (rfl : x.comp φ = x.comp φ))) :
    Function.Bijective (tangentMap φ (rfl : x'.comp φ = x'.comp φ)) := by
  subst hx'
  have e₁ : (x.comp α).comp α' = x := by rw [AlgHom.comp_assoc, hα, AlgHom.comp_id]
  have e₃ : (x.comp φ).comp β = (x.comp α).comp φ := by
    rw [AlgHom.comp_assoc, ← hcomm, AlgHom.comp_assoc]
  have hfac : (tangentMap φ (rfl : (x.comp α).comp φ = (x.comp α).comp φ) :
      TangentSpace k A (x.comp α) → TangentSpace k B ((x.comp α).comp φ)) =
      tangentMap β e₃ ∘ tangentMap φ (rfl : x.comp φ = x.comp φ) ∘ tangentMap α' e₁ := by
    funext D
    refine Subtype.ext (LinearMap.ext fun b => ?_)
    change (D : A →ₗ[k] k) (φ b) = (D : A →ₗ[k] k) (α' (φ (β b)))
    rw [← AlgHom.comp_apply φ β, ← hcomm, AlgHom.comp_apply, ← AlgHom.comp_apply α' α, hα',
      AlgHom.id_apply]
  rw [hfac]
  exact (tangentMap_bijective_of_comp_eq_id β β' hβ hβ' e₃).comp
    (hx.comp (tangentMap_bijective_of_comp_eq_id α' α hα' hα e₁))

end Transfer

section Group

variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A]

theorem constPoint_inv (a : WithConv (A →ₐ[k] k)) : constPoint a⁻¹ = (constPoint a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← constPoint_mul, inv_mul_cancel, constPoint_one])

theorem algHom_comp_constPoint (f : A →ₐ[k] A) (a : WithConv (A →ₐ[k] k)) :
    toConv (f.comp (constPoint a).ofConv) = constPoint a := by
  rw [comp_constPoint]
  rfl

@[expose] def biTransCo (a b : WithConv (A →ₐ[k] k)) : A →ₐ[k] A :=
  (constPoint a * toConv (AlgHom.id k A) * constPoint b).ofConv

theorem toConv_biTransCo (a b : WithConv (A →ₐ[k] k)) :
    toConv (biTransCo a b) = constPoint a * toConv (AlgHom.id k A) * constPoint b := by
  unfold biTransCo
  rw [toConv_ofConv]

theorem algHom_comp_biTransCo (f : A →ₐ[k] A) (a b : WithConv (A →ₐ[k] k)) :
    toConv (f.comp (biTransCo a b)) = constPoint a * toConv f * constPoint b := by
  unfold biTransCo
  rw [AlgHom.comp_convMul_distrib, toConv_ofConv, AlgHom.comp_convMul_distrib, toConv_ofConv,
    algHom_comp_constPoint, algHom_comp_constPoint, ofConv_toConv, AlgHom.comp_id]

theorem point_comp_biTransCo (a b h : WithConv (A →ₐ[k] k)) :
    toConv (h.ofConv.comp (biTransCo a b)) = a * h * b := by
  unfold biTransCo
  rw [AlgHom.comp_convMul_distrib, toConv_ofConv, AlgHom.comp_convMul_distrib, toConv_ofConv,
    point_comp_constPoint, point_comp_constPoint, ofConv_toConv, AlgHom.comp_id]

theorem counit_comp_biTransCo (a b : WithConv (A →ₐ[k] k)) :
    (counitAlgHom k A).comp (biTransCo a b) = (a * b).ofConv := by
  have h := point_comp_biTransCo a b 1
  rw [convOne_ofConv_eq_counit, mul_one] at h
  have h' := congrArg ofConv h
  simpa only [ofConv_toConv] using h'

theorem biTransCo_comp (a b a' b' : WithConv (A →ₐ[k] k)) :
    (biTransCo a b).comp (biTransCo a' b') = biTransCo (a' * a) (b * b') := by
  apply toConv_injective
  rw [algHom_comp_biTransCo, toConv_biTransCo, toConv_biTransCo, constPoint_mul, constPoint_mul]
  simp only [mul_assoc]

theorem biTransCo_one : biTransCo (1 : WithConv (A →ₐ[k] k)) 1 = AlgHom.id k A := by
  unfold biTransCo
  rw [constPoint_one, one_mul, mul_one, ofConv_toConv]

theorem biTransCo_comp_inv (a b : WithConv (A →ₐ[k] k)) :
    (biTransCo a b).comp (biTransCo a⁻¹ b⁻¹) = AlgHom.id k A := by
  rw [biTransCo_comp, inv_mul_cancel, mul_inv_cancel, biTransCo_one]

theorem biTransCo_inv_comp (a b : WithConv (A →ₐ[k] k)) :
    (biTransCo a⁻¹ b⁻¹).comp (biTransCo a b) = AlgHom.id k A := by
  rw [biTransCo_comp, mul_inv_cancel, inv_mul_cancel, biTransCo_one]

theorem rightTransCo_eq_biTransCo (a : WithConv (A →ₐ[k] k)) :
    rightTransCo a = biTransCo 1 a := by
  unfold rightTransCo biTransCo
  rw [constPoint_one, one_mul]

theorem toConv_biTransCo_comp_bialgHom (σ : A →ₐc[k] A) (a b : WithConv (A →ₐ[k] k)) :
    toConv ((biTransCo a b).comp (σ : A →ₐ[k] A)) =
      constPoint (pointMap σ a) * toConv (σ : A →ₐ[k] A) * constPoint (pointMap σ b) := by
  unfold biTransCo
  rw [AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv, AlgHom.convMul_comp_bialgHom_distrib,
    toConv_ofConv, ofConv_toConv, AlgHom.id_comp]
  rfl

theorem biTransCo_comp_twistOrbitCo (σ : A →ₐc[k] A) (x a : WithConv (A →ₐ[k] k)) :
    (biTransCo a 1).comp (twistOrbitCo σ x) =
      (twistOrbitCo σ x).comp (biTransCo a (pointMap σ a)⁻¹) := by
  apply toConv_injective
  rw [algHom_comp_biTransCo, constPoint_inv]
  have hL : toConv ((biTransCo a 1).comp (twistOrbitCo σ x)) =
      toConv (biTransCo a 1) * constPoint x *
        (toConv ((biTransCo a 1).comp (σ : A →ₐ[k] A)))⁻¹ := by
    unfold twistOrbitCo
    rw [AlgHom.comp_convMul_distrib, toConv_ofConv, AlgHom.comp_convMul_distrib, toConv_ofConv,
      ofConv_toConv, AlgHom.comp_id, algHom_comp_constPoint, comp_convInv, toConv_ofConv,
      ofConv_toConv]
  rw [hL, toConv_biTransCo_comp_bialgHom, toConv_biTransCo]
  unfold twistOrbitCo
  simp only [toConv_ofConv, map_one, constPoint_one]
  group

theorem exists_comp_twistOrbitCo_iff (σ : A →ₐc[k] A) (x : WithConv (A →ₐ[k] k))
    (y : A →ₐ[k] k) :
    (∃ h : A →ₐ[k] k, h.comp (twistOrbitCo σ x) = y) ↔
      ∃ h : WithConv (A →ₐ[k] k), toConv y = h * x * (pointMap σ h)⁻¹ := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨toConv h, point_comp_twistOrbitCo σ x (toConv h)⟩
  · rintro ⟨h, hy⟩
    exact ⟨h.ofConv, toConv_injective ((point_comp_twistOrbitCo σ x h).trans hy.symm)⟩

theorem tangentMap_twistOrbitCo_bijective (σ : A →ₐc[k] A) {m : ℕ} (hm : 1 ≤ m)
    (hS : ∀ D ∈ tangentSpace k A (counitAlgHom k A),
      D ∘ₗ ((σ : A →ₐ[k] A) ^ m).toLinearMap = 0)
    (x : WithConv (A →ₐ[k] k)) (y : A →ₐ[k] k) :
    Function.Bijective (tangentMap (twistOrbitCo σ x)
      (rfl : y.comp (twistOrbitCo σ x) = y.comp (twistOrbitCo σ x))) := by
  obtain ⟨-, -, -, h₁, h₂, -, -, hR, hdiff⟩ :=
    exceptional_Lang_inner_twist_nilpotent_differential σ hm hS x
  set N := tangentMap ((σ : A →ₐ[k] A).comp (innerCo x)) (counit_comp_twist σ x)
  have hIN : Function.Bijective
      ((1 : Module.End k (TangentSpace k A (counitAlgHom k A))) - N) := by
    refine Function.bijective_iff_has_inverse.2
      ⟨⇑(∑ i ∈ Finset.range m, N ^ i : Module.End k (TangentSpace k A (counitAlgHom k A))),
        fun v => ?_, fun v => ?_⟩
    · change ((∑ i ∈ Finset.range m, N ^ i) *
        ((1 : Module.End k (TangentSpace k A (counitAlgHom k A))) - N)) v = v
      rw [h₂]
      rfl
    · change (((1 : Module.End k (TangentSpace k A (counitAlgHom k A))) - N) *
        ∑ i ∈ Finset.range m, N ^ i) v = v
      rw [h₁]
      rfl
  have hR' : ((counitAlgHom k A).comp (twistOrbitCo σ x)).comp (rightTransCo x⁻¹) =
      counitAlgHom k A := by
    rw [AlgHom.comp_assoc]
    exact hR
  have hRbij : Function.Bijective (tangentMap (rightTransCo x⁻¹) hR') := by
    refine tangentMap_bijective_of_comp_eq_id _ (rightTransCo x) ?_ ?_ hR'
    · rw [rightTransCo_eq_biTransCo, rightTransCo_eq_biTransCo, biTransCo_comp, one_mul,
        inv_mul_cancel, biTransCo_one]
    · rw [rightTransCo_eq_biTransCo, rightTransCo_eq_biTransCo, biTransCo_comp, one_mul,
        mul_inv_cancel, biTransCo_one]
  have hc : tangentMap ((twistOrbitCo σ x).comp (rightTransCo x⁻¹)) hR =
      (tangentMap (rightTransCo x⁻¹) hR').comp (tangentMap (twistOrbitCo σ x)
        (rfl : (counitAlgHom k A).comp (twistOrbitCo σ x) =
          (counitAlgHom k A).comp (twistOrbitCo σ x))) :=
    tangentMap_comp _ _ rfl hR'
  have hε : Function.Bijective (tangentMap (twistOrbitCo σ x)
      (rfl : (counitAlgHom k A).comp (twistOrbitCo σ x) =
        (counitAlgHom k A).comp (twistOrbitCo σ x))) := by
    have h := hIN
    rw [← hdiff, hc, LinearMap.coe_comp] at h
    exact (Function.Bijective.of_comp_iff' hRbij _).1 h
  have hy : (counitAlgHom k A).comp (biTransCo (toConv y) 1) = y := by
    rw [counit_comp_biTransCo, mul_one]
  exact tangentMap_bijective_of_comp_eq (twistOrbitCo σ x) (biTransCo_comp_inv (toConv y) 1)
    (biTransCo_inv_comp (toConv y) 1) (biTransCo_comp_inv (toConv y) (pointMap σ (toConv y))⁻¹)
    (biTransCo_inv_comp (toConv y) (pointMap σ (toConv y))⁻¹)
    (biTransCo_comp_twistOrbitCo σ x (toConv y)) hy hε


theorem exceptional_Lang_connected_twisted_orbit_surjectivity [IsAlgClosed k]
    [Algebra.FiniteType k A] [Algebra.Smooth k A] [ConnectedSpace (PrimeSpectrum A)]
    (σ : A →ₐc[k] A) {m : ℕ} (hm : 1 ≤ m)
    (hS : ∀ D ∈ tangentSpace k A (counitAlgHom k A),
      D ∘ₗ ((σ : A →ₐ[k] A) ^ m).toLinearMap = 0)
    (x : WithConv (A →ₐ[k] k)) :
    ∃ h : WithConv (A →ₐ[k] k), x = h⁻¹ * pointMap σ h := by
  classical
  have hopen : ∀ x : WithConv (A →ₐ[k] k), ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ y : A →ₐ[k] k, (⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum A) ∈ U ↔
        ∃ h : WithConv (A →ₐ[k] k), toConv y = h * x * (pointMap σ h)⁻¹ := by
    intro x
    obtain ⟨-, -, U, hU, hUeq⟩ := (exceptional_Lang_smooth_tangent_isomorphism_open
      (twistOrbitCo σ x)).2 (tangentMap_twistOrbitCo_bijective σ hm hS x)
    refine ⟨U, hU, fun y => ?_⟩
    rw [← exists_comp_twistOrbitCo_iff]
    have h := Set.ext_iff.1 hUeq y
    simp only [Set.mem_ofPred_eq] at h
    exact h.symm
  choose U hUo hU using hopen
  set Q : WithConv (A →ₐ[k] k) → Prop := fun y => ∃ h, y = h⁻¹ * pointMap σ h with hQ
  have hU1 : ∀ y : A →ₐ[k] k,
      (⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum A) ∈ U 1 ↔ Q (toConv y) := by
    intro y
    rw [hU]
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨h⁻¹, ?_⟩
      rw [hh, map_inv, inv_inv, mul_one]
    · rintro ⟨h, hh⟩
      refine ⟨h⁻¹, ?_⟩
      rw [hh, map_inv, inv_inv, mul_one]
  have hsep : ∀ (x' : WithConv (A →ₐ[k] k)) (y : A →ₐ[k] k), ¬ Q x' →
      (⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum A) ∈ U x' → ¬ Q (toConv y) := by
    intro x' y hx' hy hQy
    obtain ⟨h, hh⟩ := (hU x' y).1 hy
    obtain ⟨g, hg⟩ := hQy
    apply hx'
    refine ⟨g * h, ?_⟩
    rw [map_mul]
    calc x' = h⁻¹ * (h * x' * (pointMap σ h)⁻¹) * pointMap σ h := by group
      _ = (g * h)⁻¹ * (pointMap σ g * pointMap σ h) := by rw [← hh, hg]; group
  have hself : ∀ y : A →ₐ[k] k,
      (⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum A) ∈ U (toConv y) :=
    fun y => (hU (toConv y) y).2 ⟨1, by rw [map_one, inv_one, one_mul, mul_one]⟩
  set W : Set (PrimeSpectrum A) := ⋃ (x' : WithConv (A →ₐ[k] k)) (_ : ¬ Q x'), U x' with hW
  have hWo : IsOpen W := isOpen_iUnion fun x' => isOpen_iUnion fun _ => hUo x'
  have hmemW : ∀ y : A →ₐ[k] k,
      (⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum A) ∈ W → ¬ Q (toConv y) := by
    intro y hy
    obtain ⟨x', hx', hyx'⟩ := Set.mem_iUnion₂.1 hy
    exact hsep x' y hx' hyx'
  have hdisj : U 1 ∩ W = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := exists_algHom_mem_of_isLocallyClosed k A ((hUo 1).inter hWo).isLocallyClosed
      (Set.nonempty_iff_ne_empty.2 hne)
    exact hmemW y hy.2 ((hU1 y).1 hy.1)
  have hcover : U 1 ∪ W = Set.univ := by
    by_contra hne
    obtain ⟨y, hy⟩ := exists_algHom_mem_of_isLocallyClosed k A
      ((hUo 1).union hWo).isClosed_compl.isLocallyClosed (Set.nonempty_compl.2 hne)
    apply hy
    by_cases hQy : Q (toConv y)
    · exact Or.inl ((hU1 y).2 hQy)
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨toConv y, hQy, hself y⟩)
  have hcompl : (U 1)ᶜ = W := by
    ext p
    constructor
    · intro hp
      have hp' : p ∈ U 1 ∪ W := hcover ▸ Set.mem_univ p
      rcases hp' with hp' | hp'
      · exact absurd hp' hp
      · exact hp'
    · intro hp hp1
      have hpW : p ∈ U 1 ∩ W := ⟨hp1, hp⟩
      rw [hdisj] at hpW
      exact hpW
  have hclopen : IsClopen (U 1) := ⟨by rw [← isOpen_compl_iff, hcompl]; exact hWo, hUo 1⟩
  by_contra hx
  have hxW : (⟨RingHom.ker x.ofConv, RingHom.ker_isPrime _⟩ : PrimeSpectrum A) ∈ W :=
    Set.mem_iUnion₂.2 ⟨x, hx, by simpa only [toConv_ofConv] using hself x.ofConv⟩
  rcases isClopen_iff.1 hclopen with h | h
  · have h1 : (⟨RingHom.ker (1 : WithConv (A →ₐ[k] k)).ofConv, RingHom.ker_isPrime _⟩ :
        PrimeSpectrum A) ∈ U 1 := (hU1 _).2 ⟨1, by rw [toConv_ofConv, map_one, inv_one, one_mul]⟩
    rw [h] at h1
    exact h1
  · have hx1 : (⟨RingHom.ker x.ofConv, RingHom.ker_isPrime _⟩ : PrimeSpectrum A) ∈ U 1 ∩ W :=
      ⟨h ▸ Set.mem_univ _, hxW⟩
    rw [hdisj] at hx1
    exact hx1

end Group

end CFSG.LieType.AlgebraicGroups
