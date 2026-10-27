module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusPlane
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthMinusSec

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus

open Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

section Cyclic

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem omega_apply_coord {g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)} (hg : IsOmegaTwisted b c g 0)
    (w : Fin 2 → K) :
    g w 0 = g (Pi.single 0 1) 0 * w 0 + g (Pi.single 0 1) 1 * (c * w 1) ∧
      g w 1 = g (Pi.single 0 1) 0 * w 1 + g (Pi.single 0 1) 1 * (w 0 + b * w 1) := by
  have h := LinearMap.congr_fun (eq_of_isOmegaTwisted_zero hg) w
  constructor
  · have h0 := congrFun h 0
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe, minusOmegaMul_apply_zero] using h0
  · have h1 := congrFun h 1
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe, minusOmegaMul_apply_one] using h1

open Polynomial in
@[expose] noncomputable def omegaPoly (b c : K) : K[X] := X ^ 2 + C b * X + C c

open Polynomial in
theorem omegaPoly_monic : (omegaPoly b c).Monic := by
  unfold omegaPoly
  monicity!

open Polynomial in
theorem omegaPoly_natDegree : (omegaPoly b c).natDegree = 2 := by
  unfold omegaPoly
  compute_degree!

open Polynomial in
theorem omegaPoly_irreducible (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Irreducible (omegaPoly b c) := by
  rw [omegaPoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [omegaPoly_natDegree]) (by rw [omegaPoly_natDegree]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun s hs => ?_
  rw [mem_roots omegaPoly_monic.ne_zero] at hs
  have h := hs.eq_zero
  simp only [omegaPoly, eval_add, eval_pow, eval_X, eval_mul, eval_C] at h
  exact hirr s h

theorem isCyclic_omegaRotations (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsCyclic ↥(omegaRotations b c) := by
  haveI : Fact (Irreducible (omegaPoly b c)) := ⟨omegaPoly_irreducible hirr⟩
  haveI : Finite ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) := finite_orthLinearEquiv
  let ω : AdjoinRoot (omegaPoly b c) := AdjoinRoot.root (omegaPoly b c)
  have h0 : ω ^ 2 + algebraMap K (AdjoinRoot (omegaPoly b c)) b * ω +
      algebraMap K (AdjoinRoot (omegaPoly b c)) c = 0 := by
    have h : AdjoinRoot.mk (omegaPoly b c) (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
        Polynomial.C c) = 0 := AdjoinRoot.mk_self
    simpa only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
      AdjoinRoot.algebraMap_eq] using h
  have hCharF : CharP (AdjoinRoot (omegaPoly b c)) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (omegaPoly b c))).injective 2
  have h2F : (2 : AdjoinRoot (omegaPoly b c)) = 0 := CharTwo.two_eq_zero
  have hω : ω ^ 2 = algebraMap K (AdjoinRoot (omegaPoly b c)) b * ω +
      algebraMap K (AdjoinRoot (omegaPoly b c)) c := by
    linear_combination h0 - (algebraMap K (AdjoinRoot (omegaPoly b c)) b * ω +
      algebraMap K (AdjoinRoot (omegaPoly b c)) c) * h2F
  have hli : ∀ x y : K, algebraMap K (AdjoinRoot (omegaPoly b c)) x +
      algebraMap K (AdjoinRoot (omegaPoly b c)) y * ω = 0 → x = 0 ∧ y = 0 := by
    intro x y h
    by_cases hy : y = 0
    · subst hy
      simp only [map_zero, zero_mul, add_zero] at h
      exact ⟨(map_eq_zero_iff _ (algebraMap K (AdjoinRoot (omegaPoly b c))).injective).1 h, rfl⟩
    · exfalso
      have hy' : algebraMap K (AdjoinRoot (omegaPoly b c)) y ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap K (AdjoinRoot (omegaPoly b c))).injective).2 hy
      have hωs : ω = algebraMap K (AdjoinRoot (omegaPoly b c)) (-x / y) := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination h
      rw [hωs] at h0
      have : algebraMap K (AdjoinRoot (omegaPoly b c)) ((-x / y) ^ 2 + b * (-x / y) + c) = 0 := by
        simpa using h0
      exact hirr (-x / y)
        ((map_eq_zero_iff _ (algebraMap K (AdjoinRoot (omegaPoly b c))).injective).1 this)
  let φ : ↥(omegaRotations b c) →* AdjoinRoot (omegaPoly b c) :=
    { toFun := fun g => algebraMap K (AdjoinRoot (omegaPoly b c))
          ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 0) +
        algebraMap K (AdjoinRoot (omegaPoly b c))
          ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 1) * ω
      map_one' := by simp
      map_mul' := by
        intro g g'
        have hg : IsOmegaTwisted b c (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) 0 := g.2
        obtain ⟨e0, e1⟩ := omega_apply_coord hg
          ((g' : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1))
        have hmul : ((g * g' : ↥(omegaRotations b c)) : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
            (Pi.single 0 1) = (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
              ((g' : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1)) := rfl
        simp only [hmul, e0, e1, map_add, map_mul]
        linear_combination (-(algebraMap K (AdjoinRoot (omegaPoly b c))
          ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 1) *
          algebraMap K (AdjoinRoot (omegaPoly b c))
          ((g' : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 1))) * hω }
  have hinj : Function.Injective φ := by
    intro g g' h
    have h' : algebraMap K (AdjoinRoot (omegaPoly b c))
        ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 0 -
          (g' : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 0) +
        algebraMap K (AdjoinRoot (omegaPoly b c))
          ((g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 1 -
            (g' : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (Pi.single 0 1) 1) * ω = 0 := by
      have : φ g - φ g' = 0 := sub_eq_zero.2 h
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, map_sub] at this ⊢
      linear_combination this
    obtain ⟨h1, h2⟩ := hli _ _ h'
    refine Subtype.ext (LinearEquiv.toLinearMap_injective ?_)
    rw [eq_of_isOmegaTwisted_zero g.2, eq_of_isOmegaTwisted_zero g'.2, sub_eq_zero.1 h1,
      sub_eq_zero.1 h2]
  exact isCyclic_of_injective_ringHom φ hinj

end Cyclic

section Pm

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r : ℕ} {t : ℕ} (ht : t ≤ r)
  (hm0 : r - t = 0)

local notation "𝕍" => (Fin r ⊕ Fin r → K) × (Fin 2 → K)

include hm0 in
theorem pmHom_eq_one_iff {g : 𝕍 ≃ₗ[K] 𝕍} (hg : g ∈ G0 (K := K) (r := r) ht) :
    pmHom ht hm0 ⟨g, hg⟩ = 1 ↔ TrivRes ht g := by
  constructor
  · intro h1 v hv
    have hpm : ∀ a, (g ((0 : Fin r ⊕ Fin r → K), a)).2 = a := fun a => by
      have := LinearEquiv.congr_fun h1 a
      exact this
    have hF0 := fst_mem_tailFlag_of_isResPerp ht hm0 hv
    have h1' : g ((v.1, 0) : 𝕍) - ((v.1, 0) : 𝕍) ∈ tailFlag K (Fin 2 → K) r t :=
      Submodule.sub_mem _ ((hg.1 _).2 hF0) hF0
    have hp : IsResPerp ht (g ((0 : Fin r ⊕ Fin r → K), v.2)) :=
      (hg.2 _).2 (fun i => by simp)
    have hF1 := fst_mem_tailFlag_of_isResPerp ht hm0 hp
    have h3 : g ((0 : Fin r ⊕ Fin r → K), v.2) - ((0 : Fin r ⊕ Fin r → K), v.2) =
        ((g ((0 : Fin r ⊕ Fin r → K), v.2)).1, 0) := by
      ext
      · simp
      · simp [hpm]
    have hdec : v = ((v.1, 0) : 𝕍) + ((0 : Fin r ⊕ Fin r → K), v.2) := by
      ext <;> simp
    have h4 : g v - v = (g ((v.1, 0) : 𝕍) - ((v.1, 0) : 𝕍)) +
        (g ((0 : Fin r ⊕ Fin r → K), v.2) - ((0 : Fin r ⊕ Fin r → K), v.2)) := by
      conv_lhs => rw [hdec, map_add]
      abel
    rw [h4, h3]
    exact Submodule.add_mem _ h1' hF1
  · intro h
    refine LinearEquiv.ext fun a => ?_
    have h' := h ((0 : Fin r ⊕ Fin r → K), a) (fun i => by simp)
    have h2 := (mem_tailFlag_iff.1 h').2
    simp only [Prod.snd_sub] at h2
    exact sub_eq_zero.1 h2

include hm0 in
theorem pmHom_isOmegaTwisted (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {g : 𝕍 ≃ₗ[K] 𝕍}
    (hg : g ∈ G0 (K := K) (r := r) ht)
    (hq : ∀ v, quadTail r (minusTailForm K b c) (g v) = quadTail r (minusTailForm K b c) v)
    {N : ℕ} (hN : Odd N) (hgN : g ^ N = 1) :
    IsOmegaTwisted b c (pmHom ht hm0 ⟨g, hg⟩) 0 := by
  refine plane_isOmegaTwisted_zero hirr hN (pmHom ht hm0 ⟨g, hg⟩) 1 (fun a' => ?_) (s := 1)
    (fun a' => ?_)
  · have h1 := hq ((0 : Fin r ⊕ Fin r → K), a')
    have hperp : IsResPerp ht (g ((0 : Fin r ⊕ Fin r → K), a')) :=
      (hg.2 _).2 (fun i => by simp)
    rw [quadTail_eq_of_fst_mem (fst_mem_tailFlag_of_isResPerp ht hm0 hperp), quadTail_tail] at h1
    rw [one_mul]
    exact h1
  · have h1 : (pmHom ht hm0 ⟨g, hg⟩) ^ N = 1 := by
      rw [← map_pow]
      have : (⟨g, hg⟩ : ↥(G0 (K := K) (r := r) ht)) ^ N = 1 := Subtype.ext (by simpa using hgN)
      rw [this, map_one]
    rw [h1]
    simp

end Pm

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus
