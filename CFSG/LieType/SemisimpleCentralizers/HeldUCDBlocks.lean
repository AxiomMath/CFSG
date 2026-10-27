module

public import CFSG.LieType.SemisimpleCentralizers.HeldUCDPair

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix Polynomial

open scoped _root_.Classical

variable {L : Type} [Field L] {n : ℕ}

@[expose] noncomputable def Fset (s : Matrix (Fin n) (Fin n) L) (b : L[X] → L[X]) (F : Finset L[X]) :
    Finset L[X] :=
  by
    classical
    exact F.filter (fun f => Pmat s b F f ≠ 0)

section Blocks

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]}

theorem mem_Fset {f : L[X]} : f ∈ Fset s b F ↔ f ∈ F ∧ Pmat s b F f ≠ 0 := by
  simp [Fset, Finset.mem_filter]

theorem Pmat_idem_vec (H : PrimaryHyp τ s m F a b) {f : L[X]} (hf : f ∈ F) (x : Fin n → L) :
    Pmat s b F f *ᵥ (Pmat s b F f *ᵥ x) = Pmat s b F f *ᵥ x := by
  rw [Matrix.mulVec_mulVec, H.Pmat_idem hf]

theorem Pmat_mulVec_of_mem_ne (H : PrimaryHyp τ s m F a b) {f g : L[X]} (hf : f ∈ F) (hg : g ∈ F)
    (hne : f ≠ g) {y : Fin n → L} (hy : y ∈ Vf s b F g) : Pmat s b F f *ᵥ y = 0 := by
  have hy' : Pmat s b F g *ᵥ y = y := mem_Vf.mp hy
  calc Pmat s b F f *ᵥ y = Pmat s b F f *ᵥ (Pmat s b F g *ᵥ y) := by rw [hy']
    _ = (Pmat s b F f * Pmat s b F g) *ᵥ y := Matrix.mulVec_mulVec _ _ _
    _ = 0 := by rw [H.Pmat_orth hf hg hne, Matrix.zero_mulVec]

theorem sum_Pmat_mulVec (H : PrimaryHyp τ s m F a b) (x : Fin n → L) :
    ∑ f ∈ Fset s b F, Pmat s b F f *ᵥ x = x := by
  have h1 : ∑ f ∈ F, Pmat s b F f *ᵥ x = x := by
    rw [← Matrix.sum_mulVec, HeldUCD.sum_Pmat H.hirr H.hmon H.hprod H.hsm H.hab, Matrix.one_mulVec]
  rw [Fset, Finset.sum_filter]
  conv_rhs => rw [← h1]
  refine Finset.sum_congr rfl fun f hf => ?_
  by_cases h0 : Pmat s b F f = 0
  · simp [h0]
  · rw [if_pos h0]

theorem Pmat_idem_index (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) (x : Fin n → L) :
    Pmat s b F f.1 *ᵥ (Pmat s b F f.1 *ᵥ x) = Pmat s b F f.1 *ᵥ x :=
  Pmat_idem_vec H (mem_Fset.mp f.2).1 x

@[expose] noncomputable def prjB (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) :
    (Fin n → L) →ₗ[L] Vf s b F f.1 :=
  prjV s b F f.1 (Pmat_idem_index H f)

@[expose] noncomputable def inclB (f : ↥(Fset s b F)) : Vf s b F f.1 →ₗ[L] (Fin n → L) :=
  (Vf s b F f.1).subtype

@[expose] noncomputable def Bk (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F))
    (w : Vf s b F f.1 →ₗ[L] Vf s b F f.1) : (Fin n → L) →ₗ[L] (Fin n → L) :=
  inclB f ∘ₗ w ∘ₗ prjB H f

@[expose] noncomputable def rhoL (H : PrimaryHyp τ s m F a b)
    (w : (f : ↥(Fset s b F)) → Vf s b F f.1 →ₗ[L] Vf s b F f.1) : (Fin n → L) →ₗ[L] (Fin n → L) :=
  ∑ f, Bk H f (w f)

theorem prjB_incl_self (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) (y : Vf s b F f.1) :
    prjB H f (y : Fin n → L) = y :=
  prjV_incl _ y

theorem prjB_incl_ne (H : PrimaryHyp τ s m F a b) {f g : ↥(Fset s b F)} (hne : f ≠ g)
    (y : Vf s b F g.1) : ((prjB H f (y : Fin n → L) : Vf s b F f.1) : Fin n → L) = 0 := by
  rw [prjB, coe_prjV]
  exact Pmat_mulVec_of_mem_ne H (mem_Fset.mp f.2).1 (mem_Fset.mp g.2).1
    (fun h => hne (Subtype.ext h)) y.2

theorem Bk_comp_self (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F))
    (w v : Vf s b F f.1 →ₗ[L] Vf s b F f.1) :
    Bk H f w ∘ₗ Bk H f v = Bk H f (w ∘ₗ v) := by
  apply LinearMap.ext
  intro x
  simp only [Bk, LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  simp only [inclB, Submodule.subtype_apply]
  rw [prjB_incl_self]

theorem Bk_comp_ne (H : PrimaryHyp τ s m F a b) {f g : ↥(Fset s b F)} (hne : f ≠ g)
    (w : Vf s b F f.1 →ₗ[L] Vf s b F f.1) (v : Vf s b F g.1 →ₗ[L] Vf s b F g.1) :
    Bk H f w ∘ₗ Bk H g v = 0 := by
  apply LinearMap.ext
  intro x
  have h0 : prjB H f ((v (prjB H g x) : Vf s b F g.1) : Fin n → L) = 0 :=
    Subtype.ext (prjB_incl_ne H hne _)
  simp only [Bk, LinearMap.comp_apply, LinearMap.zero_apply, inclB, Submodule.subtype_apply, h0,
    map_zero]

theorem sum_Bk_id (H : PrimaryHyp τ s m F a b) :
    ∑ f : ↥(Fset s b F), Bk H f LinearMap.id = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.sum_apply]
  simp only [Bk, LinearMap.comp_apply, LinearMap.id_apply, inclB, Submodule.subtype_apply,
    prjB, coe_prjV]
  rw [Finset.sum_coe_sort (Fset s b F) (fun g => Pmat s b F g *ᵥ x)]
  exact sum_Pmat_mulVec H x

theorem rhoL_comp (H : PrimaryHyp τ s m F a b)
    (w v : (f : ↥(Fset s b F)) → Vf s b F f.1 →ₗ[L] Vf s b F f.1) :
    rhoL H w ∘ₗ rhoL H v = rhoL H (fun f => w f ∘ₗ v f) := by
  apply LinearMap.ext
  intro x
  simp only [rhoL, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_eq_single f]
  · have := LinearMap.congr_fun (Bk_comp_self H f (w f) (v f)) x
    simpa using this
  · intro g _ hg
    have := LinearMap.congr_fun (Bk_comp_ne H hg (w g) (v f)) x
    simpa using this
  · intro h
    exact absurd (Finset.mem_univ f) h

theorem rhoL_one (H : PrimaryHyp τ s m F a b) :
    rhoL H (fun _ => LinearMap.id) = LinearMap.id := sum_Bk_id H

theorem rhoL_apply_block (H : PrimaryHyp τ s m F a b)
    (w : (f : ↥(Fset s b F)) → Vf s b F f.1 →ₗ[L] Vf s b F f.1) (f : ↥(Fset s b F))
    (y : Vf s b F f.1) : rhoL H w (y : Fin n → L) = (w f y : Fin n → L) := by
  unfold rhoL
  rw [LinearMap.sum_apply, Finset.sum_eq_single f]
  · simp only [Bk, LinearMap.comp_apply, inclB, Submodule.subtype_apply, prjB_incl_self]
  · intro g _ hg
    have h0 : prjB H g ((y : Vf s b F f.1) : Fin n → L) = 0 := Subtype.ext (prjB_incl_ne H hg y)
    simp only [Bk, LinearMap.comp_apply, inclB, Submodule.subtype_apply, h0, map_zero]
  · intro h
    exact absurd (Finset.mem_univ f) h

@[expose] noncomputable def resT (H : PrimaryHyp τ s m F a b) (T : (Fin n → L) →ₗ[L] (Fin n → L))
    (hcomm : ∀ (f : ↥(Fset s b F)) (x : Fin n → L),
      Pmat s b F f.1 *ᵥ (T x) = T (Pmat s b F f.1 *ᵥ x))
    (f : ↥(Fset s b F)) : Vf s b F f.1 →ₗ[L] Vf s b F f.1 :=
  T.restrict (fun y hy => mem_Vf.mpr (by
    rw [hcomm, mem_Vf.mp hy]))

theorem rho_restrict (H : PrimaryHyp τ s m F a b) (T : (Fin n → L) →ₗ[L] (Fin n → L))
    (hcomm : ∀ (f : ↥(Fset s b F)) (x : Fin n → L),
      Pmat s b F f.1 *ᵥ (T x) = T (Pmat s b F f.1 *ᵥ x)) :
    T = rhoL H (fun f => resT H T hcomm f) := by
  apply LinearMap.ext
  intro x
  conv_lhs => rw [← sum_Pmat_mulVec H x]
  rw [map_sum]
  rw [← Finset.sum_coe_sort (Fset s b F) (fun g => T (Pmat s b F g *ᵥ x))]
  unfold rhoL
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Bk, LinearMap.comp_apply, inclB, Submodule.subtype_apply, resT,
    LinearMap.restrict_apply, prjB, coe_prjV]

end Blocks

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end
