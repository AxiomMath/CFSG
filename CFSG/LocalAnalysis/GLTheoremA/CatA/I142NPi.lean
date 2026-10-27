module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142N

open CFSG.Open
open scoped commutatorElement

section Product

variable {S : Type*} [Group S] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def piProd (H : ι → Subgroup S)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y) : (∀ i, ↥(H i)) →* S :=
  MonoidHom.noncommPiCoprod (fun i => (H i).subtype)
    (by
      intro i j hij x y
      exact hcomm i j hij x x.2 y y.2)

theorem piProd_mulSingle (H : ι → Subgroup S)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y) (i : ι) (x : ↥(H i)) :
    piProd H hcomm (Pi.mulSingle i x) = (x : S) := by
  unfold piProd
  rw [MonoidHom.noncommPiCoprod_mulSingle]
  rfl

theorem piHom_ext {N : ι → Type*} [∀ i, Group (N i)] {M : Type*} [Group M]
    (φ ψ : (∀ i, N i) →* M) (h : ∀ i (x : N i), φ (Pi.mulSingle i x) = ψ (Pi.mulSingle i x)) :
    φ = ψ := by
  ext f
  have hf := Finset.noncommProd_mulSingle f
  conv_lhs => rw [← hf]
  conv_rhs => rw [← hf]
  erw [Finset.map_noncommProd _ _ _ φ, Finset.map_noncommProd _ _ _ ψ]
  congr 1
  funext i
  exact h i (f i)

theorem piProd_ker_central (H : ι → Subgroup S)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y) {f : ∀ i, ↥(H i)}
    (hf : piProd H hcomm f = 1) : f ∈ Subgroup.center (∀ i, ↥(H i)) := by
  have hcommf : ∀ i, ∀ x ∈ H i, Commute x (f i : S) := by
    intro i
    set f' : ∀ j, ↥(H j) := Function.update f i 1 with hf'
    have hsplit : f = Pi.mulSingle i (f i) * f' := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp [hf']
      · simp [hf', Pi.mulSingle_apply, hj]
    have h1 : (f i : S) * piProd H hcomm f' = 1 := by
      rw [← piProd_mulSingle H hcomm i (f i), ← map_mul, ← hsplit, hf]
    have h2 : piProd H hcomm f' = (f i : S)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : ∀ x ∈ H i, Commute x (piProd H hcomm f') := by
      intro x hx
      rw [piProd, MonoidHom.noncommPiCoprod_apply]
      refine Finset.noncommProd_induction _ _ _ (fun y => Commute x y)
        (fun y z hy hz => hy.mul_right hz) (Commute.one_right x) ?_
      intro c _
      by_cases hc : c = i
      · subst hc
        simp [hf']
      · have hfc : (f' c : S) ∈ H c := (f' c).2
        exact hcomm i c (Ne.symm hc) x hx _ hfc
    intro x hx
    have := h3 x hx
    rw [h2] at this
    exact Commute.inv_right_iff.1 this
  rw [Subgroup.mem_center_iff]
  intro g
  funext j
  apply Subtype.ext
  have := hcommf j (g j : S) (g j).2
  simpa [Pi.mul_apply] using this.eq

theorem piProd_range (H : ι → Subgroup S)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y) :
    (piProd H hcomm).range = ⨆ i, H i := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    rw [piProd, MonoidHom.noncommPiCoprod_apply]
    apply Subgroup.noncommProd_mem
    intro c _
    exact le_iSup H c (f c).2
  · refine iSup_le fun i x hx => ?_
    refine ⟨Pi.mulSingle i ⟨x, hx⟩, ?_⟩
    rw [piProd_mulSingle]

section Action

variable {A : Type*} [Group A]

@[expose] def coordFun (ρ : A →* MulAut S) (H : ι → Subgroup S) (σ : A →* Equiv.Perm ι)
    (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i)) (a : A) (f : ∀ i, ↥(H i)) :
    ∀ i, ↥(H i) :=
  fun k => ⟨ρ a (f ((σ a).symm k)), by
    have h1 : ρ a (f ((σ a).symm k) : S) ∈ (H ((σ a).symm k)).map (ρ a).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (f _).2
    rw [hmap] at h1
    rwa [Equiv.apply_symm_apply] at h1⟩

theorem coordFun_apply (ρ : A →* MulAut S) (H : ι → Subgroup S) (σ : A →* Equiv.Perm ι)
    (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i)) (a : A) (f : ∀ i, ↥(H i))
    (k : ι) : ((coordFun ρ H σ hmap a f k : ↥(H k)) : S) = ρ a (f ((σ a).symm k) : S) := rfl

theorem coordFun_mul (ρ : A →* MulAut S) (H : ι → Subgroup S) (σ : A →* Equiv.Perm ι)
    (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i)) (a b : A) (f : ∀ i, ↥(H i)) :
    coordFun ρ H σ hmap (a * b) f = coordFun ρ H σ hmap a (coordFun ρ H σ hmap b f) := by
  funext k
  apply Subtype.ext
  rw [coordFun_apply, coordFun_apply, coordFun_apply, map_mul, MulAut.mul_apply]
  congr 2
  rw [map_mul, Equiv.Perm.mul_def, Equiv.symm_trans_apply]

theorem coordFun_one (ρ : A →* MulAut S) (H : ι → Subgroup S) (σ : A →* Equiv.Perm ι)
    (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i)) (f : ∀ i, ↥(H i)) :
    coordFun ρ H σ hmap 1 f = f := by
  funext k
  apply Subtype.ext
  rw [coordFun_apply, map_one, map_one, MulAut.one_apply]
  rfl

@[expose] def coordEquiv (ρ : A →* MulAut S) (H : ι → Subgroup S) (σ : A →* Equiv.Perm ι)
    (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i)) (a : A) :
    (∀ i, ↥(H i)) ≃* (∀ i, ↥(H i)) where
  toFun := coordFun ρ H σ hmap a
  invFun := coordFun ρ H σ hmap a⁻¹
  left_inv f := by
    rw [← coordFun_mul, inv_mul_cancel, coordFun_one]
  right_inv f := by
    rw [← coordFun_mul, mul_inv_cancel, coordFun_one]
  map_mul' f g := by
    funext k
    apply Subtype.ext
    simp only [Pi.mul_apply, Subgroup.coe_mul, coordFun_apply, map_mul]

theorem mem_coordTarget (ρ : A →* MulAut S) (H : ι → Subgroup S) (σ : A →* Equiv.Perm ι)
    (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i)) (a : A) (i : ι) (x : ↥(H i)) :
    ρ a (x : S) ∈ H ((σ a) i) := by
  rw [← hmap]
  exact Subgroup.mem_map_of_mem _ x.2

theorem coordFun_mulSingle (ρ : A →* MulAut S) (H : ι → Subgroup S) (σ : A →* Equiv.Perm ι)
    (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i)) (a : A) (i : ι) (x : ↥(H i)) :
    coordFun ρ H σ hmap a (Pi.mulSingle i x) =
      Pi.mulSingle ((σ a) i) ⟨ρ a (x : S), mem_coordTarget ρ H σ hmap a i x⟩ := by
  funext k
  apply Subtype.ext
  rw [coordFun_apply]
  by_cases hk : k = (σ a) i
  · subst hk
    have hsymm : (σ a).symm ((σ a) i) = i := Equiv.symm_apply_apply (σ a) i
    rw [hsymm, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · have hk' : (σ a).symm k ≠ i := by
      intro h
      apply hk
      rw [← h, Equiv.apply_symm_apply]
    simp [Pi.mulSingle_apply, hk, hk']

@[expose] def coordHom (ρ : A →* MulAut S) (H : ι → Subgroup S) (σ : A →* Equiv.Perm ι)
    (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i)) :
    A →* MulAut (∀ i, ↥(H i)) :=
  MonoidHom.mk' (coordEquiv ρ H σ hmap) (fun a b => MulEquiv.ext fun f =>
    coordFun_mul ρ H σ hmap a b f)

theorem piProd_coordHom (ρ : A →* MulAut S) (H : ι → Subgroup S)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y) (σ : A →* Equiv.Perm ι)
    (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i)) (a : A)
    (f : ∀ i, ↥(H i)) :
    piProd H hcomm (coordHom ρ H σ hmap a f) = ρ a (piProd H hcomm f) := by
  have h := piHom_ext ((piProd H hcomm).comp (coordEquiv ρ H σ hmap a).toMonoidHom)
    ((ρ a).toMonoidHom.comp (piProd H hcomm)) (fun i x => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coordEquiv]
      change piProd H hcomm (coordFun ρ H σ hmap a (Pi.mulSingle i x)) = ρ a (piProd H hcomm _)
      rw [coordFun_mulSingle, piProd_mulSingle, piProd_mulSingle])
  exact DFunLike.congr_fun h f

end Action

end Product

end CFSG.LocalAnalysis.GLTheoremA.I142N
